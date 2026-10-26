use clap::error::ErrorKind;
use clap::{Args, CommandFactory, Parser as ClapParser, Subcommand, ValueEnum};
use colored_json::{ColoredFormatter, CompactFormatter, Styler};
use indicatif::{ProgressBar, ProgressStyle};
use log2src::{
    Cache, LogError, LogFormat, LogLevel, LogMapping, LogMatchOptions, LogMatcher, LogRef,
    LogRefBuilder, ProgressTracker, ProgressUpdate, Revision, SourceLanguage, SourceRef,
};
use miette::{miette, IntoDiagnostic, MietteHandlerOpts, Report};
use serde::Serialize;
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet};
use std::io::{stdout, BufRead, BufReader, Write};
use std::path::Path;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::thread::{sleep, JoinHandle};
use std::time::Duration;
use std::{env, fs, io, path::PathBuf};

fn get_footer() -> String {
    let mut footer = String::new();
    if let Ok(cache) = Cache::open() {
        footer.push_str("Paths:\n");
        footer.push_str(
            format!(
                "    Cache directory: {}\n",
                cache.location.to_string_lossy()
            )
            .as_str(),
        );
    }
    footer.push_str("\nFor more information, see https://github.com/ttiimm/log2src\n");
    footer
}

/// The log2src command maps log statements back to the source code that emitted them.
#[derive(ClapParser)]
#[command(author, version, about, long_about)]
#[command(after_help = get_footer())]
struct Cli {
    /// The source directories to map logs onto
    #[arg(short = 'd', long = "source", value_name = "SOURCE", global = true)]
    sources: Vec<String>,

    /// Print progress information to standard error
    #[arg(short, long, global = true)]
    verbose: bool,

    /// Do not read or write the cache of log statements
    #[arg(long, global = true)]
    no_cache: bool,

    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Map log messages to the source code that emitted them
    Match(MatchArgs),
    /// Print the log statements found in the source directories
    Statements(StatementsArgs),
    /// Find the source file for a path, like one from a stack trace
    Locate(LocateArgs),
    /// Manage the cache of log statements
    #[command(subcommand)]
    Cache(CacheCommand),
}

#[derive(Args)]
struct MatchArgs {
    /// A log file to use, if not from stdin
    #[arg(short, long, value_name = "LOG", conflicts_with = "message")]
    log: Option<PathBuf>,

    /// A single log message to match, instead of reading a log
    #[arg(short, long, value_name = "MESSAGE")]
    message: Option<String>,

    /// The regex of a log format being used
    #[arg(short, long, value_name = "FORMAT")]
    format: Option<String>,

    /// The first line in the log to use (0 based)
    #[arg(short, long, value_name = "START")]
    start: Option<usize>,

    /// The number of log messages to process
    #[arg(short, long, value_name = "COUNT")]
    count: Option<usize>,

    /// Do not extract the values of variables from the messages
    #[arg(long)]
    no_vars: bool,
}

#[derive(Copy, Clone, ValueEnum)]
enum StatementsOutput {
    /// One JSON object per statement
    Json,
    /// Tab-separated path, line, level, name, and message
    Tsv,
}

#[derive(Args)]
struct StatementsArgs {
    /// Only print statements with these levels
    #[arg(long, value_name = "LEVEL", value_delimiter = ',', value_parser = parse_level)]
    level: Vec<LogLevel>,

    /// Only print statements in these languages
    #[arg(long, value_name = "LANG", value_delimiter = ',', value_parser = parse_language)]
    lang: Vec<SourceLanguage>,

    /// Only print statements in this source file
    #[arg(long, value_name = "FILE")]
    file: Option<PathBuf>,

    /// The output format
    #[arg(short, long, value_enum, default_value_t = StatementsOutput::Json)]
    output: StatementsOutput,

    /// Print the number of statements by language and level instead of the statements
    #[arg(long, conflicts_with = "output")]
    summary: bool,
}

#[derive(Args)]
struct LocateArgs {
    /// The paths to find
    #[arg(required = true, value_name = "PATH")]
    paths: Vec<PathBuf>,
}

#[derive(Subcommand)]
enum CacheCommand {
    /// Print the location of the cache directory
    Path,
    /// List the entries in the cache, or only the ones for the given sources
    List,
    /// Find the log statements in the given sources and save them to the cache
    Update,
    /// Remove all of the entries in the cache, or only the ones for the given sources
    Clear,
}

const LEVELS: [LogLevel; 7] = [
    LogLevel::Trace,
    LogLevel::Debug,
    LogLevel::Info,
    LogLevel::Warn,
    LogLevel::Error,
    LogLevel::Fatal,
    LogLevel::Unknown,
];

const LANGUAGES: [SourceLanguage; 5] = [
    SourceLanguage::Rust,
    SourceLanguage::Java,
    SourceLanguage::Cpp,
    SourceLanguage::Python,
    SourceLanguage::Kotlin,
];

fn parse_level(arg: &str) -> Result<LogLevel, String> {
    LEVELS
        .into_iter()
        .find(|level| format!("{:?}", level).eq_ignore_ascii_case(arg))
        .ok_or_else(|| {
            let names: Vec<_> = LEVELS
                .iter()
                .map(|level| format!("{:?}", level).to_lowercase())
                .collect();
            format!("expected one of: {}", names.join(", "))
        })
}

fn parse_language(arg: &str) -> Result<SourceLanguage, String> {
    LANGUAGES
        .into_iter()
        .find(|lang| lang.as_str().eq_ignore_ascii_case(arg))
        .ok_or_else(|| {
            let names: Vec<_> = LANGUAGES
                .iter()
                .map(|lang| lang.as_str().to_lowercase())
                .collect();
            format!("expected one of: {}", names.join(", "))
        })
}

fn get_colored_formatter() -> ColoredFormatter<CompactFormatter> {
    let compact_formatter = CompactFormatter {};

    ColoredFormatter::with_styler(compact_formatter, Styler::default())
}

#[must_use]
struct MessageAccumulator {
    log_matcher: LogMatcher,
    log_format: Option<LogFormat>,
    match_options: LogMatchOptions,
    content: String,
    message_count: usize,
    limit: usize,
}

impl MessageAccumulator {
    fn new(
        log_matcher: LogMatcher,
        log_format: Option<LogFormat>,
        match_options: LogMatchOptions,
        limit: usize,
    ) -> Self {
        Self {
            log_matcher,
            log_format,
            match_options,
            content: String::new(),
            message_count: 0,
            limit,
        }
    }

    fn get_log_mapping<'a>(&self, log_ref: LogRef<'a>) -> LogMapping<'a, '_> {
        self.log_matcher
            .match_log_statement(&log_ref, &self.match_options)
            .unwrap_or_else(move || LogMapping {
                log_ref,
                src_ref: None,
                variables: vec![],
                exception_trace: vec![],
            })
    }

    fn process_msg(&mut self) {
        if let Some(captures) = self.log_format.as_ref().unwrap().captures(&self.content) {
            self.message_count += 1;
            let log_ref = LogRefBuilder::new().build_from_captures(captures, &self.content);
            let log_mapping = self.get_log_mapping(log_ref);
            let serialized = get_colored_formatter().to_colored_json_auto(&log_mapping);
            println!("{}", serialized.unwrap());
        }
        self.content.clear();
    }

    fn new_msg(&mut self, line: &str) {
        if !self.content.is_empty() {
            self.process_msg();
        }

        self.content.push_str(line);
    }

    fn continued_line(&mut self, line: &str) {
        if self.content.is_empty() {
            return;
        }
        self.content.push('\n');
        self.content.push_str(line);
    }

    fn process_bare_msg(&self, line: &str) {
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        let log_mapping = self.get_log_mapping(log_ref);
        println!(
            "{}",
            get_colored_formatter()
                .to_colored_json_auto(&log_mapping)
                .unwrap()
        );
    }

    fn consume_line(&mut self, line: &str) {
        match &self.log_format {
            Some(format) => {
                if format.is_match(&line) {
                    self.new_msg(&line);
                } else {
                    self.continued_line(&line);
                }
            }
            None => {
                self.process_bare_msg(&line);
            }
        }
    }

    fn flush(&mut self) {
        if !self.content.is_empty() && !self.at_limit() {
            self.process_msg();
        }
    }

    fn at_limit(&self) -> bool {
        self.message_count >= self.limit
    }

    fn eof(mut self) -> miette::Result<()> {
        self.flush();

        if self.log_format.is_some() && self.message_count == 0 {
            Err(LogError::NoLogMessages.into())
        } else {
            Ok(())
        }
    }
}

#[derive(Debug, Serialize)]
struct SerializableDiagnostic {
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    severity: Option<miette::Severity>,
    #[serde(skip_serializing_if = "Option::is_none")]
    source: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    help: Option<String>,
}

impl From<Report> for SerializableDiagnostic {
    fn from(value: Report) -> Self {
        Self {
            message: value.to_string(),
            code: value.code().map(|c| c.to_string()),
            severity: value.severity(),
            source: value.source().map(|s| s.to_string()),
            help: value.help().map(|h| h.to_string()),
        }
    }
}

#[derive(Debug, Serialize)]
struct ErrorWrapper {
    error: SerializableDiagnostic,
}

/// Print the progress updates from the tracker to stderr until it is dropped.
fn spawn_progress_listener(tracker: &mut ProgressTracker) -> JoinHandle<()> {
    let listener = tracker.subscribe();
    std::thread::spawn(move || {
        let mut prefix = String::new();
        for update in listener {
            match update {
                ProgressUpdate::Step(msg) => eprintln!("{}", msg),
                ProgressUpdate::BeginStep(msg) => {
                    prefix = msg;
                }
                ProgressUpdate::EndStep(msg) => {
                    eprintln!("{}... {}", prefix, msg);
                    prefix.clear();
                }
                ProgressUpdate::Work(info) => {
                    // XXX Take the stdout lock so that the actual output does not interfere
                    // with the progress bar updates on stderr.
                    let _stdout_lock = stdout().lock();
                    let template = if info.units == "bytes" {
                        "{prefix}... {bar} {bytes:>10}/{total_bytes:10}"
                    } else {
                        "{prefix}... {bar} {pos:>7}/{len:7}"
                    };
                    let bar = ProgressBar::new(info.total)
                        .with_prefix(prefix.clone())
                        .with_style(ProgressStyle::with_template(template).unwrap());
                    while info.is_in_progress() {
                        bar.set_position(info.completed.load(Ordering::Relaxed));
                        sleep(Duration::from_millis(33));
                    }
                    bar.finish_and_clear();
                }
            }
        }
    })
}

/// How the cache is used when building a LogMatcher.
#[derive(Copy, Clone, PartialEq)]
enum CacheMode {
    /// Load the statements from the cache and save them if anything changed.
    ReadWrite,
    /// Load the statements from the cache and always save them.
    ForceWrite,
    /// Do not touch the cache.
    Disabled,
}

/// Find the log statements in the source trees, using the cache when possible.
fn build_log_matcher(
    sources: &[String],
    verbose: bool,
    cache_mode: CacheMode,
    require_statements: bool,
    tracker: &ProgressTracker,
) -> miette::Result<LogMatcher> {
    let mut log_matcher = LogMatcher::new();
    for source in sources {
        log_matcher
            .add_root(&PathBuf::from(source))
            .into_diagnostic()?;
    }

    let cache_open_res = Cache::open();
    if verbose && cache_mode != CacheMode::Disabled && cache_open_res.is_err() {
        eprintln!("Could not find cache directory, will not cache source trees");
    }
    let cache = cache_open_res
        .ok()
        .filter(|_| cache_mode != CacheMode::Disabled);

    if let Some(cache) = &cache {
        let res = log_matcher.load_from_cache(&cache, tracker);
        for err in res {
            let report = Report::new(err);
            if verbose
                || report.severity().unwrap_or(miette::Severity::Error) != miette::Severity::Advice
            {
                eprintln!("{:?}", report);
            }
        }
    }

    log_matcher
        .discover_sources(tracker)
        .into_iter()
        .for_each(|err| eprintln!("{:?}", Report::new(err)));
    let mut extract_summary = log_matcher.extract_log_statements(tracker);
    extract_summary
        .errors
        .drain(..)
        .for_each(|err| eprintln!("{:?}", Report::new(err)));
    if require_statements && log_matcher.is_empty() {
        return Err(LogError::NoLogStatements.into());
    }

    if extract_summary.changes() > 0 || cache_mode == CacheMode::ForceWrite {
        if let Some(cache) = &cache {
            let res = log_matcher.cache_to(&cache, tracker);
            if let Err(err) = res {
                eprintln!("{:?}", Report::new(err));
            }
        }
    }

    Ok(log_matcher)
}

/// Build a LogMatcher for the sources given on the command line, printing progress if asked.
fn load_log_matcher(
    cli: &Cli,
    cache_mode: CacheMode,
    require_statements: bool,
) -> miette::Result<LogMatcher> {
    if cli.sources.is_empty() {
        Cli::command()
            .error(
                ErrorKind::MissingRequiredArgument,
                "at least one source directory must be given with '--source <SOURCE>'",
            )
            .exit();
    }

    let mut tracker = ProgressTracker::new();
    let listener_thread = cli.verbose.then(|| spawn_progress_listener(&mut tracker));
    let cache_mode = if cli.no_cache {
        match cache_mode {
            CacheMode::ForceWrite => CacheMode::ForceWrite,
            _ => CacheMode::Disabled,
        }
    } else {
        cache_mode
    };
    let matcher_res = build_log_matcher(
        &cli.sources,
        cli.verbose,
        cache_mode,
        require_statements,
        &tracker,
    );
    // Nothing else reports progress, so close the channel and wait for the listener to print
    // the remaining updates.  Otherwise, they are lost if the program exits early.
    drop(tracker);
    if let Some(handle) = listener_thread {
        let _ = handle.join();
    }
    matcher_res
}

fn run_match(cli: &Cli, args: &MatchArgs) -> miette::Result<()> {
    let log_format: Option<LogFormat> = if let Some(format) = &args.format {
        Some(format.as_str().try_into()?)
    } else {
        None
    };

    let reader: Box<dyn io::Read> = match (&args.log, &args.message) {
        (_, Some(message)) => Box::new(io::Cursor::new(message.clone().into_bytes())),
        (None, None) => Box::new(io::stdin()),
        (Some(filename), None) => {
            let path = PathBuf::from(filename);
            match fs::File::open(&path) {
                Ok(file) => Box::new(file),
                Err(err) => {
                    return Err(LogError::CannotReadLogFile {
                        path,
                        source: err.into(),
                    }
                    .into());
                }
            }
        }
    };

    let log_matcher = load_log_matcher(cli, CacheMode::ReadWrite, true)?;

    let start = args.start.unwrap_or(0);
    let count = args.count.unwrap_or(usize::MAX);
    let match_options = LogMatchOptions {
        extract_variables: !args.no_vars,
    };
    let mut accumulator = MessageAccumulator::new(log_matcher, log_format, match_options, count);

    let reader = BufReader::new(reader);
    for (lineno, line_res) in reader.lines().skip(start).enumerate() {
        if accumulator.at_limit() {
            break;
        }
        match line_res {
            Ok(line) => accumulator.consume_line(&line),
            Err(err) => {
                accumulator.flush();
                let report: Report = LogError::UnableToReadLine {
                    line: lineno,
                    source: err.into(),
                }
                .into();
                let wrapper = ErrorWrapper {
                    error: SerializableDiagnostic::from(report),
                };
                println!(
                    "{}",
                    get_colored_formatter()
                        .to_colored_json_auto(&wrapper)
                        .unwrap()
                );
            }
        }
    }

    accumulator.eof()
}

/// Escape the characters that would break up a TSV row.
fn escape_tsv(value: &str) -> String {
    value
        .replace('\\', "\\\\")
        .replace('\t', "\\t")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

fn run_statements(cli: &Cli, args: &StatementsArgs) -> miette::Result<()> {
    let log_matcher = load_log_matcher(cli, CacheMode::ReadWrite, true)?;

    let mut statements: Vec<&SourceRef> = match &args.file {
        Some(path) => {
            let Some(found) = log_matcher.find_file(path) else {
                return Err(miette!("cannot find source file \"{}\"", path.display()));
            };
            log_matcher
                .find_source_file_statements(&found)
                .into_iter()
                .flat_map(|sif| sif.statements())
                .collect()
        }
        None => log_matcher.statements().collect(),
    };
    statements.retain(|stmt| {
        (args.level.is_empty() || args.level.contains(&stmt.level))
            && (args.lang.is_empty() || args.lang.contains(&stmt.language))
    });
    statements.sort_by(|lhs, rhs| {
        (&lhs.source_path, lhs.line_no, lhs.column).cmp(&(
            &rhs.source_path,
            rhs.line_no,
            rhs.column,
        ))
    });

    if args.summary {
        let mut by_language: BTreeMap<&str, BTreeMap<String, usize>> = BTreeMap::new();
        for stmt in &statements {
            *by_language
                .entry(stmt.language.as_str())
                .or_default()
                .entry(format!("{:?}", stmt.level))
                .or_default() += 1;
        }
        let files: BTreeSet<&str> = statements
            .iter()
            .map(|stmt| stmt.source_path.as_str())
            .collect();
        let summary = json!({
            "statements": statements.len(),
            "files": files.len(),
            "byLanguage": by_language,
        });
        println!(
            "{}",
            get_colored_formatter()
                .to_colored_json_auto(&summary)
                .unwrap()
        );
        return Ok(());
    }

    let mut out = stdout().lock();
    for stmt in statements {
        let line = match args.output {
            StatementsOutput::Json => get_colored_formatter().to_colored_json_auto(stmt).unwrap(),
            StatementsOutput::Tsv => format!(
                "{}\t{}\t{:?}\t{}\t{}",
                escape_tsv(&stmt.source_path),
                stmt.line_no,
                stmt.level,
                escape_tsv(&stmt.name),
                escape_tsv(&stmt.text)
            ),
        };
        if writeln!(out, "{}", line).is_err() {
            // The reader went away, like when piping to `head`.
            break;
        }
    }

    Ok(())
}

fn run_locate(cli: &Cli, args: &LocateArgs) -> miette::Result<()> {
    let log_matcher = load_log_matcher(cli, CacheMode::ReadWrite, false)?;

    for path in &args.paths {
        let found = log_matcher.find_file(path);
        let result = json!({
            "path": path.to_string_lossy(),
            "file": found.map(|found| found.to_string_lossy().to_string()),
        });
        println!(
            "{}",
            get_colored_formatter()
                .to_colored_json_auto(&result)
                .unwrap()
        );
    }

    Ok(())
}

/// The paths of the entries in the cache, or only the ones for the given sources.
fn cache_entries(cache: &Cache, sources: &[String]) -> Vec<PathBuf> {
    if !sources.is_empty() {
        return sources
            .iter()
            .map(|source| cache.entry_path(Path::new(source)))
            .filter(|path| path.is_file())
            .collect();
    }

    let Ok(dir) = fs::read_dir(&cache.location) else {
        return vec![];
    };
    let mut retval: Vec<PathBuf> = dir
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.path())
        .filter(|path| {
            path.is_file()
                && path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with("cache."))
        })
        .collect();
    retval.sort();
    retval
}

/// Print the header of each cache entry.
fn list_cache_entries(cache: &Cache, sources: &[String]) -> miette::Result<()> {
    let current_revision = serde_json::to_value(Revision::Current).into_diagnostic()?;
    for entry_path in cache_entries(cache, sources) {
        let header = fs::File::open(&entry_path)
            .ok()
            .and_then(|file| BufReader::new(file).lines().next())
            .and_then(|line| line.ok())
            .and_then(|line| serde_json::from_str::<serde_json::Value>(&line).ok())
            .unwrap_or_default();
        let size = fs::metadata(&entry_path).map_or(0, |meta| meta.len());
        let revision = header.get("revision").cloned().unwrap_or_default();
        let result = json!({
            "entry": entry_path.to_string_lossy(),
            "root": header.get("path"),
            "revision": revision,
            "timestamp": header.get("timestamp"),
            "size": size,
            "stale": revision != current_revision,
        });
        println!(
            "{}",
            get_colored_formatter()
                .to_colored_json_auto(&result)
                .unwrap()
        );
    }

    Ok(())
}

fn run_cache(cli: &Cli, command: &CacheCommand) -> miette::Result<()> {
    let cache = Cache::open()?;
    match command {
        CacheCommand::Path => {
            println!("{}", cache.location.display());
        }
        CacheCommand::List => {
            list_cache_entries(&cache, &cli.sources)?;
        }
        CacheCommand::Update => {
            load_log_matcher(cli, CacheMode::ForceWrite, false)?;
            list_cache_entries(&cache, &cli.sources)?;
        }
        CacheCommand::Clear => {
            for entry_path in cache_entries(&cache, &cli.sources) {
                fs::remove_file(&entry_path).map_err(|err| LogError::FailedToWriteCache {
                    source: Arc::new(err),
                })?;
                if cli.verbose {
                    eprintln!("Removed {}", entry_path.display());
                }
            }
        }
    }

    Ok(())
}

fn main() -> miette::Result<()> {
    let _ = miette::set_hook(Box::new(move |_| {
        Box::new(
            MietteHandlerOpts::new()
                .width(env::var("COLS").unwrap_or_default().parse().unwrap_or(80))
                .break_words(false)
                .build(),
        )
    }));

    let cli = Cli::parse();

    match &cli.command {
        Command::Match(args) => run_match(&cli, args),
        Command::Statements(args) => run_statements(&cli, args),
        Command::Locate(args) => run_locate(&cli, args),
        Command::Cache(command) => run_cache(&cli, command),
    }
}
