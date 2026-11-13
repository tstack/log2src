use directories::ProjectDirs;
use indicatif::HumanBytes;
use itertools::Itertools;
use miette::Diagnostic;
use rayon::prelude::*;
use regex::{Captures, Regex};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::ffi::OsStr;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Read, Seek, Write};
use std::ops::{Deref, Range};
use std::path::{Component, Path, PathBuf};
use std::sync::{Arc, LazyLock, OnceLock, PoisonError, RwLock};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{fs, io};
use tempfile::NamedTempFile;
use thiserror::Error;
use tree_sitter::{Language, Query};

mod code_source;
mod java_symbols;
mod log_format;
mod match_stats;
mod message_source;
mod prefilter;
mod progress;
mod source_hier;
mod source_query;
mod source_ref;
mod value_kind;
mod wrappers;

// TODO: doesn't need to be exposed if we can clean up the arguments to do_mapping
use crate::java_symbols::{JavaSymbols, MessageRef, StringConstant};
use crate::prefilter::{Prefilter, StatementID};
use crate::progress::{ProgressReader, WorkGuard};
use crate::source_hier::{ScanEvent, SourceFileID, SourceHierContent, SourceHierTree};
use crate::source_query::ConcatPart;
use crate::source_ref::{ChainFrame, FormatArgument, Splice};
use crate::value_kind::SplitOrder;
pub use code_source::CodeSource;
pub use log_format::LogFormat;
pub use match_stats::{match_stats, take_match_stats, MatchStats, PhaseStats};
use match_stats::{Outcome, Step};
pub use message_source::{find_message_sources, MessageSource};
pub use progress::ProgressTracker;
pub use progress::ProgressUpdate;
pub use progress::WorkInfo;
use source_query::QueryResult;
pub use source_query::SourceQuery;
pub use source_ref::{LogLevel, MessageCategory, Quality, Statement};

#[derive(Error, Debug, Diagnostic, Clone, Default)]
pub enum LogError {
    #[default]
    #[error("unknown error")]
    Unknown,
    #[error("unable to read line {line}")]
    UnableToReadLine { line: usize, source: Arc<io::Error> },
    #[error("invalid log format regular expression")]
    InvalidFormatRegex { source: regex::Error },
    #[error("unknown capture in log format: {name}")]
    #[diagnostic(help(
        "The supported captures are: timestamp, thread, level, file, line, method, and body"
    ))]
    UnknownFormatCapture { name: String },
    #[error("log format is missing capture: {name}")]
    #[diagnostic(help("A log format must have a 'body' capture at a minimum"))]
    FormatMissingCapture { name: String },
    #[error("\"{path}\" is already covered by \"{root}\"")]
    PathExists { path: PathBuf, root: PathBuf },
    #[error("cannot read source file \"{path}\"")]
    #[diagnostic(severity(warning))]
    CannotReadSourceFile {
        path: PathBuf,
        source: Arc<io::Error>,
    },
    #[error("cannot read log file \"{path}\"")]
    CannotReadLogFile {
        path: PathBuf,
        source: Arc<io::Error>,
    },
    #[error("no log statements found")]
    #[diagnostic(help(
        "\
    Make sure the source path is valid and refers to a tree with \
    supported source code and logging statements"
    ))]
    NoLogStatements,
    #[error("cannot access path \"{path}\"")]
    #[diagnostic(severity(warning))]
    CannotAccessPath {
        path: PathBuf,
        source: Arc<io::Error>,
    },
    #[error("unsupported file type \"{name}\"")]
    UnsupportedFileType { name: String },
    #[error("no log messages found in input")]
    #[diagnostic(help("Make sure the log format matches the input"))]
    NoLogMessages,
    #[error("failed to find user cache directory")]
    #[diagnostic(severity(warning))]
    CannotFindCache,
    #[error("failed to create cache directory \"{path}\"")]
    #[diagnostic(severity(warning))]
    CannotCreateCache {
        path: PathBuf,
        source: Arc<dyn Error + Send + Sync>,
    },
    #[error("failed to write cache file")]
    #[diagnostic(severity(warning))]
    FailedToWriteCache {
        source: Arc<dyn Error + Send + Sync>,
    },
    #[error("outdated cache file \"{path}\"")]
    #[diagnostic(severity(info))]
    OldCacheEntry { path: PathBuf },
    #[error("failed to read cache file \"{path}\"")]
    #[diagnostic(severity(warning))]
    FailedToReadCache {
        path: PathBuf,
        source: Arc<dyn Error + Send + Sync>,
    },
}

/// Handle for the source tree cache
pub struct Cache {
    pub location: PathBuf,
}

impl Cache {
    /// Try to get a handle on the cache in the user's default location.
    pub fn open() -> Result<Cache, LogError> {
        // XXX we don't own log2src.org
        let project_dirs =
            ProjectDirs::from("org", "log2src", "log2src").ok_or(LogError::CannotFindCache {})?;
        let location = project_dirs.cache_dir().to_path_buf();
        Ok(Cache { location })
    }

    /// The path of the entry that holds the log statements for the given source root.
    pub fn entry_path(&self, root: &Path) -> PathBuf {
        let root = root.canonicalize().unwrap_or(root.to_owned());
        self.location.join(to_cached_name(&root))
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub enum CacheEntrySchema {
    #[serde(
        rename = "https://raw.githubusercontent.com/ttiimm/log2src/refs/heads/main/schemas/cache-header-v1.json"
    )]
    V1,
}

/// The revision value is a simple way to invalidate the cache entries by changing the number.
#[derive(Serialize, Deserialize, Debug)]
pub enum Revision {
    #[serde(rename = "60")]
    Current,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum CacheEntryFormat {
    Bincode,
}

/// Header for an entry in the cache.  Currently, this is more of interest to humans than machines.
#[derive(Serialize, Deserialize, Debug)]
pub struct CacheEntryHeader {
    #[serde(rename = "$schema")]
    pub schema: CacheEntrySchema,
    pub revision: Revision,
    pub format: CacheEntryFormat,
    pub path: String,
    pub timestamp: u64,
}

fn to_write_cache_error<E>(err: E) -> LogError
where
    E: Error + Send + Sync + 'static,
{
    LogError::FailedToWriteCache {
        source: Arc::new(err),
    }
}

/// A log statement and the file it is in, which has the details shared by all of the
/// statements in the file.  This is what the matching API returns, and it serializes to a
/// self-contained description of the statement for the JSON output.
#[derive(Copy, Clone, Debug)]
pub struct StatementRef<'s> {
    pub file: &'s StatementsInFile,
    pub stmt: &'s Statement,
}

impl<'s> StatementRef<'s> {
    pub fn source_path(&self) -> &'s str {
        &self.file.path
    }

    pub fn language(&self) -> SourceLanguage {
        self.file.language
    }
}

impl Serialize for StatementRef<'_> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        let stmt = self.stmt;
        // The fields used for matching, like the segments and the kinds of the arguments, are
        // left out: they are internal, and `LogMapping::variables` has what they found.
        let mut state = serializer.serialize_struct("StatementRef", 14)?;
        state.serialize_field("sourcePath", self.source_path())?;
        state.serialize_field("language", &self.language())?;
        state.serialize_field("lineNumber", &stmt.line_no)?;
        state.serialize_field("endLineNumber", &stmt.end_line_no)?;
        state.serialize_field("column", &stmt.column)?;
        state.serialize_field("name", &stmt.name)?;
        state.serialize_field("qualifiedName", &stmt.qualified_name)?;
        state.serialize_field("blockId", &stmt.block_id)?;
        state.serialize_field("text", &stmt.text)?;
        state.serialize_field("level", &stmt.level)?;
        state.serialize_field("category", &stmt.category)?;
        state.serialize_field("callName", &stmt.call_name)?;
        state.serialize_field("pattern", &stmt.pattern_source())?;
        if !stmt.call_chain.is_empty() {
            state.serialize_field("callChain", &stmt.call_chain)?;
        }
        if !stmt.continuations.is_empty() {
            state.serialize_field("continuations", &stmt.continuations)?;
        }
        state.end()
    }
}

impl Deref for StatementRef<'_> {
    type Target = Statement;

    fn deref(&self) -> &Statement {
        self.stmt
    }
}

/// Collection of log statements in a single source file
#[derive(Debug, Serialize, Deserialize)]
pub struct StatementsInFile {
    pub path: String,
    pub language: SourceLanguage,
    id: SourceFileID,
    /// The statements with a string-literal message.  Use `statements()` to also get the ones
    /// whose message is a constant.
    log_statements: Vec<Statement>,
    /// The locations, as line and column, of the statements whose level comes from an
    /// argument, like `syslog(LOG_ERR, ...)`, instead of the name of the call.  Those levels
    /// are never pruned by `prune_log_calls()`.
    arg_levels: BTreeSet<(usize, usize)>,
    /// The statements whose message is a constant, or a concatenation with constants in it.
    /// The constants are usually defined in other files, so these are rebuilt by
    /// `SourceTree::resolve_message_refs()` instead of cached.
    #[serde(skip)]
    resolved_statements: Vec<Statement>,
    /// The statements derived from the ones in this file for calls that pass a string for a
    /// placeholder, which can be in other files, so these are rebuilt by
    /// `SourceTree::derive_call_statements()` instead of cached.  They are only used for
    /// matching, not listed with the other statements.
    #[serde(skip)]
    derived_statements: Vec<Statement>,
    /// The Linux kernel continuations without any literal text, like `pr_cont(" %s", x)` or
    /// `pr_cont("\n")`, which are not matched to log messages on their own, but are joined to
    /// the line that an earlier statement started, see `join_continued_lines()`.
    bare_continuations: Vec<Statement>,
    /// The C and C++ macros defined in this file that pass their arguments to another call.
    macros: Vec<wrappers::MacroWrapper>,
    /// The Java string constants defined in this file.
    constants: Vec<StringConstant>,
    /// The Java log calls in this file whose message is a constant.
    message_refs: Vec<MessageRef>,
    /// The Java log statements in this file whose message is a concatenation with a piece that
    /// could be a constant, like `PREFIX + ": " + name`.
    constant_concats: Vec<ConstantConcat>,
}

/// A Java log statement whose message is a concatenation with a piece that could be a
/// constant.  Until the constants are known, every piece that is not a literal is a
/// placeholder, so `LOAD_BALANCING_PREFIX + ": " + node` would be `"{}: {}"`, which matches
/// nearly anything.  See `Statement::with_constants()`.
#[derive(Debug, Serialize, Deserialize)]
struct ConstantConcat {
    stmt: Statement,
    parts: Vec<ConcatPart>,
}

impl StatementsInFile {
    /// Iterate over all of the statements, paired with the file's language and whether their
    /// level came from an argument, for `prune_log_calls()`.
    fn statements_for_pruning(
        &mut self,
    ) -> impl Iterator<Item = (&mut Statement, SourceLanguage, bool)> {
        let arg_levels = &self.arg_levels;
        let language = self.language;
        self.log_statements
            .iter_mut()
            .chain(self.resolved_statements.iter_mut())
            .map(move |stmt| {
                let from_arg = arg_levels.contains(&(stmt.line_no, stmt.column));
                (stmt, language, from_arg)
            })
    }

    /// Iterate over all of the statements, the ones with a string-literal message first.
    pub fn statements(&self) -> impl Iterator<Item = StatementRef<'_>> {
        self.log_statements
            .iter()
            .chain(self.resolved_statements.iter())
            .map(move |stmt| StatementRef { file: self, stmt })
    }

    /// Iterate over the statements that log messages are matched against, which are the ones
    /// from `statements()` followed by the derived ones.
    fn matchable_statements(&self) -> impl Iterator<Item = StatementRef<'_>> {
        self.statements().chain(
            self.derived_statements
                .iter()
                .map(move |stmt| StatementRef { file: self, stmt }),
        )
    }

    /// Get a statement by its index in `matchable_statements()`.
    fn statement(&self, index: usize) -> Option<StatementRef<'_>> {
        let resolved_start = self.log_statements.len();
        let derived_start = resolved_start + self.resolved_statements.len();
        let stmt = if index < resolved_start {
            self.log_statements.get(index)
        } else if index < derived_start {
            self.resolved_statements.get(index - resolved_start)
        } else {
            self.derived_statements.get(index - derived_start)
        }?;
        Some(StatementRef { file: self, stmt })
    }

    fn to_lookup_pair(&self) -> Option<(String, SourceFileID)> {
        PATH_TO_NAME_REGEX
            .captures(&self.path)
            .into_iter()
            .flat_map(|caps| caps.get(1))
            .map(|name_match| (name_match.as_str().to_owned(), self.id))
            .next()
    }
}

/// Collection of individual source files under a root path
#[derive(Serialize, Deserialize, Debug)]
pub struct SourceTree {
    pub tree: SourceHierTree,
    pub files_with_statements: HashMap<SourceFileID, StatementsInFile>,
    /// Most log statements only have the file name, so we keep an extra map from the name
    /// to the source file IDs to speed up matches.
    #[serde(skip)]
    pub file_name_to_sources: HashMap<String, Vec<SourceFileID>>,
    /// Finds the candidate statements for matching all of a log message: the logging calls.
    /// The prefilters are reset whenever the statements change and built the first time they
    /// are needed, since building them for a big tree takes a while and the statements usually
    /// change more than once before then, like after loading the cache and again after deriving
    /// the statements for calls through wrappers.
    #[serde(skip)]
    log_prefilter: OnceLock<Prefilter>,
    /// Finds the statements that are not logging calls that can be matched to all of a log
    /// message when no logging call matches, like a `println!()` or the message of an
    /// exception that was logged, but only when that is asked for, see
    /// [`LogMatchOptions::fallback`].
    #[serde(skip)]
    fallback_prefilter: OnceLock<Prefilter>,
    /// Finds the candidate statements for the parts of a log message, for
    /// [`message_source::best_log_source`], which only uses the ones with enough literal text.
    #[serde(skip)]
    find_prefilter: OnceLock<Prefilter>,
    /// The statements that matched log messages with a given file name and line number.  They
    /// are tried before the prefilter when another message has the same file and line.  An
    /// entry without statements is for a message that matched nothing, so the next ones with
    /// the same file and line are not looked for again.  Cleared whenever the statements change.
    #[serde(skip)]
    line_cache: RwLock<LineCache>,
    /// The source files that a file name in a log message refers to, sorted, for the names that
    /// were looked up.  A name that is not the name of any file, like a partial path, is looked
    /// for in all of the paths, which is too slow to do for every statement found by the
    /// prefilter.  Cleared whenever the statements change.
    #[serde(skip)]
    files_by_name: RwLock<HashMap<String, Arc<[SourceFileID]>>>,
    /// The prefixes that were found in front of the messages of a statement, like the device
    /// name that the Linux kernel's `dev_info()` adds, so the next message from the statement
    /// is matched without looking for the prefix again, see `learned_match()`.  Cleared
    /// whenever the statements change.
    #[serde(skip)]
    learned_prefixes: RwLock<HashMap<StatementID, Vec<LearnedPrefix>>>,
    /// The logging functions/macros/methods called by the statements under this root, keyed by
    /// the name of the call.  Rebuilt after loading/extracting.
    #[serde(skip)]
    pub log_calls: BTreeMap<String, LogCall>,
    /// The languages of the files with statements under this root.  Rebuilt with `log_calls`.
    #[serde(skip)]
    pub languages: BTreeSet<SourceLanguage>,
}

/// A logging function/macro/method, like `ws_debug` or `logger.info`, and the levels of the
/// statements that call it.
#[derive(Debug, Default, Serialize)]
pub struct LogCall {
    /// The number of statements that call it.
    pub statements: usize,
    /// The number of statements with each level, before pruning.  The level usually comes
    /// from the name of the call, but it can also come from an argument, like
    /// `syslog(LOG_ERR, ...)`.
    pub levels: BTreeMap<LogLevel, usize>,
    /// The prefix shared with other calls, like `ws` for `ws_debug`, if the level comes from
    /// a prefix that might not be a logger.  See [`LogLevel::call_family`].
    #[serde(skip_serializing_if = "Option::is_none")]
    pub family: Option<String>,
    /// True if the family does not look like logging, so the statements that got their level
    /// from the name of this call were changed to `Unknown` and `MessageCategory::Other`.
    pub pruned: bool,
}

/// Collect the calls of the statements that have a level, which are the ones identified as
/// logging.  Then, for the calls whose level comes from a prefix that might not be a logger,
/// like `ws_warning`, `luaL_error`, or `zbee_append_info`, check that the calls with the same
/// prefix have at least two levels other than `Info`.  A logger has several levels, but
/// something like `luaL_error` raises an error and `append_info` adds text to the packet info.
/// "info" and "message" are not counted since they are usually nouns.  The statements in a
/// family that fails the check have their level changed to `Unknown` and their category changed
/// to `MessageCategory::Other`.
///
/// The statements are paired with whether their level came from an argument.  Pruning can be
/// done again, like after a file changes, since a statement whose call name has a level is
/// only `Unknown` if it was pruned before, so its level is restored first.  The calls that are
/// known not to be logging, see [`MessageCategory::from_call`], are skipped.
fn prune_log_calls(
    mut stmts: Vec<(&mut Statement, SourceLanguage, bool)>,
) -> BTreeMap<String, LogCall> {
    // The level from the name of each call, which only needs to be computed once per name.
    let mut name_levels: HashMap<String, Option<LogLevel>> = HashMap::new();
    let mut log_calls: BTreeMap<String, LogCall> = BTreeMap::new();
    for (stmt, language, from_arg) in stmts.iter_mut() {
        let Some(call_name) = stmt.call_name.as_deref() else {
            continue;
        };
        if MessageCategory::from_call(stmt, *language).is_some() {
            // A call that is known not to be logging, like `Err(...)`, is never counted.
            continue;
        }
        if stmt.level == LogLevel::Unknown && !*from_arg {
            let name_level = match name_levels.get(call_name) {
                Some(level) => *level,
                None => {
                    let level = LogLevel::from_name(call_name);
                    name_levels.insert(call_name.to_string(), level);
                    level
                }
            };
            if let Some(level) = name_level {
                stmt.level = level;
            }
        }
        if stmt.level == LogLevel::Unknown {
            continue;
        }
        if !log_calls.contains_key(call_name) {
            log_calls.insert(
                call_name.to_string(),
                LogCall {
                    family: LogLevel::call_family(call_name),
                    ..LogCall::default()
                },
            );
        }
        let log_call = log_calls.get_mut(call_name).unwrap();
        log_call.statements += 1;
        *log_call.levels.entry(stmt.level).or_default() += 1;
    }
    let mut family_levels: HashMap<&str, BTreeSet<LogLevel>> = HashMap::new();
    for log_call in log_calls.values() {
        if let Some(family) = &log_call.family {
            family_levels.entry(family.as_str()).or_default().extend(
                log_call
                    .levels
                    .keys()
                    .filter(|level| **level != LogLevel::Info),
            );
        }
    }
    let pruned_families: HashSet<String> = family_levels
        .into_iter()
        .filter(|(_, levels)| levels.len() < 2)
        .map(|(family, _)| family.to_string())
        .collect();
    for log_call in log_calls.values_mut() {
        log_call.pruned = log_call
            .family
            .as_ref()
            .is_some_and(|family| pruned_families.contains(family));
    }
    for (stmt, language, from_arg) in stmts.iter_mut() {
        if stmt.category_from_use {
            continue;
        }
        stmt.category = MessageCategory::Log;
        // A level from an argument, like `syslog(LOG_ERR, ...)`, is kept.
        if *from_arg {
            continue;
        }
        let pruned = stmt
            .call_name
            .as_deref()
            .and_then(|call_name| log_calls.get(call_name))
            .is_some_and(|log_call| log_call.pruned);
        if pruned {
            stmt.level = LogLevel::Unknown;
            stmt.category = MessageCategory::Other;
        } else {
            stmt.category = MessageCategory::classify(stmt, *language);
        }
    }
    log_calls
}

/// The most file names that `SourceTree::files_by_name` remembers.
const MAX_FILES_BY_NAME: usize = 4096;

/// Maps the source file that the file name in a log message refers to, and the message's line
/// number, to the statements that matched it.  No statements means that a message with that
/// file and line matched nothing without [`LogMatchOptions::fallback`], see
/// `LogMatcher::known_unmatched()`.
type LineCache = HashMap<(SourceFileID, usize), Vec<StatementID>>;

/// A prefix that was found in front of a message from a statement, see
/// `SourceTree::learned_prefixes`.  Only the separator is kept, since the prefix itself is
/// different for each message, like the name of the device.
#[derive(Debug)]
struct LearnedPrefix {
    /// The text between the prefix and the statement's text, like `": "`.
    separator: String,
}

/// A statement that a log message was matched to with a prefix in front of it, from
/// `LogMatcher::explain_log_body()`, so the prefix can be learned.
struct Learnable<'s> {
    tree: &'s SourceTree,
    id: StatementID,
}

/// The outcome of resolving the log calls that use message constants.
#[derive(Default)]
struct MessageRefSummary {
    resolved: usize,
    /// The constant could not be found, e.g. it is defined in a library.
    not_found: usize,
    /// The constant has no literal text to match, like "{}".
    no_text: usize,
}

impl SourceTree {
    /// Turn the log calls whose message is a constant into statements.  The constants are
    /// usually defined in other files, so this needs to be redone whenever any file changes.
    fn resolve_message_refs(&mut self) -> MessageRefSummary {
        // Sort by path so the same definition wins when a constant name is duplicated.
        let mut files: Vec<&StatementsInFile> = self.files_with_statements.values().collect();
        files.sort_by(|lhs, rhs| lhs.path.cmp(&rhs.path));
        let constants =
            java_symbols::constants_by_name(files.into_iter().flat_map(|sif| sif.constants.iter()));
        let mut summary = MessageRefSummary::default();
        for sif in self.files_with_statements.values_mut() {
            sif.resolved_statements.clear();
            for message_ref in &sif.message_refs {
                let Some(value) = java_symbols::resolve(message_ref, &constants) else {
                    summary.not_found += 1;
                    continue;
                };
                match Statement::from_message_ref(message_ref, value) {
                    Some(src_ref) => {
                        sif.resolved_statements.push(src_ref);
                        summary.resolved += 1;
                    }
                    None => summary.no_text += 1,
                }
            }
            for concat in &sif.constant_concats {
                if let Some(src_ref) =
                    concat
                        .stmt
                        .with_constants(&concat.parts, &constants, sif.language)
                {
                    sif.resolved_statements.push(src_ref);
                }
            }
        }
        summary
    }

    /// Collect the logging calls under this root and prune the levels of the ones that don't
    /// look like logging, see `prune_log_calls()`.  This needs to be redone whenever any file
    /// changes, since the decision depends on the calls in all of the files.
    fn prune_log_calls(&mut self) {
        let stmts = self
            .files_with_statements
            .values_mut()
            .flat_map(|sif| sif.statements_for_pruning())
            .collect();
        self.log_calls = prune_log_calls(stmts);
        self.languages = self
            .files_with_statements
            .values()
            .filter(|sif| sif.statements().next().is_some())
            .map(|sif| sif.language)
            .collect();
    }

    fn rebuild_prefilter(&mut self) {
        self.log_prefilter = OnceLock::new();
        self.fallback_prefilter = OnceLock::new();
        self.find_prefilter = OnceLock::new();
        // The statement IDs in the cache may now refer to different statements.
        self.line_cache
            .get_mut()
            .unwrap_or_else(PoisonError::into_inner)
            .clear();
        self.files_by_name
            .get_mut()
            .unwrap_or_else(PoisonError::into_inner)
            .clear();
        self.learned_prefixes
            .get_mut()
            .unwrap_or_else(PoisonError::into_inner)
            .clear();
    }

    /// Remember that a message from the statement had a prefix in front of it that ended with
    /// `separator`, see `learned_match()`.
    fn learn_prefix(&self, id: StatementID, separator: &str) {
        let known = |learned: &HashMap<StatementID, Vec<LearnedPrefix>>| {
            learned
                .get(&id)
                .is_some_and(|prefixes| prefixes.iter().any(|lp| lp.separator == separator))
        };
        if known(
            &self
                .learned_prefixes
                .read()
                .unwrap_or_else(PoisonError::into_inner),
        ) {
            return;
        }
        let mut learned = self
            .learned_prefixes
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        if !known(&learned) {
            learned.entry(id).or_default().push(LearnedPrefix {
                separator: separator.to_string(),
            });
        }
    }

    /// Find the statement for a log message whose text is after a prefix, like an earlier
    /// message from the statement had, so the prefix does not have to be looked for again by
    /// `LogMatcher::explain_log_body()`.  Each place after the separator is tried, see
    /// `message_source::learned_prefix_starts()`.  The prefix has to end like one, see
    /// `message_source::prefix_end()`, and the statement has to explain enough of the rest of the
    /// message, the same as when the whole message is matched, or else the message is left to be
    /// read the slow way, which could find a better reading of it.  Returns the statement, where
    /// its text starts in the trimmed body, and the score of the reading, the same as
    /// `message_source::best_log_source()` would give it without the values, so it can be
    /// compared the same way.  Like the line cache, this depends on the messages that were
    /// matched before, so a reading that the slow way would prefer, like a chain of messages,
    /// can be missed.  Without `fallback`, only logging calls are used, see
    /// [`LogMatchOptions::fallback`].
    fn learned_match(
        &self,
        log_ref: &LogRef,
        fallback: bool,
    ) -> Option<(StatementRef<'_>, usize, Quality)> {
        let learned = self
            .learned_prefixes
            .read()
            .unwrap_or_else(PoisonError::into_inner);
        if learned.is_empty() {
            return None;
        }
        let body = log_ref.body().trim();
        let lineno = log_ref.details.as_ref().and_then(|details| details.lineno);
        let level = log_ref.level();
        // The prefix was learned from a reading by `explain_log_body()`, which only uses the
        // statements in this prefilter, found in the head of the message.
        let prefilter = self.find_prefilter();
        let mut candidates: Vec<(StatementID, StatementRef)> = self
            .prefiltered_candidates(prefilter, log_ref, message_source::log_head(body))
            .into_iter()
            .filter(|(id, src_ref)| {
                learned.contains_key(id) && (fallback || src_ref.category == MessageCategory::Log)
            })
            .collect();
        candidates.sort_by_cached_key(|((file_id, _), src_ref)| {
            candidate_key(src_ref, prefilter.rank(*file_id), lineno, level)
        });
        candidates.into_iter().find_map(|(id, src_ref)| {
            learned.get(&id)?.iter().find_map(|lp| {
                message_source::learned_prefix_starts(body, &lp.separator).find_map(|start| {
                    let rest = &body[start..];
                    match_stats::record_pattern_check();
                    if !src_ref.pattern().is_match(rest) || !explains_enough(Some(&src_ref), rest) {
                        return None;
                    }
                    let score = if src_ref.values_fit_kinds(src_ref.pattern(), rest) {
                        src_ref.quality
                    } else {
                        Quality::ZERO
                    };
                    Some((src_ref, start, score))
                })
            })
        })
    }

    /// The source files that the file name in a log message refers to: the ones with that name,
    /// or else the ones whose path contains it, or else, for a path from another machine, like
    /// the build directory in a `file!()`, the ones that share the longest trailing run of
    /// components with it.
    fn files_named(&self, name: &str) -> Arc<[SourceFileID]> {
        if let Some(ids) = self
            .files_by_name
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .get(name)
        {
            return ids.clone();
        }
        let mut ids: Vec<SourceFileID> = match self.file_name_to_sources.get(name) {
            Some(ids) => ids.clone(),
            None => self
                .files_with_statements
                .values()
                .filter(|sif| sif.path.contains(name))
                .map(|sif| sif.id)
                .collect(),
        };
        if ids.is_empty() && Path::new(name).has_root() {
            ids = self.files_with_path_suffix(name);
        }
        ids.sort_unstable();
        let ids: Arc<[SourceFileID]> = ids.into();
        let mut cache = self
            .files_by_name
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        // A long-running reader can see all sorts of file names, like temporary paths, so the
        // cache is started over instead of growing without a limit.
        if cache.len() >= MAX_FILES_BY_NAME {
            cache.clear();
        }
        cache.insert(name.to_string(), ids.clone());
        ids
    }

    /// The source files that share the most trailing components with `path`, if they share at
    /// least the file name, like the ones for an absolute path from the machine a log came from.
    fn files_with_path_suffix(&self, path: &str) -> Vec<SourceFileID> {
        let names: Vec<_> = Path::new(path)
            .components()
            .filter_map(|comp| match comp {
                Component::Normal(name) => Some(name),
                _ => None,
            })
            .collect();
        let mut best = 0;
        let mut ids = Vec::new();
        for sif in self.files_with_statements.values() {
            let matched = Path::new(&sif.path)
                .components()
                .rev()
                .zip(names.iter().rev())
                .take_while(|(comp, name)| comp.as_os_str() == **name)
                .count();
            if matched == 0 || matched < best {
                continue;
            }
            if matched > best {
                best = matched;
                ids.clear();
            }
            ids.push(sif.id);
        }
        ids
    }

    /// The line cache key for a log message, if it has a file name and line number and the
    /// file name refers to a single source file: that file and the line number.  Messages for
    /// file names shared by several source files are not cached, since a statement in one could
    /// hide a better match in another.
    fn line_cache_key(&self, log_ref: &LogRef) -> Option<(SourceFileID, usize)> {
        let (filename, lineno) = log_ref.file_and_line()?;
        match self.file_name_to_sources.get(filename)?.as_slice() {
            [id] => Some((*id, lineno)),
            _ => None,
        }
    }

    /// What the line cache knows about matching a log message in this tree without
    /// [`LogMatchOptions::fallback`]: `Some(true)` if an earlier message with the same file and
    /// line matched nothing, `Some(false)` if the message's file name refers to no files here,
    /// so nothing here can match it, and `None` if it has to be looked for.
    fn known_unmatched(&self, log_ref: &LogRef) -> Option<bool> {
        let (filename, _) = log_ref.file_and_line()?;
        if let Some(key) = self.line_cache_key(log_ref) {
            let cache = self
                .line_cache
                .read()
                .unwrap_or_else(PoisonError::into_inner);
            return cache.get(&key).filter(|ids| ids.is_empty()).map(|_| true);
        }
        self.files_named(filename).is_empty().then_some(false)
    }

    /// Remember that a log message matched nothing, if it has a file name and line number that
    /// can be cached and no earlier message with them matched anything.  An entry with
    /// statements is left alone, since those may match the next message.
    fn remember_unmatched(&self, log_ref: &LogRef) {
        if let Some(key) = self.line_cache_key(log_ref) {
            self.line_cache
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .entry(key)
                .or_default();
        }
    }

    /// Find the highest quality statement that previously matched a log message with the same
    /// file name and line number as this one, and matches this one too.  Without `fallback`,
    /// only logging calls are used, see [`LogMatchOptions::fallback`].
    fn find_cached_match(
        &self,
        log_ref: &LogRef,
        fallback: bool,
    ) -> Option<(StatementRef<'_>, bool)> {
        let key = self.line_cache_key(log_ref)?;
        let lineno = key.1;
        let body = log_ref.body();
        let cache = self
            .line_cache
            .read()
            .unwrap_or_else(PoisonError::into_inner);
        let candidates = cache
            .get(&key)?
            .iter()
            .filter_map(|(file_id, index)| {
                self.files_with_statements.get(file_id)?.statement(*index)
            })
            .filter(|src_ref| fallback || src_ref.category == MessageCategory::Log)
            .sorted_by(|lhs, rhs| compare_candidates(lhs, rhs, Some(lineno), log_ref.level()));
        let found = first_match_full(candidates, body, Some(lineno), |src_ref| src_ref.stmt);
        if found.is_some() {
            match_stats::record_line_cache_hit();
        }
        found
    }

    /// Find the highest quality statement that matches the given log message, preferring the one
    /// closest to the message's line number for a tie.  The logging calls are tried first, and
    /// then, with `fallback`, the other statements, see [`LogMatchOptions::fallback`].  This is
    /// the same as [`first_match`] with all of them in order, since it only goes on to the
    /// statements that are not logging calls when none of the logging calls match.  If the
    /// message has a file name and line number, the statement is added to the cache for them.
    fn find_best_match(
        &self,
        log_ref: &LogRef,
        fallback: bool,
    ) -> Option<(StatementRef<'_>, bool)> {
        let ((stmt_id, src_ref), without_empty_values) = self
            .first_match_in(self.log_prefilter(), log_ref)
            .or_else(|| {
                fallback
                    .then(|| self.first_match_in(self.fallback_prefilter(), log_ref))
                    .flatten()
            })?;
        if let Some(key) = self.line_cache_key(log_ref) {
            let mut cache = self
                .line_cache
                .write()
                .unwrap_or_else(PoisonError::into_inner);
            let ids = cache.entry(key).or_default();
            if !ids.contains(&stmt_id) {
                ids.push(stmt_id);
            }
        }
        Some((src_ref, without_empty_values))
    }

    /// The [`first_match`] for a log message of the statements in `prefilter`.
    fn first_match_in(
        &self,
        prefilter: &Prefilter,
        log_ref: &LogRef,
    ) -> Option<((StatementID, StatementRef<'_>), bool)> {
        let body = log_ref.body();
        let lineno = log_ref.details.as_ref().and_then(|details| details.lineno);
        let level = log_ref.level();
        let mut candidates = self.prefiltered_candidates(prefilter, log_ref, body);
        match_stats::record_prefilter_candidates(candidates.len());
        // A long message, like a JSON object, has the key literals of a lot of the statements, so
        // they are ordered by a key, instead of by comparing their paths over and over.
        candidates.sort_by_cached_key(|((file_id, _), src_ref)| {
            candidate_key(src_ref, prefilter.rank(*file_id), lineno, level)
        });
        debug_assert!(candidates.is_sorted_by(|lhs, rhs| {
            compare_candidates(&lhs.1, &rhs.1, lineno, level) != Ordering::Greater
        }));
        first_match_full(candidates, body, lineno, |(_, src_ref)| src_ref.stmt)
    }

    /// The prefilter for matching all of a log message, which is built if it has not been yet.
    fn log_prefilter(&self) -> &Prefilter {
        self.log_prefilter.get_or_init(|| {
            Prefilter::new(self.files_with_statements.values(), |stmt| {
                stmt.category == MessageCategory::Log
            })
        })
    }

    /// The prefilter for matching all of a log message to a statement that is not a logging
    /// call, which is built if it has not been yet.  It is not built with the others, since it is
    /// only used when asked for.
    fn fallback_prefilter(&self) -> &Prefilter {
        self.fallback_prefilter.get_or_init(|| {
            Prefilter::new(self.files_with_statements.values(), |stmt| {
                stmt.category != MessageCategory::Log && has_fallback_quality(stmt)
            })
        })
    }

    /// The prefilter for the parts of a log message, which is built if it has not been yet.
    fn find_prefilter(&self) -> &Prefilter {
        self.find_prefilter.get_or_init(|| {
            Prefilter::new(self.files_with_statements.values(), |stmt| {
                has_fallback_quality(stmt)
            })
        })
    }

    /// The statements in `prefilter` that might match some or all of `text`, which is the body
    /// of the log message or the start of it, since their key literal is in it, limited to the
    /// source files with the message's file name, if it has one.  A statement that matches part
    /// of the text has its key literal in that part, so these are also the candidates for the
    /// parts of a message, like the value of a placeholder or the text after a prefix.
    fn prefiltered_candidates(
        &self,
        prefilter: &Prefilter,
        log_ref: &LogRef,
        text: &str,
    ) -> Vec<(StatementID, StatementRef<'_>)> {
        let mut candidates = Vec::new();
        let file_ids = match log_ref.details {
            Some(LogDetails {
                file: Some(filename),
                ..
            }) => Some(self.files_named(filename)),
            _ => None,
        };
        // None of the statements are in the message's file, like one from a library.
        if file_ids.as_ref().is_some_and(|ids| ids.is_empty()) {
            return candidates;
        }
        prefilter.candidates(text, |(file_id, index)| {
            if file_ids
                .as_ref()
                .is_some_and(|ids| ids.binary_search(&file_id).is_err())
            {
                return;
            }
            if let Some(stmt) = self
                .files_with_statements
                .get(&file_id)
                .and_then(|sif| sif.statement(index))
            {
                candidates.push(((file_id, index), stmt));
            }
        });
        candidates
    }
}

/// Check if a C or C++ file is a header, which can be included by other files.
fn is_c_header(path: &str) -> bool {
    Path::new(path)
        .extension()
        .and_then(OsStr::to_str)
        .is_some_and(|ext| matches!(ext, "h" | "hh" | "hpp" | "hxx" | "tpp" | "inc"))
}

/// The most macros and functions to follow from a call to the statement that prints its message.
const MAX_WRAPPER_DEPTH: usize = 6;

/// The most continuations of a line that are in a different block than the statement that
/// starts it, like in an `if`, which can be left out of the line.  Every combination of them is
/// tried, so there are up to 2^N statements for a line.
const MAX_OPTIONAL_CONTINUATIONS: usize = 6;

/// Derive the statements for the lines in the Linux kernel that are printed by a statement and
/// then continued by the `pr_cont()` or `printk(KERN_CONT ...)` calls after it in the same
/// function, like
///
/// ```c
/// pr_info("Console: switching ");
/// if (!deflt)
///     pr_cont("consoles %d-%d ", first + 1, last + 1);
/// pr_cont("to %s\n", desc);
/// ```
///
/// The continuations in the same block as the start are always printed, but the others, like
/// in an `if` or a loop, might not be, so a statement is derived for each combination of them,
/// up to the first one that ends the line.  Whether the branches of an `if` exclude each other
/// is not known, so some of the combinations cannot happen.  A loop that prints a continuation more than once
/// is not handled.  The start can also be one of the statements derived for a wrapper, like
/// the one with the prefix from `pr_fmt()`.  See `Statement::join()`.
fn join_continued_lines(sif: &StatementsInFile) -> Vec<Statement> {
    let mut order: Vec<&Statement> = sif
        .log_statements
        .iter()
        .chain(&sif.bare_continuations)
        .collect();
    order.sort_by_key(|stmt| (stmt.line_no, stmt.column));
    let mut lines: Vec<(&Statement, Vec<&Statement>)> = vec![];
    let mut current: Option<(&Statement, Vec<&Statement>)> = None;
    for stmt in order {
        if current
            .as_ref()
            .is_some_and(|(start, _)| start.qualified_name != stmt.qualified_name)
        {
            lines.extend(current.take());
        }
        if stmt.is_continuation() {
            if let Some((start, conts)) = current.as_mut() {
                conts.push(stmt);
                if stmt.block_id == start.block_id && stmt.ends_line() {
                    lines.extend(current.take());
                }
            }
        } else if stmt.is_kernel_print() {
            // Any other print starts a new line, even if the last one was not ended.
            lines.extend(current.take());
            if !stmt.ends_line() {
                current = Some((stmt, vec![]));
            }
        }
    }
    lines.extend(current);

    let mut joined = vec![];
    for (start, conts) in lines {
        if conts.is_empty() {
            continue;
        }
        let mut optional = 0;
        let conts: Vec<(&Statement, bool)> = conts
            .into_iter()
            .filter_map(|cont| {
                if cont.block_id == start.block_id {
                    Some((cont, false))
                } else if optional < MAX_OPTIONAL_CONTINUATIONS {
                    optional += 1;
                    Some((cont, true))
                } else {
                    None
                }
            })
            .collect();
        let starts = std::iter::once(start).chain(sif.derived_statements.iter().filter(|stmt| {
            stmt.line_no == start.line_no
                && stmt.column == start.column
                && stmt.continuations.is_empty()
        }));
        let starts: Vec<&Statement> = starts.collect();
        let mut seen: HashSet<Vec<(usize, usize)>> = HashSet::new();
        for mask in 0..(1usize << optional) {
            let mut bit = 0;
            let mut chosen: Vec<&Statement> = conts
                .iter()
                .filter(|(_, is_optional)| {
                    if *is_optional {
                        bit += 1;
                        mask & (1 << (bit - 1)) != 0
                    } else {
                        true
                    }
                })
                .map(|(cont, _)| *cont)
                .collect();
            // The line ends at the first continuation that ends it, and the rest are a line
            // of their own.
            if let Some(end) = chosen.iter().position(|cont| cont.ends_line()) {
                chosen.truncate(end + 1);
            }
            let key = chosen
                .iter()
                .map(|cont| (cont.line_no, cont.column))
                .collect();
            if chosen.is_empty() || !seen.insert(key) {
                continue;
            }
            joined.extend(starts.iter().filter_map(|start| start.join(&chosen)));
        }
    }
    joined
}

/// The C and C++ wrappers that a message can go through, see `LogMatcher::link_statements()`.
struct Wrappers<'s> {
    macros: HashMap<&'s str, Vec<(&'s StatementsInFile, &'s wrappers::MacroWrapper)>>,
    /// The statements with placeholders, by the name of the function they are in.
    functions: HashMap<&'s str, Vec<(&'s StatementsInFile, &'s Statement)>>,
}

impl<'s> Wrappers<'s> {
    /// The definitions with the name that a call in the file uses.  A definition in the file
    /// with the call wins, like a `pr_fmt` that a file defines before it includes the headers.
    /// Otherwise, the definitions have to be in a single file, or else in a single header, like
    /// the default `pr_fmt` in `printk.h` when several files define their own, since it is not
    /// known which one is used.  A macro is only seen by the file it is defined in and the ones
    /// that include it, so, when `file_scoped`, the single file has to be a header.
    fn pick<T: Copy>(
        defs: Option<&Vec<(&'s StatementsInFile, T)>>,
        call_site: &StatementsInFile,
        file_scoped: bool,
    ) -> Vec<(&'s StatementsInFile, T)> {
        let Some(defs) = defs else {
            return vec![];
        };
        // The IDs of files are only unique within a root, and the definitions can be in any root.
        let in_call_site: Vec<_> = defs
            .iter()
            .filter(|(sif, _)| std::ptr::eq(*sif, call_site))
            .copied()
            .collect();
        if !in_call_site.is_empty() {
            return in_call_site;
        }
        if !file_scoped && defs.iter().map(|(sif, _)| &sif.path).all_equal() {
            return defs.clone();
        }
        let in_headers: Vec<_> = defs
            .iter()
            .filter(|(sif, _)| is_c_header(&sif.path))
            .copied()
            .collect();
        if !in_headers.is_empty() && in_headers.iter().map(|(sif, _)| &sif.path).all_equal() {
            return in_headers;
        }
        vec![]
    }

    /// The macros with the name that a call in the file can use, see `pick()`.
    fn pick_macros(
        &self,
        name: &str,
        call_site: &StatementsInFile,
    ) -> Vec<(&'s StatementsInFile, &'s wrappers::MacroWrapper)> {
        Self::pick(self.macros.get(name), call_site, true)
    }

    fn frame(path: &str, wrapper: &wrappers::MacroWrapper, parameter: &str) -> ChainFrame {
        ChainFrame {
            source_path: path.to_string(),
            line_number: wrapper.line_no,
            column: wrapper.column,
            name: wrapper.name.clone(),
            call_name: wrapper.callee().unwrap_or_default().to_string(),
            text: wrapper.text.clone(),
            parameter: parameter.to_string(),
        }
    }

    /// The statements derived for a call whose message goes through wrappers that change it.
    fn link(&self, call: &Statement, sif: &'s StatementsInFile) -> Vec<Statement> {
        let (Some(position), Some(callee)) = (call.arg_position, call.call_name.as_deref()) else {
            return vec![];
        };
        // A text macro, like `pr_fmt`, following aliases, like `#define dev_fmt pr_fmt`.
        let lookup = |name: &str| {
            let mut name = name;
            for _ in 0..MAX_WRAPPER_DEPTH {
                let defs = self.pick_macros(name, sif);
                if let Some((def_file, wrapper)) =
                    defs.iter().find(|(_, wrapper)| wrapper.is_text())
                {
                    return Some((def_file.path.as_str(), *wrapper));
                }
                match defs.iter().find_map(|(_, wrapper)| match &wrapper.body {
                    wrappers::MacroBody::Alias(target) => Some(target.as_str()),
                    _ => None,
                }) {
                    Some(target) => name = target,
                    None => return None,
                }
            }
            None
        };
        let mut position = position as usize;
        let mut name = callee;
        let mut frames: Vec<ChainFrame> = vec![];
        let mut prefix = String::new();
        let mut suffix = String::new();
        let mut last_macro: Option<&wrappers::MacroWrapper> = None;
        for _ in 0..MAX_WRAPPER_DEPTH {
            let defs: Vec<_> = self
                .pick_macros(name, sif)
                .into_iter()
                .filter(|(_, wrapper)| wrapper.callee().is_some())
                .collect();
            let mut applied = vec![];
            let Some((def_file, wrapper, forward)) = defs.iter().find_map(|(def_file, wrapper)| {
                let forward = wrapper.forward(position, &lookup, &mut applied)?;
                Some((*def_file, *wrapper, forward))
            }) else {
                if !defs.is_empty() {
                    // The macro changes the message in a way that is not known, so the text
                    // around it is not known either.
                    return vec![];
                }
                let derived = self.link_function(
                    call, name, position, sif, &frames, &prefix, &suffix, last_macro,
                );
                if !derived.is_empty() {
                    return derived;
                }
                break;
            };
            frames.push(Self::frame(
                &def_file.path,
                wrapper,
                &wrapper.params[position],
            ));
            for (path, text_macro) in applied {
                frames.push(Self::frame(path, text_macro, &text_macro.params[0]));
            }
            prefix = format!("{}{}", forward.prefix, prefix);
            suffix.push_str(&forward.suffix);
            position = forward.position;
            name = wrapper.callee().unwrap_or_default();
            last_macro = Some(wrapper);
        }
        if prefix.is_empty() && suffix.is_empty() {
            // The macros only pass the message on, so the call already matches it.
            return vec![];
        }
        vec![call.with_affixes(&prefix, &suffix, frames)]
    }

    /// The statements derived for a call whose message is passed to a function with a
    /// statement that prints it.
    #[allow(clippy::too_many_arguments)]
    fn link_function(
        &self,
        call: &Statement,
        name: &str,
        position: usize,
        call_site: &StatementsInFile,
        frames: &[ChainFrame],
        prefix: &str,
        suffix: &str,
        last_macro: Option<&wrappers::MacroWrapper>,
    ) -> Vec<Statement> {
        let mut retval = vec![];
        for (def_file, inner) in Self::pick(self.functions.get(name), call_site, false) {
            let params = source_ref::c_parameter_names(&inner.name);
            let Some(param) = params.get(position).filter(|param| !param.is_empty()) else {
                continue;
            };
            let exprs = inner.arg_exprs();
            let specs = inner.c_placeholder_specs();
            let is_format = source_ref::c_is_variadic(&inner.name) && position + 2 == params.len();
            let placeholder = if is_format {
                // The format string of a variadic function, printed with the arguments by
                // the Linux kernel's `%pV`.
                specs.and_then(|specs| specs.iter().position(|spec| spec.ends_with("pV")))
            } else if call.kinds.is_empty() && inner.category == MessageCategory::Log {
                // A string printed with `%s` by a log statement.
                exprs.iter().enumerate().position(|(index, expr)| {
                    expr.trim() == param
                        && specs
                            .as_ref()
                            .and_then(|specs| specs.get(index))
                            .is_some_and(|spec| spec.ends_with('s'))
                })
            } else {
                None
            };
            let Some(placeholder) = placeholder else {
                continue;
            };
            let param_index = |expr: &str| {
                let expr = expr.trim();
                params
                    .iter()
                    .position(|param| !param.is_empty() && param == expr)
            };
            // A Linux kernel level, like `KERN_INFO`, is taken out of the message by printk().
            let empty = exprs
                .iter()
                .enumerate()
                .filter(|(index, expr)| {
                    *index != placeholder
                        && param_index(expr)
                            .and_then(|pos| last_macro?.constant_arg(pos))
                            .is_some_and(wrappers::is_kernel_log_level)
                })
                .map(|(index, _)| index)
                .collect();
            // Without a macro in between, the arguments after the message are the call's.
            let caller_exprs = exprs
                .iter()
                .map(|expr| {
                    if !frames.is_empty() {
                        return None;
                    }
                    let pos = param_index(expr).filter(|pos| *pos > position)?;
                    call.trailing_args().get(pos - position - 1).cloned()
                })
                .collect();
            let mut frames = frames.to_vec();
            frames.push(ChainFrame {
                source_path: def_file.path.clone(),
                line_number: inner.line_no,
                column: inner.column,
                name: inner.name.clone(),
                call_name: inner.call_name.clone().unwrap_or_default(),
                text: inner.text.clone(),
                parameter: param.clone(),
            });
            retval.extend(call.splice(&Splice {
                inner,
                placeholder,
                prefix: prefix.to_string(),
                suffix: suffix.to_string(),
                empty,
                caller_exprs,
                frames,
            }));
        }
        retval
    }
}

/// The least fraction of the non-whitespace text in a log message that the literal text of the
/// statement matched to it has to cover, as a percentage, before other readings of the message
/// are tried, like one with a prefix that is not from the source.
const MIN_EXPLAINED_PERCENT: usize = 50;

/// Check if the statement matched to a log message explains enough of the message that other
/// readings of it are not needed.
fn explains_enough(best: Option<&StatementRef>, body: &str) -> bool {
    let Some(best) = best else {
        return false;
    };
    let total = body.chars().filter(|c| !c.is_whitespace()).count();
    best.quality.total() * 100 >= total * MIN_EXPLAINED_PERCENT
}

/// Find the first of the ordered candidates whose statement matches `body`.  A statement that
/// only matches with an empty value for a placeholder is passed over for a later candidate that
/// matches without one, even a lower quality one, since a missing value is less likely than the
/// line coming from a different statement.  The exception is when the statement is closer to
/// the line number in the log message, which is better evidence than the values.  The
/// candidates are ordered by [`MessageCategory::match_priority`] first, and a later tier is only
/// searched when nothing in an earlier tier matched, even with an empty value.  Statements that
/// are not `Log` need [`MIN_FALLBACK_QUALITY`], since there are a lot of them, like
/// `format!("{}/{}", dir, name)`, and they would match lines that are not from this source.
fn first_match<'a, T>(
    candidates: impl IntoIterator<Item = T>,
    body: &str,
    lineno: Option<usize>,
    src_ref: impl Fn(&T) -> &'a Statement,
) -> Option<T> {
    first_match_full(candidates, body, lineno, src_ref).map(|(candidate, _)| candidate)
}

/// [`first_match`], and whether the candidate matched without an empty value, so the choice can
/// be made again between the matches from several roots without matching them again, see
/// [`choose_match`].
fn first_match_full<'a, T>(
    candidates: impl IntoIterator<Item = T>,
    body: &str,
    lineno: Option<usize>,
    src_ref: impl Fn(&T) -> &'a Statement,
) -> Option<(T, bool)> {
    choose_match(candidates, lineno, &src_ref, |candidate| {
        let stmt = src_ref(candidate);
        match_stats::record_pattern_check();
        stmt.pattern()
            .is_match(body)
            .then(|| stmt.matches_without_empty_values(body))
    })
}

/// The choice made by [`first_match`] among the ordered candidates, where `matches` says if a
/// candidate matches the message, and if so, whether it does without an empty value.
fn choose_match<'a, T>(
    candidates: impl IntoIterator<Item = T>,
    lineno: Option<usize>,
    src_ref: impl Fn(&T) -> &'a Statement,
    mut matches: impl FnMut(&T) -> Option<bool>,
) -> Option<(T, bool)> {
    let mut with_empty_value: Option<T> = None;
    for candidate in candidates {
        let stmt = src_ref(&candidate);
        if with_empty_value.as_ref().is_some_and(|prior| {
            src_ref(prior).category.match_priority() < stmt.category.match_priority()
        }) {
            break;
        }
        if stmt.category != MessageCategory::Log && !has_fallback_quality(stmt) {
            continue;
        }
        let Some(without_empty_values) = matches(&candidate) else {
            continue;
        };
        if without_empty_values {
            return match with_empty_value {
                Some(prior)
                    if line_distance(src_ref(&prior), lineno) < line_distance(stmt, lineno) =>
                {
                    Some((prior, false))
                }
                _ => Some((candidate, true)),
            };
        }
        with_empty_value.get_or_insert(candidate);
    }
    with_empty_value.map(|candidate| (candidate, false))
}

/// The least amount of literal text, not counting whitespace, for a statement that is not `Log` to
/// be matched to a log message.
const MIN_FALLBACK_QUALITY: usize = 5;

/// The least amount of alphanumeric literal text for a statement that is not `Log` to be matched
/// to a log message, so one that only joins values with punctuation, like
/// `format!("{}/{}.{}", dir, name, ext)`, is not used.
const MIN_FALLBACK_ALNUM: usize = 3;

/// Check if a statement has enough literal text to be used even when it is not `Log`, see
/// [`MIN_FALLBACK_QUALITY`] and [`MIN_FALLBACK_ALNUM`].
fn has_fallback_quality(stmt: &Statement) -> bool {
    stmt.quality.total() >= MIN_FALLBACK_QUALITY && stmt.quality.alnum >= MIN_FALLBACK_ALNUM
}

/// How far a statement is from the line number in a log message, or zero if there is none.
fn line_distance(src_ref: &Statement, lineno: Option<usize>) -> usize {
    lineno.map_or(0, |lineno| {
        if lineno < src_ref.line_no {
            src_ref.line_no - lineno
        } else {
            lineno.saturating_sub(src_ref.end_line_no)
        }
    })
}

/// Order the candidate statements for a log message from best to worst.  `Log` statements are
/// better than the other categories, so those are only a fallback.  Then, higher quality is
/// better and, for the same quality, a statement with the same level as the log message, and
/// then one closer to the line number in the log message.  The line number is only a
/// tie-breaker since it is not always the line of the log call, like for a message built in a
/// lambda.  Then, a statement with fewer placeholders is better.  Any remaining tie goes to the
/// earliest location in the source so that the choice does not depend on the order the
/// candidates were found in.
fn compare_candidates(
    lhs: &StatementRef,
    rhs: &StatementRef,
    lineno: Option<usize>,
    level: Option<LogLevel>,
) -> Ordering {
    let distance = |src_ref: &StatementRef| line_distance(src_ref, lineno);
    let level_matches = |src_ref: &StatementRef| level == Some(src_ref.level);
    lhs.category
        .match_priority()
        .cmp(&rhs.category.match_priority())
        .then_with(|| rhs.quality.cmp(&lhs.quality))
        .then_with(|| level_matches(rhs).cmp(&level_matches(lhs)))
        .then_with(|| distance(lhs).cmp(&distance(rhs)))
        // A placeholder can be empty, so a message like "Done" matches both "Done" and "Done{}".
        .then_with(|| lhs.kinds.len().cmp(&rhs.kinds.len()))
        .then_with(|| {
            (lhs.source_path(), lhs.line_no, lhs.column).cmp(&(
                rhs.source_path(),
                rhs.line_no,
                rhs.column,
            ))
        })
}

/// The key that orders candidates in a single root the same as [`compare_candidates`], where
/// `path_rank` is the position of the statement's file in the order of the paths of the files in
/// the root, from [`Prefilter::rank`].
fn candidate_key(
    src_ref: &StatementRef,
    path_rank: u32,
    lineno: Option<usize>,
    level: Option<LogLevel>,
) -> (u8, Reverse<Quality>, bool, usize, usize, u32, usize, usize) {
    (
        src_ref.category.match_priority(),
        Reverse(src_ref.quality),
        level != Some(src_ref.level),
        line_distance(src_ref, lineno),
        src_ref.kinds.len(),
        path_rank,
        src_ref.line_no,
        src_ref.column,
    )
}

/// Collection of root paths to their tree of source files
/// that contain log statements.
#[derive(Default)]
pub struct LogMatcher {
    roots: HashMap<PathBuf, SourceTree>,
}

/// Options for matching log statements.
#[derive(Debug, Copy, Clone)]
pub struct LogMatchOptions {
    /// Whether to extract variables from log statements.
    pub extract_variables: bool,
    /// Whether a log message can be matched to a statement that is not a logging call when no
    /// logging call matches it, like a `println!()`, a thread dump written to a stream, or the
    /// message of an exception that is logged as is with `log.error(e.getMessage())`.  There are
    /// a lot of those statements, like every string passed to a function, so looking through them
    /// is slow, and they rarely explain a log message, so this is only for when the source of a
    /// message is asked for, not for scanning a whole log.
    pub fallback: bool,
}

impl Default for LogMatchOptions {
    fn default() -> Self {
        Self {
            extract_variables: true,
            fallback: false,
        }
    }
}

fn to_cached_name(path: &Path) -> String {
    format!(
        "cache.{:x}",
        Sha256::digest(path.as_os_str().as_encoded_bytes())
    )
}

/// A summary of the work done by extract_log_statements().  Useful for knowing if there were
/// any changes that need to be saved to the cache.
#[derive(Default, Debug)]
pub struct ExtractLogSummary {
    pub deleted: u64,
    pub new: u64,
    /// Problems encountered while reading source files.
    pub errors: Vec<LogError>,
}

impl ExtractLogSummary {
    pub fn changes(&self) -> u64 {
        self.new.saturating_add(self.deleted)
    }
}

impl LogMatcher {
    /// Create an empty LogMatcher
    pub fn new() -> Self {
        Self::default()
    }

    /// Find a file, in any language, under one of the roots.  The file with the same name that
    /// shares the longest trailing run of components with the path is chosen, so a path that is
    /// not under a root, like an absolute path from the machine that produced a stack trace,
    /// still matches.  If the path only partially matches more than one file, it is ambiguous
    /// and nothing is returned rather than guessing.
    ///
    /// A relative path with directories, like a Java package's, has to match at least the file
    /// and the directory it is in: `com/foo/Bar.java` is not `com/other/Bar.java`.  A Windows
    /// path, like `C:\src\App\Program.cs` in a .NET trace, is read with `\` as the separator.
    pub fn find_file(&self, path: &Path) -> Option<PathBuf> {
        let windows_path = Self::from_windows_path(path);
        let path = windows_path.as_deref().unwrap_or(path);
        let names: Vec<_> = path
            .components()
            .filter_map(|comp| match comp {
                Component::Normal(name) => Some(name),
                _ => None,
            })
            .collect();
        let file_name = names.last()?;
        let mut candidates: Vec<_> = self
            .roots
            .values()
            .flat_map(|root| root.tree.find_by_name(file_name))
            .map(|found| {
                let matched = found
                    .components()
                    .rev()
                    .zip(names.iter().rev())
                    .take_while(|(comp, name)| comp.as_os_str() == **name)
                    .count();
                (matched, found)
            })
            .collect();
        // Sort by longest match and then by path so that the result does not depend on the
        // order of the roots.
        candidates.sort_by(|lhs, rhs| rhs.0.cmp(&lhs.0).then_with(|| lhs.1.cmp(&rhs.1)));
        let mut iter = candidates.into_iter();
        let (best_len, best) = iter.next()?;
        if !path.has_root() && best_len < names.len().min(2) {
            // Only the file name is the same, and the path's directories say where it is.
            return None;
        }
        match iter.next() {
            Some((next_len, _)) if next_len == best_len && best_len < names.len() => None,
            _ => Some(best),
        }
    }

    /// `path` with `/` for `\` and without its drive letter, if it's a Windows path: it has
    /// backslashes and no slashes.
    fn from_windows_path(path: &Path) -> Option<PathBuf> {
        let path_str = path.to_str()?;
        if !path_str.contains('\\') || path_str.contains('/') {
            return None;
        }
        let path_str = path_str.replace('\\', "/");
        let bytes = path_str.as_bytes();
        let without_drive =
            if bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':' {
                &path_str[2..]
            } else {
                &path_str[..]
            };
        Some(PathBuf::from(without_drive))
    }

    fn load_cache_entry(path: &Path, input: impl Read) -> Result<SourceTree, LogError> {
        let mut reader = BufReader::new(input);
        let mut header_str = String::new();
        reader
            .read_line(&mut header_str)
            .map_err(|err| LogError::FailedToReadCache {
                path: path.to_owned(),
                source: Arc::new(err),
            })?;
        // We're deserializing the header to check for garbage and version compatibility.
        let _header = serde_json::from_str::<CacheEntryHeader>(&header_str).map_err(|_err| {
            LogError::OldCacheEntry {
                path: path.to_owned(),
            }
        })?;
        // XXX check that the path matches?
        let mut decoded_root: SourceTree =
            bincode::serde::decode_from_std_read(&mut reader, bincode::config::standard())
                .map_err(|err| LogError::FailedToReadCache {
                    path: path.to_owned(),
                    source: Arc::new(err),
                })?;
        for sif in decoded_root.files_with_statements.values() {
            sif.to_lookup_pair().into_iter().for_each(|(name, sid)| {
                decoded_root
                    .file_name_to_sources
                    .entry(name)
                    .or_default()
                    .push(sid);
            });
        }
        decoded_root.resolve_message_refs();
        decoded_root.prune_log_calls();
        decoded_root.rebuild_prefilter();
        Ok(decoded_root)
    }

    /// Try to load SourceTrees from the cache for each root.
    #[must_use]
    pub fn load_from_cache(&mut self, cache: &Cache, tracker: &ProgressTracker) -> Vec<LogError> {
        tracker.begin_step(format!(
            "Loading cached log statements from: {}",
            cache.location.display()
        ));
        let mut old_roots: HashMap<PathBuf, SourceTree> = HashMap::new();
        let mut retval: Vec<LogError> = Vec::new();
        std::mem::swap(&mut self.roots, &mut old_roots);
        let entries: Vec<(PathBuf, SourceTree, PathBuf, u64)> = old_roots
            .into_iter()
            .map(|(root_path, old_root)| {
                let cached_path = cache.location.join(to_cached_name(&root_path));
                let size = fs::metadata(&cached_path).map_or(0, |meta| meta.len());
                (root_path, old_root, cached_path, size)
            })
            .collect();
        let total_size = entries.iter().map(|entry| entry.3).sum();
        let work_guard = tracker.doing_work(total_size, "bytes".to_string());
        let mut found = 0;
        let mut not_found = 0;
        let mut skipped = 0;
        for (root_path, old_root, cached_path, size) in entries {
            let start = work_guard.completed();
            let new_root = if let Ok(file) = File::open(&cached_path) {
                let reader = ProgressReader::new(file, &work_guard);
                match Self::load_cache_entry(&cached_path, reader) {
                    Ok(new_root) => {
                        found += 1;
                        new_root
                    }
                    Err(err) => {
                        skipped += 1;
                        retval.push(err);
                        old_root
                    }
                }
            } else {
                not_found += 1;
                old_root
            };
            self.roots.insert(root_path, new_root);
            // An entry that was skipped will not have been read all the way through.
            work_guard.inc(size.saturating_sub(work_guard.completed() - start));
        }
        tracker.end_step(format!(
            "found {}; skipped {}; not found {}",
            found, skipped, not_found
        ));

        retval
    }

    /// Save the log statements to the cache.
    pub fn cache_to(&self, cache: &Cache, tracker: &ProgressTracker) -> Result<(), LogError> {
        tracker.begin_step(format!(
            "Saving log statements to: {}",
            cache.location.display()
        ));
        let mut total_size: u64 = 0;
        let work_guard = tracker.doing_work(self.roots.len() as u64, "root".to_string());
        for (root_path, root) in &self.roots {
            let cached_name = to_cached_name(root_path);
            let tmp_path = {
                fs::create_dir_all(&cache.location).map_err(to_write_cache_error)?;
                let mut file =
                    NamedTempFile::with_suffix_in(".tmp", &cache.location).map_err(|err| {
                        LogError::FailedToWriteCache {
                            source: Arc::new(err),
                        }
                    })?;
                // Write a JSON header as the first line so that a user can figure out what this
                // file is.  It can also be used in the future if the file format needs to change.
                let header = CacheEntryHeader {
                    schema: CacheEntrySchema::V1,
                    revision: Revision::Current,
                    format: CacheEntryFormat::Bincode,
                    path: root_path.to_string_lossy().to_string(),
                    timestamp: SystemTime::now()
                        .duration_since(UNIX_EPOCH)
                        .unwrap_or_default()
                        .as_secs(),
                };
                serde_json::to_writer(&file, &header).map_err(to_write_cache_error)?;
                file.write_all("\n".as_bytes())
                    .map_err(to_write_cache_error)?;
                // bincode writes each field on its own, which is a lot of small writes.
                let mut writer = BufWriter::new(&mut file);
                bincode::serde::encode_into_std_write(
                    root,
                    &mut writer,
                    bincode::config::standard(),
                )
                .map_err(to_write_cache_error)?;
                writer.flush().map_err(to_write_cache_error)?;
                drop(writer);
                total_size = total_size.saturating_add(file.stream_position().unwrap_or(0));
                file.into_temp_path()
            };
            fs::rename(tmp_path, cache.location.join(cached_name)).map_err(to_write_cache_error)?;
            work_guard.inc(1);
        }
        tracker.end_step(format!(
            "{} files totaling {}",
            self.roots.len(),
            HumanBytes(total_size)
        ));

        Ok(())
    }

    /// True if no log statements are recognized by this matcher.
    pub fn is_empty(&self) -> bool {
        self.statements().next().is_none()
    }

    /// Add a source root path
    /// Add a directory to search for source files.  A path under an existing root
    /// is already covered and ignored.  Existing roots under the new path are
    /// replaced by it, so a file is only ever in one root; otherwise its statements
    /// would be found (and reported) once per root.
    pub fn add_root(&mut self, path: &Path) -> Result<(), LogError> {
        let path = path.canonicalize().unwrap_or(path.to_owned());
        if let Some(_existing_path) = self.match_path(&path) {
        } else {
            self.roots
                .retain(|existing_path, _| !existing_path.starts_with(&path));
            self.roots
                .entry(path.to_owned())
                .or_insert_with(|| SourceTree {
                    tree: SourceHierTree::from(&path),
                    files_with_statements: HashMap::new(),
                    file_name_to_sources: HashMap::new(),
                    log_prefilter: OnceLock::new(),
                    fallback_prefilter: OnceLock::new(),
                    find_prefilter: OnceLock::new(),
                    line_cache: RwLock::default(),
                    files_by_name: RwLock::default(),
                    learned_prefixes: RwLock::default(),
                    log_calls: BTreeMap::new(),
                    languages: BTreeSet::new(),
                });
        }
        Ok(())
    }

    /// Check if the given path is covered by any of the roots in this matcher.
    pub fn match_path(&self, path: &Path) -> Option<(&PathBuf, &SourceTree)> {
        self.roots
            .iter()
            .find(|(existing_path, _coll)| path.starts_with(existing_path))
    }

    pub fn find_source_file_statements(&self, path: &Path) -> Vec<&StatementsInFile> {
        self.roots
            .values()
            .flat_map(|root| {
                root.tree
                    .find_file(path)
                    .into_iter()
                    .filter_map(|(_actual_path, info)| root.files_with_statements.get(&info.id))
            })
            .collect()
    }

    /// Traverse the roots looking for supported source files.
    #[must_use]
    pub fn discover_sources(&mut self, tracker: &ProgressTracker) -> Vec<LogError> {
        tracker.begin_step("Finding source code".to_string());
        let pguard = tracker.doing_work(self.roots.len() as u64, "paths".to_string());
        self.roots.par_iter_mut().for_each(|(_path, coll)| {
            coll.tree.sync();
            pguard.inc(1);
        });
        let mut retval: Vec<LogError> = Vec::new();
        let mut file_count: usize = 0;
        self.roots.values().for_each(|coll| {
            coll.tree.visit(|node| match &node.content {
                SourceHierContent::File { .. } => file_count += 1,
                SourceHierContent::UnsupportedFile { .. } => {}
                SourceHierContent::Directory { .. } => {}
                SourceHierContent::Error { ref source } => retval.push(source.clone()),
                SourceHierContent::Unknown { .. } => {}
            });
        });
        tracker.end_step(format!("{} files found", file_count));

        retval
    }

    /// Scan the source files looking for potential log statements.
    pub fn extract_log_statements(&mut self, tracker: &ProgressTracker) -> ExtractLogSummary {
        let mut retval = ExtractLogSummary::default();
        let mut ref_summary = MessageRefSummary::default();
        tracker.begin_step("Extracting log statements".to_string());
        self.roots.iter_mut().for_each(|(_path, coll)| {
            let events: Vec<ScanEvent> = coll.tree.scan().collect();
            let new_files = events
                .iter()
                .filter(|event| matches!(event, ScanEvent::NewFile(..)))
                .count();
            let guard = tracker.doing_work(new_files as u64, "files".to_string());
            let mut new_files = Vec::with_capacity(new_files);
            for event in events {
                match event {
                    ScanEvent::NewFile(path, info) => new_files.push((path, info)),
                    ScanEvent::DeletedFile(_path, id) => {
                        retval.deleted += 1;
                        coll.files_with_statements.remove(&id);
                        coll.file_name_to_sources.values_mut().for_each(|ids| {
                            ids.retain_mut(|elem| *elem != id);
                        });
                    }
                }
            }
            // Each file is read and extracted by the same worker, so the work is spread over all
            // of the threads and only the files being worked on are in memory.
            let results: Vec<Result<Option<StatementsInFile>, (PathBuf, LogError)>> = new_files
                .into_par_iter()
                .map(|(path, info)| {
                    let code = File::open(&path)
                        .map_err(|err| LogError::CannotReadSourceFile {
                            path: path.clone(),
                            source: Arc::new(err),
                        })
                        .and_then(|file| CodeSource::new(&path, info, file));
                    match code {
                        Ok(code) => {
                            Ok(extract_logging_guarded(std::slice::from_ref(&code), &guard).pop())
                        }
                        Err(err) => {
                            guard.inc(1);
                            Err((path, err))
                        }
                    }
                })
                .collect();
            let mut unreadable: Vec<PathBuf> = Vec::new();
            for result in results {
                match result {
                    Ok(sif) => {
                        retval.new += 1;
                        if let Some(sif) = sif {
                            sif.to_lookup_pair().into_iter().for_each(|(name, sid)| {
                                coll.file_name_to_sources.entry(name).or_default().push(sid);
                            });
                            coll.files_with_statements.insert(sif.id, sif);
                        }
                    }
                    Err((path, err)) => {
                        retval.errors.push(err);
                        unreadable.push(path);
                    }
                }
            }
            // The scan marked these as done, but they need to be retried on the next run.
            unreadable
                .iter()
                .for_each(|path| coll.tree.mark_unscanned(path));
            let summary = coll.resolve_message_refs();
            ref_summary.resolved += summary.resolved;
            ref_summary.not_found += summary.not_found;
            ref_summary.no_text += summary.no_text;
            coll.prune_log_calls();
        });
        tracker.step("linking calls through wrappers".to_string());
        let (derived, joined) = self.link_statements();
        // Built now, instead of when the first message is matched, so the time is reported
        // with the rest of the work of loading the statements.
        tracker.step("indexing the statements".to_string());
        self.roots.par_iter().for_each(|(_path, coll)| {
            rayon::join(|| coll.log_prefilter(), || coll.find_prefilter());
        });
        let mut found = format!("{} found", self.statements().count());
        if derived > 0 {
            found.push_str(&format!(", {derived} more for calls through wrappers"));
        }
        if joined > 0 {
            found.push_str(&format!(", {joined} more for continued lines"));
        }
        if ref_summary.resolved + ref_summary.not_found + ref_summary.no_text > 0 {
            found.push_str(&format!(
                " ({} with a message constant; {} constants not found, {} without text)",
                ref_summary.resolved, ref_summary.not_found, ref_summary.no_text
            ));
        }
        tracker.end_step(found);

        retval
    }

    /// Derive statements for the C and C++ calls whose message goes through a wrapper that
    /// changes it, and rebuild the prefilters with them.  A wrapper is a function-like macro
    /// that passes the message on, like
    /// `#define acpi_handle_info(handle, fmt, ...) acpi_handle_printk(KERN_INFO, handle, fmt, ...)`,
    /// which can add text, like `"foo: " fmt`, and a function that prints the message with a
    /// statement of its own, either a string passed for a `%s`, like the
    /// `show_string(udev, "Product", udev->product)` calls of
    /// `dev_info(&udev->dev, "%s: %s\n", id, string)` in `show_string()`, or the format string
    /// of a variadic function printed with the Linux kernel's `%pV`, like the
    /// `printk("%sACPI: %s: %pV", ...)` in `acpi_handle_printk()`.  The wrappers can be in any
    /// root, like a macro in a header.  A wrapper defined in the same file as the call is used
    /// before one in other files, since C functions are often `static`, and one defined in
    /// several other files is not used, since it is not known which one is called.  Then, the
    /// statements for the lines that are continued, see `join_continued_lines()`, are derived.
    /// Returns the number of statements derived for wrappers and for continued lines.  See
    /// `Statement::splice()`.
    fn link_statements(&mut self) -> (usize, usize) {
        for coll in self.roots.values_mut() {
            for sif in coll.files_with_statements.values_mut() {
                sif.derived_statements.clear();
            }
        }
        let c_files = || {
            self.roots
                .iter()
                .flat_map(|(root, coll)| {
                    coll.files_with_statements
                        .values()
                        .map(move |sif| (root, sif))
                })
                .filter(|(_, sif)| sif.language.is_c_family())
        };
        let mut macros: HashMap<&str, Vec<(&StatementsInFile, &wrappers::MacroWrapper)>> =
            HashMap::new();
        let mut functions: HashMap<&str, Vec<(&StatementsInFile, &Statement)>> = HashMap::new();
        for (_, sif) in c_files() {
            for wrapper in &sif.macros {
                macros
                    .entry(wrapper.name.as_str())
                    .or_default()
                    .push((sif, wrapper));
            }
            for stmt in &sif.log_statements {
                // Not only log statements, since a wrapper can print with a call that does
                // not look like logging, like `printk("%sACPI: %s: %pV", level, ...)`.
                if !stmt.kinds.is_empty() {
                    functions
                        .entry(stmt.qualified_name.as_str())
                        .or_default()
                        .push((sif, stmt));
                }
            }
        }
        let wrappers = Wrappers { macros, functions };
        let derived: Vec<(PathBuf, SourceFileID, Statement)> = c_files()
            .flat_map(|(root, sif)| {
                let wrappers = &wrappers;
                sif.log_statements.iter().flat_map(move |call| {
                    wrappers
                        .link(call, sif)
                        .into_iter()
                        .map(move |stmt| (root.clone(), sif.id, stmt))
                })
            })
            .collect();
        let count = derived.len();
        for (root, file_id, stmt) in derived {
            if let Some(sif) = self
                .roots
                .get_mut(&root)
                .and_then(|coll| coll.files_with_statements.get_mut(&file_id))
            {
                sif.derived_statements.push(stmt);
            }
        }
        let mut joined_count = 0;
        for coll in self.roots.values_mut() {
            for sif in coll.files_with_statements.values_mut() {
                if sif.language.is_c_family() {
                    let joined = join_continued_lines(sif);
                    joined_count += joined.len();
                    sif.derived_statements.extend(joined);
                }
            }
        }
        self.roots
            .values_mut()
            .for_each(SourceTree::rebuild_prefilter);
        (count, joined_count)
    }

    /// Attempt to match the given log message.  If the message has a file name and line number,
    /// the statements in a root that matched earlier messages with the same ones are tried
    /// before the rest of that root.  The best match from each root is found and then the best
    /// of those is chosen the same way as within a root, so a generic statement in one root,
    /// like `"%s\n"`, does not hide a better one in another, and the result does not depend on
    /// the order of the roots.
    ///
    /// Without [`LogMatchOptions::fallback`], a message that matches nothing is remembered by its
    /// file name and line number, and the next messages with the same ones are not looked for,
    /// so the time spent on a log with a lot of messages from code that is not in the roots, or
    /// that log2src does not understand, is not spent over and over.  Like the cache of the
    /// statements that matched, this depends on the order of the messages: a message that would
    /// match is not found if one with the same file and line that did not match came first.
    pub fn match_log_statement<'a, 's>(
        &'s self,
        log_ref: &LogRef<'a>,
        options: &LogMatchOptions,
    ) -> Option<LogMapping<'a, 's>> {
        let start = std::time::Instant::now();
        if !options.fallback && self.known_unmatched(log_ref) {
            match_stats::record_line_cache_negative_hit();
            match_stats::record_message(start, Outcome::Unmatched, log_ref.body());
            return None;
        }
        let (mapping, outcome) = self.match_log_statement_inner(log_ref, options);
        if !options.fallback && matches!(outcome, Outcome::Unmatched) {
            self.roots
                .values()
                .for_each(|coll| coll.remember_unmatched(log_ref));
        }
        match_stats::record_message(start, outcome, log_ref.body());
        mapping
    }

    /// Check if an earlier message with the same file name and line number as this one matched
    /// nothing, and nothing else could match it: every root either remembers that, or has no
    /// files with that name.
    fn known_unmatched(&self, log_ref: &LogRef) -> bool {
        let mut remembered = false;
        for coll in self.roots.values() {
            match coll.known_unmatched(log_ref) {
                Some(true) => remembered = true,
                Some(false) => {}
                None => return false,
            }
        }
        remembered
    }

    fn match_log_statement_inner<'a, 's>(
        &'s self,
        log_ref: &LogRef<'a>,
        options: &LogMatchOptions,
    ) -> (Option<LogMapping<'a, 's>>, Outcome) {
        let lineno = log_ref.details.as_ref().and_then(|details| details.lineno);
        let level = log_ref.level();
        let body = log_ref.body();
        let candidates = self
            .roots
            .values()
            .filter_map(|coll| {
                match_stats::timed(Step::LineCache, || {
                    coll.find_cached_match(log_ref, options.fallback)
                })
                .or_else(|| {
                    match_stats::timed(Step::Prefilter, || {
                        coll.find_best_match(log_ref, options.fallback)
                    })
                })
            })
            .sorted_by(|lhs, rhs| compare_candidates(&lhs.0, &rhs.0, lineno, level));
        // Each root's statement already matched, so only the choice between them is made again.
        let best = choose_match(
            candidates,
            lineno,
            |(src_ref, _)| src_ref.stmt,
            |(_, without_empty_values)| Some(*without_empty_values),
        )
        .map(|((src_ref, _), _)| src_ref);
        if !explains_enough(best.as_ref(), body) {
            // A prefix that was found in front of an earlier message from the statement.
            let learned = match_stats::timed(Step::Learned, || {
                self.roots
                    .values()
                    .filter_map(|coll| coll.learned_match(log_ref, options.fallback))
                    .min_by(|lhs, rhs| compare_candidates(&lhs.0, &rhs.0, lineno, level))
            });
            // The same test as for the slow way's reading below.
            if let Some((src_ref, start, score)) = learned {
                if best.as_ref().is_none_or(|best| score > best.quality) {
                    let body = body.trim();
                    let mut mapping =
                        self.to_log_mapping(log_ref, src_ref, &body[start..], options);
                    mapping.prefix = message_source::prefix_end(body, start)
                        .and_then(|end| trim_prefix(&body[..end]));
                    return (Some(mapping), Outcome::Learned);
                }
            }
            let explained = match_stats::timed(Step::Explain, || {
                self.explain_log_body(log_ref, options.fallback, best.as_ref())
            });
            if let Some((source, learnable)) = explained {
                if best.as_ref().is_none_or(|best| source.score > best.quality) {
                    if let (Some(learnable), Some(prefix), Some(start)) =
                        (learnable, source.prefix.as_deref(), source.start)
                    {
                        if let Some(separator) = body.trim().get(prefix.len()..start) {
                            learnable.tree.learn_prefix(learnable.id, separator);
                        }
                    }
                    let mut mapping =
                        self.to_log_mapping(log_ref, source.stmt, &source.text, options);
                    mapping.prefix = source.prefix.as_deref().and_then(|prefix| {
                        let body = body.trim_start();
                        trim_prefix(body.get(..prefix.len()).filter(|start| *start == prefix)?)
                    });
                    return (Some(mapping), Outcome::Explained);
                }
            }
        }
        let outcome = if best.is_some() {
            Outcome::Direct
        } else {
            Outcome::Unmatched
        };
        (
            best.map(|src_ref| self.to_log_mapping(log_ref, src_ref, body, options)),
            outcome,
        )
    }

    /// Find the statement that produced the most of a log message when none matches enough of
    /// all of it, like a message with a prefix that is not from the source, such as the device
    /// name that the Linux kernel's `dev_info()` adds, or one that wraps a message made
    /// somewhere else.  See [`message_source::best_log_source`].  Only the statements found by
    /// the prefilters are used, which keeps this fast, since the statement for any part of the
    /// message has its key literal in that part.  Only the start of a long message is read, so
    /// only that is prefiltered.  When the reading is a prefix and a statement, the statement is
    /// returned too, so the prefix can be learned.
    fn explain_log_body<'s>(
        &'s self,
        log_ref: &LogRef,
        fallback: bool,
        best: Option<&StatementRef>,
    ) -> Option<(message_source::LogSource<'s>, Option<Learnable<'s>>)> {
        let head = message_source::log_head(log_ref.body().trim());
        // Without `fallback`, the reading has to be from a logging call, and the statements in
        // the other categories that can make the values in it are errors and formatted
        // messages, so the rest are never used.
        let candidates: Vec<(&SourceTree, Vec<(StatementID, StatementRef)>)> = self
            .roots
            .values()
            .map(|coll| {
                let mut found = coll.prefiltered_candidates(coll.find_prefilter(), log_ref, head);
                if !fallback {
                    found.retain(|(_, stmt)| stmt.category != MessageCategory::Other);
                }
                (coll, found)
            })
            .collect();
        match_stats::record_explain_candidates(
            candidates.iter().map(|(_, found)| found.len()).sum(),
        );
        // A reading is only used if it explains more literal text than `best`, which it can
        // only do with another statement: `best` by itself, even after a prefix, explains the
        // same text.  So, when no other statement's key literal is in the message, which is
        // most of the time, the message does not have to be read.  A chain of `best` with
        // itself, like `"retry: retry"`, is missed, but that is not worth reading every
        // message for.
        let others = candidates
            .iter()
            .flat_map(|(_, found)| found)
            .any(|(_, stmt)| best.is_none_or(|best| !std::ptr::eq(stmt.stmt, best.stmt)));
        if !others {
            match_stats::record_explain_skipped();
            return None;
        }
        let statements = candidates
            .iter()
            .flat_map(|(_, found)| found.iter().map(|(_, stmt)| *stmt));
        let source = message_source::best_log_source(statements, log_ref.body(), fallback)?;
        let learnable = source.start.and_then(|_| {
            candidates.iter().find_map(|(tree, found)| {
                found
                    .iter()
                    .find(|(_, stmt)| std::ptr::eq(stmt.stmt, source.stmt.stmt))
                    .map(|(id, _)| Learnable { tree, id: *id })
            })
        });
        Some((source, learnable))
    }

    #[doc(hidden)]
    pub fn rebuild_prefilters(&mut self) {
        self.roots
            .values_mut()
            .for_each(SourceTree::rebuild_prefilter);
    }

    /// Iterate over the logging calls found under each root.
    pub fn log_calls(&self) -> impl Iterator<Item = (&PathBuf, &BTreeMap<String, LogCall>)> {
        self.roots
            .iter()
            .map(|(root, coll)| (root, &coll.log_calls))
    }

    /// The languages of the log statements found under all of the roots, each once.
    pub fn languages(&self) -> BTreeSet<SourceLanguage> {
        self.roots
            .values()
            .flat_map(|coll| coll.languages.iter().copied())
            .collect()
    }

    /// Iterate over all of the log statements that were found.
    pub fn statements(&self) -> impl Iterator<Item = StatementRef<'_>> {
        self.roots
            .values()
            .flat_map(|coll| coll.files_with_statements.values())
            .flat_map(|sif| sif.statements())
    }

    /// Find the statements that could have produced a message, like one copied from a log, a
    /// screenshot, or a GUI, and the sources of the values in it.  See
    /// [`find_message_sources`].
    pub fn find_message_sources(
        &self,
        message: &str,
        extract_variables: bool,
    ) -> Vec<MessageSource<'_>> {
        let statements = self
            .roots
            .values()
            .flat_map(|coll| coll.files_with_statements.values())
            .flat_map(|sif| sif.matchable_statements());
        let mut sources = find_message_sources(statements, message);
        if !extract_variables {
            fn clear(sources: &mut [MessageSource]) {
                for source in sources {
                    source.variables.clear();
                    clear(&mut source.causes);
                }
            }
            clear(&mut sources);
        }
        sources
    }

    /// Map the log message to the statement, whose values are extracted from `text`, which is
    /// the part of the message's body that the statement produced.  The text in front of it
    /// that no statement produced is filled in by the caller.
    fn to_log_mapping<'a, 's>(
        &self,
        log_ref: &LogRef<'a>,
        src_ref: StatementRef<'s>,
        text: &str,
        options: &LogMatchOptions,
    ) -> LogMapping<'a, 's> {
        let variables = if options.extract_variables {
            match_stats::timed(Step::Variables, || {
                extract_variables_from(text, src_ref.stmt)
            })
        } else {
            Vec::new()
        };
        LogMapping {
            log_ref: *log_ref,
            src_ref: Some(src_ref),
            prefix: None,
            variables,
        }
    }
}

/// The text in front of a message that no statement produced, without the separator after it,
/// like the `: ` in `"usb 1-5: new device"`, or `None` if there is nothing else.
fn trim_prefix(prefix: &str) -> Option<&str> {
    Some(prefix.trim_end().trim_end_matches(':').trim_end()).filter(|prefix| !prefix.is_empty())
}

/// Named by their LSP language identifiers ("rust", "java", "cpp", ...) in the JSON output,
/// on the command line, and by [SourceLanguage::as_str].
#[derive(
    Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Serialize, Deserialize, clap::ValueEnum,
)]
#[serde(rename_all = "lowercase")]
pub enum SourceLanguage {
    Rust,
    Java,
    C,
    #[value(alias = "c++")]
    Cpp,
    Python,
    Kotlin,
}

impl From<SourceLanguage> for Language {
    fn from(value: SourceLanguage) -> Self {
        match value {
            SourceLanguage::Rust => tree_sitter_rust_orchard::LANGUAGE.into(),
            SourceLanguage::Java => tree_sitter_java::LANGUAGE.into(),
            SourceLanguage::C => tree_sitter_c::LANGUAGE.into(),
            SourceLanguage::Cpp => tree_sitter_cpp::LANGUAGE.into(),
            SourceLanguage::Python => tree_sitter_python::LANGUAGE.into(),
            SourceLanguage::Kotlin => tree_sitter_kotlin_ng::LANGUAGE.into(),
        }
    }
}

const IDENTS_RS: &[&str] = &["debug", "info", "warn"];
const IDENTS_JAVA: &[&str] = &["logger", "log", "fine", "debug", "info", "warn", "trace"];
const IDENTS_CPP: &[&str] = &["debug", "info", "warn", "trace"];

const IDENTS_PYTHON: &[&str] = &["debug", "info", "warn", "trace"];

const IDENTS_KOTLIN: &[&str] = IDENTS_JAVA;

/// The `{{` and `}}` alternatives are escaped braces, which are found so that they are not
/// mistaken for the start or end of a placeholder.
static RUST_PLACEHOLDER_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"\{\{|\}\}|\{(?:([a-zA-Z_][a-zA-Z0-9_.]*)|(\d+))?\s*(?::[^}]*)?}"#).unwrap()
});

/// Other braces in an SLF4J message are literal, so a placeholder cannot contain a `{`.
/// The names of Java loggers and of their methods that log at a level.  `config` is anchored
/// since it is part of so many other names, like `loadConfig`.
const JAVA_LOGGER_OBJECT: &str = "log(ger)?|LOG(GER)?";
const JAVA_LEVEL_METHODS: &str = "fine|^config$|debug|info|warn|trace|error|severe|fatal";

/// The methods that are not given to the patterns for builders in the Java query, since a
/// level name would make a call on something that is not a logger, like `parser.error("...")`,
/// look like logging.  The calls on a logger are found by the other patterns.
const JAVA_NOT_BUILDER_METHODS: &str =
    "^(log|fine|finer|finest|config|debug|info|warn|warning|trace|error|severe|fatal)$";

/// The comments that can come before an argument, like the `// language=sql` in front of SQL,
/// for the patterns with an anchor.
const JAVA_COMMENTS: &str = "[(line_comment) (block_comment)]*";

static JAVA_QUERY: LazyLock<String> = LazyLock::new(|| {
    format!(
        r#"
                    (method_invocation
                        object: (identifier) @object-name
                        name: (identifier) @method-name
                        arguments: [
                            (argument_list (template_expression
                                template_argument: (string_literal) @arguments))
                            (argument_list . [(string_literal) (binary_expression)] @arguments)
                            ; java.util.logging's log(Level, String, ...) or a SLF4J Marker
                            (argument_list . [(field_access) (identifier)] .
                                [(string_literal) (binary_expression)] @arguments)
                        ]
                        (#match? @object-name "{JAVA_LOGGER_OBJECT}")
                        (#match? @method-name "^log$|{JAVA_LEVEL_METHODS}")
                    )
                    ; A message that is built by another call, like String.format("...", x)
                    (method_invocation
                        object: (identifier) @object-name
                        name: (identifier) @method-name
                        arguments: [
                            (argument_list . (method_invocation) @message-call)
                            (argument_list . [(field_access) (identifier)] .
                                (method_invocation) @message-call)
                        ]
                        (#match? @object-name "{JAVA_LOGGER_OBJECT}")
                        (#match? @method-name "^log$|{JAVA_LEVEL_METHODS}")
                    )
                    ; A Supplier for the message, like log.fine(() -> "...") or
                    ; log.log(Level.WARNING, e, () -> "...")
                    (method_invocation
                        object: (identifier) @object-name
                        name: (identifier) @method-name
                        arguments: [
                            (argument_list . (lambda_expression
                                body: [(string_literal) (binary_expression)] @arguments))
                            (argument_list . (_) . (lambda_expression
                                body: [(string_literal) (binary_expression)] @arguments))
                            (argument_list . (_) . (_) . (lambda_expression
                                body: [(string_literal) (binary_expression)] @arguments))
                            (argument_list . (lambda_expression
                                body: (method_invocation) @message-call))
                            (argument_list . (_) . (lambda_expression
                                body: (method_invocation) @message-call))
                            (argument_list . (_) . (_) . (lambda_expression
                                body: (method_invocation) @message-call))
                        ]
                        (#match? @object-name "{JAVA_LOGGER_OBJECT}")
                        (#match? @method-name "^log$|{JAVA_LEVEL_METHODS}")
                    )
                    ; A message that is a constant, like log.info(Messages.LOG_STARTING, name)
                    (method_invocation
                        object: (identifier) @object-name
                        name: (identifier) @method-name
                        arguments: (argument_list . [(identifier) (field_access)] @message-ref)
                        (#match? @object-name "{JAVA_LOGGER_OBJECT}")
                        (#match? @method-name "{JAVA_LEVEL_METHODS}")
                    )
                    ; java.util.logging's log(Level, String, ...) with a constant message
                    (method_invocation
                        object: (identifier) @object-name
                        name: (identifier) @method-name
                        arguments: (argument_list . (_) . [(identifier) (field_access)] @message-ref)
                        (#match? @object-name "{JAVA_LOGGER_OBJECT}")
                        (#eq? @method-name "log")
                    )
                    ; An exception, like throw new IllegalStateException("...") or
                    ; throw new IOException(String.format("...", x))
                    (throw_statement
                        (object_creation_expression
                            type: (_) @exception-name
                            arguments: [
                                (argument_list . [(string_literal) (binary_expression)] @arguments)
                                (argument_list . (method_invocation) @message-call)
                            ]
                        )
                    )
                    ; Text passed to a method of a builder, like the `.append(" is not valid")`
                    ; in `new StringBuilder().append(name).append(" is not valid")`, or the
                    ; first link of a chain, like `sql.append(" OR (").append(clause)`
                    (method_invocation
                        object: [(method_invocation) (object_creation_expression)]
                        name: (identifier) @method-name
                        arguments: (argument_list . {JAVA_COMMENTS} . [(string_literal) (binary_expression)] @arguments)
                        (#not-match? @method-name "{JAVA_NOT_BUILDER_METHODS}")
                    )
                    (method_invocation
                        object: (method_invocation
                            name: (identifier) @method-name
                            arguments: (argument_list . {JAVA_COMMENTS} . [(string_literal) (binary_expression)] @arguments)
                        )
                        (#not-match? @method-name "{JAVA_NOT_BUILDER_METHODS}")
                    )
                    ; Text passed to a constructor, like `new StringBuilder("SELECT ...")`.  The
                    ; name of an exception that is thrown is changed by `exception_call_name()`.
                    (object_creation_expression
                        type: (_) @type-name
                        arguments: (argument_list . {JAVA_COMMENTS} . [(string_literal) (binary_expression)] @arguments)
                    )
                    ; Text passed to a method by itself, like `sql.append(" ORDER BY 1");`
                    (expression_statement
                        (method_invocation
                            name: (identifier) @method-name
                            arguments: (argument_list . {JAVA_COMMENTS} . [(string_literal) (binary_expression)] @arguments)
                        )
                        (#not-match? @method-name "{JAVA_NOT_BUILDER_METHODS}")
                    )
                "#
    )
});

static JAVA_PLACEHOLDER_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#"\{[^{}]*}|\\\{([^}]*)}"#).unwrap());

/// A printf-style conversion, like `%-5d`, `%'.2f`, `%1$s`, or glibc's `%m`, followed by the
/// conversion characters that are accepted.  There are no capture groups since the other
/// placeholders in a language's regex are identified by their group.
const PRINTF_CONVERSION: &str = r#"%(?:\d+\$)?[-+ #0']*(?:\d+|\*)?(?:\.(?:\d+|\*))?[hlLzjt]*"#;
/// The Linux kernel's printk() extends `%p` with the alphanumeric characters that follow it,
/// like `%pR` for a resource or `%pOFn` for a device tree node, which print something other
/// than the address.  Plain printf() would print the address followed by those characters,
/// but that is rare in a format string, so they are treated as part of the conversion.
const C_CONVERSIONS: &str = "(?:[diuoxXfFeEgGaAcsnm%]|p[0-9A-Za-z]*)";

/// The extension characters after the `p` of a C pointer conversion, like `R` for `%pR`, or
/// `None` if the conversion is not a pointer.  `spec` is the conversion without the `%`.  The
/// flags, width, precision, and length modifiers that come before the conversion character do
/// not contain a `p`, so the first one starts the conversion.
pub(crate) fn pointer_extension(spec: &str) -> Option<&str> {
    spec.split_once('p').map(|(_, ext)| ext)
}

/// C only has printf-style placeholders.
static C_PLACEHOLDER_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(&format!("{PRINTF_CONVERSION}{C_CONVERSIONS}")).unwrap());

static CPP_PLACEHOLDER_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        r#"{PRINTF_CONVERSION}{C_CONVERSIONS}|\{{\{{|\}}\}}|\{{(?:([a-zA-Z_][a-zA-Z0-9_.]*)|(\d+))?\s*(?::[^}}]*)?}}"#
    ))
    .unwrap()
});

/// SLF4J-style placeholders.  String templates are converted to these placeholders, too.
static KOTLIN_PLACEHOLDER_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#"\{[^{}]*}"#).unwrap());

static PYTHON_PLACEHOLDER_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"%[-+ #0]*(?:\d+|\*)?(?:\.(?:\d+|\*))?[hlLzjt]*[diuoxXfFeEgGaAcrspn%]"#).unwrap()
});

/// Calls that take string-literals that are not messages, like `strcpy` or `getenv`.
const C_NOT_LOGGING_CALLS: &str = "(^|::)(strcpy|strncpy|strcat|strncat|strcmp|strncmp|strcasecmp|strncasecmp|strstr|strchr|strrchr|strdup|strtok|setenv|getenv|fopen|open|access|stat)$";

/// Names with a word about errors or messages, like `make_error`, `user_message::error`,
/// `Err`, or `zErrMsg`, where a word starts after a non-letter or is a capitalized part of
/// a camel-case name.
const C_MESSAGE_NAME: &str = "((^|[^A-Za-z])(?i:err|error|fail|failure|warn|warning|msg|message|exception)|[a-z0-9](Err|Error|Fail|Failure|Warn|Warning|Msg|Message|Exception))s?([^a-z]|$)";

/// The query for C and C++ calls with a message, where `literals` are the kinds of nodes that
/// are messages.  C++ also has the messages of the exceptions that are thrown, like
/// `throw std::runtime_error("...")`, and the messages passed to a method of a builder that
/// is part of a larger expression, like the `.append("...")` in
/// `report(attr_line_t().append_quoted(x).append(" is not valid"))`, or that start a chain,
/// like the `" OR ("` in `sql.append(" OR (").append(clause);`, and the text passed to a
/// constructor, like `std::string sql("SELECT ...");`.
fn c_family_query(literals: &str, cpp: bool) -> String {
    let cpp_only = if cpp {
        format!(
            r#"
            (call_expression
                function: (field_expression argument: (call_expression)) @fname
                arguments: (argument_list [{literals}] @arguments)
            )
            ; the first link of a chain, like `sql.append(" OR (").append(x)` or
            ; `attr_line_t("invalid value ").append(x)`
            (field_expression
                argument: (call_expression
                    function: (_) @fname
                    arguments: (argument_list [{literals}] @arguments)
                )
            )
            ; a constructor, like `std::string sql("SELECT ...");`
            (declaration
                type: (_) @fname
                declarator: (init_declarator
                    value: (argument_list [{literals}] @arguments)
                )
            )
            (throw_statement
                (call_expression
                    function: (_) @fname
                    arguments: (argument_list . [{literals}] @arguments)
                )
            )
            (throw_statement
                (call_expression
                    function: (_) @fname
                    arguments: (argument_list . (call_expression) @message-call)
                )
            )
            "#
        )
    } else {
        String::new()
    };
    format!(
        r#"
            (
                (expression_statement
                    (call_expression
                        function: (_) @fname
                        arguments: (argument_list [{literals}] @arguments)
                    )
                )
                (#not-match? @fname "{C_NOT_LOGGING_CALLS}")
            )
            ; A message that is built by another call, like fmt::format("...", x) or _("...")
            (
                (expression_statement
                    (call_expression
                        function: (_) @fname
                        arguments: (argument_list (call_expression) @message-call)
                    )
                )
                (#not-match? @fname "{C_NOT_LOGGING_CALLS}")
            )
            ; A message for a call whose result is used, like `return ec.make_error("...")`,
            ; `msg = user_message::error("...")`, or `return Err(fmt::format("...", x))`.  The
            ; results of all sorts of calls are used, like `auto msg = fmt::format("...")` or
            ; `auto it = m.find("key")`, so only calls named for errors and messages are kept.
            (
                (call_expression
                    function: (_) @fname
                    arguments: (argument_list [{literals}] @arguments)
                )
                (#match? @fname "{C_MESSAGE_NAME}")
            )
            (
                (call_expression
                    function: (_) @fname
                    arguments: (argument_list (call_expression) @message-call)
                )
                (#match? @fname "{C_MESSAGE_NAME}")
            )
            ; A message assigned to an error, like `tab->zErrMsg = sqlite3_mprintf("...")`
            (
                (assignment_expression
                    left: (_) @_lhs
                    right: (call_expression
                        function: (_) @fname
                        arguments: (argument_list [{literals}] @arguments)
                    )
                )
                (#match? @_lhs "{C_MESSAGE_NAME}")
                (#not-match? @fname "{C_NOT_LOGGING_CALLS}")
            )
            {cpp_only}
        "#
    )
}

/// Like C++, but without raw strings, and `+` on a string-literal is never a concatenation.
static C_QUERY: LazyLock<String> =
    LazyLock::new(|| c_family_query("(string_literal) (concatenated_string)", false));
static CPP_QUERY: LazyLock<String> = LazyLock::new(|| {
    c_family_query(
        "(string_literal) (raw_string_literal) (concatenated_string) (binary_expression) \
         (user_defined_literal)",
        true,
    )
});

static PATH_TO_NAME_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#"[/\\]([^/\\]+)$"#).unwrap());

impl SourceLanguage {
    /// C and C++ share most of their grammar and logging conventions.
    pub fn is_c_family(&self) -> bool {
        matches!(self, SourceLanguage::C | SourceLanguage::Cpp)
    }

    /// The LSP language identifier.
    pub fn as_str(&self) -> &'static str {
        match self {
            SourceLanguage::Rust => "rust",
            SourceLanguage::Java => "java",
            SourceLanguage::C => "c",
            SourceLanguage::Cpp => "cpp",
            SourceLanguage::Python => "python",
            SourceLanguage::Kotlin => "kotlin",
        }
    }

    /// Every language that can be parsed.
    pub fn all() -> &'static [SourceLanguage] {
        <Self as clap::ValueEnum>::value_variants()
    }

    /// The extensions, without the dot, of this language's source files.  They are matched
    /// case-sensitively.  A `.h` header is listed under C++, though its contents may make it C
    /// (see [SourceLanguage::from_contents]).  Tools that watch source files, like editor
    /// plugins, can use these to tell which changes matter.
    pub fn extensions(&self) -> &'static [&'static str] {
        match self {
            SourceLanguage::Rust => &["rs"],
            SourceLanguage::Java => &["java"],
            SourceLanguage::C => &["c"],
            SourceLanguage::Cpp => &["h", "hh", "hpp", "hxx", "tpp", "cc", "cpp", "cxx"],
            SourceLanguage::Python => &["py"],
            SourceLanguage::Kotlin => &["kt", "kts"],
        }
    }

    fn from_extension(extension: &OsStr) -> Option<Self> {
        let extension = extension.to_str()?;
        Self::all()
            .iter()
            .copied()
            .find(|lang| lang.extensions().contains(&extension))
    }

    /// The language of a source file, using its contents for a `.h` header, which could be C
    /// or C++.  A C header parsed as C++ breaks on identifiers that are C++ keywords, like
    /// `new` or `class`.
    pub(crate) fn from_contents(path: &Path, language: Self, contents: &str) -> Self {
        static CPP_REGEX: LazyLock<Regex> = LazyLock::new(|| {
            Regex::new(
                r"(?m)\bclass\s+\w+\s*[:{;]|\bnamespace\b|\btemplate\s*<|^\s*(public|private|protected)\s*:|::|\b(virtual|nullptr|constexpr|operator|typename)\b|^\s*#\s*include\s*<\w+>",
            )
            .unwrap()
        });
        let is_header = path.extension().is_some_and(|ext| ext == "h");
        if language == Self::Cpp && is_header && !CPP_REGEX.is_match(contents) {
            Self::C
        } else {
            language
        }
    }

    fn from_path(path: &Path) -> Option<Self> {
        match path.extension() {
            Some(extension) => Self::from_extension(extension),
            // Some languages might have well-known file names without an extension
            None => None,
        }
    }

    /// The query for the log statements in this language, which is compiled the first time it
    /// is needed and then shared, since compiling it takes longer than running it on most
    /// files.
    fn compiled_query(&self) -> &'static Query {
        static QUERIES: [OnceLock<Query>; 6] = [const { OnceLock::new() }; 6];
        let index = match self {
            SourceLanguage::Rust => 0,
            SourceLanguage::Java => 1,
            SourceLanguage::C => 2,
            SourceLanguage::Cpp => 3,
            SourceLanguage::Python => 4,
            SourceLanguage::Kotlin => 5,
        };
        QUERIES[index].get_or_init(|| {
            Query::new(&(*self).into(), self.get_query()).expect("the query is valid")
        })
    }

    fn get_query(&self) -> &str {
        match self {
            SourceLanguage::Rust => {
                // XXX: assumes it's a debug macro
                r#"
                    (macro_invocation macro: (_) @macro-name
                        (token_tree .
                            (string_literal) @log
                        )
                        ; standard macros that build strings or read files at compile time, but
                        ; not `format!`, whose messages end up in errors and output
                        (#not-match? @macro-name "(^|::)(vec|env|option_env|include|include_str|include_bytes|concat|stringify|compile_error)$")
                    )
                    ; a format string built with `concat!`, like `info!(concat!("a ", "{}"), x)`
                    (macro_invocation macro: (_) @macro-name
                        (token_tree .
                            (identifier) @_concat . "!" . (token_tree) @log
                        )
                        (#eq? @_concat "concat")
                        (#not-match? @macro-name "(^|::)(vec|env|option_env|include|include_str|include_bytes|concat|stringify|compile_error)$")
                    )
                    ; macros that take the level before the format string, like
                    ; `log!(Level::Warn, "...")` or `tracing::event!(Level::INFO, "...")`
                    (macro_invocation macro: (_) @macro-name
                        (token_tree .
                            (identifier) @_level . (string_literal) @log
                        )
                        (#match? @macro-name "(^|::)(log|event)$")
                        (#not-eq? @_level "target")
                    )
                    (macro_invocation macro: (_) @macro-name
                        (token_tree .
                            (identifier) . (identifier) . (string_literal) @log
                        )
                        (#match? @macro-name "(^|::)(log|event)$")
                    )
                    (macro_invocation macro: (_) @macro-name
                        (token_tree .
                            (identifier) . (identifier) . (identifier) . (string_literal) @log
                        )
                        (#match? @macro-name "(^|::)(log|event)$")
                    )
                    ; a message written by a `Display` or `Debug` impl, like `write!(f, "...")`
                    (macro_invocation macro: (_) @macro-name
                        (token_tree . (identifier) . (string_literal) @log)
                        (#match? @macro-name "^(write|writeln)$")
                    )
                    ; error and panic messages passed to a method, like `.context("...")`
                    (call_expression
                        function: (field_expression field: (field_identifier) @macro-name)
                        arguments: (arguments . (string_literal) @log)
                        (#match? @macro-name "^(context|with_context|wrap_err|wrap_err_with|expect|expect_err|ok_or)$")
                    )
                    ; thiserror's `#[error("...")]`
                    (attribute (identifier) @macro-name
                        arguments: (token_tree . (string_literal) @log)
                        (#eq? @macro-name "error")
                    )
                "#
            }
            SourceLanguage::Java => JAVA_QUERY.as_str(),
            SourceLanguage::C => C_QUERY.as_str(),
            SourceLanguage::Cpp => CPP_QUERY.as_str(),
            SourceLanguage::Python => {
                r#"
                (
                    (expression_statement
                      (call
                        function: (_) @func
                        arguments: (argument_list .
                          [(string) (concatenated_string) (binary_operator)] @args
                        )
                      )
                    )
                )
                ; `logger.log(logging.WARNING, "...")`
                (
                    (expression_statement
                      (call
                        function: (_) @func
                        arguments: (argument_list .
                          (_) . [(string) (concatenated_string) (binary_operator)] @args
                        )
                      )
                    )
                    (#match? @func "(^|\\.)log$")
                )
                ; `logger.info("{} done".format(name))`
                (
                    (expression_statement
                      (call
                        function: (_) @func
                        arguments: (argument_list .
                          (call
                            function: (attribute
                              object: [(string) (concatenated_string)]
                              attribute: (identifier) @_format)) @args
                        )
                      )
                    )
                    (#eq? @_format "format")
                )
                ; `logging.log(logging.INFO, "{} done".format(name))`
                (
                    (expression_statement
                      (call
                        function: (_) @func
                        arguments: (argument_list .
                          (_) .
                          (call
                            function: (attribute
                              object: [(string) (concatenated_string)]
                              attribute: (identifier) @_format)) @args
                        )
                      )
                    )
                    (#eq? @_format "format")
                    (#match? @func "(^|\\.)log$")
                )
                ; an exception, like `raise ValueError(f"...")`
                (raise_statement
                  (call
                    function: (_) @func
                    arguments: (argument_list .
                      [(string) (concatenated_string) (binary_operator)] @args
                    )
                  )
                )
                ; `raise ValueError("{} failed".format(name))`
                (
                  (raise_statement
                    (call
                      function: (_) @func
                      arguments: (argument_list .
                        (call
                          function: (attribute
                            object: [(string) (concatenated_string)]
                            attribute: (identifier) @_format)) @args
                      )
                    )
                  )
                  (#eq? @_format "format")
                )
                "#
            }
            SourceLanguage::Kotlin => {
                r#"
                    (call_expression
                        (navigation_expression
                            (identifier) @object-name
                            (identifier) @method-name)
                        (value_arguments .
                            (value_argument . [(string_literal) (binary_expression)] @arguments))
                        (#match? @object-name "log(ger)?|LOG(GER)?")
                        (#match? @method-name "debug|info|warn|trace|error")
                    )
                    ; kotlin-logging's lazy messages, like logger.info { "..." }
                    (call_expression
                        (navigation_expression
                            (identifier) @object-name
                            (identifier) @method-name)
                        (annotated_lambda
                            (lambda_literal [(string_literal) (binary_expression)] @arguments .))
                        (#match? @object-name "log(ger)?|LOG(GER)?")
                        (#match? @method-name "debug|info|warn|trace|error")
                    )
                    ; ... with a throwable, like logger.error(e) { "..." }
                    (call_expression
                        (call_expression
                            (navigation_expression
                                (identifier) @object-name
                                (identifier) @method-name))
                        (annotated_lambda
                            (lambda_literal [(string_literal) (binary_expression)] @arguments .))
                        (#match? @object-name "log(ger)?|LOG(GER)?")
                        (#match? @method-name "debug|info|warn|trace|error")
                    )
                "#
            }
        }
    }

    fn get_identifiers(&self) -> &[&str] {
        match self {
            SourceLanguage::Rust => IDENTS_RS,
            SourceLanguage::Java => IDENTS_JAVA,
            SourceLanguage::C | SourceLanguage::Cpp => IDENTS_CPP,
            SourceLanguage::Python => IDENTS_PYTHON,
            SourceLanguage::Kotlin => IDENTS_KOTLIN,
        }
    }

    fn get_placeholder_regex(&self) -> &'static Regex {
        match self {
            SourceLanguage::Rust => RUST_PLACEHOLDER_REGEX.deref(),
            SourceLanguage::Java => JAVA_PLACEHOLDER_REGEX.deref(),
            SourceLanguage::C => C_PLACEHOLDER_REGEX.deref(),
            SourceLanguage::Cpp => CPP_PLACEHOLDER_REGEX.deref(),
            SourceLanguage::Python => PYTHON_PLACEHOLDER_REGEX.deref(),
            SourceLanguage::Kotlin => KOTLIN_PLACEHOLDER_REGEX.deref(),
        }
    }

    fn captures_to_format_arg(&self, caps: &Captures) -> FormatArgument {
        for (index, cap) in caps.iter().skip(1).enumerate() {
            if let Some(cap) = cap {
                return match (self, index) {
                    (SourceLanguage::Rust | SourceLanguage::Java | SourceLanguage::Cpp, 0) => {
                        FormatArgument::Named(cap.as_str().to_string())
                    }
                    (SourceLanguage::Rust | SourceLanguage::Cpp, 1) => {
                        FormatArgument::Positional(cap.as_str().parse().unwrap())
                    }
                    _ => unreachable!(),
                };
            }
        }
        FormatArgument::Placeholder
    }
}

#[derive(PartialEq, Clone, Debug, Serialize)]
pub struct VariablePair {
    pub expr: String,
    pub value: String,
    /// The line could also be split so that this variable has a different value.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub ambiguous: bool,
}

#[derive(Serialize)]
pub struct LogMapping<'a, 's> {
    #[serde(rename(serialize = "logRef"))]
    pub log_ref: LogRef<'a>,
    #[serde(rename(serialize = "srcRef"))]
    pub src_ref: Option<StatementRef<'s>>,
    /// The text at the start of the message that no statement produced, like the device name
    /// that the Linux kernel's `dev_info()` adds, when the statement only produced the rest.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prefix: Option<&'a str>,
    pub variables: Vec<VariablePair>,
}

#[derive(Copy, Clone, Debug, PartialEq, Serialize)]
pub struct LogRef<'a> {
    #[serde(skip_serializing)]
    pub line: &'a str,
    #[serde(skip_serializing_if = "is_only_body")]
    pub details: Option<LogDetails<'a>>,
}

fn is_only_body(details: &Option<LogDetails>) -> bool {
    if let Some(details) = details {
        details.thread.is_none() && details.file.is_none() && details.lineno.is_none()
    } else {
        true
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Serialize, Default)]
pub struct LogDetails<'a> {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub thread: Option<&'a str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<&'a str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lineno: Option<usize>,
    #[serde(skip_serializing)]
    pub level: Option<LogLevel>,
    #[serde(skip_serializing)]
    pub body: Option<&'a str>,
}

impl<'a> LogDetails<'a> {
    fn is_empty(&self) -> bool {
        self.thread.is_none()
            && self.file.is_none()
            && self.lineno.is_none()
            && self.level.is_none()
            && self.body.is_none()
    }
}

#[derive(Default)]
pub struct LogRefBuilder<'a> {
    details: LogDetails<'a>,
}

impl<'a> LogRefBuilder<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn build_from_captures(self, captures: Captures<'a>, content: &'a str) -> LogRef<'a> {
        self.with_file(captures.name("file").map(|m| m.as_str()))
            .with_lineno(
                captures
                    .name("line")
                    .map(|m| m.as_str().parse::<usize>().unwrap_or_default()),
            )
            .with_thread(captures.name("thread").map(|m| m.as_str()))
            .with_level(captures.name("level").map(|m| m.as_str()))
            .with_body(captures.name("body").map(|m| m.as_str()))
            .build(content)
    }

    pub fn with_thread(mut self, thread: Option<&'a str>) -> Self {
        self.details.thread = thread;
        self
    }
    pub fn with_file(mut self, file: Option<&'a str>) -> Self {
        self.details.file = file;
        self
    }
    pub fn with_lineno(mut self, lineno: Option<usize>) -> Self {
        self.details.lineno = lineno;
        self
    }
    pub fn with_level(mut self, level: Option<&'a str>) -> Self {
        self.details.level = level.and_then(LogLevel::from_log_text);
        self
    }
    /// Like [`LogRefBuilder::with_level`], for a level that is already known instead of the
    /// text from the log message.  An `Unknown` level is the same as none.
    pub fn with_log_level(mut self, level: Option<LogLevel>) -> Self {
        self.details.level = level.filter(|level| *level != LogLevel::Unknown);
        self
    }

    pub fn with_body(mut self, body: Option<&'a str>) -> Self {
        // A stack trace after the message is not from the statement, like the exception that
        // was passed to `log.error("Failed to connect", e)`, so it is left out.
        self.details.body = body.map(|body| match trace_start(body) {
            Some(start) => body[..start].trim_end(),
            None => body,
        });
        self
    }

    pub fn build(self, line: &'a str) -> LogRef<'a> {
        let details = if self.details.is_empty() {
            None
        } else {
            Some(self.details)
        };
        LogRef { line, details }
    }
}

/// Where a Java or Python stack trace starts in the body of a log message, if it has one.  A
/// Java trace is one or more lines with an exception, like `java.io.IOException: closed` or
/// `Caused by: ...`, followed by a frame, like `\tat com.example.Foo.run(Foo.java:12)`.  A
/// Python trace starts with `Traceback (most recent call last):` followed by a frame, like
/// `  File "foo.py", line 12, in run`.  Only the start is found, since the frames are left to
/// the caller, like lnav, which finds them in the whole message.
fn trace_start(body: &str) -> Option<usize> {
    // A trace has more than one line, and most messages have only one.
    if !body.contains('\n') {
        return None;
    }
    let mut offset = 0;
    // Where the run of exception lines in front of the current line starts.
    let mut exceptions_start = None;
    let mut traceback_start = None;
    for line in body.split_inclusive('\n') {
        let start = offset;
        offset += line.len();
        let line = line.trim_end();
        if traceback_start.is_some() && line.trim_start().starts_with("File \"") {
            return traceback_start;
        }
        traceback_start = (line == "Traceback (most recent call last):").then_some(start);
        if exceptions_start.is_some() && is_java_frame(line) {
            return exceptions_start;
        }
        exceptions_start = if is_java_exception(line) {
            exceptions_start.or(Some(start))
        } else {
            None
        };
    }
    None
}

/// Check if a line of a Java stack trace is a frame, like `\tat com.example.Foo.run(...)`.
fn is_java_frame(line: &str) -> bool {
    let trimmed = line.trim_start();
    trimmed.len() < line.len() && trimmed.starts_with("at ")
}

/// Check if a line of a Java stack trace names an exception, like `java.io.IOException: closed`,
/// `MyError`, or `Caused by: ...`.
fn is_java_exception(line: &str) -> bool {
    let trimmed = line.trim_start();
    if trimmed.starts_with("Caused by:") || trimmed.starts_with("Suppressed:") {
        return true;
    }
    let class = line.split(':').next().unwrap_or(line);
    !class.is_empty()
        && !class.contains(char::is_whitespace)
        && (class.ends_with("Exception") || class.ends_with("Error"))
}

impl<'a> LogRef<'a> {
    /// The file name and line number of the log statement, if the message has both.
    fn file_and_line(self) -> Option<(&'a str, usize)> {
        match self.details {
            Some(LogDetails {
                file: Some(file),
                lineno: Some(lineno),
                ..
            }) => Some((file, lineno)),
            _ => None,
        }
    }

    pub fn body(self) -> &'a str {
        if let Some(LogDetails { body: Some(s), .. }) = self.details {
            s
        } else {
            self.line
        }
    }

    pub fn level(&self) -> Option<LogLevel> {
        self.details.and_then(|details| details.level)
    }
}

pub fn link_to_source<'a>(log_ref: &LogRef, sif: &'a StatementsInFile) -> Option<StatementRef<'a>> {
    let candidates = sif
        .statements()
        .sorted_by(|lhs, rhs| compare_candidates(lhs, rhs, None, log_ref.level()));
    first_match(candidates, log_ref.body(), None, |src_ref| src_ref.stmt)
}

pub fn lookup_source<'a>(
    log_ref: &LogRef,
    log_format: &LogFormat,
    sif: &'a StatementsInFile,
) -> Option<StatementRef<'a>> {
    if let Some(captures) = log_format.captures(log_ref.body()) {
        let file_name = captures.name("file").map_or("", |m| m.as_str());
        let line_no: usize = captures
            .name("line")
            .map_or(0, |m| m.as_str().parse::<usize>().unwrap_or_default());
        // println!("{:?} {:?}", file_name, line_no);

        sif.statements().find(|source_ref| {
            source_ref.source_path().contains(file_name) && source_ref.line_no == line_no
        })
    } else {
        None
    }
}

pub fn extract_variables(log_ref: &LogRef, src_ref: &Statement) -> Vec<VariablePair> {
    let line = match log_ref.details {
        Some(details) => details.body.unwrap_or(log_ref.line),
        None => log_ref.line,
    };
    extract_variables_from(line, src_ref)
}

/// Extract the values of the statement's placeholders from the text it produced.
fn extract_variables_from(line: &str, src_ref: &Statement) -> Vec<VariablePair> {
    extract_variables_with(line, src_ref, src_ref.pattern())
}

/// The variables in the text that `find_message_sources()` found the statement for, which
/// might only match the statement's relaxed pattern, like text whose whitespace was collapsed
/// or that does not have the whitespace the statement starts with.
pub(crate) fn find_variables(text: &str, src_ref: &Statement) -> Vec<VariablePair> {
    let pattern = if src_ref.pattern().is_match(text) {
        src_ref.pattern()
    } else {
        src_ref.relaxed_pattern()
    };
    extract_variables_with(text, src_ref, pattern)
}

/// [`extract_variables_from`] with the values found by `pattern`, which is the statement's
/// pattern or its relaxed pattern.
fn extract_variables_with(line: &str, src_ref: &Statement, pattern: &Regex) -> Vec<VariablePair> {
    let mut variables = Vec::new();
    if let Some(captures) = pattern.captures(line) {
        let exprs = src_ref.arg_exprs();
        let greedy = captures
            .iter()
            .skip(1)
            .map(|cap| cap.unwrap().range())
            .collect();
        let (ranges, ambiguous) = find_values(line, src_ref, greedy);
        for ((expr, range), ambiguous) in std::iter::zip(exprs, ranges).zip(ambiguous) {
            variables.push(VariablePair {
                expr: expr.to_string(),
                value: line[range].to_string(),
                ambiguous,
            });
        }
    }

    variables
}

/// Find the values of the placeholders in a line, starting from the greedy captures of the
/// statement's matcher, and whether each value is ambiguous.  The greedy captures give
/// everything to the first placeholder when the placeholders are next to each other, so the line
/// might be re-split using the kinds of values expected for each placeholder.
fn find_values(
    line: &str,
    src_ref: &Statement,
    greedy: Vec<Range<usize>>,
) -> (Vec<Range<usize>>, Vec<bool>) {
    let not_ambiguous = vec![false; greedy.len()];
    let kinds = src_ref.value_kinds();
    if let ([range], [kind]) = (&greedy[..], kinds) {
        // With one placeholder, there is only one way to split the line, but the value might
        // be padded.
        let value = kind
            .value_range(&line[range.clone()])
            .map_or(range.clone(), |value| {
                range.start + value.start..range.start + value.end
            });
        return (vec![value], not_ambiguous);
    }
    if greedy.len() < 2 || kinds.len() != greedy.len() {
        return (greedy, not_ambiguous);
    }
    // The lazy captures find the split with the shortest values for the earlier placeholders.
    // If that is the same as the greedy split, there is only one way to split the line.  The
    // lazy captures are skipped when a cheaper check shows there is no other split.
    let may_be_ambiguous = src_ref
        .separators()
        .is_none_or(|separators| value_kind::may_be_ambiguous(line, &greedy, separators));
    let lazy: Option<Vec<Range<usize>>> = src_ref
        .lazy_matcher()
        .filter(|_| may_be_ambiguous)
        .and_then(|matcher| matcher.captures(line))
        .map(|caps| {
            caps.iter()
                .skip(1)
                .map(|cap| cap.unwrap().range())
                .collect()
        });
    let unique = lazy.as_ref().is_none_or(|lazy| *lazy == greedy);
    if unique && value_kind::is_plausible(line, &greedy, kinds) {
        return (greedy, not_ambiguous);
    }
    let differs = |lhs: &[Range<usize>], rhs: &[Range<usize>]| -> Vec<bool> {
        std::iter::zip(lhs, rhs).map(|(l, r)| l != r).collect()
    };
    let split = |order| {
        src_ref.segment_matchers().and_then(|segments| {
            let choices = src_ref.choice_matchers().unwrap_or_default();
            value_kind::split_values(line, segments, kinds, choices, order)
        })
    };
    match split(SplitOrder::LongestFirst) {
        Some(longest) if unique => (longest, not_ambiguous),
        Some(longest) => {
            // The values that are the same whether the split prefers longer or shorter values
            // are not ambiguous.
            let ambiguous = split(SplitOrder::ShortestFirst)
                .map_or(not_ambiguous, |shortest| differs(&longest, &shortest));
            (longest, ambiguous)
        }
        // No split has values that look like their kinds, so use the greedy captures.
        None => {
            let ambiguous = lazy.map_or(not_ambiguous, |lazy| differs(&greedy, &lazy));
            (greedy, ambiguous)
        }
    }
}

pub fn extract_logging_guarded(sources: &[CodeSource], guard: &WorkGuard) -> Vec<StatementsInFile> {
    sources
        .par_iter()
        .flat_map(|code| {
            /// Where the "args" results go.  They belong to the message that precedes them, so
            /// they need to be dropped if that message was not usable.
            enum ArgsTarget {
                None,
                Statement,
                MessageRef,
            }

            let mut matched = vec![];
            let mut message_refs: Vec<MessageRef> = vec![];
            let mut arg_levels = BTreeSet::new();
            let mut args_target = ArgsTarget::None;
            let src_query = SourceQuery::new(code);
            let symbols = if code.info.language == SourceLanguage::Java {
                JavaSymbols::extract(&src_query)
            } else {
                Default::default()
            };
            let mut results = src_query.query(code.info.language.compiled_query(), None);
            let queried = results.len();
            // The query can read some of these too, like the start of
            // `event!(Level::INFO, count, "...")`, so its reading of them is dropped.
            let tracing_events = src_query.tracing_events();
            let tracing_messages: HashSet<usize> = tracing_events
                .iter()
                .filter(|result| result.kind == "string_literal")
                .map(|result| result.range.start_byte)
                .collect();
            results.extend(src_query.append_chains());
            results.extend(src_query.python_message_vars());
            results.extend(src_query.glyph_literals());
            results.extend(tracing_events);
            for (index, result) in results.into_iter().enumerate() {
                if index < queried
                    && result.kind == "string_literal"
                    && tracing_messages.contains(&result.range.start_byte)
                {
                    args_target = ArgsTarget::None;
                    continue;
                }
                // println!("node.kind()={:?} range={:?}", result.kind, result.range);
                match result.kind.as_str() {
                    "string_literal" | "string" | "concatenated_string" | "binary_expression" => {
                        args_target = ArgsTarget::None;
                        let from_arg = result.arg_level().is_some();
                        let mut result = result;
                        for part in &mut result.concat_parts {
                            if let ConcatPart::Expr {
                                text,
                                candidates,
                                constant_at: Some(at),
                                ..
                            } = part
                            {
                                *candidates = symbols.candidates(text, *at);
                            }
                        }
                        if let Some(src_ref) = Statement::new(code, result) {
                            if from_arg {
                                arg_levels.insert((src_ref.line_no, src_ref.column));
                            }
                            matched.push(src_ref);
                            args_target = ArgsTarget::Statement;
                        }
                    }
                    "message_ref" => {
                        let range = result.range;
                        let text = &code.buffer[range.start_byte..range.end_byte];
                        let level = result.level();
                        let line_no = range.start_point.row + 1;
                        let column = range.start_point.column;
                        if result.arg_level().is_some() {
                            arg_levels.insert((line_no, column));
                        }
                        message_refs.push(MessageRef {
                            line_no,
                            end_line_no: range.end_point.row + 1,
                            column,
                            name: result.name,
                            qualified_name: result.qualified_name,
                            block_id: result.block_id,
                            text: text.to_string(),
                            level,
                            call_name: result.call_name.clone(),
                            vars: vec![],
                            var_kinds: vec![],
                            candidates: symbols.candidates(text, range.start_byte),
                        });
                        args_target = ArgsTarget::MessageRef;
                    }
                    // Arguments are only kept for the message that precedes them.
                    "args" | "this" => {
                        if matches!(args_target, ArgsTarget::None) {
                            continue;
                        }
                        let range = result.range;
                        let source = code.buffer.as_str();
                        let text = source[range.start_byte..range.end_byte].to_string();
                        // eprintln!("text={} matched.len()={}", text, matched.len());
                        // check the text doesn't match any of the logging related identifiers
                        if code
                            .info
                            .language
                            .get_identifiers()
                            .iter()
                            .all(|&s| s != text.to_lowercase())
                        {
                            let end_line_no = result.range.end_point.row + 1;
                            let var = text.trim().to_string();
                            if let ArgsTarget::MessageRef = args_target {
                                let prior = message_refs.last_mut().unwrap();
                                prior.end_line_no = end_line_no;
                                prior.vars.push(var);
                                prior.var_kinds.push(result.value_kind);
                            } else {
                                let prior = matched.last_mut().unwrap();
                                prior.end_line_no = end_line_no;
                                prior.vars.push(var);
                                prior.var_kinds.push(result.value_kind);
                                prior.var_choices.push(result.value_choices);
                            }
                        }
                    }
                    _ => {} // eprintln!("ignoring {}", result.kind),
                }
                // println!("*****");
            }
            // Taken out after their arguments were added, since those follow the message, but
            // before the choices of the arguments add to the quality, since a continuation like
            // `pr_cont(" %s", on ? "on" : "off")` still has no literal text of its own.
            let (mut bare_continuations, mut matched): (Vec<_>, Vec<_>) = matched
                .into_iter()
                .partition(Statement::is_bare_continuation);
            matched.iter_mut().for_each(Statement::resolve_choices);
            bare_continuations
                .iter_mut()
                .for_each(Statement::resolve_choices);
            // The concatenations with constants are rebuilt once the constants are known.
            let (concats, matched): (Vec<_>, Vec<_>) = matched
                .into_iter()
                .partition(|stmt| !stmt.concat.is_empty());
            let constant_concats: Vec<ConstantConcat> = concats
                .into_iter()
                .map(|mut stmt| {
                    let parts = std::mem::take(&mut stmt.concat);
                    ConstantConcat { stmt, parts }
                })
                .collect();
            let macros = src_query.macro_wrappers();
            guard.inc(1);
            if matched.is_empty()
                && message_refs.is_empty()
                && constant_concats.is_empty()
                && symbols.constants.is_empty()
                && macros.is_empty()
            {
                None
            } else {
                Some(StatementsInFile {
                    path: code.filename.clone(),
                    language: code.info.language,
                    id: code.info.id,
                    arg_levels,
                    log_statements: matched,
                    bare_continuations,
                    resolved_statements: vec![],
                    derived_statements: vec![],
                    macros,
                    constants: symbols.constants,
                    message_refs,
                    constant_concats,
                })
            }
        })
        .collect()
}

pub fn extract_logging(sources: &[CodeSource], tracker: &ProgressTracker) -> Vec<StatementsInFile> {
    let guard = tracker.doing_work(sources.len() as u64, "files".to_string());
    extract_logging_guarded(sources, &guard)
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::{assert_snapshot, assert_yaml_snapshot};
    use std::ptr;

    fn from_log_format_and_line<'a>(buffer: &'a str, log_format: LogFormat) -> LogRef<'a> {
        let captures = log_format.captures(buffer).unwrap();
        LogRefBuilder::new().build_from_captures(captures, buffer)
    }

    #[test]
    fn test_source_language_extensions() {
        let ext = |e: &str| SourceLanguage::from_extension(OsStr::new(e));
        assert_eq!(ext("rs"), Some(SourceLanguage::Rust));
        assert_eq!(ext("kts"), Some(SourceLanguage::Kotlin));
        assert_eq!(ext("h"), Some(SourceLanguage::Cpp));
        assert_eq!(ext("c"), Some(SourceLanguage::C));
        assert_eq!(ext("RS"), None);
        assert_eq!(ext("txt"), None);
        // Every language has extensions, and no extension is two languages'.
        let mut seen = std::collections::HashSet::new();
        for lang in SourceLanguage::all() {
            assert!(!lang.extensions().is_empty(), "{:?}", lang);
            for e in lang.extensions() {
                assert!(seen.insert(*e), "{} is listed twice", e);
                assert_eq!(ext(e), Some(*lang));
            }
        }
    }

    #[test]
    fn test_source_language_names_are_lsp_ids() {
        use clap::ValueEnum;
        let expected = ["rust", "java", "c", "cpp", "python", "kotlin"];
        let langs = SourceLanguage::value_variants();
        assert_eq!(langs.len(), expected.len());
        for (lang, name) in langs.iter().zip(expected) {
            assert_eq!(lang.as_str(), name);
            assert_eq!(serde_json::to_string(lang).unwrap(), format!("\"{name}\""));
            assert_eq!(SourceLanguage::from_str(name, false), Ok(*lang));
        }
        assert_eq!(
            SourceLanguage::from_str("c++", false),
            Ok(SourceLanguage::Cpp)
        );
    }

    #[test]
    fn test_log_ref_builder() {
        let buffer = String::from(
            "2025-04-10 22:12:52 INFO  JvmPauseMonitor:146 - JvmPauseMonitor-n0: Started",
        );
        let regex = r"^(?<timestamp>\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}) (?<level>\w+)\s+ (?<file>[\w$.]+):(?<line>\d+) - (?<body>.*)$";
        let log_format: LogFormat = regex.try_into().unwrap();
        let captures = log_format.captures(&buffer).unwrap();
        let result = LogRefBuilder::new().build_from_captures(captures, &buffer);
        let details = Some(LogDetails {
            thread: None,
            file: Some("JvmPauseMonitor"),
            lineno: Some(146),
            level: Some(LogLevel::Info),
            body: Some("JvmPauseMonitor-n0: Started"),
        });
        assert_eq!(
            result,
            LogRef {
                line: "2025-04-10 22:12:52 INFO  JvmPauseMonitor:146 - JvmPauseMonitor-n0: Started",
                details
            }
        );
    }

    const TEST_SOURCE: &str = r#"
#[macro_use]
extern crate log;

fn main() {
    env_logger::init();
    debug!("you're only as funky as your last cut");
    for i in 0..3 {
        foo(i);
    }
}

fn foo(i: u32) {
    nope(i);
}

fn nope(i: u32, j: i32) {
    log::debug!("this won't match i={}; j={}", i, j);
}

fn namedarg0(salutation: &str, name: &str) {
    debug!("{salutation}, {name}!"); // lower quality than the next one
}

fn namedarg(name: &str) {
    let msg = format!("Goodbye, {name}!");
    debug!("Hello, {name}!");
}

fn namedarg2(salutation: &str, name: &str) {
    debug!("{salutation}, {name}!"); // lower quality than the previous one
}
    "#;

    #[test]
    fn test_extract_logging() {
        let code = CodeSource::from_string(Path::new("in-mem.rs"), TEST_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        assert_yaml_snapshot!(sif.statements().collect::<Vec<_>>());
    }

    #[test]
    fn test_link_to_source() {
        let lf = r#"^\[\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z \w+ \w+\]\s+(?<body>.*)"#
            .try_into()
            .unwrap();
        let log_ref = from_log_format_and_line(
            "[2024-05-09T19:58:53Z DEBUG main] you're only as funky as your last cut",
            lf,
        );
        let code = CodeSource::from_string(Path::new("in-mem.rs"), TEST_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 6);
        let result = link_to_source(&log_ref, &sif);
        assert!(ptr::eq(result.unwrap().stmt, &src_refs[0]));
    }

    #[test]
    fn test_link_to_quality_source() {
        let lf = r#"^\[\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z \w+ \w+\]\s+(?<body>.*)"#
            .try_into()
            .unwrap();
        let log_ref =
            from_log_format_and_line("[2024-05-09T19:58:53Z DEBUG main] Hello, Leander!", lf);
        let code = CodeSource::from_string(Path::new("in-mem.rs"), TEST_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let result = link_to_source(&log_ref, &sif);
        assert_yaml_snapshot!(result);
    }

    const MULTILINE_SOURCE: &str = r#"
#[macro_use]
extern crate log;

fn main() {
    env_logger::init();
    let adjective = "funky";
    debug!("you're only as {}\n as your last cut", adjective);
}
"#;
    #[test]
    fn test_link_multiline() {
        let lf = r#"^\[\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z \w+ \w+\]\s+(?<body>.*)"#
            .try_into()
            .unwrap();
        let log_ref = from_log_format_and_line(
            "[2024-05-09T19:58:53Z DEBUG main] you're only as funky\n as your last cut",
            lf,
        );
        let code = CodeSource::from_string(Path::new("in-mem.rs"), MULTILINE_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 1);
        let result = link_to_source(&log_ref, &sif);
        assert!(ptr::eq(result.unwrap().stmt, &src_refs[0]));
        let vars = extract_variables(&log_ref, &src_refs[0]);
        assert_eq!(
            vars,
            [VariablePair {
                expr: "adjective".to_string(),
                value: "funky".to_string(),
                ambiguous: false,
            }]
        );
    }

    #[test]
    fn test_link_to_source_no_matches() {
        let log_ref = LogRefBuilder::new().build("nope!");
        let code = CodeSource::from_string(Path::new("in-mem.rs"), TEST_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 6);
        let result = link_to_source(&log_ref, &sif);
        assert!(result.is_none());
    }

    #[test]
    fn test_extract_variables() {
        let log_ref = LogRefBuilder::new().build("this won't match i=1; j=2");
        let code = CodeSource::from_string(Path::new("in-mem.rs"), TEST_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 6);
        let vars = extract_variables(&log_ref, &src_refs[1]);
        assert_eq!(
            vars,
            vec![
                VariablePair {
                    expr: "i".to_string(),
                    value: "1".to_string(),
                    ambiguous: false,
                },
                VariablePair {
                    expr: "j".to_string(),
                    value: "2".to_string(),
                    ambiguous: false,
                }
            ]
        );
    }

    #[test]
    fn test_extract_named() {
        let log_ref = LogRefBuilder::new().build("Hello, Tim!");
        let code = CodeSource::from_string(Path::new("in-mem.rs"), TEST_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 6);
        let vars = extract_variables(&log_ref, &src_refs[4]);
        assert_eq!(
            vars,
            vec![VariablePair {
                expr: "name".to_string(),
                value: "Tim".to_string(),
                ambiguous: false,
            },]
        );
    }

    const TEST_PUNC_SRC: &str = r#"""
  private void run() {
    LOG.info("{}: Started", this);
    try {
      for (; Thread.currentThread().equals(threadRef.get()); ) {
        detectPause();
      }
    } finally {
      LOG.info("{}: Stopped", this);
    }
  }
"""#;
    #[test]
    fn test_extract_var_punctuation() {
        let lf =
            r"^(?<timestamp>\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}) (?<level>\w+)\s+ (?<file>[\w$.]+):(?<line>\d+) - (?<body>.*)$".try_into().unwrap();
        let log_ref = from_log_format_and_line(
            "2025-04-10 22:12:52 INFO  JvmPauseMonitor:146 - JvmPauseMonitor-n0: Started",
            lf,
        );
        let code = CodeSource::from_string(&PathBuf::from("in-mem.java"), TEST_PUNC_SRC);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 2);
        let vars = extract_variables(&log_ref, &src_refs[0]);
        assert_eq!(
            vars,
            vec![VariablePair {
                expr: "this".to_string(),
                value: "JvmPauseMonitor-n0".to_string(),
                ambiguous: false,
            },]
        );
    }

    const TEST_JUL_SRC: &str = r#"""
  void load(ClassLoader cl, Exception e) {
    LOGGER.log(Level.FINE, "Loading driver configuration via classloader {0}", cl);
    LOGGER.log(Level.WARNING, "Unexpected interrupt while executing onClean", e);
    LOGGER.isLoggable(Level.FINE);
    LOG.info("not a {}", "statement");
  }
"""#;

    #[test]
    fn test_extract_java_util_logging() {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.java"), TEST_JUL_SRC);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 3);
        assert_eq!(src_refs[2].text, r#""not a {}""#);
        let line = "Loading driver configuration via classloader jdk.internal.loader";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        assert!(ptr::eq(
            link_to_source(&log_ref, &sif).unwrap().stmt,
            &src_refs[0]
        ));
        let vars = extract_variables(&log_ref, &src_refs[0]);
        assert_eq!(
            vars,
            vec![VariablePair {
                expr: "cl".to_string(),
                value: "jdk.internal.loader".to_string(),
                ambiguous: false,
            },]
        );
        assert_eq!(src_refs[1].line_no, 4);
    }

    const TEST_JAVA_CONCAT_SRC: &str = r#"""
  void run(String name, String host, int a, int b) {
    LOGGER.log(Level.FINE, "Can''t find our classloader for the Driver; "
        + "attempting to use the thread context classloader");
    log.info("User " + name + " logged in from {}", host);
    log.info(a + b + " total");
    log.info(a + b);
    log.debug("sum=" + (a + b) + "!");
  }
"""#;

    #[test]
    fn test_extract_java_wrapped_message() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.java"),
            r#"
class Main {
  void run(String name, int count, Exception e) {
    LOG.info(String.format("Session '%s' expired after %d ms.%n", name, count));
    LOGGER.log(Level.WARNING, String.format(Locale.ROOT, "Cannot parse %s, 100%%", name), e);
    LOGGER.fine(() -> "sending " + name);
    LOGGER.log(Level.SEVERE, e, () -> "Uncaught exception in thread " + name);
    LOGGER.log(Level.FINER, () -> String.format("Jar file cache hit %16X", count));
    LOGGER.log(Level.CONFIG, "JAR Cache is not defined for channel {0}", name);
    LOG.info(name.toString());
    LOG.info(String.format("a " + name + " %s", count));
  }
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let found: Vec<(&str, LogLevel)> = src_refs
            .iter()
            .map(|s| (s.pattern().as_str(), s.level))
            .collect();
        assert_eq!(
            found,
            vec![
                (
                    "(?s)^Session '(.*)' expired after (.*) ms\\.\\s*$",
                    LogLevel::Info
                ),
                ("(?s)^Cannot parse (.*), 100%$", LogLevel::Warn),
                ("(?s)^sending (.*)$", LogLevel::Debug),
                ("(?s)^Uncaught exception in thread (.*)$", LogLevel::Error),
                ("(?s)^Jar file cache hit (.*)$", LogLevel::Trace),
                (
                    "(?s)^JAR Cache is not defined for channel (.*)$",
                    LogLevel::Info
                ),
            ]
        );
        assert_eq!(src_refs[0].vars, vec!["name", "count"]);
        assert_eq!(src_refs[1].vars, vec!["name"]);

        let line = "Session 'abc' expired after 10 ms.\n";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        assert_eq!(
            extract_variables(&log_ref, &src_refs[0]),
            vec![
                VariablePair {
                    expr: "name".to_string(),
                    value: "abc".to_string(),
                    ambiguous: false,
                },
                VariablePair {
                    expr: "count".to_string(),
                    value: "10".to_string(),
                    ambiguous: false,
                },
            ]
        );
    }

    #[test]
    fn test_extract_java_concatenation() {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.java"), TEST_JAVA_CONCAT_SRC);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(
            patterns,
            vec![
                "(?s)^Can''t find our classloader for the Driver; attempting to use the thread context classloader$",
                "(?s)^User (.*) logged in from (.*)$",
                "(?s)^(.*) total$",
                "(?s)^sum=(.*)!$",
            ]
        );
        assert_eq!((src_refs[0].line_no, src_refs[0].end_line_no), (3, 4));

        let line = "User alice logged in from example.com";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        assert_eq!(
            extract_variables(&log_ref, &src_refs[1]),
            vec![
                VariablePair {
                    expr: "name".to_string(),
                    value: "alice".to_string(),
                    ambiguous: false,
                },
                VariablePair {
                    expr: "host".to_string(),
                    value: "example.com".to_string(),
                    ambiguous: false,
                },
            ]
        );

        let line = "42 total";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        assert_eq!(
            extract_variables(&log_ref, &src_refs[2]),
            vec![VariablePair {
                expr: "a + b".to_string(),
                value: "42".to_string(),
                ambiguous: false,
            }]
        );
        assert_eq!(
            src_refs[3].args,
            vec![FormatArgument::Named("(a + b)".to_string())]
        );
    }

    const MESSAGES_SRC: &str = r#"package com.example.cc;

class Messages {
    static final String LOG_INIT_GROUND_PROXY = "Starting ground proxy" +
            " with CloudProxy {}, JCC {}:{}";
    static final String LOG_KEY_FILE = "Key material file: {}";
}
"#;

    const OTHER_MESSAGES_SRC: &str = r#"package com.example.config;

public class Messages {
    public static final String LOG_KEY_FILE = "Config key file: {}";
    public static final String LOG_LOADED = "Loaded {} keys";
}
"#;

    const CALLER_SRC: &str = r#"package com.example.cc;

import static com.example.config.Messages.*;

class Caller {
    void start(String uri, String host, int port, String name) {
        log.info(Messages.LOG_INIT_GROUND_PROXY, uri, host,
                port);
        log.debug(Messages.LOG_KEY_FILE, name);
        log.debug(LOG_LOADED, port - 1);
        log.info(Messages.NOT_DEFINED, name);
    }
}
"#;

    fn write_message_tree(root: &Path) {
        for (path, src) in [
            ("com/example/cc/Messages.java", MESSAGES_SRC),
            ("com/example/config/Messages.java", OTHER_MESSAGES_SRC),
            ("com/example/cc/Caller.java", CALLER_SRC),
        ] {
            let path = root.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, src).unwrap();
        }
    }

    fn matcher_for(root: &Path) -> LogMatcher {
        let tracker = ProgressTracker::new();
        let mut matcher = LogMatcher::new();
        matcher.add_root(root).unwrap();
        assert!(matcher.discover_sources(&tracker).is_empty());
        matcher.extract_log_statements(&tracker);
        matcher
    }

    /// Match the message and return the line number and variables of the statement.
    fn match_message(matcher: &LogMatcher, msg: &str) -> Option<(usize, Vec<(String, String)>)> {
        let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
        matcher
            .match_log_statement(&log_ref, &LogMatchOptions::default())
            .map(|mapping| {
                let src_ref = mapping.src_ref.unwrap();
                assert!(src_ref.source_path().ends_with("Caller.java"));
                (
                    src_ref.line_no,
                    mapping
                        .variables
                        .into_iter()
                        .map(|var| (var.expr, var.value))
                        .collect(),
                )
            })
    }

    const DUP_SRC: &str = r#"package com.example;

class Dup {
    void run(int count) {
        log.info("count is {}", count);
        log.info("total is {}", count);
    }
}
"#;

    #[test]
    fn test_line_cache() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir.path().join("com/example/Dup.java");
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, DUP_SRC).unwrap();
        let mut matcher = matcher_for(temp_dir.path());

        let match_line = |matcher: &LogMatcher, msg: &str| {
            let log_ref = LogRefBuilder::new()
                .with_file(Some("Dup.java"))
                .with_lineno(Some(6))
                .with_body(Some(msg))
                .build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|mapping| mapping.src_ref)
                .map(|src_ref| src_ref.line_no)
        };
        let cached_lines = |matcher: &LogMatcher| {
            let coll = matcher.roots.values().next().unwrap();
            let cache = coll.line_cache.read().unwrap();
            let file_id = coll.file_name_to_sources["Dup.java"][0];
            let mut lines: Vec<usize> = cache
                .get(&(file_id, 6))
                .into_iter()
                .flatten()
                .map(|(file_id, index)| {
                    coll.files_with_statements[file_id]
                        .statement(*index)
                        .unwrap()
                        .line_no
                })
                .collect();
            lines.sort();
            lines
        };

        assert_eq!(match_line(&matcher, "total is 3"), Some(6));
        assert_eq!(cached_lines(&matcher), vec![6]);
        // Found in the cache, so nothing is added.
        assert_eq!(match_line(&matcher, "total is 4"), Some(6));
        assert_eq!(cached_lines(&matcher), vec![6]);
        // The cached statement doesn't match, so fall back to the prefilter and remember it.
        assert_eq!(match_line(&matcher, "count is 3"), Some(5));
        assert_eq!(cached_lines(&matcher), vec![5, 6]);
        assert_eq!(match_line(&matcher, "nothing like it"), None);
        assert_eq!(cached_lines(&matcher), vec![5, 6]);

        // A change to the source clears the cache.
        fs::write(&path, DUP_SRC.replace("class Dup {", "class Dup {\n")).unwrap();
        let tracker = ProgressTracker::new();
        assert!(matcher.discover_sources(&tracker).is_empty());
        matcher.extract_log_statements(&tracker);
        assert_eq!(cached_lines(&matcher), Vec::<usize>::new());
        assert_eq!(match_line(&matcher, "count is 3"), Some(6));
        assert_eq!(cached_lines(&matcher), vec![6]);
    }

    #[test]
    fn test_line_cache_unmatched() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir.path().join("com/example/Dup.java");
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, DUP_SRC).unwrap();
        let mut matcher = matcher_for(temp_dir.path());

        let match_line = |matcher: &LogMatcher, msg: &str, fallback: bool| {
            let log_ref = LogRefBuilder::new()
                .with_file(Some("Dup.java"))
                .with_lineno(Some(20))
                .with_body(Some(msg))
                .build(msg);
            let options = LogMatchOptions {
                fallback,
                ..LogMatchOptions::default()
            };
            matcher
                .match_log_statement(&log_ref, &options)
                .and_then(|mapping| mapping.src_ref)
                .map(|src_ref| src_ref.line_no)
        };
        let cached = |matcher: &LogMatcher| {
            let coll = matcher.roots.values().next().unwrap();
            let file_id = coll.file_name_to_sources["Dup.java"][0];
            coll.line_cache.read().unwrap().get(&(file_id, 20)).cloned()
        };

        // Not remembered when looking for other kinds of statements too.
        assert_eq!(match_line(&matcher, "nothing like it", true), None);
        assert_eq!(cached(&matcher), None);
        assert_eq!(match_line(&matcher, "nothing like it", false), None);
        assert_eq!(cached(&matcher), Some(vec![]));
        // Remembered, so a message with the same file and line is not looked for...
        assert_eq!(match_line(&matcher, "count is 3", false), None);
        // ...unless other kinds of statements are wanted too.
        assert_eq!(match_line(&matcher, "count is 3", true), Some(5));

        // A change to the source forgets it.
        fs::write(&path, DUP_SRC.replace("class Dup {", "class Dup {\n")).unwrap();
        let tracker = ProgressTracker::new();
        assert!(matcher.discover_sources(&tracker).is_empty());
        matcher.extract_log_statements(&tracker);
        assert_eq!(cached(&matcher), None);
        assert_eq!(match_line(&matcher, "count is 3", false), Some(6));
    }

    #[test]
    fn test_line_cache_ambiguous_name() {
        let temp_dir = tempfile::tempdir().unwrap();
        let generic = temp_dir.path().join("com/a/Dup.java");
        let specific = temp_dir.path().join("com/b/Dup.java");
        fs::create_dir_all(generic.parent().unwrap()).unwrap();
        fs::create_dir_all(specific.parent().unwrap()).unwrap();
        fs::write(
            &generic,
            "package com.a;\n\nclass Dup {\n    void run(String msg) {\n        log.info(\"count {}\", msg);\n    }\n}\n",
        )
        .unwrap();
        fs::write(&specific, DUP_SRC).unwrap();
        let matcher = matcher_for(temp_dir.path());

        let match_path = |msg: &str| {
            let log_ref = LogRefBuilder::new()
                .with_file(Some("Dup.java"))
                .with_lineno(Some(6))
                .with_body(Some(msg))
                .build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|mapping| mapping.src_ref)
                .map(|src_ref| src_ref.source_path().to_string())
        };

        assert!(match_path("count xyz").unwrap().ends_with("com/a/Dup.java"));
        // The generic statement also matches, but must not hide the better one in the other file.
        assert!(match_path("count is 3")
            .unwrap()
            .ends_with("com/b/Dup.java"));
        let coll = matcher.roots.values().next().unwrap();
        assert!(coll.line_cache.read().unwrap().is_empty());
    }

    #[test]
    fn test_match_file_name_is_part_of_path() {
        let temp_dir = tempfile::tempdir().unwrap();
        let generic = temp_dir.path().join("com/a/Dup.java");
        let specific = temp_dir.path().join("com/b/Dup.java");
        fs::create_dir_all(generic.parent().unwrap()).unwrap();
        fs::create_dir_all(specific.parent().unwrap()).unwrap();
        fs::write(
            &generic,
            "package com.a;\n\nclass Dup {\n    void run(String msg) {\n        log.info(\"count {}\", msg);\n    }\n}\n",
        )
        .unwrap();
        fs::write(&specific, DUP_SRC).unwrap();
        let matcher = matcher_for(temp_dir.path());

        let match_path = |file: &str, msg: &str| {
            let log_ref = LogRefBuilder::new()
                .with_file(Some(file))
                .with_body(Some(msg))
                .build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|mapping| mapping.src_ref)
                .map(|src_ref| src_ref.source_path().to_string())
        };

        // A file name that is not the name of a file is looked for in the paths.
        assert!(match_path("a/Dup.java", "count is 3")
            .unwrap()
            .ends_with("com/a/Dup.java"));
        assert!(match_path("b/Dup.java", "count is 3")
            .unwrap()
            .ends_with("com/b/Dup.java"));
        // Asked again, the files for the name are remembered.
        assert!(match_path("a/Dup.java", "count xyz")
            .unwrap()
            .ends_with("com/a/Dup.java"));
        // An absolute path from another machine, like a build directory in a `file!()`, is
        // the file that shares the most of its trailing components.
        assert!(match_path("/build/tmp/src/com/b/Dup.java", "count is 3")
            .unwrap()
            .ends_with("com/b/Dup.java"));
        assert!(match_path("/build/tmp/src/com/a/Dup.java", "count is 3")
            .unwrap()
            .ends_with("com/a/Dup.java"));
        // No statement is in a file that is not in the tree, like one in a library.
        assert_eq!(match_path("Other.java", "count is 3"), None);
        assert_eq!(match_path("/build/tmp/src/Other.java", "count is 3"), None);
        let coll = matcher.roots.values().next().unwrap();
        assert_eq!(coll.files_by_name.read().unwrap().len(), 6);
    }

    const SAME_TEXT_SRC: &str = r#"package com.example;

class Same {
    void start(int count) {
        log.info("count is {}", count);
    }

    void stop(int count) {
        log.info("count is {}", count);
    }
}
"#;

    #[test]
    fn test_closest_line() {
        let temp_dir = tempfile::tempdir().unwrap();
        let first = temp_dir.path().join("com/a/Same.java");
        let second = temp_dir.path().join("com/b/Same.java");
        fs::create_dir_all(first.parent().unwrap()).unwrap();
        fs::create_dir_all(second.parent().unwrap()).unwrap();
        fs::write(&first, SAME_TEXT_SRC).unwrap();
        // Shift the statements so they are on different lines from the first file.
        fs::write(
            &second,
            SAME_TEXT_SRC.replace("class Same {", "class Same {\n\n\n\n\n"),
        )
        .unwrap();
        let matcher = matcher_for(temp_dir.path());

        let match_line = |lineno: Option<usize>| {
            let msg = "count is 3";
            let log_ref = LogRefBuilder::new()
                .with_file(Some("Same.java"))
                .with_lineno(lineno)
                .with_body(Some(msg))
                .build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|mapping| mapping.src_ref)
                .map(|src_ref| {
                    let dir = if src_ref.source_path().ends_with("com/a/Same.java") {
                        "a"
                    } else {
                        "b"
                    };
                    (dir, src_ref.line_no)
                })
        };

        assert_eq!(match_line(Some(5)), Some(("a", 5)));
        assert_eq!(match_line(Some(9)), Some(("a", 9)));
        assert_eq!(match_line(Some(10)), Some(("b", 10)));
        assert_eq!(match_line(Some(14)), Some(("b", 14)));
        // Not exactly on a statement, so the nearest one.
        assert_eq!(match_line(Some(8)), Some(("a", 9)));
        // Equally close to a:5 and a:9, so the earlier one.
        assert_eq!(match_line(Some(7)), Some(("a", 5)));
        assert_eq!(match_line(Some(100)), Some(("b", 14)));
        // Without a line number, any of them will do.
        assert!(match_line(None).is_some());
    }

    #[test]
    fn test_closest_line_cached() {
        let temp_dir = tempfile::tempdir().unwrap();
        let path = temp_dir.path().join("com/example/Same.java");
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, SAME_TEXT_SRC).unwrap();
        let matcher = matcher_for(temp_dir.path());

        let match_line = |lineno: usize| {
            let msg = "count is 3";
            let log_ref = LogRefBuilder::new()
                .with_file(Some("Same.java"))
                .with_lineno(Some(lineno))
                .with_body(Some(msg))
                .build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|mapping| mapping.src_ref)
                .map(|src_ref| src_ref.line_no)
        };

        // The second lookup for each line is answered by the cache.
        for _ in 0..2 {
            assert_eq!(match_line(9), Some(9));
            assert_eq!(match_line(5), Some(5));
        }
    }

    fn vars(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
        pairs
            .iter()
            .map(|(expr, value)| (expr.to_string(), value.to_string()))
            .collect()
    }

    #[test]
    fn test_message_constants() {
        let temp_dir = tempfile::tempdir().unwrap();
        write_message_tree(temp_dir.path());
        let matcher = matcher_for(temp_dir.path());

        assert_eq!(
            match_message(
                &matcher,
                "Starting ground proxy with CloudProxy http://proxy, JCC localhost:8090"
            ),
            Some((
                7,
                vars(&[
                    ("uri", "http://proxy"),
                    ("host", "localhost"),
                    ("port", "8090")
                ])
            ))
        );
        // The same name in two packages resolves to the one for the caller's package.
        assert_eq!(
            match_message(&matcher, "Key material file: /etc/key.pem"),
            Some((9, vars(&[("name", "/etc/key.pem")])))
        );
        assert_eq!(
            match_message(&matcher, "Config key file: /etc/key.pem"),
            None
        );
        // A bare name from a static import.
        assert_eq!(
            match_message(&matcher, "Loaded 3 keys"),
            Some((10, vars(&[("port - 1", "3")])))
        );
        let caller: Vec<StatementRef> = matcher
            .statements()
            .filter(|stmt| stmt.source_path().ends_with("Caller.java"))
            .collect();
        assert_eq!(caller.len(), 3);
        assert!(caller
            .iter()
            .all(|stmt| stmt.qualified_name == "com.example.cc.Caller.start"));
    }

    #[test]
    fn test_message_constants_change() {
        let temp_dir = tempfile::tempdir().unwrap();
        let root = temp_dir.path();
        write_message_tree(root);
        let tracker = ProgressTracker::new();
        let mut matcher = matcher_for(root);

        // Only the file with the constants changes, the caller is not re-extracted.
        let messages_path = root.join("com/example/cc/Messages.java");
        fs::write(
            &messages_path,
            MESSAGES_SRC.replace("Key material file", "Key file is"),
        )
        .unwrap();
        let later = SystemTime::now() + std::time::Duration::from_secs(5);
        File::options()
            .write(true)
            .open(&messages_path)
            .unwrap()
            .set_modified(later)
            .unwrap();
        let _ = matcher.discover_sources(&tracker);
        let summary = matcher.extract_log_statements(&tracker);
        assert_eq!((summary.new, summary.deleted), (1, 1));

        assert_eq!(
            match_message(&matcher, "Key material file: /etc/key.pem"),
            None
        );
        assert_eq!(
            match_message(&matcher, "Key file is: /etc/key.pem"),
            Some((9, vars(&[("name", "/etc/key.pem")])))
        );
        assert_eq!(matcher.statements().count(), 3);
    }

    const CONCAT_CALLER_SRC: &str = r#"package com.example.cc;

class Balancer {
    static final String LOAD_BALANCING_PREFIX = "LOAD_BALANCING";

    void run(String node, String name, int port) {
        log.info(LOAD_BALANCING_PREFIX + ": " + node);
        log.info(Messages.LOG_KEY_FILE + " (from " + name + ")", node);
        log.info(Library.TAG + ": " + node);
        log.info(Library.TAG + node);
        log.info("Prefix is " + LOAD_BALANCING_PREFIX);
    }
}
"#;

    fn write_concat_tree(root: &Path) {
        write_message_tree(root);
        let path = root.join("com/example/cc/Balancer.java");
        fs::write(path, CONCAT_CALLER_SRC).unwrap();
    }

    #[test]
    fn test_message_constant_concatenation() {
        let temp_dir = tempfile::tempdir().unwrap();
        write_concat_tree(temp_dir.path());
        let matcher = matcher_for(temp_dir.path());
        let balancer = |matcher: &LogMatcher| -> Vec<String> {
            let mut patterns: Vec<String> = matcher
                .statements()
                .filter(|stmt| stmt.source_path().ends_with("Balancer.java"))
                .map(|stmt| stmt.pattern().as_str().to_string())
                .collect();
            patterns.sort();
            patterns
        };
        let match_message = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .map(|mapping| {
                    let src_ref = mapping.src_ref.unwrap();
                    assert!(src_ref.source_path().ends_with("Balancer.java"));
                    let vars: Vec<(String, String)> = mapping
                        .variables
                        .into_iter()
                        .map(|var| (var.expr, var.value))
                        .collect();
                    (src_ref.line_no, vars)
                })
        };

        // A constant in the same class, one in another file, and one that is not in the tree,
        // which is left as a placeholder, unless that leaves no literal text at all.
        assert_eq!(
            balancer(&matcher),
            vec![
                "(?s)^(.*): (.*)$",
                "(?s)^Key material file: (.*) \\(from (.*)\\)$",
                "(?s)^LOAD_BALANCING: (.*)$",
                "(?s)^Prefix is LOAD_BALANCING$",
            ]
        );
        assert_eq!(
            match_message("LOAD_BALANCING: node-1"),
            Some((7, vars(&[("node", "node-1")])))
        );
        // The placeholder from the constant takes the call's argument, and the expression
        // concatenated after it is its own value.
        assert_eq!(
            match_message("Key material file: /etc/key.pem (from proxy)"),
            Some((8, vars(&[("node", "/etc/key.pem"), ("name", "proxy")])))
        );

        // From the cache, the constants are resolved again.
        let cache = Cache {
            location: temp_dir.path().join("cache"),
        };
        let tracker = ProgressTracker::new();
        matcher.cache_to(&cache, &tracker).unwrap();
        let mut cached = LogMatcher::new();
        cached.add_root(temp_dir.path()).unwrap();
        assert!(cached.load_from_cache(&cache, &tracker).is_empty());
        let _ = cached.discover_sources(&tracker);
        assert_eq!(cached.extract_log_statements(&tracker).changes(), 0);
        assert_eq!(balancer(&cached), balancer(&matcher));
    }

    /// Get the totals of the deterministic work reported to the listener so far.
    fn work_totals(listener: &progress::ProgressListener) -> Vec<(u64, String)> {
        let mut retval = Vec::new();
        while let Some(update) = listener.try_next_for(std::time::Duration::from_millis(10)) {
            if let ProgressUpdate::Work(info) = update {
                retval.push((info.total, info.units.clone()));
            }
        }
        retval
    }

    #[test]
    fn test_progress_totals() {
        let temp_dir = tempfile::tempdir().unwrap();
        let root = temp_dir.path().join("src");
        write_message_tree(&root);
        let cache = Cache {
            location: temp_dir.path().join("cache"),
        };
        let mut tracker = ProgressTracker::new();
        let listener = tracker.subscribe();
        let mut matcher = LogMatcher::new();
        matcher.add_root(&root).unwrap();
        let _ = matcher.discover_sources(&tracker);
        matcher.extract_log_statements(&tracker);
        matcher.cache_to(&cache, &tracker).unwrap();
        assert_eq!(
            work_totals(&listener),
            vec![
                (1, "paths".to_string()),
                (3, "files".to_string()),
                (1, "root".to_string())
            ]
        );

        // Loading reports the size of the cache file.
        let cache_size: u64 = fs::read_dir(&cache.location)
            .unwrap()
            .map(|entry| entry.unwrap().metadata().unwrap().len())
            .sum();
        let mut matcher = LogMatcher::new();
        matcher.add_root(&root).unwrap();
        assert!(matcher.load_from_cache(&cache, &tracker).is_empty());
        assert_eq!(
            work_totals(&listener),
            vec![(cache_size, "bytes".to_string())]
        );

        // Only the changed file is counted when extracting.
        let caller_path = root.join("com/example/cc/Caller.java");
        let later = SystemTime::now() + std::time::Duration::from_secs(5);
        File::options()
            .write(true)
            .open(&caller_path)
            .unwrap()
            .set_modified(later)
            .unwrap();
        let _ = matcher.discover_sources(&tracker);
        matcher.extract_log_statements(&tracker);
        assert_eq!(
            work_totals(&listener),
            vec![(1, "paths".to_string()), (1, "files".to_string())]
        );
    }

    #[test]
    fn test_nested_roots_find_statements_once() {
        let temp_dir = tempfile::tempdir().unwrap();
        let project = temp_dir.path().join("project");
        let src = project.join("src");
        write_message_tree(&src);
        let caller = src
            .join("com/example/cc/Caller.java")
            .canonicalize()
            .unwrap();
        let count = |matcher: &LogMatcher| -> usize {
            matcher
                .find_source_file_statements(&caller)
                .iter()
                .map(|stmts| stmts.statements().count())
                .sum()
        };
        let tracker = ProgressTracker::new();

        // The parent added after the child replaces it.
        let mut matcher = LogMatcher::new();
        matcher.add_root(&src).unwrap();
        matcher.add_root(&project).unwrap();
        assert!(matcher.discover_sources(&tracker).is_empty());
        matcher.extract_log_statements(&tracker);
        let once = count(&matcher);
        assert!(once > 0);
        assert_eq!(matcher.find_source_file_statements(&caller).len(), 1);

        // The child added after the parent is already covered.
        let mut matcher = LogMatcher::new();
        matcher.add_root(&project).unwrap();
        matcher.add_root(&src).unwrap();
        assert!(matcher.discover_sources(&tracker).is_empty());
        matcher.extract_log_statements(&tracker);
        assert_eq!(count(&matcher), once);
    }

    #[test]
    fn test_match_explains_rest_of_message() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(
            temp_dir.path().join("hub.rs"),
            r#"fn announce(dev: &str, mfr: u32) {
    warn!("{}: {}", dev, mfr);
    info!("New USB device strings: Mfr={}", mfr);
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(temp_dir.path());
        let matched = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|mapping| {
                    let vars: Vec<(String, String)> = mapping
                        .variables
                        .into_iter()
                        .map(|var| (var.expr, var.value))
                        .collect();
                    mapping.src_ref.map(|src_ref| (src_ref.line_no, vars))
                })
        };

        // A generic statement matches all of the line, but most of it is explained by the
        // statement for the text after the device name, whose values are taken from that text.
        assert_eq!(
            matched("usb 1-5: New USB device strings: Mfr=3"),
            Some((3, vec![("mfr".to_string(), "3".to_string())]))
        );
        // A line that is mostly explained by a generic statement keeps it.
        assert_eq!(
            matched("usb 1-5: 3"),
            Some((
                2,
                vec![
                    ("dev".to_string(), "usb 1-5".to_string()),
                    ("mfr".to_string(), "3".to_string())
                ]
            ))
        );
    }

    #[test]
    fn test_match_explains_rest_of_long_message() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(
            temp_dir.path().join("dump.rs"),
            r#"fn dump(dev: &str, mfr: &str, count: u32, when: &str) {
    warn!("{}: {}", dev, mfr);
    info!("New USB device strings: Mfr={}", mfr);
    info!("Dump of {} threads at {}", count, when);
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(temp_dir.path());
        let matched = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            let mapping = matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .unwrap();
            let vars: Vec<(String, String)> = mapping
                .variables
                .into_iter()
                .map(|var| (var.expr, var.value))
                .collect();
            (mapping.src_ref.unwrap().line_no, vars)
        };

        // A statement that matches all of a long message is still found, though only its
        // start is read for a prefix or a chain.
        let threads = "\"main\": running\n\"worker-1\": waiting\n".repeat(50);
        let when = format!("noon\n\n{threads}");
        assert_eq!(
            matched(&format!("Dump of 100 threads at {when}")),
            (
                4,
                vec![
                    ("count".to_string(), "100".to_string()),
                    ("when".to_string(), when)
                ]
            )
        );
        // Only the start of the line is read, but the statement after the prefix produced the
        // rest too, so its values are taken from all of it.
        let mfr = "3".repeat(2 * message_source::MAX_LOG_HEAD_LEN);
        assert_eq!(
            matched(&format!("usb 1-5: New USB device strings: Mfr={mfr}")),
            (3, vec![("mfr".to_string(), mfr.clone())])
        );
        // The head of a long message is cut at a line break, without the '\r' of a CRLF.
        let lines = "more\r\n".repeat(400);
        assert_eq!(
            matched(&format!(
                "usb 1-5: New USB device strings: Mfr=3\r\n{lines}"
            )),
            (
                3,
                vec![(
                    "mfr".to_string(),
                    format!("3\r\n{lines}").trim_end().to_string()
                )]
            )
        );
    }

    #[test]
    fn test_match_prefixed_multi_line_message() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(
            temp_dir.path().join("multi.rs"),
            r#"fn multi(dev: &str, mfr: &str, count: u32) {
    warn!("{}: {}", dev, mfr);
    info!("Line one\nLine two {}", count);
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(temp_dir.path());
        let msg = "usb 1-5: Line one\nLine two 42";
        let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
        let mapping = matcher
            .match_log_statement(&log_ref, &LogMatchOptions::default())
            .unwrap();
        assert_eq!(mapping.src_ref.unwrap().line_no, 3);
        assert_eq!(mapping.variables[0].value, "42");
    }

    #[test]
    fn test_match_explains_rest_of_message_keeps_evidence() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(
            temp_dir.path().join("disk.rs"),
            r#"fn check(dev: &str, ctl: &str) -> String {
    warn!("Got {} from {}", dev, ctl);
    let err = format!("disk failure on {}", dev);
    let chained = format!("Controller {} reset", ctl);
    warn!("Got {} from {}", dev, ctl);
    err
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(temp_dir.path());
        let matched_with = |msg: &str, lineno: Option<usize>, fallback: bool| {
            let log_ref = LogRefBuilder::new()
                .with_body(Some(msg))
                .with_lineno(lineno)
                .build(msg);
            let options = LogMatchOptions {
                fallback,
                ..LogMatchOptions::default()
            };
            let mapping = matcher.match_log_statement(&log_ref, &options)?;
            Some((
                mapping.src_ref.unwrap().line_no,
                mapping.prefix.map(str::to_string),
            ))
        };
        let matched = |msg: &str, lineno: Option<usize>| matched_with(msg, lineno, false).unwrap();
        // The values of the line are explained by other statements, but the reading of all of
        // it does not change which of the statements that match all of it is the best.
        let msg = "Got disk failure on sda1 from controller zero";
        assert_eq!(matched(msg, Some(5)), (5, None));
        assert_eq!(matched(msg, Some(2)), (2, None));
        // The text in front of a chain of messages is not from any statement.  The chain is
        // from formatted messages, not a logging call, so it is only used with the fallback.
        let chain = "usb 1-5: disk failure on sda1: Controller one reset";
        assert_eq!(
            matched_with(chain, None, true),
            Some((3, Some("usb 1-5".to_string())))
        );
        assert_eq!(matched_with(chain, None, false), None);
    }

    #[test]
    fn test_match_through_call_chain() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(
            temp_dir.path().join("hub.c"),
            r#"static void show_string(int dev, const char *id, const char *value)
{
    syslog(LOG_INFO, "%s: %s\n", id, value);
}

static void announce(int dev, const char *product)
{
    show_string(dev, "Product", product);
    show_string(dev, "Manufacturer", product);
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(temp_dir.path());
        let msg = "usb 1-5: Product: USB2.0 HUB";
        let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
        let mapping = matcher
            .match_log_statement(&log_ref, &LogMatchOptions::default())
            .unwrap();
        let src_ref = mapping.src_ref.unwrap();
        // The call that has the text, then the statement that printed it.
        assert_eq!(src_ref.line_no, 8);
        let chain: Vec<(usize, &str, &str, &str)> = src_ref
            .call_chain
            .iter()
            .map(|frame| {
                (
                    frame.line_number,
                    frame.call_name.as_str(),
                    frame.parameter.as_str(),
                    frame.text.as_str(),
                )
            })
            .collect();
        assert_eq!(chain, vec![(3, "syslog", "id", "\"%s: %s\\n\"")]);
        // The value is for the expression in the call, not the parameter.
        let vars: Vec<(&str, &str)> = mapping
            .variables
            .iter()
            .map(|var| (var.expr.as_str(), var.value.as_str()))
            .collect();
        assert_eq!(vars, vec![("product", "USB2.0 HUB")]);
        assert_eq!(mapping.prefix, Some("usb 1-5"));

        // The derived statements are only used for matching.
        assert_eq!(
            matcher
                .statements()
                .filter(|stmt| !stmt.call_chain.is_empty())
                .count(),
            0
        );
        // A message from the statement without the call is still matched to it as is.
        let msg = "Serial: 1234";
        let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
        let src_ref = matcher
            .match_log_statement(&log_ref, &LogMatchOptions::default())
            .and_then(|mapping| mapping.src_ref)
            .unwrap();
        assert_eq!(src_ref.line_no, 3);
        assert!(src_ref.call_chain.is_empty());
    }

    #[test]
    fn test_match_linux_dev_info_prefix() {
        let temp_dir = tempfile::tempdir().unwrap();
        // From drivers/usb/core/hub.c in the Linux kernel.  The functions after the ones that
        // announce a device have the other levels of the `dev_` calls, so they are recognized as
        // logging, like in the whole kernel.
        fs::write(
            temp_dir.path().join("hub.c"),
            r#"static void show_string(struct usb_device *udev, char *id, char *string)
{
	if (!string)
		return;
	dev_info(&udev->dev, "%s: %s\n", id, string);
}

static void announce_device_ids(struct usb_device *udev)
{
	u16 bcdDevice = le16_to_cpu(udev->descriptor.bcdDevice);

	dev_info(&udev->dev,
		"New USB device found: idVendor=%04x, idProduct=%04x, bcdDevice=%x.%02x\n",
		le16_to_cpu(udev->descriptor.idVendor),
		le16_to_cpu(udev->descriptor.idProduct),
		bcdDevice >> 8, bcdDevice & 0xff);
}

static void announce_device_strings(struct usb_device *udev)
{
	dev_info(&udev->dev,
		"New USB device strings: Mfr=%d, Product=%d, SerialNumber=%d\n",
		udev->descriptor.iManufacturer,
		udev->descriptor.iProduct,
		udev->descriptor.iSerialNumber);
	show_string(udev, "Product", udev->product);
	show_string(udev, "Manufacturer", udev->manufacturer);
	show_string(udev, "SerialNumber", udev->serial);
}

static int hub_port_disable(struct usb_hub *hub, int port1, int set_state)
{
	struct usb_port *port_dev = hub->ports[port1 - 1];
	struct usb_device *hdev = hub->hdev;
	int ret = 0;

	if (!hub->error) {
		if (hub_is_superspeed(hub->hdev)) {
			hub_usb3_port_prepare_disable(hub, port_dev);
			ret = hub_set_port_link_state(hub, port_dev->portnum,
						      USB_SS_PORT_LS_U3);
		} else {
			ret = usb_clear_port_feature(hdev, port1,
					USB_PORT_FEAT_ENABLE);
		}
	}
	if (port_dev->child && set_state)
		usb_set_device_state(port_dev->child, USB_STATE_NOTATTACHED);
	if (ret && ret != -ENODEV)
		dev_err(&port_dev->dev, "cannot disable (err = %d)\n", ret);
	return ret;
}

static int usb_set_device_initiated_lpm(struct usb_device *udev,
		enum usb3_link_state state, bool enable)
{
	int ret;
	int feature;

	switch (state) {
	case USB3_LPM_U1:
		feature = USB_DEVICE_U1_ENABLE;
		break;
	case USB3_LPM_U2:
		feature = USB_DEVICE_U2_ENABLE;
		break;
	default:
		dev_warn(&udev->dev, "%s: Can't %s non-U1 or U2 state.\n",
				__func__, str_enable_disable(enable));
		return -EINVAL;
	}

	if (udev->state != USB_STATE_CONFIGURED) {
		dev_dbg(&udev->dev, "%s: Can't %s %s state "
				"for unconfigured device.\n",
				__func__, str_enable_disable(enable),
				usb3_lpm_names[state]);
		return -EINVAL;
	}

	if (enable) {
		/*
		 * Now send the control transfer to enable device-initiated LPM
		 * for either U1 or U2.
		 */
		ret = usb_control_msg(udev, usb_sndctrlpipe(udev, 0),
				USB_REQ_SET_FEATURE,
				USB_RECIP_DEVICE,
				feature,
				0, NULL, 0,
				USB_CTRL_SET_TIMEOUT);
	} else {
		ret = usb_control_msg(udev, usb_sndctrlpipe(udev, 0),
				USB_REQ_CLEAR_FEATURE,
				USB_RECIP_DEVICE,
				feature,
				0, NULL, 0,
				USB_CTRL_SET_TIMEOUT);
	}
	if (ret < 0) {
		dev_warn(&udev->dev, "%s of device-initiated %s failed.\n",
			 str_enable_disable(enable), usb3_lpm_names[state]);
		return -EBUSY;
	}
	return 0;
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(temp_dir.path());
        let matched = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            let mapping = matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .unwrap();
            let vars: Vec<(String, String)> = mapping
                .variables
                .iter()
                .map(|var| (var.expr.clone(), var.value.clone()))
                .collect();
            (
                mapping.src_ref.unwrap().line_no,
                vars,
                mapping.prefix.map(str::to_string),
            )
        };
        let vars = |pairs: &[(&str, &str)]| -> Vec<(String, String)> {
            pairs
                .iter()
                .map(|(expr, value)| (expr.to_string(), value.to_string()))
                .collect()
        };

        // The device name that `dev_info()` adds is not in the format string, so it is the
        // prefix, and the values are taken from the text after it.
        assert_eq!(
            matched(
                "usb 1-5: New USB device found: idVendor=05e3, idProduct=0610, bcdDevice=60.60"
            ),
            (
                13,
                vars(&[
                    ("le16_to_cpu(udev->descriptor.idVendor)", "05e3"),
                    ("le16_to_cpu(udev->descriptor.idProduct)", "0610"),
                    ("bcdDevice >> 8", "60"),
                    ("bcdDevice & 0xff", "60"),
                ]),
                Some("usb 1-5".to_string())
            )
        );
        assert_eq!(
            matched("usb 1-5: New USB device strings: Mfr=0, Product=1, SerialNumber=0"),
            (
                22,
                vars(&[
                    ("udev->descriptor.iManufacturer", "0"),
                    ("udev->descriptor.iProduct", "1"),
                    ("udev->descriptor.iSerialNumber", "0"),
                ]),
                Some("usb 1-5".to_string())
            )
        );
        // Printed by `show_string()`, so it is matched to the call that has the text.
        assert_eq!(
            matched("usb 1-5: Product: USB2.0 Hub"),
            (
                26,
                vars(&[("udev->product", "USB2.0 Hub")]),
                Some("usb 1-5".to_string())
            )
        );
    }

    const PREFIX_SRC: &str = r#"fn work(id: u32, count: u32, path: &str) {
    info!("Started worker {} with {} tasks", id, count);
    info!("open file: {}", path);
}
"#;

    /// The line number, variables, and prefix of the statement matched to a message.
    type PrefixedMatch = (usize, Vec<(String, String)>, Option<String>);

    /// Match the message and return the line number, variables, and prefix of the statement.
    fn match_with_prefix(matcher: &LogMatcher, msg: &str) -> Option<PrefixedMatch> {
        let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
        let mapping = matcher.match_log_statement(&log_ref, &LogMatchOptions::default())?;
        let vars = mapping
            .variables
            .iter()
            .map(|var| (var.expr.clone(), var.value.clone()))
            .collect();
        Some((
            mapping.src_ref?.line_no,
            vars,
            mapping.prefix.map(str::to_string),
        ))
    }

    #[test]
    fn test_match_prefix_separators() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(temp_dir.path().join("work.rs"), PREFIX_SRC).unwrap();
        let matcher = matcher_for(temp_dir.path());
        let started = |prefix: &str| {
            Some((
                2,
                vec![
                    ("id".to_string(), "3".to_string()),
                    ("count".to_string(), "10".to_string()),
                ],
                Some(prefix.to_string()),
            ))
        };

        // The prefix can end with any punctuation, so the separator does not have to be known.
        // A closing bracket is part of the prefix, but a separator like `|` is not.
        for (msg, prefix) in [
            ("[main] Started worker 3 with 10 tasks", "[main]"),
            ("<12>Started worker 3 with 10 tasks", "<12>"),
            ("svc | Started worker 3 with 10 tasks", "svc"),
            ("host1\tStarted worker 3 with 10 tasks", "host1"),
        ] {
            assert_eq!(match_with_prefix(&matcher, msg), started(prefix), "{msg}");
        }
        // A statement whose text starts after a space between words is a fragment of another
        // message, not the text after a prefix.
        assert_eq!(
            match_with_prefix(&matcher, "Failed to open file: /tmp/x"),
            None
        );
    }

    #[test]
    fn test_match_long_message_partly_explained() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(temp_dir.path().join("work.rs"), PREFIX_SRC).unwrap();
        let matcher = matcher_for(temp_dir.path());
        // Only the head of a long message is read, but a statement that explains the head and
        // not the rest is not used, since its values would be cut off.
        let lines = "more\n".repeat(400);
        for msg in [
            format!("Started worker 3 with 10 tasks\n{lines}"),
            format!("[main] Started worker 3 with 10 tasks\n{lines}"),
        ] {
            assert_eq!(match_with_prefix(&matcher, &msg), None);
        }
    }

    #[test]
    fn test_match_learned_prefix() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(temp_dir.path().join("work.rs"), PREFIX_SRC).unwrap();
        let matcher = matcher_for(temp_dir.path());
        let coll = matcher.roots.values().next().unwrap();
        let learned = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            coll.learned_match(&log_ref, false)
                .map(|(src_ref, start, _)| (src_ref.line_no, start))
        };
        let separators = || -> Vec<String> {
            coll.learned_prefixes
                .read()
                .unwrap()
                .values()
                .flatten()
                .map(|lp| lp.separator.clone())
                .collect()
        };

        assert_eq!(learned("[pool-2] Started worker 4 with 1 tasks"), None);
        // Found the slow way, and the separator after the prefix is remembered.
        assert_eq!(
            match_with_prefix(&matcher, "[main] Started worker 3 with 10 tasks"),
            Some((
                2,
                vec![
                    ("id".to_string(), "3".to_string()),
                    ("count".to_string(), "10".to_string()),
                ],
                Some("[main]".to_string())
            ))
        );
        assert_eq!(separators(), vec![" ".to_string()]);
        // Another message from the statement, with a different prefix, is found with it, and
        // the result is the same as the slow way.
        assert_eq!(
            learned("[pool-2] Started worker 4 with 1 tasks"),
            Some((2, 9))
        );
        assert_eq!(
            match_with_prefix(&matcher, "[pool-2] Started worker 4 with 1 tasks"),
            Some((
                2,
                vec![
                    ("id".to_string(), "4".to_string()),
                    ("count".to_string(), "1".to_string()),
                ],
                Some("[pool-2]".to_string())
            ))
        );
        // Each place after the separator is tried, not just the first one that the statement
        // matches after.
        assert_eq!(
            learned("dev Started worker [x] Started worker 4 with 1 tasks"),
            Some((2, 23))
        );
        // The prefix still has to end like one.
        assert_eq!(learned("just Started worker 4 with 1 tasks"), None);
        // The statement has to explain enough of the rest of the message.
        assert_eq!(
            learned(
                "[main] Started worker 3 with 10 tasks, and then a whole lot more text after it"
            ),
            None
        );
        assert_eq!(separators(), vec![" ".to_string()]);

        // A change to the statements forgets them, since the statement IDs can change.
        let mut matcher = matcher;
        matcher.rebuild_prefilters();
        let coll = matcher.roots.values().next().unwrap();
        assert!(coll.learned_prefixes.read().unwrap().is_empty());
    }

    #[test]
    fn test_match_through_format_wrappers() {
        let temp_dir = tempfile::tempdir().unwrap();
        let include = temp_dir.path().join("include");
        let drivers = temp_dir.path().join("drivers");
        fs::create_dir_all(&include).unwrap();
        fs::create_dir_all(&drivers).unwrap();
        // The header, which does not parse, has the default `dev_fmt` and a macro that passes
        // the message to a function that prints it with `%pV`.
        fs::write(
            include.join("acpi.h"),
            r#"#ifndef dev_fmt
#define dev_fmt(fmt) fmt
#endif
__printf(3, 4) void acpi_handle_printk(const char *level, void *handle, const char *fmt, ...);
#define acpi_handle_info(handle, fmt, ...) \
	acpi_handle_printk(KERN_INFO, handle, dev_fmt(fmt), ##__VA_ARGS__)
"#,
        )
        .unwrap();
        fs::write(
            drivers.join("utils.c"),
            r#"void acpi_handle_printk(const char *level, void *handle, const char *fmt, ...)
{
	struct va_format vaf;
	const char *path = acpi_handle_path(handle);
	printk("%sACPI: %s: %pV", level, path, &vaf);
}
"#,
        )
        .unwrap();
        // The file with the call defines its own `dev_fmt` as another name for `pr_fmt`.
        fs::write(
            drivers.join("power.c"),
            r#"#define pr_fmt(fmt) "PM: " fmt
#define dev_fmt pr_fmt

static int add_power_resource(void *handle, int count)
{
	acpi_handle_info(handle, "New power resource %d\n", count);
	return 0;
}
"#,
        )
        .unwrap();
        let tracker = ProgressTracker::new();
        let mut matcher = LogMatcher::new();
        matcher.add_root(&include).unwrap();
        matcher.add_root(&drivers).unwrap();
        assert!(matcher.discover_sources(&tracker).is_empty());
        matcher.extract_log_statements(&tracker);

        let msg = "ACPI: \\_SB_.PWRS: PM: New power resource 2";
        let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
        let mapping = matcher
            .match_log_statement(
                &log_ref,
                &LogMatchOptions {
                    fallback: true,
                    ..LogMatchOptions::default()
                },
            )
            .unwrap();
        let src_ref = mapping.src_ref.unwrap();
        // The call where the message was written, which explains all of the line.
        assert!(src_ref.source_path().ends_with("power.c"));
        assert_eq!(src_ref.line_no, 6);
        assert_eq!(mapping.prefix, None);
        let chain: Vec<(&str, usize, &str)> = src_ref
            .call_chain
            .iter()
            .map(|frame| {
                let file = Path::new(&frame.source_path).file_name().unwrap();
                (
                    file.to_str().unwrap(),
                    frame.line_number,
                    frame.name.as_str(),
                )
            })
            .collect();
        assert_eq!(
            chain,
            vec![
                ("acpi.h", 5, "acpi_handle_info"),
                ("power.c", 1, "pr_fmt"),
                (
                    "utils.c",
                    5,
                    "acpi_handle_printk(const char *level, void *handle, const char *fmt, ...)"
                ),
            ]
        );
        // The level is taken out of the message by printk(), so it is not a value.
        let vars: Vec<(&str, &str)> = mapping
            .variables
            .iter()
            .map(|var| (var.expr.as_str(), var.value.as_str()))
            .collect();
        assert_eq!(vars, vec![("path", "\\_SB_.PWRS"), ("count", "2")]);
    }

    #[test]
    fn test_match_through_macro_wrappers() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(
            temp_dir.path().join("printk.h"),
            r#"#define pr_info(fmt, ...) printk(KERN_INFO pr_fmt(fmt), ##__VA_ARGS__)
"#,
        )
        .unwrap();
        fs::write(
            temp_dir.path().join("a.c"),
            r#"#define pr_fmt(fmt) "alpha: " fmt
#define DBG(fmt) printk(KERN_DEBUG "drv: " fmt)
#define B(fmt) printk(xlate(fmt))
#define A(fmt, ...) B("bee: " fmt)

void start(void)
{
    pr_info("started up\n");
    DBG("probe complete\n");
    A("hello there\n");
}
"#,
        )
        .unwrap();
        // This file does not define `pr_fmt`, and it cannot see the one in `a.c`.
        fs::write(
            temp_dir.path().join("b.c"),
            r#"void ready(void)
{
    pr_info("ready to go\n");
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(temp_dir.path());
        let matched = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            let mapping = matcher
                .match_log_statement(
                    &log_ref,
                    &LogMatchOptions {
                        fallback: true,
                        ..LogMatchOptions::default()
                    },
                )
                .unwrap();
            let src_ref = mapping.src_ref.unwrap();
            let file = Path::new(src_ref.source_path()).file_name().unwrap();
            let chain: Vec<String> = src_ref
                .call_chain
                .iter()
                .map(|frame| frame.name.clone())
                .collect();
            (
                file.to_str().unwrap().to_string(),
                src_ref.line_no,
                chain,
                mapping.prefix.map(str::to_string),
            )
        };

        assert_eq!(
            matched("alpha: started up"),
            (
                "a.c".to_string(),
                8,
                vec!["pr_info".to_string(), "pr_fmt".to_string()],
                None
            )
        );
        // A macro with one parameter that is a single call is followed.
        assert_eq!(
            matched("drv: probe complete"),
            ("a.c".to_string(), 9, vec!["DBG".to_string()], None)
        );
        // `B()` changes the message in a way that is not known, so the text from `A()` is not
        // added either, and the text in front is not from any statement.
        assert_eq!(
            matched("bee: hello there"),
            ("a.c".to_string(), 10, vec![], Some("bee".to_string()))
        );
        assert_eq!(
            matched("alpha: ready to go"),
            ("b.c".to_string(), 3, vec![], Some("alpha".to_string()))
        );
    }

    #[test]
    fn test_best_match_across_roots() {
        let temp_dir = tempfile::tempdir().unwrap();
        let generic = temp_dir.path().join("generic");
        let specific = temp_dir.path().join("specific");
        fs::create_dir_all(&generic).unwrap();
        fs::create_dir_all(&specific).unwrap();
        fs::write(
            generic.join("dock.c"),
            "void dock(const char *msg, int irq) {\n    pr_info(\"%s with IRQ %d\\n\", msg, irq);\n}\n",
        )
        .unwrap();
        fs::write(
            specific.join("aer.c"),
            "void probe(int irq) {\n    pr_info(\"enabled with IRQ %d\\n\", irq);\n}\n",
        )
        .unwrap();
        let tracker = ProgressTracker::new();
        // The order the roots are visited in is not fixed, so try a few matchers, in both
        // orders, to check that the generic statement in one root never wins.
        for attempt in 0..8 {
            let mut matcher = LogMatcher::new();
            if attempt % 2 == 0 {
                matcher.add_root(&generic).unwrap();
                matcher.add_root(&specific).unwrap();
            } else {
                matcher.add_root(&specific).unwrap();
                matcher.add_root(&generic).unwrap();
            }
            assert!(matcher.discover_sources(&tracker).is_empty());
            matcher.extract_log_statements(&tracker);
            let msg = "enabled with IRQ 122";
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            let src_ref = matcher
                .match_log_statement(
                    &log_ref,
                    &LogMatchOptions {
                        fallback: true,
                        ..LogMatchOptions::default()
                    },
                )
                .and_then(|mapping| mapping.src_ref)
                .unwrap();
            assert!(src_ref.source_path().ends_with("aer.c"));

            // The generic statement is still used when it is the only one that matches.
            let msg = "requested with IRQ 5";
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            let src_ref = matcher
                .match_log_statement(
                    &log_ref,
                    &LogMatchOptions {
                        fallback: true,
                        ..LogMatchOptions::default()
                    },
                )
                .and_then(|mapping| mapping.src_ref)
                .unwrap();
            assert!(src_ref.source_path().ends_with("dock.c"));
        }
    }

    #[test]
    fn test_message_constants_from_cache() {
        let temp_dir = tempfile::tempdir().unwrap();
        let root = temp_dir.path().join("src");
        write_message_tree(&root);
        let cache = Cache {
            location: temp_dir.path().join("cache"),
        };
        let tracker = ProgressTracker::new();
        matcher_for(&root).cache_to(&cache, &tracker).unwrap();

        let mut matcher = LogMatcher::new();
        matcher.add_root(&root).unwrap();
        assert!(matcher.load_from_cache(&cache, &tracker).is_empty());
        let _ = matcher.discover_sources(&tracker);
        let summary = matcher.extract_log_statements(&tracker);
        assert_eq!(summary.changes(), 0);
        assert_eq!(matcher.statements().count(), 3);
        assert_eq!(
            match_message(&matcher, "Loaded 12 keys"),
            Some((10, vars(&[("port - 1", "12")])))
        );
    }

    const CPP_SOURCE: &str = r#"
    #include <stdio.h>

    int main(int argc, char* argv[]) {
        printf("Hello, %s!", argv[1]);
    }
    "#;

    const CPP_REJECTED_LITERAL_SOURCE: &str = r#"
    void scan(int line) {
        log_debug("scanned %d", line);
    }

    void result(sqlite3_context* ctx) {
        sqlite3_result_text(
            ctx, "", 0, SQLITE_STATIC);
    }
    "#;

    #[test]
    fn test_rejected_literal_args_are_dropped() {
        let code =
            CodeSource::from_string(&PathBuf::from("in-mem.cc"), CPP_REJECTED_LITERAL_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 1);
        assert_eq!(src_refs[0].line_no, 3);
        assert_eq!(src_refs[0].end_line_no, 3);
        assert_eq!(src_refs[0].vars, vec!["line".to_string()]);
    }

    const CPP_NESTED_SOURCE: &str = r#"
    TEST_CASE("not a log statement") {
        CHECK(true);
    }

    _Pragma("GCC diagnostic ignored \"-Wunused\"")

    bool open_request(int line, int kind) {
    #ifdef HAVE_RUST_DEPS
        log_info("sending line %d", line);
        return true;
    #else
        return false;
    #endif
        switch (kind) {
            case 1:
                log_debug("kind one %d", kind);
                break;
        }
        if (line > 0)
            log_warning("positive line %d", line);
    }
    "#;

    const CPP_CONCAT_SOURCE: &str = r#"
    void open_href(const char* path, unsigned long line, uint64_t size) {
        log_info(
            "Opening href with external editor: "
            "%s:%lu:%lu",
            path,
            line,
            0);
        log_debug("read %" PRIu64 " bytes", size);
        log_debug("unknown " SOME_MACRO " text", size);
    }
    "#;

    #[test]
    fn test_cpp_concatenated_string() {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), CPP_CONCAT_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 3);
        assert_eq!(
            src_refs[0].pattern().as_str(),
            "(?s)^Opening href with external editor: (.*):(.*):(.*)$"
        );
        assert_eq!((src_refs[0].line_no, src_refs[0].end_line_no), (4, 8));
        assert_eq!(src_refs[0].vars, vec!["path", "line", "0"]);
        assert_eq!(src_refs[1].pattern().as_str(), "(?s)^read (.*) bytes$");
        assert_eq!(src_refs[1].vars, vec!["size"]);
        // A macro whose value is unknown matches anything.
        assert_eq!(src_refs[2].pattern().as_str(), "(?s)^unknown (.*) text$");
        assert_eq!(src_refs[2].arg_exprs(), vec!["SOME_MACRO"]);
    }

    #[test]
    fn test_join_ended_by_newline_only() {
        let source = r#"
static void show_features(int n, const char **names, int extra)
{
    int i;

    pr_info("features:");
    for (i = 0; i < n; i++)
        pr_cont(" name=%s", names[i]);
    pr_cont("\n");
    if (extra)
        pr_cont("extra flag set\n");
    printk(KERN_INFO "regs:");
    printk(KERN_CONT "\n");
    printk(KERN_CONT "after regs\n");
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.c"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        // The continuations that only end the line are not matched to messages.
        assert!(sif
            .log_statements
            .iter()
            .all(|stmt| !stmt.quality.is_zero()));
        assert_eq!(
            sif.bare_continuations
                .iter()
                .map(|stmt| stmt.line_no)
                .collect::<Vec<_>>(),
            vec![9, 13]
        );
        let joined = join_continued_lines(&sif);
        let found: Vec<(usize, Vec<usize>, &str)> = joined
            .iter()
            .map(|stmt| {
                (
                    stmt.line_no,
                    stmt.continuations.iter().map(|c| c.line_number).collect(),
                    stmt.pattern().as_str(),
                )
            })
            .sorted()
            .collect();
        // The line ends at the `pr_cont("\n")`, so the continuations after it are not joined.
        assert_eq!(
            found,
            vec![
                (6, vec![8, 9], r"(?s)^features: name=(.*?)\s*$"),
                (6, vec![9], r"(?s)^features:\s*$"),
                (12, vec![13], r"(?s)^(.*)regs:\s*$"),
            ]
        );
    }

    #[test]
    fn test_bare_continuation_with_choices() {
        let source = r#"
void show(int on)
{
    pr_info("state:");
    pr_cont(" %s\n", on ? "on" : "off");
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.c"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        // The choices do not make the continuation a statement of its own.
        let lines = |stmts: &[Statement]| stmts.iter().map(|s| s.line_no).collect::<Vec<_>>();
        assert_eq!(lines(&sif.log_statements), vec![4]);
        assert_eq!(lines(&sif.bare_continuations), vec![5]);
        let joined = join_continued_lines(&sif);
        let patterns: Vec<&str> = joined.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(patterns, vec![r"(?s)^state: (off|on)\s*$"]);
    }

    #[test]
    fn test_join_bare_continuation_in_loop() {
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(
            temp_dir.path().join("cpu.c"),
            r#"static void show_cpu_features(int n, const char **names)
{
    int i;

    pr_info("CPU features detected:");
    for (i = 0; i < n; i++)
        pr_cont(" %s", names[i]);
    pr_cont("\n");
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(temp_dir.path());
        let matched = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            let mapping = matcher
                .match_log_statement(
                    &log_ref,
                    &LogMatchOptions {
                        fallback: true,
                        ..LogMatchOptions::default()
                    },
                )
                .unwrap();
            let src_ref = mapping.src_ref.unwrap();
            let conts: Vec<usize> = src_ref
                .continuations
                .iter()
                .map(|cont| cont.line_number)
                .collect();
            let vars: Vec<(String, String)> = mapping
                .variables
                .into_iter()
                .map(|var| (var.expr, var.value))
                .collect();
            (src_ref.line_no, conts, vars)
        };
        // The loop printed its continuation more than once, which is not known, so all of the
        // values are in the one placeholder.
        assert_eq!(
            matched("CPU features detected: fpu vme de pse"),
            (
                5,
                vec![7, 8],
                vec![("names[i]".to_string(), "fpu vme de pse".to_string())]
            )
        );
        // The loop printed nothing, which the start alone matches as well as the joined line.
        let (line_no, _, vars) = matched("CPU features detected:");
        assert_eq!((line_no, vars), (5, vec![]));
        // A continuation without literal text is not matched on its own.
        assert!(matcher
            .statements()
            .all(|stmt| !stmt.is_continuation() || !stmt.quality.is_zero()));
    }

    #[test]
    fn test_join_continued_lines() {
        let source = r#"
static int do_bind_con_driver(int first, int last, int deflt, int j)
{
    pr_info("Console: switching ");
    if (!deflt)
        pr_cont("consoles %d-%d ", first + 1, last + 1);
    if (j >= 0) {
        pr_cont("to %s %dx%d\n", color ? "colour" : "mono", cols, rows);
    } else {
        pr_cont("to %s\n", desc);
    }
    pr_cont("ends the line\n");
}

void dump(int a, int b)
{
    printk(KERN_INFO "regs:");
    printk(KERN_CONT " a=%d", a);
    printk(KERN_CONT " b=%d\n", b);
    printk(KERN_CONT "after the end\n");
    pr_info("complete\n");
    pr_cont("not after a start\n");
    pr_warn("interrupted ");
    pr_err("by another print\n");
    pr_cont("so not continued\n");
}

void other(void)
{
    pr_cont("in another function\n");
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.c"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let joined = join_continued_lines(&sif);
        let found: Vec<(usize, Vec<usize>, &str)> = joined
            .iter()
            .map(|stmt| {
                (
                    stmt.line_no,
                    stmt.continuations.iter().map(|c| c.line_number).collect(),
                    stmt.pattern().as_str(),
                )
            })
            .sorted()
            .collect();
        assert_eq!(
            found,
            vec![
                (
                    4,
                    vec![6, 8],
                    r"(?s)^Console: switching\s*consoles (.*)-(.*)\s*to (colour|mono) (.*)x(.*?)\s*$"
                ),
                (
                    4,
                    vec![6, 10],
                    r"(?s)^Console: switching\s*consoles (.*)-(.*)\s*to (.*?)\s*$"
                ),
                (
                    4,
                    vec![6, 12],
                    r"(?s)^Console: switching\s*consoles (.*)-(.*)\s*ends the line\s*$"
                ),
                (
                    4,
                    vec![8],
                    r"(?s)^Console: switching\s*to (colour|mono) (.*)x(.*?)\s*$"
                ),
                (4, vec![10], r"(?s)^Console: switching\s*to (.*?)\s*$"),
                (4, vec![12], r"(?s)^Console: switching\s*ends the line\s*$"),
                // `KERN_CONT` prints nothing, so it is left out.
                (17, vec![18, 19], r"(?s)^(.*)regs: a=(.*) b=(.*?)\s*$"),
            ]
        );
        let line = "Console: switching consoles 1-63 to colour 128x48";
        let stmt = joined
            .iter()
            .find(|stmt| stmt.pattern().is_match(line))
            .unwrap();
        assert_eq!(stmt.end_line_no, 8);
        assert_eq!(
            stmt.text,
            r#""Console: switching " "consoles %d-%d " "to %s %dx%d\n""#
        );
        assert_eq!(stmt.level, LogLevel::Info);
        let vars: Vec<(String, String)> = extract_variables_from(line, stmt)
            .into_iter()
            .map(|pair| (pair.expr, pair.value))
            .collect();
        assert_eq!(
            vars,
            vec![
                ("first + 1".to_string(), "1".to_string()),
                ("last + 1".to_string(), "63".to_string()),
                (
                    r#"color ? "colour" : "mono""#.to_string(),
                    "colour".to_string()
                ),
                ("cols".to_string(), "128".to_string()),
                ("rows".to_string(), "48".to_string()),
            ]
        );
    }

    #[test]
    fn test_conditional_string_args() {
        // A conditional whose results are string literals can only print one of them, so a
        // line with something else there did not come from the statement, even though `(.*)`
        // would match it.
        let source = r#"
void con_init(struct vc_data *vc, const char *display_desc) {
    pr_info("Console: %s %s %dx%d\n",
            vc->vc_can_do_color ? "colour" : "mono",
            display_desc, vc->vc_cols, vc->vc_rows);
    pr_info("mode %s\n", fast ? "fast" : (slow ? "slow\t(really)" : "normal"));
    pr_info("padded %-6s|\n", on ? "on" : "off");
    pr_info("either %s\n", on ? "on" : name);
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.c"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(
            patterns,
            vec![
                r"(?s)^Console: (colour|mono) (.*) (.*)x(.*?)\s*$",
                r"(?s)^mode (fast|normal|slow\t\(really\))\s*$",
                // The width pads the value, so it is not one of the choices.
                r"(?s)^padded (.*)\|\s*$",
                // `name` can be anything.
                r"(?s)^either (.*?)\s*$",
            ]
        );
        // The literal text of the shortest choice counts toward the quality.
        assert_eq!(
            src_refs[0].quality,
            Quality::of_text("Console:") + Quality::of_text("mono") + Quality::of_text("x")
        );

        let stmt = &src_refs[0];
        assert!(!stmt
            .pattern()
            .is_match("Console: switching to colour frame buffer device 128x48"));
        let vars: Vec<(String, String)> =
            extract_variables_from("Console: colour dummy device 80x25", stmt)
                .into_iter()
                .map(|pair| (pair.expr, pair.value))
                .collect();
        assert_eq!(
            vars,
            vec![
                (
                    r#"vc->vc_can_do_color ? "colour" : "mono""#.to_string(),
                    "colour".to_string()
                ),
                ("display_desc".to_string(), "dummy device".to_string()),
                ("vc->vc_cols".to_string(), "80".to_string()),
                ("vc->vc_rows".to_string(), "25".to_string()),
            ]
        );

        // The choices are kept in the cache.
        let encoded = bincode::serde::encode_to_vec(stmt, bincode::config::standard()).unwrap();
        let (decoded, _): (Statement, usize) =
            bincode::serde::decode_from_slice(&encoded, bincode::config::standard()).unwrap();
        assert_eq!(decoded.pattern().as_str(), stmt.pattern().as_str());
    }

    #[test]
    fn test_c_family_macro_calls_in_concatenation() {
        // Macros that wrap a string-literal, like lnav's ANSI_BOLD("..."), cannot be parsed
        // when they are concatenated with other string-literals.
        let source = r#"
#include "ansi.h"
TEST_CASE("first")
TEST_CASE("second")

void report(char *buf, int count, long secs, long msecs) {
    snprintf(buf, 128,
             ANSI_BOLD("%'d") " row%s matched in " ANSI_BOLD(
                 "%ld.%03ld") " seconds",
             count, count == 1 ? "" : "s", secs, msecs);
    log_info("Press " ANSI_BOLD("TAB") " to focus " ANSI_UNDERLINE("%s"), name);
    log_info(ANSI_BOLD_START "%d" ANSI_NORM " files", count);
    log_info("not rewritten " TWO_ARGS("a", "b"));
    log_info(_("translated %d"), count);
    // log_info("commented " ANSI_BOLD("%d"));
    log_info("See " ANSI_BOLD("https://example.com/" "docs.html") " for more");
    log_info("trailing " ANSI_BOLD("abc/" "def"));
    log_info("got %" G_GINT64_FORMAT " items, %-4" G_GSIZE_FORMAT " bytes", n, size);
}
"#;
        for name in ["in-mem.cc", "in-mem.c"] {
            let code = CodeSource::from_string(&PathBuf::from(name), source);
            let sif = extract_logging(&[code], &ProgressTracker::new())
                .pop()
                .unwrap();
            let src_refs = &sif.log_statements;
            let found: Vec<(&str, usize, Vec<&str>)> = src_refs
                .iter()
                .map(|s| (s.pattern().as_str(), s.line_no, s.arg_exprs()))
                .collect();
            assert_eq!(
                found,
                vec![
                    (
                        r"(?s)^(.*)(.*)(.*) row(|s) matched in (.*)(.*)\.(.*)(.*) seconds$",
                        8,
                        vec![
                            "ANSI_BOLD",
                            "count",
                            "ANSI_BOLD",
                            r#"count == 1 ? "" : "s""#,
                            "ANSI_BOLD",
                            "secs",
                            "msecs",
                            "ANSI_BOLD"
                        ]
                    ),
                    (
                        "(?s)^Press (.*)TAB(.*) to focus (.*)(.*)(.*)$",
                        11,
                        vec![
                            "ANSI_BOLD",
                            "ANSI_BOLD",
                            "ANSI_UNDERLINE",
                            "name",
                            "ANSI_UNDERLINE"
                        ]
                    ),
                    (
                        "(?s)^(.*)(.*)(.*) files$",
                        12,
                        vec!["ANSI_BOLD_START", "count", "ANSI_NORM"]
                    ),
                    ("(?s)^translated (.*)$", 14, vec!["count"]),
                    (
                        r"(?s)^See (.*)https://example\.com/docs\.html(.*) for more$",
                        16,
                        vec!["ANSI_BOLD", "ANSI_BOLD"]
                    ),
                    (
                        "(?s)^trailing (.*)abc/def(.*)$",
                        17,
                        vec!["ANSI_BOLD", "ANSI_BOLD"]
                    ),
                    ("(?s)^got (.*) items, (.*) bytes$", 18, vec!["n", "size"]),
                ],
                "{name}"
            );
            assert_eq!(
                src_refs[1].text, r#""Press " ANSI_BOLD("TAB") " to focus " ANSI_UNDERLINE("%s")"#,
                "{name}"
            );
            assert_eq!(
                src_refs[4].text,
                r#""See " ANSI_BOLD("https://example.com/" "docs.html") " for more""#,
                "{name}"
            );
            assert_eq!(
                src_refs[5].text, r#""trailing " ANSI_BOLD("abc/" "def")"#,
                "{name}"
            );
            let line = "1,234 rows matched in 0.010 seconds";
            let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
            assert!(src_refs[0].pattern().is_match(log_ref.body()), "{name}");
        }
    }

    #[test]
    fn test_cpp_raw_string() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.cc"),
            r#"
void load() {
    LOG(Log::DEBUG, R"( [PluginSystem] Plugin {} loaded, path: "{}")", name, path);
    spdlog::error(R"delim(bad\d "{}")delim", input);
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(
            patterns,
            vec![
                r#"(?s)^ \[PluginSystem\] Plugin (.*) loaded, path: "(.*)"$"#,
                r#"(?s)^bad\\d "(.*)"$"#,
            ]
        );
        assert_eq!(src_refs[0].level, LogLevel::Debug);
        assert_eq!(src_refs[0].vars, vec!["name", "path"]);
        assert_eq!(src_refs[1].level, LogLevel::Error);
    }

    #[test]
    fn test_java_builder_chain() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.java"),
            r#"
class Options {
    void check(String value) {
        String msg = new StringBuilder()
            .append(value)
            .append(" is not a valid value for option ")
            .toString();
        logger.info("checked " + value);
        sql.append(" OR ( ").append(clause).append(" ) ");
        sql.append(" ORDER BY 1");
        parser.error("not a log message");
    }
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let found: Vec<(usize, &str, MessageCategory)> = sif
            .log_statements
            .iter()
            .map(|s| (s.line_no, s.text.as_str(), s.category))
            .collect();
        assert_eq!(
            found,
            vec![
                (
                    6,
                    "\" is not a valid value for option \"",
                    MessageCategory::Other
                ),
                (8, "\"checked \" + value", MessageCategory::Log),
                (9, "\" OR ( \"", MessageCategory::Other),
                (9, "\" ) \"", MessageCategory::Other),
                (10, "\" ORDER BY 1\"", MessageCategory::Other),
            ]
        );
    }

    #[test]
    fn test_cpp_builder_chain() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.cc"),
            r#"
void check(ypc_t* ypc, const std::string& value) {
    ypc->report_error(user_message::error(
        attr_line_t()
            .append_quoted(value)
            .append(" is not a valid value for option ")
            .append_quoted(ypc->get_full_path())));
    auto um = attr_line_t().append("unable to open file");
    attr_line_t().append("only once");
    sql.append(" OR ( ").append(clause).append(" ) ");
}
static const handlers h = {
    yajlpp::property_handler("pattern")
        .with_description("A regular expression that matches a frame"),
};
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let found: Vec<(usize, &str, Option<&str>)> = sif
            .log_statements
            .iter()
            .map(|s| (s.line_no, s.text.as_str(), s.call_name.as_deref()))
            .collect();
        assert_eq!(
            found,
            vec![
                (
                    6,
                    "\" is not a valid value for option \"",
                    Some("attr_line_t().append_quoted().append")
                ),
                (8, "\"unable to open file\"", Some("attr_line_t().append")),
                (9, "\"only once\"", Some("attr_line_t().append")),
                (10, "\" OR ( \"", Some("sql.append")),
                (10, "\" ) \"", Some("sql.append().append().append")),
                // A method of a builder that initializes a static, but not the call at the
                // start of the chain, which could be a macro.
                (
                    14,
                    "\"A regular expression that matches a frame\"",
                    Some("yajlpp::property_handler().with_description")
                ),
                // The text of the chains of appends, see `SourceQuery::append_chains()`.
                (
                    4,
                    "attr_line_t()\n            .append_quoted(value)\n            \
                     .append(\" is not a valid value for option \")\n            \
                     .append_quoted(ypc->get_full_path())",
                    Some("attr_line_t().append_quoted().append().append_quoted")
                ),
                (
                    10,
                    "sql.append(\" OR ( \").append(clause).append(\" ) \")",
                    Some("sql.append().append().append")
                ),
            ]
        );
    }

    #[test]
    fn test_cpp_user_defined_literals() {
        // The string of a user-defined literal, like lnav's `"error"_error`, is the text, but
        // a number with a suffix is not a message.
        let patterns = cpp_patterns(
            r#"
void f() {
    al.append(" ").append("✘ Filter-out"_error).append("  ");
    log_info("hello %d"_fmt, count);
    auto delay = 10_ms;
}
"#,
        );
        assert_eq!(
            patterns,
            vec![
                r"(?s)^✘ Filter-out$",
                r"(?s)^hello (.*)$",
                // The whole chain, whose whitespace at the end is optional.
                r"(?s)^ ✘ Filter-out\s*$",
            ]
        );
    }

    #[test]
    fn test_cpp_append_chains() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.cc"),
            r#"
attr_line_t to_attr_line(level lvl, bool x) {
    switch (lvl) {
        case level::error:
            retval.append("  ").append("error"_error).append(": ");
            retval.al_attrs.emplace_back(line_range{0, 1}, ICON);
            break;
        case level::ok:
            retval.append("  ");
            break;
    }
    retval.append(this->um_message).append("\n");
    if (x) {
        retval.append("maybe");
    }
    retval.append("50% {done}");
    for (auto& i : items) {
        retval.append(i).append(" item");
    }
    retval.append("never");
    return retval;
}
void report() {
    report_error(user_message::error(attr_line_t().append_quoted(n).append(" is bad")));
    auto um = attr_line_t("unable to open: ").append(fn);
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        // Only the text of whole chains, not the string-literals in them.
        let found: Vec<(usize, &str, Vec<usize>, MessageCategory)> = sif
            .log_statements
            .iter()
            .filter(|stmt| !stmt.text.starts_with('"'))
            .map(|stmt| {
                (
                    stmt.line_no,
                    stmt.pattern().as_str(),
                    stmt.continuations.iter().map(|c| c.line_number).collect(),
                    stmt.category,
                )
            })
            .collect();
        assert_eq!(
            found,
            vec![
                // The appends after the `switch` always run, whichever case was taken, and the
                // field of the receiver that is changed does not change its text.  The other
                // case only adds whitespace.
                (
                    5,
                    r"(?s)^  error: (.*?)\s*$",
                    vec![12],
                    MessageCategory::Other
                ),
                // The appends after the `if` always run, until the loop, which might not.  The
                // text is not a format string.
                (
                    14,
                    r"(?s)^maybe50% \{done\}$",
                    vec![16],
                    MessageCategory::Other
                ),
                (18, r"(?s)^(.*) item$", vec![], MessageCategory::Other),
                // The text is made into an error, which is shown somewhere else.
                (24, r"(?s)^(.*) is bad$", vec![], MessageCategory::Error),
                // The text the builder starts with.
                (
                    25,
                    r"(?s)^unable to open: (.*)$",
                    vec![],
                    MessageCategory::Other
                ),
            ]
        );
    }

    #[test]
    fn test_find_glyph() {
        let source = r#"
static block_elem_t wchar_for_icon(ui_icon_t ic) {
    switch (ic) {
        case ui_icon_t::ok:
            return {U'✔', role_t::VCR_OK};
        case ui_icon_t::error:
            return {U'✘', role_t::VCR_ERROR};
    }
}
attr_line_t user_message::to_attr_line() const {
    attr_line_t retval;
    retval.append("  ").append("error"_error).append(": ");
    retval.al_attrs.emplace_back(line_range{0, 1}, VC_ICON.value(ui_icon_t::error));
    retval.append(this->um_message).append("\n");
    return retval;
}
void f() {
    um_error(attr_line_t().append_quoted(name).append(" is already a named search"));
    tl.append("✘"_error);
    char letter = 'x';
    char32_t accent = U'é';
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let found =
            find_message_sources(sif.statements(), "✘ error: “dup” is already a named search");
        let lines: Vec<(&str, Vec<usize>)> = found
            .iter()
            .map(|source| {
                (
                    source.text.as_str(),
                    source.candidates.iter().map(|stmt| stmt.line_no).collect(),
                )
            })
            .collect();
        // The icon is drawn in place of the first space of the prefix, so it is not part of any
        // text, but the places it could come from are found.  A letter, even one that is not
        // ASCII, is not a glyph.
        assert_eq!(
            lines,
            vec![
                ("✘", vec![7, 19]),
                // The chain matches all of it too, but the prefix is better, since the chain
                // explains the rest.
                ("error: “dup” is already a named search", vec![12, 18]),
            ]
        );
        let causes: Vec<Vec<usize>> = found[1]
            .causes
            .iter()
            .map(|cause| cause.candidates.iter().map(|stmt| stmt.line_no).collect())
            .collect();
        assert_eq!(causes, vec![vec![18]]);
    }

    #[test]
    fn test_find_variables() {
        let source = r#"
attr_line_t user_message::to_attr_line() const {
    attr_line_t retval;
    retval.append("  ").append("error"_error).append(": ");
    retval.append(this->um_message).append("\n");
    return retval;
}
void f() {
    um_error(attr_line_t().append_quoted(name).append(" is already a named search"));
    status.set_value("%'d messages ", count);
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let variables = |sources: &[MessageSource]| -> Vec<Vec<(String, String)>> {
            sources
                .iter()
                .map(|source| {
                    source
                        .variables
                        .iter()
                        .map(|pair| (pair.expr.clone(), pair.value.clone()))
                        .collect()
                })
                .collect()
        };
        let pair = |expr: &str, value: &str| (expr.to_string(), value.to_string());
        let found =
            find_message_sources(sif.statements(), "error: “dup” is already a named search");
        // The statement only matches without the whitespace it starts with, so the values are
        // found with its relaxed pattern.
        assert_eq!(
            variables(&found),
            vec![vec![pair(
                "this->um_message",
                "“dup” is already a named search"
            )]]
        );
        // The causes have the values of their own statements.
        assert_eq!(
            variables(&found[0].causes),
            vec![vec![pair("name", "“dup”")]]
        );
        // A value that is too short to look up the source of still has a variable.
        let found = find_message_sources(sif.statements(), "42 messages");
        assert_eq!(variables(&found), vec![vec![pair("count", "42")]]);
        assert!(found[0].causes.is_empty());
    }

    #[test]
    fn test_glyph_literals_in_other_languages() {
        let glyphs = |path: &str, source: &str| -> Vec<String> {
            let code = CodeSource::from_string(&PathBuf::from(path), source);
            extract_logging(&[code], &ProgressTracker::new())
                .pop()
                .map(|sif| {
                    sif.log_statements
                        .iter()
                        .map(|stmt| stmt.pattern().as_str().to_string())
                        .collect()
                })
                .unwrap_or_default()
        };
        assert_eq!(
            glyphs(
                "in-mem.rs",
                "fn icon(ok: bool) -> char { if ok { '✔' } else { '\\u{2718}' } }"
            ),
            vec![r"(?s)^✔$", r"(?s)^✘$"]
        );
        assert_eq!(
            glyphs(
                "in-mem.java",
                "class A { char c = '\\u2718'; char d = 'x'; }"
            ),
            vec![r"(?s)^✘$"]
        );
    }

    const PYTHON_FORMATTED_SOURCE: &str = r#"
def main(name, count, err, user, d, a, b, off, old_id):
    logger.info("user %s has %d items" % (name, count))
    logger.warning("Failed: " + str(err) + "!")
    logger.debug("{}: {} missing (byte {offset})".format(name, user.path, offset=off))
    logger.info("{0.name} is {{literal}} 100%".format(user))
    logger.error("100%% of %s" % name)
    logger.info(a + b)
    logger.info("%s took " + "%s", name, count)
    logger.debug("process (%s, %s) is dying" % old_id)
    print("total: %d" % count)
    out.write("\n" + name)
    logging.log(logging.WARNING, "lost " + name)
"#;

    #[test]
    fn test_python_formatted() {
        let code = CodeSource::from_string(Path::new("in-mem.py"), PYTHON_FORMATTED_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(
            patterns,
            vec![
                r"(?s)^user (.*) has (.*) items$",
                r"(?s)^Failed: (.*)!$",
                r"(?s)^(.*): (.*) missing \(byte (.*)\)$",
                r"(?s)^(.*) is \{literal\} 100%$",
                r"(?s)^100% of (.*)$",
                r"(?s)^(.*) took (.*)$",
                r"(?s)^process \((.*), (.*)\) is dying$",
                r"(?s)^lost (.*)$",
            ]
        );
        assert_eq!(src_refs[0].level, LogLevel::Info);
        assert_eq!(src_refs[7].level, LogLevel::Warn);
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_FORMATTED_SOURCE,
                6,
                "process (1, 2) is dying"
            ),
            pairs(&[("old_id[0]", "1"), ("old_id[1]", "2")])
        );
        assert_eq!(src_refs[1].level, LogLevel::Warn);
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_FORMATTED_SOURCE,
                0,
                "user bob has 3 items"
            ),
            pairs(&[("name", "bob"), ("count", "3")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_FORMATTED_SOURCE,
                1,
                "Failed: disk full!"
            ),
            pairs(&[("str(err)", "disk full")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_FORMATTED_SOURCE,
                2,
                "a1: /tmp/x missing (byte 42)"
            ),
            pairs(&[("name", "a1"), ("user.path", "/tmp/x"), ("off", "42")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_FORMATTED_SOURCE,
                3,
                "bob is {literal} 100%"
            ),
            pairs(&[("user.name", "bob")])
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_FORMATTED_SOURCE, 5, "job took 5s"),
            pairs(&[("name", "job"), ("count", "5s")])
        );
    }

    const PYTHON_MAPPING_SOURCE: &str = r#"
def main(d, port, user, n):
    logger.info("x %(a)s" % d)
    logger.error('bind "%(name)s" port %(port)d: %(error)s' % port)
    logger.info("%(who)s has %(count)d items, 100%%" % {"who": user.name, "count": n})
    logger.info("%(user)s again" % locals())
    logger.info("%(a)s and %s" % d)
    logger.info("%(missing)s" % {"who": user})
    logger.info("%(a)s" % (d,))
    logger.info("%(user)s left %(where)s", {"user": user.name, "where": d})
    logger.info("%(user)s stays", d, n)
"#;

    #[test]
    fn test_python_mapping() {
        let code = CodeSource::from_string(Path::new("in-mem.py"), PYTHON_MAPPING_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let patterns: Vec<&str> = sif
            .log_statements
            .iter()
            .map(|s| s.pattern().as_str())
            .collect();
        // A mix of keys and other placeholders, a missing key, and a tuple are not mappings.
        assert_eq!(
            patterns,
            vec![
                r"(?s)^x (.*)$",
                r#"(?s)^bind "(.*)" port (.*): (.*)$"#,
                r"(?s)^(.*) has (.*) items, 100%$",
                r"(?s)^(.*) again$",
                r"(?s)^(.*) left (.*)$",
                r"(?s)^%\(user\)s stays$",
            ]
        );
        // `logging` formats with the mapping when it is the only argument.
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_MAPPING_SOURCE, 4, "bob left home"),
            pairs(&[("user.name", "bob"), ("d", "home")])
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_MAPPING_SOURCE, 0, "x 1"),
            pairs(&[("d['a']", "1")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_MAPPING_SOURCE,
                1,
                r#"bind "cc_port" port 8090: in use"#
            ),
            pairs(&[
                ("port['name']", "cc_port"),
                ("port['port']", "8090"),
                ("port['error']", "in use")
            ])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_MAPPING_SOURCE,
                2,
                "bob has 3 items, 100%"
            ),
            pairs(&[("user.name", "bob"), ("n", "3")])
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_MAPPING_SOURCE, 3, "bob again"),
            pairs(&[("user", "bob")])
        );
    }

    const PYTHON_MESSAGE_VAR_SOURCE: &str = r#"
def main(port, path, name, n, x):
    msg = 'Could not bind to "%(name)s" port %(port)s' % port
    alerts.append(self._generate_cc_alert('PORT_BIND_ERROR', msg, port))
    text = "user %s left" % name
    logger.warning(text)
    reason = "no such file: " + path
    raise ValueError(reason)
    err_msg = "Bad count {}".format(n)
    report(code=1, msg=err_msg)
    query = "SELECT %s FROM t" % x
    db.execute(query)
    label = "total %s" % n
    widget.set(label)
    fmt = "user %s has %d items"
    logger.info(fmt, name, n)
    sep = ", "
    logger.info(sep)
    unused_msg = "never used %s" % x
"#;

    #[test]
    fn test_python_message_vars() {
        let code = CodeSource::from_string(Path::new("in-mem.py"), PYTHON_MESSAGE_VAR_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let summary: Vec<(&str, usize, Option<&str>, LogLevel, MessageCategory)> = sif
            .log_statements
            .iter()
            .map(|s| {
                (
                    s.pattern().as_str(),
                    s.line_no,
                    s.call_name.as_deref(),
                    s.level,
                    s.category,
                )
            })
            .collect();
        // The SQL and the label are passed to calls that are not about messages, the separator
        // has no text, and the last message is never used.
        assert_eq!(
            summary,
            vec![
                (
                    r#"(?s)^Could not bind to "(.*)" port (.*)$"#,
                    3,
                    Some("self._generate_cc_alert"),
                    LogLevel::Unknown,
                    MessageCategory::Other
                ),
                (
                    r"(?s)^user (.*) left$",
                    5,
                    Some("logger.warning"),
                    LogLevel::Warn,
                    MessageCategory::Log
                ),
                (
                    r"(?s)^no such file: (.*)$",
                    7,
                    Some("raise ValueError"),
                    LogLevel::Unknown,
                    MessageCategory::Error
                ),
                (
                    r"(?s)^Bad count (.*)$",
                    9,
                    Some("report"),
                    LogLevel::Unknown,
                    MessageCategory::Other
                ),
                (
                    r"(?s)^user (.*) has (.*) items$",
                    15,
                    Some("logger.info"),
                    LogLevel::Info,
                    MessageCategory::Log
                ),
            ]
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_MESSAGE_VAR_SOURCE,
                0,
                r#"Could not bind to "cc_port" port 8090"#
            ),
            pairs(&[("port['name']", "cc_port"), ("port['port']", "8090")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_MESSAGE_VAR_SOURCE,
                2,
                "no such file: /x"
            ),
            pairs(&[("path", "/x")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_MESSAGE_VAR_SOURCE,
                4,
                "user bob has 3 items"
            ),
            pairs(&[("name", "bob"), ("n", "3")])
        );
    }

    const PYTHON_MESSAGE_USE_SOURCE: &str = r#"
def describe(path, n):
    msg = "Could not open %s" % path
    return msg

def results(n, name, x):
    err = "Found %d problems" % n
    warnings.append({"code": "PROBLEMS", "msg": err})
    path = "/tmp/%s" % name
    return path
    fmt = "%(user)s logged in"
    logger.info(fmt, {"user": name})
    msg = "shadowed %s" % x
    report(msg=x)

class BadThing(Exception):
    def __init__(self, thing):
        self.message = "Bad thing: %s" % thing
        self.code = "BAD_%s" % thing
        self.label = "label %s" % thing

    def show(self):
        log.error(self.label)

def mismatch(a, b):
    err = ("Mismatch %s != %s; "
           "check config")
    msg = ""
    msg += err % (a, b)
    tmpl = "user {} has {n} items"
    log.info(tmpl.format(a, n=b))
    return msg
"#;

    #[test]
    fn test_python_message_uses() {
        let code = CodeSource::from_string(Path::new("in-mem.py"), PYTHON_MESSAGE_USE_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let summary: Vec<(&str, usize, Option<&str>, MessageCategory)> = sif
            .log_statements
            .iter()
            .map(|s| {
                (
                    s.pattern().as_str(),
                    s.line_no,
                    s.call_name.as_deref(),
                    s.category,
                )
            })
            .collect();
        // A path that is returned is not a message, a variable that is only the name of a
        // keyword is not used, and an attribute that is not a message is only kept when it is
        // logged.
        assert_eq!(
            summary,
            vec![
                (
                    r"(?s)^Could not open (.*)$",
                    3,
                    Some("return"),
                    MessageCategory::Format
                ),
                (
                    r"(?s)^Found (.*) problems$",
                    7,
                    None,
                    MessageCategory::Format
                ),
                (
                    r"(?s)^(.*) logged in$",
                    11,
                    Some("logger.info"),
                    MessageCategory::Log
                ),
                (r"(?s)^Bad thing: (.*)$", 18, None, MessageCategory::Format),
                (
                    r"(?s)^label (.*)$",
                    20,
                    Some("log.error"),
                    MessageCategory::Log
                ),
                (
                    r"(?s)^Mismatch (.*) != (.*); check config$",
                    26,
                    None,
                    MessageCategory::Format
                ),
                (
                    r"(?s)^user (.*) has (.*) items$",
                    30,
                    Some("log.info"),
                    MessageCategory::Log
                ),
            ]
        );
        // A template is formatted where it is used.
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_MESSAGE_USE_SOURCE,
                5,
                "Mismatch 1 != 2; check config"
            ),
            pairs(&[("a", "1"), ("b", "2")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_MESSAGE_USE_SOURCE,
                6,
                "user bob has 3 items"
            ),
            pairs(&[("a", "bob"), ("b", "3")])
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_MESSAGE_USE_SOURCE, 2, "bob logged in"),
            pairs(&[("name", "bob")])
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_MESSAGE_USE_SOURCE, 3, "Bad thing: x"),
            pairs(&[("thing", "x")])
        );
    }

    const PYTHON_FORMATTED_EDGE_SOURCE: &str = r#"
def main(name, value, d, x):
    logger.info("hex {:x} done".format(255))
    logger.info("%s: %%d" % name, value)
    logger.info("\N{BULLET} item {}".format(x))
    logging.log(logging.WARNING, "lost {}".format(x))
    logger.info("key {0[k]} {0[1]} end".format(d))
    logger.info("val %s end" % (x))
    logger.info("A " + "b %s" % x + " c")
    logger.info("repr {!r} spaced {:,}".format(x, 1000))
"#;

    #[test]
    fn test_python_formatted_edge_cases() {
        let code = CodeSource::from_string(Path::new("in-mem.py"), PYTHON_FORMATTED_EDGE_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(
            patterns,
            vec![
                r"(?s)^hex (.*) done$",
                r"(?s)^. item (.*)$",
                r"(?s)^lost (.*)$",
                r"(?s)^key (.*) (.*) end$",
                r"(?s)^val (.*) end$",
                r"(?s)^A b (.*) c$",
                r"(?s)^repr (.*) spaced (.*)$",
            ]
        );
        assert_eq!(src_refs[2].level, LogLevel::Warn);
        let pairs_at =
            |index, line| extract_pairs("in-mem.py", PYTHON_FORMATTED_EDGE_SOURCE, index, line);
        assert_eq!(pairs_at(0, "hex ff done"), pairs(&[("255", "ff")]));
        assert_eq!(pairs_at(1, "• item a1"), pairs(&[("x", "a1")]));
        assert_eq!(
            pairs_at(3, "key v1 v2 end"),
            pairs(&[("d['k']", "v1"), ("d[1]", "v2")])
        );
        assert_eq!(pairs_at(4, "val 5 end"), pairs(&[("x", "5")]));
        assert_eq!(pairs_at(5, "A b 5 c"), pairs(&[("x", "5")]));
        assert_eq!(
            pairs_at(6, "repr 'a' spaced 1,000"),
            pairs(&[("x", "'a'"), ("1000", "1,000")])
        );
    }

    #[test]
    fn test_cpp_raw_string_not_logged() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.cc"),
            r#"
void load() {
    auto doc = json::parse(R"({"a": 1})");
    puts(R"(usage: tool [options])");
}
"#,
        );
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .map(|stmts| stmts.log_statements)
            .unwrap_or_default();
        assert!(src_refs.is_empty());
    }

    #[test]
    fn test_cpp_plus_concatenation() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.cc"),
            r#"
void connect() {
    spdlog::error("Failed to create proxy: " + std::string(error->message));
    spdlog::error(
        "server does not support the events; the "
        "module will be disabled" +
        std::to_string(version));
    spdlog::warn("{} retries " + name + " left", count);
    foo("abc" + 1);
    spdlog::info("abc" + 1);
    add_path("prefix-" + name);
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(
            patterns,
            vec![
                "(?s)^Failed to create proxy: (.*)$",
                "(?s)^server does not support the events; the module will be disabled(.*)$",
                "(?s)^(.*) retries (.*) left$",
            ]
        );
        assert_eq!(src_refs[0].level, LogLevel::Error);
        assert_eq!(src_refs[1].level, LogLevel::Error);
        assert_eq!(src_refs[2].level, LogLevel::Warn);
        assert_eq!(src_refs[2].vars, vec!["count"]);
    }

    #[test]
    fn test_extract_java_wrapped_message_edge_cases() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.java"),
            r#"
class Main {
  void run(String name, int count, Level level, Exception e) {
    LOG.info(String.format(FORMAT, "literal arg"));
    LOG.info(String.format("%2$s then %1$s, again %<s", name, count));
    LOG.info(String.format("{id} is %s", name));
    LOGGER.log(level, () -> "supplier with var level " + name);
    LOG.info(AUDIT_MARKER, String.format("audit %s", name));
    LOG.loadConfig(CONFIG_PATH);
    LOGGER.config("config message");
  }
}
"#,
        );
        let stmts = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        // Neither `AUDIT_MARKER` nor `CONFIG_PATH` is a message.
        assert!(stmts.message_refs.is_empty());
        let src_refs = stmts.log_statements;
        let found: Vec<(&str, LogLevel)> = src_refs
            .iter()
            .map(|s| (s.pattern().as_str(), s.level))
            .collect();
        assert_eq!(
            found,
            vec![
                ("(?s)^(.*) then (.*), again (.*)$", LogLevel::Info),
                (r"(?s)^\{id\} is (.*)$", LogLevel::Info),
                ("(?s)^supplier with var level (.*)$", LogLevel::Unknown),
                ("(?s)^audit (.*)$", LogLevel::Info),
                ("(?s)^config message$", LogLevel::Info),
            ]
        );
        assert_eq!(src_refs[0].arg_exprs(), vec!["count", "name", "name"]);
        assert_eq!(src_refs[1].arg_exprs(), vec!["name"]);

        let line = "5 then bob, again bob";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        let pairs: Vec<(String, String)> = extract_variables(&log_ref, &src_refs[0])
            .into_iter()
            .map(|pair| (pair.expr, pair.value))
            .collect();
        assert_eq!(
            pairs,
            vec![
                ("count".to_string(), "5".to_string()),
                ("name".to_string(), "bob".to_string()),
                ("name".to_string(), "bob".to_string()),
            ]
        );
    }

    #[test]
    fn test_level_from_name_not_logging() {
        for name in [
            "dialog->setErrorText",
            "dialog.show_warning",
            "catalog.add_info_entry",
            "logger.isDebugEnabled",
            "log_config",
        ] {
            assert_eq!(LogLevel::from_name(name), None, "{name}");
        }
        assert_eq!(
            LogLevel::from_name("logger.warning_once"),
            Some(LogLevel::Warn)
        );
        assert_eq!(LogLevel::from_name("log_warn_once"), Some(LogLevel::Warn));
        assert_eq!(LogLevel::from_name("config"), Some(LogLevel::Info));
        assert_eq!(
            LogLevel::from_level_arg("Level.CONFIG"),
            Some(LogLevel::Info)
        );
        assert_eq!(LogLevel::from_log_text("CONFIG"), Some(LogLevel::Info));
    }

    #[test]
    fn test_cpp_wrapped_message() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.cc"),
            r#"
void connect() {
    tr_logAddInfo(fmt::format("Cached {} global address {}", family, addr));
    tr_logAddError(_("Couldn't obtain source address"));
    tr_logAddWarn(fmt::format(fmt::runtime(_("Couldn't read '{path}'")), fmt::arg("path", name)));
    tr_logAddDebugTor(tor, fmt::format("Verifying {} pieces", count));
    tr_logAddTraceHand(this, "sending vc");
    label->setText(tr("not a log message"));
    auto msg = fmt::format("not logged {}", count);
    report(fmt::format("not a log message {}", count));
    m_dialog->setErrorText(fmt::format("Bad value {}", count));
    logger->info(fmt::runtime(_("Loaded {}")), "file.txt");
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let found: Vec<(&str, LogLevel)> = src_refs
            .iter()
            .map(|s| (s.pattern().as_str(), s.level))
            .collect();
        assert_eq!(
            found,
            vec![
                ("(?s)^Cached (.*) global address (.*)$", LogLevel::Info),
                ("(?s)^Couldn't obtain source address$", LogLevel::Error),
                ("(?s)^Couldn't read '(.*)'$", LogLevel::Warn),
                ("(?s)^Verifying (.*) pieces$", LogLevel::Debug),
                ("(?s)^sending vc$", LogLevel::Trace),
                ("(?s)^not a log message (.*)$", LogLevel::Unknown),
                ("(?s)^Bad value (.*)$", LogLevel::Unknown),
                ("(?s)^Loaded (.*)$", LogLevel::Info),
            ]
        );
        assert_eq!(src_refs[5].category, MessageCategory::Format);
        assert_eq!(src_refs[5].call_name.as_deref(), Some("fmt::format"));
        assert_eq!(src_refs[6].category, MessageCategory::Format);
        assert_eq!(src_refs[7].vars, vec!["\"file.txt\""]);
        assert_eq!(src_refs[0].vars, vec!["family", "addr"]);
        assert_eq!(src_refs[3].vars, vec!["count"]);
    }

    #[test]
    fn test_cpp_returned_message() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.cc"),
            r#"
Result<std::string, user_message> com_unix_time(exec_context& ec) {
    if (bad) {
        return ec.make_error("invalid unix time -- {}", args[1]);
    }
    if (url.empty()) {
        return Err(lnav::console::user_message::error(
            "expecting a regex101.com URL to import"));
    }
    if (missing) {
        return Err(fmt::format(FMT_STRING("failed to find file: {} -- {}"), path, err));
    }
    msg = lnav::console::user_message::error("unexpected JSON value");
    tab->zErrMsg = sqlite3_mprintf("Environment variable names cannot contain '='");
    auto msg = fmt::format("not logged {}", count);
    auto it = m.find("key");
    auto rc = get_preferred("not an error");
    name = sqlite3_mprintf("not an error %s", x);
    return std::string("not a message");
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let found: Vec<(&str, Option<&str>)> = sif
            .log_statements
            .iter()
            .map(|s| (s.pattern().as_str(), s.call_name.as_deref()))
            .collect();
        assert_eq!(
            found,
            vec![
                ("(?s)^invalid unix time -- (.*)$", Some("ec.make_error")),
                (
                    "(?s)^expecting a regex101\\.com URL to import$",
                    Some("lnav::console::user_message::error")
                ),
                ("(?s)^failed to find file: (.*) -- (.*)$", Some("Err")),
                (
                    "(?s)^unexpected JSON value$",
                    Some("lnav::console::user_message::error")
                ),
                (
                    "(?s)^Environment variable names cannot contain '='$",
                    Some("sqlite3_mprintf")
                ),
            ]
        );
        // `Err` makes an error, it is not a log call with a level.
        let err = &sif.log_statements[2];
        assert_eq!(err.category, MessageCategory::Error);
        assert_eq!(err.level, LogLevel::Unknown);
    }

    /// The patterns of the statements found in a C++ snippet.
    fn cpp_patterns(source: &str) -> Vec<String> {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), source);
        // A file without any statements has no entry.
        extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .map(|sif| {
                sif.log_statements
                    .iter()
                    .map(|s| s.pattern().as_str().to_string())
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The text of each source of a message found in a C++ snippet, with the line of its best
    /// candidate.
    fn cpp_find(source: &str, message: &str) -> Vec<(String, Option<usize>)> {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        find_message_sources(sif.statements(), message)
            .iter()
            .map(|source| {
                (
                    source.text.clone(),
                    source.candidates.first().map(|stmt| stmt.line_no),
                )
            })
            .collect()
    }

    #[test]
    fn test_cpp_find_rewrapped_message() {
        // The message has two spaces after a sentence, but it was copied from a man page that
        // wrapped and indented it.  A generic statement matches the text as is, so the exact
        // whitespace is not enough.
        let source = r#"
void f() {
    help_text(":add-source-path")
        .with_summary(
            "Add a path to the source code that generated log messages.  "
            "Adding source allows lnav to more accurately extract values "
            "from log messages");
    status.set_value("%'d messages ", count);
}
"#;
        assert_eq!(
            cpp_find(
                source,
                "           Add a path to the source code that generated log messages.  Adding
           source allows lnav to more accurately extract values from log
           messages
"
            ),
            vec![(
                "Add a path to the source code that generated log messages. Adding source \
                 allows lnav to more accurately extract values from log messages"
                    .to_string(),
                Some(5)
            )]
        );
    }

    #[test]
    fn test_cpp_find_checks_value_kinds() {
        let source = r#"
void f() {
    status.set_value("%'d messages ", count);
    help_text(":filter-in").with_summary("Only show lines that match the given messages");
}
"#;
        // A grouped number is a value of `%'d`.
        assert_eq!(
            cpp_find(source, "1,234 messages"),
            vec![("1,234 messages".to_string(), Some(3))]
        );
        // Text is not, so the fragment of the other message is found instead.
        assert_eq!(
            cpp_find(source, "show lines that match the given messages"),
            vec![(
                "show lines that match the given messages".to_string(),
                Some(4)
            )]
        );
        // But it is better than nothing.
        assert_eq!(
            cpp_find(source, "Some other messages"),
            vec![("Some other messages".to_string(), Some(3))]
        );
    }

    #[test]
    fn test_cpp_find_fragment_skips_weaker_overlaps() {
        let source = r#"
void f() {
    one.append(" is already a named search");
    two.append(" is already a named search");
    um_error("a named search must have a name");
    log_info("%s: using %zu named search hits in [%d:%d)", a, b, c, d);
    um_error("Unable to open file");
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let found =
            find_message_sources(sif.statements(), "✘ error: “dup” is already a named search");
        let lines: Vec<(bool, Vec<usize>)> = found
            .iter()
            .map(|source| {
                (
                    source.partial,
                    source.candidates.iter().map(|stmt| stmt.line_no).collect(),
                )
            })
            .collect();
        // The statements that only share "a named search" or " named search", which the best
        // ones share too, are left out, but the ones that are as good are kept.
        assert_eq!(lines, vec![(true, vec![3, 4])]);
    }

    #[test]
    fn test_cpp_find_fragment_of_value() {
        let source = r#"
void f(attr_line_t& al) {
    al.append(" is already a named search");
}

void g() {
    err.set_value("error: %s", msg);
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let found =
            find_message_sources(sif.statements(), "✘ error: “dup” is already a named search");
        // The generic statement matches after the prefix, but its value is only partly from
        // another statement, which is found too.  The statements are in different functions,
        // so the pieces are not put together, and `"error: "` is too short to be a piece from
        // another function anyway.
        let last = found.last().unwrap();
        assert_eq!(last.candidates.first().map(|stmt| stmt.line_no), Some(7));
        let lines: Vec<(bool, Vec<usize>)> = last
            .causes
            .iter()
            .map(|cause| {
                (
                    cause.partial,
                    cause.candidates.iter().map(|stmt| stmt.line_no).collect(),
                )
            })
            .collect();
        assert_eq!(lines, vec![(true, vec![3])]);
    }

    // The tests below are known gaps, found by running `log2src find` on the expected error
    // output of lnav's tests.  They are expected to fail, so remove the `should_panic` when one
    // is fixed.

    #[test]
    #[should_panic(expected = "assertion `left == right` failed")]
    fn test_cpp_message_in_conditional_xfail() {
        // Each branch of the conditional is a message.
        let found = cpp_patterns(
            r#"
void list() {
    auto um = console::user_message::error(
        total == 0 ? "no running lnav instances were found"
                   : "no running lnav instances matched");
}
"#,
        );
        assert_eq!(
            found,
            vec![
                "(?s)^no running lnav instances were found$",
                "(?s)^no running lnav instances matched$",
            ]
        );
    }

    #[test]
    #[should_panic(expected = "assertion `left == right` failed")]
    fn test_cpp_message_in_brace_init_xfail() {
        // A result type that is made with a brace initializer.
        let found = cpp_patterns(
            r#"
scan_result scan(string_fragment line_frag) {
    if (!line_frag.startswith("{")) {
        return scan_no_match{"line is not a JSON object"};
    }
}
"#,
        );
        assert_eq!(found, vec!["(?s)^line is not a JSON object$"]);
    }

    #[test]
    #[should_panic(expected = "assertion `left == right` failed")]
    fn test_cpp_message_wrapped_in_builder_arg_xfail() {
        // The literal is wrapped in a constructor that is the argument of a builder method.
        let found = cpp_patterns(
            r#"
void check() {
    errors.emplace_back(
        lnav::console::user_message::error("invalid sample")
            .with_help(attr_line_t(
                "A timestamp needs to be captured in order for a "
                "line to be recognized as a log message")));
}
"#,
        );
        assert_eq!(
            found,
            vec![
                "(?s)^invalid sample$",
                "(?s)^A timestamp needs to be captured in order for a line to be recognized as a log message$",
            ]
        );
    }

    #[test]
    fn test_find_prefers_longer_prefix() {
        // The statement with the `: ` covers more of the message than the one without it, so
        // it wins, rather than splitting the message at the end of the shorter one.  The text
        // of the builder is from the whole chain of appends.
        let found = cpp_find(
            r#"
Result<void, user_message> exec(exec_context& ec) {
    return ec.make_error("unable to open file");
}
void open_files() {
    auto um = lnav::console::user_message::error(
        attr_line_t("unable to open file: ").append(lnav::roles::file(fn)));
}
"#,
            "unable to open file: badfilename",
        );
        assert_eq!(
            found,
            vec![("unable to open file: badfilename".to_string(), Some(7))]
        );
    }

    #[test]
    #[should_panic(expected = "assertion failed")]
    fn test_find_ignores_single_words_in_values_xfail() {
        // Statements that are a single word, like `"level"`, should not be matched to words
        // inside a quoted value, like a path.
        let sources = cpp_find(
            r#"
void report() {
    errors.emplace_back(attr_line_t("invalid value ").append_quoted(path));
    out.append("value");
    out.append("level");
}
"#,
            "invalid value “/invalid_props_log/value/log_level”",
        );
        assert!(sources
            .iter()
            .all(|(text, line)| line.is_none() || text.starts_with("invalid value")));
    }

    const CPP_SPLIT_ELSE_SOURCE: &str = r#"
    bool load(int fd) {
        int rc = 0;
        if (fd == 0) {
            rc = 1;
        }
    #ifdef HAVE_BZLIB_H // ü
        else if (fd == 1) {
            rc = 2;
        }
    #endif
        else {
            rc = 3;
        }
        log_debug("END load fd(%d): %d", fd, rc);
        return true;
    }
    "#;

    #[test]
    fn test_cpp_else_split_by_preproc() {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), CPP_SPLIT_ELSE_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 1);
        assert_eq!(src_refs[0].line_no, 15);
        assert_eq!(src_refs[0].text, r#""END load fd(%d): %d""#);
        assert_eq!(src_refs[0].vars, vec!["fd", "rc"]);
    }

    const CPP_SPLIT_ELSE_COMPLEX_SOURCE: &str = r#"
bool load(int fd) {
    int rc = 0;
    if (fd == 0) {
        rc = 1;
    }
#if defined(HAVE_BZLIB_H) && (BZ_VERSION >= 0x0106 || \
        !defined(_WIN32)) /* ü */
    else if (fd == 1) {
        rc = 2;
    }
#elif (defined(HAVE_ZLIB_H) && ZLIB_VERNUM > 0x1200) || defined(__APPLE__)
    else if (fd == 2) {
        rc = 4;
    }
#endif
    else {
        rc = 3;
    }
    log_debug("END load fd(%d): %d", fd, rc);
    return true;
}

int other(int x) {
    log_debug("second %d", x);
    return 1;
}
"#;

    #[test]
    fn test_cpp_else_split_by_complex_preproc() {
        let code =
            CodeSource::from_string(&PathBuf::from("in-mem.cc"), CPP_SPLIT_ELSE_COMPLEX_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 2);
        assert_eq!(src_refs[0].line_no, 20);
        assert_eq!(src_refs[0].qualified_name, "load");
        assert_eq!(src_refs[0].vars, vec!["fd", "rc"]);
        assert_eq!(src_refs[1].line_no, 25);
        assert_eq!(src_refs[1].qualified_name, "other");
    }

    const CPP_SPLIT_SIGNATURE_SOURCE: &str = r#"
#ifdef WIN32
int load(int fd, HANDLE h) {
#else
int load(int fd) {
#endif
    log_debug("first %d", fd);
    return 0;
}

int other(int x) {
    log_debug("second %d", x);
    return 1;
}
"#;

    #[test]
    fn test_cpp_signature_split_by_preproc() {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), CPP_SPLIT_SIGNATURE_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 2);
        assert_eq!(src_refs[0].qualified_name, "load");
        assert_eq!(src_refs[1].qualified_name, "other");
    }

    #[test]
    fn test_cpp_nested_statements() {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), CPP_NESTED_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let found: Vec<(usize, &str)> = src_refs
            .iter()
            .map(|s| (s.line_no, s.text.as_str()))
            .collect();
        assert_eq!(
            found,
            vec![
                (10, r#""sending line %d""#),
                (17, r#""kind one %d""#),
                (21, r#""positive line %d""#),
            ]
        );
    }

    #[test]
    fn test_basic_cpp() {
        let log_ref = LogRefBuilder::new().build("Hello, Steve!");
        let code = CodeSource::from_string(Path::new("in-mem.cc"), CPP_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 1);
        let vars = extract_variables(&log_ref, &src_refs[0]);
        assert_eq!(
            vars,
            vec![VariablePair {
                expr: "argv[1]".to_string(),
                value: "Steve".to_string(),
                ambiguous: false,
            },]
        );
    }

    const C_SOURCE: &str = r#"
#include <stdio.h>
#include <inttypes.h>

LOG_DEFINE("not a log statement");

static struct node *
node_insert(struct node *list, const char *class, uint64_t size)
{
    struct node *new = calloc(1, sizeof(*new));

    if (new == NULL)
        fatal_fr(errno, "calloc %s", class);
    serverLog(LL_WARNING, "inserted %s with %" PRIu64 " bytes", class, size);
    debug3_f("list " "head %p", list);
    puts("abc" + size);
    return new;
}
"#;

    #[test]
    fn test_basic_c() {
        let code = CodeSource::from_string(Path::new("in-mem.c"), C_SOURCE);
        assert_eq!(code.info.language, SourceLanguage::C);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let summary: Vec<_> = src_refs
            .iter()
            .map(|s| {
                (
                    s.line_no,
                    s.level,
                    s.qualified_name.as_str(),
                    s.text.as_str(),
                )
            })
            .collect();
        assert_eq!(
            summary,
            vec![
                (13, LogLevel::Fatal, "node_insert", r#""calloc %s""#),
                (
                    14,
                    LogLevel::Warn,
                    "node_insert",
                    r#""inserted %s with %" PRIu64 " bytes""#
                ),
                (15, LogLevel::Debug, "node_insert", r#""list " "head %p""#),
            ]
        );
        assert_eq!(
            src_refs[0].name,
            "node_insert(struct node *list, const char *class, uint64_t size)"
        );
        assert_eq!(src_refs[0].vars, vec!["class".to_string()]);
        assert_eq!(
            src_refs[1].vars,
            vec!["class".to_string(), "size".to_string()]
        );

        let log_ref = LogRefBuilder::new().build("inserted widget with 42 bytes");
        let result = link_to_source(&log_ref, &sif).unwrap();
        assert_eq!(result.line_no, 14);
        assert_eq!(
            extract_variables(&log_ref, &result),
            vec![
                VariablePair {
                    expr: "class".to_string(),
                    value: "widget".to_string(),
                    ambiguous: false,
                },
                VariablePair {
                    expr: "size".to_string(),
                    value: "42".to_string(),
                    ambiguous: false,
                },
            ]
        );
    }

    #[test]
    fn test_c_header_language() {
        let c_header = "static inline void push(struct node *new, const char *class) {\n    log_info(\"push %s\", class);\n}\n";
        let code = CodeSource::from_string(Path::new("list.h"), c_header);
        assert_eq!(code.info.language, SourceLanguage::C);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 1);
        assert_eq!(
            src_refs[0].name,
            "push(struct node *new, const char *class)"
        );
        assert_eq!(sif.language, SourceLanguage::C);

        for cpp_header in [
            "namespace net { void f(); }",
            "class Server : public Base {};",
            "template <typename T> T max(T a, T b);",
            "#include <string>\n",
            "void f() { std::cout << 1; }",
        ] {
            let code = CodeSource::from_string(Path::new("x.h"), cpp_header);
            assert_eq!(code.info.language, SourceLanguage::Cpp, "{cpp_header}");
        }
        let code = CodeSource::from_string(Path::new("x.hpp"), "int x;");
        assert_eq!(code.info.language, SourceLanguage::Cpp);
    }

    #[test]
    fn test_c_printf_extensions() {
        let code = CodeSource::from_string(
            Path::new("in-mem.c"),
            r#"
void f(const char *path, int a, int b, long total) {
    syslog(LOG_ERR, "open %s failed: %m", path);
    printf("%2$d before %1$d\n", a, b);
    log_info("total %'ld bytes", total);
    strcpy(buf, "default");
    strcat(path, "/");
    setenv("LANG", "C", 1);
    vsnprintf(buf, sizeof(buf), "formatted %d", a);
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<(&str, MessageCategory)> = src_refs
            .iter()
            .map(|s| (s.pattern().as_str(), s.category))
            .collect();
        assert_eq!(
            patterns,
            vec![
                ("(?s)^open (.*) failed: (.*)$", MessageCategory::Log),
                (r"(?s)^(.*) before (.*?)\s*$", MessageCategory::Other),
                ("(?s)^total (.*) bytes$", MessageCategory::Log),
                ("(?s)^formatted (.*)$", MessageCategory::Format),
            ]
        );
        let pairs = |index: usize, line: &str| -> Vec<(String, String)> {
            let log_ref = LogRefBuilder::new().build(line);
            extract_variables(&log_ref, &src_refs[index])
                .into_iter()
                .map(|pair| (pair.expr, pair.value))
                .collect()
        };
        assert_eq!(
            pairs(0, "open /etc/x failed: No such file or directory"),
            vec![
                ("path".to_string(), "/etc/x".to_string()),
                (
                    "strerror(errno)".to_string(),
                    "No such file or directory".to_string()
                ),
            ]
        );
        assert_eq!(
            pairs(1, "2 before 1\n"),
            vec![
                ("b".to_string(), "2".to_string()),
                ("a".to_string(), "1".to_string()),
            ]
        );
        assert_eq!(
            pairs(2, "total 1,024 bytes"),
            vec![("total".to_string(), "1,024".to_string())]
        );
    }

    #[test]
    fn test_cpp_encoding_prefixes() {
        // The prefix is not part of the text, and the escapes are decoded the same.
        let patterns = cpp_patterns(
            r#"
void f() {
    log_error(u8"✘ handler %s exited", name);
    log_error(L"wide string %s", name);
    log_error(u"utf-16 string %s", name);
    log_error(U"utf-32 string %s", name);
    log_error(u8"joined " "pieces %s", name);
    log_error("\xe2\x9c\x98 byte escapes %s", name);
}
"#,
        );
        assert_eq!(
            patterns,
            vec![
                r"(?s)^✘ handler (.*) exited$",
                r"(?s)^wide string (.*)$",
                r"(?s)^utf-16 string (.*)$",
                r"(?s)^utf-32 string (.*)$",
                r"(?s)^joined pieces (.*)$",
                r"(?s)^✘ byte escapes (.*)$",
            ]
        );
    }

    #[test]
    fn test_c_escapes_and_placeholders() {
        let code = CodeSource::from_string(
            Path::new("in-mem.c"),
            r#"
void f(int n) {
    log_info("{literal} %d\e[0m", n);
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_eq!(src_refs.len(), 1);
        // Braces are not placeholders in C.
        let log_ref = LogRefBuilder::new().build("{literal} 7\x1b[0m");
        let result = link_to_source(&log_ref, &sif).unwrap();
        assert_eq!(
            extract_variables(&log_ref, &result),
            vec![VariablePair {
                expr: "n".to_string(),
                value: "7".to_string(),
                ambiguous: false,
            }]
        );
    }

    const PYTHON_CONCAT_SOURCE: &str = r#"
def main(name, count, x):
    logger.info("first part "
                "second part %s", name)
    logger.info(f"user {name} " "has %d items", count)
    logger.info(r"C:\dir " "x\tz")
    logger.info(f"{{literal}} {name}")
    logger.info(R"raw\d {x}")
"#;

    #[test]
    fn test_python_concatenation() {
        let code = CodeSource::from_string(Path::new("in-mem.py"), PYTHON_CONCAT_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(
            patterns,
            vec![
                r"(?s)^first part second part (.*)$",
                r"(?s)^user (.*) has (.*) items$",
                r"(?s)^C:\\dir x\tz$",
                r"(?s)^\{literal\} (.*)$",
                r"(?s)^raw\\d \{x\}$",
            ]
        );
        assert_eq!((src_refs[0].line_no, src_refs[0].end_line_no), (3, 4));
        assert_eq!(src_refs[0].vars, vec!["name"]);

        let line = "user bob has 3 items";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        assert_eq!(
            extract_variables(&log_ref, &src_refs[1]),
            vec![
                VariablePair {
                    expr: "name".to_string(),
                    value: "bob".to_string(),
                    ambiguous: false,
                },
                VariablePair {
                    expr: "count".to_string(),
                    value: "3".to_string(),
                    ambiguous: false,
                },
            ]
        );
        let line = "C:\\dir x\tz";
        assert!(src_refs[2].pattern().is_match(line));
    }

    const PYTHON_SOURCE: &str = r#"
def main(args):
    logger.info("foo %s \N{greek small letter pi}", test_var)
    logging.info(f'Hello, {args[1]}!')
    logger.warning(f"warning message:\nlow disk space")
    logger.info(rf"""info message:
processing \started -- {args[0]}""")
"#;

    #[test]
    fn test_basic_python() {
        let log_ref = LogRefBuilder::new().build("foo bar π");
        let code = CodeSource::from_string(Path::new("in-mem.py"), PYTHON_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_yaml_snapshot!(sif.statements().collect::<Vec<_>>());
        let vars = extract_variables(&log_ref, &src_refs[0]);
        assert_eq!(
            vars,
            vec![VariablePair {
                expr: "test_var".to_string(),
                value: "bar".to_string(),
                ambiguous: false,
            },]
        );
    }

    fn qualified_names(filename: &str, source: &str) -> Vec<(String, String)> {
        let code = CodeSource::from_string(&PathBuf::from(filename), source);
        extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements
            .into_iter()
            .map(|s| (s.name, s.qualified_name))
            .collect()
    }

    fn pairs(expected: &[(&str, &str)]) -> Vec<(String, String)> {
        expected
            .iter()
            .map(|(name, qname)| (name.to_string(), qname.to_string()))
            .collect()
    }

    #[test]
    fn test_qualified_name_rust() {
        let source = r#"
mod net {
    struct Server;
    impl Server {
        fn handle(&self) {
            info!("handling");
        }
    }
    impl Drop for Server {
        fn drop(&mut self) {
            info!("dropping");
        }
    }
    trait Greet {
        fn greet(&self) {
            fn inner() {
                info!("inner");
            }
            let f = || info!("closure");
        }
    }
}
"#;
        assert_eq!(
            qualified_names("in-mem.rs", source),
            pairs(&[
                ("handle", "net::Server::handle"),
                ("drop", "net::<Server as Drop>::drop"),
                ("inner", "net::Greet::greet::inner"),
                ("greet", "net::Greet::greet"),
            ])
        );
    }

    #[test]
    fn test_qualified_name_java() {
        let source = r#"package com.example
    .net;

class Server {
    Server() {
        logger.info("constructing");
    }

    void handle() {
        logger.info("handling");
        Runnable r = () -> logger.info("lambda");
    }

    static class Inner {
        void run() {
            logger.info("inner");
        }
    }
}
"#;
        assert_eq!(
            qualified_names("Server.java", source),
            pairs(&[
                ("Server", "com.example.net.Server.Server"),
                ("handle", "com.example.net.Server.handle"),
                ("handle", "com.example.net.Server.handle"),
                ("run", "com.example.net.Server.Inner.run"),
            ])
        );
    }

    #[test]
    fn test_qualified_name_cpp() {
        let source = r#"
namespace net {
namespace {
void helper() {
    printf("helper");
}
}

class Server {
    void handle() {
        printf("handle");
    }
};

const char *Server::name(int x) const {
    printf("name %d", x);
}

Server &Server::self() {
    printf("self");
}
}
"#;
        assert_eq!(
            qualified_names("in-mem.cc", source),
            pairs(&[
                ("helper()", "net::(anonymous namespace)::helper"),
                ("handle()", "net::Server::handle"),
                ("Server::name(int x) const", "net::Server::name"),
                ("Server::self()", "net::Server::self"),
            ])
        );
    }

    #[test]
    fn test_qualified_name_python() {
        let source = r#"
logger.info("top")

class Server:
    def handle(self):
        logger.info("handle")

        def inner():
            logger.info("inner")
"#;
        assert_eq!(
            qualified_names("in-mem.py", source),
            pairs(&[
                ("<module>", "<module>"),
                ("handle", "Server.handle"),
                ("inner", "Server.handle.<locals>.inner"),
            ])
        );
    }

    #[test]
    fn test_name_cpp_namespace_scope() {
        let source = r#"
namespace net {
auto init = [] { LOG(INFO, "start"); };
}
"#;
        assert_eq!(
            qualified_names("in-mem.cc", source),
            pairs(&[("init", "net::init")])
        );
    }

    #[test]
    fn test_name_in_attribute() {
        let source = r#"
mod net {
    #[doc = my_macro!("in attr")]
    // a comment
    #[inline]
    fn handle() {}
}
"#;
        assert_eq!(
            qualified_names("in-mem.rs", source),
            pairs(&[("handle", "net::handle")])
        );
    }

    #[test]
    fn test_rust_concat_format() {
        let source = r#"
fn main() {
    info!(concat!("request ", "{} done"), id);
    warn!(concat!("x", env!("Y")));
    let p = Config::load(concat!("a", "b"));
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.rs"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(patterns, vec![r"(?s)^request (.*) done$"]);
        assert_eq!(src_refs[0].level, LogLevel::Info);
        assert_eq!(src_refs[0].vars, vec!["id"]);
    }

    #[test]
    fn test_rust_tracing_events() {
        let source = r#"
fn main() {
    trace!(target: "gc", "saving last-use data");
    debug!(target: "net", "fetching {} from {url}", name);
    tracing::debug!(?path, %why, includes, "load config from file");
    trace!(token = t, count = ?self.items.len(), "finish");
    debug!(target: "x", pending);
    tracing::trace!(start = now().to_string());
    info!(r#type = kind, "typed");
    debug!(span = field::Empty, done, "with empty");
    tracing::event!(Level::WARN, retries, "giving up");
    tracing::event!(target: "y", tracing::Level::ERROR, "failed {}", code);
    warn!(target: "z", concat!("joined ", "{}"), v);
    info!("plain {}", x);
    debug!(1 + 2, "not a field");
}
"#;
        let code = CodeSource::from_string(&PathBuf::from("in-mem.rs"), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let mut stmts: Vec<_> = sif.log_statements.iter().collect();
        stmts.sort_by_key(|stmt| stmt.line_no);
        let actual: Vec<(&str, LogLevel, Vec<&str>)> = stmts
            .iter()
            .map(|stmt| (stmt.pattern().as_str(), stmt.level, stmt.arg_exprs()))
            .collect();
        assert_eq!(
            actual,
            vec![
                (r"(?s)^saving last-use data$", LogLevel::Trace, vec![]),
                (
                    r"(?s)^fetching (.*) from (.*)$",
                    LogLevel::Debug,
                    vec!["name", "url"]
                ),
                (
                    r"(?s)^load config from file path=(.*) why=(.*) includes=(.*)$",
                    LogLevel::Debug,
                    vec!["path", "why", "includes"]
                ),
                (
                    r"(?s)^finish token=(.*) count=(.*)$",
                    LogLevel::Trace,
                    vec!["t", "self.items.len()"]
                ),
                (r"(?s)^pending=(.*)$", LogLevel::Debug, vec!["pending"]),
                (
                    r"(?s)^start=(.*)$",
                    LogLevel::Trace,
                    vec!["now().to_string()"]
                ),
                (r"(?s)^typed type=(.*)$", LogLevel::Info, vec!["kind"]),
                (r"(?s)^with empty done=(.*)$", LogLevel::Debug, vec!["done"]),
                (
                    r"(?s)^giving up retries=(.*)$",
                    LogLevel::Warn,
                    vec!["retries"]
                ),
                (r"(?s)^failed (.*)$", LogLevel::Error, vec!["code"]),
                (r"(?s)^joined (.*)$", LogLevel::Warn, vec!["v"]),
                (r"(?s)^plain (.*)$", LogLevel::Info, vec!["x"]),
            ]
        );

        // The values of the fields are the variables, as `tracing-subscriber` prints them.
        let temp_dir = tempfile::tempdir().unwrap();
        fs::write(temp_dir.path().join("main.rs"), source).unwrap();
        let matcher = matcher_for(temp_dir.path());
        let match_message = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            let mapping = matcher.match_log_statement(&log_ref, &LogMatchOptions::default())?;
            Some((
                mapping.src_ref?.line_no,
                mapping
                    .variables
                    .into_iter()
                    .map(|var| (var.expr, var.value))
                    .collect::<Vec<_>>(),
            ))
        };
        let pairs = |vars: &[(&str, &str)]| -> Vec<(String, String)> {
            vars.iter()
                .map(|(expr, value)| (expr.to_string(), value.to_string()))
                .collect()
        };
        assert_eq!(
            match_message(r#"load config from file path="/a/b" why=Cli includes=true"#),
            Some((
                5,
                pairs(&[("path", r#""/a/b""#), ("why", "Cli"), ("includes", "true")])
            ))
        );
        assert_eq!(
            match_message("pending=3"),
            Some((7, pairs(&[("pending", "3")])))
        );
    }

    #[test]
    fn test_name_outside_function() {
        // Statements outside of a function should not be named after the whole file, and
        // compile-time macros, like `env!()`, are not logging.
        let source = r#"
const VERSION: &str = env!("VERSION");
static DEFAULTS: &str = include_str!("defaults.toml");
static CONFIG: LazyLock<Config> = LazyLock::new(|| {
    info!("loading config");
    Config::load(concat!("a", "b"))
});
mod net {
    static NAME: LazyLock<String> = LazyLock::new(|| {
        debug!("naming");
        std::env!("NAME").to_string()
    });
}
"#;
        assert_eq!(
            qualified_names("in-mem.rs", source),
            pairs(&[("CONFIG", "CONFIG"), ("NAME", "net::NAME")])
        );
    }

    /// Map the message of each log statement, without quotes, to its block ID.
    fn block_ids(filename: &str, source: &str) -> HashMap<String, u32> {
        let code = CodeSource::from_string(&PathBuf::from(filename), source);
        extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements
            .into_iter()
            .map(|s| (s.text.trim_matches('"').to_string(), s.block_id))
            .collect()
    }

    /// Check that the statements in each group share a block and that the groups differ.
    fn assert_blocks(ids: &HashMap<String, u32>, groups: &[&[&str]]) {
        let mut seen = std::collections::HashSet::new();
        for group in groups {
            let id = ids[group[0]];
            for msg in &group[1..] {
                assert_eq!(
                    ids[*msg], id,
                    "{} should be in the block of {}",
                    msg, group[0]
                );
            }
            assert!(seen.insert(id), "{} should be in its own block", group[0]);
        }
        assert_eq!(
            ids.len(),
            groups.iter().map(|group| group.len()).sum::<usize>()
        );
    }

    #[test]
    fn test_block_id_rust() {
        let source = r#"
fn run(x: Result<(), ()>, c: bool) {
    info!("a");
    if c {
        info!("b");
    }
    info!("c");
    match x {
        Ok(_) => info!("d"),
        Err(_) => info!("e"),
    }
}
"#;
        assert_blocks(
            &block_ids("in-mem.rs", source),
            &[&["a", "c"], &["b"], &["d"], &["e"]],
        );
    }

    #[test]
    fn test_block_id_java() {
        let source = r#"
class Server {
    void handle(boolean x, int y) {
        logger.info("a");
        if (x) logger.info("b");
        else logger.info("c");
        for (int i = 0; i < y; i++) {
            logger.info("d");
        }
        logger.info("e");
        switch (y) {
            case 1:
                logger.info("f");
                break;
        }
    }
}
"#;
        assert_blocks(
            &block_ids("Server.java", source),
            &[&["a", "e"], &["b"], &["c"], &["d"], &["f"]],
        );
    }

    #[test]
    fn test_block_id_java_finally() {
        let source = r#"
class Server {
    void handle() {
        logger.info("a");
        try {
            logger.info("b");
        } catch (IOException e) {
            logger.info("c");
        } finally {
            logger.info("d");
        }
        try (Reader r = open()) {
            logger.info("e");
        } finally {
            logger.info("f");
        }
    }
}
"#;
        assert_blocks(
            &block_ids("Server.java", source),
            &[&["a"], &["b", "d"], &["c"], &["e", "f"]],
        );
    }

    #[test]
    fn test_block_id_cpp() {
        let source = r#"
void handle(bool x, int y) {
    printf("a");
    if (x) printf("b");
    while (y--) {
        printf("c");
    }
    printf("d");
    switch (y) {
        case 1:
            printf("e");
            break;
    }
}
"#;
        assert_blocks(
            &block_ids("in-mem.cc", source),
            &[&["a", "d"], &["b"], &["c"], &["e"]],
        );
    }

    #[test]
    fn test_block_id_cpp_preproc() {
        let source = r#"
void handle(bool x) {
    printf("a");
#ifdef X
    printf("b");
#elif defined(Y)
    printf("c");
#else
    printf("d");
#endif
    if (x) {
#if X
        printf("e");
#else
        printf("f");
#endif
    }
}
"#;
        assert_blocks(
            &block_ids("in-mem.cc", source),
            &[&["a", "b", "c", "d"], &["e", "f"]],
        );
    }

    #[test]
    fn test_block_id_python() {
        let source = r#"
logger.info("a")

def handle(x):
    logger.info("b")
    if x:
        logger.info("c")
    logger.info("d")
"#;
        let ids = block_ids("in-mem.py", source);
        assert_eq!(ids["a"], 0);
        assert_blocks(&ids, &[&["a"], &["b", "d"], &["c"]]);
    }

    #[test]
    fn test_block_id_python_finally() {
        let source = r#"
def handle():
    logger.info("a")
    try:
        logger.info("b")
    except IOError:
        logger.info("c")
    finally:
        logger.info("d")
"#;
        assert_blocks(
            &block_ids("in-mem.py", source),
            &[&["a"], &["b", "d"], &["c"]],
        );
    }

    const KOTLIN_SOURCE: &str = r#"package com.example

class Server {
    fun handle(user: User, count: Int, e: Exception) {
        logger.info("Started {} with {} threads", user.name, count)
        logger.info("Hello $user, you have ${user.messages.size} messages")
        logger.debug("Mixed {} and $count \$5\ttab", user)
        logger.info { "Lazy ${user.id}" }
        logger.error(e) { "Failed for $user" }
        logger.warn("Concat " + count + " items")
        logger.warn(e) {
            "Failed [count=${user.messages.size}] " +
                "after ${count / 1000.0} sec, " + count + " left"
        }
        logger.info("""raw $user""")
        println("not a log $user")
    }
}
"#;

    fn kotlin_statements() -> StatementsInFile {
        let code = CodeSource::from_string(Path::new("Server.kt"), KOTLIN_SOURCE);
        extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
    }

    fn kotlin_vars(src_ref: &Statement, line: &str) -> Vec<(String, String)> {
        let log_ref = LogRefBuilder::new().build(line);
        extract_variables(&log_ref, src_ref)
            .into_iter()
            .map(|pair| (pair.expr, pair.value))
            .collect()
    }

    #[test]
    fn test_basic_kotlin() {
        let sif = kotlin_statements();
        let src_refs = &sif.log_statements;
        assert_yaml_snapshot!(sif.statements().collect::<Vec<_>>());
        // The raw string and println() are skipped.
        assert_eq!(src_refs.len(), 7);
        assert_eq!(
            kotlin_vars(&src_refs[0], "Started api with 4 threads"),
            pairs(&[("user.name", "api"), ("count", "4")])
        );
        assert_eq!(
            kotlin_vars(&src_refs[1], "Hello bob, you have 3 messages"),
            pairs(&[("user", "bob"), ("user.messages.size", "3")])
        );
        assert_eq!(
            kotlin_vars(&src_refs[2], "Mixed bob and 7 $5\ttab"),
            pairs(&[("user", "bob"), ("count", "7")])
        );
        assert_eq!(
            kotlin_vars(&src_refs[3], "Lazy 42"),
            pairs(&[("user.id", "42")])
        );
        assert_eq!(
            kotlin_vars(&src_refs[4], "Failed for bob"),
            pairs(&[("user", "bob")])
        );
        assert_eq!(
            kotlin_vars(&src_refs[5], "Concat 9 items"),
            pairs(&[("count", "9")])
        );
        assert_eq!(
            kotlin_vars(&src_refs[6], "Failed [count=3] after 1.5 sec, 1500 left"),
            pairs(&[
                ("user.messages.size", "3"),
                ("count / 1000.0", "1.5"),
                ("count", "1500")
            ])
        );
    }

    #[test]
    fn test_qualified_name_kotlin() {
        let source = r#"package com.example.net

class Server {
    constructor(x: Int) {
        logger.info("constructing")
    }

    init {
        logger.info("initializing")
    }

    fun handle() {
        logger.info("handling")
        val r = Runnable { logger.info("lambda") }
    }

    companion object {
        fun create() {
            logger.info { "creating" }
        }
    }
}

object Registry {
    fun register() {
        logger.info("registering")
    }
}

fun main() {
    logger.info("main")
}
"#;
        assert_eq!(
            qualified_names("my-server.kt", source),
            pairs(&[
                ("Server", "com.example.net.Server.Server"),
                ("Server", "com.example.net.Server.Server"),
                ("handle", "com.example.net.Server.handle"),
                ("handle", "com.example.net.Server.handle"),
                ("create", "com.example.net.Server.Companion.create"),
                ("register", "com.example.net.Registry.register"),
                ("main", "com.example.net.My_serverKt.main"),
            ])
        );
        let renamed = format!("@file:JvmName(\"Util\")\n{}", source);
        assert_eq!(
            qualified_names("main.kt", &renamed).last().unwrap().1,
            "com.example.net.Util.main"
        );
    }

    #[test]
    fn test_block_id_kotlin() {
        let source = r#"
fun handle(x: Boolean, y: Int) {
    logger.info("a")
    if (x) logger.info("b") else logger.info("c")
    for (i in 0 until y) {
        logger.info("d")
    }
    logger.info { "e" }
    when (y) {
        1 -> logger.info("f")
        else -> {
            logger.info("g")
        }
    }
    try {
        logger.info("h")
    } catch (e: Exception) {
        logger.error(e) { "i" }
    } finally {
        logger.info("j")
    }
    items.forEach { logger.info("k") }
}
"#;
        assert_blocks(
            &block_ids("in-mem.kt", source),
            &[
                &["a", "e"],
                &["b"],
                &["c"],
                &["d"],
                &["f"],
                &["g"],
                &["h", "j"],
                &["i"],
                &["k"],
            ],
        );
    }

    fn extract_pairs(path: &str, source: &str, index: usize, line: &str) -> Vec<(String, String)> {
        let log_ref = LogRefBuilder::new().build(line);
        let code = CodeSource::from_string(Path::new(path), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        extract_variables(&log_ref, &src_refs[index])
            .into_iter()
            .map(|pair| (pair.expr, pair.value))
            .collect()
    }

    const JAVA_ADJACENT_SOURCE: &str = r#"
public class Adjacent {
    public void run() {
        log.debug("foo bar: {} {} {}", a, b, c);
        log.debug("sizes: {} {} {}", name, items.size(), other);
        log.debug("flags: {}{}", ready, map.isEmpty());
    }
}
"#;

    #[test]
    fn test_adjacent_java() {
        assert_eq!(
            extract_pairs(
                "in-mem.java",
                JAVA_ADJACENT_SOURCE,
                0,
                "foo bar: 1 2 [a, b]"
            ),
            pairs(&[("a", "1"), ("b", "2"), ("c", "[a, b]")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.java",
                JAVA_ADJACENT_SOURCE,
                0,
                "foo bar: {k=v, z=1} [x, y] 42"
            ),
            pairs(&[("a", "{k=v, z=1}"), ("b", "[x, y]"), ("c", "42")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.java",
                JAVA_ADJACENT_SOURCE,
                1,
                "sizes: hello world 5 foo bar"
            ),
            pairs(&[
                ("name", "hello world"),
                ("items.size()", "5"),
                ("other", "foo bar")
            ])
        );
        assert_eq!(
            extract_pairs("in-mem.java", JAVA_ADJACENT_SOURCE, 2, "flags: truefalse"),
            pairs(&[("ready", "true"), ("map.isEmpty()", "false")])
        );
        // Without any hints, the split is ambiguous and the earlier placeholder gets more.
        assert_eq!(
            extract_pairs(
                "in-mem.java",
                JAVA_ADJACENT_SOURCE,
                0,
                "foo bar: 1 hello world 3"
            ),
            pairs(&[("a", "1 hello"), ("b", "world"), ("c", "3")])
        );
    }

    const RUST_ADJACENT_SOURCE: &str = r#"
fn adjacent(mask: u32, name: &str, point: Point) {
    debug!("mask: {:x} {}", mask, name);
    debug!("point: {:?} {:?}", name, point);
    debug!("count: {} {}", name, v.len());
    debug!("trailing: {} {}\n", name, point);
    debug!("len: {} {}", v.len(), name);
    debug!("cast: {} {}", x as u8, name);
}
"#;

    #[test]
    fn test_adjacent_rust() {
        assert_eq!(
            extract_pairs("in-mem.rs", RUST_ADJACENT_SOURCE, 0, "mask: ff hello world"),
            pairs(&[("mask", "ff"), ("name", "hello world")])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.rs",
                RUST_ADJACENT_SOURCE,
                1,
                r#"point: "a b" Point { x: 1, y: 2 }"#
            ),
            pairs(&[("name", r#""a b""#), ("point", "Point { x: 1, y: 2 }")])
        );
        assert_eq!(
            extract_pairs("in-mem.rs", RUST_ADJACENT_SOURCE, 2, "count: a b c 3"),
            pairs(&[("name", "a b c"), ("v.len()", "3")])
        );
        // The trailing newline is optional and is not part of the last value.
        for line in ["trailing: a [b, c]", "trailing: a [b, c]\n"] {
            assert_eq!(
                extract_pairs("in-mem.rs", RUST_ADJACENT_SOURCE, 3, line),
                pairs(&[("name", "a"), ("point", "[b, c]")])
            );
        }
        // The arguments of a macro are tokens, so they are parsed to get the kind of value.
        assert_eq!(
            extract_pairs("in-mem.rs", RUST_ADJACENT_SOURCE, 4, "len: 3 a b c"),
            pairs(&[("v.len()", "3"), ("name", "a b c")])
        );
        assert_eq!(
            extract_pairs("in-mem.rs", RUST_ADJACENT_SOURCE, 5, "cast: 7 a b"),
            pairs(&[("x as u8", "7"), ("name", "a b")])
        );
    }

    const CPP_ADJACENT_SOURCE: &str = r#"
    #include <stdio.h>

    int main(int argc, char* argv[]) {
        printf("got: %d %s %5d|", argc, argv[1], count);
        printf("char: %s%3c|", name, c);
        spdlog::info("day {:%Y-%m-%d} {}", tp, name);
        printf("padded: %5d|", count);
    }
    "#;

    #[test]
    fn test_adjacent_cpp() {
        assert_eq!(
            extract_pairs(
                "in-mem.cc",
                CPP_ADJACENT_SOURCE,
                0,
                "got: 1 hello world    42|"
            ),
            pairs(&[("argc", "1"), ("argv[1]", "hello world"), ("count", "42")])
        );
        assert_eq!(
            extract_pairs("in-mem.cc", CPP_ADJACENT_SOURCE, 1, "char: a b  z|"),
            pairs(&[("name", "a b"), ("c", "z")])
        );
        // A date/time spec does not end with a kind of value.
        assert_eq!(
            extract_pairs("in-mem.cc", CPP_ADJACENT_SOURCE, 2, "day 2026-10-25 a b"),
            pairs(&[("tp", "2026-10-25 a"), ("name", "b")])
        );
        // The padding is left out of the value even when there is only one placeholder.
        assert_eq!(
            extract_pairs("in-mem.cc", CPP_ADJACENT_SOURCE, 3, "padded:    42|"),
            pairs(&[("count", "42")])
        );
    }

    #[test]
    fn test_type_mismatch_still_matches() {
        // The format spec only helps split the values, so a value that does not look like the
        // spec still matches.
        let source = r#"
    int main() {
        printf("value: %f", x);
        printf("values: %f %s", x, name);
    }
    "#;
        assert_eq!(
            extract_pairs("in-mem.cc", source, 0, "value: -nan(ind)"),
            pairs(&[("x", "-nan(ind)")])
        );
        // With more than one placeholder, there is no split where the values match their kinds,
        // so the greedy split is used.
        assert_eq!(
            extract_pairs("in-mem.cc", source, 1, "values: -nan(ind) hello world"),
            pairs(&[("x", "-nan(ind) hello"), ("name", "world")])
        );
    }

    /// Extract the variables and get the names of the ones that are ambiguous.
    fn ambiguous_vars(path: &str, source: &str, index: usize, line: &str) -> Vec<String> {
        let log_ref = LogRefBuilder::new().build(line);
        let code = CodeSource::from_string(Path::new(path), source);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        extract_variables(&log_ref, &src_refs[index])
            .into_iter()
            .filter(|pair| pair.ambiguous)
            .map(|pair| pair.expr)
            .collect()
    }

    #[test]
    fn test_ambiguous_variables() {
        let java = |index, line| ambiguous_vars("in-mem.java", JAVA_ADJACENT_SOURCE, index, line);
        // Every value could be different: "1 hello", "world", "3" or "1", "hello", "world 3".
        assert_eq!(
            java(0, "foo bar: 1 hello world 3"),
            vec!["a".to_string(), "b".to_string(), "c".to_string()]
        );
        // The brackets and the kinds of values leave only one valid split.
        assert!(java(0, "foo bar: 1 2 [a, b]").is_empty());
        assert!(java(1, "sizes: hello world 5 foo bar").is_empty());
        // There is only one way to split the line.
        assert!(java(0, "foo bar: 1 2 3").is_empty());

        let source = r#"
    int main() {
        printf("pair: %s %s, count=%d", a, b, count);
        printf("padded: %5d %5d|", x, y);
        printf("values: %f %s", x, name);
    }
    "#;
        let cpp = |index, line| ambiguous_vars("in-mem.cc", source, index, line);
        // Only the values next to each other are ambiguous.
        assert_eq!(
            cpp(0, "pair: a b c, count=5"),
            vec!["a".to_string(), "b".to_string()]
        );
        // Padding is not ambiguity.
        assert!(cpp(1, "padded:     1     2|").is_empty());
        // No split has values that look like their kinds.
        assert_eq!(
            cpp(2, "values: -nan(ind) hello world"),
            vec!["x".to_string(), "name".to_string()]
        );
    }

    #[test]
    fn test_ambiguous_json() {
        let pair = |ambiguous| VariablePair {
            expr: "a".to_string(),
            value: "1".to_string(),
            ambiguous,
        };
        assert_eq!(
            serde_json::to_string(&pair(false)).unwrap(),
            r#"{"expr":"a","value":"1"}"#
        );
        assert_eq!(
            serde_json::to_string(&pair(true)).unwrap(),
            r#"{"expr":"a","value":"1","ambiguous":true}"#
        );
    }

    #[test]
    fn test_empty_values() {
        let java = r#"
public class Empty {
    public void run() {
        log.info("user={} logged in", name);
        log.info("pair: [{}] [{}]", a, b);
    }
}
"#;
        assert_eq!(
            extract_pairs("in-mem.java", java, 0, "user= logged in"),
            pairs(&[("name", "")])
        );
        assert_eq!(
            extract_pairs("in-mem.java", java, 1, "pair: [] [x y]"),
            pairs(&[("a", ""), ("b", "x y")])
        );
        let rust = r#"
fn f(a: &str, b: u32) {
    debug!("a={} b={}", a, b);
}
"#;
        assert_eq!(
            extract_pairs("in-mem.rs", rust, 0, "a= b=2"),
            pairs(&[("a", ""), ("b", "2")])
        );
        let cpp = r#"
    int main() {
        printf("name: '%s'", name);
    }
    "#;
        assert_eq!(
            extract_pairs("in-mem.cc", cpp, 0, "name: ''"),
            pairs(&[("name", "")])
        );
        let python = r#"
def main(name):
    logger.info("name=%s.", name)
    logger.info(f"name={name}.")
"#;
        for index in [0, 1] {
            assert_eq!(
                extract_pairs("in-mem.py", python, index, "name=."),
                pairs(&[("name", "")])
            );
        }
        let kotlin = r#"
class Empty {
    fun run(name: String) {
        logger.info("name=$name.")
    }
}
"#;
        assert_eq!(
            extract_pairs("in-mem.kt", kotlin, 0, "name=."),
            pairs(&[("name", "")])
        );
    }

    #[test]
    fn test_escaped_braces() {
        let rust = r#"
fn f(x: &str) {
    debug!("set {{{}}}", x);
}
"#;
        assert_eq!(
            extract_pairs("in-mem.rs", rust, 0, "set {a b}"),
            pairs(&[("x", "a b")])
        );
        let cpp = r#"
    void f() {
        spdlog::info("map {{{}: {}}}", k, v);
    }
    "#;
        assert_eq!(
            extract_pairs("in-mem.cc", cpp, 0, "map {a: 1}"),
            pairs(&[("k", "a"), ("v", "1")])
        );
        let java = r#"
public class Braces {
    public void run() {
        log.info("json {\"a\": {}}", v);
    }
}
"#;
        assert_eq!(
            extract_pairs("in-mem.java", java, 0, r#"json {"a": 1}"#),
            pairs(&[("v", "1")])
        );
        let kotlin = r#"
class Braces {
    fun run(a: String, b: String) {
        logger.info("obj {} {{}}", a, b)
    }
}
"#;
        assert_eq!(
            extract_pairs("in-mem.kt", kotlin, 0, "obj a {b}"),
            pairs(&[("a", "a"), ("b", "b")])
        );
    }

    #[test]
    fn test_empty_values_ambiguous() {
        let source = r#"
public class Empty {
    public void run() {
        log.info("joined: {}{}", a, b);
        log.info("words: {} {}", a, b);
    }
}
"#;
        // Either value could be empty.
        assert_eq!(
            ambiguous_vars("in-mem.java", source, 0, "joined: ab"),
            vec!["a".to_string(), "b".to_string()]
        );
        // Neither value can be empty since the message does not have a space next to them.
        assert!(ambiguous_vars("in-mem.java", source, 1, "words: a b").is_empty());
        // The first value is empty.
        assert!(ambiguous_vars("in-mem.java", source, 1, "words:  b").is_empty());
    }

    #[test]
    fn test_prefer_fewer_placeholders() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(
            dir.path().join("Done.java"),
            r#"
public class Done {
    public void run() {
        log.info("Done{}", suffix);
        log.info("Done");
    }
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(dir.path());
        let line_of = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|mapping| mapping.src_ref.map(|src_ref| src_ref.line_no))
        };
        // Both statements match, but "Done{}" would need an empty value.
        assert_eq!(line_of("Done"), Some(5));
        assert_eq!(line_of("Done now"), Some(4));
    }

    #[test]
    fn test_prefer_non_empty_values() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(
            dir.path().join("Failed.java"),
            r#"
public class Failed {
    public void run() {
        log.info("Failed: {} at {}", what, where);
        log.info("Failed: {}", what);
        log.info("Stopped {} at {}", what, where);
    }
}
"#,
        )
        .unwrap();
        let matcher = matcher_for(dir.path());
        let line_of = |msg: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(msg)).build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|mapping| mapping.src_ref.map(|src_ref| src_ref.line_no))
        };
        // The higher quality statement would need an empty value.
        assert_eq!(line_of("Failed: x at "), Some(5));
        assert_eq!(line_of("Failed: x at y"), Some(4));
        // An empty value is fine when no other statement matches.
        assert_eq!(line_of("Stopped x at "), Some(6));

        // A line number is better evidence than whether a value is empty.
        let line_at = |msg: &str, lineno: usize| {
            let log_ref = LogRefBuilder::new()
                .with_file(Some("Failed.java"))
                .with_lineno(Some(lineno))
                .with_body(Some(msg))
                .build(msg);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|mapping| mapping.src_ref.map(|src_ref| src_ref.line_no))
        };
        assert_eq!(line_at("Failed: x at ", 4), Some(4));
        assert_eq!(line_at("Failed: x at ", 5), Some(5));
        // The second time, the statement is found through the line number cache.
        assert_eq!(line_at("Failed: x at ", 4), Some(4));
        assert_eq!(line_at("Failed: x at ", 5), Some(5));
    }

    #[test]
    fn test_link_to_source_prefers_non_empty_values() {
        let code = CodeSource::from_string(
            Path::new("in-mem.java"),
            r#"
public class Done {
    public void run() {
        log.info("Done{}", suffix);
        log.info("Done");
    }
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let line_of = |msg: &str| {
            let log_ref = LogRefBuilder::new().build(msg);
            link_to_source(&log_ref, &sif).map(|src_ref| src_ref.line_no)
        };
        assert_eq!(line_of("Done"), Some(5));
        assert_eq!(line_of("Done now"), Some(4));
    }

    const PYTHON_ADJACENT_SOURCE: &str = r#"
def main(args):
    logger.info(f"stats: {name} {count:d} {other}")
    logger.info("items: %s %s", len(items), rest)
    logger.info(f"bits: {mask:b} {name}")
    logger.info(f"day: {d:%Y-%m-%d}")
"#;

    #[test]
    fn test_adjacent_python() {
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_ADJACENT_SOURCE,
                0,
                "stats: hello world 3 foo bar"
            ),
            pairs(&[
                ("name", "hello world"),
                ("count", "3"),
                ("other", "foo bar")
            ])
        );
        assert_eq!(
            extract_pairs(
                "in-mem.py",
                PYTHON_ADJACENT_SOURCE,
                1,
                "items: 3 ['a b', 'c']"
            ),
            pairs(&[("len(items)", "3"), ("rest", "['a b', 'c']")])
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_ADJACENT_SOURCE, 2, "bits: 101 a b"),
            pairs(&[("mask", "101"), ("name", "a b")])
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_ADJACENT_SOURCE, 3, "day: 2026-10-25"),
            pairs(&[("d", "2026-10-25")])
        );
    }

    const KOTLIN_ADJACENT_SOURCE: &str = r#"
class Adjacent {
    fun run(name: String, items: List<String>, other: String) {
        logger.info("sizes: $name ${items.size} $other")
    }
}
"#;

    #[test]
    fn test_adjacent_kotlin() {
        assert_eq!(
            extract_pairs(
                "in-mem.kt",
                KOTLIN_ADJACENT_SOURCE,
                0,
                "sizes: hello world 5 [a, b]"
            ),
            pairs(&[
                ("name", "hello world"),
                ("items.size", "5"),
                ("other", "[a, b]")
            ])
        );
    }

    #[test]
    fn test_adjacent_after_cache_round_trip() {
        let code = CodeSource::from_string(Path::new("in-mem.java"), JAVA_ADJACENT_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let encoded =
            bincode::serde::encode_to_vec(&src_refs[1], bincode::config::standard()).unwrap();
        let (decoded, _): (Statement, usize) =
            bincode::serde::decode_from_slice(&encoded, bincode::config::standard()).unwrap();
        let log_ref = LogRefBuilder::new().build("sizes: hello world 5 foo bar");
        let vars: Vec<(String, String)> = extract_variables(&log_ref, &decoded)
            .into_iter()
            .map(|pair| (pair.expr, pair.value))
            .collect();
        assert_eq!(
            vars,
            pairs(&[
                ("name", "hello world"),
                ("items.size()", "5"),
                ("other", "foo bar")
            ])
        );
    }

    const CPP_PERCENT_SOURCE: &str = r#"
    #include <stdio.h>

    int main(int argc, char* argv[]) {
        printf("100%% done in %d steps", steps);
        printf("[%*d] %s", width, value, name);
        printf("wrote%n %s", &count, name);
    }
    "#;

    #[test]
    fn test_percent_cpp() {
        assert_eq!(
            extract_pairs("in-mem.cc", CPP_PERCENT_SOURCE, 0, "100% done in 5 steps"),
            pairs(&[("steps", "5")])
        );
        assert_eq!(
            extract_pairs("in-mem.cc", CPP_PERCENT_SOURCE, 1, "[   42] bob"),
            pairs(&[("value", "42"), ("name", "bob")])
        );
        assert_eq!(
            extract_pairs("in-mem.cc", CPP_PERCENT_SOURCE, 2, "wrote bob"),
            pairs(&[("name", "bob")])
        );
    }

    const PYTHON_PERCENT_SOURCE: &str = r#"
def main(x, t, pct):
    logger.info("100% done")
    logger.info("50% done", exc_info=True)
    logger.info(f"{x} is 50% done")
    logger.info(f"{x} took %s", t)
    logger.info("%d%% done", pct)
"#;

    #[test]
    fn test_percent_python() {
        let code = CodeSource::from_string(Path::new("in-mem.py"), PYTHON_PERCENT_SOURCE);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(
            patterns,
            vec![
                r"(?s)^100% done$",
                r"(?s)^50% done$",
                r"(?s)^(.*) is 50% done$",
                r"(?s)^(.*) took (.*)$",
                r"(?s)^(.*)% done$",
            ]
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_PERCENT_SOURCE, 2, "job is 50% done"),
            pairs(&[("x", "job")])
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_PERCENT_SOURCE, 3, "job took 5s"),
            pairs(&[("x", "job"), ("t", "5s")])
        );
        assert_eq!(
            extract_pairs("in-mem.py", PYTHON_PERCENT_SOURCE, 4, "75% done"),
            pairs(&[("pct", "75")])
        );
    }

    fn extract_levels(path: &str, source: &str) -> Vec<(String, LogLevel)> {
        let code = CodeSource::from_string(Path::new(path), source);
        let mut sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        prune_log_calls(sif.statements_for_pruning().collect());
        sif.log_statements
            .into_iter()
            .map(|src_ref| (src_ref.text, src_ref.level))
            .collect()
    }

    #[test]
    fn test_kernel_level_args() {
        let code = CodeSource::from_string(
            Path::new("sd.c"),
            r#"
void sd(struct scsi_disk *sdkp, struct scsi_device *sdp, int wp, const char *name) {
    sd_printk(KERN_NOTICE, sdkp, "Write Protect is %s\n", wp ? "on" : "off");
    sdev_printk(KERN_ERR, sdp, "Unable to read %s\n", name);
    printk(KERN_INFO "Booting paravirtualized kernel on %s\n", name);
    printk(KERN_WARNING "disk %s is slow\n", name);
    printk(LOG_ERR "syslog style %s\n", name);
    printk(KERN_CONT " and more\n");
    printk(KERN_DEFAULT "no level %s\n", name);
    printk(PREFIX "not a level %s\n", name);
}
"#,
        );
        let mut sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        prune_log_calls(sif.statements_for_pruning().collect());
        let found: Vec<(String, LogLevel, MessageCategory)> = sif
            .log_statements
            .iter()
            .map(|stmt| (stmt.text.clone(), stmt.level, stmt.category))
            .collect();
        let expected = |text: &str, level, category| (text.to_string(), level, category);
        assert_eq!(
            found,
            vec![
                // The level is the argument in front of the message, so the call is logging
                // although its name has no level and its family has only one.
                expected(
                    "\"Write Protect is %s\\n\"",
                    LogLevel::Info,
                    MessageCategory::Log
                ),
                expected(
                    "\"Unable to read %s\\n\"",
                    LogLevel::Error,
                    MessageCategory::Log
                ),
                // The level is a macro in front of the string.
                expected(
                    "KERN_INFO \"Booting paravirtualized kernel on %s\\n\"",
                    LogLevel::Info,
                    MessageCategory::Log
                ),
                expected(
                    "KERN_WARNING \"disk %s is slow\\n\"",
                    LogLevel::Warn,
                    MessageCategory::Log
                ),
                expected(
                    "LOG_ERR \"syslog style %s\\n\"",
                    LogLevel::Error,
                    MessageCategory::Log
                ),
                // `KERN_CONT` and `KERN_DEFAULT` are not levels, and neither is any other macro.
                expected(
                    "KERN_CONT \" and more\\n\"",
                    LogLevel::Unknown,
                    MessageCategory::Other
                ),
                expected(
                    "KERN_DEFAULT \"no level %s\\n\"",
                    LogLevel::Unknown,
                    MessageCategory::Other
                ),
                expected(
                    "PREFIX \"not a level %s\\n\"",
                    LogLevel::Unknown,
                    MessageCategory::Other
                ),
            ]
        );
    }

    #[test]
    fn test_prune_log_calls() {
        let codes = [
            CodeSource::from_string(
                Path::new("a.c"),
                r#"
int main(int argc, char *argv[]) {
    log_debug("first debug message %d", argc);
    syslog(LOG_ERR, "syslog error message");
    syslog(LOG_INFO, "syslog info message");
    printf("plain message\n");
    ws_debug("ws debug message");
    ws_info("ws info message");
    luaL_error(L, "lua error message");
}
"#,
            ),
            CodeSource::from_string(
                Path::new("b.c"),
                r#"
void dissect(void) {
    ws_warning("ws warn message");
    ws_warning(_("ws wrapped message"));
    dissect_error("dissect error message");
    dissect_error(LOG_ERR, "dissect syslog message");
    dissect_info("dissect info message");
}
"#,
            ),
        ];
        let mut tree = SourceTree {
            tree: SourceHierTree::from(Path::new("in-mem")),
            files_with_statements: HashMap::new(),
            file_name_to_sources: HashMap::new(),
            log_prefilter: OnceLock::new(),
            fallback_prefilter: OnceLock::new(),
            find_prefilter: OnceLock::new(),
            line_cache: RwLock::default(),
            files_by_name: RwLock::default(),
            learned_prefixes: RwLock::default(),
            log_calls: BTreeMap::new(),
            languages: BTreeSet::new(),
        };
        for sif in extract_logging(&codes, &ProgressTracker::new()) {
            tree.files_with_statements.insert(sif.id, sif);
        }
        // Pruning again, like after a file changes, starts over from the extracted levels.  The
        // statements are restored from their call names, so nothing else needs to be kept.
        tree.prune_log_calls();
        tree.prune_log_calls();
        assert_eq!(tree.languages, BTreeSet::from([SourceLanguage::C]));
        let found: Vec<(&str, Vec<(LogLevel, usize)>, Option<&str>, bool)> = tree
            .log_calls
            .iter()
            .map(|(name, log_call)| {
                (
                    name.as_str(),
                    log_call.levels.clone().into_iter().collect(),
                    log_call.family.as_deref(),
                    log_call.pruned,
                )
            })
            .collect();
        // `printf` has no level, so it is not identified as logging.  The `ws` family has two
        // levels other than `Info`, but `dissect` and `luaL` only have one.
        assert_eq!(
            found,
            vec![
                (
                    "dissect_error",
                    vec![(LogLevel::Error, 2)],
                    Some("dissect"),
                    true
                ),
                (
                    "dissect_info",
                    vec![(LogLevel::Info, 1)],
                    Some("dissect"),
                    true
                ),
                ("log_debug", vec![(LogLevel::Debug, 1)], None, false),
                (
                    "luaL_error",
                    vec![(LogLevel::Error, 1)],
                    Some("lua_l"),
                    true
                ),
                (
                    "syslog",
                    vec![(LogLevel::Info, 1), (LogLevel::Error, 1)],
                    None,
                    false
                ),
                ("ws_debug", vec![(LogLevel::Debug, 1)], Some("ws"), false),
                ("ws_info", vec![(LogLevel::Info, 1)], Some("ws"), false),
                ("ws_warning", vec![(LogLevel::Warn, 2)], Some("ws"), false),
            ]
        );
        let mut levels: Vec<(&str, LogLevel, MessageCategory)> = tree
            .files_with_statements
            .values()
            .flat_map(|sif| sif.statements())
            .map(|stmt| stmt.stmt)
            .map(|stmt| (stmt.text.as_str(), stmt.level, stmt.category))
            .collect();
        levels.sort();
        use MessageCategory::{Log, Other};
        assert_eq!(
            levels,
            vec![
                ("\"dissect error message\"", LogLevel::Unknown, Other),
                ("\"dissect info message\"", LogLevel::Unknown, Other),
                // The level from `LOG_ERR` is kept, although the family is pruned.
                ("\"dissect syslog message\"", LogLevel::Error, Log),
                ("\"first debug message %d\"", LogLevel::Debug, Log),
                ("\"lua error message\"", LogLevel::Unknown, Other),
                ("\"plain message\\n\"", LogLevel::Unknown, Other),
                ("\"syslog error message\"", LogLevel::Error, Log),
                ("\"syslog info message\"", LogLevel::Info, Log),
                ("\"ws debug message\"", LogLevel::Debug, Log),
                ("\"ws info message\"", LogLevel::Info, Log),
                ("\"ws warn message\"", LogLevel::Warn, Log),
                // A wrapped message is found for a family that is only known to be logging
                // after pruning.
                ("\"ws wrapped message\"", LogLevel::Warn, Log),
            ]
        );
    }

    #[test]
    fn test_categories_rust() {
        let code = CodeSource::from_string(
            Path::new("in-mem.rs"),
            r#"
#[derive(thiserror::Error, Debug)]
enum ConfigError {
    #[error("cannot read config {0}")]
    Read(String),
}

struct ParseError;

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "parse failed at {}", self.0)
    }
}

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "point ({}, {})", self.x, self.y)
    }
}

mod wire {
    impl<T> fmt::Display for super::FrameErr<T> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "bad frame {}", self.0)
        }
    }
}

fn main() -> Result<()> {
    info!("starting up");
    log!(lvl, "level variable message");
    println!("plain output {}", 1);
    writeln!(out, "written output {}", 2)?;
    let path = format!("dir {}", 3);
    let f = File::open(&path).context("failed to open file")?;
    let g = File::open(&path).with_context(|| format!("failed to open {}", path))?;
    let h = File::open(&path).map_err(|e| format!("cannot open {}: {}", path, e))?;
    let v = parse(&path).expect("parse must succeed");
    if v.is_empty() {
        bail!("no values in {}", path);
    }
    if v.len() > 10 {
        return Err(format!("too many values in {}", path));
    }
    panic!("unreachable state {}", 4);
    custom_macro!("custom message {}", 5);
}
"#,
        );
        let mut sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        prune_log_calls(sif.statements_for_pruning().collect());
        let found: Vec<(&str, Option<&str>, MessageCategory)> = sif
            .statements()
            .map(|stmt| stmt.stmt)
            .map(|stmt| (stmt.text.as_str(), stmt.call_name.as_deref(), stmt.category))
            .collect();
        use MessageCategory::*;
        assert_eq!(
            found,
            vec![
                // An attribute is not mistaken for the `error!` macro.
                ("\"cannot read config {0}\"", Some("#[error]"), Error),
                // A `Display` impl for an error type is an error message.
                ("\"parse failed at {}\"", Some("write"), Error),
                ("\"point ({}, {})\"", Some("write"), Format),
                ("\"bad frame {}\"", Some("write"), Error),
                ("\"starting up\"", Some("info"), Log),
                ("\"level variable message\"", Some("log"), Log),
                ("\"plain output {}\"", Some("println"), Other),
                ("\"written output {}\"", Some("writeln"), Other),
                ("\"dir {}\"", Some("format"), Format),
                ("\"failed to open file\"", Some("context"), Error),
                // A `format!` is named after the call that consumes the message.
                ("\"failed to open {}\"", Some("with_context"), Error),
                ("\"cannot open {}: {}\"", Some("map_err"), Error),
                ("\"parse must succeed\"", Some("expect"), Error),
                ("\"no values in {}\"", Some("bail"), Error),
                ("\"too many values in {}\"", Some("Err"), Error),
                ("\"unreachable state {}\"", Some("panic"), Error),
                ("\"custom message {}\"", Some("custom_macro"), Other),
            ]
        );
    }

    #[test]
    fn test_find_message_sources() {
        let code = CodeSource::from_string(
            Path::new("in-mem.rs"),
            r#"
#[derive(thiserror::Error, Debug)]
enum StoreError {
    #[error("cannot open store at {0}")]
    Open(String),
}

fn load(path: &str) -> Result<()> {
    let store = Store::open(path).context("failed to load the cache")?;
    warn!("Unable to read file: {}", err);
    eprintln!("tool: error: {}", e);
    let key = format!("{}/{}", dir, name);
}
"#,
        );
        let mut sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        prune_log_calls(sif.statements_for_pruning().collect());
        // The text of each source with the line of its best candidate, and its causes.
        fn summary(sources: &[MessageSource]) -> Vec<(String, Option<usize>, Vec<String>)> {
            sources
                .iter()
                .map(|source| {
                    (
                        source.text.clone(),
                        source.candidates.first().map(|stmt| stmt.line_no),
                        source
                            .causes
                            .iter()
                            .map(|cause| {
                                let line = cause.candidates.first().map(|stmt| stmt.line_no);
                                format!("{} @ {:?}", cause.text, line)
                            })
                            .collect(),
                    )
                })
                .collect()
        }
        let find = |message: &str| summary(&find_message_sources(sif.statements(), message));

        // The value in a log message is found in an error that was made somewhere else.
        assert_eq!(
            find("Unable to read file: cannot open store at /var/cache"),
            vec![(
                "Unable to read file: cannot open store at /var/cache".to_string(),
                Some(10),
                vec!["cannot open store at /var/cache @ Some(4)".to_string()],
            )]
        );
        // A chain of errors, like anyhow's `{:#}`, is split when no statement matches it all.
        // The formatted message has too little literal text to be a source.
        assert_eq!(
            find("failed to load the cache: Permission denied (os error 13)"),
            vec![
                ("failed to load the cache".to_string(), Some(9), vec![]),
                ("Permission denied (os error 13)".to_string(), None, vec![]),
            ]
        );
        // The message of an error that is printed by itself.
        assert_eq!(
            find("tool: error: failed to load the cache"),
            vec![(
                "tool: error: failed to load the cache".to_string(),
                Some(11),
                vec!["failed to load the cache @ Some(9)".to_string()],
            )]
        );
        assert_eq!(find("nothing like this"), vec![]);
    }

    #[test]
    fn test_find_message_fragments() {
        let code = CodeSource::from_string(
            Path::new("in-mem.rs"),
            r#"
fn load(path: &str) -> Result<()> {
    let store = Store::open(path).context("failed to load the cache")?;
    bail!("cannot open the settings file at {}", path);
    warn!("Unable to read file: {}", err);
    bail!("cannot open config.toml (read-only) at {}", path);
    warn!(" is not a valid value for option ");
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        // The text, line of the best candidate, and whether it is partial, for each source.
        let find = |message: &str| -> Vec<(String, Option<usize>, bool)> {
            find_message_sources(sif.statements(), message)
                .iter()
                .map(|source| {
                    (
                        source.text.clone(),
                        source.candidates.first().map(|stmt| stmt.line_no),
                        source.partial,
                    )
                })
                .collect()
        };

        // A message that was wrapped differently in a GUI.
        assert_eq!(
            find("cannot open the settings\n  file at /etc/app.toml"),
            vec![(
                "cannot open the settings file at /etc/app.toml".to_string(),
                Some(4),
                false
            )]
        );
        // A message with text put in front of it.
        assert_eq!(
            find("Error: failed to load the cache"),
            vec![
                ("Error".to_string(), None, false),
                ("failed to load the cache".to_string(), Some(3), false),
            ]
        );
        // Only part of a message was copied.
        assert_eq!(
            find("open the settings file"),
            vec![("open the settings file".to_string(), Some(4), true)]
        );
        // The end of one literal part and some of a value.
        assert_eq!(
            find("to read file: permission den"),
            vec![("to read file: permission den".to_string(), Some(5), true)]
        );
        // Text with characters that are special in a regex.
        assert_eq!(
            find("open config.toml (read-only)"),
            vec![("open config.toml (read-only)".to_string(), Some(6), true)]
        );
        assert_eq!(
            find("config.toml (read-only) at"),
            vec![("config.toml (read-only) at".to_string(), Some(6), true)]
        );
        // A message with values on both sides of a literal that ends with whitespace, whose
        // optional match is not part of the literal text.
        assert_eq!(
            find("“foolang” is not a valid value for option “/log/languages#”"),
            vec![(
                "“foolang” is not a valid value for option “/log/languages#”".to_string(),
                Some(7),
                true
            )]
        );
        // Too little in common.
        assert_eq!(find("the cache"), vec![]);
    }

    #[test]
    fn test_find_assembled_message() {
        let code = CodeSource::from_string(
            Path::new("in-mem.java"),
            r#"
class Meta {
    String procs(String schema) {
        StringBuilder sql = new StringBuilder("SELECT p.proname FROM pg_proc p WHERE p.oid > 0");
        if (schema != null) {
            sql.append(" AND n.nspname LIKE ?");
        }
        sql.append(" ORDER BY p.proname");
        return sql.toString();
    }
    String any(String table) {
        StringBuilder sql = new StringBuilder("SELECT " + table);
        sql.append(" AND n.nspname LIKE ?");
        return sql.toString();
    }
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let find = |message: &str| -> Vec<(String, Option<usize>)> {
            find_message_sources(sif.statements(), message)
                .iter()
                .map(|source| {
                    (
                        source.text.clone(),
                        source.candidates.first().map(|stmt| stmt.line_no),
                    )
                })
                .collect()
        };

        // The pieces are from the function that built the text, even though another function
        // has one of them and a generic statement matches all of it.
        assert_eq!(
            find("SELECT p.proname FROM pg_proc p WHERE p.oid > 0 AND n.nspname LIKE ? ORDER BY p.proname"),
            vec![
                (
                    "SELECT p.proname FROM pg_proc p WHERE p.oid > 0".to_string(),
                    Some(4)
                ),
                ("AND n.nspname LIKE ?".to_string(), Some(6)),
                ("ORDER BY p.proname".to_string(), Some(8)),
            ]
        );
        // The text between the pieces is from somewhere else, like the value of the
        // placeholder at the end of `"SELECT " + table`.
        assert_eq!(
            find("SELECT pg_class AND n.nspname LIKE ? AND x = 1"),
            vec![
                ("SELECT".to_string(), Some(12)),
                ("pg_class".to_string(), None),
                ("AND n.nspname LIKE ?".to_string(), Some(13)),
                ("AND x = 1".to_string(), None),
            ]
        );
    }

    #[test]
    fn test_find_message_sources_unknown_prefix() {
        let code = CodeSource::from_string(
            Path::new("in-mem.c"),
            r#"
void announce(struct device *dev, const char *a, const char *b, int m) {
    pr_info("%s strings: %s\n", a, b);
    dev_info(dev, "New USB device strings: Mfr=%d\n", m);
}
"#,
        );
        let mut sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        prune_log_calls(sif.statements_for_pruning().collect());
        let find = |message: &str| -> Vec<(String, Option<usize>)> {
            find_message_sources(sif.statements(), message)
                .iter()
                .map(|source| {
                    (
                        source.text.clone(),
                        source.candidates.first().map(|stmt| stmt.line_no),
                    )
                })
                .collect()
        };
        // The device name that `dev_info()` adds is not from a statement, but the generic
        // statement that matches all of the message must not hide the one for the rest of it.
        assert_eq!(
            find("usb 1-5: New USB device strings: Mfr=3"),
            vec![
                ("usb 1-5".to_string(), None),
                ("New USB device strings: Mfr=3".to_string(), Some(4)),
            ]
        );
        // The generic statement is still used when nothing explains more of the message.
        assert_eq!(
            find("foo: bar strings: baz"),
            vec![("foo: bar strings: baz".to_string(), Some(3))]
        );
    }

    #[test]
    fn test_find_message_sources_like_match() {
        let code = CodeSource::from_string(
            Path::new("in-mem.rs"),
            r#"
#[derive(thiserror::Error, Debug)]
enum StepError {
    #[error("error in {0}")]
    In(String),
}

fn run(a: &str, b: &str) {
    warn!("{}: {}", a, b);
    warn!("server ready{}", a);
    info!("server ready");
}
"#,
        );
        let mut sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        prune_log_calls(sif.statements_for_pruning().collect());
        let find = |message: &str| -> Vec<(String, Option<usize>)> {
            find_message_sources(sif.statements(), message)
                .iter()
                .map(|source| {
                    (
                        source.text.clone(),
                        source.candidates.first().map(|stmt| stmt.line_no),
                    )
                })
                .collect()
        };
        // A wrapper that only adds the separator does not hide the parts of a chain.
        assert_eq!(
            find("error in step0: error in step1: error in step2"),
            vec![
                ("error in step0".to_string(), Some(4)),
                ("error in step1".to_string(), Some(4)),
                ("error in step2".to_string(), Some(4)),
            ]
        );
        // The best statement is the one that matching a log line would choose, which does not
        // need an empty value.
        let line = "server ready";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        let matched = link_to_source(&log_ref, &sif).map(|stmt| stmt.line_no);
        assert_eq!(matched, Some(11));
        assert_eq!(find(line), vec![(line.to_string(), matched)]);
    }

    #[test]
    fn test_categories_python() {
        let code = CodeSource::from_string(
            Path::new("in-mem.py"),
            r#"
def load(path, count):
    logger.info("loading %s", path)
    logger.log(level, "level variable message")
    print("plain output", count)
    if count < 0:
        raise ValueError(f"negative count {count}")
    if count > 100:
        raise ConfigError("too many entries in {}".format(path)) from None
    if not path:
        raise RuntimeError("no path given for %s" % name)
    raise errors.LoadError("cannot load file")
"#,
        );
        let mut sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        prune_log_calls(sif.statements_for_pruning().collect());
        let found: Vec<(&str, Option<&str>, LogLevel, MessageCategory)> = sif
            .statements()
            .map(|stmt| stmt.stmt)
            .map(|stmt| {
                (
                    stmt.pattern().as_str(),
                    stmt.call_name.as_deref(),
                    stmt.level,
                    stmt.category,
                )
            })
            .collect();
        use MessageCategory::*;
        assert_eq!(
            found,
            vec![
                (
                    "(?s)^loading (.*)$",
                    Some("logger.info"),
                    LogLevel::Info,
                    Log
                ),
                (
                    "(?s)^level variable message$",
                    Some("logger.log"),
                    LogLevel::Unknown,
                    Log
                ),
                (
                    "(?s)^plain output$",
                    Some("print"),
                    LogLevel::Unknown,
                    Other
                ),
                (
                    "(?s)^negative count (.*)$",
                    Some("raise ValueError"),
                    LogLevel::Unknown,
                    Error
                ),
                (
                    "(?s)^too many entries in (.*)$",
                    Some("raise ConfigError"),
                    LogLevel::Unknown,
                    Error
                ),
                (
                    "(?s)^no path given for (.*)$",
                    Some("raise RuntimeError"),
                    LogLevel::Unknown,
                    Error
                ),
                (
                    "(?s)^cannot load file$",
                    Some("raise errors.LoadError"),
                    LogLevel::Unknown,
                    Error
                ),
            ]
        );
    }

    #[test]
    fn test_categories_java() {
        let code = CodeSource::from_string(
            Path::new("Loader.java"),
            r#"
class Loader {
    void load(String path, int count) throws IOException {
        log.info("loading {}", path);
        if (count < 0) {
            throw new IllegalArgumentException("negative count " + count);
        }
        if (count > 100) {
            throw new IOException(String.format("too many entries in %s", path));
        }
        throw new java.io.UncheckedIOException("cannot load file", cause);
    }
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let found: Vec<(&str, Option<&str>, LogLevel, MessageCategory)> = src_refs
            .iter()
            .map(|stmt| {
                (
                    stmt.pattern().as_str(),
                    stmt.call_name.as_deref(),
                    stmt.level,
                    stmt.category,
                )
            })
            .collect();
        use MessageCategory::*;
        assert_eq!(
            found,
            vec![
                ("(?s)^loading (.*)$", Some("info"), LogLevel::Info, Log),
                (
                    "(?s)^negative count (.*)$",
                    Some("throw IllegalArgumentException"),
                    LogLevel::Unknown,
                    Error
                ),
                (
                    "(?s)^too many entries in (.*)$",
                    Some("throw IOException"),
                    LogLevel::Unknown,
                    Error
                ),
                (
                    "(?s)^cannot load file$",
                    Some("throw java.io.UncheckedIOException"),
                    LogLevel::Unknown,
                    Error
                ),
            ]
        );
    }

    #[test]
    fn test_categories_cpp() {
        let code = CodeSource::from_string(
            Path::new("in-mem.cc"),
            r#"
void load(const std::string &path, int count) {
    LOG_INFO("loading %s", path.c_str());
    printf("plain output %d\n", count);
    snprintf(buf, sizeof(buf), "%s/cache-%d", path.c_str(), count);
    report(fmt::format("cannot parse {}", path));
    if (count < 0) {
        throw std::runtime_error("negative count");
    }
    if (count > 100) {
        throw ConfigError(fmt::format("too many entries in {}", path));
    }
    g_set_error(error, G_IO_ERROR, G_IO_ERROR_FAILED, "Failed to open %s", path.c_str());
}
"#,
        );
        let mut sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        prune_log_calls(sif.statements_for_pruning().collect());
        let found: Vec<(&str, Option<&str>, MessageCategory)> = sif
            .statements()
            .map(|stmt| stmt.stmt)
            .map(|stmt| (stmt.text.as_str(), stmt.call_name.as_deref(), stmt.category))
            .collect();
        use MessageCategory::*;
        assert_eq!(
            found,
            vec![
                ("\"loading %s\"", Some("LOG_INFO"), Log),
                ("\"plain output %d\\n\"", Some("printf"), Other),
                ("\"%s/cache-%d\"", Some("snprintf"), Format),
                ("\"cannot parse {}\"", Some("fmt::format"), Format),
                (
                    "\"negative count\"",
                    Some("throw std::runtime_error"),
                    Error
                ),
                (
                    "\"too many entries in {}\"",
                    Some("throw ConfigError"),
                    Error
                ),
                ("\"Failed to open %s\"", Some("g_set_error"), Error),
            ]
        );
    }

    #[test]
    fn test_categories_cpp_translated() {
        let code = CodeSource::from_string(
            Path::new("in-mem.cc"),
            r#"
void load(const char *path, int count) {
    snprintf(buf, sizeof(buf), _("Could not open the file %s"), path);
    g_strdup_printf(_("Cannot load the profile %s"), path);
    g_set_error(error, G_IO_ERROR, G_IO_ERROR_FAILED, _("Failed to read the file %s"), path);
    throw std::runtime_error(_("bad configuration value"));
    label->setText(tr("not a message"));
}
"#,
        );
        let mut sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        prune_log_calls(sif.statements_for_pruning().collect());
        let found: Vec<(&str, Option<&str>, MessageCategory)> = sif
            .statements()
            .map(|stmt| stmt.stmt)
            .map(|stmt| {
                (
                    stmt.pattern().as_str(),
                    stmt.call_name.as_deref(),
                    stmt.category,
                )
            })
            .collect();
        use MessageCategory::*;
        // A translated message is kept for a call that formats or makes an error, but not
        // for other calls.
        assert_eq!(
            found,
            vec![
                (
                    "(?s)^Could not open the file (.*)$",
                    Some("snprintf"),
                    Format
                ),
                (
                    "(?s)^Cannot load the profile (.*)$",
                    Some("g_strdup_printf"),
                    Format
                ),
                (
                    "(?s)^Failed to read the file (.*)$",
                    Some("g_set_error"),
                    Error
                ),
                (
                    "(?s)^bad configuration value$",
                    Some("throw std::runtime_error"),
                    Error
                ),
            ]
        );
        assert_eq!(sif.statements().next().unwrap().vars, vec!["path"]);
    }

    #[test]
    fn test_format_consumers() {
        let code = CodeSource::from_string(
            Path::new("in-mem.rs"),
            r#"
fn check(p: &str) -> Result<()> {
    names.push(format!("failed to open the file {}", p));
    let path = PathBuf::from(format!("{}/sessions/{}.db", root, p));
    let f = File::open(p).with_context(|| format!("cannot read {}", p))?;
    bail!("failed to open the file {}", p);
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        let found: Vec<(usize, Option<&str>, MessageCategory)> = src_refs
            .iter()
            .map(|stmt| (stmt.line_no, stmt.call_name.as_deref(), stmt.category))
            .collect();
        // Only a `format!` passed to an error call is named after that call.
        assert_eq!(
            found,
            vec![
                (3, Some("format"), MessageCategory::Format),
                (4, Some("format"), MessageCategory::Format),
                (5, Some("with_context"), MessageCategory::Error),
                (6, Some("bail"), MessageCategory::Error),
            ]
        );
        let line = "failed to open the file /x";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        assert_eq!(
            link_to_source(&log_ref, &sif).map(|src_ref| src_ref.line_no),
            Some(6)
        );
    }

    #[test]
    fn test_alnum_beats_punctuation() {
        let code = CodeSource::from_string(
            Path::new("in-mem.rs"),
            r#"
fn main() {
    info!("{}: {} [{}] ({})", a, b, c, d);
    info!("Done{}", rest);
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let line = "Done: x [y] (z)";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        // Both match, but the one with text wins over the one with more punctuation.
        assert_eq!(
            link_to_source(&log_ref, &sif).map(|src_ref| src_ref.line_no),
            Some(4)
        );
    }

    #[test]
    fn test_fallback_quality() {
        let code = CodeSource::from_string(
            Path::new("in-mem.rs"),
            r#"
fn main() {
    let a = format!("{}/{}", dir, name);
    let b = format!("ready: {}", name);
    let c = format!("[{}] <{}> ({})", x, y, z);
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let best = |line: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
            link_to_source(&log_ref, &sif).map(|src_ref| src_ref.line_no)
        };
        // Too little literal text to match a log message unless it is a log statement.
        assert_eq!(best("usr/bin"), None);
        assert_eq!(best("ready: now"), Some(4));
        // Enough punctuation, but no text.
        assert_eq!(best("[a] <b> (c)"), None);
    }

    #[test]
    fn test_match_prefers_log_category() {
        let code = CodeSource::from_string(
            Path::new("a.c"),
            r#"
int main(int argc, char *argv[]) {
    luaL_error(L, "cannot open file %s", argv[0]);
    log_warn("cannot open %s", argv[0]);
    luaL_error(L, "cannot parse %s", argv[0]);
    log_warn("server ready%s", argv[0]);
    luaL_error(L, "server ready");
}
"#,
        );
        let mut tree = SourceTree {
            tree: SourceHierTree::from(Path::new("in-mem")),
            files_with_statements: HashMap::new(),
            file_name_to_sources: HashMap::new(),
            log_prefilter: OnceLock::new(),
            fallback_prefilter: OnceLock::new(),
            find_prefilter: OnceLock::new(),
            line_cache: RwLock::default(),
            files_by_name: RwLock::default(),
            learned_prefixes: RwLock::default(),
            log_calls: BTreeMap::new(),
            languages: BTreeSet::new(),
        };
        for sif in extract_logging(&[code], &ProgressTracker::new()) {
            tree.files_with_statements.insert(sif.id, sif);
        }
        tree.prune_log_calls();
        tree.rebuild_prefilter();
        let best_with = |line: &str, fallback: bool| {
            let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
            tree.find_best_match(&log_ref, fallback)
                .map(|(src_ref, _)| (src_ref.line_no, src_ref.category))
        };
        let best = |line: &str| best_with(line, true);
        // The `luaL` family is pruned, so the log statement wins although the other one has
        // more literal text.
        assert_eq!(
            best("cannot open file foo"),
            Some((4, MessageCategory::Log))
        );
        // The other categories are still matched when no log statement does.
        assert_eq!(best("cannot parse foo"), Some((5, MessageCategory::Other)));
        // A log statement is used even if it only matches with an empty value and the other
        // statement matches without one.
        assert_eq!(best("server ready"), Some((6, MessageCategory::Log)));
        // Without the fallback, only the logging calls are used.
        assert_eq!(best_with("cannot parse foo", false), None);
        assert_eq!(
            best_with("cannot open file foo", false),
            Some((4, MessageCategory::Log))
        );
    }

    #[test]
    fn test_prefilter_single_byte_literals() {
        let code = CodeSource::from_string(
            &PathBuf::from("in-mem.c"),
            r#"
void f(const char *key, int value) {
    log_info("%s=%d", key, value);
    log_info("%s: %d", key, value);
}
"#,
        );
        let mut tree = SourceTree {
            tree: SourceHierTree::from(Path::new("in-mem")),
            files_with_statements: HashMap::new(),
            file_name_to_sources: HashMap::new(),
            log_prefilter: OnceLock::new(),
            fallback_prefilter: OnceLock::new(),
            find_prefilter: OnceLock::new(),
            line_cache: RwLock::default(),
            files_by_name: RwLock::default(),
            learned_prefixes: RwLock::default(),
            log_calls: BTreeMap::new(),
            languages: BTreeSet::new(),
        };
        for sif in extract_logging(&[code], &ProgressTracker::new()) {
            tree.files_with_statements.insert(sif.id, sif);
        }
        tree.rebuild_prefilter();
        let candidates_in = |prefilter: &Prefilter, line: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
            tree.prefiltered_candidates(prefilter, &log_ref, line)
                .into_iter()
                .map(|(_, stmt)| stmt.line_no)
                .sorted()
                .collect::<Vec<_>>()
        };
        let candidates = |line: &str| candidates_in(tree.log_prefilter(), line);
        // The literal of the first statement is a single byte, which is looked up by byte
        // instead of in the automaton.
        assert_eq!(candidates("a=1"), vec![3]);
        assert_eq!(candidates("a: 1"), vec![4]);
        assert_eq!(candidates("a=b: 1="), vec![3, 4]);
        assert!(candidates("nothing").is_empty());
        // Neither has enough literal text to explain a part of a message.
        assert!(candidates_in(tree.find_prefilter(), "a=b: 1=").is_empty());
    }

    #[test]
    fn test_levels_rust() {
        let levels = extract_levels(
            "in-mem.rs",
            r#"
fn main() {
    trace!("trace message");
    debug!("debug message");
    info!("info message");
    log::warn!("warn message");
    tracing::error!("error message");
    println!("plain message");
    log::log!(Level::Warn, "log macro message");
    tracing::event!(tracing::Level::INFO, "event macro message");
    log!(lvl, "level variable message");
    log!(target: "app", "target message");
}
"#,
        );
        assert_eq!(
            levels,
            vec![
                ("\"trace message\"".to_string(), LogLevel::Trace),
                ("\"debug message\"".to_string(), LogLevel::Debug),
                ("\"info message\"".to_string(), LogLevel::Info),
                ("\"warn message\"".to_string(), LogLevel::Warn),
                ("\"error message\"".to_string(), LogLevel::Error),
                ("\"plain message\"".to_string(), LogLevel::Unknown),
                ("\"log macro message\"".to_string(), LogLevel::Warn),
                ("\"event macro message\"".to_string(), LogLevel::Info),
                ("\"level variable message\"".to_string(), LogLevel::Unknown),
            ]
        );
    }

    #[test]
    fn test_levels_java() {
        let levels = extract_levels(
            "in-mem.java",
            r#"
class Main {
    void run() {
        LOG.trace("trace message");
        log.debug("debug message");
        logger.info("info message");
        LOGGER.warn("warn message");
        LOG.error("error message");
        log.severe("severe message");
        LOG.fatal("fatal message");
        log.finest("finest message");
        log.log(Level.WARNING, "level arg message");
    }
}
"#,
        );
        assert_eq!(
            levels,
            vec![
                ("\"trace message\"".to_string(), LogLevel::Trace),
                ("\"debug message\"".to_string(), LogLevel::Debug),
                ("\"info message\"".to_string(), LogLevel::Info),
                ("\"warn message\"".to_string(), LogLevel::Warn),
                ("\"error message\"".to_string(), LogLevel::Error),
                ("\"severe message\"".to_string(), LogLevel::Error),
                ("\"fatal message\"".to_string(), LogLevel::Fatal),
                ("\"finest message\"".to_string(), LogLevel::Trace),
                ("\"level arg message\"".to_string(), LogLevel::Warn),
            ]
        );
    }

    #[test]
    fn test_levels_cpp() {
        let levels = extract_levels(
            "in-mem.cc",
            r#"
int main(int argc, char* argv[]) {
    spdlog::info("info message");
    logger->warn("warn message");
    SPDLOG_ERROR("error message");
    spdlog::critical("critical message");
    log_debug("lnav debug message");
    log_warning("lnav warn message");
    log_warn_once("suffix warn message");
    logger.warning_once("qualified suffix message");
    on_error_log("not a suffix log message");
    syslog(LOG_ERR, "syslog error message");
    spdlog::log(spdlog::level::trace, "spdlog trace message");
    report_error("not a log message");
    printf("plain message");
    log_info("conn error", "second message");
    logger->info(err, "variable arg message");
    logInfo("camel message");
    errors.error("not a log message either");
    qWarning("qt warn message");
    qCritical("qt critical message");
    g_message("glib message");
    g_warning("glib warn message");
    q_tool("not a qt log message");
    on_error("not a log message handler");
    x_y_debug("single letter prefix message");
}
"#,
        );
        assert_eq!(
            levels,
            vec![
                ("\"info message\"".to_string(), LogLevel::Info),
                ("\"warn message\"".to_string(), LogLevel::Warn),
                ("\"error message\"".to_string(), LogLevel::Error),
                ("\"critical message\"".to_string(), LogLevel::Fatal),
                ("\"lnav debug message\"".to_string(), LogLevel::Debug),
                ("\"lnav warn message\"".to_string(), LogLevel::Warn),
                ("\"suffix warn message\"".to_string(), LogLevel::Warn),
                ("\"qualified suffix message\"".to_string(), LogLevel::Warn),
                (
                    "\"not a suffix log message\"".to_string(),
                    LogLevel::Unknown
                ),
                ("\"syslog error message\"".to_string(), LogLevel::Error),
                ("\"spdlog trace message\"".to_string(), LogLevel::Trace),
                ("\"not a log message\"".to_string(), LogLevel::Unknown),
                ("\"plain message\"".to_string(), LogLevel::Unknown),
                ("\"conn error\"".to_string(), LogLevel::Info),
                ("\"second message\"".to_string(), LogLevel::Info),
                ("\"variable arg message\"".to_string(), LogLevel::Info),
                ("\"camel message\"".to_string(), LogLevel::Info),
                (
                    "\"not a log message either\"".to_string(),
                    LogLevel::Unknown
                ),
                ("\"qt warn message\"".to_string(), LogLevel::Warn),
                ("\"qt critical message\"".to_string(), LogLevel::Fatal),
                ("\"glib message\"".to_string(), LogLevel::Info),
                ("\"glib warn message\"".to_string(), LogLevel::Warn),
                ("\"not a qt log message\"".to_string(), LogLevel::Unknown),
                (
                    "\"not a log message handler\"".to_string(),
                    LogLevel::Unknown
                ),
                (
                    "\"single letter prefix message\"".to_string(),
                    LogLevel::Debug
                ),
            ]
        );
    }

    #[test]
    fn test_levels_python() {
        let levels = extract_levels(
            "in-mem.py",
            r#"
def main():
    logger.debug("debug message")
    logging.info("info message")
    logger.warning("warn message")
    self.log.error("error message")
    logger.exception("exception message")
    logger.critical("critical message")
    print("plain message")
    warnings.warn("deprecated message")
    parser.error("bad arg message")
    logger.log(logging.WARNING, "level arg message")
    logging.log(level, "level variable message")
"#,
        );
        assert_eq!(
            levels,
            vec![
                ("\"debug message\"".to_string(), LogLevel::Debug),
                ("\"info message\"".to_string(), LogLevel::Info),
                ("\"warn message\"".to_string(), LogLevel::Warn),
                ("\"error message\"".to_string(), LogLevel::Error),
                ("\"exception message\"".to_string(), LogLevel::Error),
                ("\"critical message\"".to_string(), LogLevel::Fatal),
                ("\"plain message\"".to_string(), LogLevel::Unknown),
                ("\"deprecated message\"".to_string(), LogLevel::Unknown),
                ("\"bad arg message\"".to_string(), LogLevel::Unknown),
                ("\"level arg message\"".to_string(), LogLevel::Warn),
                ("\"level variable message\"".to_string(), LogLevel::Unknown),
            ]
        );
    }

    #[test]
    fn test_link_to_source_by_level() {
        let code = CodeSource::from_string(
            Path::new("in-mem.rs"),
            r#"
fn main() {
    debug!("retry");
    warn!("retry");
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let log_format: LogFormat = r"^(?<level>\w+) (?<body>.*)$".try_into().unwrap();
        for (line, expected) in [
            ("DEBUG retry", LogLevel::Debug),
            ("WARN retry", LogLevel::Warn),
        ] {
            let log_ref =
                LogRefBuilder::new().build_from_captures(log_format.captures(line).unwrap(), line);
            let result = link_to_source(&log_ref, &sif).unwrap();
            assert_eq!(result.level, expected, "{line}");
        }
    }

    #[test]
    fn test_with_log_level() {
        let code = CodeSource::from_string(
            Path::new("in-mem.rs"),
            r#"
fn main() {
    debug!("retry");
    warn!("retry");
}
"#,
        );
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        for level in [LogLevel::Debug, LogLevel::Warn] {
            let log_ref = LogRefBuilder::new()
                .with_log_level(Some(level))
                .with_body(Some("retry"))
                .build("retry");
            assert_eq!(log_ref.level(), Some(level));
            let result = link_to_source(&log_ref, &sif).unwrap();
            assert_eq!(result.level, level);
        }
        let log_ref = LogRefBuilder::new()
            .with_log_level(Some(LogLevel::Unknown))
            .build("retry");
        assert_eq!(log_ref.level(), None);
    }

    const TRACE: &str = r#"JvmPauseMonitor-n0: Started
java.lang.IllegalStateException: simulated failure for demo
    at org.example.Main.simulateError(Main.java:50)
    at org.example.Main.main(Main.java:41)
    at org.codehaus.mojo.exec.ExecJavaMojo$1.run(ExecJavaMojo.java:279)
    at java.base/java.lang.Thread.run(Thread.java:1447)
"#;

    #[test]
    fn test_backtrace_re() {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.java"), TEST_PUNC_SRC);
        let log_ref = LogRefBuilder::new().with_body(Some(TRACE)).build(TRACE);
        assert_snapshot!(log_ref.line);
        assert_yaml_snapshot!(log_ref);
        let sif = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap();
        let src_refs = &sif.log_statements;
        assert_yaml_snapshot!(sif.statements().collect::<Vec<_>>());
        let vars = extract_variables(&log_ref, &src_refs[0]);
        assert_yaml_snapshot!(vars);
    }

    fn find_file_matcher() -> (tempfile::TempDir, LogMatcher) {
        let dir = tempfile::tempdir().unwrap();
        for rel in [
            "cmd/server/main.go",
            "src/main/java/com/foo/Bar.java",
            "src/main/java/com/other/Bar.java",
            "src/main/kotlin/com/MyCo/app/UserId.kt",
        ] {
            let path = dir.path().join(rel);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, "class Bar {}\n").unwrap();
        }
        let mut log_matcher = LogMatcher::new();
        log_matcher.add_root(dir.path()).unwrap();
        assert!(log_matcher
            .discover_sources(&ProgressTracker::new())
            .is_empty());
        (dir, log_matcher)
    }

    #[test]
    fn test_find_file() {
        let (dir, log_matcher) = find_file_matcher();
        let root = dir.path().canonicalize().unwrap();
        let canon = |path: Option<PathBuf>| path.map(|path| path.canonicalize().unwrap());
        let main_go = Some(root.join("cmd/server/main.go"));

        // Files in languages that are not scanned for log statements are found too.
        assert_eq!(
            canon(log_matcher.find_file(Path::new("cmd/server/main.go"))),
            main_go
        );
        assert_eq!(
            canon(log_matcher.find_file(Path::new("./cmd/server/main.go"))),
            main_go
        );
        // An absolute path from another machine is matched by its suffix.
        assert_eq!(
            canon(log_matcher.find_file(Path::new("/build/agent/work/cmd/server/main.go"))),
            main_go
        );
        assert_eq!(
            log_matcher.find_file(Path::new("cmd/server/missing.go")),
            None
        );

        let foo_bar = Some(root.join("src/main/java/com/foo/Bar.java"));
        // The longest matching suffix wins.
        assert_eq!(
            canon(log_matcher.find_file(Path::new("x/foo/Bar.java"))),
            foo_bar
        );
        // Both Bar.java files match only by name, so it is ambiguous.
        assert_eq!(log_matcher.find_file(Path::new("com/zzz/Bar.java")), None);
        // A bare name is matched completely by both, so the first one is picked.
        assert_eq!(canon(log_matcher.find_file(Path::new("Bar.java"))), foo_bar);

        // A relative path's directories say where the file is: the only main.go is in another
        // directory, so it isn't this one.
        assert_eq!(log_matcher.find_file(Path::new("net/other/main.go")), None);
        // An absolute path from another machine can fall back to the file name alone.
        assert_eq!(
            canon(log_matcher.find_file(Path::new("/build/agent/main.go"))),
            main_go
        );
        // A Windows path, as in a .NET trace.
        assert_eq!(
            canon(log_matcher.find_file(Path::new(r"C:\build\agent\cmd\server\main.go"))),
            main_go
        );
        assert_eq!(
            canon(log_matcher.find_file(Path::new(r"cmd\server\main.go"))),
            main_go
        );
    }

    #[test]
    fn test_from_windows_path() {
        let cases = [
            (r"C:\build\agent\main.go", Some("/build/agent/main.go")),
            (r"c:\src\App\Program.cs", Some("/src/App/Program.cs")),
            (r"C:\", Some("/")),
            (r"cmd\server\main.go", Some("cmd/server/main.go")),
            (r"\\server\share\App.cs", Some("//server/share/App.cs")),
            // Not Windows paths, so they are left alone.
            ("cmd/server/main.go", None),
            (r"C:\build/agent\main.go", None),
            ("main.go", None),
            ("C:", None),
        ];
        for (input, expected) in cases {
            assert_eq!(
                LogMatcher::from_windows_path(Path::new(input)),
                expected.map(PathBuf::from),
                "input: {input}"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn test_from_windows_path_not_utf8() {
        use std::os::unix::ffi::OsStrExt;

        let path = Path::new(std::ffi::OsStr::from_bytes(b"C:\\build\\\xff.go"));
        assert_eq!(LogMatcher::from_windows_path(path), None);
    }

    const PYTHON_TRACE: &str = r#"\
Traceback (most recent call last):
  File "python-logging-example/python_logging_example/__main__.py", line 26, in main
    helper.fail_now()
    ~~~~~~~~~~~~~~~^^
  File "python-logging-example/python_logging_example/helper.py", line 3, in fail_now
    return 1 / 0
           ~~^~~
ZeroDivisionError: division by zero
"#;

    #[test]
    fn test_trace_start() {
        fn body(text: &str) -> Option<&str> {
            LogRefBuilder::new()
                .with_body(Some(text))
                .build(text)
                .details
                .and_then(|details| details.body)
        }
        assert_eq!(body(TRACE), Some("JvmPauseMonitor-n0: Started"));
        assert_eq!(
            body(&format!(
                "Failed to divide\n{}",
                PYTHON_TRACE.trim_start_matches("\\\n")
            )),
            Some("Failed to divide")
        );
        // The trace can be all of the message, like for `log.error("", e)`.
        assert_eq!(body(PYTHON_TRACE.trim_start_matches("\\\n")), Some(""));
        // A chain of causes, with tabs.
        assert_eq!(
            body("Request failed\nWrapperException: outer\n\tat a.B.c(B.java:1)\nCaused by: java.io.IOException: inner\n\tat d.E.f(E.java:2)\n"),
            Some("Request failed")
        );
        // Without a frame after it, an exception's name is just part of the message.
        assert_eq!(
            body("ConnectionError: timeout"),
            Some("ConnectionError: timeout")
        );
        assert_eq!(
            body("Retrying\nConnectionError: timeout"),
            Some("Retrying\nConnectionError: timeout")
        );
        // A frame needs an exception in front of it.
        assert_eq!(
            body("Steps:\n  at home\n  at work"),
            Some("Steps:\n  at home\n  at work")
        );
    }
}
