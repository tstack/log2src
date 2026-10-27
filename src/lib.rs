use directories::ProjectDirs;
use indicatif::HumanBytes;
use itertools::Itertools;
use miette::Diagnostic;
use rayon::prelude::*;
use regex::{Captures, Regex};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::ffi::OsStr;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Seek, Write};
use std::ops::{Deref, Range};
use std::path::{Component, Path, PathBuf};
use std::sync::{Arc, LazyLock, PoisonError, RwLock};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{fs, io};
use tempfile::NamedTempFile;
use thiserror::Error;
use tree_sitter::Language;

mod code_source;
mod java_symbols;
mod log_format;
mod message_source;
mod prefilter;
mod progress;
mod source_hier;
mod source_query;
mod source_ref;
mod value_kind;

// TODO: doesn't need to be exposed if we can clean up the arguments to do_mapping
use crate::java_symbols::{JavaSymbols, MessageRef, StringConstant};
use crate::prefilter::{Prefilter, StatementID};
use crate::progress::{ProgressReader, WorkGuard};
use crate::source_hier::{ScanEvent, SourceFileID, SourceHierContent, SourceHierTree};
use crate::source_ref::{CallSite, FormatArgument};
use crate::value_kind::SplitOrder;
pub use code_source::CodeSource;
pub use log_format::LogFormat;
pub use message_source::{find_message_sources, MessageSource};
pub use progress::ProgressTracker;
pub use progress::ProgressUpdate;
pub use progress::WorkInfo;
use source_query::QueryResult;
pub use source_query::SourceQuery;
pub use source_ref::{LogLevel, MessageCategory, SourceRef};

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
    #[serde(rename = "35")]
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

/// Collection of log statements in a single source file
#[derive(Debug, Serialize, Deserialize)]
pub struct StatementsInFile {
    pub path: String,
    id: SourceFileID,
    /// The statements with a string-literal message.  Use `statements()` to also get the ones
    /// whose message is a constant.
    log_statements: Vec<SourceRef>,
    /// The locations, as line and column, of the statements whose level comes from an
    /// argument, like `syslog(LOG_ERR, ...)`, instead of the name of the call.  Those levels
    /// are never pruned by `prune_log_calls()`.
    arg_levels: BTreeSet<(usize, usize)>,
    /// The statements whose message is a constant.  The constants are usually defined in other
    /// files, so these are rebuilt by `SourceTree::resolve_message_refs()` instead of cached.
    #[serde(skip)]
    resolved_statements: Vec<SourceRef>,
    /// The Java string constants defined in this file.
    constants: Vec<StringConstant>,
    /// The Java log calls in this file whose message is a constant.
    message_refs: Vec<MessageRef>,
}

impl StatementsInFile {
    /// Iterate over all of the statements, paired with whether their level came from an
    /// argument, for `prune_log_calls()`.
    fn statements_for_pruning(&mut self) -> impl Iterator<Item = (&mut SourceRef, bool)> {
        let arg_levels = &self.arg_levels;
        self.log_statements
            .iter_mut()
            .chain(self.resolved_statements.iter_mut())
            .map(move |stmt| {
                let from_arg = arg_levels.contains(&(stmt.line_no, stmt.column));
                (stmt, from_arg)
            })
    }

    /// Iterate over all of the statements, the ones with a string-literal message first.
    pub fn statements(&self) -> impl Iterator<Item = &SourceRef> {
        self.log_statements
            .iter()
            .chain(self.resolved_statements.iter())
    }

    /// Get a statement by its index in `statements()`.
    fn statement(&self, index: usize) -> Option<&SourceRef> {
        match index.checked_sub(self.log_statements.len()) {
            None => self.log_statements.get(index),
            Some(resolved_index) => self.resolved_statements.get(resolved_index),
        }
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
    /// Finds the candidate statements for a log message, rebuilt after loading/extracting.
    #[serde(skip)]
    prefilter: Option<Prefilter>,
    /// The statements that matched log messages with a given file name and line number.  They
    /// are tried before the prefilter when another message has the same file and line.  Cleared
    /// whenever the statements change.
    #[serde(skip)]
    line_cache: RwLock<LineCache>,
    /// The logging functions/macros/methods called by the statements under this root, keyed by
    /// the name of the call.  Rebuilt after loading/extracting.
    #[serde(skip)]
    pub log_calls: BTreeMap<String, LogCall>,
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
fn prune_log_calls(mut stmts: Vec<(&mut SourceRef, bool)>) -> BTreeMap<String, LogCall> {
    // The level from the name of each call, which only needs to be computed once per name.
    let mut name_levels: HashMap<String, Option<LogLevel>> = HashMap::new();
    let mut log_calls: BTreeMap<String, LogCall> = BTreeMap::new();
    for (stmt, from_arg) in stmts.iter_mut() {
        let Some(call_name) = stmt.call_name.as_deref() else {
            continue;
        };
        if MessageCategory::from_call(stmt).is_some() {
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
    for (stmt, from_arg) in stmts.iter_mut() {
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
            stmt.category = MessageCategory::classify(stmt);
        }
    }
    log_calls
}

/// Maps a file name and line number from a log message to the statements that matched it.
type LineCache = HashMap<String, HashMap<usize, Vec<StatementID>>>;

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
                match SourceRef::from_message_ref(&sif.path, message_ref, value) {
                    Some(src_ref) => {
                        sif.resolved_statements.push(src_ref);
                        summary.resolved += 1;
                    }
                    None => summary.no_text += 1,
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
    }

    fn rebuild_prefilter(&mut self) {
        self.prefilter = Some(Prefilter::new(self.files_with_statements.values()));
        // The statement IDs in the cache may now refer to different statements.
        self.line_cache
            .get_mut()
            .unwrap_or_else(PoisonError::into_inner)
            .clear();
    }

    /// The line cache key for a log message, if it has a file name and line number and the
    /// file name refers to a single source file.  Messages for file names shared by several
    /// source files are not cached, since a statement in one could hide a better match in another.
    fn line_cache_key<'a>(&self, log_ref: &LogRef<'a>) -> Option<(&'a str, usize)> {
        let (filename, lineno) = log_ref.file_and_line()?;
        match self.file_name_to_sources.get(filename) {
            Some(ids) if ids.len() == 1 => Some((filename, lineno)),
            _ => None,
        }
    }

    /// Find the highest quality statement that previously matched a log message with the same
    /// file name and line number as this one, and matches this one too.
    fn find_cached_match(&self, log_ref: &LogRef) -> Option<&SourceRef> {
        let (filename, lineno) = self.line_cache_key(log_ref)?;
        let body = log_ref.body();
        let cache = self
            .line_cache
            .read()
            .unwrap_or_else(PoisonError::into_inner);
        let candidates = cache
            .get(filename)?
            .get(&lineno)?
            .iter()
            .filter_map(|(file_id, index)| {
                self.files_with_statements.get(file_id)?.statement(*index)
            })
            .sorted_by(|lhs, rhs| compare_candidates(lhs, rhs, Some(lineno), log_ref.level()));
        first_match(candidates, body, Some(lineno), |src_ref| src_ref)
    }

    /// Find the highest quality statement that matches the given log message, preferring the one
    /// closest to the message's line number for a tie.  If the message has a file name and line
    /// number, the statement is added to the cache for them.
    fn find_best_match(&self, log_ref: &LogRef) -> Option<&SourceRef> {
        let prefilter = self.prefilter.as_ref()?;
        let body = log_ref.body();
        let filename = match log_ref.details {
            Some(LogDetails {
                file: Some(filename),
                ..
            }) => Some(filename),
            _ => None,
        };
        let file_ids = filename.and_then(|name| self.file_name_to_sources.get(name));
        let mut candidates: Vec<(StatementID, &SourceRef)> = Vec::new();
        prefilter.candidates(body, |(file_id, index)| {
            let Some(sif) = self.files_with_statements.get(&file_id) else {
                return;
            };
            let in_file = match (filename, file_ids) {
                (None, _) => true,
                (Some(_), Some(ids)) => ids.contains(&file_id),
                (Some(name), None) => sif.path.contains(name),
            };
            if in_file {
                candidates.extend(sif.statement(index).map(|stmt| ((file_id, index), stmt)));
            }
        });
        let lineno = log_ref.details.as_ref().and_then(|details| details.lineno);
        let level = log_ref.level();
        candidates.sort_by(|lhs, rhs| compare_candidates(lhs.1, rhs.1, lineno, level));
        let (stmt_id, src_ref) = first_match(candidates, body, lineno, |(_, src_ref)| src_ref)?;
        if let Some((filename, lineno)) = self.line_cache_key(log_ref) {
            let mut cache = self
                .line_cache
                .write()
                .unwrap_or_else(PoisonError::into_inner);
            let ids = cache
                .entry(filename.to_string())
                .or_default()
                .entry(lineno)
                .or_default();
            if !ids.contains(&stmt_id) {
                ids.push(stmt_id);
            }
        }
        Some(src_ref)
    }
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
    src_ref: impl Fn(&T) -> &'a SourceRef,
) -> Option<T> {
    let mut with_empty_value: Option<T> = None;
    for candidate in candidates {
        let stmt = src_ref(&candidate);
        if with_empty_value.as_ref().is_some_and(|prior| {
            src_ref(prior).category.match_priority() < stmt.category.match_priority()
        }) {
            break;
        }
        if stmt.category != MessageCategory::Log && stmt.quality < MIN_FALLBACK_QUALITY {
            continue;
        }
        if !stmt.pattern.is_match(body) {
            continue;
        }
        if stmt.matches_without_empty_values(body) {
            return match with_empty_value {
                Some(prior)
                    if line_distance(src_ref(&prior), lineno) < line_distance(stmt, lineno) =>
                {
                    Some(prior)
                }
                _ => Some(candidate),
            };
        }
        with_empty_value.get_or_insert(candidate);
    }
    with_empty_value
}

/// The least amount of literal text, not counting whitespace, for a statement that is not `Log` to
/// be matched to a log message.
const MIN_FALLBACK_QUALITY: usize = 5;

/// How far a statement is from the line number in a log message, or zero if there is none.
fn line_distance(src_ref: &SourceRef, lineno: Option<usize>) -> usize {
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
    lhs: &SourceRef,
    rhs: &SourceRef,
    lineno: Option<usize>,
    level: Option<LogLevel>,
) -> Ordering {
    let distance = |src_ref: &SourceRef| line_distance(src_ref, lineno);
    let level_matches = |src_ref: &SourceRef| level == Some(src_ref.level);
    lhs.category
        .match_priority()
        .cmp(&rhs.category.match_priority())
        .then_with(|| rhs.quality.cmp(&lhs.quality))
        .then_with(|| level_matches(rhs).cmp(&level_matches(lhs)))
        .then_with(|| distance(lhs).cmp(&distance(rhs)))
        // A placeholder can be empty, so a message like "Done" matches both "Done" and "Done{}".
        .then_with(|| lhs.kinds.len().cmp(&rhs.kinds.len()))
        .then_with(|| {
            (&lhs.source_path, lhs.line_no, lhs.column).cmp(&(
                &rhs.source_path,
                rhs.line_no,
                rhs.column,
            ))
        })
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
}

impl Default for LogMatchOptions {
    fn default() -> Self {
        Self {
            extract_variables: true,
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
        for sif in decoded_root.files_with_statements.values_mut() {
            // The pattern string is not serialized, so fill it in from the regex.
            for stmt in sif.log_statements.iter_mut() {
                stmt.pattern_str = stmt.pattern.to_string();
            }
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
                bincode::serde::encode_into_std_write(root, &mut file, bincode::config::standard())
                    .map_err(to_write_cache_error)?;
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
                    prefilter: None,
                    line_cache: RwLock::default(),
                    log_calls: BTreeMap::new(),
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
            let mut unreadable: Vec<PathBuf> = Vec::new();
            for event_chunk in &events.into_iter().chunks(10) {
                let sources = event_chunk
                    .flat_map(|event| match event {
                        ScanEvent::NewFile(path, info) => {
                            let res = File::open(&path)
                                .map_err(|err| LogError::CannotReadSourceFile {
                                    path: path.clone(),
                                    source: Arc::new(err),
                                })
                                .and_then(|file| CodeSource::new(&path, info, file));
                            match res {
                                Ok(cs) => {
                                    retval.new += 1;
                                    Some(cs)
                                }
                                Err(err) => {
                                    retval.errors.push(err);
                                    unreadable.push(path);
                                    guard.inc(1);
                                    None
                                }
                            }
                        }
                        ScanEvent::DeletedFile(_path, id) => {
                            retval.deleted += 1;
                            coll.files_with_statements.remove(&id);
                            coll.file_name_to_sources.values_mut().for_each(|ids| {
                                ids.retain_mut(|elem| *elem != id);
                            });
                            None
                        }
                    })
                    .collect::<Vec<CodeSource>>();
                extract_logging_guarded(&sources, &guard)
                    .into_iter()
                    .for_each(|sif| {
                        sif.to_lookup_pair().into_iter().for_each(|(name, sid)| {
                            coll.file_name_to_sources.entry(name).or_default().push(sid);
                        });
                        coll.files_with_statements.insert(sif.id, sif);
                    });
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
            coll.rebuild_prefilter();
        });
        let mut found = format!("{} found", self.statements().count());
        if ref_summary.resolved + ref_summary.not_found + ref_summary.no_text > 0 {
            found.push_str(&format!(
                " ({} with a message constant; {} constants not found, {} without text)",
                ref_summary.resolved, ref_summary.not_found, ref_summary.no_text
            ));
        }
        tracker.end_step(found);

        retval
    }

    /// Attempt to match the given log message.  If the message has a file name and line number,
    /// the statements in a root that matched earlier messages with the same ones are tried
    /// before the rest of that root.
    pub fn match_log_statement<'a, 's>(
        &'s self,
        log_ref: &LogRef<'a>,
        options: &LogMatchOptions,
    ) -> Option<LogMapping<'a, 's>> {
        self.roots
            .values()
            .find_map(|coll| {
                coll.find_cached_match(log_ref)
                    .or_else(|| coll.find_best_match(log_ref))
            })
            .map(|src_ref| self.to_log_mapping(log_ref, src_ref, options))
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

    /// Iterate over all of the log statements that were found.
    pub fn statements(&self) -> impl Iterator<Item = &SourceRef> {
        self.roots
            .values()
            .flat_map(|coll| coll.files_with_statements.values())
            .flat_map(|sif| sif.statements())
    }

    /// Find the statements that could have produced a message, like one copied from a log, a
    /// screenshot, or a GUI, and the sources of the values in it.  See
    /// [`find_message_sources`].
    pub fn find_message_sources(&self, message: &str) -> Vec<MessageSource<'_>> {
        find_message_sources(self.statements(), message)
    }

    fn to_log_mapping<'a, 's>(
        &self,
        log_ref: &LogRef<'a>,
        src_ref: &'s SourceRef,
        options: &LogMatchOptions,
    ) -> LogMapping<'a, 's> {
        let exception_trace = match log_ref {
            LogRef {
                details:
                    Some(LogDetails {
                        trace: Some(trace), ..
                    }),
                ..
            } => trace.exception_call_sites(self),
            _ => Vec::new(),
        };
        let variables = if options.extract_variables {
            extract_variables(log_ref, src_ref)
        } else {
            Vec::new()
        };
        LogMapping {
            log_ref: *log_ref,
            src_ref: Some(src_ref),
            variables,
            exception_trace,
        }
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone, Serialize, Deserialize, clap::ValueEnum)]
pub enum SourceLanguage {
    Rust,
    Java,
    C,
    #[serde(rename = "C++")]
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
                "#
    )
});

static JAVA_PLACEHOLDER_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#"\{[^{}]*}|\\\{([^}]*)}"#).unwrap());

/// A printf-style conversion, like `%-5d`, `%'.2f`, `%1$s`, or glibc's `%m`, followed by the
/// conversion characters that are accepted.  There are no capture groups since the other
/// placeholders in a language's regex are identified by their group.
const PRINTF_CONVERSION: &str = r#"%(?:\d+\$)?[-+ #0']*(?:\d+|\*)?(?:\.(?:\d+|\*))?[hlLzjt]*"#;
const C_CONVERSIONS: &str = "[diuoxXfFeEgGaAcspnm%]";

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

/// The query for C and C++ calls with a message, where `literals` are the kinds of nodes that
/// are messages.  C++ also has the messages of the exceptions that are thrown, like
/// `throw std::runtime_error("...")`.
fn c_family_query(literals: &str, cpp: bool) -> String {
    let throw = if cpp {
        format!(
            r#"
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
            {throw}
        "#
    )
}

/// Like C++, but without raw strings, and `+` on a string-literal is never a concatenation.
static C_QUERY: LazyLock<String> =
    LazyLock::new(|| c_family_query("(string_literal) (concatenated_string)", false));
static CPP_QUERY: LazyLock<String> = LazyLock::new(|| {
    c_family_query(
        "(string_literal) (raw_string_literal) (concatenated_string) (binary_expression)",
        true,
    )
});

static PATH_TO_NAME_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#"[/\\]([^/\\]+)$"#).unwrap());

static BACKTRACE_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r#"(?smx)
    (?<python>
        # Match the initial 'Traceback' line
        ^Traceback\s+\(most\s+recent\s+call\s+last\):\s*$\n?

        # Match all stack frames
        (?:
            # File line: '  File "path", line N, in function'
            ^\s{2}File\s+"[^"]*",\s+line\s+\d+,\s+in\s+\S+\s*$\n?

            # Code line (optional): '    code_here'
            (?:^\s{4}.*$\n?)?
        )+

        # Match the final exception line
        ^[a-zA-Z_][a-zA-Z0-9_.]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*)*:.*$
    )
    |
    (?<java>
        # Match exception header(s)
        (?:^\S*?(?:Exception|Error)(?::\s*.*?)?$\n?)+

        # Match all stack trace components
        (?:
            # Stack frame: at package.Class.method(Source.java:123)
            (?:^\s*at\s+
                (?:[a-zA-Z_$][a-zA-Z0-9_$]*\.)*  # Package names
                [a-zA-Z_$][a-zA-Z0-9_$]*         # Class name
                (?:\.[a-zA-Z_$][a-zA-Z0-9_$]*)?  # Method name
                (?:\([^)]*\))?                    # Source info
                (?:\s*~\[[^\]]+\])?              # Module info
                (?:\s*@[a-fA-F0-9]+)?$\n?        # Memory address
            )
            |
            # Suppressed frames: ... N more
            (?:^\s*\.{3}\s*\d+\s+
                (?:more|common\s+frames?\s+omitted)$\n?
            )
            |
            # Caused by chain
            (?:^\s*Caused\s+by:\s*
                [a-zA-Z_$][a-zA-Z0-9_$.]*       # Exception class
                (?::\s*.*?)?$\n?                 # Optional message
            )
            |
            # Suppressed exceptions
            (?:^\s*Suppressed:\s*
                [a-zA-Z_$][a-zA-Z0-9_$.]*       # Exception class
                (?::\s*.*?)?$\n?                 # Optional message
            )
        )*
    )
"#,
    )
    .unwrap()
});

impl SourceLanguage {
    /// C and C++ share most of their grammar and logging conventions.
    pub fn is_c_family(&self) -> bool {
        matches!(self, SourceLanguage::C | SourceLanguage::Cpp)
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            SourceLanguage::Rust => "Rust",
            SourceLanguage::Java => "Java",
            SourceLanguage::C => "C",
            SourceLanguage::Cpp => "C++",
            SourceLanguage::Python => "Python",
            SourceLanguage::Kotlin => "Kotlin",
        }
    }

    fn from_extension(extension: &OsStr) -> Option<Self> {
        match extension.to_str() {
            Some("rs") => Some(Self::Rust),
            Some("java") => Some(Self::Java),
            Some("c") => Some(Self::C),
            Some("h" | "hh" | "hpp" | "hxx" | "tpp" | "cc" | "cpp" | "cxx") => Some(Self::Cpp),
            Some("py") => Some(Self::Python),
            Some("kt" | "kts") => Some(Self::Kotlin),
            None | Some(_) => None,
        }
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
    pub src_ref: Option<&'s SourceRef>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    #[serde(rename(serialize = "exceptionTrace"))]
    pub exception_trace: Vec<CallSite>,
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
        details.thread.is_none()
            && details.file.is_none()
            && details.lineno.is_none()
            && details.trace.is_none()
    } else {
        true
    }
}

static PYTHON_CALLER_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r#"(?smx)
    (?:
        ^\s+File\s+"(?<path>[^"]+)",\s+line\s+(?<line>\d+),\s+in\s+(?<name>[^\n]+)$\n?
    )
"#,
    )
    .unwrap()
});

static JAVA_CALLER_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r#"(?smx)
    (?:
        ^\s+at\s+(?:[^\s/(]*/)*(?<pkg>(?:[\w$]+\.)*)(?<class>[\w$]+)\.(?<name>[\w$<>-]+)\((?<file>[^:()\n]+):(?<line>\d+)\)\s*$\n?
    )
"#,
    )
        .unwrap()
});

#[derive(Copy, Clone, Debug, PartialEq, Serialize)]
pub struct StackTrace<'a> {
    pub language: SourceLanguage,
    pub content: &'a str,
}

impl<'a> StackTrace<'a> {
    fn exception_call_sites(&self, log_matcher: &LogMatcher) -> Vec<CallSite> {
        let mut retval = Vec::new();
        match self.language {
            SourceLanguage::Rust => {}
            SourceLanguage::Java => {
                for cap in JAVA_CALLER_REGEX.captures_iter(self.content) {
                    // The Java stack trace does not contain the full path to the source file.
                    // So, we need to construct a path from the package and class name.  Then,
                    // we use SourceHierTree::find_file() to find the actual path.
                    let path_for_pkg = cap
                        .name("pkg")
                        .map(|m| PathBuf::from(m.as_str().replace(".", "/")))
                        .unwrap_or_default();
                    let path_for_class = path_for_pkg.join(cap.name("file").unwrap().as_str());
                    let full_path = log_matcher.find_file(&path_for_class);
                    if let Some(full_path) = full_path {
                        retval.push(CallSite {
                            name: cap.name("name").unwrap().as_str().to_string(),
                            source_path: full_path.to_string_lossy().to_string(),
                            // The trace could also be from Kotlin or another JVM language.
                            language: SourceLanguage::from_path(&full_path)
                                .unwrap_or(SourceLanguage::Java),
                            line_no: cap.name("line").unwrap().as_str().parse::<usize>().unwrap(),
                        });
                    }
                }
            }
            // JVM traces are always recognized as Java.
            SourceLanguage::C | SourceLanguage::Cpp | SourceLanguage::Kotlin => {}
            SourceLanguage::Python => {
                for cap in PYTHON_CALLER_REGEX.captures_iter(self.content) {
                    retval.push(CallSite {
                        name: cap.name("name").unwrap().as_str().to_string(),
                        source_path: cap.name("path").unwrap().as_str().to_string(),
                        language: SourceLanguage::Python,
                        line_no: cap.name("line").unwrap().as_str().parse::<usize>().unwrap(),
                    });
                }
            }
        }
        retval
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trace: Option<StackTrace<'a>>,
}

impl<'a> LogDetails<'a> {
    fn is_empty(&self) -> bool {
        self.thread.is_none()
            && self.file.is_none()
            && self.lineno.is_none()
            && self.level.is_none()
            && self.body.is_none()
            && self.trace.is_none()
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
        let (body, trace) = if let Some(body) = body {
            if let Some(trace) = BACKTRACE_REGEX.captures(body) {
                let language = if trace.name("python").is_some() {
                    SourceLanguage::Python
                } else if trace.name("java").is_some() {
                    SourceLanguage::Java
                } else {
                    unreachable!();
                };
                let cap0 = trace.get(0).unwrap();
                (
                    Some(body[0..cap0.range().start].trim_end()),
                    Some(StackTrace {
                        language,
                        content: cap0.as_str(),
                    }),
                )
            } else {
                (Some(body), None)
            }
        } else {
            (None, None)
        };
        self.details.body = body;
        self.details.trace = trace;
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

pub fn link_to_source<'a>(log_ref: &LogRef, src_refs: &'a [SourceRef]) -> Option<&'a SourceRef> {
    let candidates = src_refs
        .iter()
        .sorted_by(|lhs, rhs| compare_candidates(lhs, rhs, None, log_ref.level()));
    first_match(candidates, log_ref.body(), None, |src_ref| src_ref)
}

pub fn lookup_source<'a>(
    log_ref: &LogRef,
    log_format: &LogFormat,
    src_refs: &'a [SourceRef],
) -> Option<&'a SourceRef> {
    if let Some(captures) = log_format.captures(log_ref.body()) {
        let file_name = captures.name("file").map_or("", |m| m.as_str());
        let line_no: usize = captures
            .name("line")
            .map_or(0, |m| m.as_str().parse::<usize>().unwrap_or_default());
        // println!("{:?} {:?}", file_name, line_no);

        src_refs.iter().find(|&source_ref| {
            // println!("source_ref.source_path = {} line_no = {}", source_ref.source_path, source_ref.line_no);
            source_ref.source_path.contains(file_name) && source_ref.line_no == line_no
        })
    } else {
        None
    }
}

pub fn extract_variables<'a>(log_ref: &LogRef<'a>, src_ref: &'a SourceRef) -> Vec<VariablePair> {
    let mut variables = Vec::new();
    let line = match log_ref.details {
        Some(details) => details.body.unwrap_or(log_ref.line),
        None => log_ref.line,
    };
    if let Some(captures) = src_ref.captures(line) {
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
    src_ref: &SourceRef,
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
        src_ref
            .segment_matchers()
            .and_then(|segments| value_kind::split_values(line, segments, kinds, order))
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
            let query = code.info.language.get_query();
            let results = src_query.query(query, None);
            for result in results {
                // println!("node.kind()={:?} range={:?}", result.kind, result.range);
                match result.kind.as_str() {
                    "string_literal" | "string" | "concatenated_string" | "binary_expression" => {
                        args_target = ArgsTarget::None;
                        let from_arg = result.arg_level().is_some();
                        if let Some(src_ref) = SourceRef::new(code, result) {
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
                            }
                        }
                    }
                    _ => {} // eprintln!("ignoring {}", result.kind),
                }
                // println!("*****");
            }
            guard.inc(1);
            if matched.is_empty() && message_refs.is_empty() && symbols.constants.is_empty() {
                None
            } else {
                Some(StatementsInFile {
                    path: code.filename.clone(),
                    id: code.info.id,
                    arg_levels,
                    log_statements: matched,
                    resolved_statements: vec![],
                    constants: symbols.constants,
                    message_refs,
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
            trace: None,
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_yaml_snapshot!(src_refs);
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 6);
        let result = link_to_source(&log_ref, &src_refs);
        assert!(ptr::eq(result.unwrap(), &src_refs[0]));
    }

    #[test]
    fn test_link_to_quality_source() {
        let lf = r#"^\[\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z \w+ \w+\]\s+(?<body>.*)"#
            .try_into()
            .unwrap();
        let log_ref =
            from_log_format_and_line("[2024-05-09T19:58:53Z DEBUG main] Hello, Leander!", lf);
        let code = CodeSource::from_string(Path::new("in-mem.rs"), TEST_SOURCE);
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        let result = link_to_source(&log_ref, &src_refs);
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 1);
        let result = link_to_source(&log_ref, &src_refs);
        assert!(ptr::eq(result.unwrap(), &src_refs[0]));
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 6);
        let result = link_to_source(&log_ref, &src_refs);
        assert!(result.is_none());
    }

    #[test]
    fn test_extract_variables() {
        let log_ref = LogRefBuilder::new().build("this won't match i=1; j=2");
        let code = CodeSource::from_string(Path::new("in-mem.rs"), TEST_SOURCE);
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 3);
        assert_eq!(src_refs[2].text, r#""not a {}""#);
        let line = "Loading driver configuration via classloader jdk.internal.loader";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        assert_eq!(link_to_source(&log_ref, &src_refs), Some(&src_refs[0]));
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
                assert!(src_ref.source_path.ends_with("Caller.java"));
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
            let mut lines: Vec<usize> = cache
                .get("Dup.java")
                .and_then(|by_line| by_line.get(&6))
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
                .map(|src_ref| src_ref.source_path.clone())
        };

        assert!(match_path("count xyz").unwrap().ends_with("com/a/Dup.java"));
        // The generic statement also matches, but must not hide the better one in the other file.
        assert!(match_path("count is 3")
            .unwrap()
            .ends_with("com/b/Dup.java"));
        let coll = matcher.roots.values().next().unwrap();
        assert!(coll.line_cache.read().unwrap().is_empty());
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
                    let dir = if src_ref.source_path.ends_with("com/a/Same.java") {
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
        let caller: Vec<&SourceRef> = matcher
            .statements()
            .filter(|stmt| stmt.source_path.ends_with("Caller.java"))
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 2);
        assert_eq!(
            src_refs[0].pattern().as_str(),
            "(?s)^Opening href with external editor: (.*):(.*):(.*)$"
        );
        assert_eq!((src_refs[0].line_no, src_refs[0].end_line_no), (4, 8));
        assert_eq!(src_refs[0].vars, vec!["path", "line", "0"]);
        assert_eq!(src_refs[1].pattern().as_str(), "(?s)^read (.*) bytes$");
        assert_eq!(src_refs[1].vars, vec!["size"]);
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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

    const PYTHON_FORMATTED_SOURCE: &str = r#"
def main(name, count, err, user, d, a, b, off, old_id):
    logger.info("user %s has %d items" % (name, count))
    logger.warning("Failed: " + str(err) + "!")
    logger.debug("{}: {} missing (byte {offset})".format(name, user.path, offset=off))
    logger.info("{0.name} is {{literal}} 100%".format(user))
    logger.error("100%% of %s" % name)
    logger.info("x %(a)s" % d)
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 2);
        assert_eq!(src_refs[0].qualified_name, "load");
        assert_eq!(src_refs[1].qualified_name, "other");
    }

    #[test]
    fn test_cpp_nested_statements() {
        let code = CodeSource::from_string(&PathBuf::from("in-mem.cc"), CPP_NESTED_SOURCE);
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let result = link_to_source(&log_ref, &src_refs).unwrap();
        assert_eq!(result.line_no, 14);
        assert_eq!(
            extract_variables(&log_ref, result),
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 1);
        assert_eq!(
            src_refs[0].name,
            "push(struct node *new, const char *class)"
        );
        assert_eq!(src_refs[0].language, SourceLanguage::C);

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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
    fn test_c_escapes_and_placeholders() {
        let code = CodeSource::from_string(
            Path::new("in-mem.c"),
            r#"
void f(int n) {
    log_info("{literal} %d\e[0m", n);
}
"#,
        );
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 1);
        // Braces are not placeholders in C.
        let log_ref = LogRefBuilder::new().build("{literal} 7\x1b[0m");
        let result = link_to_source(&log_ref, &src_refs).unwrap();
        assert_eq!(
            extract_variables(&log_ref, result),
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_yaml_snapshot!(src_refs);
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(patterns, vec![r"(?s)^request (.*) done$"]);
        assert_eq!(src_refs[0].level, LogLevel::Info);
        assert_eq!(src_refs[0].vars, vec!["id"]);
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

    fn kotlin_statements() -> Vec<SourceRef> {
        let code = CodeSource::from_string(Path::new("Server.kt"), KOTLIN_SOURCE);
        extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements
    }

    fn kotlin_vars(src_ref: &SourceRef, line: &str) -> Vec<(String, String)> {
        let log_ref = LogRefBuilder::new().build(line);
        extract_variables(&log_ref, src_ref)
            .into_iter()
            .map(|pair| (pair.expr, pair.value))
            .collect()
    }

    #[test]
    fn test_basic_kotlin() {
        let src_refs = kotlin_statements();
        assert_yaml_snapshot!(src_refs);
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        let line_of = |msg: &str| {
            let log_ref = LogRefBuilder::new().build(msg);
            link_to_source(&log_ref, &src_refs).map(|src_ref| src_ref.line_no)
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        let encoded =
            bincode::serde::encode_to_vec(&src_refs[1], bincode::config::standard()).unwrap();
        let (decoded, _): (SourceRef, usize) =
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
            prefilter: None,
            line_cache: RwLock::default(),
            log_calls: BTreeMap::new(),
        };
        for sif in extract_logging(&codes, &ProgressTracker::new()) {
            tree.files_with_statements.insert(sif.id, sif);
        }
        // Pruning again, like after a file changes, starts over from the extracted levels.  The
        // statements are restored from their call names, so nothing else needs to be kept.
        tree.prune_log_calls();
        tree.prune_log_calls();
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
        // Too little in common.
        assert_eq!(find("the cache"), vec![]);
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
        let matched = link_to_source(&log_ref, &sif.log_statements).map(|stmt| stmt.line_no);
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
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
            link_to_source(&log_ref, &src_refs).map(|src_ref| src_ref.line_no),
            Some(6)
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
}
"#,
        );
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        let best = |line: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
            link_to_source(&log_ref, &src_refs).map(|src_ref| src_ref.line_no)
        };
        // Too little literal text to match a log message unless it is a log statement.
        assert_eq!(best("usr/bin"), None);
        assert_eq!(best("ready: now"), Some(4));
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
            prefilter: None,
            line_cache: RwLock::default(),
            log_calls: BTreeMap::new(),
        };
        for sif in extract_logging(&[code], &ProgressTracker::new()) {
            tree.files_with_statements.insert(sif.id, sif);
        }
        tree.prune_log_calls();
        tree.rebuild_prefilter();
        let best = |line: &str| {
            let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
            tree.find_best_match(&log_ref)
                .map(|src_ref| (src_ref.line_no, src_ref.category))
        };
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        let log_format: LogFormat = r"^(?<level>\w+) (?<body>.*)$".try_into().unwrap();
        for (line, expected) in [
            ("DEBUG retry", LogLevel::Debug),
            ("WARN retry", LogLevel::Warn),
        ] {
            let log_ref =
                LogRefBuilder::new().build_from_captures(log_format.captures(line).unwrap(), line);
            let result = link_to_source(&log_ref, &src_refs).unwrap();
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        for level in [LogLevel::Debug, LogLevel::Warn] {
            let log_ref = LogRefBuilder::new()
                .with_log_level(Some(level))
                .with_body(Some("retry"))
                .build("retry");
            assert_eq!(log_ref.level(), Some(level));
            let result = link_to_source(&log_ref, &src_refs).unwrap();
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
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_yaml_snapshot!(src_refs);
        let vars = extract_variables(&log_ref, &src_refs[0]);
        assert_yaml_snapshot!(vars);
    }

    #[test]
    fn test_kotlin_trace() {
        let content = r#"java.lang.IllegalStateException: boom
    at org.example.Worker.run(Basic.kt:13)
    at org.example.BasicKt.main(Basic.kt:21)
"#;
        let mut log_matcher = LogMatcher::new();
        log_matcher
            .add_root(&Path::new("tests").join("kotlin"))
            .unwrap();
        assert!(log_matcher
            .discover_sources(&ProgressTracker::new())
            .is_empty());
        let stacktrace = StackTrace {
            language: SourceLanguage::Java,
            content,
        };
        let trace: Vec<_> = stacktrace
            .exception_call_sites(&log_matcher)
            .into_iter()
            .map(|site| (site.name, site.language, site.line_no))
            .collect();
        assert_eq!(
            trace,
            vec![
                ("run".to_string(), SourceLanguage::Kotlin, 13),
                ("main".to_string(), SourceLanguage::Kotlin, 21),
            ]
        );
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

    #[test]
    fn test_java_trace_inner_classes() {
        let content = r#"java.lang.IllegalStateException: boom
	at com.foo.Bar$1.run(Bar.java:42)
	at com.foo.Bar$Inner$2.call(Bar.java:55)
	at com.foo.Bar.lambda$main$0(Bar.java:12)
	at app//com.foo.Bar$1.<init>(Bar.java:40)
	at com.foo.Bar$$Lambda$14/0x0000000800c03000.run(Unknown Source)
	at com.zzz.Bar.run(Bar.java:7)
	at com.MyCo.app.UserId.box-impl(UserId.kt:5)
	at java.base/java.lang.Thread.run(Thread.java:833)
"#;
        let (dir, log_matcher) = find_file_matcher();
        let bar = dir
            .path()
            .join("src/main/java/com/foo/Bar.java")
            .canonicalize()
            .unwrap();
        let user_id = dir
            .path()
            .join("src/main/kotlin/com/MyCo/app/UserId.kt")
            .canonicalize()
            .unwrap();
        let stacktrace = StackTrace {
            language: SourceLanguage::Java,
            content,
        };
        let trace: Vec<_> = stacktrace
            .exception_call_sites(&log_matcher)
            .into_iter()
            .map(|site| {
                (
                    site.name,
                    PathBuf::from(site.source_path).canonicalize().unwrap(),
                    site.line_no,
                )
            })
            .collect();
        // com/other/Bar.java has the same name, so the package has to be split off correctly.
        // com.zzz.Bar is in neither package, so it is dropped instead of guessing.
        assert_eq!(
            trace,
            vec![
                ("run".to_string(), bar.clone(), 42),
                ("call".to_string(), bar.clone(), 55),
                ("lambda$main$0".to_string(), bar.clone(), 12),
                ("<init>".to_string(), bar.clone(), 40),
                ("box-impl".to_string(), user_id, 5),
            ]
        );
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
    fn test_python_trace() {
        let stacktrace = StackTrace {
            language: SourceLanguage::Python,
            content: PYTHON_TRACE,
        };

        let log_matcher = LogMatcher::new();
        let trace = stacktrace.exception_call_sites(&log_matcher);
        assert_yaml_snapshot!(trace);
    }
}
