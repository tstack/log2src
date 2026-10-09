use directories::ProjectDirs;
use indicatif::HumanBytes;
use itertools::Itertools;
use miette::Diagnostic;
use rayon::prelude::*;
use regex::{Captures, Regex};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::error::Error;
use std::ffi::OsStr;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Seek, Write};
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::sync::{Arc, LazyLock, PoisonError, RwLock};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{fs, io};
use tempfile::NamedTempFile;
use thiserror::Error;
use tree_sitter::Language;

mod code_source;
mod java_symbols;
mod log_format;
mod prefilter;
mod progress;
mod source_hier;
mod source_query;
mod source_ref;

// TODO: doesn't need to be exposed if we can clean up the arguments to do_mapping
use crate::java_symbols::{JavaSymbols, MessageRef, StringConstant};
use crate::prefilter::{Prefilter, StatementID};
use crate::progress::{ProgressReader, WorkGuard};
use crate::source_hier::{ScanEvent, SourceFileID, SourceHierContent, SourceHierTree};
use crate::source_ref::{CallSite, FormatArgument};
pub use code_source::CodeSource;
pub use log_format::LogFormat;
pub use progress::ProgressTracker;
pub use progress::ProgressUpdate;
pub use progress::WorkInfo;
use source_query::QueryResult;
pub use source_query::SourceQuery;
pub use source_ref::SourceRef;

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
    #[serde(rename = "13")]
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
        cache
            .get(filename)?
            .get(&lineno)?
            .iter()
            .filter_map(|(file_id, index)| {
                self.files_with_statements.get(file_id)?.statement(*index)
            })
            .filter(|src_ref| src_ref.pattern.is_match(body))
            .max_by_key(|src_ref| src_ref.quality)
    }

    /// Find the highest quality statement that matches the given log message.  If the message
    /// has a file name and line number, the statement is added to the cache for them.
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
        candidates.sort_by(|lhs, rhs| rhs.1.quality.cmp(&lhs.1.quality));
        let (stmt_id, src_ref) = candidates
            .into_iter()
            .find(|(_, src_ref)| src_ref.pattern.is_match(body))?;
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

/// Collection of root paths to their tree of source files
/// that contain log statements.
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
        Self {
            roots: HashMap::new(),
        }
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
            let cached_name = to_cached_name(&root_path);
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
    pub fn add_root(&mut self, path: &Path) -> Result<(), LogError> {
        let path = path.canonicalize().unwrap_or(path.to_owned());
        if let Some(_existing_path) = self.match_path(&path) {
        } else {
            self.roots
                .entry(path.to_owned())
                .or_insert_with(|| SourceTree {
                    tree: SourceHierTree::from(&path),
                    files_with_statements: HashMap::new(),
                    file_name_to_sources: HashMap::new(),
                    prefilter: None,
                    line_cache: RwLock::default(),
                });
        }
        Ok(())
    }

    /// Check if the given path is covered by any of the roots in this matcher.
    pub fn match_path(&self, path: &Path) -> Option<(&PathBuf, &SourceTree)> {
        self.roots
            .iter()
            .filter(|(existing_path, _coll)| path.starts_with(existing_path))
            .next()
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

    /// Iterate over all of the log statements that were found.
    pub fn statements(&self) -> impl Iterator<Item = &SourceRef> {
        self.roots
            .values()
            .flat_map(|coll| coll.files_with_statements.values())
            .flat_map(|sif| sif.statements())
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
            } => trace.to_exception_trace(self),
            _ => Vec::new(),
        };
        let variables = if options.extract_variables {
            extract_variables(log_ref, src_ref)
        } else {
            Vec::new()
        };
        LogMapping {
            log_ref: log_ref.clone(),
            src_ref: Some(src_ref),
            variables,
            exception_trace,
        }
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone, Serialize, Deserialize)]
pub enum SourceLanguage {
    Rust,
    Java,
    #[serde(rename = "C++")]
    Cpp,
    Python,
    Kotlin,
}

impl From<SourceLanguage> for Language {
    fn from(value: SourceLanguage) -> Self {
        match value {
            SourceLanguage::Rust => tree_sitter_rust_orchard::LANGUAGE.into(),
            SourceLanguage::Java => tree_sitter_java::LANGUAGE.into(),
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

static RUST_PLACEHOLDER_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"\{(?:([a-zA-Z_][a-zA-Z0-9_.]*)|(\d+))?\s*(?::[^}]*)?}"#).unwrap()
});

static JAVA_PLACEHOLDER_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#"\{[^}]*}|\\\{([^}]*)}"#).unwrap());

static CPP_PLACEHOLDER_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"%[-+ #0]*(?:\d+|\*)?(?:\.(?:\d+|\*))?[hlLzjt]*[diuoxXfFeEgGaAcspn%]|\{(?:([a-zA-Z_][a-zA-Z0-9_.]*)|(\d+))?\s*(?::[^}]*)?}"#).unwrap()
});

/// SLF4J-style placeholders.  String templates are converted to these placeholders, too.
static KOTLIN_PLACEHOLDER_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#"\{[^}]*}"#).unwrap());

static PYTHON_PLACEHOLDER_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"%[-+ #0]*(?:\d+|\*)?(?:\.(?:\d+|\*))?[hlLzjt]*[diuoxXfFeEgGaAcrspn%]"#).unwrap()
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
    pub fn as_str(&self) -> &'static str {
        match self {
            SourceLanguage::Rust => "Rust",
            SourceLanguage::Java => "Java",
            SourceLanguage::Cpp => "C++",
            SourceLanguage::Python => "Python",
            SourceLanguage::Kotlin => "Kotlin",
        }
    }

    fn from_extension(extension: &OsStr) -> Option<Self> {
        match extension.to_str() {
            Some("rs") => Some(Self::Rust),
            Some("java") => Some(Self::Java),
            Some("h" | "hh" | "hpp" | "hxx" | "tpp" | "cc" | "cpp" | "cxx") => Some(Self::Cpp),
            Some("py") => Some(Self::Python),
            Some("kt" | "kts") => Some(Self::Kotlin),
            None | Some(_) => None,
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
                        (#not-any-of? @macro-name "format" "vec")
                    )
                "#
            }
            SourceLanguage::Java => {
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
                        (#match? @object-name "log(ger)?|LOG(GER)?")
                        (#match? @method-name "^log$|fine|debug|info|warn|trace|error")
                    )
                    ; A message that is a constant, like log.info(Messages.LOG_STARTING, name)
                    (method_invocation
                        object: (identifier) @object-name
                        name: (identifier) @method-name
                        arguments: (argument_list . [(identifier) (field_access)] @message-ref)
                        (#match? @object-name "log(ger)?|LOG(GER)?")
                        (#match? @method-name "fine|debug|info|warn|trace|error")
                    )
                    ; java.util.logging's log(Level, String, ...) with a constant message
                    (method_invocation
                        object: (identifier) @object-name
                        name: (identifier) @method-name
                        arguments: (argument_list . (_) . [(identifier) (field_access)] @message-ref)
                        (#match? @object-name "log(ger)?|LOG(GER)?")
                        (#eq? @method-name "log")
                    )
                "#
            }
            SourceLanguage::Cpp => {
                r#"
                    (
                        (expression_statement
                            (call_expression
                                function: (_) @fname
                                arguments: (argument_list
                                    [(string_literal) (concatenated_string)] @arguments)
                            )
                        )
                        (#not-match? @fname "snprintf|sprintf")
                    )
                "#
            }
            SourceLanguage::Python => {
                r#"
                (
                    (expression_statement
                      (call
                        function: (_) @func
                        arguments: (argument_list .
                          [(string) (concatenated_string)] @args
                        )
                      )
                    )
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
            SourceLanguage::Cpp => IDENTS_CPP,
            SourceLanguage::Python => IDENTS_PYTHON,
            SourceLanguage::Kotlin => IDENTS_KOTLIN,
        }
    }

    fn get_placeholder_regex(&self) -> &'static Regex {
        match self {
            SourceLanguage::Rust => RUST_PLACEHOLDER_REGEX.deref(),
            SourceLanguage::Java => JAVA_PLACEHOLDER_REGEX.deref(),
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
        ^\s+at\s+(?<pkg>(?:[^.\n(]+\.)*)(?<class>[^.$\n(]+)\.(?<name>\S+)\((?<file>[^:]+):(?<line>\d+)\)\s*$\n?
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
    fn to_exception_trace(&self, log_matcher: &LogMatcher) -> Vec<CallSite> {
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
                    let full_path = log_matcher
                        .roots
                        .values()
                        .filter_map(|root| {
                            if let Some((actual_path, _source_info)) =
                                root.tree.find_file(&path_for_class).iter().next()
                            {
                                Some(actual_path.clone())
                            } else {
                                None
                            }
                        })
                        .next();
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
            SourceLanguage::Cpp | SourceLanguage::Kotlin => {}
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
    pub body: Option<&'a str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trace: Option<StackTrace<'a>>,
}

impl<'a> LogDetails<'a> {
    fn is_empty(&self) -> bool {
        self.thread.is_none()
            && self.file.is_none()
            && self.lineno.is_none()
            && self.body.is_none()
            && self.trace.is_none()
    }
}

pub struct LogRefBuilder<'a> {
    details: LogDetails<'a>,
}

impl<'a> LogRefBuilder<'a> {
    pub fn new() -> Self {
        Self {
            details: Default::default(),
        }
    }

    pub fn build_from_captures(self, captures: Captures<'a>, content: &'a str) -> LogRef<'a> {
        self.with_file(captures.name("file").map(|m| m.as_str()))
            .with_lineno(
                captures
                    .name("line")
                    .map(|m| m.as_str().parse::<usize>().unwrap_or_default()),
            )
            .with_thread(captures.name("thread").map(|m| m.as_str()))
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
                    Some(*&body[0..cap0.range().start].trim_end()),
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
}

pub fn link_to_source<'a>(log_ref: &LogRef, src_refs: &'a [SourceRef]) -> Option<&'a SourceRef> {
    src_refs
        .iter()
        .sorted_by(|lhs, rhs| rhs.quality.cmp(&lhs.quality))
        .find(|&source_ref| source_ref.captures(log_ref.body()).is_some())
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
        let mut placeholder_index = 0;
        for (cap, placeholder) in std::iter::zip(captures.iter().skip(1), src_ref.args.iter()) {
            let expr = match placeholder {
                FormatArgument::Named(name) => name.clone(),
                FormatArgument::Positional(pos) => src_ref
                    .vars
                    .get(*pos)
                    .map(|s| s.as_str())
                    .unwrap_or("<unknown>")
                    .to_string(),
                FormatArgument::Placeholder => {
                    let res = src_ref
                        .vars
                        .get(placeholder_index)
                        .map(|s| s.as_str())
                        .unwrap_or("<unknown>")
                        .to_string();

                    placeholder_index += 1;
                    res
                }
            };
            variables.push(VariablePair {
                expr,
                value: cap.unwrap().as_str().to_string(),
            });
        }
    }

    variables
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
            let mut args_target = ArgsTarget::None;
            let src_query = SourceQuery::new(code);
            let symbols = (code.info.language == SourceLanguage::Java)
                .then(|| JavaSymbols::extract(&src_query))
                .unwrap_or_default();
            let query = code.info.language.get_query();
            let results = src_query.query(query, None);
            for result in results {
                // println!("node.kind()={:?} range={:?}", result.kind, result.range);
                match result.kind.as_str() {
                    "string_literal" | "string" | "concatenated_string" | "binary_expression" => {
                        args_target = ArgsTarget::None;
                        if let Some(src_ref) = SourceRef::new(code, result) {
                            matched.push(src_ref);
                            args_target = ArgsTarget::Statement;
                        }
                    }
                    "message_ref" => {
                        let range = result.range;
                        let text = &code.buffer[range.start_byte..range.end_byte];
                        message_refs.push(MessageRef {
                            line_no: range.start_point.row + 1,
                            end_line_no: range.end_point.row + 1,
                            column: range.start_point.column,
                            name: code.buffer[result.name_range].to_string(),
                            qualified_name: result.qualified_name,
                            block_id: result.block_id,
                            text: text.to_string(),
                            vars: vec![],
                            candidates: symbols.candidates(text, range.start_byte),
                        });
                        args_target = ArgsTarget::MessageRef;
                    }
                    "args" | "this" => {
                        if !matches!(args_target, ArgsTarget::None) {
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
                                } else {
                                    let prior = matched.last_mut().unwrap();
                                    prior.end_line_no = end_line_no;
                                    prior.vars.push(var);
                                }
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
        let captures = log_format.captures(&buffer).unwrap();
        LogRefBuilder::new().build_from_captures(captures, &buffer)
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
        let code = CodeSource::from_string(&Path::new("in-mem.rs"), TEST_SOURCE);
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
        let code = CodeSource::from_string(&Path::new("in-mem.rs"), TEST_SOURCE);
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 5);
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
        let code = CodeSource::from_string(&Path::new("in-mem.rs"), TEST_SOURCE);
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
        let code = CodeSource::from_string(&Path::new("in-mem.rs"), MULTILINE_SOURCE);
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
                value: "funky".to_string()
            }]
        );
    }

    #[test]
    fn test_link_to_source_no_matches() {
        let log_ref = LogRefBuilder::new().build("nope!");
        let code = CodeSource::from_string(&Path::new("in-mem.rs"), TEST_SOURCE);
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 5);
        let result = link_to_source(&log_ref, &src_refs);
        assert!(result.is_none());
    }

    #[test]
    fn test_extract_variables() {
        let log_ref = LogRefBuilder::new().build("this won't match i=1; j=2");
        let code = CodeSource::from_string(&Path::new("in-mem.rs"), TEST_SOURCE);
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 5);
        let vars = extract_variables(&log_ref, &src_refs[1]);
        assert_eq!(
            vars,
            vec![
                VariablePair {
                    expr: "i".to_string(),
                    value: "1".to_string()
                },
                VariablePair {
                    expr: "j".to_string(),
                    value: "2".to_string()
                }
            ]
        );
    }

    #[test]
    fn test_extract_named() {
        let log_ref = LogRefBuilder::new().build("Hello, Tim!");
        let code = CodeSource::from_string(&Path::new("in-mem.rs"), TEST_SOURCE);
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        assert_eq!(src_refs.len(), 5);
        let vars = extract_variables(&log_ref, &src_refs[3]);
        assert_eq!(
            vars,
            vec![VariablePair {
                expr: "name".to_string(),
                value: "Tim".to_string()
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
                value: "JvmPauseMonitor-n0".to_string()
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
                value: "jdk.internal.loader".to_string()
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
                "(?s)^User (.+) logged in from (.+)$",
                "(?s)^(.+) total$",
                "(?s)^sum=(.+)!$",
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
                    value: "alice".to_string()
                },
                VariablePair {
                    expr: "host".to_string(),
                    value: "example.com".to_string()
                },
            ]
        );

        let line = "42 total";
        let log_ref = LogRefBuilder::new().with_body(Some(line)).build(line);
        assert_eq!(
            extract_variables(&log_ref, &src_refs[2]),
            vec![VariablePair {
                expr: "a + b".to_string(),
                value: "42".to_string()
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
            "(?s)^Opening href with external editor: (.+):(.+):(.+)$"
        );
        assert_eq!((src_refs[0].line_no, src_refs[0].end_line_no), (4, 8));
        assert_eq!(src_refs[0].vars, vec!["path", "line", "0"]);
        assert_eq!(src_refs[1].pattern().as_str(), "(?s)^read (.+) bytes$");
        assert_eq!(src_refs[1].vars, vec!["size"]);
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
        let code = CodeSource::from_string(&Path::new("in-mem.cc"), CPP_SOURCE);
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
                value: "Steve".to_string()
            },]
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
        let code = CodeSource::from_string(&Path::new("in-mem.py"), PYTHON_CONCAT_SOURCE);
        let src_refs = extract_logging(&[code], &ProgressTracker::new())
            .pop()
            .unwrap()
            .log_statements;
        let patterns: Vec<&str> = src_refs.iter().map(|s| s.pattern().as_str()).collect();
        assert_eq!(
            patterns,
            vec![
                r"(?s)^first part second part (.+)$",
                r"(?s)^user (.+) has (.+) items$",
                r"(?s)^C:\\dir x\tz$",
                r"(?s)^\{literal\} (.+)$",
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
                    value: "bob".to_string()
                },
                VariablePair {
                    expr: "count".to_string(),
                    value: "3".to_string()
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
        let code = CodeSource::from_string(&Path::new("in-mem.py"), PYTHON_SOURCE);
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
                value: "bar".to_string()
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
                ("*Server::name(int x) const", "net::Server::name"),
                ("&Server::self()", "net::Server::self"),
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
        let names: Vec<String> = qualified_names("in-mem.py", source)
            .into_iter()
            .map(|(_, qname)| qname)
            .collect();
        assert_eq!(
            names,
            vec!["<module>", "Server.handle", "Server.handle.<locals>.inner"]
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
            .to_exception_trace(&log_matcher)
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
        let trace = stacktrace.to_exception_trace(&log_matcher);
        assert_yaml_snapshot!(trace);
    }
}
