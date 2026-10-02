use std::io;
use std::path::{Path, PathBuf};

use crate::source_hier::SourceFileInfo;
use crate::{LogError, SourceLanguage};

pub struct CodeSource {
    pub(crate) filename: String,
    pub(crate) info: SourceFileInfo,
    pub(crate) buffer: String,
}

impl CodeSource {
    pub fn new<I>(path: &Path, info: SourceFileInfo, mut input: I) -> Result<CodeSource, LogError>
    where
        I: io::Read,
    {
        let mut bytes = Vec::new();
        match input.read_to_end(&mut bytes) {
            // Source files are not always UTF-8, so replace any invalid sequences instead of
            // giving up on the whole file.
            Ok(_) => Ok(CodeSource {
                filename: path.to_string_lossy().to_string(),
                info,
                buffer: String::from_utf8(bytes)
                    .unwrap_or_else(|err| String::from_utf8_lossy(err.as_bytes()).into_owned()),
            }),
            Err(err) => Err(LogError::CannotReadSourceFile {
                path: PathBuf::from(path),
                source: err.into(),
            }),
        }
    }

    pub fn from_string(path: &Path, input: &str) -> CodeSource {
        CodeSource {
            filename: path.to_string_lossy().to_string(),
            info: SourceFileInfo::new(SourceLanguage::from_path(path).unwrap()),
            buffer: input.to_string(),
        }
    }
}
