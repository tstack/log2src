use std::io;
use std::path::{Path, PathBuf};

use crate::source_hier::SourceFileInfo;
use crate::source_query::SourceQuery;
use crate::{LogError, SourceLanguage};

/// The text of a source file as it is parsed.  C and C++ macro calls with a parenthesized list
/// of arguments are rewritten as plain calls, see [`SourceQuery::rewrite_double_paren_calls`].
/// The rewrite keeps the byte offsets and lines the same, and it is done here so that the
/// tree and the text of the arguments come from the same buffer.
fn parsable_buffer(language: SourceLanguage, buffer: String) -> String {
    if !language.is_c_family() {
        return buffer;
    }
    SourceQuery::rewrite_double_paren_calls(&buffer).unwrap_or(buffer)
}

pub struct CodeSource {
    pub(crate) filename: String,
    pub(crate) info: SourceFileInfo,
    pub(crate) buffer: String,
}

impl CodeSource {
    pub fn new<I>(
        path: &Path,
        mut info: SourceFileInfo,
        mut input: I,
    ) -> Result<CodeSource, LogError>
    where
        I: io::Read,
    {
        let mut bytes = Vec::new();
        match input.read_to_end(&mut bytes) {
            Ok(_) => {
                // Source files are not always UTF-8, so replace any invalid sequences instead
                // of giving up on the whole file.
                let buffer = String::from_utf8(bytes)
                    .unwrap_or_else(|err| String::from_utf8_lossy(err.as_bytes()).into_owned());
                info.language = SourceLanguage::from_contents(path, info.language, &buffer);
                Ok(CodeSource {
                    filename: path.to_string_lossy().to_string(),
                    buffer: parsable_buffer(info.language, buffer),
                    info,
                })
            }
            Err(err) => Err(LogError::CannotReadSourceFile {
                path: PathBuf::from(path),
                source: err.into(),
            }),
        }
    }

    pub fn from_string(path: &Path, input: &str) -> CodeSource {
        let language =
            SourceLanguage::from_contents(path, SourceLanguage::from_path(path).unwrap(), input);
        CodeSource {
            filename: path.to_string_lossy().to_string(),
            info: SourceFileInfo::new(language),
            buffer: parsable_buffer(language, input.to_string()),
        }
    }
}
