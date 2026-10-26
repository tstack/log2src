# Error-cause prototype

Not for merging.  Checks whether an error value that a log statement prints, like the
`{}` in `warn!("Failed to remove container {}: {}", cid, e)`, can be reversed to the
place that created the error message.

The log2src side is a handful of extra Rust query patterns in `src/lib.rs` (marked
`PROTOTYPE`) that capture error-message sources as Unknown-level statements:
`.context("...")`, `.context(format!(...))`, `.with_context(|| format!(...))`,
`Err(format!(...))`, `write!(f, "...")` inside `fmt`, and thiserror's `#[error("...")]`.
`bail!`/`anyhow!` were already captured.

`cargo run --release -- <source-root> [-v]` runs four checks:

- **A.** Render every source with sample values and match it back against all sources.
- **B.** Put a leaf message into the last placeholder of a wrapping source, like
  `bail!("failed to read {}: {}", path, e)`, and resolve both levels.
- **C.** anyhow `{:#}` output, `"context: leaf"`, split at `": "`.  The reading that
  explains the most literal text wins, since `#[error("Error: {0}")]` matches anything.
- **D.** End to end: for each log statement with an `e`/`err`/`error` argument, put a
  random source's message into that argument, match the line with `LogMatcher`, and
  resolve the extracted value.

Results (pairings are random and statement order isn't stable, so the numbers move by
a few percent between runs):

| | sccache | lychee | meilisearch |
|---|---|---|---|
| sources | 512 | 119 | 780 |
| A. best-ranked | 100% | 100% | 98% |
| A. single candidate | 78% | 40% | 48% |
| B. inner cause found | 97% | 96% | 92% |
| C. both levels found | 100% | 100% | 80% |
| D. log lines matched / cause resolved | 32 / 30-32 | 7 / 5-6 | 46 / 40 |

"Single candidate" is low for thiserror-heavy code because the same text is often
repeated across error enums; identical texts are counted as a hit.

## Real-world text from GitHub issues

`--match` reads log message bodies from stdin, matches each to a log statement, and
resolves its variables.  `--resolve` resolves bare error values, like the
`sccache: caused by:` lines a CLI prints.  The text was copied from public issues
(sccache #837, #1015, #1745, #1750, #1789, #1825, #2884; lychee #1487;
meilisearch #3598, #4917, #4934) and checked against current sources.

Each row is one piece of text from an issue.  "Log statement" is filled in when the text
was a whole log message, which `--match` first links to the statement that wrote it.
"Error value" is the part that came from an error, which is what gets reversed.  "Cause"
is where that error message is created, with `->` for an error wrapped inside it.

| Log statement | Error value (input) | Cause (output) | Reported in |
|---|---|---|---|
|  | `Server startup failed: cache storage failed to read: PermissionDenied ... S3Error {...}` | `commands.rs:873` `bail!("Server startup failed: {}")` -> `cache/cache.rs:279` `bail!("cache storage failed to read: {:?}")` -> opendal (not in tree) | [sccache#1825](https://github.com/mozilla/sccache/issues/1825), [sccache#2884](https://github.com/mozilla/sccache/issues/2884) (GCS variant) |
|  | `failed to zip up compiler outputs` | `compiler/compiler.rs:835` | [sccache#1750](https://github.com/mozilla/sccache/issues/1750) |
|  | ``failed to put object `"...regex_automata-....d"` in cache entry`` | `cache/cache_io.rs:254` (needed the `\|\| { format!(..) }` pattern) | [sccache#1750](https://github.com/mozilla/sccache/issues/1750) |
|  | `Allocation error : not enough memory` | zstd (not in tree) | [sccache#1750](https://github.com/mozilla/sccache/issues/1750) |
|  | `Failed to create temp dir` | `compiler/rust.rs:454` | [sccache#837](https://github.com/mozilla/sccache/issues/837) |
|  | `No such file or directory (os error 2)` | std::io (not in tree) | [sccache#837](https://github.com/mozilla/sccache/issues/837) |
|  | `failed to execute compile` | `commands.rs:1022` (+1 with the same text) | [sccache#1789](https://github.com/mozilla/sccache/issues/1789) |
|  | `Failed to send data to or receive data from server` | `commands.rs:395` (+2 with the same text) | [sccache#1789](https://github.com/mozilla/sccache/issues/1789) |
|  | `Failed to read response header` | **missed**: the literal is assigned to a variable, then passed to `.context(context)` in `client.rs:58` | [sccache#1789](https://github.com/mozilla/sccache/issues/1789) |
|  | `An existing connection was forcibly closed by the remote host. (os error 10054)` | std::io (not in tree) | [sccache#1789](https://github.com/mozilla/sccache/issues/1789) |
|  | `couldn't connect to server` | `commands.rs:879` | [sccache#1745](https://github.com/mozilla/sccache/issues/1745) |
|  | `Connection refused (os error 111)` | std::io (not in tree) | [sccache#1745](https://github.com/mozilla/sccache/issues/1745) |
| `config.rs:810` `debug!("Couldn't open config file: {}", e)` | ``failed to open file `/root/.config/sccache/config` `` | **wrong**: `cache_io.rs:249`, whose `{:?}` would have quoted the path; the issue is from an older version | [sccache#1745](https://github.com/mozilla/sccache/issues/1745) |
| `server.rs:1712` `error!("[{:?}] fatal error: {}", out_pretty, err)` | `Permission denied (os error 13) at path "/dev/.tmp8jzDrb"` | std/tempfile (not in tree) | [sccache#1015](https://github.com/mozilla/sccache/issues/1015) |
|  | `timed out` | not in tree (likely std/tokio) | [sccache#2069](https://github.com/mozilla/sccache/issues/2069) |
|  | `Network error: error sending request for url (...)` | `types/error.rs:20` `#[error("Network error: {analysis} ({error})")]` -> reqwest (not in tree) | [lychee#1487](https://github.com/lycheeverse/lychee/issues/1487) |
|  | `Meilisearch (v1.10.1) failed to infer the version of the database. ...` | `versioning.rs:75` `#[error(...)]`, only when the indentation of the continuation line is kept | [meilisearch#4917](https://github.com/meilisearch/meilisearch/issues/4917) |
| `tracing::error!("{e}")`-style, so the message is the error | `internal: decoding failed.` | `error.rs:35` `#[error("internal: {0}.")]` -> heed (not in tree) | [meilisearch#4934](https://github.com/meilisearch/meilisearch/issues/4934) |
|  | `Invalid argument (os error 22)` | std::io (not in tree) | [meilisearch#3598](https://github.com/meilisearch/meilisearch/issues/3598) |
