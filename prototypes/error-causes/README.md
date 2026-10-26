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

| text | result |
|---|---|
| `Server startup failed: cache storage failed to read: PermissionDenied ... S3Error {...}` | `commands.rs:873` -> `cache/cache.rs:279` -> opendal (not in tree) |
| `failed to zip up compiler outputs` | `compiler/compiler.rs:835` |
| ``failed to put object `"...regex_automata-....d"` in cache entry`` | `cache/cache_io.rs:254` (needed the `\|\| { format!(..) }` pattern) |
| `Failed to create temp dir` | `compiler/rust.rs:454` |
| `failed to execute compile` | `commands.rs:1022` (+1 with the same text) |
| `Failed to send data to or receive data from server` | `commands.rs:395` (+2 with the same text) |
| `couldn't connect to server` | `commands.rs:879` |
| `["null"] fatal error: Permission denied (os error 13) at path "/dev/.tmp8jzDrb"` | log `server.rs:1712`, value from std/tempfile |
| `Couldn't open config file: failed to open file `/root/.config/sccache/config`` | log `config.rs:810`, value **wrongly** linked to `cache_io.rs:249` (`{:?}` would have quoted the path; the issue is from an older version) |
| `Failed to read response header` | **missed**: the literal is assigned to a variable, then passed to `.context(context)` |
| `Network error: error sending request for url (...)` (lychee) | `#[error]` in `types/error.rs:20`, inner value from reqwest |
| `Meilisearch (v1.10.1) failed to infer the version of the database. ...` | `#[error]` in `versioning.rs:75`, only when the indentation of the continuation line is kept |
| `index_scheduler: internal: decoding failed.` (meilisearch) | the whole message is `#[error("internal: {0}.")]` in `error.rs:35`, inner value from heed |
| `Allocation error : not enough memory`, `... (os error 2/10054/111/22)`, `timed out` | not in tree (zstd, std::io) |
