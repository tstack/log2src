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
