//! Counters for how log messages are being matched, for finding out where the time goes.
//!
//! They are global, instead of in a [`crate::LogMatcher`], so the helpers deep in the matching
//! code can bump them without the stats being passed down to them, and since a program only has
//! one matcher anyway.  They are atomics, since matching is done from several threads at once.
//! Use [`match_stats`] to read them or [`take_match_stats`] to read and reset them, like after a
//! log has been processed.

use serde::Serialize;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{LazyLock, Mutex, PoisonError};
use std::time::{Duration, Instant};

/// The upper bounds, in microseconds, of the buckets of the time to match a message.  The last
/// bucket is for the rest.
const LATENCY_BOUNDS_US: [u64; 4] = [10, 100, 1_000, 10_000];

/// The most characters of the slowest message that are kept.
const MAX_SLOWEST_CHARS: usize = 160;

#[derive(Default)]
struct Counter(AtomicU64);

impl Counter {
    fn add(&self, n: u64) {
        self.0.fetch_add(n, Ordering::Relaxed);
    }

    fn max(&self, n: u64) {
        self.0.fetch_max(n, Ordering::Relaxed);
    }

    fn get(&self) -> u64 {
        self.0.load(Ordering::Relaxed)
    }

    fn take(&self) -> u64 {
        self.0.swap(0, Ordering::Relaxed)
    }
}

/// The number of times a step was done and the time it took in all.
#[derive(Default)]
struct Phase {
    calls: Counter,
    nanos: Counter,
}

impl Phase {
    fn record(&self, start: Instant) {
        self.calls.add(1);
        self.nanos.add(elapsed_nanos(start));
    }

    fn snapshot(&self, take: bool) -> PhaseStats {
        let read = |counter: &Counter| if take { counter.take() } else { counter.get() };
        PhaseStats {
            calls: read(&self.calls),
            nanos: read(&self.nanos),
        }
    }
}

fn elapsed_nanos(start: Instant) -> u64 {
    u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

#[derive(Default)]
struct Stats {
    messages: Phase,
    max_nanos: Counter,
    latency: [Counter; LATENCY_BOUNDS_US.len() + 1],

    matched_direct: Counter,
    matched_learned: Counter,
    matched_explained: Counter,
    unmatched: Counter,

    line_cache: Phase,
    line_cache_hits: Counter,
    line_cache_negative_hits: Counter,
    prefilter: Phase,
    prefilter_candidates: Counter,
    max_prefilter_candidates: Counter,
    pattern_checks: Counter,
    learned: Phase,
    explain: Phase,
    explain_candidates: Counter,
    explain_skipped: Counter,
    variables: Phase,

    slowest: Mutex<Option<(u64, String)>>,
}

static STATS: LazyLock<Stats> = LazyLock::new(Stats::default);

/// How a message was matched, or that it was not.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Outcome {
    /// A statement matched enough of the whole message, from the line cache or the prefilter.
    Direct,
    /// A statement matched the text after a prefix that was learned from an earlier message.
    Learned,
    /// The message was explained by looking for the statement that produced most of it.
    Explained,
    Unmatched,
}

/// The steps of matching a message that are timed.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Step {
    LineCache,
    Prefilter,
    Learned,
    Explain,
    Variables,
}

fn phase(step: Step) -> &'static Phase {
    match step {
        Step::LineCache => &STATS.line_cache,
        Step::Prefilter => &STATS.prefilter,
        Step::Learned => &STATS.learned,
        Step::Explain => &STATS.explain,
        Step::Variables => &STATS.variables,
    }
}

/// Time a step of matching a message.
pub(crate) fn timed<T>(step: Step, f: impl FnOnce() -> T) -> T {
    let start = Instant::now();
    let retval = f();
    phase(step).record(start);
    retval
}

/// Record that a message took from `start` until now to match, with the given outcome.
pub(crate) fn record_message(start: Instant, outcome: Outcome, body: &str) {
    let nanos = elapsed_nanos(start);
    STATS.messages.calls.add(1);
    STATS.messages.nanos.add(nanos);
    let micros = nanos / 1_000;
    let bucket = LATENCY_BOUNDS_US
        .iter()
        .position(|bound| micros < *bound)
        .unwrap_or(LATENCY_BOUNDS_US.len());
    STATS.latency[bucket].add(1);
    match outcome {
        Outcome::Direct => STATS.matched_direct.add(1),
        Outcome::Learned => STATS.matched_learned.add(1),
        Outcome::Explained => STATS.matched_explained.add(1),
        Outcome::Unmatched => STATS.unmatched.add(1),
    }
    // Only take the lock for a new maximum, which is rare after the first few messages.
    if nanos > STATS.max_nanos.get() {
        STATS.max_nanos.max(nanos);
        let mut slowest = STATS.slowest.lock().unwrap_or_else(PoisonError::into_inner);
        if slowest.as_ref().is_none_or(|(prior, _)| nanos > *prior) {
            let body: String = body.trim().chars().take(MAX_SLOWEST_CHARS).collect();
            *slowest = Some((nanos, body));
        }
    }
}

pub(crate) fn record_line_cache_hit() {
    STATS.line_cache_hits.add(1);
}

/// Record that a message was not looked for, since an earlier one with the same file name and
/// line number matched nothing.
pub(crate) fn record_line_cache_negative_hit() {
    STATS.line_cache_negative_hits.add(1);
}

pub(crate) fn record_prefilter_candidates(count: usize) {
    let count = count as u64;
    STATS.prefilter_candidates.add(count);
    STATS.max_prefilter_candidates.max(count);
}

pub(crate) fn record_explain_candidates(count: usize) {
    STATS.explain_candidates.add(count as u64);
}

/// Record that a message was not read by the explain step, since no statement but the one that
/// matched it directly could explain more of it.
pub(crate) fn record_explain_skipped() {
    STATS.explain_skipped.add(1);
}

/// Record that a statement's regex was run against a message.
pub(crate) fn record_pattern_check() {
    STATS.pattern_checks.add(1);
}

/// The number of times a step was done and the time it took in all.
#[derive(Copy, Clone, Debug, Default, Serialize)]
pub struct PhaseStats {
    pub calls: u64,
    pub nanos: u64,
}

impl PhaseStats {
    pub fn duration(&self) -> Duration {
        Duration::from_nanos(self.nanos)
    }

    /// The average time per call.
    pub fn average(&self) -> Duration {
        Duration::from_nanos(self.nanos.checked_div(self.calls).unwrap_or(0))
    }
}

/// A copy of the counters for how log messages were matched.  The `Display` form is a few lines
/// of text for a person to read, like in a log.
#[derive(Clone, Debug, Default, Serialize)]
pub struct MatchStats {
    /// The calls to `match_log_statement()` and the time spent in them.
    pub messages: PhaseStats,
    /// The longest time to match a single message.
    pub max_nanos: u64,
    /// The number of messages that took less than 10µs, 100µs, 1ms, 10ms, and the rest.
    pub latency: [u64; LATENCY_BOUNDS_US.len() + 1],
    /// Messages matched by a statement from the line cache or the prefilter.
    pub matched_direct: u64,
    /// Messages matched after a prefix that was learned from an earlier message.
    pub matched_learned: u64,
    /// Messages matched by looking for the statement that produced most of them, the slow way.
    pub matched_explained: u64,
    pub unmatched: u64,
    /// Lookups in the cache of the statements that matched a file name and line number, per
    /// source root.
    pub line_cache: PhaseStats,
    pub line_cache_hits: u64,
    /// Messages that were not looked for, since an earlier one with the same file name and line
    /// number matched nothing.  These are counted as unmatched too.
    pub line_cache_negative_hits: u64,
    /// Searches of the statements found by the prefilter, per source root.
    pub prefilter: PhaseStats,
    /// The statements found by the prefilter, in all, and for a single search.
    pub prefilter_candidates: u64,
    pub max_prefilter_candidates: u64,
    /// The number of times a statement's regex was run against a message.
    pub pattern_checks: u64,
    /// Tries of the prefixes learned from earlier messages.
    pub learned: PhaseStats,
    /// Tries at finding the statement that produced most of a message, which happen when no
    /// statement matched enough of all of it.
    pub explain: PhaseStats,
    pub explain_candidates: u64,
    /// Tries that stopped after the prefilter, since no other statement was in the message.
    pub explain_skipped: u64,
    /// Extractions of the values of the variables from a matched message.
    pub variables: PhaseStats,
    /// The slowest message, cut short, and the time it took.
    pub slowest: Option<(u64, String)>,
}

fn snapshot(take: bool) -> MatchStats {
    let read = |counter: &Counter| if take { counter.take() } else { counter.get() };
    let slowest = {
        let mut slowest = STATS.slowest.lock().unwrap_or_else(PoisonError::into_inner);
        if take {
            slowest.take()
        } else {
            slowest.clone()
        }
    };
    MatchStats {
        messages: STATS.messages.snapshot(take),
        max_nanos: read(&STATS.max_nanos),
        latency: std::array::from_fn(|index| read(&STATS.latency[index])),
        matched_direct: read(&STATS.matched_direct),
        matched_learned: read(&STATS.matched_learned),
        matched_explained: read(&STATS.matched_explained),
        unmatched: read(&STATS.unmatched),
        line_cache: STATS.line_cache.snapshot(take),
        line_cache_hits: read(&STATS.line_cache_hits),
        line_cache_negative_hits: read(&STATS.line_cache_negative_hits),
        prefilter: STATS.prefilter.snapshot(take),
        prefilter_candidates: read(&STATS.prefilter_candidates),
        max_prefilter_candidates: read(&STATS.max_prefilter_candidates),
        pattern_checks: read(&STATS.pattern_checks),
        learned: STATS.learned.snapshot(take),
        explain: STATS.explain.snapshot(take),
        explain_candidates: read(&STATS.explain_candidates),
        explain_skipped: read(&STATS.explain_skipped),
        variables: STATS.variables.snapshot(take),
        slowest,
    }
}

/// The counters for how log messages were matched since the program started or they were last
/// taken.
pub fn match_stats() -> MatchStats {
    snapshot(false)
}

/// The counters for how log messages were matched, which are then reset, so the next call gives
/// the ones for the messages matched after this.  The counters are not all reset at once, so a
/// message matched by another thread during this can be split between this and the next call.
pub fn take_match_stats() -> MatchStats {
    snapshot(true)
}

/// A percentage of a total, which is zero if the total is.
fn percent(part: u64, total: u64) -> f64 {
    if total == 0 {
        0.0
    } else {
        part as f64 * 100.0 / total as f64
    }
}

fn average(sum: u64, count: u64) -> f64 {
    if count == 0 {
        0.0
    } else {
        sum as f64 / count as f64
    }
}

impl fmt::Display for MatchStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let total = self.messages.calls;
        let share = |phase: &PhaseStats| percent(phase.nanos, self.messages.nanos);
        writeln!(
            f,
            "matched {} messages in {:.3?} (avg {:.1?}, max {:.1?})",
            total,
            self.messages.duration(),
            self.messages.average(),
            Duration::from_nanos(self.max_nanos),
        )?;
        writeln!(
            f,
            "  outcomes: direct {} ({:.1}%), learned prefix {} ({:.1}%), explained {} ({:.1}%), \
             unmatched {} ({:.1}%)",
            self.matched_direct,
            percent(self.matched_direct, total),
            self.matched_learned,
            percent(self.matched_learned, total),
            self.matched_explained,
            percent(self.matched_explained, total),
            self.unmatched,
            percent(self.unmatched, total),
        )?;
        writeln!(
            f,
            "  latency: <10us {}, <100us {}, <1ms {}, <10ms {}, >=10ms {}",
            self.latency[0], self.latency[1], self.latency[2], self.latency[3], self.latency[4],
        )?;
        writeln!(
            f,
            "  line cache: {} lookups, {} hits ({:.1}%), {} known unmatched ({:.1}% of messages), \
             {:.3?} ({:.1}%)",
            self.line_cache.calls,
            self.line_cache_hits,
            percent(self.line_cache_hits, self.line_cache.calls),
            self.line_cache_negative_hits,
            percent(self.line_cache_negative_hits, total),
            self.line_cache.duration(),
            share(&self.line_cache),
        )?;
        writeln!(
            f,
            "  prefilter: {} searches, {:.3?} ({:.1}%), candidates avg {:.1} max {}, \
             {} pattern checks",
            self.prefilter.calls,
            self.prefilter.duration(),
            share(&self.prefilter),
            average(self.prefilter_candidates, self.prefilter.calls),
            self.max_prefilter_candidates,
            self.pattern_checks,
        )?;
        writeln!(
            f,
            "  learned prefix: {} tries, {:.3?} ({:.1}%)",
            self.learned.calls,
            self.learned.duration(),
            share(&self.learned),
        )?;
        writeln!(
            f,
            "  explain: {} tries, {} with no other statements, {:.3?} ({:.1}%), avg {:.1?}, \
             candidates avg {:.1}",
            self.explain.calls,
            self.explain_skipped,
            self.explain.duration(),
            share(&self.explain),
            self.explain.average(),
            average(self.explain_candidates, self.explain.calls),
        )?;
        write!(
            f,
            "  variables: {} extractions, {:.3?} ({:.1}%)",
            self.variables.calls,
            self.variables.duration(),
            share(&self.variables),
        )?;
        if let Some((nanos, body)) = &self.slowest {
            write!(
                f,
                "\n  slowest: {:.1?} {:?}",
                Duration::from_nanos(*nanos),
                body
            )?;
        }
        Ok(())
    }
}
