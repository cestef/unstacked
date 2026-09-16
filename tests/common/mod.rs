//! Shared test helpers.

/// Miri is orders of magnitude slower than native execution.
const MIRI_DIVISOR: usize = 50;

/// Below this, a "stress" test stops exercising any interleaving at all.
const MIN_STRESS: usize = 2;

/// Scales a stress-test count down under Miri so the suite stays runnable.
pub(crate) fn scale(n: usize) -> usize {
    if cfg!(miri) {
        (n / MIRI_DIVISOR).max(MIN_STRESS)
    } else {
        n
    }
}
