//! Hazard registry sizing.
//!
//! These assertions read process-global state, so they live in their own test
//! binary where no other test can allocate slots concurrently.

mod common;

use common::scale;
use std::sync::{Arc, Barrier};
use std::thread;
use unstacked::{Stack, hazard};

const THREADS: usize = 4;
const OPS_PER_THREAD: usize = 500;

#[test]
fn registry_is_bounded_by_concurrency_not_operations() {
    let stack = Arc::new(Stack::new());
    let barrier = Arc::new(Barrier::new(THREADS));
    let ops = scale(OPS_PER_THREAD);

    let handles: Vec<_> = (0..THREADS)
        .map(|_| {
            let stack = Arc::clone(&stack);
            let barrier = Arc::clone(&barrier);
            thread::spawn(move || {
                barrier.wait();
                for i in 0..ops {
                    stack.push(i);
                    let _ = stack.pop();
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }

    // About one slot per thread that was ever concurrently mid-operation. Not
    // exactly: `acquire_slot` walks the list without a snapshot, so a slot
    // released behind the walker is missed and a new one is allocated. Miri's
    // preemption makes that likely. A per-operation leak would still be far
    // above this bound.
    let slots = hazard::registry_len();
    assert!(
        slots <= 2 * THREADS,
        "{slots} slots for {THREADS} threads and {} operations",
        THREADS * ops
    );
}
