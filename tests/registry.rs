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

    // At most one slot per thread that was ever concurrently mid-operation.
    let slots = hazard::registry_len();
    assert!(
        slots <= THREADS,
        "{slots} slots for {THREADS} threads and {} operations",
        THREADS * ops
    );
}
