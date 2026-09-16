//! Concurrent stress. These are the tests that matter: run them under Miri
//! (`cargo miri test`) and under `ThreadSanitizer` to exercise the hazard
//! pointer protocol.

mod common;

use common::scale;
use std::collections::HashSet;
use std::sync::{Arc, Barrier, Mutex};
use std::thread;
use unstacked::{Stack, hazard};

#[test]
fn concurrent_pushes_lose_nothing() {
    const THREADS: usize = 8;
    let per_thread = scale(1000);

    let stack = Arc::new(Stack::new());
    let barrier = Arc::new(Barrier::new(THREADS));

    let handles: Vec<_> = (0..THREADS)
        .map(|t| {
            let stack = Arc::clone(&stack);
            let barrier = Arc::clone(&barrier);
            thread::spawn(move || {
                barrier.wait();
                for i in 0..per_thread {
                    stack.push(t * per_thread + i);
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(stack.len(), THREADS * per_thread);

    let stack = Arc::into_inner(stack).expect("sole owner");
    let drained: HashSet<usize> = stack.into_iter().collect();
    let expected: HashSet<usize> = (0..THREADS * per_thread).collect();
    assert_eq!(
        drained, expected,
        "every pushed value must survive exactly once"
    );
}

/// The central correctness property: under concurrent producers and consumers,
/// every value is popped exactly once. Duplicates would mean two threads won
/// the same node (ABA); missing values would mean a lost update.
#[test]
fn concurrent_push_and_pop_is_exactly_once() {
    const PRODUCERS: usize = 4;
    const CONSUMERS: usize = 4;
    /// Enough attempts that consumers outlast the producers.
    const ATTEMPTS_PER_ITEM: usize = 4;

    let per_thread = scale(500);
    let total = PRODUCERS * per_thread;

    let stack = Arc::new(Stack::new());
    let barrier = Arc::new(Barrier::new(PRODUCERS + CONSUMERS));
    let popped = Arc::new(Mutex::new(Vec::with_capacity(total)));

    let mut handles = Vec::new();

    for t in 0..PRODUCERS {
        let stack = Arc::clone(&stack);
        let barrier = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            barrier.wait();
            for i in 0..per_thread {
                stack.push(t * per_thread + i);
            }
        }));
    }

    for _ in 0..CONSUMERS {
        let stack = Arc::clone(&stack);
        let barrier = Arc::clone(&barrier);
        let popped = Arc::clone(&popped);
        handles.push(thread::spawn(move || {
            barrier.wait();
            let mut mine = Vec::new();
            for _ in 0..per_thread * ATTEMPTS_PER_ITEM {
                if let Some(v) = stack.pop() {
                    mine.push(v);
                }
            }
            popped.lock().unwrap().extend(mine);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    let mut all = popped.lock().unwrap().clone();
    all.extend(Arc::into_inner(stack).expect("sole owner"));
    all.sort_unstable();

    let expected: Vec<usize> = (0..total).collect();
    assert_eq!(all, expected, "each value must be popped exactly once");
}

/// Exercises the path that Miri flagged as a use-after-free in the previous
/// implementation: `clear` racing concurrent pushes and pops.
#[test]
fn clear_races_pushes_and_pops() {
    const PUSHERS: usize = 2;
    const CLEARERS: usize = 2;
    const POPPERS: usize = 2;
    const CLEARS_PER_THREAD: usize = 5;

    let items = scale(500);
    let stack = Arc::new(Stack::new());

    for i in 0..items {
        stack.push(i);
    }

    let mut handles = Vec::new();

    for t in 0..PUSHERS {
        let stack = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for i in 0..items {
                stack.push(items + t * items + i);
                thread::yield_now();
            }
        }));
    }

    for _ in 0..CLEARERS {
        let stack = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for _ in 0..CLEARS_PER_THREAD {
                stack.clear();
                thread::yield_now();
            }
        }));
    }

    for _ in 0..POPPERS {
        let stack = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for _ in 0..items {
                let _ = stack.pop();
                thread::yield_now();
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}

/// `pop_all` detaches the chain out from under threads that are mid-`pop` and
/// mid-`push`.
#[test]
fn pop_all_races_mutation() {
    const DRAINERS: usize = 2;
    const MUTATORS: usize = 2;
    /// Each drainer sweeps a fraction of the initial contents.
    const DRAINS_PER_THREAD_DIVISOR: usize = 4;

    let items = scale(200);
    let stack = Arc::new(Stack::new());

    for i in 0..items {
        stack.push(i.to_string());
    }

    let mut handles = Vec::new();

    for _ in 0..DRAINERS {
        let stack = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for _ in 0..items / DRAINS_PER_THREAD_DIVISOR {
                let _ = stack.pop_all().count();
                thread::yield_now();
            }
        }));
    }

    for t in 0..MUTATORS {
        let stack = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for i in 0..items {
                if i % 2 == 0 {
                    stack.push(format!("{t}-{i}"));
                } else {
                    let _ = stack.pop();
                }
                thread::yield_now();
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}

/// A tiny scan threshold forces the reclamation path to run constantly, which
/// is where a broken hazard protocol shows up fastest.
#[test]
fn eager_reclamation_stays_sound() {
    const THREADS: usize = 4;
    /// Reclaim on every retirement, so the scan path runs constantly.
    const EAGER: usize = 1;

    let previous = hazard::scan_threshold();
    hazard::set_scan_threshold(EAGER);

    let items = scale(300);
    let stack = Arc::new(Stack::new());
    let barrier = Arc::new(Barrier::new(THREADS));

    let handles: Vec<_> = (0..THREADS)
        .map(|_| {
            let stack = Arc::clone(&stack);
            let barrier = Arc::clone(&barrier);
            thread::spawn(move || {
                barrier.wait();
                for i in 0..items {
                    stack.push(i);
                    let _ = stack.pop();
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }

    hazard::set_scan_threshold(previous);
}
