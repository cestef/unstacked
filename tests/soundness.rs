//! Regression tests for the specific unsoundness fixed in 0.2.0.
//!
//! The negative cases (code that *must not* compile) live as `compile_fail`
//! doctests on `Stack`, since a test binary cannot assert that something fails
//! to build.

use std::sync::{Arc, Mutex};
use unstacked::{Stack, hazard};

fn assert_send<T: Send>() {}
fn assert_sync<T: Sync>() {}

#[test]
fn auto_trait_bounds_are_correct() {
    // `pop(&self)` moves a `T` out through a shared reference, so `Sync`
    // must require `T: Send` and not merely `T: Sync`. The previously
    // auto-derived impls got this wrong.
    assert_send::<Stack<i32>>();
    assert_sync::<Stack<i32>>();
    assert_send::<Stack<String>>();
    assert_sync::<Stack<Arc<Mutex<i32>>>>();
}

#[test]
fn dropping_a_populated_stack_frees_everything() {
    // Regression: `Stack` had no `Drop`, so every remaining node and payload
    // leaked. Under Miri this test fails loudly if the leak returns.
    struct Tracked(Arc<Mutex<usize>>);
    impl Drop for Tracked {
        fn drop(&mut self) {
            *self.0.lock().unwrap() += 1;
        }
    }

    let drops = Arc::new(Mutex::new(0));
    {
        let stack = Stack::new();
        for _ in 0..8 {
            stack.push(Tracked(Arc::clone(&drops)));
        }
        assert_eq!(*drops.lock().unwrap(), 0);
    }
    assert_eq!(*drops.lock().unwrap(), 8, "drop must run for every value");
}

#[test]
fn clear_drops_every_payload() {
    struct Tracked(Arc<Mutex<usize>>);
    impl Drop for Tracked {
        fn drop(&mut self) {
            *self.0.lock().unwrap() += 1;
        }
    }

    let drops = Arc::new(Mutex::new(0));
    let stack = Stack::new();
    for _ in 0..5 {
        stack.push(Tracked(Arc::clone(&drops)));
    }

    stack.clear();
    assert_eq!(*drops.lock().unwrap(), 5);
}

#[test]
fn popped_values_are_not_double_dropped() {
    struct Tracked(Arc<Mutex<usize>>);
    impl Drop for Tracked {
        fn drop(&mut self) {
            *self.0.lock().unwrap() += 1;
        }
    }

    let drops = Arc::new(Mutex::new(0));
    let stack = Stack::new();
    stack.push(Tracked(Arc::clone(&drops)));

    let value = stack.pop().unwrap();
    assert_eq!(*drops.lock().unwrap(), 0, "moving out must not drop");
    drop(value);
    assert_eq!(*drops.lock().unwrap(), 1);

    // Reclaiming the node must free the allocation without re-dropping.
    hazard::collect();
    assert_eq!(*drops.lock().unwrap(), 1, "reclamation must not drop again");
}

#[test]
fn retired_nodes_are_reclaimed() {
    let previous = hazard::scan_threshold();
    hazard::set_scan_threshold(4);

    let stack = Stack::new();
    for i in 0..32 {
        stack.push(i);
        assert_eq!(stack.pop(), Some(i));
    }

    hazard::collect();
    hazard::set_scan_threshold(previous);
}

#[test]
fn scan_threshold_is_clamped() {
    let previous = hazard::scan_threshold();
    hazard::set_scan_threshold(0);
    assert_eq!(hazard::scan_threshold(), hazard::MIN_SCAN_THRESHOLD);
    hazard::set_scan_threshold(previous);
}

#[test]
fn a_drop_impl_may_re_enter_the_same_stack() {
    // With the `std` feature a thread caches one hazard guard, so an operation
    // that runs user code which re-enters the stack must not clobber the
    // in-flight protection. Nothing in the crate calls back into user code
    // while holding the cached guard today, so this is a guard-rail against
    // that changing.
    use std::sync::Weak;

    struct Reentrant {
        stack: Weak<Stack<Reentrant>>,
        depth: usize,
    }

    impl Drop for Reentrant {
        fn drop(&mut self) {
            if self.depth == 0 {
                return;
            }
            if let Some(stack) = self.stack.upgrade() {
                // Popping here drops another `Reentrant`, recursing.
                let _ = stack.pop();
            }
        }
    }

    let stack: Arc<Stack<Reentrant>> = Arc::new(Stack::new());
    for depth in 0..8 {
        stack.push(Reentrant {
            stack: Arc::downgrade(&stack),
            depth,
        });
    }

    // Draining runs each payload's `Drop`, which pops again.
    stack.clear();
    assert!(stack.is_empty());
}
