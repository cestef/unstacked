//! Single-threaded behaviour of the public API.

use unstacked::Stack;

#[test]
fn new_stack_is_empty() {
    let stack: Stack<i32> = Stack::new();
    assert!(stack.is_empty());
    assert_eq!(stack.len(), 0);
    assert_eq!(stack.pop(), None);
}

#[test]
fn default_matches_new() {
    let stack: Stack<i32> = Stack::default();
    assert!(stack.is_empty());
}

#[test]
fn new_is_usable_in_a_static() {
    static STACK: Stack<u32> = Stack::new();
    STACK.push(7);
    assert_eq!(STACK.pop(), Some(7));
}

#[test]
fn pops_in_lifo_order() {
    let stack = Stack::new();
    stack.push(3);
    stack.push(2);
    stack.push(1);

    assert_eq!(stack.len(), 3);
    assert_eq!(stack.pop(), Some(1));
    assert_eq!(stack.pop(), Some(2));
    assert_eq!(stack.pop(), Some(3));
    assert_eq!(stack.pop(), None);
    assert_eq!(stack.len(), 0);
}

#[test]
fn pop_on_empty_is_repeatable() {
    let stack = Stack::new();
    assert_eq!(stack.pop(), None);
    assert_eq!(stack.pop(), None);

    stack.push(1);
    assert_eq!(stack.pop(), Some(1));
    assert_eq!(stack.pop(), None);
}

#[test]
fn holds_non_copy_values() {
    #[derive(Debug, PartialEq)]
    struct Payload {
        id: u32,
        name: String,
    }

    let stack = Stack::new();
    stack.push(Payload {
        id: 1,
        name: "test".to_string(),
    });

    assert_eq!(
        stack.pop(),
        Some(Payload {
            id: 1,
            name: "test".to_string(),
        })
    );
}

#[test]
fn holds_zero_sized_values() {
    let stack = Stack::new();
    stack.push(());
    stack.push(());
    assert_eq!(stack.len(), 2);
    assert_eq!(stack.pop(), Some(()));
    assert_eq!(stack.pop(), Some(()));
    assert_eq!(stack.pop(), None);
}

#[test]
fn peek_does_not_consume() {
    let mut stack = Stack::new();
    assert_eq!(stack.peek(), None);

    stack.push(42);
    assert_eq!(stack.peek(), Some(&42));
    assert_eq!(stack.peek(), Some(&42));
    assert_eq!(stack.len(), 1);

    stack.push(43);
    assert_eq!(stack.peek(), Some(&43));

    assert_eq!(stack.pop(), Some(43));
    assert_eq!(stack.peek(), Some(&42));
}

#[test]
fn peek_borrows_without_consuming() {
    let mut stack = Stack::new();
    stack.push(vec![1, 2, 3]);

    assert_eq!(stack.peek(), Some(&vec![1, 2, 3]));
    assert_eq!(stack.len(), 1);
    assert_eq!(stack.pop(), Some(vec![1, 2, 3]));
}

#[test]
fn pop_all_drains_top_first() {
    let stack = Stack::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);

    assert_eq!(stack.pop_all().collect::<Vec<_>>(), vec![3, 2, 1]);
    assert!(stack.is_empty());
    assert_eq!(stack.len(), 0);
}

#[test]
fn pop_all_on_empty_yields_nothing() {
    let stack: Stack<i32> = Stack::new();
    assert_eq!(stack.pop_all().count(), 0);
}

#[test]
fn dropping_a_partial_drain_discards_the_rest() {
    let stack = Stack::new();
    for i in 0..5 {
        stack.push(i.to_string());
    }

    let mut drain = stack.pop_all();
    assert_eq!(drain.next(), Some("4".to_string()));
    drop(drain);

    assert!(stack.is_empty());
    assert_eq!(stack.len(), 0);
}

#[test]
fn pop_all_leaves_concurrent_pushes_a_fresh_stack() {
    let stack = Stack::new();
    stack.push(1);

    let drain = stack.pop_all();
    // The chain is already detached, so this push builds a new one.
    stack.push(2);

    assert_eq!(drain.collect::<Vec<_>>(), vec![1]);
    assert_eq!(stack.pop(), Some(2));
}

#[test]
fn clear_empties_the_stack() {
    let stack = Stack::new();

    stack.clear();
    assert!(stack.is_empty());

    stack.push(1);
    stack.push(2);
    stack.push(3);
    assert_eq!(stack.len(), 3);

    stack.clear();
    assert!(stack.is_empty());
    assert_eq!(stack.len(), 0);
    assert_eq!(stack.pop(), None);

    stack.push(42);
    assert_eq!(stack.pop(), Some(42));
}

#[test]
fn len_is_available_for_non_clone_values() {
    // Regression: `len` used to require `T: Clone`, because `#[derive(Clone)]`
    // on the internal tagged pointer added a `T: Clone` bound its fields never
    // needed. `NotClone` would not have compiled.
    struct NotClone(#[allow(dead_code)] u32);

    let stack = Stack::new();
    stack.push(NotClone(1));
    stack.push(NotClone(2));
    assert_eq!(stack.len(), 2);
}

#[test]
fn into_iter_yields_top_first() {
    let stack = Stack::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);

    assert_eq!(stack.into_iter().collect::<Vec<_>>(), vec![3, 2, 1]);
}

#[test]
fn into_iter_reports_exact_len() {
    let stack = Stack::new();
    for i in 0..5 {
        stack.push(i);
    }

    let mut iter = stack.into_iter();
    assert_eq!(iter.len(), 5);
    assert_eq!(iter.size_hint(), (5, Some(5)));
    iter.next();
    assert_eq!(iter.len(), 4);
}

#[test]
fn partially_consumed_into_iter_drops_the_rest() {
    let stack = Stack::new();
    for i in 0..5 {
        stack.push(i.to_string());
    }

    let mut iter = stack.into_iter();
    assert_eq!(iter.next(), Some("4".to_string()));
    drop(iter); // remaining four nodes and Strings must be freed
}

#[test]
fn iter_borrows_top_first() {
    let mut stack = Stack::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);

    assert_eq!(stack.iter().copied().collect::<Vec<_>>(), vec![3, 2, 1]);
    // Still usable afterwards: `iter` only borrowed.
    assert_eq!(stack.len(), 3);
    assert_eq!(stack.pop(), Some(3));
}

#[test]
fn collects_from_an_iterator() {
    let stack: Stack<i32> = (1..=3).collect();
    assert_eq!(stack.len(), 3);
    // Last item pushed ends up on top.
    assert_eq!(stack.pop(), Some(3));
}

#[test]
fn extend_pushes_each_item() {
    let mut stack: Stack<i32> = Stack::new();
    stack.extend([1, 2, 3]);
    assert_eq!(stack.len(), 3);
    assert_eq!(stack.pop(), Some(3));
}

#[test]
fn debug_reports_length() {
    let stack = Stack::new();
    stack.push(1);
    stack.push(2);
    assert_eq!(format!("{stack:?}"), "Stack { len: 2, .. }");
}
