use core::fmt;
use core::marker::PhantomData;
use core::ptr;
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

use crate::hazard::lease;
use crate::iter::Drain;
use crate::node::Node;

/// A lock-free, concurrent LIFO stack.
///
/// Every operation takes `&self`, so one stack can be shared across threads and
/// pushed to and popped from concurrently without external synchronisation.
///
/// # Memory reclamation
///
/// Popped nodes are not freed immediately; they are handed to the
/// [`hazard`](crate::hazard) registry and freed once no thread can still be
/// looking at them. This is what makes concurrent `pop` sound, and it means a
/// bounded amount of memory can outlive the values it held. See
/// [`hazard::collect`](crate::hazard::collect) and
/// [`hazard::set_scan_threshold`](crate::hazard::set_scan_threshold).
///
/// # Examples
///
/// ```
/// use unstacked::Stack;
///
/// let stack = Stack::new();
/// stack.push(1);
/// stack.push(2);
///
/// assert_eq!(stack.pop(), Some(2));
/// assert_eq!(stack.pop(), Some(1));
/// assert_eq!(stack.pop(), None);
/// ```
///
/// `Sync` requires `T: Send`, because `pop` hands an owned `T` out through a
/// shared reference. A type that is `Sync` but not `Send` must therefore not
/// make the stack `Sync`:
///
/// ```compile_fail
/// use std::sync::MutexGuard;
/// use unstacked::Stack;
///
/// fn assert_sync<T: Sync>() {}
/// assert_sync::<Stack<MutexGuard<'static, i32>>>();
/// ```
pub struct Stack<T> {
    pub(crate) head: AtomicPtr<Node<T>>,
    pub(crate) len: AtomicUsize,
    _marker: PhantomData<T>,
}

// SAFETY: `Stack` owns its values, so moving it to another thread moves the
// `T`s with it.
unsafe impl<T: Send> Send for Stack<T> {}

// SAFETY: a shared `&Stack<T>` hands out owned `T`s via `pop`, which needs
// `T: Send` — a bound the auto-derived impl would not have required — and `&T`
// via iteration, which needs `T: Sync`.
unsafe impl<T: Send + Sync> Sync for Stack<T> {}

impl<T> Stack<T> {
    /// Creates an empty stack. Does not allocate.
    #[must_use]
    pub const fn new() -> Self {
        Stack {
            head: AtomicPtr::new(ptr::null_mut()),
            len: AtomicUsize::new(0),
            _marker: PhantomData,
        }
    }

    /// Pushes a value onto the top of the stack.
    pub fn push(&self, data: T) {
        let node = Node::alloc(data);

        // Counted before it becomes reachable, so a pop can never decrement for
        // a node that was not yet counted and underflow `len`.
        self.len.fetch_add(1, Ordering::Relaxed);

        let mut head = self.head.load(Ordering::Acquire);
        loop {
            // SAFETY: `node` is not yet published, so we hold it exclusively.
            unsafe { (*node).next = head };

            match self
                .head
                .compare_exchange_weak(head, node, Ordering::AcqRel, Ordering::Acquire)
            {
                Ok(_) => return,
                Err(actual) => {
                    head = actual;
                    core::hint::spin_loop();
                }
            }
        }
    }

    /// Pushes every item of an iterator, through a shared reference.
    ///
    /// [`Extend`] needs `&mut self`; this is the same operation without that
    /// requirement.
    pub fn extend_shared<I: IntoIterator<Item = T>>(&self, iter: I) {
        for item in iter {
            self.push(item);
        }
    }

    /// Pops the top value, or returns `None` if the stack is empty.
    pub fn pop(&self) -> Option<T> {
        let guard = lease();

        loop {
            let head = guard.protect(&self.head);
            if head.is_null() {
                return None;
            }

            // SAFETY: `head` is published in our hazard slot and was validated
            // afterwards as still being `self.head`, so it cannot be reclaimed
            // while this lease lives.
            let next = unsafe { (*head).next };

            match self
                .head
                .compare_exchange_weak(head, next, Ordering::AcqRel, Ordering::Acquire)
            {
                Ok(_) => {
                    self.len.fetch_sub(1, Ordering::Relaxed);
                    // SAFETY: winning the compare-exchange unlinked `head` and
                    // gave us sole claim to its payload.
                    let data = unsafe { Node::take_payload(head) };
                    // SAFETY: unlinked, payload moved out, not retired before.
                    unsafe { guard.retire(head) };
                    return Some(data);
                }
                Err(_) => core::hint::spin_loop(),
            }
        }
    }

    /// Detaches every value at once and returns an iterator over them,
    /// top-first.
    ///
    /// One atomic swap takes the whole chain, where a `while let Some(v) =
    /// stack.pop()` loop would need `N` compare-and-swaps, and concurrent
    /// pushes immediately start building a fresh stack rather than competing
    /// with the drain. Dropping the [`Drain`] discards what was not consumed.
    ///
    /// ```
    /// use unstacked::Stack;
    ///
    /// let stack = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    ///
    /// assert_eq!(stack.pop_all().collect::<Vec<_>>(), vec![2, 1]);
    /// assert!(stack.is_empty());
    /// ```
    pub fn pop_all(&self) -> Drain<'_, T> {
        Drain::new(self.head.swap(ptr::null_mut(), Ordering::AcqRel), &self.len)
    }

    /// Removes every value, dropping them.
    pub fn clear(&self) {
        drop(self.pop_all());
    }

    /// Returns `true` if the stack held no values at the moment it was observed.
    pub fn is_empty(&self) -> bool {
        self.head.load(Ordering::Acquire).is_null()
    }

    /// Returns the number of values in the stack.
    ///
    /// `O(1)`. Under concurrent access this is a snapshot that may over-report
    /// while operations are in flight; it is exact when the stack is quiescent.
    pub fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    /// Returns a reference to the top value.
    ///
    /// Takes `&mut self` on purpose: with a shared `&self`, a concurrent or
    /// even same-thread `pop` could free the node while the returned reference
    /// was still live. There is deliberately no shared-access peek, because
    /// hazard protection keeps a node's allocation alive but not its payload,
    /// which the winner of the `head` compare-and-swap moves out.
    ///
    /// ```
    /// use unstacked::Stack;
    ///
    /// let mut stack = Stack::new();
    /// stack.push(1);
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    ///
    /// Holding the reference across a `pop` is rejected at compile time:
    ///
    /// ```compile_fail
    /// use unstacked::Stack;
    ///
    /// let mut stack = Stack::new();
    /// stack.push("a heap string".to_string());
    ///
    /// let borrowed = stack.peek().unwrap();
    /// let owned = stack.pop().unwrap();
    /// drop(owned);
    /// println!("{borrowed}");
    /// ```
    pub fn peek(&mut self) -> Option<&T> {
        let head = *self.head.get_mut();
        if head.is_null() {
            return None;
        }
        // SAFETY: `&mut self` rules out concurrent access, and the borrow is
        // tied to `self`'s lifetime.
        Some(unsafe { &(*head).data })
    }
}

impl<T> Default for Stack<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for Stack<T> {
    fn drop(&mut self) {
        // `&mut self` means no hazard protection can point into this chain, so
        // it can be freed directly rather than retired.
        drop(self.take_chain());
    }
}

impl<T> fmt::Debug for Stack<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Stack")
            .field("len", &self.len())
            .finish_non_exhaustive()
    }
}
