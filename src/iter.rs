use alloc::boxed::Box;
use core::fmt;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::ptr;
use core::sync::atomic::{AtomicUsize, Ordering};

use crate::hazard::{Lease, lease};
use crate::node::Node;
use crate::stack::Stack;

/// Owning iterator over a [`Stack`], yielding values top-first.
///
/// Created by [`Stack::into_iter`]. The stack is consumed, so the chain is
/// walked under exclusive ownership and freed directly.
pub struct IntoIter<T> {
    node: *mut Node<T>,
    len: usize,
}

// SAFETY: `IntoIter` exclusively owns its chain, so sending it sends the `T`s.
unsafe impl<T: Send> Send for IntoIter<T> {}
// SAFETY: `&IntoIter<T>` exposes no more than `&T` would.
unsafe impl<T: Sync> Sync for IntoIter<T> {}

impl<T> IntoIter<T> {
    pub(crate) fn new(node: *mut Node<T>, len: usize) -> Self {
        IntoIter { node, len }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.node.is_null() {
            return None;
        }
        let node = self.node;
        // SAFETY: the chain is exclusively ours, and each node came from
        // `Box::into_raw` and has not been freed.
        unsafe {
            self.node = (*node).next;
            let data = Node::take_payload(node);
            drop(Box::from_raw(node));
            self.len -= 1;
            Some(data)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> FusedIterator for IntoIter<T> {}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        for _ in self.by_ref() {}
    }
}

impl<T> fmt::Debug for IntoIter<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IntoIter")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

impl<T> IntoIterator for Stack<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(mut self) -> IntoIter<T> {
        self.take_chain()
    }
}

/// Draining iterator over a [`Stack`], yielding values top-first.
///
/// Created by [`Stack::pop_all`]. The chain was detached with one atomic swap,
/// so its payloads are exclusively ours, but a concurrent `pop` may still hold
/// a protection into it, so the nodes go back through the hazard registry
/// instead of being freed here.
pub struct Drain<'a, T> {
    node: *mut Node<T>,
    len: &'a AtomicUsize,
    lease: Lease,
}

impl<'a, T> Drain<'a, T> {
    pub(crate) fn new(node: *mut Node<T>, len: &'a AtomicUsize) -> Self {
        Drain {
            node,
            len,
            lease: lease(),
        }
    }
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.node.is_null() {
            return None;
        }
        let node = self.node;
        // SAFETY: the chain is detached and unreachable from the stack, so no
        // other thread can win these nodes or their payloads.
        unsafe {
            self.node = (*node).next;
            let data = Node::take_payload(node);
            self.lease.retire(node);
            self.len.fetch_sub(1, Ordering::Relaxed);
            Some(data)
        }
    }
}

impl<T> FusedIterator for Drain<'_, T> {}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        for _ in self.by_ref() {}
    }
}

impl<T> fmt::Debug for Drain<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Drain").finish_non_exhaustive()
    }
}

/// Borrowing iterator over a [`Stack`], yielding references top-first.
///
/// Needs `&mut` for the same reason [`Stack::peek`] does.
pub struct Iter<'a, T> {
    node: *mut Node<T>,
    len: usize,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.node.is_null() {
            return None;
        }
        // SAFETY: the stack is borrowed for `'a`, so nothing can pop or reclaim
        // these nodes while the iterator lives.
        unsafe {
            let data = &(*self.node).data;
            self.node = (*self.node).next;
            self.len -= 1;
            Some(data)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<T> FusedIterator for Iter<'_, T> {}

impl<T> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Iter")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

impl<'a, T> IntoIterator for &'a mut Stack<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        Iter {
            node: *self.head.get_mut(),
            len: *self.len.get_mut(),
            _marker: PhantomData,
        }
    }
}

impl<T> Stack<T> {
    /// Returns an iterator over the stack's values, top-first.
    pub fn iter(&mut self) -> Iter<'_, T> {
        self.into_iter()
    }

    /// Detaches the chain, leaving the stack empty.
    pub(crate) fn take_chain(&mut self) -> IntoIter<T> {
        let node = core::mem::replace(self.head.get_mut(), ptr::null_mut());
        IntoIter::new(node, core::mem::replace(self.len.get_mut(), 0))
    }
}

impl<T> FromIterator<T> for Stack<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let stack = Stack::new();
        stack.extend_shared(iter);
        stack
    }
}

impl<T> Extend<T> for Stack<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.extend_shared(iter);
    }
}
