use alloc::boxed::Box;
use core::mem::ManuallyDrop;
use core::ptr;

/// A single stack cell.
///
/// # Payload ownership
///
/// A hazard pointer keeps a node's *allocation* alive, not its payload, which
/// the winner of the `head` compare-and-swap moves out. So `data` may only be
/// touched by a thread holding exclusive logical ownership of the node: one
/// that won that compare-and-swap, that detached the whole chain, or that holds
/// `&mut Stack`. Hazard protection alone is not enough.
///
/// `data` is a [`ManuallyDrop`] so that reclaiming the allocation after the
/// payload has been moved out does not run drop glue for `T` a second time.
pub(crate) struct Node<T> {
    pub(crate) data: ManuallyDrop<T>,
    pub(crate) next: *mut Node<T>,
}

impl<T> Node<T> {
    pub(crate) fn alloc(data: T) -> *mut Self {
        Box::into_raw(Box::new(Node {
            data: ManuallyDrop::new(data),
            next: ptr::null_mut(),
        }))
    }

    /// # Safety
    /// `node` must be live and exclusively owned, and its payload must not have
    /// been taken or dropped already.
    pub(crate) unsafe fn take_payload(node: *mut Self) -> T {
        // SAFETY: guaranteed by the caller.
        unsafe { ManuallyDrop::take(&mut (*node).data) }
    }
}
