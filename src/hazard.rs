//! A dependency-free hazard pointer registry.
//!
//! # Why this exists
//!
//! A Treiber stack pops by reading `head`, dereferencing it for `head.next`,
//! then swinging `head` to `next`. Between the read and the dereference another
//! thread may pop and free that node, so the dereference is a use-after-free.
//! Tagged pointers do not fix this: a tag stops a stale compare-and-swap from
//! succeeding, it does not keep the memory alive long enough to be read.
//!
//! Before dereferencing a node, a thread publishes its address in a globally
//! visible slot and re-validates that the node is still reachable. A thread
//! that wants to free a node first scans every slot, and defers any node it
//! finds published.
//!
//! # ABA
//!
//! Protecting a node also removes the need for tagging. A protected node cannot
//! be freed, so the allocator cannot hand its address back out, so `head`
//! cannot return to that address holding a different `next`.
//!
//! # Memory behaviour
//!
//! Slots are allocated on demand and reused but never freed, so the registry
//! settles at the peak number of concurrent operations. Retired nodes live on
//! the retiring slot's private list until a scan reclaims them; see
//! [`collect`].

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering, fence};

/// Retired nodes a slot accumulates before it scans and reclaims.
pub const DEFAULT_SCAN_THRESHOLD: usize = 64;

/// Smallest threshold that still makes progress: reclaim on every retirement.
pub const MIN_SCAN_THRESHOLD: usize = 1;

static SCAN_THRESHOLD: AtomicUsize = AtomicUsize::new(DEFAULT_SCAN_THRESHOLD);
static REGISTRY: AtomicPtr<Slot> = AtomicPtr::new(ptr::null_mut());
static SLOT_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Sets how many retired nodes a thread buffers before attempting reclamation.
///
/// Larger values amortise the scan over more retirements at the cost of holding
/// more garbage. Clamped to at least [`MIN_SCAN_THRESHOLD`].
pub fn set_scan_threshold(threshold: usize) {
    SCAN_THRESHOLD.store(threshold.max(MIN_SCAN_THRESHOLD), Ordering::Relaxed);
}

/// Returns the current scan threshold.
pub fn scan_threshold() -> usize {
    SCAN_THRESHOLD.load(Ordering::Relaxed)
}

/// Returns how many hazard slots have been allocated.
///
/// Settles at the peak number of concurrent operations.
pub fn registry_len() -> usize {
    SLOT_COUNT.load(Ordering::Relaxed)
}

/// A node awaiting reclamation, with its type erased.
struct Retired {
    ptr: *mut (),
    reclaim: unsafe fn(*mut ()),
}

struct Slot {
    protected: AtomicPtr<()>,
    active: AtomicBool,
    next: AtomicPtr<Slot>,
    retired: UnsafeCell<Vec<Retired>>,
}

// SAFETY: `retired` is guarded by `active`: exactly one thread can win the
// `false -> true` compare-exchange, and only that thread dereferences the
// `UnsafeCell` before storing `false` again. Every other field is atomic.
unsafe impl Sync for Slot {}
// SAFETY: a `Slot` holds no thread-affine state; ownership transfers through
// `active`'s release/acquire pair.
unsafe impl Send for Slot {}

fn acquire_slot() -> *const Slot {
    let mut cur = REGISTRY.load(Ordering::Acquire);
    while !cur.is_null() {
        // SAFETY: registered slots are never freed.
        let slot = unsafe { &*cur };
        if !slot.active.load(Ordering::Relaxed)
            && slot
                .active
                .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
        {
            return cur;
        }
        cur = slot.next.load(Ordering::Acquire);
    }

    let slot = Box::into_raw(Box::new(Slot {
        protected: AtomicPtr::new(ptr::null_mut()),
        active: AtomicBool::new(true),
        next: AtomicPtr::new(ptr::null_mut()),
        retired: UnsafeCell::new(Vec::new()),
    }));

    let mut head = REGISTRY.load(Ordering::Acquire);
    loop {
        // SAFETY: `slot` is not yet published, so we hold it exclusively.
        unsafe { (*slot).next.store(head, Ordering::Relaxed) };
        match REGISTRY.compare_exchange_weak(head, slot, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => {
                SLOT_COUNT.fetch_add(1, Ordering::Relaxed);
                return slot;
            }
            Err(actual) => {
                head = actual;
                core::hint::spin_loop();
            }
        }
    }
}

/// An owned hazard slot. Dropping it clears the protection and frees the slot
/// for reuse.
///
/// Deliberately not `Send`: the slot's private retire list belongs to the
/// thread that claimed it.
pub(crate) struct Guard {
    slot: *const Slot,
}

impl Guard {
    fn new() -> Self {
        Guard {
            slot: acquire_slot(),
        }
    }

    fn slot(&self) -> &Slot {
        // SAFETY: slots are never freed, and this guard owns `self.slot`.
        unsafe { &*self.slot }
    }

    /// Publishes and validates a protection for whatever `src` holds, returning
    /// a pointer that will not be reclaimed while the protection stands.
    pub(crate) fn protect<T>(&self, src: &AtomicPtr<T>) -> *mut T {
        let slot = self.slot();
        loop {
            let candidate = src.load(Ordering::Acquire);
            slot.protected.store(candidate.cast(), Ordering::SeqCst);

            // Release/acquire would permit StoreLoad reordering, letting a
            // scanner miss this publication and free the node before the
            // re-read. Sequential consistency puts the publication, the
            // validation below and the scanner's read in one total order, so a
            // scanner that misses us must also have unlinked the node, which
            // the validation then observes.
            fence(Ordering::SeqCst);

            if src.load(Ordering::SeqCst) == candidate {
                return candidate;
            }
            core::hint::spin_loop();
        }
    }

    fn clear(&self) {
        self.slot()
            .protected
            .store(ptr::null_mut(), Ordering::Release);
    }

    /// Defers reclamation of `ptr` until no slot protects it.
    ///
    /// # Safety
    /// `ptr` must come from `Box::into_raw`, must not already be retired or
    /// freed, must be unreachable from the data structure, and its payload must
    /// already have been moved out or dropped.
    pub(crate) unsafe fn retire<T>(&self, ptr: *mut T) {
        /// # Safety
        /// `p` must be a live `Box::into_raw`-derived `*mut T`.
        unsafe fn reclaim<T>(p: *mut ()) {
            // SAFETY: guaranteed by `retire`'s contract.
            drop(unsafe { Box::from_raw(p.cast::<T>()) });
        }

        // SAFETY: we own this slot, so `retired` is ours alone.
        let retired = unsafe { &mut *self.slot().retired.get() };
        retired.push(Retired {
            ptr: ptr.cast(),
            reclaim: reclaim::<T>,
        });

        if retired.len() >= scan_threshold() {
            scan(retired);
        }
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        let slot = self.slot();
        slot.protected.store(ptr::null_mut(), Ordering::Release);
        // Released last: it publishes our writes to `retired` to the next owner.
        slot.active.store(false, Ordering::Release);
    }
}

fn protected_addresses() -> Vec<*mut ()> {
    // Pairs with the fence in `Guard::protect`.
    fence(Ordering::SeqCst);

    let mut protected = Vec::new();
    let mut cur = REGISTRY.load(Ordering::Acquire);
    while !cur.is_null() {
        // SAFETY: registered slots are never freed.
        let slot = unsafe { &*cur };
        let p = slot.protected.load(Ordering::SeqCst);
        if !p.is_null() {
            protected.push(p);
        }
        cur = slot.next.load(Ordering::Acquire);
    }
    protected.sort_unstable();
    protected
}

fn scan(retired: &mut Vec<Retired>) {
    let protected = protected_addresses();
    retired.retain(|entry| {
        if protected.binary_search(&entry.ptr).is_ok() {
            return true;
        }
        // SAFETY: no slot protects `entry.ptr`, and `retire`'s contract
        // guarantees it is live, unreachable and exclusively ours to free.
        unsafe { (entry.reclaim)(entry.ptr) };
        false
    });
}

/// Eagerly reclaims retired nodes that are no longer protected.
///
/// Only unclaimed slots can be drained, so this makes no progress against
/// garbage held by threads that are mid-operation. It is a best-effort hint.
pub fn collect() {
    let mut cur = REGISTRY.load(Ordering::Acquire);
    while !cur.is_null() {
        // SAFETY: registered slots are never freed.
        let slot = unsafe { &*cur };
        if slot
            .active
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            // SAFETY: we just claimed the slot, so `retired` is ours alone.
            scan(unsafe { &mut *slot.retired.get() });
            slot.active.store(false, Ordering::Release);
        }
        cur = slot.next.load(Ordering::Acquire);
    }
}

/// A hazard guard borrowed for the duration of one operation.
///
/// With the `std` feature the [`Guard`] returns to a thread-local cache on
/// drop, so a thread claims a registry slot once rather than per operation. A
/// reentrant lease finds the cache empty and claims its own slot, so nested
/// operations never share a protection.
pub(crate) struct Lease {
    guard: ManuallyDrop<Guard>,
}

impl Deref for Lease {
    type Target = Guard;

    fn deref(&self) -> &Guard {
        &self.guard
    }
}

impl Drop for Lease {
    fn drop(&mut self) {
        self.guard.clear();
        // SAFETY: `guard` is live and this is the only place it is taken.
        release(unsafe { ManuallyDrop::take(&mut self.guard) });
    }
}

pub(crate) fn lease() -> Lease {
    Lease {
        guard: ManuallyDrop::new(claim()),
    }
}

#[cfg(not(feature = "std"))]
fn claim() -> Guard {
    Guard::new()
}

#[cfg(not(feature = "std"))]
fn release(_guard: Guard) {}

#[cfg(feature = "std")]
std::thread_local! {
    static CACHED: core::cell::Cell<Option<Guard>> = const { core::cell::Cell::new(None) };
}

#[cfg(feature = "std")]
fn claim() -> Guard {
    CACHED
        .try_with(core::cell::Cell::take)
        .ok()
        .flatten()
        .unwrap_or_else(Guard::new)
}

#[cfg(feature = "std")]
fn release(guard: Guard) {
    // On failure the closure is dropped unrun, dropping `guard` and returning
    // its slot to the registry.
    let _ = CACHED.try_with(|cached| cached.set(Some(guard)));
}
