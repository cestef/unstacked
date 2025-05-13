#![cfg_attr(not(test), no_std)]

use core::marker::PhantomData;
use core::ptr;
use core::sync::atomic::{AtomicUsize, Ordering};

extern crate alloc;
use alloc::boxed::Box;

#[derive(Clone, Copy)]
pub struct TaggedPtr<T> {
    ptr: *mut Node<T>,
    tag: usize,
}

const NULL_TAG: usize = 0;
const NULL_PTR: *mut Node<()> = ptr::null_mut();

impl<T> TaggedPtr<T> {
    const fn new(ptr: *mut Node<T>, tag: usize) -> Self {
        TaggedPtr { ptr, tag }
    }

    const fn null() -> Self {
        Self {
            ptr: NULL_PTR as *mut Node<T>,
            tag: NULL_TAG,
        }
    }

    const fn is_null(&self) -> bool {
        self.ptr.is_null()
    }

    fn encode(&self) -> usize {
        let ptr_bits = self.ptr as usize;
        let tag_shifted = (self.tag << TAG_SHIFT_BITS) & TAG_MASK;

        let ptr_masked = ptr_bits & PTR_MASK;

        ptr_masked | tag_shifted
    }

    const fn decode(value: usize) -> Self {
        let ptr = (value & PTR_MASK) as *mut Node<T>;

        let tag = (value & TAG_MASK) >> TAG_SHIFT_BITS;

        Self::new(ptr, tag)
    }
}

struct Node<T> {
    data: T,
    next: TaggedPtr<T>,
}

pub struct Stack<T> {
    head: AtomicUsize,
    _marker: PhantomData<T>,
}

const PTR_MASK: usize = 0x0000FFFFFFFFFFFF;
const TAG_MASK: usize = 0xFFFF000000000000;
const TAG_SHIFT_BITS: usize = 48;

/// # Example
/// ```
/// use unstacked::Stack;
/// let stack: Stack<i32> = Stack::new();
/// stack.push(1);
/// assert_eq!(stack.pop(), Some(1));
/// assert_eq!(stack.pop(), None);
/// stack.push(2);
/// assert_eq!(stack.peek(), Some(2).as_ref());
/// assert!(!stack.is_empty())
/// ```
impl<T> Stack<T> {
    pub fn new() -> Self {
        Stack {
            head: AtomicUsize::new(TaggedPtr::<T>::null().encode()),
            _marker: PhantomData,
        }
    }

    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: TaggedPtr::null(),
        }));

        loop {
            let head_bits = self.head.load(Ordering::Acquire);
            let current_head = TaggedPtr::decode(head_bits);
            let current_head_tag = current_head.tag;

            unsafe {
                (*new_node).next = current_head;
            }

            let new_tagged = TaggedPtr::new(new_node, current_head_tag + 1);
            let new_bits = new_tagged.encode();

            match self.head.compare_exchange(
                head_bits,
                new_bits,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => core::hint::spin_loop(),
            }
        }
    }

    pub fn pop(&self) -> Option<T> {
        loop {
            let head_bits = self.head.load(Ordering::Acquire);
            let current_head = TaggedPtr::decode(head_bits);

            if current_head.is_null() {
                return None;
            }

            let next = unsafe { &(*current_head.ptr).next };

            let new_tagged = TaggedPtr::new(next.ptr, current_head.tag + 1);
            let new_bits = new_tagged.encode();

            match self.head.compare_exchange(
                head_bits,
                new_bits,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    let node = unsafe { Box::from_raw(current_head.ptr) };
                    return Some(node.data);
                }
                Err(_) => core::hint::spin_loop(),
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        TaggedPtr::<T>::decode(self.head.load(Ordering::Acquire)).is_null()
    }

    pub fn clear(&self) {
        while self.pop().is_some() {}
    }

    pub fn peek(&self) -> Option<&T> {
        let head_bits = self.head.load(Ordering::Acquire);
        let current_head = TaggedPtr::decode(head_bits);

        if current_head.is_null() {
            None
        } else {
            unsafe { Some(&(*current_head.ptr).data) }
        }
    }
}

impl<T> Stack<T>
where
    T: Clone,
{
    pub fn len(&self) -> usize {
        let mut count = 0;
        let mut current = TaggedPtr::<T>::decode(self.head.load(Ordering::Acquire));

        while !current.is_null() {
            count += 1;
            unsafe {
                current = (*current.ptr).next.clone();
            }
        }

        count
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier};
    use std::thread::{self, JoinHandle};

    #[test]
    fn test_new_stack_is_empty() {
        let stack: Stack<i32> = Stack::new();
        assert!(stack.pop().is_none());
    }

    #[test]
    fn test_push_and_pop_single_element() {
        let stack = Stack::new();
        stack.push(42);

        let value = stack.pop();
        assert_eq!(value, Some(42));
        assert!(stack.pop().is_none());
    }

    #[test]
    fn test_push_and_pop_multiple_elements() {
        let stack = Stack::new();

        stack.push(3);
        stack.push(2);
        stack.push(1);

        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(3));
        assert!(stack.pop().is_none());
    }

    #[test]
    fn test_push_after_pop() {
        let stack = Stack::new();

        stack.push(1);
        assert_eq!(stack.pop(), Some(1));

        stack.push(2);
        assert_eq!(stack.pop(), Some(2));
        assert!(stack.pop().is_none());
    }

    #[test]
    fn test_multiple_pops_when_empty() {
        let stack = Stack::new();

        assert!(stack.pop().is_none());
        assert!(stack.pop().is_none());

        stack.push(1);
        assert_eq!(stack.pop(), Some(1));
        assert!(stack.pop().is_none());
    }

    #[test]
    fn test_push_and_pop_with_custom_type() {
        #[derive(Debug, PartialEq)]
        struct TestStruct {
            id: u32,
            name: String,
        }

        let stack = Stack::new();
        let test_value = TestStruct {
            id: 1,
            name: "test".to_string(),
        };

        stack.push(test_value);

        let popped_value = stack.pop().unwrap();
        assert_eq!(popped_value.id, 1);
        assert_eq!(popped_value.name, "test");
    }

    #[test]
    fn test_concurrent_push() {
        const THREADS: usize = 8;
        const ITEMS_PER_THREAD: usize = 1000;

        let stack = Arc::new(Stack::new());
        let barrier = Arc::new(Barrier::new(THREADS));

        let mut handles = vec![];

        for t in 0..THREADS {
            let stack_clone = Arc::clone(&stack);
            let barrier_clone = Arc::clone(&barrier);

            let handle = thread::spawn(move || {
                barrier_clone.wait();

                for i in 0..ITEMS_PER_THREAD {
                    let value = t * ITEMS_PER_THREAD + i;
                    stack_clone.push(value);
                }
            });

            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let mut count = 0;
        while stack.pop().is_some() {
            count += 1;
        }

        assert_eq!(count, THREADS * ITEMS_PER_THREAD);
    }

    #[test]
    fn test_concurrent_push_and_pop() {
        const THREADS: usize = 4;
        const ITEMS_PER_THREAD: usize = 1000;

        let stack = Arc::new(Stack::new());
        let barrier = Arc::new(Barrier::new(THREADS * 2));

        for i in 0..ITEMS_PER_THREAD {
            stack.push(i);
        }

        let mut handles: Vec<JoinHandle<Result<usize, String>>> = vec![];

        for t in 0..THREADS {
            let stack_clone = Arc::clone(&stack);
            let barrier_clone = Arc::clone(&barrier);

            let handle = thread::spawn(move || {
                barrier_clone.wait();

                for i in 0..ITEMS_PER_THREAD {
                    let value = (t + 1) * ITEMS_PER_THREAD + i;
                    stack_clone.push(value);
                }
                Ok(0)
            });

            handles.push(handle);
        }

        for _ in 0..THREADS {
            let stack_clone = Arc::clone(&stack);
            let barrier_clone = Arc::clone(&barrier);

            let handle = thread::spawn(move || {
                barrier_clone.wait();

                let mut popped_count = 0;
                for _ in 0..ITEMS_PER_THREAD {
                    if stack_clone.pop().is_some() {
                        popped_count += 1;
                    }
                }

                Ok(popped_count)
            });

            handles.push(handle);
        }

        let mut total_popped = 0;
        for handle in handles {
            if let Ok(popped_count) = handle.join().unwrap_or(Ok(0)) {
                total_popped += popped_count;
            }
        }

        let mut remaining_count = 0;
        while stack.pop().is_some() {
            remaining_count += 1;
        }

        assert_eq!(
            total_popped + remaining_count,
            ITEMS_PER_THREAD * (THREADS + 1)
        );
    }

    #[test]
    fn test_tagged_ptr_operations() {
        let null_ptr: TaggedPtr<i32> = TaggedPtr::null();
        assert!(null_ptr.is_null());

        let node = Box::into_raw(Box::new(Node {
            data: 42,
            next: TaggedPtr::null(),
        }));

        let tagged = TaggedPtr::new(node, 5);
        assert!(!tagged.is_null());
        assert_eq!(tagged.tag, 5);

        unsafe {
            let _ = Box::from_raw(node);
        }
    }

    #[test]
    fn test_encode_decode() {
        let null_ptr = TaggedPtr::<i32>::null();
        let encoded = null_ptr.encode();
        let decoded = TaggedPtr::<i32>::decode(encoded);

        assert!(decoded.is_null());
        assert_eq!(decoded.tag, 0);

        let node = Box::into_raw(Box::new(Node {
            data: 123,
            next: TaggedPtr::null(),
        }));

        let tagged = TaggedPtr::new(node, 42);
        let encoded = tagged.encode();
        let decoded = TaggedPtr::<i32>::decode(encoded);

        assert_eq!(decoded.ptr, node);
        assert_eq!(decoded.tag, 42);

        unsafe {
            let _ = Box::from_raw(node);
        }
    }

    #[test]
    fn test_tag_increment_on_operations() {
        let stack = Stack::new();

        stack.push(1);

        let head_bits = stack.head.load(Ordering::Acquire);
        let head = TaggedPtr::<i32>::decode(head_bits);
        let tag_after_push = head.tag;

        let _ = stack.pop();

        let head_bits_after_pop = stack.head.load(Ordering::Acquire);
        let head_after_pop = TaggedPtr::<i32>::decode(head_bits_after_pop);

        assert!(head_after_pop.tag > tag_after_push);
    }

    #[test]
    fn test_aba_problem_prevention() {
        let stack = Arc::new(Stack::new());

        stack.push(3);
        stack.push(2);
        stack.push(1);

        let head_bits = stack.head.load(Ordering::Acquire);

        let one = stack.pop();
        let _two = stack.pop();

        if let Some(value) = one {
            stack.push(value);
        }

        let current_head_bits = stack.head.load(Ordering::Acquire);
        let _current_head = TaggedPtr::<i32>::decode(current_head_bits);

        let result = stack.head.compare_exchange(
            head_bits,
            current_head_bits,
            Ordering::Release,
            Ordering::Relaxed,
        );

        assert!(result.is_err());
    }

    #[test]
    fn test_is_empty() {
        let stack = Stack::new();

        assert!(stack.is_empty());

        stack.push(42);
        assert!(!stack.is_empty());

        let _ = stack.pop();
        assert!(stack.is_empty());

        stack.push(1);
        stack.push(2);
        assert!(!stack.is_empty());

        let _ = stack.pop();
        let _ = stack.pop();
        assert!(stack.is_empty());
    }

    #[test]
    fn test_len() {
        let stack = Stack::new();

        assert_eq!(stack.len(), 0);

        stack.push(42);
        assert_eq!(stack.len(), 1);

        stack.push(43);
        stack.push(44);
        assert_eq!(stack.len(), 3);

        let _ = stack.pop();
        assert_eq!(stack.len(), 2);
        let _ = stack.pop();
        assert_eq!(stack.len(), 1);
        let _ = stack.pop();
        assert_eq!(stack.len(), 0);

        let _ = stack.pop();
        assert_eq!(stack.len(), 0);
    }

    #[test]
    fn test_clear() {
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
        assert!(stack.pop().is_none());

        stack.push(42);
        assert_eq!(stack.len(), 1);
        assert_eq!(stack.pop(), Some(42));
    }

    #[test]
    fn test_peek() {
        let stack = Stack::new();

        assert!(stack.peek().is_none());

        stack.push(42);
        assert_eq!(*stack.peek().unwrap(), 42);

        assert_eq!(*stack.peek().unwrap(), 42);
        assert_eq!(stack.len(), 1);

        stack.push(43);
        assert_eq!(*stack.peek().unwrap(), 43);

        stack.push(44);
        assert_eq!(*stack.peek().unwrap(), 44);

        let _ = stack.pop();
        assert_eq!(*stack.peek().unwrap(), 43);

        let _ = stack.pop();
        let _ = stack.pop();
        assert!(stack.peek().is_none());
    }

    #[test]
    fn test_peek_and_modify() {
        let stack = Stack::new();
        stack.push(vec![1, 2, 3]);

        if let Some(data) = stack.peek() {
            assert_eq!(data, &vec![1, 2, 3]);
        }

        let popped_data = stack.pop().unwrap();
        assert_eq!(popped_data, vec![1, 2, 3]);
    }

    #[test]
    fn test_clear_concurrent() {
        const THREADS: usize = 4;
        const ITEMS: usize = 1000;

        let stack = Arc::new(Stack::new());

        for i in 0..ITEMS {
            stack.push(i);
        }

        let mut handles = vec![];

        for t in 0..THREADS / 2 {
            let stack_clone = Arc::clone(&stack);

            let handle = thread::spawn(move || {
                for i in 0..ITEMS / 10 {
                    stack_clone.push(ITEMS + t * ITEMS / 10 + i);
                    thread::yield_now();
                }
            });

            handles.push(handle);
        }

        for _ in 0..THREADS / 2 {
            let stack_clone = Arc::clone(&stack);

            let handle = thread::spawn(move || {
                for _ in 0..5 {
                    stack_clone.clear();
                    thread::yield_now();
                }
            });

            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }
    }

    #[test]
    fn test_peek_concurrent() {
        const THREADS: usize = 4;
        const ITEMS: usize = 100;

        let stack = Arc::new(Stack::new());

        for i in 0..ITEMS {
            stack.push(i);
        }

        let mut handles = vec![];

        for _ in 0..THREADS / 2 {
            let stack_clone = Arc::clone(&stack);

            let handle = thread::spawn(move || {
                for _ in 0..ITEMS {
                    if let Some(_) = stack_clone.peek() {
                    } else {
                    }
                    thread::yield_now();
                }
            });

            handles.push(handle);
        }

        for t in 0..THREADS / 2 {
            let stack_clone = Arc::clone(&stack);

            let handle = thread::spawn(move || {
                for i in 0..ITEMS {
                    if i % 2 == 0 {
                        stack_clone.push(ITEMS + t * ITEMS + i);
                    } else {
                        let _ = stack_clone.pop();
                    }
                    thread::yield_now();
                }
            });

            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }
    }
}
