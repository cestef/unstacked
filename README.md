<p align="center">
    <img src="https://raw.githubusercontent.com/cestef/unstacked/main/assets/banner.png" alt="unstacked banner" />
</p>

Concurrent, lock-free, `no_std` stack for Rust.

- Treiber stack driven by atomic compare-and-exchange, with no locks anywhere
- Safe concurrent `pop` via built-in [hazard pointers](https://en.wikipedia.org/wiki/Hazard_pointer), so a node is never freed while another thread may still read it
- Immune to the [ABA problem](https://en.wikipedia.org/wiki/ABA_problem): a protected node cannot be reclaimed, so its address cannot be recycled underneath a racing thread
- No dependencies, `no_std` + `alloc`, works on 16-, 32- and 64-bit targets

## Example

```rust
use unstacked::Stack;

let stack = Stack::new();
stack.push(1);
assert_eq!(stack.pop(), Some(1));
assert_eq!(stack.pop(), None);

stack.push(2);
assert!(!stack.is_empty());
assert_eq!(stack.len(), 1);
```

Drain everything in one atomic swap instead of `N` compare-and-swaps:

```rust
use unstacked::Stack;

let stack: Stack<u32> = (1..=3).collect();
assert_eq!(stack.pop_all().collect::<Vec<_>>(), vec![3, 2, 1]);
assert!(stack.is_empty());
```

Sharing one stack across threads:

```rust
use std::sync::Arc;
use std::thread;
use unstacked::Stack;

let stack = Arc::new(Stack::new());

let producers: Vec<_> = (0..4)
    .map(|t| {
        let stack = Arc::clone(&stack);
        thread::spawn(move || {
            for i in 0..100 {
                stack.push(t * 100 + i);
            }
        })
    })
    .collect();

for p in producers {
    p.join().unwrap();
}

assert_eq!(stack.len(), 400);
```

## Reclamation

`pop` cannot free a node right away: another thread may have read the same
`head` and still be about to dereference it. Instead the node is *retired* and
freed later, once no thread has it published in a hazard slot.

That trade is tunable:

```rust
use unstacked::hazard;

// Reclaim more eagerly (default: 64 retired nodes per thread).
hazard::set_scan_threshold(8);

// Or force a sweep now, e.g. at the end of a test.
hazard::collect();
```

The hazard registry itself grows to the peak number of concurrent operations
and is then reused forever; it is never freed. This is a bounded, intentional
leak, and the reason the test suite runs Miri with `-Zmiri-ignore-leaks`.
`hazard::registry_len()` reports the current size.

The default `std` feature caches each thread's hazard guard in thread-local
storage, so a thread claims a registry slot once rather than on every `pop`.
Building with `default-features = false` drops that optimisation and the `std`
dependency; nothing else changes.

## Caveats

- `peek` takes `&mut self`, and there is no shared-access peek. Hazard
  protection keeps a node's allocation alive but not its payload, which the
  winner of the `head` compare-and-swap moves out, so reading the top value
  through `&self` races that move. Use `pop` if you want the value.
- `len` is `O(1)` but, under concurrent access, is a snapshot that may
  over-report while operations are in flight. It is exact when the stack is
  quiescent.

## License

MIT
