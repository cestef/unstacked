<p align="center">
    <img src="./assets/banner.png" alt="unstacked banner" />
</p>

Concurrent, lock-free, `no-std` stack implementation in Rust.

- Uses atomic compare-and-exchange operations for thread safety
- Implements tagged pointers to prevent the [ABA problem](https://en.wikipedia.org/wiki/ABA_problem)
- Each modification increments a tag counter to detect concurrent modifications
- Safe for concurrent access from multiple threads

## Example

```rust
use unstacked::Stack;
let stack: Stack<i32> = Stack::new();
stack.push(1);
assert_eq!(stack.pop(), Some(1));
assert_eq!(stack.pop(), None);

stack.push(2);
assert_eq!(stack.peek(), Some(2).as_ref());
assert!(!stack.is_empty())
```
