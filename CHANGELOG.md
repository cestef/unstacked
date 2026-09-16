# Changelog

## 0.2.0

Fixes three soundness bugs, two of which were reachable from entirely safe
code. **0.1.x is unsound and should not be used.**

### Soundness

- `pop` read `head.next` after loading `head`, so a concurrent `pop` could free
  that node in between. Miri reported a use-after-free. Tagged pointers do not
  prevent this: a tag stops a stale compare-and-swap from succeeding, it does
  not keep the memory alive. Node reclamation now goes through a built-in
  hazard pointer registry (`unstacked::hazard`).
- `peek` returned `&T` from `&self`, so a `pop` could free the node while the
  reference was live. It now takes `&mut self`, which rejects that at compile
  time.
- `Send`/`Sync` were auto-derived, making `Stack<T>: Sync` whenever `T: Sync`.
  Since `pop` moves a `T` out through a shared reference, `Sync` now requires
  `T: Send + Sync`.

### Correctness

- Added `Drop`. A dropped stack used to leak every remaining node and payload.
- `len` no longer requires `T: Clone` and is now `O(1)` rather than `O(n)`. The
  bound came from `#[derive(Clone)]` on the internal tagged pointer adding a
  `T: Clone` bound its fields never needed.
- The crate now compiles on 16- and 32-bit targets. The tagged-pointer masks
  were hardcoded 48-bit literals that failed to build anywhere `usize` is
  narrower, which included most embedded targets the `no_std` claim was aimed
  at.
- `include` in `Cargo.toml` omitted `src`, so `cargo publish` failed with
  "no targets specified in the manifest". 0.1.2 was never published as a result.

### Removed

- `peek_cloned`. Hazard protection keeps a node's allocation alive but not its
  payload, which the winner of the `head` compare-and-swap moves out, so
  cloning the top value through `&self` raced that move. Miri reported a data
  race on every seed. There is no cheap way to make a shared-access peek sound.
- `TaggedPtr`, internally. A protected node cannot be freed, so its address
  cannot be recycled, so `head` cannot return to it holding a different `next`.
  Hazard pointers make ABA unrepresentable without a tag.

### Added

- `Stack::pop_all` returning `Drain`, which detaches the whole chain in one
  atomic swap instead of `N` compare-and-swaps.
- `Stack::extend_shared`, `Default`, `Debug`, `IntoIterator` (owned and
  borrowed), `FromIterator`, `Extend`, `Stack::iter`.
- `Stack::new` is now `const`, so a stack can live in a `static`.
- `hazard::set_scan_threshold`, `hazard::scan_threshold`, `hazard::collect`,
  `hazard::registry_len`.
- A default-on `std` feature that caches each thread's hazard guard in
  thread-local storage. `default-features = false` keeps the crate fully
  functional.

## 0.1.1

Initial release. Unsound; see above.
