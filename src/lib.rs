#![no_std]
#![doc = include_str!("../README.md")]

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

pub mod hazard;
mod iter;
mod node;
mod stack;

pub use iter::{Drain, IntoIter, Iter};
pub use stack::Stack;
