#![warn(missing_docs)]

//! Sonobe is a library of folding/accumulation schemes and folding-based
//! protocols.
//!
//! This crate re-exports the whole library, so that depending on `sonobe` is
//! equivalent to depending on the three crates below:
//!
//! - [`primitives`]: fundamental building blocks and their in-circuit gadgets,
//!   such as algebra, arithmetizations, commitment schemes, transcripts, etc.
//! - [`fs`]: folding schemes.
//! - [`ivc`]: IVC compiled from folding.

pub use sonobe_fs as fs;
pub use sonobe_ivc as ivc;
pub use sonobe_primitives as primitives;
