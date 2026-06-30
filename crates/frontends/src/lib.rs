//! Experimental frontends for Sonobe.
//!
//! This crate lets circuits authored in other languages be folded by Sonobe by
//! implementing the [`sonobe_primitives::circuits::FCircuit`] trait. The
//! recommended frontend remains writing the circuit directly with arkworks;
//! the frontends here trade some overhead for the convenience of reusing an
//! existing toolchain.
//!
//! Currently available:
//! - [`noir`]: [Noir](https://github.com/noir-lang/noir) circuits, via Aztec's
//!   ACVM.

pub mod noir;

use thiserror::Error;

/// [`Error`] enumerates the errors that can occur while loading and using a
/// frontend circuit.
#[derive(Debug, Error)]
pub enum Error {
    /// [`Error::JSONSerdeError`] indicates a failure while (de)serializing a
    /// circuit artifact.
    #[error("JSON serialization/deserialization error: {0}")]
    JSONSerdeError(String),
    /// [`Error::NotSameLength`] indicates that two quantities that were
    /// expected to match in length did not.
    #[error("{0} ({1}) does not match {2} ({3})")]
    NotSameLength(String, usize, String, usize),
    /// [`Error::UnsupportedOpcode`] indicates that the circuit contains an
    /// opcode that the frontend does not (yet) support.
    #[error("unsupported opcode: {0}")]
    UnsupportedOpcode(String),
    /// [`Error::WitnessGeneration`] indicates that witness generation (ACVM
    /// solving) failed or did not complete.
    #[error("witness generation failed: {0}")]
    WitnessGeneration(String),
    /// [`Error::Other`] is a catch-all for other errors.
    #[error("{0}")]
    Other(String),
}
