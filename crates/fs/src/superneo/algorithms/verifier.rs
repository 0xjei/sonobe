//! Proof verification for SuperNeo.

use ark_std::{borrow::Borrow, cfg_iter, ops::Mul};
#[cfg(not(feature = "parallel"))]
use itertools::Itertools;
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use sonobe_primitives::{
    algebra::ops::bits::FromBits, commitments::GroupBasedCommitment,
    transcripts::Transcript,
};

use crate::{Error, FoldingSchemeVerifier, nova::AbstractNova};
