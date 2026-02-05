use ark_r1cs_std::{alloc::AllocVar, GR1CSVar};
use ark_std::fmt::Debug;
use sonobe_primitives::{
    arithmetizations::ArithConfig,
    commitments::{VectorCommitmentDef, VectorCommitmentDefGadget},
    traits::Dummy,
};

use super::utils::TaggedVec;

pub trait FoldingWitness<VC: VectorCommitmentDef>: Debug {
    const N_OPENINGS: usize;

    /// Returns the reference to all openings contained in the witness, each
    /// being a tuple of the values being committed to and the randomness.
    fn openings(&self) -> Vec<(&[VC::Scalar], &VC::Randomness)>;
}

pub type PlainWitness<V> = TaggedVec<V, 'w'>;

impl<V: Default + Clone, A: ArithConfig> Dummy<&A> for PlainWitness<V> {
    fn dummy(cfg: &A) -> Self {
        vec![V::default(); cfg.n_witnesses()].into()
    }
}

impl<VC: VectorCommitmentDef> FoldingWitness<VC> for PlainWitness<VC::Scalar> {
    const N_OPENINGS: usize = 0;

    fn openings(&self) -> Vec<(&[VC::Scalar], &VC::Randomness)> {
        vec![]
    }
}

pub trait FoldingWitnessVar<VC: VectorCommitmentDefGadget>:
    AllocVar<Self::Value, VC::ConstraintField>
    + GR1CSVar<VC::ConstraintField, Value: FoldingWitness<VC::Native>>
{
}

impl<VC: VectorCommitmentDefGadget, T> FoldingWitnessVar<VC> for T where
    T: AllocVar<Self::Value, VC::ConstraintField>
        + GR1CSVar<VC::ConstraintField, Value: FoldingWitness<VC::Native>>
{
}

pub type PlainWitnessVar<V> = PlainWitness<V>;
