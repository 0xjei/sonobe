use ark_r1cs_std::{alloc::AllocVar, GR1CSVar};
use ark_std::fmt::Debug;
use sonobe_primitives::{
    arithmetizations::ArithConfig,
    commitments::{CommitmentDef, CommitmentDefGadget},
    traits::Dummy,
};

use super::utils::TaggedVec;

pub trait FoldingWitness<VC: CommitmentDef>: Debug {
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

impl<VC: CommitmentDef> FoldingWitness<VC> for PlainWitness<VC::Scalar> {
    const N_OPENINGS: usize = 0;

    fn openings(&self) -> Vec<(&[VC::Scalar], &VC::Randomness)> {
        vec![]
    }
}

pub trait FoldingWitnessVar<VC: CommitmentDefGadget>:
    AllocVar<Self::Value, VC::ConstraintField>
    + GR1CSVar<VC::ConstraintField, Value: FoldingWitness<VC::Widget>>
{
}

impl<VC: CommitmentDefGadget, T> FoldingWitnessVar<VC> for T where
    T: AllocVar<Self::Value, VC::ConstraintField>
        + GR1CSVar<VC::ConstraintField, Value: FoldingWitness<VC::Widget>>
{
}

pub type PlainWitnessVar<V> = PlainWitness<V>;
