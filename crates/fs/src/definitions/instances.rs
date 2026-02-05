use ark_r1cs_std::{alloc::AllocVar, select::CondSelectGadget, GR1CSVar};
use ark_relations::gr1cs::{Namespace, SynthesisError};
use ark_std::fmt::Debug;
use sonobe_primitives::{
    arithmetizations::ArithConfig,
    commitments::{CommitmentDef, CommitmentDefGadget},
    traits::Dummy,
    transcripts::{Absorbable, AbsorbableVar},
};

use super::utils::TaggedVec;

pub trait FoldingInstance<VC: CommitmentDef>:
    Clone + Debug + PartialEq + Eq + Absorbable
{
    const N_COMMITMENTS: usize;

    /// Returns the commitments contained in the committed instance.
    fn commitments(&self) -> Vec<&VC::Commitment>;

    fn public_inputs(&self) -> &[VC::Scalar];

    fn public_inputs_mut(&mut self) -> &mut [VC::Scalar];
}

pub type PlainInstance<V> = TaggedVec<V, 'u'>;

impl<V: Default + Clone, A: ArithConfig> Dummy<&A> for PlainInstance<V> {
    fn dummy(cfg: &A) -> Self {
        vec![V::default(); cfg.n_public_inputs()].into()
    }
}

impl<VC: CommitmentDef> FoldingInstance<VC> for PlainInstance<VC::Scalar> {
    const N_COMMITMENTS: usize = 0;

    fn commitments(&self) -> Vec<&VC::Commitment> {
        vec![]
    }

    fn public_inputs(&self) -> &[VC::Scalar] {
        self
    }

    fn public_inputs_mut(&mut self) -> &mut [VC::Scalar] {
        self
    }
}

pub trait FoldingInstanceVar<VC: CommitmentDefGadget>:
    AllocVar<Self::Value, VC::ConstraintField>
    + GR1CSVar<VC::ConstraintField, Value: FoldingInstance<VC::Widget>>
    + AbsorbableVar<VC::ConstraintField>
    + CondSelectGadget<VC::ConstraintField>
{
    /// Returns the commitments contained in the committed instance.
    fn commitments(&self) -> Vec<&VC::CommitmentVar>;

    fn public_inputs(&self) -> &Vec<VC::ScalarVar>;

    fn new_witness_with_public_inputs(
        cs: impl Into<Namespace<VC::ConstraintField>>,
        u: &Self::Value,
        x: Vec<VC::ScalarVar>,
    ) -> Result<Self, SynthesisError>;
}

impl<VC: CommitmentDefGadget> FoldingInstanceVar<VC> for PlainInstanceVar<VC::ScalarVar> {
    fn commitments(&self) -> Vec<&VC::CommitmentVar> {
        vec![]
    }

    fn public_inputs(&self) -> &Vec<VC::ScalarVar> {
        self
    }

    fn new_witness_with_public_inputs(
        _cs: impl Into<Namespace<VC::ConstraintField>>,
        _u: &Self::Value,
        x: Vec<VC::ScalarVar>,
    ) -> Result<Self, SynthesisError> {
        Ok(Self(x))
    }
}

pub type PlainInstanceVar<V> = PlainInstance<V>;
