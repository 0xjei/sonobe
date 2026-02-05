use ark_ff::UniformRand;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, select::CondSelectGadget, GR1CSVar};
use ark_relations::gr1cs::SynthesisError;
use ark_std::{
    fmt::Debug,
    iter::Sum,
    ops::{Add, Mul},
    rand::RngCore,
};
use thiserror::Error;

use crate::{
    algebra::{
        field::{emulated::EmulatedFieldVar, TwoStageFieldVar},
        group::emulated::EmulatedAffineVar,
        ops::bits::FromBitsGadget,
        Val,
    },
    traits::{SonobeCurve, SonobeField, CF1, CF2},
    transcripts::{Absorbable, AbsorbableGadget},
};

pub mod pedersen;
// TODO: add back other commitment schemes

#[derive(Debug, Error)]
pub enum Error {
    // Commitment errors
    #[error("The message being committed to has length {1}, exceeding the maximum supported length ({0})")]
    MessageTooLong(usize, usize),
    #[error("Blinding factor not 0 for Commitment without hiding")]
    BlindingNotZero,
    #[error("Blinding factors incorrect, blinding is set to {0} but blinding values are {1}")]
    IncorrectBlinding(bool, String),
    #[error("Commitment verification failed")]
    CommitmentVerificationFail,
}

pub trait CommitmentKey: Clone {
    fn max_scalars_len(&self) -> usize;
}

pub trait VectorCommitmentDef: 'static + Clone + Debug + PartialEq + Eq {
    const IS_HIDING: bool;

    type Key: CommitmentKey;
    type Scalar: Clone + Copy + Default + Debug + PartialEq + Eq + Sync + Absorbable + UniformRand;
    type Commitment: Clone + Default + Debug + PartialEq + Eq + Sync + Absorbable;
    type Randomness: Clone
        + Copy
        + Default
        + Debug
        + PartialEq
        + Eq
        + Sync
        + Add<Self::Scalar, Output = Self::Randomness>
        + Mul<Self::Scalar, Output = Self::Randomness>
        + for<'a> Add<&'a Self::Scalar, Output = Self::Randomness>
        + for<'a> Mul<&'a Self::Scalar, Output = Self::Randomness>
        + Add<Output = Self::Randomness>
        + Mul<Output = Self::Randomness>
        + Sum;
}

pub trait VectorCommitmentOps: VectorCommitmentDef {
    fn generate_key(len: usize, rng: impl RngCore) -> Result<Self::Key, Error>;

    fn commit(
        ck: &Self::Key,
        v: &[Self::Scalar],
        rng: impl RngCore,
    ) -> Result<(Self::Commitment, Self::Randomness), Error>;

    fn open(
        ck: &Self::Key,
        v: &[Self::Scalar],
        r: &Self::Randomness,
        cm: &Self::Commitment,
    ) -> Result<(), Error>;
}

pub trait VectorCommitmentDefGadget: Clone {
    type ConstraintField: SonobeField;

    type KeyVar;
    type ScalarVar: AbsorbableGadget<Self::ConstraintField>
        + CondSelectGadget<Self::ConstraintField>
        + FromBitsGadget<Self::ConstraintField>
        + AllocVar<<Self::Native as VectorCommitmentDef>::Scalar, Self::ConstraintField>
        + GR1CSVar<Self::ConstraintField, Value = <Self::Native as VectorCommitmentDef>::Scalar>
        + TwoStageFieldVar;
    type CommitmentVar: Clone
        + AbsorbableGadget<Self::ConstraintField>
        + CondSelectGadget<Self::ConstraintField>
        + AllocVar<<Self::Native as VectorCommitmentDef>::Commitment, Self::ConstraintField>
        + GR1CSVar<Self::ConstraintField, Value = <Self::Native as VectorCommitmentDef>::Commitment>;
    type RandomnessVar: AllocVar<<Self::Native as VectorCommitmentDef>::Randomness, Self::ConstraintField>
        + GR1CSVar<Self::ConstraintField, Value = <Self::Native as VectorCommitmentDef>::Randomness>;

    type Native: VectorCommitmentDef;
}

pub trait VectorCommitmentOpsGadget: VectorCommitmentDefGadget {
    fn open(
        ck: &Self::KeyVar,
        v: &[Self::ScalarVar],
        r: &Self::RandomnessVar,
        cm: &Self::CommitmentVar,
    ) -> Result<(), SynthesisError>;
}

pub trait GroupBasedVectorCommitment:
    VectorCommitmentDef<
        Commitment: SonobeCurve,
        Scalar = CF1<<Self as VectorCommitmentDef>::Commitment>,
    > + VectorCommitmentOps
{
    type Gadget1: VectorCommitmentOpsGadget
        + VectorCommitmentDefGadget<
            ConstraintField = CF2<Self::Commitment>,
            ScalarVar = EmulatedFieldVar<CF2<Self::Commitment>, Self::Scalar>,
            CommitmentVar = <Self::Commitment as Val>::Var,
            Native = Self,
        >;
    type Gadget2: VectorCommitmentDefGadget<
        ConstraintField = Self::Scalar,
        ScalarVar = FpVar<Self::Scalar>,
        CommitmentVar = EmulatedAffineVar<Self::Scalar, Self::Commitment>,
        Native = Self,
    >;
}

#[cfg(test)]
mod tests {
    use ark_ff::UniformRand;
    use ark_std::error::Error;

    use super::*;

    pub fn test_commitment_correctness<VC: VectorCommitmentOps>(
        mut rng: impl RngCore,
        len: usize,
    ) -> Result<(), Box<dyn Error>> {
        let v = (0..len)
            .map(|_| VC::Scalar::rand(&mut rng))
            .collect::<Vec<_>>();

        let ck = VC::generate_key(len, &mut rng)?;
        let (cm, r) = VC::commit(&ck, &v, &mut rng)?;
        VC::open(&ck, &v, &r, &cm)?;
        Ok(())
    }
}
