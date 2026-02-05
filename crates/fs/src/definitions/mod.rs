pub mod algorithms;
pub mod circuits;
pub mod errors;
pub mod instances;
pub mod keys;
pub mod utils;
pub mod variants;
pub mod witnesses;

use ark_r1cs_std::{alloc::AllocVar, GR1CSVar};
use sonobe_primitives::{
    arithmetizations::Arith,
    circuits::AssignmentsOwned,
    commitments::{CommitmentDef, CommitmentDefGadget},
    relations::{Relation, WitnessInstanceSampler},
    traits::{Dummy, SonobeField},
};

use self::{
    errors::Error,
    instances::{FoldingInstance, FoldingInstanceVar},
    keys::DeciderKey,
    witnesses::FoldingWitness,
};

pub trait FoldingSchemeDef {
    type VC: CommitmentDef<Scalar: SonobeField>;
    type RW: FoldingWitness<Self::VC> + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
    type RU: FoldingInstance<Self::VC> + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
    type IW: FoldingWitness<Self::VC> + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
    type IU: FoldingInstance<Self::VC> + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
    type TranscriptField: SonobeField;
    type Arith: Arith<Config = <Self::DeciderKey as DeciderKey>::ArithConfig>;
    type Config;
    type PublicParam;
    type DeciderKey: DeciderKey
        + Clone
        + Relation<Self::RW, Self::RU, Error = Error>
        + Relation<Self::IW, Self::IU, Error = Error>
        + WitnessInstanceSampler<Self::RW, Self::RU, Source = (), Error = Error>
        + WitnessInstanceSampler<
            Self::IW,
            Self::IU,
            Source = AssignmentsOwned<<Self::VC as CommitmentDef>::Scalar>,
            Error = Error,
        >;
    type Challenge;
    type Proof<const M: usize, const N: usize>: Clone
        + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
}

pub trait FoldingSchemeDefGadget {
    type Native: FoldingSchemeDef;

    type VC: CommitmentDefGadget<Widget = <Self::Native as FoldingSchemeDef>::VC>;
    type RU: FoldingInstanceVar<Self::VC, Value = <Self::Native as FoldingSchemeDef>::RU>;
    type IU: FoldingInstanceVar<Self::VC, Value = <Self::Native as FoldingSchemeDef>::IU>;

    type VerifierKey;

    type Challenge: AllocVar<
            <Self::Native as FoldingSchemeDef>::Challenge,
            <Self::VC as CommitmentDefGadget>::ConstraintField,
        > + GR1CSVar<
            <Self::VC as CommitmentDefGadget>::ConstraintField,
            Value = <Self::Native as FoldingSchemeDef>::Challenge,
        >;
    type Proof<const M: usize, const N: usize>: AllocVar<
            <Self::Native as FoldingSchemeDef>::Proof<M, N>,
            <Self::VC as CommitmentDefGadget>::ConstraintField,
        > + GR1CSVar<
            <Self::VC as CommitmentDefGadget>::ConstraintField,
            Value = <Self::Native as FoldingSchemeDef>::Proof<M, N>,
        >;
}
