use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_relations::gr1cs::{Namespace, SynthesisError};
use ark_std::borrow::Borrow;
use sonobe_primitives::commitments::{CommitmentDef, CommitmentDefGadget};

use super::{IncomingWitness, RunningWitness};
use crate::FoldingWitnessVar;

#[derive(Debug, PartialEq)]
pub struct RunningWitnessVar<CM: CommitmentDefGadget> {
    pub e: Vec<CM::ScalarVar>,
    pub r_e: CM::RandomnessVar,
    pub w: Vec<CM::ScalarVar>,
    pub r_w: CM::RandomnessVar,
}

impl<CM: CommitmentDefGadget> AllocVar<RunningWitness<CM::Widget>, CM::ConstraintField>
    for RunningWitnessVar<CM>
{
    fn new_variable<T: Borrow<RunningWitness<CM::Widget>>>(
        cs: impl Into<Namespace<CM::ConstraintField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let RunningWitness { e, r_e, w, r_w } = v.borrow();
        Ok(Self {
            e: AllocVar::new_variable(cs.clone(), || Ok(&e[..]), mode)?,
            r_e: AllocVar::new_variable(cs.clone(), || Ok(r_e), mode)?,
            w: AllocVar::new_variable(cs.clone(), || Ok(&w[..]), mode)?,
            r_w: AllocVar::new_variable(cs.clone(), || Ok(r_w), mode)?,
        })
    }
}

#[derive(Debug, PartialEq)]
pub struct IncomingWitnessVar<CM: CommitmentDefGadget> {
    pub w: Vec<CM::ScalarVar>,
    pub r_w: CM::RandomnessVar,
}

impl<CM: CommitmentDefGadget> AllocVar<IncomingWitness<CM::Widget>, CM::ConstraintField>
    for IncomingWitnessVar<CM>
{
    fn new_variable<T: Borrow<IncomingWitness<CM::Widget>>>(
        cs: impl Into<Namespace<CM::ConstraintField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let IncomingWitness { w, r_w } = v.borrow();
        Ok(Self {
            w: AllocVar::new_variable(cs.clone(), || Ok(&w[..]), mode)?,
            r_w: AllocVar::new_variable(cs.clone(), || Ok(r_w), mode)?,
        })
    }
}
