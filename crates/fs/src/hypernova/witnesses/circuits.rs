use ark_r1cs_std::{
    GR1CSVar,
    alloc::{AllocVar, AllocationMode},
};
use ark_relations::gr1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::borrow::Borrow;
use sonobe_primitives::commitments::CommitmentDefGadget;

use super::{CCCSWitness, LCCCSWitness};

#[derive(Debug, PartialEq)]
pub struct LCCCSWitnessVar<CM: CommitmentDefGadget> {
    pub w: Vec<CM::ScalarVar>,
    pub r: CM::RandomnessVar,
}

impl<CM: CommitmentDefGadget> AllocVar<LCCCSWitness<CM::Native>, CM::ConstraintField>
    for LCCCSWitnessVar<CM>
{
    fn new_variable<T: Borrow<LCCCSWitness<CM::Native>>>(
        cs: impl Into<Namespace<CM::ConstraintField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let LCCCSWitness { w, r } = v.borrow();
        Ok(Self {
            w: AllocVar::new_variable(cs.clone(), || Ok(&w[..]), mode)?,
            r: AllocVar::new_variable(cs.clone(), || Ok(r), mode)?,
        })
    }
}

impl<CM: CommitmentDefGadget> GR1CSVar<CM::ConstraintField> for LCCCSWitnessVar<CM> {
    type Value = LCCCSWitness<CM::Native>;

    fn cs(&self) -> ConstraintSystemRef<CM::ConstraintField> {
        self.w.cs().or(self.r.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(LCCCSWitness {
            w: self.w.value()?,
            r: self.r.value()?,
        })
    }
}

#[derive(Debug, PartialEq)]
pub struct CCCSWitnessVar<CM: CommitmentDefGadget> {
    pub w: Vec<CM::ScalarVar>,
    pub r: CM::RandomnessVar,
}

impl<CM: CommitmentDefGadget> AllocVar<CCCSWitness<CM::Native>, CM::ConstraintField>
    for CCCSWitnessVar<CM>
{
    fn new_variable<T: Borrow<CCCSWitness<CM::Native>>>(
        cs: impl Into<Namespace<CM::ConstraintField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let CCCSWitness { w, r } = v.borrow();
        Ok(Self {
            w: AllocVar::new_variable(cs.clone(), || Ok(&w[..]), mode)?,
            r: AllocVar::new_variable(cs.clone(), || Ok(r), mode)?,
        })
    }
}

impl<CM: CommitmentDefGadget> GR1CSVar<CM::ConstraintField> for CCCSWitnessVar<CM> {
    type Value = CCCSWitness<CM::Native>;

    fn cs(&self) -> ConstraintSystemRef<CM::ConstraintField> {
        self.w.cs().or(self.r.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(CCCSWitness {
            w: self.w.value()?,
            r: self.r.value()?,
        })
    }
}
