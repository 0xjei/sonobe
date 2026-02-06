use ark_r1cs_std::{
    GR1CSVar,
    alloc::{AllocVar, AllocationMode},
    fields::fp::FpVar,
    prelude::Boolean,
    select::CondSelectGadget,
};
use ark_relations::gr1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::borrow::Borrow;
use sonobe_primitives::{commitments::CommitmentDefGadget, transcripts::AbsorbableGadget};

use super::{CCCSInstance, LCCCSInstance};
use crate::FoldingInstanceVar;

#[derive(Clone, Debug, PartialEq)]
pub struct LCCCSInstanceVar<CM: CommitmentDefGadget> {
    pub cm: CM::CommitmentVar,
    pub u: CM::ScalarVar,
    pub x: Vec<CM::ScalarVar>,
    pub r_x: Vec<CM::ScalarVar>,
    pub v: Vec<CM::ScalarVar>,
}

impl<CM: CommitmentDefGadget> AllocVar<LCCCSInstance<CM::Native>, CM::ConstraintField>
    for LCCCSInstanceVar<CM>
{
    fn new_variable<T: Borrow<LCCCSInstance<CM::Native>>>(
        cs: impl Into<Namespace<CM::ConstraintField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let LCCCSInstance { cm, u, x, r_x, v } = v.borrow();
        Ok(Self {
            cm: AllocVar::new_variable(cs.clone(), || Ok(cm), mode)?,
            u: AllocVar::new_variable(cs.clone(), || Ok(u), mode)?,
            x: AllocVar::new_variable(cs.clone(), || Ok(&x[..]), mode)?,
            r_x: AllocVar::new_variable(cs.clone(), || Ok(&r_x[..]), mode)?,
            v: AllocVar::new_variable(cs.clone(), || Ok(&v[..]), mode)?,
        })
    }
}

impl<CM: CommitmentDefGadget> GR1CSVar<CM::ConstraintField> for LCCCSInstanceVar<CM> {
    type Value = LCCCSInstance<CM::Native>;

    fn cs(&self) -> ConstraintSystemRef<CM::ConstraintField> {
        self.cm
            .cs()
            .or(self.u.cs())
            .or(self.x.cs())
            .or(self.r_x.cs())
            .or(self.v.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(LCCCSInstance {
            cm: self.cm.value()?,
            u: self.u.value()?,
            x: self.x.value()?,
            r_x: self.r_x.value()?,
            v: self.v.value()?,
        })
    }
}

impl<CM: CommitmentDefGadget> AbsorbableGadget<CM::ConstraintField> for LCCCSInstanceVar<CM> {
    fn absorb_into(
        &self,
        dest: &mut Vec<FpVar<CM::ConstraintField>>,
    ) -> Result<(), SynthesisError> {
        self.cm.absorb_into(dest)?;
        self.u.absorb_into(dest)?;
        self.x.absorb_into(dest)?;
        self.r_x.absorb_into(dest)?;
        self.v.absorb_into(dest)
    }
}

impl<CM: CommitmentDefGadget> CondSelectGadget<CM::ConstraintField> for LCCCSInstanceVar<CM> {
    fn conditionally_select(
        cond: &Boolean<CM::ConstraintField>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        if true_value.x.len() != false_value.x.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        if true_value.r_x.len() != false_value.r_x.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        if true_value.v.len() != false_value.v.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        Ok(Self {
            cm: cond.select(&true_value.cm, &false_value.cm)?,
            u: cond.select(&true_value.u, &false_value.u)?,
            x: true_value
                .x
                .iter()
                .zip(&false_value.x)
                .map(|(t, f)| cond.select(t, f))
                .collect::<Result<_, _>>()?,
            r_x: true_value
                .r_x
                .iter()
                .zip(&false_value.r_x)
                .map(|(t, f)| cond.select(t, f))
                .collect::<Result<_, _>>()?,
            v: true_value
                .v
                .iter()
                .zip(&false_value.v)
                .map(|(t, f)| cond.select(t, f))
                .collect::<Result<_, _>>()?,
        })
    }
}

impl<CM: CommitmentDefGadget> FoldingInstanceVar<CM> for LCCCSInstanceVar<CM> {
    fn commitments(&self) -> Vec<&CM::CommitmentVar> {
        vec![&self.cm]
    }

    fn public_inputs(&self) -> &Vec<CM::ScalarVar> {
        &self.x
    }

    fn new_witness_with_public_inputs(
        cs: impl Into<Namespace<CM::ConstraintField>>,
        u: &Self::Value,
        x: Vec<CM::ScalarVar>,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        Ok(Self {
            cm: AllocVar::new_witness(cs.clone(), || Ok(&u.cm))?,
            u: AllocVar::new_witness(cs.clone(), || Ok(&u.u))?,
            x,
            r_x: AllocVar::new_witness(cs.clone(), || Ok(&u.r_x[..]))?,
            v: AllocVar::new_witness(cs.clone(), || Ok(&u.v[..]))?,
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct CCCSInstanceVar<CM: CommitmentDefGadget> {
    pub cm: CM::CommitmentVar,
    pub x: Vec<CM::ScalarVar>,
}

impl<CM: CommitmentDefGadget> AllocVar<CCCSInstance<CM::Native>, CM::ConstraintField>
    for CCCSInstanceVar<CM>
{
    fn new_variable<T: Borrow<CCCSInstance<CM::Native>>>(
        cs: impl Into<Namespace<CM::ConstraintField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let CCCSInstance { cm, x } = v.borrow();
        Ok(Self {
            cm: AllocVar::new_variable(cs.clone(), || Ok(cm), mode)?,
            x: AllocVar::new_variable(cs.clone(), || Ok(&x[..]), mode)?,
        })
    }
}

impl<CM: CommitmentDefGadget> GR1CSVar<CM::ConstraintField> for CCCSInstanceVar<CM> {
    type Value = CCCSInstance<CM::Native>;

    fn cs(&self) -> ConstraintSystemRef<CM::ConstraintField> {
        self.cm.cs().or(self.x.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(CCCSInstance {
            cm: self.cm.value()?,
            x: self.x.value()?,
        })
    }
}

impl<CM: CommitmentDefGadget> AbsorbableGadget<CM::ConstraintField> for CCCSInstanceVar<CM> {
    fn absorb_into(
        &self,
        dest: &mut Vec<FpVar<CM::ConstraintField>>,
    ) -> Result<(), SynthesisError> {
        self.cm.absorb_into(dest)?;
        self.x.absorb_into(dest)
    }
}

impl<CM: CommitmentDefGadget> CondSelectGadget<CM::ConstraintField> for CCCSInstanceVar<CM> {
    fn conditionally_select(
        cond: &Boolean<CM::ConstraintField>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        if true_value.x.len() != false_value.x.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        Ok(Self {
            cm: cond.select(&true_value.cm, &false_value.cm)?,
            x: true_value
                .x
                .iter()
                .zip(&false_value.x)
                .map(|(t, f)| cond.select(t, f))
                .collect::<Result<_, _>>()?,
        })
    }
}

impl<CM: CommitmentDefGadget> FoldingInstanceVar<CM> for CCCSInstanceVar<CM> {
    fn commitments(&self) -> Vec<&CM::CommitmentVar> {
        vec![&self.cm]
    }

    fn public_inputs(&self) -> &Vec<CM::ScalarVar> {
        &self.x
    }

    fn new_witness_with_public_inputs(
        cs: impl Into<Namespace<CM::ConstraintField>>,
        u: &Self::Value,
        x: Vec<CM::ScalarVar>,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        Ok(Self {
            cm: AllocVar::new_witness(cs.clone(), || Ok(&u.cm))?,
            x,
        })
    }
}
