use ark_ff::PrimeField;
use ark_r1cs_std::{GR1CSVar, alloc::AllocVar};

use crate::traits::SonobeField;

pub mod field;
pub mod group;
pub mod ops;

pub trait Val {
    type ConstraintField: PrimeField;
    type Var: AllocVar<Self, Self::ConstraintField> + GR1CSVar<Self::ConstraintField, Value = Self>;

    type EmulatedVar<F: SonobeField>: AllocVar<Self, F> + GR1CSVar<F, Value = Self>;
}
