use ark_ff::PrimeField;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_relations::gr1cs::{Namespace, SynthesisError};
use ark_std::{One, borrow::Borrow};

use super::R1CS;
use crate::{
    algebra::ops::{
        eq::EquivalenceGadget,
        matrix::{MatrixGadget, SparseMatrixVar},
        vector::VectorGadget,
    },
    arithmetizations::ArithRelationGadget,
    circuits::Assignments,
};

/// An in-circuit representation of the `R1CS` struct.
#[allow(non_snake_case)]
#[derive(Debug, Clone)]
pub struct R1CSMatricesVar<FVar> {
    pub A: SparseMatrixVar<FVar>,
    pub B: SparseMatrixVar<FVar>,
    pub C: SparseMatrixVar<FVar>,
}

impl<F: PrimeField, ConstraintF: PrimeField, FVar: AllocVar<F, ConstraintF>>
    AllocVar<R1CS<F>, ConstraintF> for R1CSMatricesVar<FVar>
{
    fn new_variable<T: Borrow<R1CS<F>>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let val = val.borrow();

            Ok(Self {
                A: SparseMatrixVar::<FVar>::new_variable(cs.clone(), || Ok(&val.A), mode)?,
                B: SparseMatrixVar::<FVar>::new_variable(cs.clone(), || Ok(&val.B), mode)?,
                C: SparseMatrixVar::<FVar>::new_variable(cs.clone(), || Ok(&val.C), mode)?,
            })
        })
    }
}

impl<FVar> R1CSMatricesVar<FVar>
where
    SparseMatrixVar<FVar>: MatrixGadget<FVar>,
    [FVar]: VectorGadget<FVar>,
{
    #[allow(non_snake_case)]
    pub fn eval_assignments(
        &self,
        z: Assignments<FVar, impl AsRef<[FVar]>>,
    ) -> Result<(Vec<FVar>, Vec<FVar>), SynthesisError> {
        // Multiply Cz by z[0] (u) here, allowing this method to be reused for
        // both relaxed and unrelaxed R1CS.
        let Az = self.A.mul_vector(&z)?;
        let Bz = self.B.mul_vector(&z)?;
        let Cz = self.C.mul_vector(&z)?;
        let uCz = Cz.scale(&z[0])?;
        let AzBz = Az.hadamard(&Bz)?;
        Ok((AzBz, uCz))
    }
}

impl<FVar, WVar: AsRef<[FVar]>, UVar: AsRef<[FVar]>> ArithRelationGadget<WVar, UVar>
    for R1CSMatricesVar<FVar>
where
    SparseMatrixVar<FVar>: MatrixGadget<FVar>,
    [FVar]: VectorGadget<FVar> + EquivalenceGadget<FVar>,
    FVar: Clone + One,
{
    /// Evaluation is a tuple of two vectors (`AzBz` and `uCz`) instead of a
    /// single vector `AzBz - uCz`, because subtraction is not supported for
    /// `FVar = NonNativeUintVar`.
    type Evaluation = (Vec<FVar>, Vec<FVar>);

    fn eval_relation(&self, w: &WVar, u: &UVar) -> Result<Self::Evaluation, SynthesisError> {
        self.eval_assignments((FVar::one(), u.as_ref(), w.as_ref()).into())
    }

    fn check_evaluation(
        _w: &WVar,
        _u: &UVar,
        (lhs, rhs): Self::Evaluation,
    ) -> Result<(), SynthesisError> {
        lhs.enforce_equivalent(&rhs)
    }
}

// TODO: add back tests
