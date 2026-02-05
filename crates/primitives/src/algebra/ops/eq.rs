use ark_ff::PrimeField;
use ark_r1cs_std::{eq::EqGadget, fields::fp::FpVar};
use ark_relations::gr1cs::SynthesisError;

/// `EquivalenceGadget` enforces that two in-circuit variables are "equivalent".
///
/// This does not only allow us to ensure the equality of two variables of the
/// same type, but can also be used for guaranteeing variables of different
/// types represent the "same" (depending on the context) value.
pub trait EquivalenceGadget<Other: ?Sized> {
    fn enforce_equivalent(&self, other: &Self) -> Result<(), SynthesisError>;
}

impl<F: PrimeField> EquivalenceGadget<FpVar<F>> for FpVar<F> {
    fn enforce_equivalent(&self, other: &Self) -> Result<(), SynthesisError> {
        self.enforce_equal(other)
    }
}

impl<T: EquivalenceGadget<T>> EquivalenceGadget<[T]> for [T] {
    fn enforce_equivalent(&self, other: &Self) -> Result<(), SynthesisError> {
        self.iter()
            .zip(other)
            .try_for_each(|(a, b)| a.enforce_equivalent(b))
    }
}
