use ark_relations::gr1cs::SynthesisError;
use ark_std::{error::Error, rand::RngCore};

pub trait Relation<W, U> {
    type Error: Error;

    /// Checks if witness `w` and instance `u` satisfy the relation `self`
    fn check_relation(&self, w: &W, u: &U) -> Result<(), Self::Error>;
}

pub trait RelationGadget<WVar, UVar> {
    /// Checks if witness `w` and instance `u` satisfy the relation `self`
    fn check_relation(&self, w: &WVar, u: &UVar) -> Result<(), SynthesisError>;
}

/// `WitnessInstanceSampler` allows sampling a random witness-instance pair that
/// satisfies the relation `self`.
pub trait WitnessInstanceSampler<W, U> {
    type Source;
    type Error: Error;

    fn sample(&self, source: Self::Source, rng: impl RngCore) -> Result<(W, U), Self::Error>;
}
