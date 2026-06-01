use ark_ff::PrimeField;
use ark_std::{array, marker::PhantomData};
use num_bigint::BigUint;
use sonobe_primitives::{
    algebra::ring::{PolynomialRingConfig, PolynomialRingOverField},
    arithmetizations::ArithConfig,
    commitments::CommitmentDef,
    traits::{Dummy, SonobePrimeField},
};

use crate::{FoldingWitness, superneo::SuperNeoConfig};

/// [`RunningWitness`] defines SuperNeo's running witness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunningWitness<Cfg: SuperNeoConfig> {
    pub w: Vec<Vec<Cfg::F>>,
}

impl<Cfg: SuperNeoConfig> FoldingWitness<Cfg::CM> for RunningWitness<Cfg> {}

impl<Cfg: SuperNeoConfig> Dummy<&ArithConfig> for RunningWitness<Cfg> {
    fn dummy(cfg: &ArithConfig) -> Self {
        Self {
            w: vec![vec![Default::default(); cfg.n_witnesses]; Cfg::M],
        }
    }
}

/// [`IncomingWitness`] defines SuperNeo's incoming witness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IncomingWitness<F> {
    pub w: Vec<F>,
}

impl<
    Cfg: PolynomialRingConfig,
    F: SonobePrimeField,
    CM: CommitmentDef<Scalar = PolynomialRingOverField<Cfg, F>>,
> FoldingWitness<CM> for IncomingWitness<F>
{
}

impl<F: Default + Clone> Dummy<&ArithConfig> for IncomingWitness<F> {
    fn dummy(cfg: &ArithConfig) -> Self {
        Self {
            w: vec![Default::default(); cfg.n_witnesses],
        }
    }
}
