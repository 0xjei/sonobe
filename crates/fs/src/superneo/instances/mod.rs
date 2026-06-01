use std::array;

use ark_ff::PrimeField;
use num_bigint::BigUint;
use sonobe_primitives::{
    algebra::{
        field::SonobeField,
        ring::{PolynomialRingConfig, PolynomialRingOverField},
    },
    arithmetizations::ArithConfig,
    commitments::CommitmentDef,
    traits::{Dummy, SonobePrimeField},
    transcripts::Absorbable,
};

use crate::{FoldingInstance, definitions::instances::FoldingIncomingInstance, superneo::SuperNeoConfig};

/// [`RunningInstance`] defines SuperNeo's running instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunningInstance<Cfg: SuperNeoConfig> {
    pub c: Vec<<Cfg::CM as CommitmentDef>::Commitment>,
    pub u: Vec<Cfg::F>,
    pub x: Vec<Vec<Cfg::F>>,
    pub r: Vec<Cfg::K>,
    pub y: Vec<Vec<PolynomialRingOverField<Cfg::P, Cfg::K>>>,
}

impl<Cfg: SuperNeoConfig> FoldingInstance<Cfg::CM> for RunningInstance<Cfg> {
    fn commitments(&self) -> Vec<<Cfg::CM as CommitmentDef>::Commitment> {
        self.c.clone().into()
    }
}

impl<Cfg: SuperNeoConfig> Dummy<&ArithConfig> for RunningInstance<Cfg> {
    fn dummy(cfg: &ArithConfig) -> Self {
        Self {
            c: vec![Default::default(); Cfg::M],
            u: vec![Default::default(); Cfg::M],
            x: vec![vec![Default::default(); cfg.n_public_inputs]; Cfg::M],
            r: vec![Default::default(); cfg.log_constraints()],
            y: vec![vec![Default::default(); cfg.n_matrices]; Cfg::M],
        }
    }
}

impl<Cfg: SuperNeoConfig> Absorbable for RunningInstance<Cfg> {
    fn absorb_into<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.c.absorb_into(dest);
        self.u.absorb_into(dest);
        self.x.absorb_into(dest);
        self.r.absorb_into(dest);
        self.y.absorb_into(dest);
    }
}

/// [`IncomingInstance`] defines SuperNeo's incoming instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IncomingInstance<C, F> {
    pub c: C,
    pub x: Vec<F>,
}

impl<
    Cfg: PolynomialRingConfig,
    F: SonobePrimeField,
    CM: CommitmentDef<Scalar = PolynomialRingOverField<Cfg, F>>,
> FoldingInstance<CM> for IncomingInstance<CM::Commitment, F>
{
    fn commitments(&self) -> Vec<CM::Commitment> {
        vec![self.c.clone()]
    }
}

impl<
    Cfg: PolynomialRingConfig,
    F: SonobePrimeField,
    CM: CommitmentDef<Scalar = PolynomialRingOverField<Cfg, F>>,
> FoldingIncomingInstance<CM> for IncomingInstance<CM::Commitment, F>
{
    type PublicInput = F;

    fn public_inputs(&self) -> &[F] {
        &self.x
    }
}

impl<C: Default, F: Default + Clone> Dummy<&ArithConfig> for IncomingInstance<C, F> {
    fn dummy(cfg: &ArithConfig) -> Self {
        Self {
            c: Default::default(),
            x: vec![Default::default(); cfg.n_public_inputs],
        }
    }
}

impl<C: Absorbable, F: Absorbable> Absorbable for IncomingInstance<C, F> {
    fn absorb_into<D: PrimeField>(&self, dest: &mut Vec<D>) {
        self.x.absorb_into(dest);
        self.c.absorb_into(dest);
    }
}
