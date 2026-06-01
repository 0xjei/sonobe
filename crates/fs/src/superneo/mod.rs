pub mod algorithms;
pub mod instances;
pub mod keys;
pub mod utils;
pub mod witnesses;

use ark_ff::{Field, One, PrimeField, Zero};
use ark_std::{fmt::Debug, marker::PhantomData, ops::Range, rand::RngCore};
use sonobe_primitives::{
    algebra::{
        field::SonobeField,
        ops::pow::Pow,
        ring::{PolynomialRingConfig, PolynomialRingOverField},
    },
    arithmetizations::{
        ArithConfig, ArithRelation,
        ccs::{self, CCS},
    },
    commitments::{CommitmentDef, CommitmentOps},
    traits::{Dummy, SonobePrimeField},
    utils::null::Null,
};

use self::{
    instances::{IncomingInstance as IU, RunningInstance as RU},
    witnesses::{IncomingWitness as IW, RunningWitness as RW},
};
use crate::{FoldingSchemeDef, superneo::keys::SuperNeoKey};

pub trait SuperNeoConfig: Clone + Debug + Eq + PartialEq {
    type P: PolynomialRingConfig;
    type K: SonobeField<BasePrimeField = Self::F>;
    type F: SonobePrimeField;
    type CM: CommitmentOps<
            Scalar = PolynomialRingOverField<Self::P, Self::F>,
            Commitment = Vec<PolynomialRingOverField<Self::P, Self::F>>,
            Randomness = Null,
        >;
    const KAPPA: usize;
    const M: usize;
    const B: usize;
    const CHALLENGE_COEFF_RANGE: Range<i8>;
}

#[derive(Clone)]
pub struct SuperNeoProof<Cfg: SuperNeoConfig, const N: usize> {
    sc_proof: Vec<Vec<Cfg::K>>,
    y_prime: Vec<Vec<PolynomialRingOverField<Cfg::P, Cfg::K>>>,
    y: Vec<Vec<PolynomialRingOverField<Cfg::P, Cfg::K>>>,
    c_prime: Vec<Vec<PolynomialRingOverField<Cfg::P, Cfg::F>>>,
}

impl<Cfg: SuperNeoConfig, const N: usize> Dummy<&ArithConfig> for SuperNeoProof<Cfg, N> {
    fn dummy(cfg: &ArithConfig) -> Self {
        let s = cfg.log_constraints();
        Self {
            sc_proof: vec![vec![Zero::zero(); cfg.degree.max(Cfg::B * 2 - 1) + 1 + 2]; s],
            y_prime: vec![vec![Default::default(); cfg.n_matrices]; Cfg::M + N],
            y: vec![vec![Default::default(); cfg.n_matrices]; Cfg::M],
            c_prime: vec![vec![Default::default(); Cfg::KAPPA]; Cfg::M],
        }
    }
}

pub struct SuperNeo<Cfg, A> {
    _t: PhantomData<(Cfg, A)>,
}

impl<Cfg: SuperNeoConfig, A: CCS<Field = Cfg::F> + ArithRelation<Vec<Cfg::F>, Vec<Cfg::F>>>
    FoldingSchemeDef for SuperNeo<Cfg, A>
{
    type CM = Cfg::CM;
    type RW = RW<Cfg>;
    type RU = RU<Cfg>;
    type IW = IW<Cfg::F>;
    type IU = IU<<Cfg::CM as CommitmentDef>::Commitment, Cfg::F>;

    type TranscriptField = Cfg::F;
    type Arith = A;

    type Config = usize;
    type PublicParam = <Cfg::CM as CommitmentDef>::Key;
    type DeciderKey = SuperNeoKey<Self::Arith, Cfg::CM>;
    type Challenge = Vec<PolynomialRingOverField<Cfg::P, Cfg::F>>;
    type Proof<const M: usize, const N: usize> = SuperNeoProof<Cfg, N>;
}
