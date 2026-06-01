//! Definitions of SuperNeo keys and trait implementations for relation checks and
//! witness-instance sampling using SuperNeo keys.

use ark_ff::{Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, array, marker::PhantomData, rand::RngCore, sync::Arc};
use sonobe_primitives::{
    algebra::{
        field::SonobeField,
        ring::{PolynomialRingConfig, PolynomialRingOverField},
    },
    arithmetizations::{
        Arith, ArithConfig, ArithRelation, Error as ArithError,
        ccs::CCS,
        r1cs::{RelaxedInstance, RelaxedWitness},
    },
    circuits::{Assignments, AssignmentsOwned},
    commitments::{CommitmentDef, CommitmentOps},
    relations::{Relation, WitnessInstanceSampler},
    traits::SonobePrimeField,
    utils::null::Null,
};

use super::{
    instances::{IncomingInstance as IU, RunningInstance as RU},
    witnesses::{IncomingWitness as IW, RunningWitness as RW},
};
use crate::{
    DeciderKey, Error, PlainInstance as PU, PlainWitness as PW,
    superneo::{SuperNeoConfig, utils::decompose},
};

/// [`SuperNeoKey`] is SuperNeo's decider key.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SuperNeoKey<A: Arith, CM: CommitmentDef> {
    pub(super) arith: Arc<A>,
    pub(super) ck: Arc<CM::Key>,
}

impl<A: Arith, CM: CommitmentDef> DeciderKey for SuperNeoKey<A, CM> {
    type ProverKey = Self;
    type VerifierKey = ArithConfig;

    fn to_pk(&self) -> Self::ProverKey {
        self.clone()
    }

    fn to_vk(&self) -> Self::VerifierKey {
        self.arith.config()
    }

    fn to_arith_config(&self) -> ArithConfig {
        self.arith.config()
    }
}

impl<A: CCS<Field = Cfg::F>, Cfg: SuperNeoConfig> Relation<RW<Cfg>, RU<Cfg>>
    for SuperNeoKey<A, Cfg::CM>
{
    type Error = Error;

    fn check_relation(&self, w: &RW<Cfg>, u: &RU<Cfg>) -> Result<(), Self::Error> {
        let cfg = self.arith.config();
        let s = cfg.log_constraints();

        let mz =
            w.w.iter()
                .zip(&u.x)
                .zip(&u.u)
                .map(|((w, x), u)| {
                    PolynomialRingOverField::<Cfg::P, Cfg::F>::vector_embedding(
                        [&[*u][..], x, w].concat(),
                    )
                })
                .map(|z| {
                    self.arith
                        .matrices()
                        .iter()
                        .map(move |matrix| {
                            let matrix = PolynomialRingOverField::matrix_transform(
                                matrix
                                    .iter()
                                    .map(|row| {
                                        let mut r = vec![Cfg::F::zero(); cfg.n_variables];
                                        for (v, i) in row {
                                            r[*i] = *v;
                                        }
                                        r
                                    })
                                    .collect(),
                            );
                            matrix
                                .iter()
                                .map(|row| {
                                    let mut res = PolynomialRingOverField::default();
                                    for (i, j) in z.iter().zip(row) {
                                        res = res.add(&i.mul(j));
                                    }
                                    res
                                })
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
        let ys = mz
            .into_iter()
            .map(|i| {
                i.into_iter()
                    .map(|j| {
                        let mut poly = j
                            .into_iter()
                            .map(|k| PolynomialRingOverField::<Cfg::P, _> {
                                _t: PhantomData,
                                coeffs: k
                                    .coeffs
                                    .into_iter()
                                    .map(Cfg::K::from_base_prime_field)
                                    .collect(),
                            })
                            .collect::<Vec<_>>();
                        let nv = s;
                        let dim = u.r.len();
                        // evaluate single variable of partial point from left to right
                        for i in 1..dim + 1 {
                            let r = u.r[i - 1];
                            for b in 0..(1 << (nv - i)) {
                                let left = &poly[b << 1];
                                let right = &poly[(b << 1) + 1];
                                poly[b] = left.add(&right.sub(&left).scale(r));
                            }
                        }
                        poly.remove(0)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        assert_eq!(u.y, ys);

        for i in 0..Cfg::M {
            Cfg::CM::open(
                &self.ck,
                &PolynomialRingOverField::vector_embedding(
                    w.w[i].iter().map(|i| Cfg::F::from(*i)).collect(),
                ),
                &Null,
                &u.c[i],
            )?;
        }

        Ok(())
    }
}

impl<
    A,
    Cfg: PolynomialRingConfig,
    F: SonobePrimeField,
    CM: CommitmentOps<Scalar = PolynomialRingOverField<Cfg, F>, Randomness = Null>,
> Relation<IW<F>, IU<CM::Commitment, F>> for SuperNeoKey<A, CM>
where
    A: ArithRelation<Vec<F>, Vec<F>>,
    CM: CommitmentOps,
{
    type Error = Error;

    fn check_relation(&self, w: &IW<F>, u: &IU<CM::Commitment, F>) -> Result<(), Self::Error> {
        self.arith.check_relation(&w.w, &u.x)?;
        CM::open(
            &self.ck,
            &PolynomialRingOverField::vector_embedding(w.w.to_vec()),
            &Null,
            &u.c,
        )?;
        Ok(())
    }
}

impl<
    A: Arith,
    Cfg: PolynomialRingConfig,
    F: SonobePrimeField,
    CM: CommitmentOps<Scalar = PolynomialRingOverField<Cfg, F>, Randomness = Null>,
> WitnessInstanceSampler<IW<F>, IU<CM::Commitment, F>> for SuperNeoKey<A, CM>
{
    type Source = AssignmentsOwned<F>;
    type Error = Error;

    fn sample(
        &self,
        z: Self::Source,
        rng: impl RngCore,
    ) -> Result<(IW<F>, IU<CM::Commitment, F>), Error> {
        let (w, x) = (z.private, z.public);
        let (c, _) = CM::commit(
            &self.ck,
            &PolynomialRingOverField::vector_embedding(w.clone()),
            rng,
        )?;
        Ok((IW { w }, IU { c, x }))
    }
}

impl<A: CCS<Field = Cfg::F>, Cfg: SuperNeoConfig> WitnessInstanceSampler<RW<Cfg>, RU<Cfg>>
    for SuperNeoKey<A, Cfg::CM>
{
    type Source = ();
    type Error = Error;

    #[allow(non_snake_case)]
    fn sample(&self, _: Self::Source, mut rng: impl RngCore) -> Result<(RW<Cfg>, RU<Cfg>), Error> {
        let cfg = self.arith.config();
        let s = cfg.log_constraints();

        let u = (0..Cfg::M)
            .map(|_| Cfg::F::rand(&mut rng))
            .collect::<Vec<_>>();
        let x = (0..Cfg::M)
            .map(|_| {
                (0..cfg.n_public_inputs)
                    .map(|_| Cfg::F::rand(&mut rng))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let w = (0..Cfg::M)
            .map(|_| {
                (0..cfg.n_witnesses)
                    .map(|_| Cfg::F::rand(&mut rng))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let c = w
            .iter()
            .map(|w| {
                Cfg::CM::commit(
                    &self.ck,
                    &PolynomialRingOverField::vector_embedding(
                        w.iter()
                            .flat_map(|i| decompose(*i, Cfg::B))
                            .map(Cfg::F::from)
                            .collect::<Vec<_>>(),
                    ),
                    &mut rng,
                )
                .map(|(c, r)| c)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let r = (0..cfg.log_constraints())
            .map(|_| Cfg::K::rand(&mut rng))
            .collect::<Vec<_>>();

        let mz = w
            .iter()
            .zip(&x)
            .zip(&u)
            .map(|((w, x), u)| {
                PolynomialRingOverField::<Cfg::P, Cfg::F>::vector_embedding(
                    [&[*u][..], x, w].concat(),
                )
            })
            .map(|z| {
                self.arith
                    .matrices()
                    .iter()
                    .map(move |matrix| {
                        let matrix = PolynomialRingOverField::matrix_transform(
                            matrix
                                .iter()
                                .map(|row| {
                                    let mut r = vec![Cfg::F::zero(); cfg.n_variables];
                                    for (v, i) in row {
                                        r[*i] = *v;
                                    }
                                    r
                                })
                                .collect(),
                        );
                        matrix
                            .iter()
                            .map(|row| {
                                let mut res = PolynomialRingOverField::default();
                                for (i, j) in z.iter().zip(row) {
                                    res = res.add(&i.mul(j));
                                }
                                res
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let ys = mz
            .into_iter()
            .map(|i| {
                i.into_iter()
                    .map(|j| {
                        let mut poly = j
                            .into_iter()
                            .map(|k| PolynomialRingOverField::<Cfg::P, _> {
                                _t: PhantomData,
                                coeffs: k
                                    .coeffs
                                    .into_iter()
                                    .map(Cfg::K::from_base_prime_field)
                                    .collect(),
                            })
                            .collect::<Vec<_>>();
                        let nv = s;
                        let dim = r.len();
                        // evaluate single variable of partial point from left to right
                        for i in 1..dim + 1 {
                            let r = r[i - 1];
                            for b in 0..(1 << (nv - i)) {
                                let left = &poly[b << 1];
                                let right = &poly[(b << 1) + 1];
                                poly[b] = left.add(&right.sub(&left).scale(r));
                            }
                        }
                        poly.remove(0)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let W = RW { w };
        let U = RU {
            c: c.try_into().unwrap(),
            u,
            x,
            r,
            y: ys,
        };

        Ok((W, U))
    }
}
