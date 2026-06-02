//! Definitions of SuperNeo keys and trait implementations for relation checks and
//! witness-instance sampling using SuperNeo keys.

use ark_ff::{Field, One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, array, log2, marker::PhantomData, rand::RngCore, sync::Arc};
use num_bigint::BigUint;
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
        let base = Cfg::B;

        let m = Cfg::F::MODULUS.into();
        let mut l = m.to_radix_le(base as u32).len();
        if BigUint::from(base).pow(l as u32 - 1) == m {
            l -= 1;
        }

        let s = log2(cfg.n_variables * l) as usize;

        let decomposed_zs =
            w.w.iter()
                .zip(&u.x)
                .zip(&u.u)
                .map(|((w, x), u)| [&u[..], x, w].concat())
                .collect::<Vec<_>>();
        let ys = decomposed_zs
            .iter()
            .map(|decomposed_z| {
                let m = decomposed_z.len();
                let embedded_z = &PolynomialRingOverField::<Cfg::P, Cfg::F>::vector_embedding(
                    decomposed_z.iter().map(|i| Cfg::F::from(*i)).collect(),
                );
                self.arith
                    .matrices()
                    .iter()
                    .map(move |matrix| {
                        matrix
                            .iter()
                            .map(|i| {
                                let mut r = PolynomialRingOverField::<Cfg::P, Cfg::F>::default();
                                for (v, j) in i {
                                    let start = j * l;
                                    let end = start + l;

                                    let min = start / Cfg::P::DEGREE * Cfg::P::DEGREE;
                                    let max = end.div_ceil(Cfg::P::DEGREE) * Cfg::P::DEGREE;
                                    let mut vec = vec![Cfg::F::zero(); max - min];
                                    for i in 0..l {
                                        vec[i + start % Cfg::P::DEGREE] =
                                            *v * Cfg::F::from(Cfg::B as u64).pow([i as u64]);
                                    }
                                    PolynomialRingOverField::<Cfg::P, Cfg::F>::vector_transform(
                                        vec,
                                    )
                                    .into_iter()
                                    .enumerate()
                                    .for_each(|(i, v)| {
                                        r = r.add(&v.mul(&embedded_z[start / Cfg::P::DEGREE + i]));
                                    });
                                }

                                r
                            })
                            .collect::<Vec<_>>()
                    })
                    .chain([{
                        (0..m)
                            .map(|i| {
                                let mut chunk = vec![Cfg::F::zero(); Cfg::P::DEGREE];
                                chunk[i % Cfg::P::DEGREE] = Cfg::F::one();

                                PolynomialRingOverField::<Cfg::P, Cfg::F>::element_transform(chunk)
                                    .mul(&embedded_z[i / Cfg::P::DEGREE])
                            })
                            .collect::<Vec<_>>()
                    }])
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
                        poly.resize(1 << s, Default::default());
                        let nv = s;
                        let dim = u.r.len();
                        // evaluate single variable of partial point from left to right
                        for i in 1..dim + 1 {
                            let r = u.r[i - 1];
                            for b in 0..(1 << (nv - i)) {
                                let left = &poly.get(b << 1).cloned().unwrap_or_default();
                                let right = &poly.get((b << 1) + 1).cloned().unwrap_or_default();
                                poly[b] = left.add(&right.sub(&left).scale(r));
                            }
                        }
                        poly.remove(0)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        for i in 0..Cfg::M {
            for j in 0..cfg.n_matrices + 1 {
                assert_eq!(u.y[i][j], ys[i][j]);
            }
        }

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
        let base = Cfg::B;

        let m = Cfg::F::MODULUS.into();
        let mut l = m.to_radix_le(base as u32).len();
        if BigUint::from(base).pow(l as u32 - 1) == m {
            l -= 1;
        }

        let s = log2(cfg.n_variables * l) as usize;

        let u = (0..Cfg::M)
            .map(|_| decompose(Cfg::F::rand(&mut rng), Cfg::B))
            .collect::<Vec<_>>();
        let x = (0..Cfg::M)
            .map(|_| {
                (0..cfg.n_public_inputs)
                    .flat_map(|_| decompose(Cfg::F::rand(&mut rng), Cfg::B))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let w = (0..Cfg::M)
            .map(|_| {
                (0..cfg.n_witnesses)
                    .flat_map(|_| decompose(Cfg::F::rand(&mut rng), Cfg::B))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let c = w
            .iter()
            .map(|w| {
                Cfg::CM::commit(
                    &self.ck,
                    &PolynomialRingOverField::vector_embedding(
                        w.iter().map(|i| Cfg::F::from(*i)).collect::<Vec<_>>(),
                    ),
                    &mut rng,
                )
                .map(|(c, r)| c)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let r = (0..s).map(|_| Cfg::K::rand(&mut rng)).collect::<Vec<_>>();

        let decomposed_zs = w
            .iter()
            .zip(&x)
            .zip(&u)
            .map(|((w, x), u)| [&u[..], x, w].concat())
            .collect::<Vec<_>>();
        let ys = decomposed_zs
            .iter()
            .map(|decomposed_z| {
                let m = decomposed_z.len();
                let embedded_z = &PolynomialRingOverField::<Cfg::P, Cfg::F>::vector_embedding(
                    decomposed_z.iter().map(|i| Cfg::F::from(*i)).collect(),
                );
                self.arith
                    .matrices()
                    .iter()
                    .map(move |matrix| {
                        matrix
                            .iter()
                            .map(|i| {
                                let mut r = PolynomialRingOverField::<Cfg::P, Cfg::F>::default();
                                for (v, j) in i {
                                    let start = j * l;
                                    let end = start + l;

                                    let min = start / Cfg::P::DEGREE * Cfg::P::DEGREE;
                                    let max = end.div_ceil(Cfg::P::DEGREE) * Cfg::P::DEGREE;
                                    let mut vec = vec![Cfg::F::zero(); max - min];
                                    for i in 0..l {
                                        vec[i + start % Cfg::P::DEGREE] =
                                            *v * Cfg::F::from(Cfg::B as u64).pow([i as u64]);
                                    }
                                    PolynomialRingOverField::<Cfg::P, Cfg::F>::vector_transform(
                                        vec,
                                    )
                                    .into_iter()
                                    .enumerate()
                                    .for_each(|(i, v)| {
                                        r = r.add(&v.mul(&embedded_z[start / Cfg::P::DEGREE + i]));
                                    });
                                }

                                r
                            })
                            .collect::<Vec<_>>()
                    })
                    .chain([{
                        (0..m)
                            .map(|i| {
                                let mut chunk = vec![Cfg::F::zero(); Cfg::P::DEGREE];
                                chunk[i % Cfg::P::DEGREE] = Cfg::F::one();

                                PolynomialRingOverField::<Cfg::P, Cfg::F>::element_transform(chunk)
                                    .mul(&embedded_z[i / Cfg::P::DEGREE])
                            })
                            .collect::<Vec<_>>()
                    }])
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
                        poly.resize(1 << s, Default::default());
                        let nv = s;
                        let dim = r.len();
                        // evaluate single variable of partial point from left to right
                        for i in 1..dim + 1 {
                            let r = r[i - 1];
                            for b in 0..(1 << (nv - i)) {
                                let left = &poly.get(b << 1).cloned().unwrap_or_default();
                                let right = &poly.get((b << 1) + 1).cloned().unwrap_or_default();
                                poly[b] = left.add(&right.sub(&left).scale(r));
                            }
                        }
                        poly.remove(0)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let W = RW { _t: PhantomData, w };
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
