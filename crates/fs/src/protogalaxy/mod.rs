use ark_ff::{Field, One, Zero, batch_inversion};
use ark_poly::{
    DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial,
    univariate::DensePolynomial,
};
use ark_std::{
    UniformRand, borrow::Borrow, cfg_into_iter, iter::once, log2, marker::PhantomData,
    rand::RngCore, sync::Arc,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use sonobe_primitives::{
    algebra::ops::{
        pow::Pow,
        rlc::{ScalarRLC, SliceRLC},
    },
    arithmetizations::{Arith, ArithConfig, ArithRelation, Error as ArithError, r1cs::R1CS},
    circuits::{Assignments, AssignmentsOwned},
    commitments::{CommitmentDef, CommitmentKey, CommitmentOps, GroupBasedCommitment},
    relations::{Relation, WitnessInstanceSampler},
    traits::Dummy,
    transcripts::Transcript,
};

use self::{
    instance::{IncomingInstance as IU, RunningInstance as RU},
    witness::{IncomingWitness as IW, RunningWitness as RW},
};
use crate::{
    DeciderKey, Error, FoldingSchemeDef, FoldingSchemeKeyGenerator, FoldingSchemePreprocessor,
    FoldingSchemeProver, FoldingSchemeVerifier, PlainInstance as PU, PlainWitness as PW, TaggedVec,
};

pub mod instance;
pub mod witness;

#[derive(Clone)]
pub struct ProtoGalaxyKey<A, CM: CommitmentDef> {
    arith: Arc<A>,
    ck: Arc<CM::Key>,
}

impl<A: Arith, CM: CommitmentDef> DeciderKey for ProtoGalaxyKey<A, CM> {
    type ProverKey = Self;
    type VerifierKey = ();
    type ArithConfig = A::Config;

    fn to_pk(&self) -> &Self::ProverKey {
        self
    }

    fn to_vk(&self) -> &Self::VerifierKey {
        &()
    }

    fn to_arith_config(&self) -> &Self::ArithConfig {
        self.arith.config()
    }
}

impl<CM: CommitmentDef<Scalar: Field>> ArithRelation<RW<CM>, RU<CM>> for R1CS<CM::Scalar> {
    type Evaluation = Vec<CM::Scalar>;

    fn eval_relation(&self, w: &RW<CM>, u: &RU<CM>) -> Result<Self::Evaluation, ArithError> {
        Self::eval_relation(self, &w.w, &u.x)
    }

    fn check_evaluation(_w: &RW<CM>, u: &RU<CM>, v: Self::Evaluation) -> Result<(), ArithError> {
        if u.betas.len() != log2(v.len()) as usize {
            return Err(ArithError::MalformedAssignments(format!(
                "The number of betas in the running instance ({}) does not match the expected length ({}).",
                u.betas.len(),
                log2(v.len())
            )));
        }

        let e = cfg_into_iter!(v)
            .zip(Pow::powers_from_repeated_squares(&u.betas))
            .map(|(x, y)| x * y)
            .sum();

        if u.e != e {
            return Err(ArithError::UnsatisfiedAssignments(
                "Evaluation does not match error term".into(),
            ));
        }
        Ok(())
    }
}

impl<A, CM> Relation<RW<CM>, RU<CM>> for ProtoGalaxyKey<A, CM>
where
    A: ArithRelation<RW<CM>, RU<CM>>,
    CM: CommitmentOps,
{
    type Error = Error;

    fn check_relation(&self, w: &RW<CM>, u: &RU<CM>) -> Result<(), Self::Error> {
        self.arith.check_relation(w, u)?;
        CM::open(&self.ck, &w.w, &w.r, &u.phi)?;
        Ok(())
    }
}

impl<A, CM> Relation<IW<CM>, IU<CM>> for ProtoGalaxyKey<A, CM>
where
    A: ArithRelation<Vec<CM::Scalar>, Vec<CM::Scalar>>,
    CM: CommitmentOps,
{
    type Error = Error;

    fn check_relation(&self, w: &IW<CM>, u: &IU<CM>) -> Result<(), Self::Error> {
        self.arith.check_relation(&w.w, &u.x)?;
        CM::open(&self.ck, &w.w, &w.r, &u.phi)?;
        Ok(())
    }
}

impl<A, CM> Relation<PW<CM::Scalar>, PU<CM::Scalar>> for ProtoGalaxyKey<A, CM>
where
    A: ArithRelation<Vec<CM::Scalar>, Vec<CM::Scalar>>,
    CM: CommitmentDef,
{
    type Error = Error;

    fn check_relation(&self, w: &PW<CM::Scalar>, u: &PU<CM::Scalar>) -> Result<(), Self::Error> {
        self.arith.check_relation(w, u)?;
        Ok(())
    }
}

impl<A, CM: CommitmentOps> WitnessInstanceSampler<IW<CM>, IU<CM>> for ProtoGalaxyKey<A, CM> {
    type Source = AssignmentsOwned<CM::Scalar>;
    type Error = Error;

    fn sample(&self, z: Self::Source, rng: impl RngCore) -> Result<(IW<CM>, IU<CM>), Error> {
        let (w, x) = (z.private, z.public);
        let (phi, r) = CM::commit(&self.ck, &w, rng)?;
        Ok((IW { w, r }, IU { phi, x }))
    }
}

impl<A, CM: CommitmentDef> WitnessInstanceSampler<PW<CM::Scalar>, PU<CM::Scalar>>
    for ProtoGalaxyKey<A, CM>
{
    type Source = AssignmentsOwned<CM::Scalar>;
    type Error = Error;

    fn sample(
        &self,
        z: Self::Source,
        _rng: impl RngCore,
    ) -> Result<(PW<CM::Scalar>, PU<CM::Scalar>), Error> {
        Ok((z.private.into(), z.public.into()))
    }
}

impl<A, CM> WitnessInstanceSampler<RW<CM>, RU<CM>> for ProtoGalaxyKey<A, CM>
where
    A: ArithRelation<Vec<CM::Scalar>, Vec<CM::Scalar>, Evaluation = Vec<CM::Scalar>>,
    CM: CommitmentOps<Scalar: Field>,
{
    type Source = ();
    type Error = Error;

    fn sample(&self, _: Self::Source, mut rng: impl RngCore) -> Result<(RW<CM>, RU<CM>), Error> {
        let cfg = self.arith.config();

        let x = (0..cfg.n_public_inputs())
            .map(|_| CM::Scalar::rand(&mut rng))
            .collect::<Vec<_>>();
        let w = (0..cfg.n_witnesses())
            .map(|_| CM::Scalar::rand(&mut rng))
            .collect::<Vec<_>>();
        let (phi, r) = CM::commit(&self.ck, &w, &mut rng)?;

        let betas = (0..cfg.log_constraints())
            .map(|_| CM::Scalar::rand(&mut rng))
            .collect::<Vec<_>>();

        let v = self.arith.eval_relation(&w, &x)?;

        let e = cfg_into_iter!(v)
            .zip(Pow::powers_from_repeated_squares(&betas))
            .map(|(x, y)| x * y)
            .sum();

        Ok((RW { w, r }, RU { phi, x, e, betas }))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoGalaxyProof<F, const N: usize> {
    f_coeffs: Vec<F>,
    k_coeffs: Vec<F>,
}

impl<F: Field, Cfg: ArithConfig, const N: usize> Dummy<&Cfg> for ProtoGalaxyProof<F, N> {
    fn dummy(cfg: &Cfg) -> Self {
        Self {
            f_coeffs: vec![Default::default(); cfg.log_constraints()],
            k_coeffs: vec![Default::default(); cfg.degree() * N + 1],
        }
    }
}

pub struct ProtoGalaxy<CM> {
    _t: PhantomData<CM>,
}

impl<CM: GroupBasedCommitment> FoldingSchemeDef for ProtoGalaxy<CM> {
    type CM = CM;
    type RW = RW<CM>;
    type RU = RU<CM>;
    type IW = IW<CM>;
    type IU = IU<CM>;

    type TranscriptField = CM::Scalar;
    type Arith = R1CS<CM::Scalar>;

    type Config = usize;
    type PublicParam = CM::Key;
    type DeciderKey = ProtoGalaxyKey<Self::Arith, CM>;
    type Challenge = TaggedVec<CM::Scalar, 'c'>;
    type Proof<const M: usize, const N: usize> = ProtoGalaxyProof<CM::Scalar, N>;
}

impl<CM: GroupBasedCommitment> FoldingSchemePreprocessor for ProtoGalaxy<CM> {
    fn preprocess(ck_len: usize, mut rng: impl RngCore) -> Result<Self::PublicParam, Error> {
        let ck = CM::generate_key(ck_len, &mut rng)?;
        Ok(ck)
    }
}

impl<CM: GroupBasedCommitment> FoldingSchemeKeyGenerator for ProtoGalaxy<CM> {
    fn generate_keys(ck: Self::PublicParam, r1cs: Self::Arith) -> Result<Self::DeciderKey, Error> {
        let ck = Arc::new(ck);
        let r1cs = Arc::new(r1cs);
        if ck.max_scalars_len() < r1cs.config().n_witnesses() {
            return Err(Error::InvalidPublicParameters(
                "The commitment key is too short for the R1CS instance".into(),
            ));
        }
        Ok(Self::DeciderKey { arith: r1cs, ck })
    }
}

impl<CM: GroupBasedCommitment, const N: usize> FoldingSchemeProver<1, N> for ProtoGalaxy<CM> {
    #[allow(non_snake_case)]
    fn prove(
        pk: &ProtoGalaxyKey<Self::Arith, CM>,
        transcript: &mut impl Transcript<CM::Scalar>,
        Ws: &[impl Borrow<Self::RW>; 1],
        Us: &[impl Borrow<Self::RU>; 1],
        ws: &[impl Borrow<Self::IW>; N],
        us: &[impl Borrow<Self::IU>; N],
        _rng: impl RngCore,
    ) -> Result<(Self::RW, Self::RU, Self::Proof<1, N>, Self::Challenge), Error> {
        if !(N + 1).is_power_of_two() {
            return Err(Error::Unsupported("N + 1 must be a power of two".into()));
        }
        let (W, U) = (Ws[0].borrow(), Us[0].borrow());
        let ws = &ws.iter().map(|i| i.borrow()).collect::<Vec<_>>();
        let us = &us.iter().map(|i| i.borrow()).collect::<Vec<_>>();

        let r1cs = &pk.arith;
        let cfg = r1cs.config();
        let d = cfg.degree();
        let t = cfg.log_constraints();

        transcript.add(&t);
        transcript.add(&(d * N + 1));

        // absorb the committed instances
        transcript.add(U);
        transcript.add(&us[..]);

        let delta = transcript.challenge_field_element();
        let deltas = delta.repeated_squares(t);

        let mut eval = r1cs.eval_relation(&W.w, &U.x)?;
        eval.resize(1 << t, CM::Scalar::default());

        // F(X)
        let f_poly = calc_f_from_btree(&eval, &U.betas, &deltas);
        let mut f_coeffs = f_poly.coeffs[1..].to_vec();
        f_coeffs.resize(t, CM::Scalar::default());
        transcript.add(&f_coeffs);

        let alpha = transcript.challenge_field_element();

        // eval F(alpha)
        let f_alpha = f_poly.evaluate(&alpha);

        // betas*
        let betas_star = [&U.betas[..], &deltas[..]]
            .into_iter()
            .slice_rlc(&[One::one(), alpha]);

        let zs = once(Assignments::from((One::one(), &U.x, &W.w)))
            .chain(
                ws.iter()
                    .zip(us)
                    .map(|(w, u)| Assignments::from((One::one(), &u.x, &w.w))),
            )
            .collect::<Vec<_>>();

        let G = GeneralEvaluationDomain::<CM::Scalar>::new(d * N + 1)
            .ok_or(Error::DomainCreationFailure)?;
        let H = GeneralEvaluationDomain::<CM::Scalar>::new(N + 1)
            .ok_or(Error::DomainCreationFailure)?;

        let omegas = H.group_gen_inv().powers(H.size());
        let mut lagrange_bases = vec![vec![H.size_inv(); H.size()]];
        for i in 1..H.size() {
            lagrange_bases.push(
                lagrange_bases[i - 1]
                    .iter()
                    .zip(&omegas)
                    .map(|(a, b)| *a * b)
                    .collect(),
            );
        }
        let lagrange_bases = lagrange_bases
            .into_iter()
            .map(DensePolynomial::from_coefficients_vec)
            .collect::<Vec<_>>();

        // Optimized G(X) computation as described in Claim 4.5 of the paper.
        let s_evals = (0..cfg.n_variables())
            .map(|i| {
                lagrange_bases
                    .iter()
                    .zip(&zs)
                    .map(|(l, z)| l * z[i])
                    .fold(DensePolynomial::zero(), |acc, x| acc + x)
                    .evaluate_over_domain(G)
                    .evals
            })
            .collect::<Vec<_>>();

        let mut invs = G
            .elements()
            .map(|e| e - CM::Scalar::one())
            .collect::<Vec<_>>();
        batch_inversion(&mut invs);

        // Compute evaluations of G(X) - F(alpha)*L_0(X)
        let beta_star_pows = Pow::powers_from_repeated_squares(&betas_star);
        let g_evals = G
            .elements()
            .zip(invs)
            .enumerate()
            .map(|(k, (e, inv))| {
                if k % H.size() == 0 {
                    return Ok(CM::Scalar::zero());
                }
                let z = AssignmentsOwned::from((
                    s_evals[0][k],
                    (1..1 + cfg.n_public_inputs())
                        .map(|i| s_evals[i][k])
                        .collect(),
                    (1 + cfg.n_public_inputs()..cfg.n_variables())
                        .map(|i| s_evals[i][k])
                        .collect(),
                ));
                let v = r1cs.evaluate_at(z)?;
                // L_0(e) = (e^H.size() - 1) / (e - 1) / H.size()
                let l_0_eval = H.evaluate_vanishing_polynomial(e) * inv * H.size_inv();
                Ok(v.into_iter().scalar_rlc(&beta_star_pows) - f_alpha * l_0_eval)
            })
            .collect::<Result<Vec<_>, Error>>()?;

        // Interpolate G(X) - F(alpha)*L_0(X)
        let g_poly = Evaluations::from_vec_and_domain(g_evals, G).interpolate();
        // Compute K(X) = (G(X) - F(alpha)*L_0(X)) / Z(X)
        let (mut k_poly, r) = g_poly.divide_by_vanishing_poly(H);
        if !r.is_zero() {
            return Err(Error::IndivisibleByVanishingPoly);
        }

        k_poly.coeffs.resize(d * N + 1, CM::Scalar::default());
        transcript.add(&k_poly.coeffs);

        let gamma = transcript.challenge_field_element();

        let lagrange_evals = H.evaluate_all_lagrange_coefficients(gamma);

        Ok((
            Self::RW {
                w: once(&W.w[..])
                    .chain(ws.iter().map(|w| &w.w[..]))
                    .slice_rlc(&lagrange_evals),
                r: once(W.r)
                    .chain(ws.iter().map(|w| w.r))
                    .scalar_rlc(&lagrange_evals),
            },
            Self::RU {
                e: f_alpha * lagrange_evals[0]
                    + H.evaluate_vanishing_polynomial(gamma) * k_poly.evaluate(&gamma),
                x: once(&U.x[..])
                    .chain(us.iter().map(|u| &u.x[..]))
                    .slice_rlc(&lagrange_evals),
                betas: betas_star,
                phi: once(U.phi)
                    .chain(us.iter().map(|u| u.phi))
                    .scalar_rlc(&lagrange_evals),
            },
            ProtoGalaxyProof {
                f_coeffs,
                k_coeffs: k_poly.coeffs,
            },
            lagrange_evals.into(),
        ))
    }
}

impl<CM: GroupBasedCommitment, const N: usize> FoldingSchemeVerifier<1, N> for ProtoGalaxy<CM> {
    #[allow(non_snake_case)]
    fn verify(
        _vk: &(),
        transcript: &mut impl Transcript<CM::Scalar>,
        Us: &[impl Borrow<Self::RU>; 1],
        us: &[impl Borrow<Self::IU>; N],
        proof: &Self::Proof<1, N>,
    ) -> Result<Self::RU, Error> {
        if !(N + 1).is_power_of_two() {
            return Err(Error::Unsupported("N + 1 must be a power of two".into()));
        }
        let U = Us[0].borrow();
        let us = &us.iter().map(|i| i.borrow()).collect::<Vec<_>>();

        transcript.add(&proof.f_coeffs.len());
        transcript.add(&proof.k_coeffs.len());

        // absorb the committed instances
        transcript.add(U);
        transcript.add(&us[..]);

        let delta = transcript.challenge_field_element();
        let deltas = delta.repeated_squares(U.betas.len());

        transcript.add(&proof.f_coeffs);

        let alpha = transcript.challenge_field_element();

        let f_poly = DensePolynomial::from_coefficients_vec([&[U.e][..], &proof.f_coeffs].concat());

        let f_alpha = f_poly.evaluate(&alpha);

        transcript.add(&proof.k_coeffs);

        let H = GeneralEvaluationDomain::new(N + 1).ok_or(Error::DomainCreationFailure)?;
        let k_poly = DensePolynomial::from_coefficients_slice(&proof.k_coeffs);

        let gamma = transcript.challenge_field_element();

        let lagrange_evals = H.evaluate_all_lagrange_coefficients(gamma);

        Ok(Self::RU {
            e: f_alpha * lagrange_evals[0]
                + H.evaluate_vanishing_polynomial(gamma) * k_poly.evaluate(&gamma),
            x: once(&U.x[..])
                .chain(us.iter().map(|u| &u.x[..]))
                .slice_rlc(&lagrange_evals),
            betas: [&U.betas[..], &deltas[..]]
                .into_iter()
                .slice_rlc(&[One::one(), alpha]),
            phi: once(U.phi)
                .chain(us.iter().map(|u| u.phi))
                .scalar_rlc(&lagrange_evals),
        })
    }
}

pub struct ProtoGalaxy2<CM> {
    _t: PhantomData<CM>,
}

impl<CM: GroupBasedCommitment> FoldingSchemeDef for ProtoGalaxy2<CM> {
    type CM = CM;
    type RW = RW<CM>;
    type RU = RU<CM>;
    type IW = PW<CM::Scalar>;
    type IU = PU<CM::Scalar>;

    type TranscriptField = CM::Scalar;
    type Arith = R1CS<CM::Scalar>;

    type Config = usize;
    type PublicParam = CM::Key;
    type DeciderKey = ProtoGalaxyKey<Self::Arith, CM>;
    type Challenge = Vec<CM::Scalar>;
    type Proof<const M: usize, const N: usize> =
        ([CM::Commitment; N], ProtoGalaxyProof<CM::Scalar, N>);
}

impl<CM: GroupBasedCommitment> FoldingSchemePreprocessor for ProtoGalaxy2<CM> {
    fn preprocess(ck_len: usize, mut rng: impl RngCore) -> Result<Self::PublicParam, Error> {
        let ck = CM::generate_key(ck_len, &mut rng)?;
        Ok(ck)
    }
}

impl<CM: GroupBasedCommitment> FoldingSchemeKeyGenerator for ProtoGalaxy2<CM> {
    fn generate_keys(ck: Self::PublicParam, r1cs: Self::Arith) -> Result<Self::DeciderKey, Error> {
        let ck = Arc::new(ck);
        let r1cs = Arc::new(r1cs);
        if ck.max_scalars_len() < r1cs.config().n_witnesses() {
            return Err(Error::InvalidPublicParameters(
                "The commitment key is too short for the R1CS instance".into(),
            ));
        }
        Ok(Self::DeciderKey { arith: r1cs, ck })
    }
}

impl<CM: GroupBasedCommitment, const N: usize> FoldingSchemeProver<1, N> for ProtoGalaxy2<CM> {
    #[allow(non_snake_case)]
    fn prove(
        pk: &ProtoGalaxyKey<Self::Arith, CM>,
        transcript: &mut impl Transcript<CM::Scalar>,
        Ws: &[impl Borrow<Self::RW>; 1],
        Us: &[impl Borrow<Self::RU>; 1],
        ws: &[impl Borrow<Self::IW>; N],
        us: &[impl Borrow<Self::IU>; N],
        mut rng: impl RngCore,
    ) -> Result<(Self::RW, Self::RU, Self::Proof<1, N>, Self::Challenge), Error> {
        if !(N + 1).is_power_of_two() {
            return Err(Error::Unsupported("N + 1 must be a power of two".into()));
        }
        let (W, U) = (Ws[0].borrow(), Us[0].borrow());
        let ws = &ws.iter().map(|i| i.borrow()).collect::<Vec<_>>();
        let us = &us.iter().map(|i| i.borrow()).collect::<Vec<_>>();

        let r1cs = &pk.arith;
        let cfg = r1cs.config();
        let d = cfg.degree();
        let t = cfg.log_constraints();

        let mut phis = [CM::Commitment::default(); N];
        let mut rs = [CM::Randomness::default(); N];
        for i in 0..N {
            let (cm, r) = CM::commit(&pk.ck, ws[i], &mut rng)?;
            phis[i] = cm;
            rs[i] = r;
        }

        transcript.add(&t);
        transcript.add(&(d * N + 1));

        // absorb the committed instances
        transcript.add(U);
        transcript.add(&us[..]);
        transcript.add(&phis[..]);

        let delta = transcript.challenge_field_element();
        let deltas = delta.repeated_squares(t);

        let mut eval = r1cs.eval_relation(&W.w, &U.x)?;
        eval.resize(1 << t, CM::Scalar::default());

        // F(X)
        let f_poly = calc_f_from_btree(&eval, &U.betas, &deltas);
        let mut f_coeffs = f_poly.coeffs[1..].to_vec();
        f_coeffs.resize(t, CM::Scalar::default());
        transcript.add(&f_coeffs);

        let alpha = transcript.challenge_field_element();

        // eval F(alpha)
        let f_alpha = f_poly.evaluate(&alpha);

        // betas*
        let betas_star = [&U.betas[..], &deltas[..]]
            .into_iter()
            .slice_rlc(&[One::one(), alpha]);

        let zs = once(Assignments::from((CM::Scalar::one(), &U.x, &W.w)))
            .chain(
                ws.iter()
                    .zip(us)
                    .map(|(w, u)| Assignments::from((CM::Scalar::one(), u.as_ref(), w.as_ref()))),
            )
            .collect::<Vec<_>>();

        let G = GeneralEvaluationDomain::<CM::Scalar>::new(d * N + 1)
            .ok_or(Error::DomainCreationFailure)?;
        let H = GeneralEvaluationDomain::<CM::Scalar>::new(N + 1)
            .ok_or(Error::DomainCreationFailure)?;

        let omegas = H.group_gen_inv().powers(H.size());
        let mut lagrange_bases = vec![vec![H.size_inv(); H.size()]];
        for i in 1..H.size() {
            lagrange_bases.push(
                lagrange_bases[i - 1]
                    .iter()
                    .zip(&omegas)
                    .map(|(a, b)| *a * b)
                    .collect(),
            );
        }
        let lagrange_bases = lagrange_bases
            .into_iter()
            .map(DensePolynomial::from_coefficients_vec)
            .collect::<Vec<_>>();

        // Optimized G(X) computation as described in Claim 4.5 of the paper.
        let s_evals = (0..cfg.n_variables())
            .map(|i| {
                lagrange_bases
                    .iter()
                    .zip(&zs)
                    .map(|(l, z)| l * z[i])
                    .fold(DensePolynomial::zero(), |acc, x| acc + x)
                    .evaluate_over_domain(G)
                    .evals
            })
            .collect::<Vec<_>>();

        let mut invs = G
            .elements()
            .map(|e| e - CM::Scalar::one())
            .collect::<Vec<_>>();
        batch_inversion(&mut invs);

        // Compute evaluations of G(X) - F(alpha)*L_0(X)
        let beta_star_pows = Pow::powers_from_repeated_squares(&betas_star);
        let g_evals = G
            .elements()
            .zip(invs)
            .enumerate()
            .map(|(k, (e, inv))| {
                if k % H.size() == 0 {
                    return Ok(CM::Scalar::zero());
                }
                let z = AssignmentsOwned::from((
                    s_evals[0][k],
                    (1..1 + cfg.n_public_inputs())
                        .map(|i| s_evals[i][k])
                        .collect(),
                    (1 + cfg.n_public_inputs()..cfg.n_variables())
                        .map(|i| s_evals[i][k])
                        .collect(),
                ));
                let v = r1cs.evaluate_at(z)?;
                // L_0(e) = (e^H.size() - 1) / (e - 1) / H.size()
                let l_0_eval = H.evaluate_vanishing_polynomial(e) * inv * H.size_inv();
                Ok(v.into_iter().scalar_rlc(&beta_star_pows) - f_alpha * l_0_eval)
            })
            .collect::<Result<Vec<_>, Error>>()?;

        // Interpolate G(X) - F(alpha)*L_0(X)
        let g_poly = Evaluations::from_vec_and_domain(g_evals, G).interpolate();
        // Compute K(X) = (G(X) - F(alpha)*L_0(X)) / Z(X)
        let (mut k_poly, r) = g_poly.divide_by_vanishing_poly(H);
        if !r.is_zero() {
            return Err(Error::IndivisibleByVanishingPoly);
        }

        k_poly.coeffs.resize(d * N + 1, CM::Scalar::default());
        transcript.add(&k_poly.coeffs);

        let gamma = transcript.challenge_field_element();

        let lagrange_evals = H.evaluate_all_lagrange_coefficients(gamma);

        Ok((
            Self::RW {
                w: once(&W.w[..])
                    .chain(ws.iter().map(|w| &w[..]))
                    .slice_rlc(&lagrange_evals),
                r: once(W.r).chain(rs).scalar_rlc(&lagrange_evals),
            },
            Self::RU {
                e: f_alpha * lagrange_evals[0]
                    + H.evaluate_vanishing_polynomial(gamma) * k_poly.evaluate(&gamma),
                x: once(&U.x[..])
                    .chain(us.iter().map(|u| &u[..]))
                    .slice_rlc(&lagrange_evals),
                betas: betas_star,
                phi: once(U.phi).chain(phis).scalar_rlc(&lagrange_evals),
            },
            (
                phis,
                ProtoGalaxyProof {
                    f_coeffs,
                    k_coeffs: k_poly.coeffs,
                },
            ),
            lagrange_evals,
        ))
    }
}

impl<CM: GroupBasedCommitment, const N: usize> FoldingSchemeVerifier<1, N> for ProtoGalaxy2<CM> {
    #[allow(non_snake_case)]
    fn verify(
        _vk: &(),
        transcript: &mut impl Transcript<CM::Scalar>,
        Us: &[impl Borrow<Self::RU>; 1],
        us: &[impl Borrow<Self::IU>; N],
        (phis, proof): &Self::Proof<1, N>,
    ) -> Result<Self::RU, Error> {
        if !(N + 1).is_power_of_two() {
            return Err(Error::Unsupported("N + 1 must be a power of two".into()));
        }
        let U = Us[0].borrow();
        let us = &us.iter().map(|i| i.borrow()).collect::<Vec<_>>();

        transcript.add(&proof.f_coeffs.len());
        transcript.add(&proof.k_coeffs.len());

        // absorb the committed instances
        transcript.add(U);
        transcript.add(&us[..]);
        transcript.add(&phis[..]);

        let delta = transcript.challenge_field_element();
        let deltas = delta.repeated_squares(U.betas.len());

        transcript.add(&proof.f_coeffs);

        let alpha = transcript.challenge_field_element();

        let f_poly = DensePolynomial::from_coefficients_vec([&[U.e][..], &proof.f_coeffs].concat());

        let f_alpha = f_poly.evaluate(&alpha);

        transcript.add(&proof.k_coeffs);

        let H = GeneralEvaluationDomain::new(N + 1).ok_or(Error::DomainCreationFailure)?;
        let k_poly = DensePolynomial::from_coefficients_slice(&proof.k_coeffs);

        let gamma = transcript.challenge_field_element();

        let lagrange_evals = H.evaluate_all_lagrange_coefficients(gamma);

        Ok(Self::RU {
            e: f_alpha * lagrange_evals[0]
                + H.evaluate_vanishing_polynomial(gamma) * k_poly.evaluate(&gamma),
            x: once(&U.x[..])
                .chain(us.iter().map(|u| &u[..]))
                .slice_rlc(&lagrange_evals),
            betas: [&U.betas[..], &deltas[..]]
                .into_iter()
                .slice_rlc(&[One::one(), alpha]),
            phi: once(U.phi).chain(*phis).scalar_rlc(&lagrange_evals),
        })
    }
}

/// calculates F[x] using the optimized binary-tree technique
/// described in Claim 4.4
/// of [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
fn calc_f_from_btree<F: Field>(fw: &[F], betas: &[F], deltas: &[F]) -> DensePolynomial<F> {
    let mut layer = fw
        .iter()
        .map(|&e| DensePolynomial::from_coefficients_vec(vec![e]))
        .collect::<Vec<_>>();
    for l in 0..betas.len() {
        layer = layer
            .chunks(2)
            .map(|chunk| {
                let e = DensePolynomial::from_coefficients_vec(vec![betas[l], deltas[l]]);
                chunk[1].naive_mul(&e) + &chunk[0]
            })
            .collect();
    }
    layer.pop().unwrap()
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fr, G1Projective};
    use ark_ff::UniformRand;
    use ark_std::{
        error::Error,
        rand::{Rng, thread_rng},
    };
    use sonobe_primitives::{
        circuits::utils::{CircuitForTest, satisfying_assignments_for_test},
        commitments::pedersen::Pedersen,
    };
    #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
    use wasm_bindgen_test::wasm_bindgen_test as test;

    use super::*;
    use crate::tests::test_folding_scheme;

    fn test_protogalaxy_opt<const N: usize>(
        rounds: usize,
        mut rng: impl Rng,
    ) -> Result<(), Box<dyn Error>> {
        test_folding_scheme::<ProtoGalaxy<Pedersen<G1Projective, true>>, 1, N>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<ProtoGalaxy<Pedersen<G1Projective, false>>, 1, N>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<ProtoGalaxy2<Pedersen<G1Projective, true>>, 1, N>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<ProtoGalaxy2<Pedersen<G1Projective, false>>, 1, N>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;
        Ok(())
    }

    #[test]
    fn test_protogalaxy() -> Result<(), Box<dyn Error>> {
        let mut rng = thread_rng();
        test_protogalaxy_opt::<1>(10, &mut rng)?;
        test_protogalaxy_opt::<3>(10, &mut rng)?;
        test_protogalaxy_opt::<7>(10, &mut rng)?;
        test_protogalaxy_opt::<0>(10, &mut rng)?;
        Ok(())
    }
}
