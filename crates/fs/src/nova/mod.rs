use ark_ff::{BigInteger, One, PrimeField};
use ark_r1cs_std::{GR1CSVar, alloc::AllocVar, boolean::Boolean, groups::CurveVar};
use ark_relations::gr1cs::SynthesisError;
use ark_std::{
    UniformRand,
    borrow::Borrow,
    cfg_into_iter, cfg_iter,
    marker::PhantomData,
    ops::Mul,
    rand::{RngCore, rngs::mock::StepRng},
    sync::Arc,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use sonobe_primitives::{
    algebra::ops::bits::FromBitsGadget,
    arithmetizations::{
        Arith, ArithConfig, ArithRelation,
        r1cs::{R1CS, RelaxedInstance, RelaxedWitness},
    },
    circuits::AssignmentsOwned,
    commitments::{
        CommitmentDef, CommitmentDefGadget, CommitmentKey, CommitmentOps, GroupBasedCommitment,
    },
    relations::{Relation, WitnessInstanceSampler},
    traits::{CF2, SonobeField},
    transcripts::{Transcript, TranscriptGadget},
};

use self::{
    instance::{
        IncomingInstance as IU, RunningInstance as RU,
        circuits::{IncomingInstanceVar as IUVar, RunningInstanceVar as RUVar},
    },
    witness::{IncomingWitness as IW, RunningWitness as RW},
};
use crate::{
    DeciderKey, Error, FoldingSchemeDef, FoldingSchemeDefGadget, FoldingSchemeFullVerifierGadget,
    FoldingSchemeKeyGenerator, FoldingSchemePartialVerifierGadget, FoldingSchemePreprocessor,
    FoldingSchemeProver, FoldingSchemeVerifier, GroupBasedFoldingSchemePrimaryDef,
    GroupBasedFoldingSchemeSecondaryDef, PlainInstance as PU, PlainWitness as PW,
};

pub mod instance;
pub mod witness;

#[derive(Clone)]
pub struct NovaKey<A, CM: CommitmentDef> {
    arith: Arc<A>,
    ck: Arc<CM::Key>,
}

impl<A: Arith, CM: CommitmentDef> DeciderKey for NovaKey<A, CM> {
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

impl<A, CM> Relation<RW<CM>, RU<CM>> for NovaKey<A, CM>
where
    A: for<'a> ArithRelation<RelaxedWitness<&'a [CM::Scalar]>, RelaxedInstance<&'a [CM::Scalar]>>,
    CM: CommitmentOps,
{
    type Error = Error;

    fn check_relation(&self, w: &RW<CM>, u: &RU<CM>) -> Result<(), Self::Error> {
        self.arith.check_relation(
            &RelaxedWitness { w: &w.w, e: &w.e },
            &RelaxedInstance { x: &u.x, u: &u.u },
        )?;
        CM::open(&self.ck, &w.w, &w.r_w, &u.cm_w)?;
        CM::open(&self.ck, &w.e, &w.r_e, &u.cm_e)?;
        Ok(())
    }
}

impl<A, CM> Relation<IW<CM>, IU<CM>> for NovaKey<A, CM>
where
    A: ArithRelation<Vec<CM::Scalar>, Vec<CM::Scalar>>,
    CM: CommitmentOps,
{
    type Error = Error;

    fn check_relation(&self, w: &IW<CM>, u: &IU<CM>) -> Result<(), Self::Error> {
        self.arith.check_relation(&w.w, &u.x)?;
        CM::open(&self.ck, &w.w, &w.r_w, &u.cm_w)?;
        Ok(())
    }
}

impl<A, CM> Relation<PW<CM::Scalar>, PU<CM::Scalar>> for NovaKey<A, CM>
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

impl<A, CM: CommitmentOps> WitnessInstanceSampler<IW<CM>, IU<CM>> for NovaKey<A, CM> {
    type Source = AssignmentsOwned<CM::Scalar>;
    type Error = Error;

    fn sample(&self, z: Self::Source, rng: impl RngCore) -> Result<(IW<CM>, IU<CM>), Error> {
        let (w, x) = (z.private, z.public);
        let (cm_w, r_w) = CM::commit(&self.ck, &w, rng)?;
        Ok((IW { w, r_w }, IU { cm_w, x }))
    }
}

impl<A, CM: CommitmentDef> WitnessInstanceSampler<PW<CM::Scalar>, PU<CM::Scalar>>
    for NovaKey<A, CM>
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

impl<A, CM> WitnessInstanceSampler<RW<CM>, RU<CM>> for NovaKey<A, CM>
where
    A: for<'a> ArithRelation<
            RelaxedWitness<&'a [CM::Scalar]>,
            RelaxedInstance<&'a [CM::Scalar]>,
            Evaluation = Vec<CM::Scalar>,
        >,
    CM: CommitmentOps,
{
    type Source = ();
    type Error = Error;

    fn sample(&self, _: Self::Source, mut rng: impl RngCore) -> Result<(RW<CM>, RU<CM>), Error> {
        let cfg = self.arith.config();

        let u = CM::Scalar::rand(&mut rng);
        let x = (0..cfg.n_public_inputs())
            .map(|_| CM::Scalar::rand(&mut rng))
            .collect::<Vec<_>>();
        let w = (0..cfg.n_witnesses())
            .map(|_| CM::Scalar::rand(&mut rng))
            .collect::<Vec<_>>();
        let e = self.arith.eval_relation(
            &RelaxedWitness { w: &w, e: &[] },
            &RelaxedInstance { x: &x, u: &u },
        )?;

        let (cm_w, r_w) = CM::commit(&self.ck, &w, &mut rng)?;
        let (cm_e, r_e) = CM::commit(&self.ck, &e, &mut rng)?;
        Ok((RW { w, r_w, e, r_e }, RU { cm_w, x, cm_e, u }))
    }
}

// used for the RO challenges.
// From [Srinath Setty](https://microsoft.com/en-us/research/people/srinath/): In Nova, soundness
// error ≤ 2/|S|, where S is the subset of the field F from which the challenges are drawn. In this
// case, we keep the size of S close to 2^128.
pub struct AbstractNova<CM, TF, const CHALLENGE_BITS: usize = 128> {
    _t: PhantomData<(CM, TF)>,
}

pub type Nova<CM, const CHALLENGE_BITS: usize = 128> =
    AbstractNova<CM, <CM as CommitmentDef>::Scalar, CHALLENGE_BITS>;

pub type CycleFoldNova<CM, const CHALLENGE_BITS: usize = 128> =
    AbstractNova<CM, CF2<<CM as CommitmentDef>::Commitment>, CHALLENGE_BITS>;

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize> FoldingSchemeDef
    for AbstractNova<CM, TF, CHALLENGE_BITS>
{
    type CM = CM;
    type RW = RW<CM>;
    type RU = RU<CM>;
    type IW = IW<CM>;
    type IU = IU<CM>;

    type TranscriptField = TF;
    type Arith = R1CS<CM::Scalar>;

    type Config = usize;
    type PublicParam = CM::Key;
    type DeciderKey = NovaKey<Self::Arith, CM>;
    type Challenge = [bool; CHALLENGE_BITS];
    type Proof<const M: usize, const N: usize> = CM::Commitment;
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemePreprocessor for AbstractNova<CM, TF, CHALLENGE_BITS>
{
    fn preprocess(ck_len: usize, mut rng: impl RngCore) -> Result<Self::PublicParam, Error> {
        let ck = CM::generate_key(ck_len, &mut rng)?;
        Ok(ck)
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeKeyGenerator for AbstractNova<CM, TF, CHALLENGE_BITS>
{
    fn generate_keys(ck: Self::PublicParam, r1cs: Self::Arith) -> Result<Self::DeciderKey, Error> {
        let ck = Arc::new(ck);
        let r1cs = Arc::new(r1cs);
        let cfg = r1cs.config();
        if ck.max_scalars_len() < cfg.n_constraints().max(cfg.n_witnesses()) {
            return Err(Error::InvalidPublicParameters(
                "The commitment key is too short for the R1CS instance".into(),
            ));
        }
        Ok(Self::DeciderKey { arith: r1cs, ck })
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeProver<1, 1> for AbstractNova<CM, TF, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn prove(
        pk: &NovaKey<Self::Arith, CM>,
        transcript: &mut impl Transcript<TF>,
        Ws: &[impl Borrow<Self::RW>; 1],
        Us: &[impl Borrow<Self::RU>; 1],
        ws: &[impl Borrow<Self::IW>; 1],
        us: &[impl Borrow<Self::IU>; 1],
        rng: impl RngCore,
    ) -> Result<(Self::RW, Self::RU, Self::Proof<1, 1>, Self::Challenge), Error> {
        let (W, U) = (Ws[0].borrow(), Us[0].borrow());
        let (w, u) = (ws[0].borrow(), us[0].borrow());

        // Compute the cross term `T` by following the optimized approach in
        // [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 5.2.
        let v = pk.arith.evaluate_at(AssignmentsOwned::from((
            U.u + CM::Scalar::one(),
            cfg_iter!(U.x).zip(&u.x).map(|(a, b)| *a + b).collect(),
            cfg_iter!(W.w).zip(&w.w).map(|(a, b)| *a + b).collect(),
        )))?;
        let t = cfg_into_iter!(v)
            .zip(&W.e)
            .map(|(a, b)| a - b)
            .collect::<Vec<_>>();

        let (cm_t, r_t) = CM::commit(&pk.ck, &t, rng)?;

        let rho_bits = {
            transcript.add(&U);
            transcript.add(&u);
            transcript.add(&cm_t);
            transcript.challenge_bits(CHALLENGE_BITS)
        };
        let rho = CM::Scalar::from(<CM::Scalar as PrimeField>::BigInt::from_bits_le(&rho_bits));

        Ok((
            RW {
                e: cfg_iter!(W.e).zip(&t).map(|(a, b)| rho * b + a).collect(),
                r_e: W.r_e + r_t * rho,
                w: cfg_iter!(W.w).zip(&w.w).map(|(a, b)| rho * b + a).collect(),
                r_w: W.r_w + w.r_w * rho,
            },
            RU {
                cm_e: U.cm_e + cm_t.mul(rho),
                u: U.u + rho,
                cm_w: U.cm_w + u.cm_w.mul(rho),
                x: cfg_iter!(U.x).zip(&u.x).map(|(a, b)| rho * b + a).collect(),
            },
            cm_t,
            rho_bits.try_into().unwrap(),
        ))
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeVerifier<1, 1> for AbstractNova<CM, TF, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn verify(
        _vk: &(),
        transcript: &mut impl Transcript<TF>,
        Us: &[impl Borrow<Self::RU>; 1],
        us: &[impl Borrow<Self::IU>; 1],
        cm_t: &Self::Proof<1, 1>,
    ) -> Result<Self::RU, Error> {
        let (U, u) = (Us[0].borrow(), us[0].borrow());

        let rho_bits = {
            transcript.add(&U);
            transcript.add(&u);
            transcript.add(&cm_t);
            transcript.challenge_bits(CHALLENGE_BITS)
        };
        let rho = CM::Scalar::from(<CM::Scalar as PrimeField>::BigInt::from_bits_le(&rho_bits));

        Ok(RU {
            cm_e: U.cm_e + cm_t.mul(rho),
            u: U.u + rho,
            cm_w: U.cm_w + u.cm_w.mul(rho),
            x: cfg_iter!(U.x).zip(&u.x).map(|(a, b)| rho * b + a).collect(),
        })
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeProver<2, 0> for AbstractNova<CM, TF, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn prove(
        pk: &NovaKey<Self::Arith, CM>,
        transcript: &mut impl Transcript<TF>,
        [W1, W2]: &[impl Borrow<Self::RW>; 2],
        [U1, U2]: &[impl Borrow<Self::RU>; 2],
        _: &[impl Borrow<Self::IW>; 0],
        _: &[impl Borrow<Self::IU>; 0],
        rng: impl RngCore,
    ) -> Result<(Self::RW, Self::RU, Self::Proof<2, 0>, Self::Challenge), Error> {
        let (W1, U1) = (W1.borrow(), U1.borrow());
        let (W2, U2) = (W2.borrow(), U2.borrow());

        // Compute the cross term `T` by following the optimized approach in
        // [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 5.2.
        let v = pk.arith.evaluate_at(AssignmentsOwned::from((
            U1.u + U2.u,
            cfg_iter!(U1.x).zip(&U2.x).map(|(a, b)| *a + b).collect(),
            cfg_iter!(W1.w).zip(&W2.w).map(|(a, b)| *a + b).collect(),
        )))?;
        let t = cfg_into_iter!(v)
            .zip(&W1.e)
            .zip(&W2.e)
            .map(|((a, b), c)| a - b - c)
            .collect::<Vec<_>>();

        let (cm_t, r_t) = CM::commit(&pk.ck, &t, rng)?;

        let rho_bits = {
            transcript.add(&U1);
            transcript.add(&U2);
            transcript.add(&cm_t);
            transcript.challenge_bits(CHALLENGE_BITS)
        };
        let rho = CM::Scalar::from(<CM::Scalar as PrimeField>::BigInt::from_bits_le(&rho_bits));
        let rho_squared = rho * rho;

        Ok((
            RW {
                e: cfg_iter!(W1.e)
                    .zip(&t)
                    .zip(&W2.e)
                    .map(|((a, b), c)| rho_squared * c + rho * b + a)
                    .collect(),
                r_e: W1.r_e + r_t * rho + W2.r_e * rho_squared,
                w: cfg_iter!(W1.w)
                    .zip(&W2.w)
                    .map(|(a, b)| rho * b + a)
                    .collect(),
                r_w: W1.r_w + W2.r_w * rho,
            },
            RU {
                cm_e: U1.cm_e + cm_t.mul(rho) + U2.cm_e.mul(rho_squared),
                u: U1.u + rho * U2.u,
                cm_w: U1.cm_w + U2.cm_w.mul(rho),
                x: cfg_iter!(U1.x)
                    .zip(&U2.x)
                    .map(|(a, b)| rho * b + a)
                    .collect(),
            },
            cm_t,
            rho_bits.try_into().unwrap(),
        ))
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeVerifier<2, 0> for AbstractNova<CM, TF, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn verify(
        _vk: &(),
        transcript: &mut impl Transcript<TF>,
        [U1, U2]: &[impl Borrow<Self::RU>; 2],
        _: &[impl Borrow<Self::IU>; 0],
        cm_t: &Self::Proof<2, 0>,
    ) -> Result<Self::RU, Error> {
        let (U1, U2) = (U1.borrow(), U2.borrow());

        let rho_bits = {
            transcript.add(&U1);
            transcript.add(&U2);
            transcript.add(cm_t);
            transcript.challenge_bits(CHALLENGE_BITS)
        };
        let rho = CM::Scalar::from(<CM::Scalar as PrimeField>::BigInt::from_bits_le(&rho_bits));
        let rho_squared = rho * rho;

        Ok(RU {
            cm_e: U1.cm_e + cm_t.mul(rho) + U2.cm_e.mul(rho_squared),
            u: U1.u + rho * U2.u,
            cm_w: U1.cm_w + U2.cm_w.mul(rho),
            x: cfg_iter!(U1.x)
                .zip(&U2.x)
                .map(|(a, b)| rho * b + a)
                .collect(),
        })
    }
}

// used for the RO challenges.
// From [Srinath Setty](https://microsoft.com/en-us/research/people/srinath/): In Nova, soundness
// error ≤ 2/|S|, where S is the subset of the field F from which the challenges are drawn. In this
// case, we keep the size of S close to 2^128.
// TODO: experimental design
struct AbstractNova2<CM, TF, const CHALLENGE_BITS: usize = 128> {
    _t: PhantomData<(CM, TF)>,
}

type Nova2<CM, const CHALLENGE_BITS: usize = 128> =
    AbstractNova2<CM, <CM as CommitmentDef>::Scalar, CHALLENGE_BITS>;

type CycleFoldNova2<CM, const CHALLENGE_BITS: usize = 128> =
    AbstractNova2<CM, CF2<<CM as CommitmentDef>::Commitment>, CHALLENGE_BITS>;

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize> FoldingSchemeDef
    for AbstractNova2<CM, TF, CHALLENGE_BITS>
{
    type CM = CM;
    type RW = RW<CM>;
    type RU = RU<CM>;
    type IW = PW<CM::Scalar>;
    type IU = PU<CM::Scalar>;

    type TranscriptField = TF;
    type Arith = R1CS<CM::Scalar>;

    type Config = usize;
    type PublicParam = CM::Key;
    type DeciderKey = NovaKey<Self::Arith, CM>;
    type Challenge = [bool; CHALLENGE_BITS];
    type Proof<const M: usize, const N: usize> = (CM::Commitment, CM::Commitment);
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemePreprocessor for AbstractNova2<CM, TF, CHALLENGE_BITS>
{
    fn preprocess(ck_len: usize, mut rng: impl RngCore) -> Result<Self::PublicParam, Error> {
        let ck = CM::generate_key(ck_len, &mut rng)?;
        Ok(ck)
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeKeyGenerator for AbstractNova2<CM, TF, CHALLENGE_BITS>
{
    fn generate_keys(ck: Self::PublicParam, r1cs: Self::Arith) -> Result<Self::DeciderKey, Error> {
        let ck = Arc::new(ck);
        let r1cs = Arc::new(r1cs);
        let cfg = r1cs.config();
        if ck.max_scalars_len() < cfg.n_constraints().max(cfg.n_witnesses()) {
            return Err(Error::InvalidPublicParameters(
                "The commitment key is too short for the R1CS instance".into(),
            ));
        }
        Ok(Self::DeciderKey { arith: r1cs, ck })
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeProver<1, 1> for AbstractNova2<CM, TF, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn prove(
        pk: &NovaKey<Self::Arith, CM>,
        transcript: &mut impl Transcript<TF>,
        Ws: &[impl Borrow<Self::RW>; 1],
        Us: &[impl Borrow<Self::RU>; 1],
        ws: &[impl Borrow<Self::IW>; 1],
        us: &[impl Borrow<Self::IU>; 1],
        mut rng: impl RngCore,
    ) -> Result<(Self::RW, Self::RU, Self::Proof<1, 1>, Self::Challenge), Error> {
        let (W, U) = (Ws[0].borrow(), Us[0].borrow());
        let (w, u) = (ws[0].borrow(), us[0].borrow());

        // Compute the cross term `T` by following the optimized approach in
        // [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 5.2.
        let v = pk.arith.evaluate_at(AssignmentsOwned::from((
            U.u + CM::Scalar::one(),
            cfg_iter!(U.x).zip(&u[..]).map(|(a, b)| *a + b).collect(),
            cfg_iter!(W.w).zip(&w[..]).map(|(a, b)| *a + b).collect(),
        )))?;
        let t = cfg_into_iter!(v)
            .zip(&W.e)
            .map(|(a, b)| a - b)
            .collect::<Vec<_>>();

        let (cm_w, r_w) = CM::commit(&pk.ck, w, &mut rng)?;

        let (cm_t, r_t) = CM::commit(&pk.ck, &t, &mut rng)?;

        let pi = (cm_w, cm_t);

        let rho_bits = {
            transcript.add(&U);
            transcript.add(&u);
            transcript.add(&pi);
            transcript.challenge_bits(CHALLENGE_BITS)
        };
        let rho = CM::Scalar::from(<CM::Scalar as PrimeField>::BigInt::from_bits_le(&rho_bits));

        Ok((
            RW {
                e: cfg_iter!(W.e).zip(&t).map(|(a, b)| rho * b + a).collect(),
                r_e: W.r_e + r_t * rho,
                w: cfg_iter!(W.w)
                    .zip(&w[..])
                    .map(|(a, b)| rho * b + a)
                    .collect(),
                r_w: W.r_w + r_w * rho,
            },
            RU {
                cm_e: U.cm_e + cm_t.mul(rho),
                u: U.u + rho,
                cm_w: U.cm_w + cm_w.mul(rho),
                x: cfg_iter!(U.x)
                    .zip(&u[..])
                    .map(|(a, b)| rho * b + a)
                    .collect(),
            },
            pi,
            rho_bits.try_into().unwrap(),
        ))
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeVerifier<1, 1> for AbstractNova2<CM, TF, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn verify(
        _vk: &(),
        transcript: &mut impl Transcript<TF>,
        Us: &[impl Borrow<Self::RU>; 1],
        us: &[impl Borrow<Self::IU>; 1],
        pi: &Self::Proof<1, 1>,
    ) -> Result<Self::RU, Error> {
        let (U, u) = (Us[0].borrow(), us[0].borrow());

        let rho_bits = {
            transcript.add(&U);
            transcript.add(&u);
            transcript.add(pi);
            transcript.challenge_bits(CHALLENGE_BITS)
        };
        let rho = CM::Scalar::from(<CM::Scalar as PrimeField>::BigInt::from_bits_le(&rho_bits));

        let (cm_w, cm_t) = pi;

        Ok(RU {
            cm_e: U.cm_e + cm_t.mul(rho),
            u: U.u + rho,
            cm_w: U.cm_w + cm_w.mul(rho),
            x: cfg_iter!(U.x)
                .zip(&u[..])
                .map(|(a, b)| rho * b + a)
                .collect(),
        })
    }
}

pub struct AbstractNovaGadget<CM, const CHALLENGE_BITS: usize = 128> {
    _vc: PhantomData<CM>,
}

impl<CM, const CHALLENGE_BITS: usize> FoldingSchemeDefGadget
    for AbstractNovaGadget<CM, CHALLENGE_BITS>
where
    CM: CommitmentDefGadget<Widget: GroupBasedCommitment>,
{
    type Widget = AbstractNova<CM::Widget, CM::ConstraintField, CHALLENGE_BITS>;

    type CM = CM;
    type RU = RUVar<CM>;
    type IU = IUVar<CM>;
    type VerifierKey = ();
    type Challenge = [Boolean<CM::ConstraintField>; CHALLENGE_BITS];
    type Proof<const M: usize, const N: usize> = CM::CommitmentVar;
}

impl<CM, const CHALLENGE_BITS: usize> FoldingSchemePartialVerifierGadget<1, 1>
    for AbstractNovaGadget<CM, CHALLENGE_BITS>
where
    CM: CommitmentDefGadget<Widget: GroupBasedCommitment>,
{
    #[allow(non_snake_case)]
    fn verify_hinted(
        _vk: &Self::VerifierKey,
        transcript: &mut impl TranscriptGadget<CM::ConstraintField>,
        [U]: [&Self::RU; 1],
        [u]: [&Self::IU; 1],
        proof: &Self::Proof<1, 1>,
    ) -> Result<(Self::RU, Self::Challenge), SynthesisError> {
        let rho_bits = {
            transcript.add(&U)?;
            transcript.add(&u)?;
            transcript.add(proof)?;
            transcript.challenge_bits(CHALLENGE_BITS)?
        };
        let rho = CM::ScalarVar::from_bits_le(&rho_bits)?;

        Ok((
            Self::RU {
                u: (U.u.clone() + &rho)
                    .try_into()
                    .map_err(|_| SynthesisError::Unsatisfiable)?,
                cm_e: CM::CommitmentVar::new_witness(
                    U.cm_e.cs().or(proof.cs()).or(rho.cs()),
                    || {
                        Ok(U.cm_e.value().unwrap_or_default()
                            + proof.value().unwrap_or_default() * rho.value().unwrap_or_default())
                    },
                )?,
                cm_w: CM::CommitmentVar::new_witness(
                    U.cm_w.cs().or(u.cm_w.cs()).or(rho.cs()),
                    || {
                        Ok(U.cm_w.value().unwrap_or_default()
                            + u.cm_w.value().unwrap_or_default() * rho.value().unwrap_or_default())
                    },
                )?,
                x: U.x
                    .iter()
                    .zip(&u.x)
                    .map(|(a, b)| (b.clone() * &rho + a).try_into())
                    .collect::<Result<_, _>>()
                    .map_err(|_| SynthesisError::Unsatisfiable)?,
            },
            rho_bits.try_into().unwrap(),
        ))
    }
}

impl<CM, const CHALLENGE_BITS: usize> FoldingSchemePartialVerifierGadget<2, 0>
    for AbstractNovaGadget<CM, CHALLENGE_BITS>
where
    CM: CommitmentDefGadget<Widget: GroupBasedCommitment>,
{
    #[allow(non_snake_case)]
    fn verify_hinted(
        _vk: &Self::VerifierKey,
        transcript: &mut impl TranscriptGadget<CM::ConstraintField>,
        [U1, U2]: [&Self::RU; 2],
        _: [&Self::IU; 0],
        proof: &Self::Proof<2, 0>,
    ) -> Result<(Self::RU, Self::Challenge), SynthesisError> {
        let rho_bits = {
            transcript.add(&U1)?;
            transcript.add(&U2)?;
            transcript.add(proof)?;
            transcript.challenge_bits(CHALLENGE_BITS)?
        };
        let rho = CM::ScalarVar::from_bits_le(&rho_bits)?;

        Ok((
            Self::RU {
                u: (U2.u.clone() * &rho + &U1.u)
                    .try_into()
                    .map_err(|_| SynthesisError::Unsatisfiable)?,
                cm_e: CM::CommitmentVar::new_witness(
                    U1.cm_e.cs().or(U2.cm_e.cs()).or(proof.cs()).or(rho.cs()),
                    || {
                        let rho = rho.value().unwrap_or_default();
                        Ok(U1.cm_e.value().unwrap_or_default()
                            + proof.value().unwrap_or_default() * rho
                            + U2.cm_e.value().unwrap_or_default() * rho * rho)
                    },
                )?,
                cm_w: CM::CommitmentVar::new_witness(
                    U1.cm_w.cs().or(U2.cm_w.cs()).or(rho.cs()),
                    || {
                        Ok(U1.cm_w.value().unwrap_or_default()
                            + U2.cm_w.value().unwrap_or_default() * rho.value().unwrap_or_default())
                    },
                )?,
                x: U1
                    .x
                    .iter()
                    .zip(&U2.x)
                    .map(|(a, b)| (b.clone() * &rho + a).try_into())
                    .collect::<Result<_, _>>()
                    .map_err(|_| SynthesisError::Unsatisfiable)?,
            },
            rho_bits.try_into().unwrap(),
        ))
    }
}

impl<CM, const CHALLENGE_BITS: usize> FoldingSchemeFullVerifierGadget<1, 1>
    for AbstractNovaGadget<CM, CHALLENGE_BITS>
where
    CM: CommitmentDefGadget<Widget: GroupBasedCommitment>,
    CM::CommitmentVar: CurveVar<<CM::Widget as CommitmentDef>::Commitment, CM::ConstraintField>,
{
    #[allow(non_snake_case)]
    fn verify(
        _vk: &Self::VerifierKey,
        transcript: &mut impl TranscriptGadget<CM::ConstraintField>,
        [U]: [&Self::RU; 1],
        [u]: [&Self::IU; 1],
        proof: &Self::Proof<1, 1>,
    ) -> Result<Self::RU, SynthesisError> {
        let rho_bits = {
            transcript.add(&U)?;
            transcript.add(&u)?;
            transcript.add(proof)?;
            transcript.challenge_bits(CHALLENGE_BITS)?
        };
        let rho = CM::ScalarVar::from_bits_le(&rho_bits)?;

        Ok(Self::RU {
            u: (U.u.clone() + &rho)
                .try_into()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
            cm_e: proof.scalar_mul_le(rho_bits.iter())? + &U.cm_e,
            cm_w: u.cm_w.scalar_mul_le(rho_bits.iter())? + &U.cm_w,
            x: U.x
                .iter()
                .zip(&u.x)
                .map(|(a, b)| (b.clone() * &rho + a).try_into())
                .collect::<Result<_, _>>()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        })
    }
}

impl<CM: GroupBasedCommitment, const CHALLENGE_BITS: usize> GroupBasedFoldingSchemePrimaryDef
    for AbstractNova<CM, CM::Scalar, CHALLENGE_BITS>
{
    type Gadget = AbstractNovaGadget<CM::Gadget2, CHALLENGE_BITS>;
}

impl<CM: GroupBasedCommitment, const CHALLENGE_BITS: usize> GroupBasedFoldingSchemeSecondaryDef
    for AbstractNova<CM, CF2<CM::Commitment>, CHALLENGE_BITS>
{
    type Gadget = AbstractNovaGadget<CM::Gadget1, CHALLENGE_BITS>;
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fq, Fr, G1Projective};
    use ark_ff::UniformRand;
    use ark_std::{error::Error, test_rng};
    use sonobe_primitives::{
        circuits::utils::{CircuitForTest, satisfying_assignments_for_test},
        commitments::pedersen::Pedersen,
    };

    use super::*;
    use crate::tests::test_folding_scheme;

    fn test_nova_opt<TF: SonobeField>(
        rounds: usize,
        mut rng: impl RngCore,
    ) -> Result<(), Box<dyn Error>> {
        test_folding_scheme::<AbstractNova<Pedersen<G1Projective, true>, TF>, 1, 1>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<AbstractNova<Pedersen<G1Projective, false>, TF>, 1, 1>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<AbstractNova<Pedersen<G1Projective, true>, TF>, 2, 0>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<AbstractNova<Pedersen<G1Projective, false>, TF>, 2, 0>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<AbstractNova2<Pedersen<G1Projective, true>, TF>, 1, 1>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<AbstractNova2<Pedersen<G1Projective, false>, TF>, 1, 1>(
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
    fn test_nova() -> Result<(), Box<dyn Error>> {
        let mut rng = test_rng();

        test_nova_opt::<Fr>(10, &mut rng)?;
        test_nova_opt::<Fq>(10, &mut rng)?;
        Ok(())
    }
}
