use ark_ff::{Field, One, Zero};
use ark_poly::{
    DenseMultilinearExtension as MLE, DenseUVPolynomial, Polynomial, univariate::DensePolynomial,
};
use ark_std::{
    UniformRand, borrow::Borrow, cfg_into_iter, cfg_iter, marker::PhantomData, rand::RngCore,
    sync::Arc,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use sonobe_primitives::{
    algebra::ops::{bits::FromBits, poly::MLEHelper},
    arithmetizations::{
        Arith, ArithConfig, ArithRelation,
        r1cs::{R1CS, RelaxedInstance, RelaxedWitness},
    },
    circuits::AssignmentsOwned,
    commitments::{CommitmentDef, CommitmentKey, CommitmentOps, GroupBasedCommitment},
    relations::{Relation, WitnessInstanceSampler},
    traits::{CF1, Dummy, SonobeCurve},
    transcripts::Transcript,
};

use self::{instance::RunningInstance as RU, witness::RunningWitness as RW};
use crate::{
    DeciderKey, Error, FoldingSchemeDef, FoldingSchemeKeyGenerator, FoldingSchemePreprocessor,
    FoldingSchemeProver, FoldingSchemeVerifier, PlainInstance as IU, PlainWitness as IW,
};

pub mod instance;
pub mod witness;

#[derive(Clone)]
pub struct MovaKey<A, CM: CommitmentDef> {
    pub arith: Arc<A>,
    pub ck: Arc<CM::Key>,
}

impl<A: Arith, CM: CommitmentDef> DeciderKey for MovaKey<A, CM> {
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

impl<A, CM> Relation<RW<CM>, RU<CM>> for MovaKey<A, CM>
where
    A: for<'a> ArithRelation<
            RelaxedWitness<&'a [CM::Scalar]>,
            RelaxedInstance<&'a [CM::Scalar]>,
            Evaluation = Vec<CM::Scalar>,
        >,
    CM: CommitmentOps<Scalar: Field>,
{
    type Error = Error;

    fn check_relation(&self, w: &RW<CM>, u: &RU<CM>) -> Result<(), Self::Error> {
        self.arith.check_relation(
            &RelaxedWitness { w: &w.w, e: &w.e },
            &RelaxedInstance { x: &u.x, u: &u.u },
        )?;
        CM::open(&self.ck, &w.w, &w.r_w, &u.cm_w)?;

        (MLE::from_evaluations(&w.e).evaluate(&u.r_e) == u.v)
            .then_some(())
            .ok_or_else(|| {
                Error::UnsatisfiedRelation("Error term does not evaluate to claimed value".into())
            })
    }
}

impl<A, CM> Relation<IW<CM::Scalar>, IU<CM::Scalar>> for MovaKey<A, CM>
where
    A: ArithRelation<Vec<CM::Scalar>, Vec<CM::Scalar>>,
    CM: CommitmentDef,
{
    type Error = Error;

    fn check_relation(&self, w: &IW<CM::Scalar>, u: &IU<CM::Scalar>) -> Result<(), Self::Error> {
        self.arith.check_relation(w, u)?;
        Ok(())
    }
}

impl<A, CM: CommitmentDef> WitnessInstanceSampler<IW<CM::Scalar>, IU<CM::Scalar>>
    for MovaKey<A, CM>
{
    type Source = AssignmentsOwned<CM::Scalar>;
    type Error = Error;

    fn sample(
        &self,
        z: Self::Source,
        _rng: impl RngCore,
    ) -> Result<(IW<CM::Scalar>, IU<CM::Scalar>), Error> {
        Ok((z.private.into(), z.public.into()))
    }
}

impl<A, CM> WitnessInstanceSampler<RW<CM>, RU<CM>> for MovaKey<A, CM>
where
    A: for<'a> ArithRelation<
            RelaxedWitness<&'a [CM::Scalar]>,
            RelaxedInstance<&'a [CM::Scalar]>,
            Evaluation = Vec<CM::Scalar>,
        >,
    CM: CommitmentOps<Scalar: Field>,
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

        let r_e = (0..cfg.log_constraints())
            .map(|_| CM::Scalar::rand(&mut rng))
            .collect::<Vec<_>>();
        let v = MLE::from_evaluations(&e).evaluate(&r_e);

        Ok((RW { w, r_w, e }, RU { x, cm_w, u, r_e, v }))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MovaProof<C: SonobeCurve> {
    pub h1_coeffs: Vec<CF1<C>>,
    pub t: CF1<C>,
    pub cm_w: C,
}

impl<C: SonobeCurve, Cfg: ArithConfig> Dummy<&Cfg> for MovaProof<C> {
    fn dummy(cfg: &Cfg) -> Self {
        Self {
            h1_coeffs: vec![Zero::zero(); cfg.log_constraints()],
            t: Zero::zero(),
            cm_w: Zero::zero(),
        }
    }
}

pub struct Mova<CM, const CHALLENGE_BITS: usize = 128> {
    _vc: PhantomData<CM>,
}

impl<CM: GroupBasedCommitment, const CHALLENGE_BITS: usize> FoldingSchemeDef
    for Mova<CM, CHALLENGE_BITS>
{
    type CM = CM;
    type RW = RW<CM>;
    type RU = RU<CM>;
    type IW = IW<CM::Scalar>;
    type IU = IU<CM::Scalar>;

    type TranscriptField = CM::Scalar;
    type Arith = R1CS<CM::Scalar>;

    type Config = usize;
    type PublicParam = CM::Key;
    type DeciderKey = MovaKey<Self::Arith, CM>;
    type Challenge = [bool; CHALLENGE_BITS];
    type Proof<const M: usize, const N: usize> = MovaProof<CM::Commitment>;
}

impl<CM: GroupBasedCommitment, const CHALLENGE_BITS: usize> FoldingSchemePreprocessor
    for Mova<CM, CHALLENGE_BITS>
{
    fn preprocess(n_witnesses: usize, mut rng: impl RngCore) -> Result<Self::PublicParam, Error> {
        let ck = CM::generate_key(n_witnesses, &mut rng)?;
        Ok(ck)
    }
}

impl<CM: GroupBasedCommitment, const CHALLENGE_BITS: usize> FoldingSchemeKeyGenerator
    for Mova<CM, CHALLENGE_BITS>
{
    fn generate_keys(ck: Self::PublicParam, r1cs: Self::Arith) -> Result<Self::DeciderKey, Error> {
        let ck = Arc::new(ck);
        let r1cs = Arc::new(r1cs);
        if ck.max_scalars_len() < r1cs.config().n_witnesses() {
            return Err(Error::InvalidPublicParameters(
                "The commitment key is too short for the R1CS instance".into(),
            ));
        }
        Ok(MovaKey { arith: r1cs, ck })
    }
}

impl<CM: GroupBasedCommitment, const CHALLENGE_BITS: usize> FoldingSchemeProver<1, 1>
    for Mova<CM, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn prove(
        pk: &MovaKey<Self::Arith, CM>,
        transcript: &mut impl Transcript<CM::Scalar>,
        Ws: &[impl Borrow<Self::RW>; 1],
        Us: &[impl Borrow<Self::RU>; 1],
        ws: &[impl Borrow<Self::IW>; 1],
        us: &[impl Borrow<Self::IU>; 1],
        rng: impl RngCore,
    ) -> Result<(Self::RW, Self::RU, Self::Proof<1, 1>, Self::Challenge), Error> {
        let (W, U) = (Ws[0].borrow(), Us[0].borrow());
        let (w, u) = (ws[0].borrow(), us[0].borrow());

        // Protocol 5

        // Step 5.1: Commit to w & send commitment
        let (cm_w, r_w) = CM::commit(&pk.ck, w, rng)?;

        transcript.add(U);
        transcript.add(u);
        transcript.add(&cm_w);

        // Step 5.2: Get challenge r_E
        let r_e = transcript.challenge_field_elements(U.r_e.len());

        // Protocol 6

        // Step 6.1: Compute l(X) such that l(0) = r1, l(1) = r2
        let l = U
            .r_e
            .iter()
            .zip(&r_e)
            .map(|(&r1, &r2)| DensePolynomial::from_coefficients_vec(vec![r1, r2 - r1]))
            .collect::<Vec<_>>();
        // Step 6.1: Compute h1(X) and h2(X), where h2(X) is empty in our case
        let h1 = {
            // Initialize the polynomial vector from the evaluations in the MLE.
            // Each evaluation is turned into a constant polynomial.
            let mut poly =
                W.e.iter()
                    .chain(vec![Zero::zero(); 1 << U.r_e.len()].iter())
                    .map(|&x| DensePolynomial::from_coefficients_slice(&[x]))
                    .collect::<Vec<_>>();

            for i in &l {
                poly = poly
                    .chunks_exact(2)
                    .map(|w| &w[0] + (&w[1] - &w[0]).naive_mul(i))
                    .collect();
            }

            poly.swap_remove(0)
        };
        // Step 6.1: Send h1(X) and h2(X), where the constant term is omitted
        // because it always equals v
        let mut h1_coeffs = h1.coeffs.clone();
        h1_coeffs.resize(pk.arith.config().log_constraints() + 1, Zero::zero());
        h1_coeffs.remove(0);
        transcript.add(&h1_coeffs);

        // Step 6.2: Get challenge beta
        let beta = transcript.challenge_field_element();

        // Step 6.3: Compute r_E'
        let r_e_prime = l.iter().map(|i| i.evaluate(&beta)).collect();

        // Protocol 7

        // Step 7.1: Compute cross term `T`. We follow the optimized approach in
        // [Mova](https://eprint.iacr.org/2024/1220.pdf)'s section 5.2.
        let v = pk.arith.evaluate_at(AssignmentsOwned::from((
            U.u + CM::Scalar::one(),
            cfg_iter!(U.x).zip(&u[..]).map(|(a, b)| *a + b).collect(),
            cfg_iter!(W.w).zip(&w[..]).map(|(a, b)| *a + b).collect(),
        )))?;
        let T = cfg_into_iter!(v)
            .zip(&W.e)
            .map(|(a, b)| a - b)
            .collect::<Vec<_>>();
        // Step 7.1: Evaluate & send T's MLE at r_E'
        let t = MLE::from_evaluations(&T).evaluate(&r_e_prime);
        transcript.add(&t);

        // Step 7.2: Get challenge rho
        let rho_bits = transcript.challenge_bits(CHALLENGE_BITS);
        let rho = CM::Scalar::from_bits_le(&rho_bits);

        // Step 7.3: Compute new W and U
        Ok((
            Self::RW {
                e: cfg_iter!(W.e).zip(&T).map(|(a, b)| rho * b + a).collect(),
                w: cfg_iter!(W.w)
                    .zip(&w[..])
                    .map(|(a, b)| rho * b + a)
                    .collect(),
                r_w: W.r_w + r_w * rho,
            },
            Self::RU {
                r_e: r_e_prime,
                v: h1.evaluate(&beta) + rho * t,
                u: U.u + rho,
                cm_w: U.cm_w + cm_w * rho,
                x: cfg_iter!(U.x)
                    .zip(&u[..])
                    .map(|(a, b)| rho * b + a)
                    .collect(),
            },
            MovaProof { h1_coeffs, t, cm_w },
            rho_bits.try_into().unwrap(),
        ))
    }
}

impl<CM: GroupBasedCommitment, const CHALLENGE_BITS: usize> FoldingSchemeVerifier<1, 1>
    for Mova<CM, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn verify(
        _vk: &(),
        transcript: &mut impl Transcript<CM::Scalar>,
        Us: &[impl Borrow<Self::RU>; 1],
        us: &[impl Borrow<Self::IU>; 1],
        proof: &Self::Proof<1, 1>,
    ) -> Result<Self::RU, Error> {
        let (U, u) = (Us[0].borrow(), us[0].borrow());

        let h1 = DensePolynomial::from_coefficients_vec([&[U.v][..], &proof.h1_coeffs].concat());

        transcript.add(U);
        transcript.add(u);
        transcript.add(&proof.cm_w);

        let r_e = transcript.challenge_field_elements(U.r_e.len());

        transcript.add(&proof.h1_coeffs);

        let beta = transcript.challenge_field_element();

        transcript.add(&proof.t);

        let rho_bits = transcript.challenge_bits(CHALLENGE_BITS);
        let rho = CM::Scalar::from_bits_le(&rho_bits);

        Ok(Self::RU {
            r_e: U
                .r_e
                .iter()
                .zip(r_e)
                .map(|(&r1, r2)| r1 + beta * (r2 - r1))
                .collect(),
            v: h1.evaluate(&beta) + rho * proof.t,
            u: U.u + rho,
            cm_w: U.cm_w + proof.cm_w * rho,
            x: cfg_iter!(U.x)
                .zip(&u[..])
                .map(|(a, b)| rho * b + a)
                .collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fr, G1Projective};
    use ark_ff::UniformRand;
    use ark_std::{error::Error, rand::Rng, test_rng};
    use sonobe_primitives::{
        circuits::utils::{CircuitForTest, satisfying_assignments_for_test},
        commitments::pedersen::Pedersen,
    };

    use super::*;
    use crate::tests::test_folding_scheme;

    fn test_mova_opt(rounds: usize, mut rng: impl Rng) -> Result<(), Box<dyn Error>> {
        test_folding_scheme::<Mova<Pedersen<G1Projective, true>>, 1, 1>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<Mova<Pedersen<G1Projective, false>>, 1, 1>(
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
    fn test_mova() -> Result<(), Box<dyn Error>> {
        let mut rng = test_rng();
        test_mova_opt(10, &mut rng)?;
        Ok(())
    }
}
