use ark_ff::One;
use ark_r1cs_std::{GR1CSVar, alloc::AllocVar, boolean::Boolean, groups::CurveVar};
use ark_relations::gr1cs::SynthesisError;
use ark_std::{
    UniformRand, borrow::Borrow, cfg_iter, marker::PhantomData, ops::Mul, rand::RngCore, sync::Arc,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use sonobe_primitives::{
    algebra::ops::bits::{FromBits, FromBitsGadget},
    arithmetizations::{
        Arith, ArithConfig, ArithRelation,
        r1cs::{R1CS, RelaxedInstance, RelaxedWitness},
    },
    circuits::{Assignments, AssignmentsOwned},
    commitments::{
        CommitmentDef, CommitmentDefGadget, CommitmentKey, CommitmentOps, GroupBasedCommitment,
    },
    relations::{Relation, WitnessInstanceSampler},
    traits::{CF2, SonobeField},
    transcripts::{Transcript, TranscriptGadget},
};

use self::{
    instance::{RunningInstance as RU, circuits::RunningInstanceVar as RUVar},
    witness::RunningWitness as RW,
};
use crate::{
    DeciderKey, Error, FoldingSchemeDef, FoldingSchemeDefGadget, FoldingSchemeFullVerifierGadget,
    FoldingSchemeKeyGenerator, FoldingSchemePartialVerifierGadget, FoldingSchemePreprocessor,
    FoldingSchemeProver, FoldingSchemeVerifier, PlainInstance as IU, PlainInstanceVar as IUVar,
    PlainWitness as IW,
};

pub mod instance;
pub mod witness;

#[derive(Clone)]
pub struct OvaKey<A, CM: CommitmentDef> {
    arith: Arc<A>,
    ck: Arc<CM::Key>,
}

impl<A: Arith, CM: CommitmentDef> DeciderKey for OvaKey<A, CM> {
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

impl<A, CM> Relation<RW<CM>, RU<CM>> for OvaKey<A, CM>
where
    A: for<'a> ArithRelation<
            RelaxedWitness<&'a [CM::Scalar]>,
            RelaxedInstance<&'a [CM::Scalar]>,
            Evaluation = Vec<CM::Scalar>,
        >,
    CM: CommitmentOps,
{
    type Error = Error;

    fn check_relation(&self, w: &RW<CM>, u: &RU<CM>) -> Result<(), Self::Error> {
        let e = self.arith.eval_relation(
            &RelaxedWitness { w: &w.w, e: &[] },
            &RelaxedInstance { x: &u.x, u: &u.u },
        )?;
        CM::open(&self.ck, &[&w.w[..], &e].concat(), &w.r, &u.cm)?;
        Ok(())
    }
}

impl<A, CM> Relation<IW<CM::Scalar>, IU<CM::Scalar>> for OvaKey<A, CM>
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
    for OvaKey<A, CM>
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

impl<A, CM> WitnessInstanceSampler<RW<CM>, RU<CM>> for OvaKey<A, CM>
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

        let (cm, r) = CM::commit(&self.ck, &[&w[..], &e].concat(), &mut rng)?;
        Ok((RW { w, r }, RU { x, cm, u }))
    }
}

pub struct AbstractOva<CM, TF, const CHALLENGE_BITS: usize = 128> {
    _t: PhantomData<(CM, TF)>,
}

pub type Ova<CM, const CHALLENGE_BITS: usize = 128> =
    AbstractOva<CM, <CM as CommitmentDef>::Scalar, CHALLENGE_BITS>;

pub type CycleFoldOva<CM, const CHALLENGE_BITS: usize = 128> =
    AbstractOva<CM, CF2<<CM as CommitmentDef>::Commitment>, CHALLENGE_BITS>;

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize> FoldingSchemeDef
    for AbstractOva<CM, TF, CHALLENGE_BITS>
{
    type CM = CM;
    type RW = RW<CM>;
    type RU = RU<CM>;
    type IW = IW<CM::Scalar>;
    type IU = IU<CM::Scalar>;

    type TranscriptField = TF;
    type Arith = R1CS<CM::Scalar>;

    type Config = (usize, usize);
    type PublicParam = CM::Key;
    type DeciderKey = OvaKey<Self::Arith, CM>;
    type Challenge = [bool; CHALLENGE_BITS];
    type Proof<const M: usize, const N: usize> = CM::Commitment;
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemePreprocessor for AbstractOva<CM, TF, CHALLENGE_BITS>
{
    fn preprocess(
        (n_constraints, n_witnesses): (usize, usize),
        mut rng: impl RngCore,
    ) -> Result<Self::PublicParam, Error> {
        let ck = CM::generate_key(n_constraints + n_witnesses, &mut rng)?;
        Ok(ck)
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeKeyGenerator for AbstractOva<CM, TF, CHALLENGE_BITS>
{
    fn generate_keys(ck: Self::PublicParam, r1cs: Self::Arith) -> Result<Self::DeciderKey, Error> {
        let ck = Arc::new(ck);
        let r1cs = Arc::new(r1cs);
        let cfg = r1cs.config();
        if ck.max_scalars_len() < cfg.n_constraints() + cfg.n_witnesses() {
            return Err(Error::InvalidPublicParameters(
                "The commitment key generated by preprocessing is too short for the R1CS instance"
                    .into(),
            ));
        }
        Ok(Self::DeciderKey { arith: r1cs, ck })
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeProver<1, 1> for AbstractOva<CM, TF, CHALLENGE_BITS>
{
    fn prove(
        pk: &OvaKey<Self::Arith, CM>,
        transcript: &mut impl Transcript<TF>,
        Ws: &[impl Borrow<Self::RW>; 1],
        Us: &[impl Borrow<Self::RU>; 1],
        ws: &[impl Borrow<Self::IW>; 1],
        us: &[impl Borrow<Self::IU>; 1],
        rng: impl RngCore,
    ) -> Result<(Self::RW, Self::RU, Self::Proof<1, 1>, Self::Challenge), Error> {
        let (W, U) = (Ws[0].borrow(), Us[0].borrow());
        let (w, u) = (ws[0].borrow(), us[0].borrow());

        // Compute the cross term `T` by following the original Nova paper.
        let z1 = Assignments::from((U.u, &U.x, &W.w));
        let z2 = Assignments::from((CM::Scalar::one(), &u[..], &w[..]));
        let t = pk.arith.evaluate_rows(|((a, b), c)| {
            let az1: CM::Scalar = a.iter().map(|(val, col)| z1[*col] * val).sum();
            let az2: CM::Scalar = a.iter().map(|(val, col)| z2[*col] * val).sum();
            let bz1: CM::Scalar = b.iter().map(|(val, col)| z1[*col] * val).sum();
            let bz2: CM::Scalar = b.iter().map(|(val, col)| z2[*col] * val).sum();
            let cz1: CM::Scalar = c.iter().map(|(val, col)| z1[*col] * val).sum();
            let cz2: CM::Scalar = c.iter().map(|(val, col)| z2[*col] * val).sum();
            Ok(az1 * bz2 + az2 * bz1 - z2[0] * cz1 - z1[0] * cz2)
        })?;

        let (cm, r) = CM::commit(&pk.ck, &[w, &t[..]].concat(), rng)?;

        let rho_bits = {
            transcript.add(&U);
            transcript.add(&u);
            transcript.add(&cm);
            transcript.challenge_bits(CHALLENGE_BITS)
        };
        let rho = CM::Scalar::from_bits_le(&rho_bits);

        Ok((
            RW {
                w: cfg_iter!(W.w)
                    .zip(&w[..])
                    .map(|(a, b)| rho * b + a)
                    .collect(),
                r: W.r + r * rho,
            },
            RU {
                u: U.u + rho,
                cm: U.cm + cm.mul(rho),
                x: cfg_iter!(U.x)
                    .zip(&u[..])
                    .map(|(a, b)| rho * b + a)
                    .collect(),
            },
            cm,
            rho_bits.try_into().unwrap(),
        ))
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemeVerifier<1, 1> for AbstractOva<CM, TF, CHALLENGE_BITS>
{
    fn verify(
        _vk: &(),
        transcript: &mut impl Transcript<TF>,
        Us: &[impl Borrow<Self::RU>; 1],
        us: &[impl Borrow<Self::IU>; 1],
        cm: &Self::Proof<1, 1>,
    ) -> Result<Self::RU, Error> {
        let (U, u) = (Us[0].borrow(), us[0].borrow());

        let rho_bits = {
            transcript.add(&U);
            transcript.add(&u);
            transcript.add(cm);
            transcript.challenge_bits(CHALLENGE_BITS)
        };
        let rho = CM::Scalar::from_bits_le(&rho_bits);

        Ok(RU {
            u: U.u + rho,
            cm: U.cm + cm.mul(rho),
            x: cfg_iter!(U.x)
                .zip(&u[..])
                .map(|(a, b)| rho * b + a)
                .collect(),
        })
    }
}

pub struct AbstractOvaGadget<CM, const CHALLENGE_BITS: usize = 128> {
    _t: PhantomData<CM>,
}

impl<CM, const CHALLENGE_BITS: usize> FoldingSchemeDefGadget
    for AbstractOvaGadget<CM, CHALLENGE_BITS>
where
    CM: CommitmentDefGadget<Widget: GroupBasedCommitment>,
{
    type Widget = AbstractOva<CM::Widget, CM::ConstraintField, CHALLENGE_BITS>;

    type CM = CM;
    type RU = RUVar<CM>;
    type IU = IUVar<CM::ScalarVar>;
    type VerifierKey = ();
    type Challenge = [Boolean<CM::ConstraintField>; CHALLENGE_BITS];
    type Proof<const M: usize, const N: usize> = CM::CommitmentVar;
}

impl<CM, const CHALLENGE_BITS: usize> FoldingSchemePartialVerifierGadget<1, 1>
    for AbstractOvaGadget<CM, CHALLENGE_BITS>
where
    CM: CommitmentDefGadget<Widget: GroupBasedCommitment>,
{
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
                cm: CM::CommitmentVar::new_witness(U.cm.cs().or(proof.cs()).or(rho.cs()), || {
                    Ok(U.cm.value().unwrap_or_default()
                        + proof.value().unwrap_or_default() * rho.value().unwrap_or_default())
                })?,
                x: U.x
                    .iter()
                    .zip(&u[..])
                    .map(|(a, b)| (b.clone() * &rho + a).try_into())
                    .collect::<Result<_, _>>()
                    .map_err(|_| SynthesisError::Unsatisfiable)?,
            },
            rho_bits.try_into().unwrap(),
        ))
    }
}

impl<CM, const CHALLENGE_BITS: usize> FoldingSchemeFullVerifierGadget<1, 1>
    for AbstractOvaGadget<CM, CHALLENGE_BITS>
where
    CM: CommitmentDefGadget<Widget: GroupBasedCommitment>,
    CM::CommitmentVar: CurveVar<<CM::Widget as CommitmentDef>::Commitment, CM::ConstraintField>,
{
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
            cm: proof.scalar_mul_le(rho_bits.iter())? + &U.cm,
            x: U.x
                .iter()
                .zip(&u[..])
                .map(|(a, b)| (b.clone() * &rho + a).try_into())
                .collect::<Result<_, _>>()
                .map_err(|_| SynthesisError::Unsatisfiable)?,
        })
    }
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

    fn test_ova_opt<TF: SonobeField>(
        rounds: usize,
        mut rng: impl RngCore,
    ) -> Result<(), Box<dyn Error>> {
        let config = (4, 4);

        test_folding_scheme::<AbstractOva<Pedersen<G1Projective, true>, TF>, 1, 1>(
            config,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<AbstractOva<Pedersen<G1Projective, false>, TF>, 1, 1>(
            config,
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
    fn test_ova() -> Result<(), Box<dyn Error>> {
        let mut rng = test_rng();

        test_ova_opt::<Fr>(10, &mut rng)?;
        test_ova_opt::<Fq>(10, &mut rng)?;
        Ok(())
    }
}
