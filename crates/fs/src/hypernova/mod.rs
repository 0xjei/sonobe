use ark_ff::{Field, One};
use ark_poly::{DenseMultilinearExtension as MLE, MultilinearExtension};
use ark_std::{
    UniformRand, borrow::Borrow, cfg_iter, marker::PhantomData, rand::RngCore, sync::Arc,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use sonobe_primitives::{
    algebra::ops::{
        bits::FromBits,
        pow::Pow,
        rlc::{ScalarRLC, SliceRLC},
    },
    arithmetizations::{
        Arith, ArithConfig, ArithRelation, Error as ArithError,
        ccs::{CCS, CCSConfig, CCSVariant},
        r1cs::R1CSConfig,
    },
    circuits::{Assignments, AssignmentsOwned},
    commitments::{CommitmentDef, CommitmentKey, CommitmentOps, GroupBasedCommitment},
    relations::{Relation, WitnessInstanceSampler},
    sumcheck::{
        Error as SumCheckError, SumCheck,
        utils::{EqPoly, VPAuxInfo, VirtualPolynomial},
    },
    traits::Dummy,
    transcripts::Transcript,
};

use self::{
    instance::{CCCSInstance as IU, LCCCSInstance as RU},
    witness::{CCCSWitness as IW, LCCCSWitness as RW},
};
use crate::{
    DeciderKey, Error, FoldingSchemeDef, FoldingSchemeKeyGenerator, FoldingSchemePreprocessor,
    FoldingSchemeProver, FoldingSchemeVerifier, PlainInstance as PU, PlainWitness as PW,
};

pub mod instance;
pub mod witness;

#[derive(Clone)]
pub struct HyperNovaKey<A, CM: CommitmentDef> {
    arith: Arc<A>,
    ck: Arc<CM::Key>,
}

impl<A: Arith, CM: CommitmentDef> DeciderKey for HyperNovaKey<A, CM> {
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

impl<CM: CommitmentDef<Scalar: Field>, V: CCSVariant> ArithRelation<RW<CM>, RU<CM>>
    for CCS<CM::Scalar, V>
{
    type Evaluation = Vec<CM::Scalar>;

    fn eval_relation(&self, w: &RW<CM>, u: &RU<CM>) -> Result<Self::Evaluation, ArithError> {
        let z = Assignments::from((u.u, &u.x, &w.w));
        Ok(self
            .mles(z)
            .iter()
            .map(|mle| mle.fix_variables(&u.r_x)[0])
            .collect())
    }

    fn check_evaluation(_w: &RW<CM>, u: &RU<CM>, e: Self::Evaluation) -> Result<(), ArithError> {
        cfg_iter!(e)
            .zip(&u.v)
            .all(|(e, v)| e == v)
            .then_some(())
            .ok_or(ArithError::UnsatisfiedAssignments(
                "Evaluation contains non-zero values".into(),
            ))
    }
}

impl<A, CM> Relation<RW<CM>, RU<CM>> for HyperNovaKey<A, CM>
where
    A: ArithRelation<RW<CM>, RU<CM>>,
    CM: CommitmentOps,
{
    type Error = Error;

    fn check_relation(&self, w: &RW<CM>, u: &RU<CM>) -> Result<(), Self::Error> {
        self.arith.check_relation(w, u)?;
        CM::open(&self.ck, &w.w, &w.r, &u.cm)?;
        Ok(())
    }
}

impl<A, CM> Relation<IW<CM>, IU<CM>> for HyperNovaKey<A, CM>
where
    A: ArithRelation<Vec<CM::Scalar>, Vec<CM::Scalar>>,
    CM: CommitmentOps,
{
    type Error = Error;

    fn check_relation(&self, w: &IW<CM>, u: &IU<CM>) -> Result<(), Self::Error> {
        self.arith.check_relation(&w.w, &u.x)?;
        CM::open(&self.ck, &w.w, &w.r, &u.cm)?;
        Ok(())
    }
}

impl<A, CM> Relation<PW<CM::Scalar>, PU<CM::Scalar>> for HyperNovaKey<A, CM>
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

impl<A, CM: CommitmentOps> WitnessInstanceSampler<IW<CM>, IU<CM>> for HyperNovaKey<A, CM> {
    type Source = AssignmentsOwned<CM::Scalar>;
    type Error = Error;

    fn sample(&self, z: Self::Source, rng: impl RngCore) -> Result<(IW<CM>, IU<CM>), Error> {
        let (w, x) = (z.private, z.public);
        let (cm, r) = CM::commit(&self.ck, &w, rng)?;
        Ok((IW { w, r }, IU { cm, x }))
    }
}

impl<A, CM: CommitmentDef> WitnessInstanceSampler<PW<CM::Scalar>, PU<CM::Scalar>>
    for HyperNovaKey<A, CM>
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

impl<A, CM> WitnessInstanceSampler<RW<CM>, RU<CM>> for HyperNovaKey<A, CM>
where
    A: ArithRelation<RW<CM>, RU<CM>, Evaluation = Vec<CM::Scalar>>,
    CM: CommitmentOps,
{
    type Source = ();
    type Error = Error;

    #[allow(non_snake_case)]
    fn sample(&self, _: Self::Source, mut rng: impl RngCore) -> Result<(RW<CM>, RU<CM>), Error> {
        let cfg = self.arith.config();

        let u = CM::Scalar::rand(&mut rng);
        let x = (0..cfg.n_public_inputs())
            .map(|_| CM::Scalar::rand(&mut rng))
            .collect::<Vec<_>>();
        let w = (0..cfg.n_witnesses())
            .map(|_| CM::Scalar::rand(&mut rng))
            .collect::<Vec<_>>();
        let (cm, r) = CM::commit(&self.ck, &w, &mut rng)?;

        let r_x = (0..cfg.log_constraints())
            .map(|_| CM::Scalar::rand(&mut rng))
            .collect();

        let W = RW { w, r };
        let mut U = RU {
            cm,
            x,
            u,
            r_x,
            v: vec![],
        };
        U.v = self.arith.eval_relation(&W, &U)?;

        Ok((W, U))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NIMFSProof<F, const M: usize, const N: usize> {
    pub sc_proof: Vec<Vec<F>>,
    pub sigmas: Vec<F>,
    pub thetas: Vec<F>,
}

impl<F: Field, const M: usize, const N: usize, V: CCSVariant> Dummy<&CCSConfig<V>>
    for NIMFSProof<F, M, N>
{
    fn dummy(cfg: &CCSConfig<V>) -> Self {
        let s = cfg.log_constraints();
        let d = cfg.degree();
        let t = V::n_matrices();
        Self {
            sc_proof: vec![vec![F::zero(); d + 2]; s],
            sigmas: vec![F::zero(); t * M],
            thetas: vec![F::zero(); t * N],
        }
    }
}

pub struct HyperNova<CM, V: CCSVariant = R1CSConfig, const CHALLENGE_BITS: usize = 128> {
    _t: PhantomData<(CM, V)>,
}

impl<CM: GroupBasedCommitment, V: CCSVariant, const CHALLENGE_BITS: usize> FoldingSchemeDef
    for HyperNova<CM, V, CHALLENGE_BITS>
{
    type CM = CM;
    type RW = RW<CM>;
    type RU = RU<CM>;
    type IW = IW<CM>;
    type IU = IU<CM>;

    type TranscriptField = CM::Scalar;
    type Arith = CCS<CM::Scalar, V>;

    type Config = usize;
    type PublicParam = CM::Key;
    type DeciderKey = HyperNovaKey<Self::Arith, CM>;
    type Challenge = [bool; CHALLENGE_BITS];
    type Proof<const M: usize, const N: usize> = NIMFSProof<CM::Scalar, M, N>;
}

impl<CM: GroupBasedCommitment, V: CCSVariant, const CHALLENGE_BITS: usize> FoldingSchemePreprocessor
    for HyperNova<CM, V, CHALLENGE_BITS>
{
    fn preprocess(ck_len: usize, mut rng: impl RngCore) -> Result<Self::PublicParam, Error> {
        let ck = CM::generate_key(ck_len, &mut rng)?;
        Ok(ck)
    }
}

impl<CM: GroupBasedCommitment, V: CCSVariant, const CHALLENGE_BITS: usize> FoldingSchemeKeyGenerator
    for HyperNova<CM, V, CHALLENGE_BITS>
{
    fn generate_keys(ck: Self::PublicParam, ccs: Self::Arith) -> Result<Self::DeciderKey, Error> {
        let ck = Arc::new(ck);
        let ccs = Arc::new(ccs);
        if ck.max_scalars_len() < ccs.config().n_witnesses() {
            return Err(Error::InvalidPublicParameters(
                "The commitment key is too short for the CCS instance".into(),
            ));
        }
        Ok(Self::DeciderKey { arith: ccs, ck })
    }
}

impl<
    CM: GroupBasedCommitment,
    V: CCSVariant,
    const M: usize,
    const N: usize,
    const CHALLENGE_BITS: usize,
> FoldingSchemeProver<M, N> for HyperNova<CM, V, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn prove(
        pk: &HyperNovaKey<Self::Arith, CM>,
        transcript: &mut impl Transcript<CM::Scalar>,
        Ws: &[impl Borrow<Self::RW>; M],
        Us: &[impl Borrow<Self::RU>; M],
        ws: &[impl Borrow<Self::IW>; N],
        us: &[impl Borrow<Self::IU>; N],
        _rng: impl RngCore,
    ) -> Result<(Self::RW, Self::RU, Self::Proof<M, N>, Self::Challenge), Error> {
        let Ws = &Ws.iter().map(|i| i.borrow()).collect::<Vec<_>>();
        let Us = &Us.iter().map(|i| i.borrow()).collect::<Vec<_>>();
        let ws = &ws.iter().map(|i| i.borrow()).collect::<Vec<_>>();
        let us = &us.iter().map(|i| i.borrow()).collect::<Vec<_>>();

        let ccs = &pk.arith;
        let d = V::degree();
        let s = ccs.config().log_constraints();
        let t = V::n_matrices();
        let S = &V::multisets_vec();
        let c = &V::coefficients_vec::<CM::Scalar>();

        // absorb instances to transcript
        transcript.add(&Us[..]);
        transcript.add(&us[..]);

        // Step 1: Get some challenges
        let gamma = transcript.challenge_field_element();
        let beta = transcript.challenge_field_elements(s);

        let gamma_powers = gamma.powers(M * t + N);
        let (running_gammas, incoming_gammas) = gamma_powers.split_at(M * t);

        // Compute g(x)
        let running_mles = Ws
            .iter()
            .zip(Us)
            .flat_map(|(W, U)| ccs.mles((U.u, &U.x, &W.w).into()));
        let incoming_mles = ws
            .iter()
            .zip(us)
            .flat_map(|(w, u)| ccs.mles((One::one(), &u.x, &w.w).into()));
        let eq_mles = Us
            .iter()
            .map(|U| &U.r_x)
            .chain([&beta])
            .map(|r| MLE::from_evaluations_vec(s, EqPoly::fix_y_evals(r)));

        let running_products = running_gammas
            .iter()
            .enumerate()
            .map(|(i, &gamma)| (gamma, vec![i, (M + N) * t + i / t]));
        let incoming_products = incoming_gammas.iter().enumerate().flat_map(|(k, gamma)| {
            S.iter().zip(c).map(move |(S_i, &c_i)| {
                (
                    c_i * gamma,
                    S_i.iter()
                        .map(|j| (M + k) * t + j)
                        .chain([(M + N) * t + M])
                        .collect(),
                )
            })
        });

        let g = VirtualPolynomial {
            aux_info: VPAuxInfo {
                num_variables: s,
                max_degree: d + 1,
            },
            flattened_ml_extensions: running_mles.chain(incoming_mles).chain(eq_mles).collect(),
            products: running_products.chain(incoming_products).collect(),
        };

        // Step 3: Run the sumcheck prover
        // Step 2: dig into the sumcheck and extract r_x_prime
        let (sumcheck_proof, r_x_prime, mles) = SumCheck::prove(g, transcript)?;

        // Step 4: compute sigmas and thetas
        let sigmas = mles[0..t * M]
            .iter()
            .map(|mle| mle.fix_variables(&[])[0])
            .collect::<Vec<_>>();
        let thetas = mles[t * M..t * (M + N)]
            .iter()
            .map(|mle| mle.fix_variables(&[])[0])
            .collect::<Vec<_>>();

        // Step 6: Get the folding challenge
        let rho_bits = transcript.challenge_bits(CHALLENGE_BITS);
        let rho = CM::Scalar::from_bits_le(&rho_bits);

        let rho_powers = rho.powers(M + N);

        Ok((
            Self::RW {
                w: Ws
                    .iter()
                    .map(|w| &w.w[..])
                    .chain(ws.iter().map(|w| &w.w[..]))
                    .slice_rlc(&rho_powers),
                r: Ws
                    .iter()
                    .map(|w| w.r)
                    .chain(ws.iter().map(|w| w.r))
                    .scalar_rlc(&rho_powers),
            },
            Self::RU {
                cm: Us
                    .iter()
                    .map(|u| u.cm)
                    .chain(us.iter().map(|u| u.cm))
                    .scalar_rlc(&rho_powers),
                u: Us
                    .iter()
                    .map(|u| u.u)
                    .chain([CM::Scalar::one(); N])
                    .scalar_rlc(&rho_powers),
                x: Us
                    .iter()
                    .map(|u| &u.x[..])
                    .chain(us.iter().map(|u| &u.x[..]))
                    .slice_rlc(&rho_powers),
                r_x: r_x_prime,
                v: sigmas
                    .chunks(t)
                    .chain(thetas.chunks(t))
                    .slice_rlc(&rho_powers),
            },
            NIMFSProof {
                sc_proof: sumcheck_proof,
                sigmas,
                thetas,
            },
            rho_bits.try_into().unwrap(),
        ))
    }
}

impl<
    CM: GroupBasedCommitment,
    V: CCSVariant,
    const M: usize,
    const N: usize,
    const CHALLENGE_BITS: usize,
> FoldingSchemeVerifier<M, N> for HyperNova<CM, V, CHALLENGE_BITS>
{
    #[allow(non_snake_case)]
    fn verify(
        _vk: &(),
        transcript: &mut impl Transcript<CM::Scalar>,
        Us: &[impl Borrow<Self::RU>; M],
        us: &[impl Borrow<Self::IU>; N],
        proof: &Self::Proof<M, N>,
    ) -> Result<Self::RU, Error> {
        let Us = &Us.iter().map(|i| i.borrow()).collect::<Vec<_>>();
        let us = &us.iter().map(|i| i.borrow()).collect::<Vec<_>>();

        let d = V::degree();
        let s = proof.sc_proof.len();
        let t = V::n_matrices();
        let S = &V::multisets_vec();
        let c = &V::coefficients_vec::<CM::Scalar>();

        // absorb instances to transcript
        transcript.add(&Us[..]);
        transcript.add(&us[..]);

        // Step 1: Get some challenges
        let gamma = transcript.challenge_field_element();
        let beta = transcript.challenge_field_elements(s);

        let gamma_powers = gamma.powers(M * t + N);

        let vp_aux_info = VPAuxInfo {
            max_degree: d + 1,
            num_variables: s,
        };

        // Step 3: Start verifying the sumcheck
        // First, compute the expected sumcheck sum: \sum gamma^j v_j
        let sum_v_j_gamma = Us
            .iter()
            .zip(gamma_powers.chunks(t))
            .flat_map(|(U, gammas)| U.v.iter().zip(gammas).map(|(&v, &g)| v * g))
            .sum();

        // Verify the interactive part of the sumcheck
        // Step 2: Dig into the sumcheck claim and extract the randomness used
        let (claimed_eval, r_x_prime) =
            SumCheck::verify(sum_v_j_gamma, &proof.sc_proof, &vp_aux_info, transcript)?;

        // Step 5: Finish verifying sumcheck (verify the claim c)
        let e_beta = EqPoly::fix_xy_eval(&beta, &r_x_prime);
        let c = proof
            .sigmas
            .chunks(t)
            .zip(Us)
            .flat_map(|(sigmas, u)| {
                let e_lcccs = EqPoly::fix_xy_eval(&u.r_x, &r_x_prime);
                sigmas.iter().map(move |sigma_j| e_lcccs * sigma_j)
            })
            .chain(proof.thetas.chunks(t).map(|thetas| {
                S.iter()
                    .zip(c)
                    .map(|(S_i, &c_i)| c_i * S_i.iter().map(|&j| thetas[j]).product::<CM::Scalar>())
                    .sum::<CM::Scalar>()
                    * e_beta
            }))
            .zip(gamma_powers)
            .map(|(val, gamma_i)| val * gamma_i)
            .sum::<CM::Scalar>();
        // check that the g(r_x') from the sumcheck proof is equal to the computed c from sigmas&thetas
        (c == claimed_eval).then_some(()).ok_or_else(|| {
            SumCheckError::IncorrectEvaluation(claimed_eval.to_string(), c.to_string())
        })?;

        // Step 6: Get the folding challenge
        let rho_bits = transcript.challenge_bits(CHALLENGE_BITS);
        let rho = CM::Scalar::from_bits_le(&rho_bits);

        let rho_powers = rho.powers(M + N);

        Ok(Self::RU {
            cm: Us
                .iter()
                .map(|u| u.cm)
                .chain(us.iter().map(|u| u.cm))
                .scalar_rlc(&rho_powers),
            u: Us
                .iter()
                .map(|u| u.u)
                .chain([CM::Scalar::one(); N])
                .scalar_rlc(&rho_powers),
            x: Us
                .iter()
                .map(|u| &u.x[..])
                .chain(us.iter().map(|u| &u.x[..]))
                .slice_rlc(&rho_powers),
            r_x: r_x_prime,
            v: proof
                .sigmas
                .chunks(t)
                .chain(proof.thetas.chunks(t))
                .slice_rlc(&rho_powers),
        })
    }
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

    use super::*;
    use crate::tests::test_folding_scheme;

    fn test_hypernova_opt<const M: usize, const N: usize>(
        rounds: usize,
        mut rng: impl Rng,
    ) -> Result<(), Box<dyn Error>> {
        test_folding_scheme::<HyperNova<Pedersen<G1Projective, true>>, M, N>(
            8,
            CircuitForTest {
                x: Fr::rand(&mut rng),
            },
            (0..rounds)
                .map(|_| satisfying_assignments_for_test(Fr::rand(&mut rng)))
                .collect(),
            &mut rng,
        )?;

        test_folding_scheme::<HyperNova<Pedersen<G1Projective, false>>, M, N>(
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
    fn test_hypernova() -> Result<(), Box<dyn Error>> {
        let mut rng = thread_rng();
        test_hypernova_opt::<1, 1>(10, &mut rng)?;
        test_hypernova_opt::<1, 3>(10, &mut rng)?;
        test_hypernova_opt::<3, 1>(10, &mut rng)?;
        test_hypernova_opt::<3, 3>(10, &mut rng)?;
        test_hypernova_opt::<0, 5>(10, &mut rng)?;
        test_hypernova_opt::<5, 0>(10, &mut rng)?;
        Ok(())
    }
}
