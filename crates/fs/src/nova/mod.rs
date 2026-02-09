//! This module implements the Nova folding scheme, which is introduced in this
//! [paper].
//!
//! [paper]: https://eprint.iacr.org/2021/370.pdf

use ark_r1cs_std::boolean::Boolean;
use ark_std::{UniformRand, marker::PhantomData, rand::RngCore, sync::Arc};
use sonobe_primitives::{
    arithmetizations::{
        Arith, ArithConfig, ArithRelation,
        r1cs::{R1CS, RelaxedInstance, RelaxedWitness},
    },
    circuits::AssignmentsOwned,
    commitments::{CommitmentDef, CommitmentDefGadget, CommitmentOps, GroupBasedCommitment},
    relations::{Relation, WitnessInstanceSampler},
    traits::{CF2, SonobeField},
};

use self::{
    instances::{
        IncomingInstance as IU, RunningInstance as RU,
        circuits::{IncomingInstanceVar as IUVar, RunningInstanceVar as RUVar},
    },
    witnesses::{IncomingWitness as IW, RunningWitness as RW},
};
use crate::{
    DeciderKey, Error, FoldingSchemeDef, FoldingSchemeDefGadget, GroupBasedFoldingSchemePrimaryDef,
    GroupBasedFoldingSchemeSecondaryDef, PlainInstance as PU, PlainWitness as PW,
};

pub mod algorithms;
pub mod circuits;
pub mod instances;
pub mod witnesses;

/// [`NovaKey`] is Nova's decider key.
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
/// [`AbstractNova`] implements the Nova folding scheme which can operate on
/// both the primary and secondary curves.
pub struct AbstractNova<CM, TF, const CHALLENGE_BITS: usize = 128> {
    _t: PhantomData<(CM, TF)>,
}

/// [`Nova`] is the main Nova folding scheme on the primary curve.
pub type Nova<CM, const CHALLENGE_BITS: usize = 128> =
    AbstractNova<CM, <CM as CommitmentDef>::Scalar, CHALLENGE_BITS>;

/// [`CycleFoldNova`] is the Nova folding scheme on the secondary curve which
/// can be used as the folding scheme for folding CycleFold instances.
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

// used for the RO challenges.
// From [Srinath Setty](https://microsoft.com/en-us/research/people/srinath/): In Nova, soundness
// error ≤ 2/|S|, where S is the subset of the field F from which the challenges are drawn. In this
// case, we keep the size of S close to 2^128.
/// [`AbstractNova2`] implements the Nova folding scheme which can operate on
/// both the primary and secondary curves.
///
/// This design is experimental, following the definition of accumulation
/// schemes where the incoming witnesses and instances are simply plain vectors
/// in the circuit's assignments.
pub struct AbstractNova2<CM, TF, const CHALLENGE_BITS: usize = 128> {
    _t: PhantomData<(CM, TF)>,
}

/// [`Nova2`] is the main Nova folding scheme on the primary curve.
pub type Nova2<CM, const CHALLENGE_BITS: usize = 128> =
    AbstractNova2<CM, <CM as CommitmentDef>::Scalar, CHALLENGE_BITS>;

/// [`CycleFoldNova2`] is the Nova folding scheme on the secondary curve which
/// can be used as the folding scheme for folding CycleFold instances.
pub type CycleFoldNova2<CM, const CHALLENGE_BITS: usize = 128> =
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

/// [`AbstractNovaGadget`] is the in-circuit gadget for [`AbstractNova`].
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
    use ark_std::{error::Error, rand::thread_rng};
    use sonobe_primitives::{
        circuits::utils::{CircuitForTest, satisfying_assignments_for_test},
        commitments::pedersen::Pedersen,
    };
    #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
    use wasm_bindgen_test::wasm_bindgen_test as test;

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
        let mut rng = thread_rng();

        test_nova_opt::<Fr>(10, &mut rng)?;
        test_nova_opt::<Fq>(10, &mut rng)?;
        Ok(())
    }
}
