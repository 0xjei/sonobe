use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{
    GR1CSVar,
    alloc::{AllocVar, AllocationMode},
    fields::fp::FpVar,
    prelude::Boolean,
    select::CondSelectGadget,
};
use ark_relations::gr1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{
    borrow::Borrow,
    fmt::Debug,
    ops::{Deref, DerefMut},
    rand::RngCore,
};
use sonobe_primitives::{
    arithmetizations::{Arith, ArithConfig},
    circuits::AssignmentsOwned,
    commitments::{CommitmentDef, CommitmentDefGadget, GroupBasedCommitment},
    relations::{Relation, WitnessInstanceSampler},
    sumcheck::Error as SumCheckError,
    traits::{CF2, Dummy, SonobeField},
    transcripts::{Absorbable, AbsorbableVar, Transcript, TranscriptGadget},
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    ArithError(#[from] sonobe_primitives::arithmetizations::Error),
    #[error(transparent)]
    CommitmentError(#[from] sonobe_primitives::commitments::Error),
    #[error(transparent)]
    SynthesisError(#[from] SynthesisError),
    #[error(transparent)]
    SumCheckError(#[from] SumCheckError),
    #[error("Unsupported use case: {0}")]
    Unsupported(String),
    #[error("Failed to create domain")]
    DomainCreationFailure,
    #[error("Indivisible by vanishing polynomial")]
    IndivisibleByVanishingPoly,
    #[error("Unsatisfied relation: {0}")]
    UnsatisfiedRelation(String),
    #[error("Invalid public parameters: {0}")]
    InvalidPublicParameters(String),
}

pub trait FoldingWitness<VC: CommitmentDef>: Debug {
    const N_OPENINGS: usize;

    /// Returns the reference to all openings contained in the witness, each
    /// being a tuple of the values being committed to and the randomness.
    fn openings(&self) -> Vec<(&[VC::Scalar], &VC::Randomness)>;
}

pub trait FoldingInstance<VC: CommitmentDef>:
    Clone + Debug + PartialEq + Eq + Absorbable
{
    const N_COMMITMENTS: usize;

    /// Returns the commitments contained in the committed instance.
    fn commitments(&self) -> Vec<&VC::Commitment>;

    fn public_inputs(&self) -> &[VC::Scalar];

    fn public_inputs_mut(&mut self) -> &mut [VC::Scalar];
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TaggedVec<V, const TAG: char>(pub Vec<V>);

impl<V, const TAG: char> Deref for TaggedVec<V, TAG> {
    type Target = Vec<V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<V, const TAG: char> DerefMut for TaggedVec<V, TAG> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<V, const TAG: char> From<Vec<V>> for TaggedVec<V, TAG> {
    fn from(v: Vec<V>) -> Self {
        Self(v)
    }
}

impl<V, const TAG: char> From<TaggedVec<V, TAG>> for Vec<V> {
    fn from(val: TaggedVec<V, TAG>) -> Self {
        val.0
    }
}

impl<V: Absorbable, const TAG: char> Absorbable for TaggedVec<V, TAG> {
    fn absorb_into<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.0.absorb_into(dest)
    }
}

impl<F: PrimeField, V: AbsorbableVar<F>, const TAG: char> AbsorbableVar<F> for TaggedVec<V, TAG> {
    fn absorb_into(&self, dest: &mut Vec<FpVar<F>>) -> Result<(), SynthesisError> {
        self.0.absorb_into(dest)
    }
}

impl<F: Field, X: AllocVar<Y, F>, Y, const TAG: char> AllocVar<TaggedVec<Y, TAG>, F>
    for TaggedVec<X, TAG>
{
    fn new_variable<T: Borrow<TaggedVec<Y, TAG>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let v = f()?;
        Vec::new_variable(cs, || Ok(&v.borrow()[..]), mode).map(Self)
    }
}

impl<F: PrimeField, X: CondSelectGadget<F>, const TAG: char> CondSelectGadget<F>
    for TaggedVec<X, TAG>
{
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        if true_value.len() != false_value.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        true_value
            .iter()
            .zip(false_value.iter())
            .map(|(t, f)| cond.select(t, f))
            .collect::<Result<_, _>>()
            .map(Self)
    }
}

impl<F: Field, V: GR1CSVar<F>, const TAG: char> GR1CSVar<F> for TaggedVec<V, TAG> {
    type Value = TaggedVec<V::Value, TAG>;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.0.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        self.0.value().map(TaggedVec)
    }
}

pub type PlainWitness<V> = TaggedVec<V, 'w'>;

impl<V: Default + Clone, A: ArithConfig> Dummy<&A> for PlainWitness<V> {
    fn dummy(cfg: &A) -> Self {
        vec![V::default(); cfg.n_witnesses()].into()
    }
}

impl<VC: CommitmentDef> FoldingWitness<VC> for PlainWitness<VC::Scalar> {
    const N_OPENINGS: usize = 0;

    fn openings(&self) -> Vec<(&[VC::Scalar], &VC::Randomness)> {
        vec![]
    }
}

pub type PlainInstance<V> = TaggedVec<V, 'u'>;

impl<V: Default + Clone, A: ArithConfig> Dummy<&A> for PlainInstance<V> {
    fn dummy(cfg: &A) -> Self {
        vec![V::default(); cfg.n_public_inputs()].into()
    }
}

impl<VC: CommitmentDef> FoldingInstance<VC> for PlainInstance<VC::Scalar> {
    const N_COMMITMENTS: usize = 0;

    fn commitments(&self) -> Vec<&VC::Commitment> {
        vec![]
    }

    fn public_inputs(&self) -> &[VC::Scalar] {
        self
    }

    fn public_inputs_mut(&mut self) -> &mut [VC::Scalar] {
        self
    }
}

pub trait DeciderKey {
    type ProverKey;
    type VerifierKey;
    type ArithConfig: ArithConfig;

    fn to_pk(&self) -> &Self::ProverKey;
    fn to_vk(&self) -> &Self::VerifierKey;
    fn to_arith_config(&self) -> &Self::ArithConfig;
}

pub trait FoldingSchemeDef {
    type VC: CommitmentDef<Scalar: SonobeField>;
    type RW: FoldingWitness<Self::VC> + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
    type RU: FoldingInstance<Self::VC> + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
    type IW: FoldingWitness<Self::VC> + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
    type IU: FoldingInstance<Self::VC> + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
    type TranscriptField: SonobeField;
    type Arith: Arith<Config = <Self::DeciderKey as DeciderKey>::ArithConfig>;
    type Config;
    type PublicParam;
    type DeciderKey: DeciderKey
        + Clone
        + Relation<Self::RW, Self::RU, Error = Error>
        + Relation<Self::IW, Self::IU, Error = Error>
        + WitnessInstanceSampler<Self::RW, Self::RU, Source = (), Error = Error>
        + WitnessInstanceSampler<
            Self::IW,
            Self::IU,
            Source = AssignmentsOwned<<Self::VC as CommitmentDef>::Scalar>,
            Error = Error,
        >;
    type Challenge;
    type Proof<const M: usize, const N: usize>: Clone
        + for<'a> Dummy<&'a <Self::Arith as Arith>::Config>;
}

pub trait FoldingSchemePreprocessor: FoldingSchemeDef {
    /// The preprocessing method is a randomized algorithm that takes as input
    /// the size bounds of the folding scheme, which are contained in the
    /// `config` parameter, and outputs the public parameters.
    ///
    /// Here, the randomness source is controlled by `rng`.
    ///
    /// The security parameter is implicitly specified by the size of underlying
    /// fields and groups.
    fn preprocess(config: Self::Config, rng: impl RngCore) -> Result<Self::PublicParam, Error>;
}

pub trait FoldingSchemeKeyGenerator: FoldingSchemeDef {
    /// The key generation method is a deterministic algorithm that takes as
    /// input the public parameters `pp` and the constraint system `arith`, and
    /// outputs a prover key and a verifier key.
    fn generate_keys(pp: Self::PublicParam, arith: Self::Arith) -> Result<Self::DeciderKey, Error>;
}

pub trait FoldingSchemeProver<const M: usize, const N: usize>: FoldingSchemeDef {
    /// The proof generation method is a deterministic algorithm that takes as
    /// input the prover key `pk`, the transcript `transcript` between the
    /// prover and the verifier, the first witness-instance pair `W`, `U`, the
    /// second witness-instance pair `w`, `u`, and outputs the folded witness
    /// and instance, the proof, and the (intermediate) randomness.
    ///
    /// Here, the randomness source is controlled by `transcript`. The returned
    /// intermediate randomness is useful for the construction of CycleFold
    /// circuits in our CycleFold-based folding-to-IVC compiler.
    #[allow(non_snake_case)]
    fn prove(
        pk: &<Self::DeciderKey as DeciderKey>::ProverKey,
        transcript: &mut impl Transcript<Self::TranscriptField>,
        Ws: &[impl Borrow<Self::RW>; M],
        Us: &[impl Borrow<Self::RU>; M],
        ws: &[impl Borrow<Self::IW>; N],
        us: &[impl Borrow<Self::IU>; N],
        rng: impl RngCore,
    ) -> Result<(Self::RW, Self::RU, Self::Proof<M, N>, Self::Challenge), Error>;
}

pub trait FoldingSchemeVerifier<const M: usize, const N: usize>: FoldingSchemeDef {
    #[allow(non_snake_case)]
    fn verify(
        vk: &<Self::DeciderKey as DeciderKey>::VerifierKey,
        transcript: &mut impl Transcript<Self::TranscriptField>,
        Us: &[impl Borrow<Self::RU>; M],
        us: &[impl Borrow<Self::IU>; N],
        proof: &Self::Proof<M, N>,
    ) -> Result<Self::RU, Error>;
}

pub trait FoldingSchemeDecider: FoldingSchemeDef {
    #[allow(non_snake_case)]
    fn decide_running(dk: &Self::DeciderKey, W: &Self::RW, U: &Self::RU) -> Result<(), Error> {
        Relation::<Self::RW, Self::RU>::check_relation(dk, W, U)
    }

    fn decide_incoming(dk: &Self::DeciderKey, w: &Self::IW, u: &Self::IU) -> Result<(), Error> {
        Relation::<Self::IW, Self::IU>::check_relation(dk, w, u)
    }
}

impl<FS: FoldingSchemeDef> FoldingSchemeDecider for FS {}

pub trait FoldingSchemeOps<const M: usize, const N: usize>:
    FoldingSchemePreprocessor
    + FoldingSchemeKeyGenerator
    + FoldingSchemeProver<M, N>
    + FoldingSchemeVerifier<M, N>
    + FoldingSchemeDecider
{
}

impl<FS, const M: usize, const N: usize> FoldingSchemeOps<M, N> for FS where
    FS: FoldingSchemePreprocessor
        + FoldingSchemeKeyGenerator
        + FoldingSchemeProver<M, N>
        + FoldingSchemeVerifier<M, N>
        + FoldingSchemeDecider
{
}

pub trait FoldingWitnessVar<VC: CommitmentDefGadget>:
    AllocVar<Self::Value, VC::ConstraintField>
    + GR1CSVar<VC::ConstraintField, Value: FoldingWitness<VC::Widget>>
{
}

impl<VC: CommitmentDefGadget, T> FoldingWitnessVar<VC> for T where
    T: AllocVar<Self::Value, VC::ConstraintField>
        + GR1CSVar<VC::ConstraintField, Value: FoldingWitness<VC::Widget>>
{
}

pub trait FoldingInstanceVar<VC: CommitmentDefGadget>:
    AllocVar<Self::Value, VC::ConstraintField>
    + GR1CSVar<VC::ConstraintField, Value: FoldingInstance<VC::Widget>>
    + AbsorbableVar<VC::ConstraintField>
    + CondSelectGadget<VC::ConstraintField>
{
    /// Returns the commitments contained in the committed instance.
    fn commitments(&self) -> Vec<&VC::CommitmentVar>;

    fn public_inputs(&self) -> &Vec<VC::ScalarVar>;

    fn new_witness_with_public_inputs(
        cs: impl Into<Namespace<VC::ConstraintField>>,
        u: &Self::Value,
        x: Vec<VC::ScalarVar>,
    ) -> Result<Self, SynthesisError>;
}

pub type PlainWitnessVar<V> = PlainWitness<V>;
pub type PlainInstanceVar<V> = PlainInstance<V>;

impl<VC: CommitmentDefGadget> FoldingInstanceVar<VC> for PlainInstanceVar<VC::ScalarVar> {
    fn commitments(&self) -> Vec<&VC::CommitmentVar> {
        vec![]
    }

    fn public_inputs(&self) -> &Vec<VC::ScalarVar> {
        self
    }

    fn new_witness_with_public_inputs(
        _cs: impl Into<Namespace<VC::ConstraintField>>,
        _u: &Self::Value,
        x: Vec<VC::ScalarVar>,
    ) -> Result<Self, SynthesisError> {
        Ok(Self(x))
    }
}

pub trait FoldingSchemeGadgetDef {
    type Native: FoldingSchemeDef;

    type VC: CommitmentDefGadget<Widget = <Self::Native as FoldingSchemeDef>::VC>;
    type RU: FoldingInstanceVar<Self::VC, Value = <Self::Native as FoldingSchemeDef>::RU>;
    type IU: FoldingInstanceVar<Self::VC, Value = <Self::Native as FoldingSchemeDef>::IU>;

    type VerifierKey;

    type Challenge: AllocVar<
            <Self::Native as FoldingSchemeDef>::Challenge,
            <Self::VC as CommitmentDefGadget>::ConstraintField,
        > + GR1CSVar<
            <Self::VC as CommitmentDefGadget>::ConstraintField,
            Value = <Self::Native as FoldingSchemeDef>::Challenge,
        >;
    type Proof<const M: usize, const N: usize>: AllocVar<
            <Self::Native as FoldingSchemeDef>::Proof<M, N>,
            <Self::VC as CommitmentDefGadget>::ConstraintField,
        > + GR1CSVar<
            <Self::VC as CommitmentDefGadget>::ConstraintField,
            Value = <Self::Native as FoldingSchemeDef>::Proof<M, N>,
        >;
}

pub trait FoldingSchemeGadgetOpsPartial<const M: usize, const N: usize>:
    FoldingSchemeGadgetDef<Native: FoldingSchemeOps<M, N>>
{
    #[allow(non_snake_case)]
    fn verify_hinted(
        vk: &Self::VerifierKey,
        transcript: &mut impl TranscriptGadget<<Self::VC as CommitmentDefGadget>::ConstraintField>,
        Us: [&Self::RU; M],
        us: [&Self::IU; N],
        proof: &Self::Proof<M, N>,
    ) -> Result<(Self::RU, Self::Challenge), SynthesisError>;
}

pub trait FoldingSchemeGadgetOpsFull<const M: usize, const N: usize>:
    FoldingSchemeGadgetOpsPartial<M, N>
{
    #[allow(non_snake_case)]
    fn verify(
        vk: &Self::VerifierKey,
        transcript: &mut impl TranscriptGadget<<Self::VC as CommitmentDefGadget>::ConstraintField>,
        Us: [&Self::RU; M],
        us: [&Self::IU; N],
        proof: &Self::Proof<M, N>,
    ) -> Result<Self::RU, SynthesisError>;
}

pub trait GroupBasedFoldingSchemePrimaryDef:
    FoldingSchemeDef<
    VC: GroupBasedCommitment,
    TranscriptField = <<Self as FoldingSchemeDef>::VC as CommitmentDef>::Scalar,
>
{
    type Gadget: FoldingSchemeGadgetDef<
        Native = Self,
        VC = <Self::VC as GroupBasedCommitment>::Gadget2,
    >;
}

pub trait GroupBasedFoldingSchemePrimary<const M: usize, const N: usize>:
    GroupBasedFoldingSchemePrimaryDef<Gadget: FoldingSchemeGadgetOpsPartial<M, N>>
    + FoldingSchemeOps<M, N>
{
}

impl<FS, const M: usize, const N: usize> GroupBasedFoldingSchemePrimary<M, N> for FS where
    FS: GroupBasedFoldingSchemePrimaryDef<Gadget: FoldingSchemeGadgetOpsPartial<M, N>>
{
}

pub trait GroupBasedFoldingSchemeSecondaryDef:
    FoldingSchemeDef<
    VC: GroupBasedCommitment,
    TranscriptField = CF2<<<Self as FoldingSchemeDef>::VC as CommitmentDef>::Commitment>,
>
{
    type Gadget: FoldingSchemeGadgetDef<
        Native = Self,
        VC = <Self::VC as GroupBasedCommitment>::Gadget1,
    >;
}

pub trait GroupBasedFoldingSchemeSecondary<const M: usize, const N: usize>:
    GroupBasedFoldingSchemeSecondaryDef<Gadget: FoldingSchemeGadgetOpsFull<M, N>>
    + FoldingSchemeOps<M, N>
{
}

impl<FS, const M: usize, const N: usize> GroupBasedFoldingSchemeSecondary<M, N> for FS where
    FS: GroupBasedFoldingSchemeSecondaryDef<Gadget: FoldingSchemeGadgetOpsFull<M, N>>
{
}

#[cfg(test)]
mod tests {
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystem};
    use ark_std::{error::Error, rand::Rng, sync::Arc};
    use sonobe_primitives::{
        circuits::{ArithExtractor, AssignmentsOwned},
        transcripts::{
            griffin::{GriffinParams, sponge::GriffinSponge},
            poseidon::poseidon_canonical_config,
        },
    };

    use super::*;

    #[allow(non_snake_case)]
    pub fn test_folding_scheme<FS: FoldingSchemeOps<M, N>, const M: usize, const N: usize>(
        config: FS::Config,
        circuit: impl ConstraintSynthesizer<<FS::VC as CommitmentDef>::Scalar>,
        assignments_vec: Vec<AssignmentsOwned<<FS::VC as CommitmentDef>::Scalar>>,
        mut rng: impl Rng,
    ) -> Result<(), Box<dyn Error>>
    where
        FS::Arith: From<ConstraintSystem<<FS::VC as CommitmentDef>::Scalar>>,
    {
        let pp = FS::preprocess(config, &mut rng)?;

        let cs = ArithExtractor::new();
        cs.execute_synthesizer(circuit)?;
        let arith = cs.arith()?;
        let dk = FS::generate_keys(pp, arith)?;
        let pk = dk.to_pk();
        let vk = dk.to_vk();

        let mut Ws = vec![];
        let mut Us = vec![];
        for _ in 0..M {
            let (W, U) = WitnessInstanceSampler::<FS::RW, FS::RU>::sample(&dk, (), &mut rng)?;
            FS::decide_running(&dk, &W, &U)?;
            Ws.push(W);
            Us.push(U);
        }
        let mut Ws = Ws.try_into().unwrap();
        let mut Us = Us.try_into().unwrap();

        let config = Arc::new(GriffinParams::new(16, 5, 9));

        let mut transcript_p = GriffinSponge::new(&config);
        let mut transcript_v = GriffinSponge::new(&config);

        for assignments in assignments_vec {
            let mut ws = vec![];
            let mut us = vec![];
            for _ in 0..N {
                let (w, u) = WitnessInstanceSampler::<FS::IW, FS::IU>::sample(
                    &dk,
                    assignments.clone(),
                    &mut rng,
                )?;
                FS::decide_incoming(&dk, &w, &u)?;
                ws.push(w);
                us.push(u);
            }
            let ws = ws.try_into().unwrap();
            let us = us.try_into().unwrap();

            let (WW, UU, pi, _) = FS::prove(pk, &mut transcript_p, &Ws, &Us, &ws, &us, &mut rng)?;
            FS::decide_running(&dk, &WW, &UU)?;
            assert_eq!(FS::verify(vk, &mut transcript_v, &Us, &us, &pi)?, UU);

            for i in 0..M {
                let (W, U) = WitnessInstanceSampler::<FS::RW, FS::RU>::sample(&dk, (), &mut rng)?;
                FS::decide_running(&dk, &W, &U)?;
                Ws[i] = W;
                Us[i] = U;
            }
            if M != 0 {
                let idx = rng.gen_range(0..M);
                Ws[idx] = WW;
                Us[idx] = UU;
            }
        }

        Ok(())
    }
}
