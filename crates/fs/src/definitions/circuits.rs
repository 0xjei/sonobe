use ark_relations::gr1cs::SynthesisError;
use sonobe_primitives::{commitments::VectorCommitmentDefGadget, transcripts::TranscriptVar};

use super::{
    algorithms::FoldingSchemeOps, FoldingSchemeDefGadget,
};

pub trait FoldingSchemePartialVerifierGadget<const M: usize, const N: usize>:
    FoldingSchemeDefGadget<Native: FoldingSchemeOps<M, N>>
{
    #[allow(non_snake_case)]
    fn verify_hinted(
        vk: &Self::VerifierKey,
        transcript: &mut impl TranscriptVar<<Self::VC as VectorCommitmentDefGadget>::ConstraintField>,
        Us: [&Self::RU; M],
        us: [&Self::IU; N],
        proof: &Self::Proof<M, N>,
    ) -> Result<(Self::RU, Self::Challenge), SynthesisError>;
}

pub trait FoldingSchemeFullVerifierGadget<const M: usize, const N: usize>:
    FoldingSchemePartialVerifierGadget<M, N>
{
    #[allow(non_snake_case)]
    fn verify(
        vk: &Self::VerifierKey,
        transcript: &mut impl TranscriptVar<<Self::VC as VectorCommitmentDefGadget>::ConstraintField>,
        Us: [&Self::RU; M],
        us: [&Self::IU; N],
        proof: &Self::Proof<M, N>,
    ) -> Result<Self::RU, SynthesisError>;
}
