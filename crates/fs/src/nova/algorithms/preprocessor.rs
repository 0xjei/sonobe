use ark_std::rand::RngCore;
use sonobe_primitives::{commitments::GroupBasedCommitment, traits::SonobeField};

use crate::{
    Error, FoldingSchemePreprocessor,
    nova::{AbstractNova, AbstractNova2},
};

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemePreprocessor for AbstractNova<CM, TF, CHALLENGE_BITS>
{
    fn preprocess(ck_len: usize, mut rng: impl RngCore) -> Result<Self::PublicParam, Error> {
        let ck = CM::generate_key(ck_len, &mut rng)?;
        Ok(ck)
    }
}

impl<CM: GroupBasedCommitment, TF: SonobeField, const CHALLENGE_BITS: usize>
    FoldingSchemePreprocessor for AbstractNova2<CM, TF, CHALLENGE_BITS>
{
    fn preprocess(ck_len: usize, mut rng: impl RngCore) -> Result<Self::PublicParam, Error> {
        let ck = CM::generate_key(ck_len, &mut rng)?;
        Ok(ck)
    }
}
