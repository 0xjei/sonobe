//! Key generation for SuperNeo.

use ark_std::sync::Arc;
use sonobe_primitives::{
    algebra::{
        field::SonobeField,
        ring::{PolynomialRingConfig, PolynomialRingOverField},
    },
    arithmetizations::{Arith, ArithRelation, ccs::CCS},
    commitments::{CommitmentKey, CommitmentOps, GroupBasedCommitment},
    traits::SonobePrimeField,
    utils::null::Null,
};

use crate::{
    Error, FoldingSchemeKeyGenerator,
    superneo::{SuperNeo, SuperNeoConfig},
};

impl<Cfg: SuperNeoConfig, A: CCS<Field = Cfg::F> + ArithRelation<Vec<Cfg::F>, Vec<Cfg::F>>>
    FoldingSchemeKeyGenerator for SuperNeo<Cfg, A>
{
    fn generate_keys(ck: Self::PublicParam, ccs: Self::Arith) -> Result<Self::DeciderKey, Error> {
        let ck = Arc::new(ck);
        let ccs = Arc::new(ccs);
        let cfg = ccs.config();
        if ck.max_scalars_len() < cfg.n_witnesses {
            return Err(Error::InvalidPublicParameters(
                "The commitment key is too short for the CCS instance".into(),
            ));
        }
        Ok(Self::DeciderKey { arith: ccs, ck })
    }
}
