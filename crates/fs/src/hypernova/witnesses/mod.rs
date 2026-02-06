use sonobe_primitives::{arithmetizations::ArithConfig, commitments::CommitmentDef, traits::Dummy};

use crate::FoldingWitness;

pub mod circuits;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LCCCSWitness<CM: CommitmentDef> {
    pub w: Vec<CM::Scalar>,
    pub r: CM::Randomness,
}

impl<CM: CommitmentDef> FoldingWitness<CM> for LCCCSWitness<CM> {
    const N_OPENINGS: usize = 1;

    fn openings(&self) -> Vec<(&[CM::Scalar], &CM::Randomness)> {
        vec![(&self.w, &self.r)]
    }
}

impl<CM: CommitmentDef, Cfg: ArithConfig> Dummy<&Cfg> for LCCCSWitness<CM> {
    fn dummy(cfg: &Cfg) -> Self {
        Self {
            w: vec![Default::default(); cfg.n_witnesses()],
            r: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CCCSWitness<CM: CommitmentDef> {
    pub w: Vec<CM::Scalar>,
    pub r: CM::Randomness,
}

impl<CM: CommitmentDef> FoldingWitness<CM> for CCCSWitness<CM> {
    const N_OPENINGS: usize = 1;

    fn openings(&self) -> Vec<(&[CM::Scalar], &CM::Randomness)> {
        vec![(&self.w, &self.r)]
    }
}

impl<CM: CommitmentDef, Cfg: ArithConfig> Dummy<&Cfg> for CCCSWitness<CM> {
    fn dummy(cfg: &Cfg) -> Self {
        Self {
            w: vec![Default::default(); cfg.n_witnesses()],
            r: Default::default(),
        }
    }
}
