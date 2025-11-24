use sonobe_primitives::{arithmetizations::ArithConfig, commitments::CommitmentDef, traits::Dummy};

use crate::FoldingWitness;

pub mod circuits;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunningWitness<CM: CommitmentDef> {
    pub w: Vec<CM::Scalar>,
    pub r: CM::Randomness,
}

impl<CM: CommitmentDef> FoldingWitness<CM> for RunningWitness<CM> {
    const N_OPENINGS: usize = 1;

    fn openings(&self) -> Vec<(&[CM::Scalar], &CM::Randomness)> {
        vec![(&self.w, &self.r)]
    }
}

impl<CM: CommitmentDef, Cfg: ArithConfig> Dummy<&Cfg> for RunningWitness<CM> {
    fn dummy(cfg: &Cfg) -> Self {
        Self {
            w: vec![Default::default(); cfg.n_witnesses()],
            r: Default::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IncomingWitness<CM: CommitmentDef> {
    pub w: Vec<CM::Scalar>,
    pub r: CM::Randomness,
}

impl<CM: CommitmentDef> FoldingWitness<CM> for IncomingWitness<CM> {
    const N_OPENINGS: usize = 1;

    fn openings(&self) -> Vec<(&[CM::Scalar], &CM::Randomness)> {
        vec![(&self.w, &self.r)]
    }
}

impl<CM: CommitmentDef, Cfg: ArithConfig> Dummy<&Cfg> for IncomingWitness<CM> {
    fn dummy(cfg: &Cfg) -> Self {
        Self {
            w: vec![Default::default(); cfg.n_witnesses()],
            r: Default::default(),
        }
    }
}
