pub mod hypernova;
pub mod mova;
pub mod nova;
pub mod ova;
pub mod protogalaxy;

pub mod definitions;

pub use self::definitions::{
    algorithms::{
        FoldingSchemeDecider, FoldingSchemeKeyGenerator, FoldingSchemeOps,
        FoldingSchemePreprocessor, FoldingSchemeProver, FoldingSchemeVerifier,
    },
    circuits::{FoldingSchemeFullVerifierGadget, FoldingSchemePartialVerifierGadget},
    errors::Error,
    instances::{FoldingInstance, FoldingInstanceVar, PlainInstance, PlainInstanceVar},
    keys::DeciderKey,
    utils::TaggedVec,
    variants::{
        GroupBasedFoldingSchemePrimary, GroupBasedFoldingSchemePrimaryDef,
        GroupBasedFoldingSchemeSecondary, GroupBasedFoldingSchemeSecondaryDef,
    },
    witnesses::{FoldingWitness, FoldingWitnessVar, PlainWitness, PlainWitnessVar},
    FoldingSchemeDef, FoldingSchemeDefGadget,
};

#[cfg(test)]
mod tests {
    use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystem};
    use ark_std::{error::Error, rand::Rng, sync::Arc};
    use sonobe_primitives::{
        circuits::{AssignmentsOwned, ConstraintSystemBuilder},
        commitments::VectorCommitmentDef,
        relations::WitnessInstanceSampler,
        transcripts::{
            griffin::{sponge::GriffinSponge, GriffinParams},
            Transcript,
        },
    };

    use super::*;

    #[allow(non_snake_case)]
    pub fn test_folding_scheme<FS: FoldingSchemeOps<M, N>, const M: usize, const N: usize>(
        config: FS::Config,
        circuit: impl ConstraintSynthesizer<<FS::VC as VectorCommitmentDef>::Scalar>,
        assignments_vec: Vec<AssignmentsOwned<<FS::VC as VectorCommitmentDef>::Scalar>>,
        mut rng: impl Rng,
    ) -> Result<(), Box<dyn Error>>
    where
        FS::Arith: From<ConstraintSystem<<FS::VC as VectorCommitmentDef>::Scalar>>,
    {
        let pp = FS::preprocess(config, &mut rng)?;

        let cs = ConstraintSystemBuilder::new()
            .with_setup_mode()
            .with_circuit(circuit);
        let cs = cs.synthesize()?;
        let dk = FS::generate_keys(pp, cs.into())?;
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
