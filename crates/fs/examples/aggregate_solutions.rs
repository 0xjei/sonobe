// Aggregating solutions to an equation with a folding scheme.
//
// Run with `cargo run --release --example aggregate_solutions`.
// Add `--features parallel` for faster proof generation.

use ark_bn254::{Fr, G1Projective};
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_ff::UniformRand;
use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{FieldVar, fp::FpVar},
};
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{error::Error, rand::thread_rng};
use sonobe_fs::{
    DeciderKey, FoldingInstance, FoldingSchemeDecider, FoldingSchemeKeyGenerator,
    FoldingSchemePreprocessor, FoldingSchemeProver, FoldingSchemeVerifier,
    nova::{
        Nova,
        instances::{IncomingInstance, RunningInstance},
        witnesses::{IncomingWitness, RunningWitness},
    },
};
use sonobe_primitives::{
    arithmetizations::r1cs::R1CS,
    circuits::{ArithExtractor, AssignmentsExtractor},
    commitments::pedersen::Pedersen,
    relations::WitnessInstanceSampler,
    transcripts::{Transcript, poseidon::poseidon_paper_config},
};

// 0. Define the circuit and implement arkworks' `ConstraintSynthesizer` trait.
//    Here the prover wants to show that `x` is indeed a solution to x^5 - 15x^4
//    + 85x^3 - 225x^2 + 274x - 120 = 0
struct SolutionCircuit {
    // The root being claimed.
    x: Fr,
}

impl ConstraintSynthesizer<Fr> for SolutionCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x = FpVar::new_input(cs, || Ok(self.x))?;

        let x2 = &x * &x;
        let x3 = &x2 * &x;
        let x4 = &x3 * &x;
        let x5 = &x4 * &x;

        // x^5 - 15x^4 + 85x^3 - 225x^2 + 274x - 120
        let p = x5 - x4 * Fr::from(15) + x3 * Fr::from(85) - x2 * Fr::from(225) + x * Fr::from(274)
            - Fr::from(120);

        p.enforce_equal(&FpVar::zero())
    }
}

/// Instantiate [`Nova`].
/// - `Pedersen<G1Projective, true>`: Pedersen over BN254 with hiding is the
///   underlying commitment scheme
type FS = Nova<Pedersen<G1Projective, true>>;

fn main() -> Result<(), Box<dyn Error>> {
    let mut rng = thread_rng();

    let config = poseidon_paper_config::<Fr, 128>(5, 4);

    // The prover's claimed roots. They could each come from a different prover.
    let roots = [1, 2, 3, 4, 5, 3, 1, 5, 5, 2].map(Fr::from);
    // What the verifier ends up knowing: one claimed root per fold.
    let mut claims = vec![];

    // 1. Generate public parameters, which only depend on the configuration and
    //    can be reused for any circuit satisfying the configuration.
    //    In the configuration, we need to specify the the size upper bound of
    //    the circuit. For Nova, this is the maximum of the number of witnesses
    //    and the number of constraints. An under-estimate is caught at key
    //    generation.
    let pp = FS::preprocess(1024, &mut rng)?;

    // 2. Generate the keys, which are specific to this relation.
    let dk = FS::generate_keys(pp, {
        // Extract R1CS matrices of the relation. Only the shape of the circuit
        // is recorded, so the values passed here are irrelevant.
        let cs = ArithExtractor::new();
        cs.execute_synthesizer(SolutionCircuit {
            x: Fr::rand(&mut rng),
        })?;
        cs.arith::<R1CS<_>>()?
    })?;
    let (pk, vk) = (dk.to_pk(), dk.to_vk());

    // 3. Start folding.
    //
    // The prover and verifier agree with the same satisfying witness-instance
    // pair in the beginning
    #[allow(non_snake_case)]
    let (mut W, mut U): (RunningWitness<_>, RunningInstance<_>) = dk.sample((), &mut rng)?;
    // The prover and verifier maintain their own transcripts
    let mut transcript_p = PoseidonSponge::new(config.clone());
    let mut transcript_v = PoseidonSponge::new(config);

    for x in roots {
        // 3.1. The prover constructs an incoming witness-instance pair.
        let (w, u): (IncomingWitness<_>, IncomingInstance<_>) = dk.sample(
            {
                // Run the circuit on a fresh claim and collect its assignments.
                let cs = AssignmentsExtractor::new();
                cs.execute_synthesizer(SolutionCircuit { x })?;
                cs.assignments()?
            },
            &mut rng,
        )?;

        // 3.2. The prover folds both witnesses and instances.
        let (folded_w, folded_u, proof) =
            FS::prove(pk, &mut transcript_p, &[&W], &[&U], &[&w], &[&u], &mut rng)?;

        // 3.3 The proof is sent to the verifier.

        // 3.4. The verifier only folds instances. The folded instance should be
        //      the same as prover's.
        assert_eq!(
            folded_u,
            FS::verify(vk, &mut transcript_v, &[&U], &[&u], &proof)?
        );
        claims.push(u.public_inputs()[0]);

        W = folded_w;
        U = folded_u;
    }

    // 4. The prover sends the folded witness to the verifier.
    //    The verifier checks it against the locally folded instance. A false
    //    claim is accumulated through every step above and is caught here.
    FS::decide_running(&dk, &W, &U)?;

    // We are confident that all claims are true, i.e., all of them are roots of
    // the equation, but the verifier may expect additional properties, say,
    // distinct roots, which cannot be guaranteed by folding itself. Therefore,
    // whether these claims are worth accepting is for the verifier to judge.
    println!("Verified claims {claims:?}");

    Ok(())
}
