// Proving & verifying a long hash chain with IVC.
//
// Run with `cargo run --release --example hash_chain`.
// Add `--features parallel` for faster proof generation.

use ark_bn254::{Fr, G1Projective};
use ark_crypto_primitives::sponge::poseidon::{
    PoseidonConfig, PoseidonSponge, constraints::PoseidonSpongeVar,
};
use ark_grumpkin::Projective;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::gr1cs::SynthesisError;
use ark_std::{error::Error, rand::thread_rng};
use sonobe_ivc::{IVC, IVCStatefulProver, compilers::cyclefold::adapters::nova::NovaNovaIVC};
use sonobe_primitives::{
    circuits::FCircuit,
    commitments::pedersen::Pedersen,
    transcripts::{TranscriptGadget, poseidon::poseidon_paper_config},
};

// 0. Define the circuit and implement the `FCircuit` trait.
struct HashChainCircuit {
    config: PoseidonConfig<Fr>,
}

impl FCircuit for HashChainCircuit {
    type Field = Fr;

    // The chain value carried from one step to the next.
    type State = [Fr; 1];
    // The in-circuit counterpart.
    type StateVar = [FpVar<Fr>; 1];

    // The chain is self-contained, so no per-step data is exchanged with the
    // outside world.
    type ExternalInputs = ();
    type ExternalOutputs = ();

    // It's important to safely implement `same_state_shape`, especially when
    // you have a custom State with dynamic members.
    fn same_state_shape(_a: &Self::State, _b: &Self::State) -> bool {
        // `[Fr; 1]` is fixed-size, so all states trivially share a shape.
        // A variable-length state must compare its lengths here.
        true
    }

    // Implement `dummy_state` to tell IVC what the state will look like. This
    // is used for IVC key generation, at which point the actual state being
    // proved is unknown, so you need to specify the dummy state with the same
    // shape.
    fn dummy_state(&self) -> Self::State {
        [Fr::from(0)]
    }

    // Implement `dummy_external_inputs` to tell IVC what the external inputs
    // will look like. This is used for IVC key generation, at which point the
    // actual external inputs used for proof generation is unknown, so you need
    // to specify the dummy external inputs with the same shape.
    fn dummy_external_inputs(&self) -> Self::ExternalInputs {}

    // The core logic of step circuit, which takes the current state as input,
    // updates it, and returns the updated state.
    fn generate_step_constraints(
        &self,
        _i: FpVar<Self::Field>,
        state: Self::StateVar,
        _external_inputs: Self::ExternalInputs,
    ) -> Result<(Self::StateVar, Self::ExternalOutputs), SynthesisError> {
        let [z] = state;

        let mut sponge = PoseidonSpongeVar::new(self.config.clone());
        sponge.add(&z)?;

        Ok(([sponge.get_field_element()?], ()))
    }
}

/// Instantiate [`NovaNovaIVC`].
/// - `Pedersen<G1Projective, true>`: Pedersen over BN254 with hiding is the
///   underlying commitment scheme for the primary folding scheme
/// - `Pedersen<Projective, true>`: Pedersen over Grumpkin with hiding is the
///   underlying commitment scheme for the secondary (CycleFold) folding scheme
/// - `PoseidonSponge<Fr>`: Poseidon is the sponge for Fiat-Shamir transcript
type I = NovaNovaIVC<Pedersen<G1Projective, true>, Pedersen<Projective, true>, PoseidonSponge<Fr>>;

fn main() -> Result<(), Box<dyn Error>> {
    let mut rng = thread_rng();

    let config = poseidon_paper_config::<Fr, 128>(5, 4);

    // We want to prove the execution of a hash chain circuit starting from 1
    // as the initial state for 5 steps.
    let step_circuit = HashChainCircuit {
        config: config.clone(),
    };
    let initial_state = [Fr::from(1)];
    let n_steps = 5;

    // 1. Generate public parameters, which only depend on the configuration and
    //    can be reused for any step circuit satisfying the configuration.
    //    In the configuration, we need to specify:
    //    - the size upper bound of the augmented step circuit (the step circuit
    //      size + ~60k for recursion overhead)
    //    - the size upper bound of the CycleFold circuit (2048 for Nova)
    //    - the transcript config
    //    An under-estimate is caught at key generation.
    let pp = I::preprocess((65536, 2048, config.clone()), &mut rng)?;

    // 2. Generate the keys, which are specific to this step circuit.
    let (pk, vk) = I::generate_keys(pp, &step_circuit)?;

    // 3. Generate the proof incrementally. Here we use `IVCStatefulProver`, so
    //    we don't need to manually manage intermediate states and proofs.
    let mut prover = IVCStatefulProver::<_, I>::new(&pk, &step_circuit, initial_state)?;
    for _ in 0..n_steps {
        prover.prove_step((), &mut rng)?;
    }

    // 4. Verify the proof. In practice, the verifier may additionally check
    //    `i`, `initial_state`, and `current_state` against application-specific
    //    requirements.
    I::verify::<HashChainCircuit>(
        &vk,
        prover.i,
        &prover.initial_state,
        &prover.current_state,
        &prover.current_proof,
    )?;
    println!(
        "verified a chain of {} hashes that updates {:?} to {:?}",
        prover.i, prover.initial_state, prover.current_state
    );

    Ok(())
}
