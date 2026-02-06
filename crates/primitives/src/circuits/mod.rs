use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{GR1CSVar, alloc::AllocVar, fields::fp::FpVar};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError, SynthesisMode,
};
use ark_std::{
    fmt::Debug,
    ops::{Deref, Index, IndexMut},
};

use crate::transcripts::{Absorbable, AbsorbableGadget};

pub mod utils;

/// FCircuit defines the trait of the circuit of the F function, which is the one being folded (ie.
/// inside the agmented F' function).
/// The parameter z_i denotes the current state, and z_{i+1} denotes the next state after applying
/// the step.
/// Note that the external inputs for the specific circuit are defined at the implementation of
/// both `FCircuit::ExternalInputs` and `FCircuit::ExternalInputsVar`, where the `Default` trait
/// implementation for the `ExternalInputs` returns the initialized data structure (ie. if the type
/// contains a vector, it is initialized at the expected length).
pub trait FCircuit {
    type Field: PrimeField;
    type State: Clone + PartialEq + Absorbable;
    type StateVar: GR1CSVar<Self::Field, Value = Self::State>
        + AllocVar<Self::State, Self::Field>
        + AbsorbableGadget<Self::Field>;
    type ExternalInputs;
    type ExternalOutputs;

    fn dummy_state(&self) -> Self::State;

    fn dummy_external_inputs(&self) -> Self::ExternalInputs;

    /// generates the constraints for the step of F for the given z_i
    fn generate_step_constraints(
        // this method uses self, so that each FCircuit implementation (and different frontends)
        // can hold a state if needed to store data to generate the constraints.
        &self,
        cs: ConstraintSystemRef<Self::Field>,
        i: FpVar<Self::Field>,
        z_i: Self::StateVar,
        external_inputs: Self::ExternalInputs, // inputs that are not part of the state
    ) -> Result<(Self::StateVar, Self::ExternalOutputs), SynthesisError>;
}

#[derive(Clone, Debug, PartialEq)]
pub struct Assignments<F, V> {
    pub constant: F,
    pub public: V,
    pub private: V,
}

pub type AssignmentsOwned<F> = Assignments<F, Vec<F>>;

impl<F, V> From<(F, V, V)> for Assignments<F, V> {
    fn from((u, x, w): (F, V, V)) -> Self {
        Self {
            constant: u,
            public: x,
            private: w,
        }
    }
}

impl<F, V: AsRef<[F]>> Index<usize> for Assignments<F, V> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        let public = self.public.as_ref();
        let private = self.private.as_ref();
        if index == 0 {
            &self.constant
        } else if index <= public.len() {
            &public[index - 1]
        } else {
            &private[index - 1 - public.len()]
        }
    }
}

impl<F, V: AsRef<[F]> + AsMut<[F]>> IndexMut<usize> for Assignments<F, V> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let public = self.public.as_mut();
        let private = self.private.as_mut();
        if index == 0 {
            &mut self.constant
        } else if index <= public.len() {
            &mut public[index - 1]
        } else {
            &mut private[index - 1 - public.len()]
        }
    }
}

pub struct ConstraintSystemExt<F: Field, const ARITH_ENABLED: bool, const ASSIGNMENTS_ENABLED: bool>
{
    cs: ConstraintSystemRef<F>,
}
impl<F: Field, const ARITH_ENABLED: bool, const ASSIGNMENTS_ENABLED: bool> Deref
    for ConstraintSystemExt<F, ARITH_ENABLED, ASSIGNMENTS_ENABLED>
{
    type Target = ConstraintSystemRef<F>;

    fn deref(&self) -> &Self::Target {
        &self.cs
    }
}

impl<F: Field, const ARITH_ENABLED: bool, const ASSIGNMENTS_ENABLED: bool>
    ConstraintSystemExt<F, ARITH_ENABLED, ASSIGNMENTS_ENABLED>
{
    pub fn new() -> Self {
        let cs = ConstraintSystem::<F>::new_ref();
        let mode = if ASSIGNMENTS_ENABLED {
            SynthesisMode::Prove {
                construct_matrices: ARITH_ENABLED,
                generate_lc_assignments: ARITH_ENABLED,
            }
        } else {
            SynthesisMode::Setup
        };
        cs.set_mode(mode);
        Self { cs }
    }

    pub fn execute_synthesizer(
        &self,
        circuit: impl ConstraintSynthesizer<F>,
    ) -> Result<(), SynthesisError> {
        self.execute_fn(|cs| circuit.generate_constraints(cs))
    }

    pub fn execute_fn<R>(
        &self,
        circuit: impl FnOnce(ConstraintSystemRef<F>) -> Result<R, SynthesisError>,
    ) -> Result<R, SynthesisError> {
        let result = circuit(self.cs.clone())?;
        if ARITH_ENABLED {
            self.cs.finalize();
        }
        Ok(result)
    }
}

impl<F: Field, const ARITH_ENABLED: bool, const ASSIGNMENTS_ENABLED: bool> Default
    for ConstraintSystemExt<F, ARITH_ENABLED, ASSIGNMENTS_ENABLED>
{
    fn default() -> Self {
        Self::new()
    }
}

pub type ArithExtractor<F> = ConstraintSystemExt<F, true, false>;
pub type AssignmentsExtractor<F> = ConstraintSystemExt<F, false, true>;

impl<F: Field> ArithExtractor<F> {
    pub fn arith<A: From<ConstraintSystem<F>>>(self) -> Result<A, SynthesisError> {
        Ok(self.cs.into_inner().unwrap().into())
    }
}

impl<F: Field> AssignmentsExtractor<F> {
    pub fn assignments(self) -> Result<Assignments<F, Vec<F>>, SynthesisError> {
        let witness = self.cs.witness_assignment()?.to_vec();
        // skip the first element which is '1'
        let instance = self.cs.instance_assignment()?[1..].to_vec();

        Ok((F::one(), instance, witness).into())
    }
}
