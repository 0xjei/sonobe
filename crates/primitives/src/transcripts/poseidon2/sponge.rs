//! Poseidon2 duplex sponge and its transcript-trait impls, ported from
//! arkworks' [`ark_crypto_primitives::sponge::poseidon`].

use ark_crypto_primitives::sponge::DuplexSpongeMode;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::{FieldVar, fp::FpVar};
use ark_relations::gr1cs::SynthesisError;
use ark_std::sync::Arc;

use crate::transcripts::{
    AbsorbableVar, Transcript, TranscriptGadget,
    poseidon2::{Poseidon2, Poseidon2Gadget, Poseidon2Params},
};

/// A duplex sponge built on the Poseidon2 permutation.
#[derive(Clone)]
pub struct Poseidon2Sponge<F: PrimeField> {
    params: Arc<Poseidon2Params<F>>,
    state: Vec<F>,
    mode: DuplexSpongeMode,
}

impl<F: PrimeField> Poseidon2Sponge<F> {
    fn permute(&mut self) {
        Poseidon2::permute(&self.params, &mut self.state);
    }

    fn absorb_internal(&mut self, mut rate_start_index: usize, elements: &[F]) {
        let mut remaining_elements = elements;
        loop {
            if rate_start_index + remaining_elements.len() <= self.params.rate {
                for (i, element) in remaining_elements.iter().enumerate() {
                    self.state[self.params.capacity + i + rate_start_index] += element;
                }
                self.mode = DuplexSpongeMode::Absorbing {
                    next_absorb_index: rate_start_index + remaining_elements.len(),
                };
                return;
            }
            let num_elements_absorbed = self.params.rate - rate_start_index;
            for (i, element) in remaining_elements
                .iter()
                .enumerate()
                .take(num_elements_absorbed)
            {
                self.state[self.params.capacity + i + rate_start_index] += element;
            }
            self.permute();
            remaining_elements = &remaining_elements[num_elements_absorbed..];
            rate_start_index = 0;
        }
    }

    fn squeeze_internal(&mut self, mut rate_start_index: usize, output: &mut [F]) {
        let mut output_remaining = output;
        loop {
            if rate_start_index + output_remaining.len() <= self.params.rate {
                output_remaining.clone_from_slice(
                    &self.state[self.params.capacity + rate_start_index
                        ..(self.params.capacity + output_remaining.len() + rate_start_index)],
                );
                self.mode = DuplexSpongeMode::Squeezing {
                    next_squeeze_index: rate_start_index + output_remaining.len(),
                };
                return;
            }
            let num_elements_squeezed = self.params.rate - rate_start_index;
            output_remaining[..num_elements_squeezed].clone_from_slice(
                &self.state[self.params.capacity + rate_start_index
                    ..(self.params.capacity + num_elements_squeezed + rate_start_index)],
            );
            output_remaining = &mut output_remaining[num_elements_squeezed..];
            if !output_remaining.is_empty() {
                self.permute();
            }
            rate_start_index = 0;
        }
    }
}

/// The in-circuit variable of [`Poseidon2Sponge`].
#[derive(Clone)]
pub struct Poseidon2SpongeVar<F: PrimeField> {
    params: Arc<Poseidon2Params<F>>,
    state: Vec<FpVar<F>>,
    mode: DuplexSpongeMode,
}

impl<F: PrimeField> Poseidon2SpongeVar<F> {
    fn permute(&mut self) -> Result<(), SynthesisError> {
        self.state = Poseidon2Gadget::permute(&self.params, &self.state)?;
        Ok(())
    }

    fn absorb_internal(
        &mut self,
        mut rate_start_index: usize,
        elements: &[FpVar<F>],
    ) -> Result<(), SynthesisError> {
        let mut remaining_elements = elements;
        loop {
            if rate_start_index + remaining_elements.len() <= self.params.rate {
                for (i, element) in remaining_elements.iter().enumerate() {
                    self.state[self.params.capacity + i + rate_start_index] += element;
                }
                self.mode = DuplexSpongeMode::Absorbing {
                    next_absorb_index: rate_start_index + remaining_elements.len(),
                };
                return Ok(());
            }
            let num_elements_absorbed = self.params.rate - rate_start_index;
            for (i, element) in remaining_elements
                .iter()
                .enumerate()
                .take(num_elements_absorbed)
            {
                self.state[self.params.capacity + i + rate_start_index] += element;
            }
            self.permute()?;
            remaining_elements = &remaining_elements[num_elements_absorbed..];
            rate_start_index = 0;
        }
    }

    fn squeeze_internal(
        &mut self,
        mut rate_start_index: usize,
        output: &mut [FpVar<F>],
    ) -> Result<(), SynthesisError> {
        let mut remaining_output = output;
        loop {
            if rate_start_index + remaining_output.len() <= self.params.rate {
                remaining_output.clone_from_slice(
                    &self.state[self.params.capacity + rate_start_index
                        ..(self.params.capacity + remaining_output.len() + rate_start_index)],
                );
                self.mode = DuplexSpongeMode::Squeezing {
                    next_squeeze_index: rate_start_index + remaining_output.len(),
                };
                return Ok(());
            }
            let num_elements_squeezed = self.params.rate - rate_start_index;
            remaining_output[..num_elements_squeezed].clone_from_slice(
                &self.state[self.params.capacity + rate_start_index
                    ..(self.params.capacity + num_elements_squeezed + rate_start_index)],
            );
            remaining_output = &mut remaining_output[num_elements_squeezed..];
            if !remaining_output.is_empty() {
                self.permute()?;
            }
            rate_start_index = 0;
        }
    }
}

impl<F: PrimeField> Transcript<F> for Poseidon2Sponge<F> {
    type Config = Arc<Poseidon2Params<F>>;
    type Gadget = Poseidon2SpongeVar<F>;

    fn new(parameters: Arc<Poseidon2Params<F>>) -> Self {
        let state = vec![F::zero(); parameters.rate + parameters.capacity];
        let mode = DuplexSpongeMode::Absorbing {
            next_absorb_index: 0,
        };

        Self {
            params: parameters.clone(),
            state,
            mode,
        }
    }

    fn add_field_elements(&mut self, elems: &[F]) -> &mut Self {
        if elems.is_empty() {
            return self;
        }

        match self.mode {
            DuplexSpongeMode::Absorbing { next_absorb_index } => {
                let mut absorb_index = next_absorb_index;
                if absorb_index == self.params.rate {
                    self.permute();
                    absorb_index = 0;
                }
                self.absorb_internal(absorb_index, elems);
            }
            DuplexSpongeMode::Squeezing {
                next_squeeze_index: _,
            } => {
                self.absorb_internal(0, elems);
            }
        };
        self
    }

    fn get_field_elements(&mut self, num_elements: usize) -> Vec<F> {
        let mut squeezed_elems = vec![F::zero(); num_elements];
        match self.mode {
            DuplexSpongeMode::Absorbing {
                next_absorb_index: _,
            } => {
                self.permute();
                self.squeeze_internal(0, &mut squeezed_elems);
            }
            DuplexSpongeMode::Squeezing { next_squeeze_index } => {
                let mut squeeze_index = next_squeeze_index;
                if squeeze_index == self.params.rate {
                    self.permute();
                    squeeze_index = 0;
                }
                self.squeeze_internal(squeeze_index, &mut squeezed_elems);
            }
        };

        squeezed_elems
    }
}

impl<F: PrimeField> TranscriptGadget<F> for Poseidon2SpongeVar<F> {
    type Config = Arc<Poseidon2Params<F>>;
    type Widget = Poseidon2Sponge<F>;

    fn new(parameters: Arc<Poseidon2Params<F>>) -> Self
    where
        Self: Sized,
    {
        let zero = FpVar::<F>::zero();
        let state = vec![zero; parameters.rate + parameters.capacity];
        let mode = DuplexSpongeMode::Absorbing {
            next_absorb_index: 0,
        };

        Self {
            params: parameters.clone(),
            state,
            mode,
        }
    }

    fn add<A: AbsorbableVar<F>>(&mut self, input: &A) -> Result<&mut Self, SynthesisError> {
        let input = {
            let mut result = Vec::new();
            input.absorb_into(&mut result)?;
            result
        };

        if input.is_empty() {
            return Ok(self);
        }

        match self.mode {
            DuplexSpongeMode::Absorbing { next_absorb_index } => {
                let mut absorb_index = next_absorb_index;
                if absorb_index == self.params.rate {
                    self.permute()?;
                    absorb_index = 0;
                }
                self.absorb_internal(absorb_index, input.as_slice())?;
            }
            DuplexSpongeMode::Squeezing {
                next_squeeze_index: _,
            } => {
                self.absorb_internal(0, input.as_slice())?;
            }
        };

        Ok(self)
    }

    fn get_field_elements(&mut self, num_elements: usize) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let zero = FpVar::zero();
        let mut squeezed_elems = vec![zero; num_elements];
        match self.mode {
            DuplexSpongeMode::Absorbing {
                next_absorb_index: _,
            } => {
                self.permute()?;
                self.squeeze_internal(0, &mut squeezed_elems)?;
            }
            DuplexSpongeMode::Squeezing { next_squeeze_index } => {
                let mut squeeze_index = next_squeeze_index;
                if squeeze_index == self.params.rate {
                    self.permute()?;
                    squeeze_index = 0;
                }
                self.squeeze_internal(squeeze_index, &mut squeezed_elems)?;
            }
        };

        Ok(squeezed_elems)
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fq, Fr, G1Projective as G1, g1::Config};
    use ark_ff::UniformRand;
    use ark_r1cs_std::{
        GR1CSVar, alloc::AllocVar, fields::fp::FpVar,
        groups::curves::short_weierstrass::ProjectiveVar,
    };
    use ark_relations::gr1cs::ConstraintSystem;
    use ark_std::{error::Error, rand::thread_rng};
    #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
    use wasm_bindgen_test::wasm_bindgen_test as test;

    use super::*;
    use crate::algebra::group::emulated::EmulatedAffineVar;

    #[test]
    fn test_challenge_field_element() -> Result<(), Box<dyn Error>> {
        let config = Arc::new(Poseidon2Params::<Fr>::new(3, 5, 8, 56));
        let mut tr = Poseidon2Sponge::<Fr>::new(config.clone());
        tr.add(&Fr::from(42_u32));
        let c = tr.challenge_field_element();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut tr_var = Poseidon2SpongeVar::<Fr>::new(config);
        let v = FpVar::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(42_u32)))?;
        tr_var.add(&v)?;
        let c_var = tr_var.challenge_field_element()?;

        assert_eq!(c, c_var.value()?);
        Ok(())
    }

    #[test]
    fn test_challenge_bits() -> Result<(), Box<dyn Error>> {
        let nbits = 128;

        let config = Arc::new(Poseidon2Params::<Fq>::new(3, 5, 8, 56));
        let mut tr = Poseidon2Sponge::<Fq>::new(config.clone());
        tr.add(&Fq::from(42_u32));
        let c = tr.challenge_bits(nbits);

        let cs = ConstraintSystem::<Fq>::new_ref();
        let mut tr_var = Poseidon2SpongeVar::<Fq>::new(config);
        let v = FpVar::<Fq>::new_witness(cs.clone(), || Ok(Fq::from(42_u32)))?;
        tr_var.add(&v)?;
        let c_var = tr_var.challenge_bits(nbits)?;

        assert_eq!(c, c_var.value()?);
        Ok(())
    }

    #[test]
    fn test_absorb_canonical_point() -> Result<(), Box<dyn Error>> {
        let config = Arc::new(Poseidon2Params::<Fq>::new(3, 5, 8, 56));
        let mut tr = Poseidon2Sponge::<Fq>::new(config.clone());
        let rng = &mut thread_rng();

        let p = G1::rand(rng);
        tr.add(&p);
        let c = tr.challenge_field_element();

        let cs = ConstraintSystem::<Fq>::new_ref();
        let mut tr_var = Poseidon2SpongeVar::<Fq>::new(config);
        let p_var = ProjectiveVar::<Config, FpVar<Fq>>::new_witness(cs, || Ok(p))?;
        tr_var.add(&p_var)?;
        let c_var = tr_var.challenge_field_element()?;

        assert_eq!(c, c_var.value()?);
        Ok(())
    }

    #[test]
    fn test_absorb_emulated_point() -> Result<(), Box<dyn Error>> {
        let config = Arc::new(Poseidon2Params::<Fr>::new(3, 5, 8, 56));
        let mut tr = Poseidon2Sponge::<Fr>::new(config.clone());
        let rng = &mut thread_rng();

        let p = G1::rand(rng);
        tr.add(&p);
        let c = tr.challenge_field_element();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut tr_var = Poseidon2SpongeVar::<Fr>::new(config);
        let p_var = EmulatedAffineVar::new_witness(cs, || Ok(p))?;
        tr_var.add(&p_var)?;
        let c_var = tr_var.challenge_field_element()?;

        assert_eq!(c, c_var.value()?);
        Ok(())
    }
}
