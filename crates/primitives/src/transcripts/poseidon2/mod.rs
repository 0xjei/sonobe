//! Poseidon2 circuit-friendly hash function: parameter generation, plain
//! permutation/hash, in-circuit gadgets, and sponges.
//!
//! Poseidon2 is a faster Poseidon variant with the same `x^d` S-box and round
//! numbers but cheaper linear layers. Versus Poseidon it (the [paper], Section
//! 6) applies an external layer `M_E` before the rounds, uses distinct layers
//! `M_E` (full rounds) and `M_I` (partial rounds) for `t >= 4`, and adds a
//! single round constant to the first state word in each internal round.
//!
//! [paper]: https://eprint.iacr.org/2023/323.pdf
//! [`HorizenLabs/poseidon2`]: https://github.com/HorizenLabs/poseidon2

use ark_ff::PrimeField;
use ark_r1cs_std::fields::{FieldVar, fp::FpVar};
use ark_relations::gr1cs::SynthesisError;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use itertools::Itertools;

mod params;
pub mod sponge;

/// Full parameterization of the Poseidon2 permutation over a prime field.
///
/// The linear layers are fixed by `t`, so they are not stored: `M_E` is
/// `circ(2, 1, ..., 1)` for `t in {2, 3}`, `M4` for `t = 4`, and
/// `circ(2 * M4, M4, ..., M4)` for `t = 4k >= 8`; `M_I` is a small fixed MDS
/// matrix for `t in {2, 3}` and the Neptune matrix `1 + diag(mu_i - 1)` for
/// `t >= 4` (stored as `mat_internal_diag_m_1`).
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct Poseidon2Params<F: PrimeField> {
    t: usize,
    d: usize,
    rounds_f: usize,
    rounds_p: usize,
    /// Constants for all `rounds_f + rounds_p` rounds (each length `t`), indexed
    /// by absolute round number, in the reference (`zkhash`/Barretenberg/Noir)
    /// layout. Internal rounds use only index `0` of their entry.
    round_constants: Vec<Vec<F>>,
    /// Internal-matrix diagonal minus identity (`mu_i - 1`); non-empty iff
    /// `t >= 4`.
    mat_internal_diag_m_1: Vec<F>,
    rate: usize,
    capacity: usize,
}

impl<F: PrimeField> Poseidon2Params<F> {
    /// Constructs parameters with state width `t`, S-box degree `d`, and
    /// `rounds_f`/`rounds_p` external/internal rounds, deriving the round
    /// constants and (for `t >= 4`) the internal-matrix diagonal from the
    /// params generator (which mirrors `HorizenLabs/poseidon2`).
    ///
    /// `t` must be `2`, `3`, or a multiple of `4`; `d` must be `3` or `5`;
    /// `rounds_f` must be positive and even.
    pub fn new(t: usize, d: usize, rounds_f: usize, rounds_p: usize) -> Self {
        Self::validate(t, d, rounds_f, rounds_p);

        let (round_constants, mat_internal_diag_mu) = params::generate::<F>(t, rounds_f, rounds_p);
        // The permutation uses `mu_i - 1` (the diagonal of `M_I - I`).
        let mat_internal_diag_m_1 = mat_internal_diag_mu
            .into_iter()
            .map(|mu| mu - F::one())
            .collect();

        Poseidon2Params {
            t,
            d,
            rounds_f,
            rounds_p,
            round_constants,
            mat_internal_diag_m_1,
            rate: t - 1,
            capacity: 1,
        }
    }

    /// Constructs parameters from explicit constants, so a known instance (e.g.
    /// the BN254 `t = 4` instance) can be reproduced verbatim.
    ///
    /// `mat_internal_diag_m_1` is `mu_i - 1` (length `t`, used iff `t >= 4`);
    /// `round_constants` is the flat per-round array (length `rounds_f +
    /// rounds_p`, each length `t`).
    pub fn new_with_params(
        t: usize,
        d: usize,
        rounds_f: usize,
        rounds_p: usize,
        mat_internal_diag_m_1: Vec<F>,
        round_constants: Vec<Vec<F>>,
    ) -> Self {
        Self::validate(t, d, rounds_f, rounds_p);
        assert_eq!(round_constants.len(), rounds_f + rounds_p);
        assert!(round_constants.iter().all(|rc| rc.len() == t));
        if t >= 4 {
            assert_eq!(mat_internal_diag_m_1.len(), t);
        }

        Poseidon2Params {
            t,
            d,
            rounds_f,
            rounds_p,
            round_constants,
            mat_internal_diag_m_1,
            rate: t - 1,
            capacity: 1,
        }
    }

    fn validate(t: usize, d: usize, rounds_f: usize, rounds_p: usize) {
        // `t % 4 == 0` written as `t & 3 == 0` to dodge clippy's
        // `is_multiple_of` lint.
        assert!(t == 2 || t == 3 || t & 3 == 0);
        assert!(d == 3 || d == 5);
        // `rounds_f` is split into two halves around the internal rounds.
        assert!(rounds_f >= 2 && rounds_f & 1 == 0);
        assert!(rounds_p >= 1);
    }

    /// The state width `t`.
    pub fn t(&self) -> usize {
        self.t
    }
}

/// The plain (out-of-circuit) Poseidon2 permutation and hash.
pub struct Poseidon2;

impl Poseidon2 {
    fn sbox<F: PrimeField>(params: &Poseidon2Params<F>, x: &mut F) {
        let mut res = x.square();
        if params.d == 5 {
            res.square_in_place();
        }
        x.mul_assign(&res);
    }

    /// Applies the `4 x 4` MDS matrix `M4 = [[5,7,1,3],[4,6,1,1],[1,3,5,7],
    /// [1,1,4,6]]` (the paper, Section 5.1) to each 4-element chunk in place,
    /// using the efficient `8` additions + `4` doublings sequence from the paper
    /// (App. B).
    fn matmul_m4<F: PrimeField>(input: &mut [F]) {
        for chunk in input.chunks_mut(4) {
            let mut t_0 = chunk[0];
            t_0.add_assign(&chunk[1]);
            let mut t_1 = chunk[2];
            t_1.add_assign(&chunk[3]);
            let mut t_2 = chunk[1];
            t_2.double_in_place();
            t_2.add_assign(&t_1);
            let mut t_3 = chunk[3];
            t_3.double_in_place();
            t_3.add_assign(&t_0);
            let mut t_4 = t_1;
            t_4.double_in_place();
            t_4.double_in_place();
            t_4.add_assign(&t_3);
            let mut t_5 = t_0;
            t_5.double_in_place();
            t_5.double_in_place();
            t_5.add_assign(&t_2);
            chunk[0] = t_3 + t_5;
            chunk[1] = t_5;
            chunk[2] = t_2 + t_4;
            chunk[3] = t_4;
        }
    }

    /// Applies the external linear layer `M_E` in place. Following the reference
    /// implementation: `circ(2, 1)` for `t = 2`, `circ(2, 1, 1)` for `t = 3` (in
    /// both cases `x_i += sum`), `M4` for `t = 4`, and `circ(2 * M4, M4, ...,
    /// M4)` for `t = 4k >= 8`.
    fn external_matmul<F: PrimeField>(params: &Poseidon2Params<F>, input: &mut [F]) {
        let t = params.t;
        if t == 2 || t == 3 {
            // circ(2, 1, ..., 1): every output is its input plus the state sum.
            let mut sum = input[0];
            input.iter().skip(1).for_each(|el| sum.add_assign(el));
            input.iter_mut().for_each(|el| el.add_assign(&sum));
            return;
        }

        Poseidon2::matmul_m4(input);

        if t > 4 {
            // Add together the corresponding words of each 4-element block, then
            // fold the sums back in (the circulant `circ(2 * M4, M4, ...)`).
            let t4 = t / 4;
            let mut stored = [F::zero(); 4];
            for (l, s) in stored.iter_mut().enumerate() {
                *s = input[l];
                for j in 1..t4 {
                    s.add_assign(&input[4 * j + l]);
                }
            }
            for (i, el) in input.iter_mut().enumerate() {
                el.add_assign(&stored[i % 4]);
            }
        }
    }

    /// Applies the internal linear layer `M_I` in place. Following the reference
    /// implementation: the fixed MDS matrix `[[2,1],[1,3]]` for `t = 2` and
    /// `[[2,1,1],[1,2,1],[1,1,3]]` for `t = 3`; for `t >= 4` the Neptune-style
    /// matrix `M_I * x = sum(x) + diag(mu_i - 1) * x`.
    fn internal_matmul<F: PrimeField>(params: &Poseidon2Params<F>, input: &mut [F]) {
        let t = params.t;
        if t == 2 || t == 3 {
            // The small matrices differ from the external ones only in the last
            // diagonal entry (`3` instead of `2`). Doubling the last word before
            // adding `sum` to every word gives `2*x_last + sum` there and
            // `x_i + sum` elsewhere.
            let mut sum = input[0];
            input.iter().skip(1).for_each(|el| sum.add_assign(el));
            input[t - 1].double_in_place();
            input.iter_mut().for_each(|el| el.add_assign(&sum));
            return;
        }

        let mut sum = input[0];
        input.iter().skip(1).for_each(|el| sum.add_assign(el));
        for (el, diag) in input.iter_mut().zip_eq(&params.mat_internal_diag_m_1) {
            // y_i = (mu_i - 1) * x_i + sum.
            el.mul_assign(diag);
            el.add_assign(&sum);
        }
    }

    /// Applies the Poseidon2 permutation to `input` in place.
    pub fn permute<F: PrimeField>(params: &Poseidon2Params<F>, input: &mut [F]) {
        let rounds_f_half = params.rounds_f / 2;
        let p_end = rounds_f_half + params.rounds_p;

        // Initial external linear layer.
        Poseidon2::external_matmul(params, input);

        // First half of the external (full) rounds.
        for r in 0..rounds_f_half {
            for (el, rc) in input.iter_mut().zip_eq(&params.round_constants[r]) {
                el.add_assign(rc);
                Poseidon2::sbox(params, el);
            }
            Poseidon2::external_matmul(params, input);
        }

        // Internal (partial) rounds: a single round constant and a single S-box,
        // both on the first word, followed by the internal linear layer.
        for r in rounds_f_half..p_end {
            input[0].add_assign(&params.round_constants[r][0]);
            Poseidon2::sbox(params, &mut input[0]);
            Poseidon2::internal_matmul(params, input);
        }

        // Second half of the external (full) rounds.
        for r in p_end..params.rounds_f + params.rounds_p {
            for (el, rc) in input.iter_mut().zip_eq(&params.round_constants[r]) {
                el.add_assign(rc);
                Poseidon2::sbox(params, el);
            }
            Poseidon2::external_matmul(params, input);
        }
    }

    /// Sponge-based hash of `message` to a single field element.
    pub fn hash<F: PrimeField>(params: &Poseidon2Params<F>, message: &[F]) -> F {
        let mut state = vec![F::zero(); params.t];
        for chunk in message.chunks(params.rate) {
            for (s, c) in state.iter_mut().zip(chunk) {
                *s += c;
            }
            Poseidon2::permute(params, &mut state);
        }
        state[0]
    }
}

/// In-circuit Poseidon2 permutation and hash gadgets.
pub struct Poseidon2Gadget;

impl Poseidon2Gadget {
    fn sbox<F: PrimeField>(
        params: &Poseidon2Params<F>,
        x: &FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut sq = x.square()?;
        if params.d == 5 {
            sq = sq.square()?;
        }
        Ok(sq * x)
    }

    fn matmul_m4<F: PrimeField>(input: &mut [FpVar<F>]) {
        for chunk in input.chunks_mut(4) {
            let t_0 = &chunk[0] + &chunk[1];
            let t_1 = &chunk[2] + &chunk[3];
            let t_2 = chunk[1].double().unwrap() + &t_1;
            let t_3 = chunk[3].double().unwrap() + &t_0;
            let t_4 = t_1.double().unwrap().double().unwrap() + &t_3;
            let t_5 = t_0.double().unwrap().double().unwrap() + &t_2;
            chunk[0] = &t_3 + &t_5;
            chunk[1] = t_5;
            chunk[2] = &t_2 + &t_4;
            chunk[3] = t_4;
        }
    }

    fn external_matmul<F: PrimeField>(params: &Poseidon2Params<F>, input: &mut [FpVar<F>]) {
        let t = params.t;
        if t == 2 || t == 3 {
            // circ(2, 1, ..., 1): every output is its input plus the state sum.
            let mut sum = input[0].clone();
            input.iter().skip(1).for_each(|el| sum += el);
            input.iter_mut().for_each(|el| *el += &sum);
            return;
        }

        Poseidon2Gadget::matmul_m4(input);

        if t > 4 {
            let t4 = t / 4;
            let mut stored = [FpVar::zero(), FpVar::zero(), FpVar::zero(), FpVar::zero()];
            for (l, s) in stored.iter_mut().enumerate() {
                *s = input[l].clone();
                for j in 1..t4 {
                    *s += &input[4 * j + l];
                }
            }
            for (i, el) in input.iter_mut().enumerate() {
                *el += &stored[i % 4];
            }
        }
    }

    fn internal_matmul<F: PrimeField>(params: &Poseidon2Params<F>, input: &mut [FpVar<F>]) {
        let t = params.t;
        if t == 2 || t == 3 {
            // Small MDS matrix: double the last word, then add `sum` to all
            // words (giving `2*x_last + sum` on the last diagonal, `x_i + sum`
            // elsewhere).
            let mut sum = input[0].clone();
            input.iter().skip(1).for_each(|el| sum += el);
            input[t - 1] = input[t - 1].double().unwrap();
            input.iter_mut().for_each(|el| *el += &sum);
            return;
        }

        let mut sum = input[0].clone();
        input.iter().skip(1).for_each(|el| sum += el);
        for (el, diag) in input.iter_mut().zip_eq(&params.mat_internal_diag_m_1) {
            *el = &*el * *diag + &sum;
        }
    }

    /// Applies the Poseidon2 permutation to the state variables `state`.
    pub fn permute<F: PrimeField>(
        params: &Poseidon2Params<F>,
        state: &[FpVar<F>],
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let rounds_f_half = params.rounds_f / 2;
        let p_end = rounds_f_half + params.rounds_p;
        let mut input = state.to_owned();

        // Initial external linear layer.
        Poseidon2Gadget::external_matmul(params, &mut input);

        // First half of the external (full) rounds.
        for r in 0..rounds_f_half {
            for (el, rc) in input.iter_mut().zip_eq(&params.round_constants[r]) {
                *el = Poseidon2Gadget::sbox(params, &(&*el + *rc))?;
            }
            Poseidon2Gadget::external_matmul(params, &mut input);
        }

        // Internal (partial) rounds.
        for r in rounds_f_half..p_end {
            input[0] = Poseidon2Gadget::sbox(params, &(&input[0] + params.round_constants[r][0]))?;
            Poseidon2Gadget::internal_matmul(params, &mut input);
        }

        // Second half of the external (full) rounds.
        for r in p_end..params.rounds_f + params.rounds_p {
            for (el, rc) in input.iter_mut().zip_eq(&params.round_constants[r]) {
                *el = Poseidon2Gadget::sbox(params, &(&*el + *rc))?;
            }
            Poseidon2Gadget::external_matmul(params, &mut input);
        }

        Ok(input)
    }

    /// Sponge-based hash of `message` to a single field-element variable.
    pub fn hash<F: PrimeField>(
        params: &Poseidon2Params<F>,
        message: &[FpVar<F>],
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut state = vec![FpVar::zero(); params.t];
        for chunk in message.chunks(params.rate) {
            for (s, c) in state.iter_mut().zip(chunk) {
                *s += c;
            }
            state = Poseidon2Gadget::permute(params, &state)?;
        }
        Ok(state[0].clone())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;
    use ark_ff::{Field, UniformRand};
    use ark_r1cs_std::{GR1CSVar, alloc::AllocVar};
    use ark_relations::gr1cs::ConstraintSystem;
    use ark_std::{error::Error, rand::thread_rng};
    #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
    use wasm_bindgen_test::wasm_bindgen_test as test;

    use super::*;

    fn fr_from_hex(hex: &str) -> Fr {
        use num_bigint::BigUint;
        Fr::from(BigUint::parse_bytes(hex.as_bytes(), 16).unwrap())
    }

    /// Known-answer test proving the generated BN254 `t = 4` instance (i.e.
    /// `new(4, 5, 8, 56)`) is byte-compatible with Barretenberg/Noir: permuting
    /// the all-zero input must reproduce the `smoke_test` output vector from
    /// Noir's `bn254_blackbox_solver`. Since the parameters here are derived
    /// purely from the [`params`] generator (Grain LFSR + minimal-polynomial
    /// diagonal) and the expected output is taken independently from Noir, this
    /// end-to-end checks the entire generation logic.
    #[test]
    fn test_noir_kat() {
        let params = Poseidon2Params::<Fr>::new(4, 5, 8, 56);
        let mut state = [Fr::from(0u64); 4];
        Poseidon2::permute(&params, &mut state);

        let expected = [
            "18DFB8DC9B82229CFF974EFEFC8DF78B1CE96D9D844236B496785C698BC6732E",
            "095C230D1D37A246E8D2D5A63B165FE0FADE040D442F61E25F0590E5FB76F839",
            "0BB9545846E1AFA4FA3C97414A60A20FC4949F537A68CCECA34C5CE71E28AA59",
            "18A4F34C9C6F99335FF7638B82AEED9018026618358873C982BBDDE265B2ED6D",
        ]
        .map(fr_from_hex);
        assert_eq!(state, expected);
    }

    /// The in-circuit gadget must match the plain permutation on the Noir BN254
    /// instance, for a nontrivial input.
    #[test]
    fn test_noir_gadget() -> Result<(), Box<dyn Error>> {
        let params = Poseidon2Params::<Fr>::new(4, 5, 8, 56);
        let input = [
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(4u64),
        ];

        let mut expected = input;
        Poseidon2::permute(&params, &mut expected);

        let cs = ConstraintSystem::new_ref();
        let input_var = Vec::new_witness(cs.clone(), || Ok(input.to_vec()))?;
        let output_var = Poseidon2Gadget::permute(&params, &input_var)?;
        let output: Vec<Fr> = output_var.iter().map(|v| v.value().unwrap()).collect();
        assert_eq!(output, expected.to_vec());
        assert!(cs.is_satisfied()?);
        Ok(())
    }

    /// Checks that the plain hash and the in-circuit gadget agree, and that the
    /// resulting constraint system is satisfied, for the given parameters.
    fn check_hash_consistency(params: &Poseidon2Params<Fr>) -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();
        let t = params.t;
        let x: Vec<Fr> = (0..t).map(|_| Fr::rand(rng)).collect();

        let y = Poseidon2::hash(params, &x);

        let cs = ConstraintSystem::new_ref();
        let x_var = Vec::new_witness(cs.clone(), || Ok(x.clone()))?;
        let y_var = Poseidon2Gadget::hash(params, &x_var)?;
        assert_eq!(y, y_var.value()?);
        assert!(cs.is_satisfied()?);

        Ok(())
    }

    /// The plain hash and the in-circuit gadget must agree across each distinct
    /// linear-layer path: `t = 2`/`3` (small fixed matrices), `t = 4` (`M4`
    /// only) and `t = 8` (`M4` + circulant fold).
    #[test]
    fn test_hash_gadget_consistency() -> Result<(), Box<dyn Error>> {
        for &(t, d, rf, rp) in &[(2, 5, 8, 56), (3, 5, 8, 56), (4, 5, 8, 56), (8, 5, 8, 57)] {
            check_hash_consistency(&Poseidon2Params::new(t, d, rf, rp))?;
        }
        Ok(())
    }

    /// A deliberately naive, textbook reference permutation used to cross-check
    /// the optimized [`Poseidon2::permute`]. It builds the external and internal
    /// matrices densely and applies the round structure literally, following the
    /// paper's Section 6 specification.
    fn reference_permute(params: &Poseidon2Params<Fr>, input: &[Fr]) -> Vec<Fr> {
        let t = params.t;

        // Dense external matrix M_E.
        let m_e = if t == 2 || t == 3 {
            // circ(2, 1, ..., 1): 2 on the diagonal, 1 elsewhere.
            (0..t)
                .map(|i| {
                    (0..t)
                        .map(|j| {
                            if i == j {
                                Fr::from(2u64)
                            } else {
                                Fr::from(1u64)
                            }
                        })
                        .collect()
                })
                .collect()
        } else {
            const M4: [[u64; 4]; 4] = [[5, 7, 1, 3], [4, 6, 1, 1], [1, 3, 5, 7], [1, 1, 4, 6]];
            let mut m = vec![vec![Fr::from(0u64); t]; t];
            for (r, m_r) in m.iter_mut().enumerate() {
                for (c, m_rc) in m_r.iter_mut().enumerate() {
                    let mut v = Fr::from(M4[r % 4][c % 4]);
                    // circ(2 * M4, M4, ..., M4): the diagonal blocks are doubled.
                    if t > 4 && r / 4 == c / 4 {
                        v += Fr::from(M4[r % 4][c % 4]);
                    }
                    *m_rc = v;
                }
            }
            m
        };

        // Dense internal matrix M_I.
        let m_i = if t == 2 || t == 3 {
            // Small fixed MDS matrix: all-ones + diag(1, ..., 1, 2), i.e. 2 on
            // the diagonal except 3 in the last position.
            (0..t)
                .map(|i| {
                    (0..t)
                        .map(|j| {
                            if i != j {
                                Fr::from(1u64)
                            } else if i == t - 1 {
                                Fr::from(3u64)
                            } else {
                                Fr::from(2u64)
                            }
                        })
                        .collect()
                })
                .collect()
        } else {
            let mut m = vec![vec![Fr::from(1u64); t]; t];
            for (i, m_ii) in m.iter_mut().enumerate() {
                // M_I = 1 (all-ones) + diag(mu_i - 1).
                m_ii[i] += params.mat_internal_diag_m_1[i];
            }
            m
        };

        let matmul = |mat: &[Vec<Fr>], x: &[Fr]| -> Vec<Fr> {
            mat.iter()
                .map(|row| row.iter().zip(x).map(|(m, x)| *m * x).sum())
                .collect()
        };
        let pow_d = |x: Fr| -> Fr {
            let mut r = x.square();
            if params.d == 5 {
                r.square_in_place();
            }
            r * x
        };

        let rf_half = params.rounds_f / 2;
        let p_end = rf_half + params.rounds_p;
        let mut state = matmul(&m_e, input);

        for r in 0..rf_half {
            for (s, rc) in state.iter_mut().zip(&params.round_constants[r]) {
                *s = pow_d(*s + rc);
            }
            state = matmul(&m_e, &state);
        }
        for r in rf_half..p_end {
            state[0] = pow_d(state[0] + params.round_constants[r][0]);
            state = matmul(&m_i, &state);
        }
        for r in p_end..params.rounds_f + params.rounds_p {
            for (s, rc) in state.iter_mut().zip(&params.round_constants[r]) {
                *s = pow_d(*s + rc);
            }
            state = matmul(&m_e, &state);
        }
        state
    }

    /// Cross-checks the optimized permutation against the naive reference,
    /// covering each distinct linear-layer path (small `t = 2`/`3`, `M4`-only
    /// `t = 4`, circulant `t = 8`, and `d = 3` at `t = 12`).
    #[test]
    fn test_permute_against_reference() {
        let rng = &mut thread_rng();
        for &(t, d, rf, rp) in &[
            (2, 5, 8, 56),
            (3, 5, 8, 56),
            (4, 5, 8, 56),
            (8, 5, 8, 57),
            (12, 3, 8, 22),
        ] {
            let params = Poseidon2Params::new(t, d, rf, rp);
            for _ in 0..3 {
                let input: Vec<Fr> = (0..params.t).map(|_| Fr::rand(rng)).collect();
                let mut optimized = input.clone();
                Poseidon2::permute(&params, &mut optimized);
                assert_eq!(optimized, reference_permute(&params, &input));
            }
        }
    }
}
