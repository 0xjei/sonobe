//! In-circuit SHA-256 block compression gadget, matching Noir's
//! `Sha256Compression` black box (a single 64-round compression with **no**
//! padding or length encoding).
//!
//! Adapted from <https://github.com/dmpierre/arkworks_backend>.

use ark_ff::PrimeField;
use ark_r1cs_std::uint32::UInt32;
use ark_relations::gr1cs::SynthesisError;

/// SHA-256 round constants (first 32 bits of the fractional parts of the cube
/// roots of the first 64 primes).
const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Applies the raw SHA-256 block compression function to `state` (the 8-word
/// previous hash value) over the 16-word `message` block, returning the 8-word
/// compressed output.
///
/// The round logic mirrors arkworks' `Sha256Gadget::update_state` (FIPS 180-4
/// §6.2.2), but operates directly on the caller-provided `u32` words instead of
/// packing bytes, and takes the previous state as an explicit input.
pub(super) fn compress<F: PrimeField>(
    state: &[UInt32<F>],
    message: &[UInt32<F>],
) -> Result<Vec<UInt32<F>>, SynthesisError> {
    debug_assert_eq!(state.len(), 8);
    debug_assert_eq!(message.len(), 16);

    // Message schedule: w[0..16] = message, then extend to 64 words.
    let mut w: Vec<UInt32<F>> = message.to_vec();
    for i in 16..64 {
        let s0 = {
            let x1 = w[i - 15].rotate_right(7);
            let x2 = w[i - 15].rotate_right(18);
            let x3 = &w[i - 15] >> 3u8;
            x1 ^ &x2 ^ &x3
        };
        let s1 = {
            let x1 = w[i - 2].rotate_right(17);
            let x2 = w[i - 2].rotate_right(19);
            let x3 = &w[i - 2] >> 10u8;
            x1 ^ &x2 ^ &x3
        };
        w.push(UInt32::wrapping_add_many(&[
            w[i - 16].clone(),
            s0,
            w[i - 7].clone(),
            s1,
        ])?);
    }

    // Working variables initialized from the previous state.
    let mut h = state.to_vec();
    for (i, k_i) in SHA256_K.iter().enumerate() {
        let ch = {
            let x1 = &h[4] & &h[5];
            let x2 = (!&h[4]) & &h[6];
            x1 ^ &x2
        };
        let maj = {
            let x1 = &h[0] & &h[1];
            let x2 = &h[0] & &h[2];
            let x3 = &h[1] & &h[2];
            x1 ^ &x2 ^ &x3
        };
        let s0 = {
            let x1 = h[0].rotate_right(2);
            let x2 = h[0].rotate_right(13);
            let x3 = h[0].rotate_right(22);
            x1 ^ &x2 ^ &x3
        };
        let s1 = {
            let x1 = h[4].rotate_right(6);
            let x2 = h[4].rotate_right(11);
            let x3 = h[4].rotate_right(25);
            x1 ^ &x2 ^ &x3
        };
        let t0 = UInt32::wrapping_add_many(&[
            h[7].clone(),
            s1,
            ch,
            UInt32::constant(*k_i),
            w[i].clone(),
        ])?;
        let t1 = s0.wrapping_add(&maj);

        h[7] = h[6].clone();
        h[6] = h[5].clone();
        h[5] = h[4].clone();
        h[4] = h[3].wrapping_add(&t0);
        h[3] = h[2].clone();
        h[2] = h[1].clone();
        h[1] = h[0].clone();
        h[0] = t0.wrapping_add(&t1);
    }

    // Add the compressed chunk to the previous state.
    Ok(state
        .iter()
        .zip(h.iter())
        .map(|(s, hi)| s.wrapping_add(hi))
        .collect())
}
