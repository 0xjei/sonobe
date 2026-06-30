//! In-circuit Keccak-f[1600] permutation gadget.
//!
//! Implements the raw Keccak-f[1600] permutation (24 rounds of θ, ρ, π, χ, ι)
//! over 25 lanes of 64 bits, matching Noir's `Keccakf1600` black box. The
//! reference witness is the standard `keccakf1600` used by ACVM. This gadget
//! reproduces it exactly.

use ark_ff::PrimeField;
use ark_r1cs_std::uint64::UInt64;
use ark_relations::gr1cs::SynthesisError;

/// Rotation offsets `ρ[x][y]` indexed as `RHO[5 * y + x]` (i.e. lane `A[x, y]`
/// stored at `state[x + 5 * y]`).
const RHO: [u32; 25] = [
    0, 1, 62, 28, 27, // y = 0
    36, 44, 6, 55, 20, // y = 1
    3, 10, 43, 25, 39, // y = 2
    41, 45, 15, 21, 8, // y = 3
    18, 2, 61, 56, 14, // y = 4
];

/// Round constants for the ι step.
const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// Applies the Keccak-f[1600] permutation to `state` (25 lanes, row-major
/// `A[x, y] = state[x + 5 * y]`) and returns the permuted lanes.
pub(super) fn keccak_f1600<F: PrimeField>(
    state: &[UInt64<F>],
) -> Result<Vec<UInt64<F>>, SynthesisError> {
    debug_assert_eq!(state.len(), 25);
    let mut a: Vec<UInt64<F>> = state.to_vec();

    for &rc in &RC {
        // θ: C[x] = A[x,0] ^ A[x,1] ^ ... ^ A[x,4]; D[x] = C[x-1] ^ rotl(C[x+1], 1).
        let c: Vec<UInt64<F>> = (0..5)
            .map(|x| &a[x] ^ &a[x + 5] ^ &a[x + 10] ^ &a[x + 15] ^ &a[x + 20])
            .collect();
        let d: Vec<UInt64<F>> = (0..5)
            .map(|x| &c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1))
            .collect();
        for x in 0..5 {
            for y in 0..5 {
                a[x + 5 * y] = &a[x + 5 * y] ^ &d[x];
            }
        }

        // ρ and π: B[y, 2x + 3y] = rotl(A[x, y], ρ[x, y]).
        let mut b = vec![UInt64::constant(0); 25];
        for x in 0..5 {
            for y in 0..5 {
                let rotated = a[x + 5 * y].rotate_left(RHO[x + 5 * y] as usize);
                b[y + 5 * ((2 * x + 3 * y) % 5)] = rotated;
            }
        }

        // χ: A[x, y] = B[x, y] ^ ((¬B[x+1, y]) & B[x+2, y]).
        for y in 0..5 {
            for x in 0..5 {
                let not_next = !&b[(x + 1) % 5 + 5 * y];
                a[x + 5 * y] = &b[x + 5 * y] ^ (&not_next & &b[(x + 2) % 5 + 5 * y]);
            }
        }

        // ι: A[0, 0] ^= RC[round].
        a[0] = &a[0] ^ UInt64::constant(rc);
    }

    Ok(a)
}
