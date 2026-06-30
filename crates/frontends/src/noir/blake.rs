//! In-circuit Blake2s and Blake3 hash gadgets, producing the 32-byte digests
//! that Noir's `Blake2s` / `Blake3` black boxes constrain.
//!
//! - Blake2s reuses arkworks' `evaluate_blake2s` (RFC 7693, unkeyed, 32-byte
//!   output), which matches Noir's `blake2s` exactly.
//! - Blake3 is implemented here directly from the [BLAKE3 reference
//!   implementation]. The input length is fixed at circuit-build time (it is the
//!   number of byte-witnesses in the opcode), so the chunk/tree structure is
//!   fully unrolled. Only the byte *values* are circuit variables.
//!
//! [BLAKE3 reference implementation]: https://github.com/BLAKE3-team/BLAKE3/blob/master/reference_impl/reference_impl.rs

use ark_crypto_primitives::prf::blake2s::constraints::evaluate_blake2s;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    convert::{ToBitsGadget, ToBytesGadget},
    uint8::UInt8,
    uint32::UInt32,
};
use ark_relations::gr1cs::SynthesisError;

/// Computes the Blake2s-256 digest of `input` (a byte array) as 32 bytes.
pub(super) fn blake2s<F: PrimeField>(input: &[UInt8<F>]) -> Result<Vec<UInt8<F>>, SynthesisError> {
    // `evaluate_blake2s` takes little-endian bits and returns the 8 state words;
    // the digest is those words serialized little-endian.
    let mut bits = Vec::with_capacity(input.len() * 8);
    for byte in input {
        bits.extend(byte.to_bits_le()?);
    }
    let words = evaluate_blake2s(&bits)?;
    let mut out = Vec::with_capacity(32);
    for word in words {
        out.extend(word.to_bytes_le()?);
    }
    Ok(out)
}

const OUT_LEN: usize = 32;
const BLOCK_LEN: usize = 64;
const CHUNK_LEN: usize = 1024;

const CHUNK_START: u32 = 1 << 0;
const CHUNK_END: u32 = 1 << 1;
const PARENT: u32 = 1 << 2;
const ROOT: u32 = 1 << 3;

const IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

/// The mixing function G.
#[allow(clippy::too_many_arguments)]
fn g<F: PrimeField>(
    state: &mut [UInt32<F>; 16],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    mx: &UInt32<F>,
    my: &UInt32<F>,
) {
    state[a] =
        UInt32::wrapping_add_many(&[state[a].clone(), state[b].clone(), mx.clone()]).unwrap();
    state[d] = (&state[d] ^ &state[a]).rotate_right(16);
    state[c] = state[c].wrapping_add(&state[d]);
    state[b] = (&state[b] ^ &state[c]).rotate_right(12);
    state[a] =
        UInt32::wrapping_add_many(&[state[a].clone(), state[b].clone(), my.clone()]).unwrap();
    state[d] = (&state[d] ^ &state[a]).rotate_right(8);
    state[c] = state[c].wrapping_add(&state[d]);
    state[b] = (&state[b] ^ &state[c]).rotate_right(7);
}

fn round<F: PrimeField>(state: &mut [UInt32<F>; 16], m: &[UInt32<F>; 16]) {
    // Columns.
    g(state, 0, 4, 8, 12, &m[0], &m[1]);
    g(state, 1, 5, 9, 13, &m[2], &m[3]);
    g(state, 2, 6, 10, 14, &m[4], &m[5]);
    g(state, 3, 7, 11, 15, &m[6], &m[7]);
    // Diagonals.
    g(state, 0, 5, 10, 15, &m[8], &m[9]);
    g(state, 1, 6, 11, 12, &m[10], &m[11]);
    g(state, 2, 7, 8, 13, &m[12], &m[13]);
    g(state, 3, 4, 9, 14, &m[14], &m[15]);
}

fn permute<F: PrimeField>(m: &[UInt32<F>; 16]) -> [UInt32<F>; 16] {
    core::array::from_fn(|i| m[MSG_PERMUTATION[i]].clone())
}

/// The BLAKE3 compression function, returning all 16 output words.
fn compress<F: PrimeField>(
    chaining_value: &[UInt32<F>; 8],
    block_words: &[UInt32<F>; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
) -> [UInt32<F>; 16] {
    let counter_low = counter as u32;
    let counter_high = (counter >> 32) as u32;
    let mut state: [UInt32<F>; 16] = [
        chaining_value[0].clone(),
        chaining_value[1].clone(),
        chaining_value[2].clone(),
        chaining_value[3].clone(),
        chaining_value[4].clone(),
        chaining_value[5].clone(),
        chaining_value[6].clone(),
        chaining_value[7].clone(),
        UInt32::constant(IV[0]),
        UInt32::constant(IV[1]),
        UInt32::constant(IV[2]),
        UInt32::constant(IV[3]),
        UInt32::constant(counter_low),
        UInt32::constant(counter_high),
        UInt32::constant(block_len),
        UInt32::constant(flags),
    ];
    let mut block = block_words.clone();

    round(&mut state, &block);
    for _ in 0..6 {
        block = permute(&block);
        round(&mut state, &block);
    }

    for i in 0..8 {
        state[i] = &state[i] ^ &state[i + 8];
        state[i + 8] = &state[i + 8] ^ &chaining_value[i];
    }
    state
}

fn first_8_words<F: PrimeField>(words: [UInt32<F>; 16]) -> [UInt32<F>; 8] {
    core::array::from_fn(|i| words[i].clone())
}

/// Packs a 64-byte block into 16 little-endian `u32` words (the block is
/// zero-padded to 64 bytes by the caller).
fn block_words<F: PrimeField>(block: &[UInt8<F>]) -> Result<[UInt32<F>; 16], SynthesisError> {
    debug_assert_eq!(block.len(), BLOCK_LEN);
    let mut words = Vec::with_capacity(16);
    for chunk in block.chunks(4) {
        words.push(UInt32::from_bytes_le(chunk)?);
    }
    Ok(core::array::from_fn(|i| words[i].clone()))
}

/// The standing data of an in-progress output node (chunk or parent), from
/// which either a chaining value or the root output can be derived.
struct Output<F: PrimeField> {
    input_chaining_value: [UInt32<F>; 8],
    block_words: [UInt32<F>; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
}

impl<F: PrimeField> Output<F> {
    fn chaining_value(&self) -> [UInt32<F>; 8] {
        first_8_words(compress(
            &self.input_chaining_value,
            &self.block_words,
            self.counter,
            self.block_len,
            self.flags,
        ))
    }

    fn root_output_bytes(&self) -> Result<Vec<UInt8<F>>, SynthesisError> {
        let words = compress(
            &self.input_chaining_value,
            &self.block_words,
            0,
            self.block_len,
            self.flags | ROOT,
        );
        let mut out = Vec::with_capacity(OUT_LEN);
        for word in words.iter().take(OUT_LEN / 4) {
            out.extend(word.to_bytes_le()?);
        }
        Ok(out)
    }
}

/// Computes the [`Output`] of a single chunk (`chunk_bytes`, `<= CHUNK_LEN`) at
/// index `chunk_counter`.
fn chunk_output<F: PrimeField>(
    chunk_bytes: &[UInt8<F>],
    chunk_counter: u64,
) -> Result<Output<F>, SynthesisError> {
    debug_assert!(!chunk_bytes.is_empty() && chunk_bytes.len() <= CHUNK_LEN);
    let mut chaining_value: [UInt32<F>; 8] = core::array::from_fn(|i| UInt32::constant(IV[i]));

    let num_blocks = chunk_bytes.len().div_ceil(BLOCK_LEN);
    for b in 0..num_blocks {
        let start = b * BLOCK_LEN;
        let end = (start + BLOCK_LEN).min(chunk_bytes.len());
        let raw = &chunk_bytes[start..end];
        let block_len = raw.len() as u32;

        // Zero-pad the (possibly partial) last block to 64 bytes.
        let mut block = raw.to_vec();
        block.resize(BLOCK_LEN, UInt8::constant(0));
        let words = block_words(&block)?;

        let is_first = b == 0;
        let is_last = b == num_blocks - 1;
        let mut flags = 0u32;
        if is_first {
            flags |= CHUNK_START;
        }

        if is_last {
            // The final block produces the chunk's Output (CHUNK_END set).
            return Ok(Output {
                input_chaining_value: chaining_value,
                block_words: words,
                counter: chunk_counter,
                block_len,
                flags: flags | CHUNK_END,
            });
        }

        // Non-final full block: fold into the chaining value.
        chaining_value = first_8_words(compress(
            &chaining_value,
            &words,
            chunk_counter,
            BLOCK_LEN as u32,
            flags,
        ));
    }
    unreachable!("a non-empty chunk always has a final block");
}

/// Builds the `Output` for a parent node combining two child chaining values.
fn parent_output<F: PrimeField>(left: &[UInt32<F>; 8], right: &[UInt32<F>; 8]) -> Output<F> {
    let block_words: [UInt32<F>; 16] = core::array::from_fn(|i| {
        if i < 8 {
            left[i].clone()
        } else {
            right[i - 8].clone()
        }
    });
    Output {
        input_chaining_value: core::array::from_fn(|i| UInt32::constant(IV[i])),
        block_words,
        counter: 0,
        block_len: BLOCK_LEN as u32,
        flags: PARENT,
    }
}

fn parent_cv<F: PrimeField>(left: &[UInt32<F>; 8], right: &[UInt32<F>; 8]) -> [UInt32<F>; 8] {
    parent_output(left, right).chaining_value()
}

/// Computes the 32-byte BLAKE3 digest of `input`.
///
/// The chunk/tree structure follows the reference `Hasher`, but because the
/// input length is fixed here, the tree is built directly: each `CHUNK_LEN`
/// chunk yields a chaining value, and chaining values are merged via the same
/// stack discipline (`add_chunk_chaining_value` / right-edge finalization),
/// with the root node emitting the output bytes.
pub(super) fn blake3<F: PrimeField>(input: &[UInt8<F>]) -> Result<Vec<UInt8<F>>, SynthesisError> {
    // Empty input is a single empty chunk that is itself the root.
    if input.is_empty() {
        let output = Output {
            input_chaining_value: core::array::from_fn(|i| UInt32::constant(IV[i])),
            block_words: block_words(&vec![UInt8::constant(0); BLOCK_LEN])?,
            counter: 0,
            block_len: 0,
            flags: CHUNK_START | CHUNK_END,
        };
        return output.root_output_bytes();
    }

    let chunks: Vec<&[UInt8<F>]> = input.chunks(CHUNK_LEN).collect();
    let num_chunks = chunks.len();

    // Single chunk: it is the root directly.
    if num_chunks == 1 {
        let mut output = chunk_output(chunks[0], 0)?;
        output.flags |= ROOT;
        return output.root_output_bytes();
    }

    // Multiple chunks: replicate the CV stack discipline. `add_chunk_chaining_value`
    // merges completed subtrees (one merge per trailing zero bit of the running
    // chunk total), so the stack always holds the chaining values of the
    // perfect subtrees along the left edge.
    let mut cv_stack: Vec<[UInt32<F>; 8]> = Vec::new();
    for (i, chunk) in chunks.iter().enumerate().take(num_chunks - 1) {
        let cv = chunk_output(chunk, i as u64)?.chaining_value();
        let mut new_cv = cv;
        let mut total_chunks = (i as u64) + 1;
        while total_chunks & 1 == 0 {
            let left = cv_stack.pop().expect("stack underflow");
            new_cv = parent_cv(&left, &new_cv);
            total_chunks >>= 1;
        }
        cv_stack.push(new_cv);
    }

    // Finalize along the right edge: start from the last chunk's Output and fold
    // in the remaining stacked chaining values, with the root being the last
    // parent node.
    let mut output = chunk_output(chunks[num_chunks - 1], (num_chunks - 1) as u64)?;
    while let Some(left) = cv_stack.pop() {
        let right = output.chaining_value();
        output = parent_output(&left, &right);
    }
    output.flags |= ROOT;
    output.root_output_bytes()
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;
    use ark_r1cs_std::{GR1CSVar, alloc::AllocVar, uint8::UInt8};
    use ark_relations::gr1cs::ConstraintSystem;

    use super::*;

    /// The BLAKE3 official test-vector input pattern: byte `i` is `i % 251`.
    fn vector_input(n: usize) -> Vec<u8> {
        (0..n).map(|i| (i % 251) as u8).collect()
    }

    /// Exercises [`blake3`] over single-chunk, chunk-boundary, multi-chunk, and
    /// unbalanced-tree input lengths against the official BLAKE3 test vectors,
    /// confirming the chunk-chaining and tree logic.
    #[test]
    fn blake3_official_vectors() {
        // (input_len, expected 32-byte digest) from the BLAKE3 reference vectors.
        let cases: &[(usize, [u8; 32])] = &[
            (
                0,
                [
                    175, 19, 73, 185, 245, 249, 161, 166, 160, 64, 77, 234, 54, 220, 201, 73, 155,
                    203, 37, 201, 173, 193, 18, 183, 204, 154, 147, 202, 228, 31, 50, 98,
                ],
            ),
            (
                1,
                [
                    45, 58, 222, 223, 241, 27, 97, 241, 76, 136, 110, 53, 175, 160, 54, 115, 109,
                    205, 135, 167, 77, 39, 181, 193, 81, 2, 37, 208, 245, 146, 226, 19,
                ],
            ),
            (
                64,
                [
                    78, 237, 113, 65, 234, 74, 92, 212, 183, 136, 96, 107, 210, 63, 70, 226, 18,
                    175, 156, 172, 235, 172, 220, 125, 31, 76, 109, 199, 242, 81, 27, 152,
                ],
            ),
            (
                1024,
                [
                    66, 33, 71, 57, 240, 149, 164, 6, 243, 252, 131, 222, 184, 137, 116, 74, 192,
                    13, 248, 49, 193, 13, 170, 85, 24, 155, 93, 18, 28, 133, 90, 247,
                ],
            ),
            (
                1025,
                [
                    208, 2, 120, 174, 71, 235, 39, 179, 79, 174, 207, 103, 180, 254, 38, 63, 130,
                    213, 65, 41, 22, 193, 255, 217, 124, 140, 183, 251, 129, 75, 132, 68,
                ],
            ),
            (
                2048,
                [
                    231, 118, 182, 2, 140, 124, 210, 42, 77, 11, 161, 130, 168, 191, 98, 32, 93,
                    46, 245, 118, 70, 126, 131, 142, 214, 242, 82, 155, 133, 251, 162, 74,
                ],
            ),
            (
                3072,
                [
                    185, 140, 176, 255, 54, 35, 190, 3, 50, 107, 55, 61, 230, 185, 9, 82, 24, 81,
                    62, 100, 241, 238, 46, 221, 37, 37, 199, 173, 30, 92, 255, 210,
                ],
            ),
        ];

        for (len, expected) in cases {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let input: Vec<UInt8<Fr>> = vector_input(*len)
                .into_iter()
                .map(|b| UInt8::new_witness(cs.clone(), || Ok(b)).unwrap())
                .collect();
            let digest = blake3(&input).unwrap();
            let got: Vec<u8> = digest.iter().map(|b| b.value().unwrap()).collect();
            assert_eq!(got, expected.to_vec(), "blake3 mismatch at len {len}");
            assert!(cs.is_satisfied().unwrap(), "unsatisfied at len {len}");
        }
    }
}
