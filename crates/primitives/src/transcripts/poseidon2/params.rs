//! Deterministic Poseidon2 parameter generation, mirroring the [reference Sage
//! script] (used to derive Noir's constants) byte-for-byte. From a single Grain
//! LFSR stream seeded by `(field, sbox, n, t, R_F, R_P)` (the [Poseidon] layout)
//! it produces:
//!
//! 1. the round constants, by **rejection sampling** (`n`-bit draws `>= p` are
//!    discarded), and
//! 2. (for `t >= 4`) the internal-matrix diagonal `mu_i`, by **reducing mod
//!    `p`** (no rejection, note this asymmetry with (1)), redrawn until
//!    `circ(0, 1, ..., 1) + diag(mu)` satisfies the subspace-trail condition
//!    (see [`minpoly_condition_holds`]).
//!
//! [reference Sage script]: https://github.com/HorizenLabs/poseidon2/blob/main/poseidon2_rust_params.sage
//! [Poseidon]: https://eprint.iacr.org/2019/458.pdf

use ark_ff::{BigInteger, PrimeField};
use ark_std::vec::Vec;

/// The Grain LFSR self-shrinking generator used by the reference scripts.
pub(super) struct GrainLfsr {
    state: [bool; 80],
}

impl GrainLfsr {
    /// Seeds the generator as the reference `init_generator` does — the bit
    /// sequence `field=1 (2 bits) || sbox=0 (4) || n (12) || t (12) || R_F (10)
    /// || R_P (10) || 1^30` — then clocks out and discards 160 bits. (`n` is the
    /// modulus bit size; `sbox = 0` matches the reference, which does not feed
    /// the actual S-box degree.)
    fn new(n: usize, t: usize, rounds_f: usize, rounds_p: usize) -> Self {
        let mut bits = [false; 80];
        let mut i = 0;
        let mut push = |bits: &mut [bool; 80], value: usize, width: usize| {
            for b in (0..width).rev() {
                bits[i] = (value >> b) & 1 == 1;
                i += 1;
            }
        };
        push(&mut bits, 1, 2); // field = 1 (prime field)
        push(&mut bits, 0, 4); // sbox = 0 (as in the reference script)
        push(&mut bits, n, 12);
        push(&mut bits, t, 12);
        push(&mut bits, rounds_f, 10);
        push(&mut bits, rounds_p, 10);
        push(&mut bits, (1 << 30) - 1, 30); // thirty 1-bits

        let mut lfsr = GrainLfsr { state: bits };
        for _ in 0..160 {
            lfsr.clock();
        }
        lfsr
    }

    /// Clocks the 80-bit LFSR once with taps `x^80 + x^62 + x^51 + x^38 + x^23 +
    /// x^13 + 1` (0-indexed positions `62, 51, 38, 23, 13, 0`) and returns the
    /// new bit.
    fn clock(&mut self) -> bool {
        let new_bit = self.state[62]
            ^ self.state[51]
            ^ self.state[38]
            ^ self.state[23]
            ^ self.state[13]
            ^ self.state[0];
        self.state.copy_within(1.., 0);
        self.state[79] = new_bit;
        new_bit
    }

    /// Produces the next output bit under the self-shrinking rule: emit a bit
    /// only when the preceding clocked bit is `1`, skipping pairs otherwise.
    fn next_bit(&mut self) -> bool {
        let mut new_bit = self.clock();
        while !new_bit {
            self.clock();
            new_bit = self.clock();
        }
        self.clock()
    }

    /// Reads `num_bits` output bits in big-endian order (most-significant first,
    /// matching the reference's `grain_random_bits`).
    fn next_bits(&mut self, num_bits: usize) -> Vec<bool> {
        (0..num_bits).map(|_| self.next_bit()).collect()
    }

    /// Reads a **round constant**: rejection-samples `n`-bit draws until one is
    /// `< p`. (`F::from_bigint` returns `Some` iff `< p`, doubling as the
    /// rejection predicate.)
    fn next_field<F: PrimeField>(&mut self, n: usize) -> F {
        loop {
            let candidate = F::BigInt::from_bits_be(&self.next_bits(n));
            if let Some(f) = F::from_bigint(candidate) {
                return f;
            }
        }
    }

    /// Reads a **diagonal entry**: a single `n`-bit draw reduced mod `p`, with
    /// no rejection (matching the reference's `F(grain_random_bits(n))`).
    fn next_field_reduce<F: PrimeField>(&mut self, n: usize) -> F {
        let bytes = F::BigInt::from_bits_be(&self.next_bits(n)).to_bytes_be();
        F::from_be_bytes_mod_order(&bytes)
    }
}

/// Generates the Poseidon2 round constants and (for `t >= 4`) the internal
/// matrix diagonal `mu_i`, as the reference script does.
///
/// `round_constants` is the flat per-round layout (`rounds_f + rounds_p` rows of
/// `t`, internal rounds carrying their single constant at index `0`);
/// `mat_internal_diag_mu` holds the raw `mu_i` (empty for `t in {2, 3}`).
pub(super) fn generate<F: PrimeField>(
    t: usize,
    rounds_f: usize,
    rounds_p: usize,
) -> (Vec<Vec<F>>, Vec<F>) {
    // `n` is the bit length of the field modulus `p`, matching the reference's
    // `n = len(p.bits())`.
    let n = F::MODULUS_BIT_SIZE as usize;
    let mut lfsr = GrainLfsr::new(n, t, rounds_f, rounds_p);

    // Full rounds draw `t` constants each; internal rounds draw one (index `0`).
    let rounds_f_half = rounds_f / 2;
    let mut round_constants = Vec::with_capacity(rounds_f + rounds_p);
    for r in 0..rounds_f + rounds_p {
        let is_internal = r >= rounds_f_half && r < rounds_f_half + rounds_p;
        if is_internal {
            let mut row = vec![F::zero(); t];
            row[0] = lfsr.next_field(n);
            round_constants.push(row);
        } else {
            round_constants.push((0..t).map(|_| lfsr.next_field(n)).collect());
        }
    }

    // Internal-matrix diagonal (t >= 4 only), drawn from the same stream after
    // the constants and redrawn until it satisfies the subspace-trail condition.
    let mat_internal_diag_mu = if t == 2 || t == 3 {
        Vec::new()
    } else {
        loop {
            let diag: Vec<F> = (0..t).map(|_| lfsr.next_field_reduce(n)).collect();
            if minpoly_condition_holds(&diag) {
                break diag;
            }
        }
    };

    (round_constants, mat_internal_diag_mu)
}

/// Checks the reference's `check_minpoly_condition` (rules out arbitrarily long
/// subspace trails): for every `k in 1..=2t`, `minpoly(M^k)` is irreducible of
/// degree `t`, where `M = circ(0, 1, ..., 1) + diag(mu)`.
///
/// Equivalent but cheaper formulation: once `f = minpoly(M)` is irreducible of
/// degree `t`, `M` acts as a generator `α` of `F_{p^t} = F_p[x]/(f)` with
/// `M^k ~ α^k = x^k mod f`. Then `minpoly(α^k)` has degree `t` iff `α^k`
/// generates `F_{p^t}`, i.e. for every prime `q | t`, `(α^k)^{p^{t/q}} != α^k`.
/// So only the `k = 1` case runs the expensive degree-`p` irreducibility test;
/// its Frobenius images `x^{p^{t/q}} mod f` are reused, and each
/// `(α^k)^{p^{t/q}} = (x^{p^{t/q}})^k` is a cheap small-exponent power.
fn minpoly_condition_holds<F: PrimeField>(diag: &[F]) -> bool {
    let t = diag.len();
    // M = all-ones off-diagonal + (mu_i) on the diagonal.
    let m: Vec<Vec<F>> = (0..t)
        .map(|i| {
            (0..t)
                .map(|j| if i == j { diag[i] } else { F::one() })
                .collect()
        })
        .collect();

    // k = 1: M itself must have an irreducible minimal polynomial of degree t.
    let Some(f) = minimal_polynomial(&m) else {
        return false;
    };
    if f.len() != t + 1 {
        return false;
    }
    // `frobenius[s - 1] = x^(p^s) mod f`; `None` if `f` is not irreducible.
    let Some(frobenius) = irreducibility_frobenius(&f) else {
        return false;
    };

    // k = 2..=2t: α^k = x^k mod f must generate F_{p^t}.
    let reducer = ModReducer::new(&f);
    let x = vec![F::zero(), F::one()];
    let primes = distinct_prime_factors(t);
    for k in 2..=2 * t {
        let alpha_k = poly_pow_mod_with(&x, &usize_bits_le(k), &reducer);
        // α^k generates F_{p^t} iff (α^k)^{p^{t/q}} != α^k for every prime q | t.
        for &q in &primes {
            // (α^k)^{p^{t/q}} = (x^{p^{t/q}})^k mod f.
            let beta = &frobenius[t / q - 1];
            let conj = poly_pow_mod_with(beta, &usize_bits_le(k), &reducer);
            if poly_trim(&conj) == poly_trim(&alpha_k) {
                return false;
            }
        }
    }
    true
}

/// Little-endian bit decomposition of a small `usize` exponent (no trailing
/// zeros; empty for `0`).
fn usize_bits_le(mut n: usize) -> Vec<bool> {
    let mut bits = Vec::new();
    while n > 0 {
        bits.push(n & 1 == 1);
        n >>= 1;
    }
    bits
}

/// Minimal polynomial of a `t x t` matrix as a monic coefficient vector
/// (low-to-high). Finds the least `d` with `I, M, ..., M^d` linearly dependent
/// and solves `M^d = sum_{i<d} a_i M^i`.
fn minimal_polynomial<F: PrimeField>(m: &[Vec<F>]) -> Option<Vec<F>> {
    let t = m.len();
    let flatten = |a: &[Vec<F>]| -> Vec<F> { a.iter().flatten().copied().collect() };

    let identity: Vec<Vec<F>> = (0..t)
        .map(|i| {
            (0..t)
                .map(|j| if i == j { F::one() } else { F::zero() })
                .collect()
        })
        .collect();

    // Flattened powers M^0, M^1, ... as row vectors (the matrices themselves are
    // not retained — only their flattenings are needed for the rank test).
    let mut flats = vec![flatten(&identity)];
    let mut current = identity;
    for _ in 0..t * t {
        current = mat_mul(m, &current);
        let flat = flatten(&current);
        // If the latest power lies in the span of the previous ones, the
        // minimal polynomial degree equals the current number of prior powers.
        if let Some(coeffs) = solve_combination(&flats, &flat) {
            // M^d = sum coeffs[i] M^i  =>  minpoly = x^d - sum coeffs[i] x^i.
            let mut minpoly: Vec<F> = coeffs.into_iter().map(|c| -c).collect();
            minpoly.push(F::one());
            return Some(minpoly);
        }
        flats.push(flat);
    }
    None
}

/// If `target` is in the span of `basis`, returns the (unique, since `basis` is
/// kept linearly independent) coefficients; otherwise returns `None`.
fn solve_combination<F: PrimeField>(basis: &[Vec<F>], target: &[F]) -> Option<Vec<F>> {
    let k = basis.len();
    let len = target.len();
    // Augmented system: columns are the basis vectors, RHS is `target`.
    let mut aug: Vec<Vec<F>> = (0..len)
        .map(|i| {
            let mut row: Vec<F> = basis.iter().map(|b| b[i]).collect();
            row.push(target[i]);
            row
        })
        .collect();

    let mut where_pivot = vec![usize::MAX; k];
    let mut rank = 0;
    for col in 0..k {
        let Some(pivot) = (rank..len).find(|&r| !aug[r][col].is_zero()) else {
            continue;
        };
        aug.swap(rank, pivot);
        let inv = aug[rank][col].inverse().unwrap();
        for x in aug[rank].iter_mut() {
            *x *= inv;
        }
        // Eliminate `col` from every other row using the (now-normalized) pivot
        // row; clone it first to avoid holding two mutable borrows of `aug`.
        let pivot_row = aug[rank].clone();
        for (r, row) in aug.iter_mut().enumerate() {
            if r != rank && !row[col].is_zero() {
                let factor = row[col];
                for (cell, pivot_cell) in row.iter_mut().zip(&pivot_row) {
                    *cell -= factor * *pivot_cell;
                }
            }
        }
        where_pivot[col] = rank;
        rank += 1;
        if rank == len {
            break;
        }
    }

    // Consistency: every all-zero coefficient row must have a zero RHS.
    for row in &aug {
        if row[..k].iter().all(|x| x.is_zero()) && !row[k].is_zero() {
            return None;
        }
    }

    Some(
        (0..k)
            .map(|col| {
                if where_pivot[col] == usize::MAX {
                    F::zero()
                } else {
                    aug[where_pivot[col]][k]
                }
            })
            .collect(),
    )
}

/// Rabin's irreducibility test on the monic polynomial `f` (degree `d`); on
/// success returns the Frobenius table `[x^(p^1) mod f, ..., x^(p^d) mod f]`,
/// else `None`. `f` is irreducible iff `x^(p^d) ≡ x (mod f)` and
/// `gcd(x^(p^(d/q)) - x, f) = 1` for each prime `q | d`. The table is built once
/// and reused by the caller's generator checks.
fn irreducibility_frobenius<F: PrimeField>(f: &[F]) -> Option<Vec<Vec<F>>> {
    let d = f.len() - 1;
    if d == 0 {
        return None;
    }
    let x = vec![F::zero(), F::one()];
    if d == 1 {
        return Some(vec![x]);
    }

    // The Frobenius exponent is the field modulus `p`; decompose it into bits
    // once (least-significant-first, trailing zeros trimmed) and reuse across
    // every `g -> g^p` step.
    let p_bits = {
        let mut bits = F::MODULUS.to_bits_le();
        while bits.last() == Some(&false) {
            bits.pop();
        }
        bits
    };

    // `frobenius[s - 1] = x^(p^s) mod f`, built iteratively (each step applies
    // one Frobenius map `g -> g^p mod f`), reusing a single reduction table.
    let reducer = ModReducer::new(f);
    let mut frobenius = Vec::with_capacity(d);
    let mut acc = x.clone();
    for _ in 0..d {
        acc = poly_pow_mod_with(&acc, &p_bits, &reducer);
        frobenius.push(acc.clone());
    }

    // x^(p^d) ≡ x (mod f)?
    if poly_trim(&frobenius[d - 1]) != x {
        return None;
    }

    // For each prime q | d: gcd(x^(p^(d/q)) - x, f) must be a unit.
    for q in distinct_prime_factors(d) {
        let mut g = frobenius[d / q - 1].clone();
        if g.len() < 2 {
            g.resize(2, F::zero());
        }
        g[1] -= F::one(); // subtract x
        let gcd = poly_gcd(&poly_trim(&g), f);
        if gcd.len() != 1 {
            return None;
        }
    }
    Some(frobenius)
}

fn distinct_prime_factors(mut d: usize) -> Vec<usize> {
    let mut factors = Vec::new();
    let mut q = 2;
    while q * q <= d {
        if d.is_multiple_of(q) {
            factors.push(q);
            while d.is_multiple_of(q) {
                d /= q;
            }
        }
        q += 1;
    }
    if d > 1 {
        factors.push(d);
    }
    factors
}

// --- Polynomial arithmetic over F[x] (coefficients low-to-high) -------------

fn poly_trim<F: PrimeField>(a: &[F]) -> Vec<F> {
    let mut a = a.to_vec();
    while a.len() > 1 && a.last() == Some(&F::zero()) {
        a.pop();
    }
    if a.is_empty() {
        a.push(F::zero());
    }
    a
}

/// Remainder of `a` modulo the monic polynomial `m`.
fn poly_rem<F: PrimeField>(a: &[F], m: &[F]) -> Vec<F> {
    let mut a = poly_trim(a);
    let dm = m.len() - 1;
    // `m` is monic, so the leading coefficient is `1`.
    while a.len() > dm {
        let lead = *a.last().unwrap();
        if lead.is_zero() {
            a.pop();
            continue;
        }
        let shift = a.len() - 1 - dm;
        for i in 0..=dm {
            let sub = lead * m[i];
            a[shift + i] -= sub;
        }
        a = poly_trim(&a);
    }
    a
}

/// Fast multiplication in `F[x]/(f)` for a fixed monic modulus `f` of degree
/// `d`. A product of two residues has degree `<= 2d - 2`; precomputing
/// `x^j mod f` for `j in d..=2d-2` turns the reduction into fused multiply-adds
/// into the low `d` coefficients, avoiding iterative long division.
struct ModReducer<F: PrimeField> {
    /// `f` itself, degree `d` (monic).
    modulus: Vec<F>,
    d: usize,
    /// `high[j - d] = x^j mod f` for `j in d..=2d-2` (empty when `d <= 1`).
    high: Vec<Vec<F>>,
}

impl<F: PrimeField> ModReducer<F> {
    fn new(modulus: &[F]) -> Self {
        let d = modulus.len() - 1;
        // x^d mod f = -(f without its leading term), padded to length d.
        let mut high: Vec<Vec<F>> = Vec::new();
        if d >= 1 {
            let mut xd = vec![F::zero(); d];
            for i in 0..d {
                xd[i] = -modulus[i];
            }
            high.push(xd);
            // x^{j+1} mod f = x * (x^j mod f): shift up by one and fold the new
            // degree-`d` term back via x^d mod f (= high[0]).
            for _ in (d + 1)..=(2 * d - 2) {
                let prev = high.last().unwrap();
                let mut next = vec![F::zero(); d];
                let overflow = prev[d - 1];
                for i in (0..d - 1).rev() {
                    next[i + 1] = prev[i];
                }
                for i in 0..d {
                    next[i] += overflow * high[0][i];
                }
                high.push(next);
            }
        }
        ModReducer {
            modulus: modulus.to_vec(),
            d,
            high,
        }
    }

    /// Reduces `a` (a residue of degree `< d`) — identity, but normalizes length.
    fn reduce_input(&self, a: &[F]) -> Vec<F> {
        poly_rem(a, &self.modulus)
    }

    /// Multiplies two residues `a`, `b` (each degree `< d`) modulo `f`, returning
    /// a length-`d` coefficient vector.
    fn mul(&self, a: &[F], b: &[F]) -> Vec<F> {
        if self.d == 0 {
            return vec![F::zero()];
        }
        // Full product (degree <= 2d - 2).
        let mut prod = vec![F::zero(); a.len() + b.len() - 1];
        for (i, &ai) in a.iter().enumerate() {
            if ai.is_zero() {
                continue;
            }
            for (j, &bj) in b.iter().enumerate() {
                prod[i + j] += ai * bj;
            }
        }
        // Fold the low `d` coefficients directly, and the high ones via the table.
        let mut out = vec![F::zero(); self.d];
        for (idx, &c) in prod.iter().enumerate() {
            if idx < self.d {
                out[idx] += c;
            } else {
                // c * (x^idx mod f)
                let row = &self.high[idx - self.d];
                for i in 0..self.d {
                    out[i] += c * row[i];
                }
            }
        }
        out
    }
}

/// `base^exp mod f` in `F[x]/(f)`, with `exp` as little-endian bits (no trailing
/// zeros) and `reducer` the shared [`ModReducer`] for `f`. Used for both the
/// Frobenius map (exponent `p`) and small-exponent element powers.
fn poly_pow_mod_with<F: PrimeField>(
    base: &[F],
    exp_bits: &[bool],
    reducer: &ModReducer<F>,
) -> Vec<F> {
    let mut result = vec![F::one()];
    let mut b = reducer.reduce_input(base);
    for (i, &bit) in exp_bits.iter().enumerate() {
        if bit {
            result = reducer.mul(&result, &b);
        }
        // Skip the final squaring once the top set bit has been consumed.
        if i + 1 < exp_bits.len() {
            b = reducer.mul(&b, &b);
        }
    }
    poly_trim(&result)
}

/// Monic gcd of two polynomials in `F[x]`.
fn poly_gcd<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    let mut a = poly_trim(a);
    let mut b = poly_trim(b);
    while !(b.len() == 1 && b[0].is_zero()) {
        let r = poly_rem_general(&a, &b);
        a = b;
        b = poly_trim(&r);
    }
    // Normalize to monic.
    if let Some(&lead) = a.last()
        && !lead.is_zero()
    {
        let inv = lead.inverse().unwrap();
        for c in a.iter_mut() {
            *c *= inv;
        }
    }
    a
}

/// Remainder of `a` modulo a general (not necessarily monic) polynomial `b`.
fn poly_rem_general<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    let mut a = poly_trim(a);
    let b = poly_trim(b);
    let db = b.len() - 1;
    let inv_lead = b[db].inverse().unwrap();
    while a.len() > db && !(a.len() == 1 && a[0].is_zero()) {
        let lead = *a.last().unwrap();
        if lead.is_zero() {
            a.pop();
            continue;
        }
        let coeff = lead * inv_lead;
        let shift = a.len() - 1 - db;
        for i in 0..=db {
            let sub = coeff * b[i];
            a[shift + i] -= sub;
        }
        a = poly_trim(&a);
    }
    a
}

// --- Matrix arithmetic over F ----------------------------------------------

fn mat_mul<F: PrimeField>(a: &[Vec<F>], b: &[Vec<F>]) -> Vec<Vec<F>> {
    let t = a.len();
    (0..t)
        .map(|i| {
            (0..t)
                .map(|j| (0..t).map(|k| a[i][k] * b[k][j]).sum())
                .collect()
        })
        .collect()
}
