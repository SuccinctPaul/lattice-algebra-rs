//! LaBRADOR-style batched-opening proof for toy R1CS (L5, Z2).
//!
//! # Protocol
//!
//! Instance: a [`ToyR1cs`] over `R = Z_{2^32}[X]/(X^64+1)` and an Ajtai
//! commitment key `A_com ∈ R^{N×M}` (tall: `N ≥ 2M`).
//! Witness: `z ∈ R^M` satisfying the gates.
//!
//! ```text
//! prover                                   verifier
//! c = A_com·z   (Ajtai commitment)
//! d = A_com·y   (mask commitment)  ──c,d──▶ X ← H(transcript) ∈ R
//! z' = z + X·y                    ──z'──▶  1. A_com·z' == c + X·d   (binding link)
//!                                          2. (A_k·z')² == U_k·z'[sel_k] ∀k
//! ```
//!
//! *Batched opening*: the single response `z'` opens **all** witness
//! polynomials simultaneously against the ring challenge `C` — the same
//! role LaBRADOR's `σ_i = w(X_i)` plays, here with one ring-challenge and
//! ring multiplication as the evaluation map.
//!
//! *Soundness sketch*: after committing `c, d`, the response is uniquely
//! pinned by the overdetermined linear check `A_com·z' = c + C·d`
//! (`N·64` scalar equations over `M·64` unknowns, `N ≥ 2M`), so the
//! constraint check on that unique `z'` cannot be adapted to a false
//! instance; deviating requires solving the R1CS or the linear problem,
//! each ≈ 2^-32 per ring coefficient by Schwartz–Zippel on `X`.
//!
//! *Knowledge*: the extractor of the binding link recovers `z'` itself —
//! the proven object *is* the satisfying vector (transparent proof of
//! knowledge, not ZK — same status as LaBRADOR).
//!
//! # The challenge must be a true non-unit
//!
//! The challenge element is `C = X − a` with the scalar `a` forced **odd**.
//! This matters: in `R = Z_{2^32}[X]/(X^64+1)` the monomial `X` is always a
//! unit (`X·(−X^63) = −X^64 = 1`), so a *unit* challenge would make the
//! verifier equation `C·t* + C²·q* = Σγ^k R_k` solvable for `t*` for **any**
//! response — the check would be vacuous. `X − a` with `a` odd is a genuine
//! non-unit: reducing mod 2 gives `X + 1`, which is nilpotent in
//! `F_2[X]/(X+1)^64`, and units lift. With a non-unit challenge the
//! equation is solvable only when `Σγ^k R_k ∈ C·R`; that ideal is exactly
//! `{f : Σ coeffs even}` and has index 2 — the coefficient-sum map
//! `χ(f) = Σ f_i (mod 2)` is a well-defined homomorphism `R → F_2` (it
//! kills both `2` and `X^64 + 1`), `χ(C) = 1 − a ≡ 0 (mod 2)` puts `C·R`
//! inside its kernel, and both have index 2, cross-checked by the norm
//! `N(C) = a^64 + 1` whose `v_2` is exactly 1 for odd `a`. Because χ is
//! multiplicative, the certified bit is `χ(R_0) + χ(γ)·Σ_{k≥1} χ(R_k)` —
//! two `F_2`-linear functionals of the witness's coefficient-sum vector. A
//! false response therefore passes with probability ½ per mask attempt (or
//! always, if its witness satisfies those parity conditions
//! structurally). The
//! full relation soundness of the documented design requires the LaBRADOR
//! recursion (committing the masked terms `m_k, q_k` under a second Ajtai
//! key before the challenges open them) — tracked as the Z2 milestone; the
//! Z3 sumcheck path replaces this single combination with round-by-round
//! challenges.
//!
//! # Why the amortized compression is not a local change
//!
//! The natural compression — replacing the revelation of `m, q` by a
//! second-level Σ-response `z_m = y_m + X₂·m` under the recursion key —
//! does **not** preserve the soundness upgrade (attempted and analyzed):
//!
//! - Bridging the hidden per-gate terms to the revealed `t*` multiplies
//!   through the level-2 challenge: consistency reduces to
//!   `X₂·(t* − ⟨γ, m⟩) = 0`. `X₂` must stay a **non-unit** (a unit
//!   level-2 challenge lets a forger solve the links post-hoc), and a
//!   non-unit of `Z_{2^32}[X]/(X^64+1)` is a zero divisor with a
//!   nontrivial annihilator — the bridge re-admits exactly the
//!   ½-per-grind slack the recursion was built to close.
//! - Dropping the per-gate responses entirely makes the check vacuous:
//!   the recursion key `A₂ ∈ R^{4×GATES}` has full row rank, so any
//!   claimed combined response solves `A₂·Z = RHS` for an arbitrary
//!   claimed `t*`.
//!
//! The sound compression therefore needs the full LaBRADOR
//! amortized-openings machinery: per-gate commitments folded pairwise
//! (Ajtai linearity `A·(s + γs′) = A·s + γ·A·s′` moves the challenge to
//! the commitment side where it is verifier-computable), with
//! JL-projection norm checks closing the relaxed extraction — tracked as
//! the Z2/Z3 size-optimization milestone (survey rows 19/24).
//!
//! # Approximate shortness (gadget layer)
//!
//! [`gadget_split`] decomposes coefficients into high digits plus a centered
//! low residual; [`approx_linear_check`] accepts openings that match the
//! committed value only up to a **provable slack** `slack_bound(...)`. This
//! is the machinery the full LaBRADOR recursion (Z3) layers into a complete
//! shortness proof.

use crate::commitment::key::AjtaiKey;
use crate::foundation::encoding::{ring_from_u32, ring_to_u32, u32s_to_le_bytes};
use crate::foundation::fs::absorb_rings;
use crate::foundation::sampling::{
    nonunit_linear_poly, uniform_matrix_from_seed, uniform_ring_from_seed, uniform_vec_from_seed,
};
use crate::instance::r1cs::{map_over_gates, ToyR1cs};
use crate::instance::ring::{Z2Coeff, Z2Ring, D};
use crate::instance::simd::z2_mul;
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake128Xof;
use algebra::ring::MatrixElement;
// Needed only under some `cfg` (test or feature); the plain lib build
// does not use it, so the lint cannot be satisfied by deleting it.
#[allow(unused_imports)]
use alloc::{vec, vec::Vec};

/// Commitment-key dimensions: `A_com ∈ R^{N_COMMIT×M_VARS}`.
pub const N_COMMIT: usize = 8;
/// Witness length (ring variables).
pub const M_VARS: usize = 2;

/// Ajtai commitment key over the Z2 ring (raw-coefficient expansion) —
/// the shared [`AjtaiKey`] under the protocol-historical name.
pub type Z2CommitKey = AjtaiKey<N_COMMIT, M_VARS>;

// === LaBRADOR recursion: full relation soundness (transparent, O(G) size) ===

/// Rows of the recursion commitment key `A₂ ∈ R^{N_RECURSION×GATES}`.
pub const N_RECURSION: usize = 4;

/// Derives the recursion commitment key for a gate count (runtime shaped:
/// one column per gate, derived from the same seed as `A_com` under a
/// distinct domain label).
pub(crate) fn recursion_key(seed: &[u8; 32], gates: usize) -> Vec<Vec<Z2Ring>> {
    uniform_matrix_from_seed::<Z2Coeff, D>(b"z2-recursion", seed, N_RECURSION, gates)
}

/// `A₂·v` for the runtime-shaped recursion key.
pub(crate) fn commit_masked(a2: &[Vec<Z2Ring>], v: &[Z2Ring]) -> Vec<Z2Ring> {
    (0..N_RECURSION)
        .map(|i| {
            let mut acc = Z2Ring::zero();
            for (a, v) in a2[i].iter().zip(v) {
                acc += z2_mul(a, v);
            }
            acc
        })
        .collect()
}

/// Recursive-mode challenges: identical to [`challenges`] but absorbing the
/// masked-term commitments — the recursion's whole point is that they are
/// bound *before* the challenges open them.
fn challenges_recursive(
    key_seed: &[u8; 32],
    r1cs_seed: &[u8; 32],
    c: &[Z2Ring],
    d: &[Z2Ring],
    c_masked: &[Z2Ring],
    c_quad: &[Z2Ring],
) -> (Z2Ring, Z2Ring) {
    let mut tr = Transcript::<Shake128Xof>::new(b"lattice-algebra/Z2/batched-open");
    tr.absorb(b"key", key_seed);
    tr.absorb(b"r1cs", r1cs_seed);
    absorb_rings(&mut tr, b"c", c);
    absorb_rings(&mut tr, b"d", d);
    absorb_rings(&mut tr, b"cm", c_masked);
    absorb_rings(&mut tr, b"cq", c_quad);
    let seed = tr.challenge_bytes(64);
    let x = nonunit_linear_poly::<Z2Coeff, Shake128Xof, D>(
        &mut crate::foundation::fs::seed_stream(b"X", &seed),
    );
    let gamma = uniform_ring_from_seed::<Z2Coeff, D>(b"gamma", &seed);
    (x, gamma)
}

/// Proof with the LaBRADOR recursion applied: the per-gate masked terms are
/// Ajtai-committed **before** the challenges open them, and revealed with
/// the proof. This upgrades the constraint check from the compact mode's
/// single parity bit to **full relation soundness**: an accepting proof
/// implies `Σγ^k R_k(z_fake) = 0` for the *pre-committed* false witness —
/// i.e. the witness satisfies the gates exactly in the ring.
///
/// Cost: the masked-term vectors (`2·GATES` ring elements) dominate the
/// proof size. Amortizing that revelation (challenge-driven second-level
/// combinations instead of full revelation) is exactly LaBRADOR's
/// contribution and stays a size-optimization milestone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Z2RecursiveProof {
    /// The compact-mode proof (mask commitment, response, combined terms).
    pub base: Z2Proof,
    /// `A₂·m` — masked linear terms, committed before the challenges.
    pub c_masked: Vec<Z2Ring>,
    /// `A₂·q` — masked quadratic terms, committed before the challenges.
    pub c_quad: Vec<Z2Ring>,
    /// The per-gate masked linear terms `m` (revealed).
    pub masked: Vec<Z2Ring>,
    /// The per-gate masked quadratic terms `q` (revealed).
    pub quad: Vec<Z2Ring>,
}

/// Prover side of the recursive mode: identical first message to [`prove`],
/// plus the recursion commitments of the per-gate masked terms.
///
/// # Example
///
/// ```rust
/// use zk::instance::r1cs::gen_toy_instance;
/// use zk::opening::{prove_recursive, verify_recursive, Z2CommitKey};
///
/// let (r1cs, z) = gen_toy_instance(&[1u8; 32], 8, 2);
/// let key = Z2CommitKey::setup(&[2u8; 32]);
/// let key_seed = [2u8; 32];
/// let r1cs_seed = [3u8; 32];
///
/// let (c, proof) =
///     prove_recursive(&key, &key_seed, &r1cs_seed, &r1cs, &z, &[9u8; 32]);
/// assert!(verify_recursive(&key, &key_seed, &r1cs_seed, &r1cs, &c, &proof));
/// ```
pub fn prove_recursive(
    key: &Z2CommitKey,
    key_seed: &[u8; 32],
    r1cs_seed: &[u8; 32],
    r1cs: &ToyR1cs,
    z: &[Z2Ring],
    randomness: &[u8; 32],
) -> (Vec<Z2Ring>, Z2RecursiveProof) {
    debug_assert_eq!(z.len(), M_VARS);
    let c = key.commit(z);
    let y = uniform_vec_from_seed::<Z2Coeff, D>(b"mask", randomness, M_VARS);
    let d = key.commit(&y);
    let (m, q) = masked_constraint_terms(r1cs, z, &y);
    let a2 = recursion_key(key_seed, r1cs.a.len());
    let c_masked = commit_masked(&a2, &m);
    let c_quad = commit_masked(&a2, &q);
    let (x, gamma) = challenges_recursive(key_seed, r1cs_seed, &c, &d, &c_masked, &c_quad);
    let z_prime: Vec<Z2Ring> = z
        .iter()
        .zip(&y)
        .map(|(zi, yi)| zi.clone() + x.clone() * yi.clone())
        .collect();
    let t_star = ring_combine(&m, &gamma);
    let q_star = ring_combine(&q, &gamma);
    (
        c,
        Z2RecursiveProof {
            base: Z2Proof {
                d,
                z_prime,
                t_star,
                q_star,
            },
            c_masked,
            c_quad,
            masked: m,
            quad: q,
        },
    )
}

/// Verifier side of the recursive mode. Beyond the compact checks, the
/// revealed masked terms are pinned to their pre-challenge commitments and
/// to the combined terms — closing the adaptivity gap entirely.
pub fn verify_recursive(
    key: &Z2CommitKey,
    key_seed: &[u8; 32],
    r1cs_seed: &[u8; 32],
    r1cs: &ToyR1cs,
    c: &[Z2Ring],
    proof: &Z2RecursiveProof,
) -> bool {
    let gates = r1cs.a.len();
    if proof.base.d.len() != N_COMMIT
        || proof.base.z_prime.len() != M_VARS
        || proof.c_masked.len() != N_RECURSION
        || proof.c_quad.len() != N_RECURSION
        || proof.masked.len() != gates
        || proof.quad.len() != gates
    {
        return false;
    }
    let a2 = recursion_key(key_seed, gates);
    let (x, gamma) = challenges_recursive(
        key_seed,
        r1cs_seed,
        c,
        &proof.base.d,
        &proof.c_masked,
        &proof.c_quad,
    );

    // 1. binding link: A_com·z' == c + X·d
    let azp = key.commit(&proof.base.z_prime);
    for i in 0..N_COMMIT {
        let rhs = c[i].clone() + x.clone() * proof.base.d[i].clone();
        if ring_to_u32(&azp[i]) != ring_to_u32(&rhs) {
            return false;
        }
    }

    // 2. the masked terms match their pre-challenge commitments (exact)
    if commit_masked(&a2, &proof.masked) != proof.c_masked {
        return false;
    }
    if commit_masked(&a2, &proof.quad) != proof.c_quad {
        return false;
    }

    // 3. the combined terms are the γ-combinations of the revealed vectors
    if ring_combine(&proof.masked, &gamma) != proof.base.t_star {
        return false;
    }
    if ring_combine(&proof.quad, &gamma) != proof.base.q_star {
        return false;
    }

    // 4. the compact equation, now over pre-committed terms:
    //    Σγ^k R_k(z') == X·t* + X²·q*
    let residuals = constraint_residuals(r1cs, &proof.base.z_prime);
    let r_comb = ring_combine(&residuals, &gamma);
    let x2 = x.clone() * x.clone();
    let rhs_comb = x.clone() * proof.base.t_star.clone() + x2 * proof.base.q_star.clone();
    ring_to_u32(&r_comb) == ring_to_u32(&rhs_comb)
}

pub use crate::shortness::gadget::{approx_linear_check, gadget_join, gadget_split, slack_bound};

/// Proof for one batched opening: mask commitment + response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Z2Proof {
    /// Mask commitment `d = A_com·y`.
    pub d: Vec<Z2Ring>,
    /// Response `z' = z + X·y`.
    pub z_prime: Vec<Z2Ring>,
    /// Masked linear constraint term `t* = Σ γ^k·m_k`.
    pub t_star: Z2Ring,
    /// Masked quadratic constraint term `q* = Σ γ^k·q_k`.
    pub q_star: Z2Ring,
}

impl Z2Proof {
    /// Wire size in bytes (raw little-endian ring coefficients).
    pub fn encoded_len(&self) -> usize {
        (self.d.len() + self.z_prime.len() + 2) * D * 4
    }

    /// Serializes the proof.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.encoded_len());
        for r in self.d.iter().chain(&self.z_prime) {
            out.extend_from_slice(&u32s_to_le_bytes(&ring_to_u32(r)));
        }
        out.extend_from_slice(&u32s_to_le_bytes(&ring_to_u32(&self.t_star)));
        out.extend_from_slice(&u32s_to_le_bytes(&ring_to_u32(&self.q_star)));
        out
    }

    /// Parses a proof; `None` on wrong length.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let total = (N_COMMIT + M_VARS + 2) * D * 4;
        if bytes.len() != total {
            return None;
        }
        let mut pos = 0usize;
        let mut take = |n: usize| -> Vec<Z2Ring> {
            let mut rows = Vec::with_capacity(n);
            for _ in 0..n {
                let mut coeffs = [0u32; D];
                for c in &mut coeffs {
                    *c = u32::from_le_bytes(bytes[pos..pos + 4].try_into().expect("4 bytes"));
                    pos += 4;
                }
                rows.push(ring_from_u32(&coeffs));
            }
            rows
        };
        let d = take(N_COMMIT);
        let z_prime = take(M_VARS);
        let t_star = take(1).remove(0);
        let q_star = take(1).remove(0);
        Some(Self {
            d,
            z_prime,
            t_star,
            q_star,
        })
    }
}

/// FS challenges for an instance+commitment pair: the ring challenge `C`
/// and the gate-combination challenge `γ`.
///
/// `C = X − a` with the scalar `a` forced **odd** — a genuine non-unit of
/// `Z_{2^32}[X]/(X^64+1)` (see the module-level soundness notes: the
/// monomial `X` alone is always a unit, which would make the verifier
/// equation vacuous).
pub(crate) fn challenges(
    key_seed: &[u8; 32],
    r1cs_seed: &[u8; 32],
    c: &[Z2Ring],
    d: &[Z2Ring],
) -> (Z2Ring, Z2Ring) {
    let mut tr = Transcript::<Shake128Xof>::new(b"lattice-algebra/Z2/batched-open");
    tr.absorb(b"key", key_seed);
    tr.absorb(b"r1cs", r1cs_seed);
    absorb_rings(&mut tr, b"c", c);
    absorb_rings(&mut tr, b"d", d);
    let seed = tr.challenge_bytes(64);
    // C = X − a with a odd: a true non-unit (see the module soundness notes).
    let x = nonunit_linear_poly::<Z2Coeff, Shake128Xof, D>(
        &mut crate::foundation::fs::seed_stream(b"X", &seed),
    );
    let gamma = uniform_ring_from_seed::<Z2Coeff, D>(b"gamma", &seed);
    (x, gamma)
}

/// Per-gate masked constraint terms on the honest witness and mask:
/// `m_k = 2(A_k·z)(A_k·y) − U_k·y_sel` and `q_k = (A_k·y)²`.
pub(crate) fn masked_constraint_terms(
    r1cs: &ToyR1cs,
    z: &[Z2Ring],
    y: &[Z2Ring],
) -> (Vec<Z2Ring>, Vec<Z2Ring>) {
    map_over_gates(r1cs, |k, row| {
        let mut az = Z2Ring::zero();
        let mut ay = Z2Ring::zero();
        for (j, coeff) in &row.terms {
            az += z2_mul(coeff, &z[*j]);
            ay += z2_mul(coeff, &y[*j]);
        }
        let term_m = z2_mul(&az, &ay) + z2_mul(&ay, &az) - z2_mul(&r1cs.u[k], &y[r1cs.sel[k]]);
        (term_m, z2_mul(&ay, &ay))
    })
    .into_iter()
    .unzip()
}

/// Verifier-side per-gate residuals on the revealed response:
/// `R_k = (A_k·z')² − U_k·z'_{sel}`.
/// Per-gate quadratic products `q_k = (A_k·z)∘(A_k·z)` — the committed
/// quantity of the folding layer (Nova's `q`).
pub fn quadratic_products(r1cs: &ToyR1cs, zp: &[Z2Ring]) -> Vec<Z2Ring> {
    map_over_gates(r1cs, |_k, row| {
        let mut az = Z2Ring::zero();
        for (j, coeff) in &row.terms {
            az += z2_mul(coeff, &zp[*j]);
        }
        z2_mul(&az, &az)
    })
}

/// The per-gate selected variable index (`sel_k`).
pub fn gate_sel(k: usize, r1cs: &ToyR1cs) -> usize {
    r1cs.sel[k]
}

/// Evaluates the per-gate constraint residuals `A·z ∘ B·z − C·z` over the
/// witness `zp` (non-zero entries are the constraints the opening must
/// account for).
pub fn constraint_residuals(r1cs: &ToyR1cs, zp: &[Z2Ring]) -> Vec<Z2Ring> {
    map_over_gates(r1cs, |k, row| {
        let mut az = Z2Ring::zero();
        for (j, coeff) in &row.terms {
            az += z2_mul(coeff, &zp[*j]);
        }
        z2_mul(&az, &az) - z2_mul(&r1cs.u[k], &zp[r1cs.sel[k]])
    })
}

/// Random linear combination `Σ γ^k · v_k` (Horner).
pub(crate) fn ring_combine(v: &[Z2Ring], gamma: &Z2Ring) -> Z2Ring {
    let mut acc = Z2Ring::zero();
    for v_k in v.iter().rev() {
        acc = z2_mul(&acc, gamma) + v_k.clone();
    }
    acc
}

/// Runs the full prover: returns the commitment `c` and the proof.
pub fn prove(
    key: &Z2CommitKey,
    key_seed: &[u8; 32],
    r1cs_seed: &[u8; 32],
    r1cs: &ToyR1cs,
    z: &[Z2Ring],
    randomness: &[u8; 32],
) -> (Vec<Z2Ring>, Z2Proof) {
    debug_assert_eq!(z.len(), M_VARS);
    let c = key.commit(z);

    // deterministic mask; retry with a re-seeded mask if the (statistically
    // unavoidable) linear-consistency pre-check fails — retained for API
    // stability even though the linear check is exact here.
    let rng_seed = *randomness;
    {
        let y = uniform_vec_from_seed::<Z2Coeff, D>(b"mask", &rng_seed, M_VARS);
        let d = key.commit(&y);
        // challenges derived AFTER committing (c, d)
        let (x, gamma) = challenges(key_seed, r1cs_seed, &c, &d);
        // z' = z + X·y
        let z_prime: Vec<Z2Ring> = z
            .iter()
            .zip(&y)
            .map(|(zi, yi)| zi.clone() + z2_mul(&x, yi))
            .collect();
        let (m, q) = masked_constraint_terms(r1cs, z, &y);
        let t_star = ring_combine(&m, &gamma);
        let q_star = ring_combine(&q, &gamma);
        (
            c,
            Z2Proof {
                d,
                z_prime,
                t_star,
                q_star,
            },
        )
    }
}

/// Verifies a batched-opening proof against instance + commitment.
pub fn verify(
    key: &Z2CommitKey,
    key_seed: &[u8; 32],
    r1cs_seed: &[u8; 32],
    r1cs: &ToyR1cs,
    c: &[Z2Ring],
    proof: &Z2Proof,
) -> bool {
    if proof.d.len() != N_COMMIT || proof.z_prime.len() != M_VARS {
        return false;
    }
    let (x, gamma) = challenges(key_seed, r1cs_seed, c, &proof.d);

    // 1. binding link: A_com·z' == c + X·d
    let azp = key.commit(&proof.z_prime);
    for i in 0..N_COMMIT {
        let rhs = c[i].clone() + z2_mul(&x, &proof.d[i]);
        if ring_to_u32(&azp[i]) != ring_to_u32(&rhs) {
            #[cfg(test)]
            std::eprintln!("verify: linear link failed at row {i}");
            return false;
        }
    }

    // 2. masked constraint consistency:
    //    Σ γ^k R_k == X·t* + X²·q*,  R_k = (A_k·z')² − U_k·z'_sel
    let residuals = constraint_residuals(r1cs, &proof.z_prime);
    let r_comb = ring_combine(&residuals, &gamma);
    let x2 = z2_mul(&x, &x);
    let rhs_comb = z2_mul(&x, &proof.t_star) + z2_mul(&x2, &proof.q_star);
    if ring_to_u32(&r_comb) != ring_to_u32(&rhs_comb) {
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::println;

    use crate::instance::r1cs::gen_toy_instance;
    use algebra::crypto::xof::Xof;

    fn instance_and_witness() -> (ToyR1cs, Vec<Z2Ring>) {
        gen_toy_instance(b"z2-instance-00000000000000000000", 512, 2)
    }

    fn instance_and_witness_10k() -> (ToyR1cs, Vec<Z2Ring>) {
        gen_toy_instance(b"z2-instance-00000000000000000000", 10_000, 2)
    }

    #[test]
    fn batched_opening_end_to_end_and_size() {
        let (r1cs, z) = instance_and_witness_10k();
        assert_eq!(r1cs.a.len(), 10_000);
        assert!(r1cs.is_satisfied(&z));

        let mut key_seed = [0u8; 32];
        key_seed[..13].copy_from_slice(b"z2-commit-key");

        let key = Z2CommitKey::setup(&key_seed);
        let (c, proof) = prove(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &z,
            &[9u8; 32],
        );

        // size gate: ≤ 10 KB
        assert!(
            proof.encoded_len() <= 10_240,
            "proof too large: {}",
            proof.encoded_len()
        );

        assert!(verify(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &c,
            &proof
        ));

        // wire roundtrip
        let bytes = proof.to_bytes();
        assert_eq!(bytes.len(), proof.encoded_len());
        assert_eq!(Z2Proof::from_bytes(&bytes).unwrap(), proof);
    }

    #[test]
    fn rejects_tampered_response() {
        let (r1cs, z) = instance_and_witness();
        let mut key_seed = [0u8; 32];
        key_seed[..13].copy_from_slice(b"z2-commit-key");
        let key = Z2CommitKey::setup(&key_seed);
        let (c, mut proof) = prove(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &z,
            &[9u8; 32],
        );

        // perturb one coefficient of the response
        let mut coeffs = ring_to_u32(&proof.z_prime[0]);
        coeffs[0] ^= 1;
        proof.z_prime[0] = ring_from_u32(&coeffs);
        assert!(!verify(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &c,
            &proof
        ));

        // restore response, perturb the mask commitment instead: the
        // binding link A·z' == c + X·d must fail
        let mut proof2 = proof;
        proof2.d[0] = ring_from_u32(&{
            let mut c = ring_to_u32(&proof2.d[0]);
            c[3] ^= 1;
            c
        });
        assert!(!verify(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &c,
            &proof2
        ));
    }

    #[test]
    fn rejects_wrong_instance() {
        let (r1cs, z) = instance_and_witness();
        let mut key_seed = [0u8; 32];
        key_seed[..13].copy_from_slice(b"z2-commit-key");
        let key = Z2CommitKey::setup(&key_seed);
        let (c, proof) = prove(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &z,
            &[9u8; 32],
        );

        // different constraint system
        let (r1cs2, _z2) = gen_toy_instance(b"z2-instance-20000000000000000000", 512, 2);
        assert!(!verify(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs2,
            &c,
            &proof
        ));
    }

    #[test]
    fn extractor_binding_link_recovered() {
        // Two accepting transcripts with the same commitment `c` but
        // different masks (adversarial forking simulation). Subtracting the
        // two binding links eliminates `c` and yields the extractor's
        // relaxed relation on public data only.
        let (r1cs, z) = instance_and_witness();
        let mut key_seed = [0u8; 32];
        key_seed[..13].copy_from_slice(b"z2-commit-key");
        let key = Z2CommitKey::setup(&key_seed);
        let c = key.commit(&z);

        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"mask-a00000000000000000000000000");
        let y1 = mask_from(&mut xof);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"mask-b00000000000000000000000000");
        let y2 = mask_from(&mut xof);
        let d1 = key.commit(&y1);
        let d2 = key.commit(&y2);
        let (x1, g1) = challenges(&key_seed, b"z2-r1cs0000000000000000000000000", &c, &d1);
        let (x2, g2) = challenges(&key_seed, b"z2-r1cs0000000000000000000000000", &c, &d2);

        let zp1: Vec<Z2Ring> = z
            .iter()
            .zip(&y1)
            .map(|(a, b)| a.clone() + z2_mul(&x1, b))
            .collect();
        let zp2: Vec<Z2Ring> = z
            .iter()
            .zip(&y2)
            .map(|(a, b)| a.clone() + z2_mul(&x2, b))
            .collect();

        // both transcripts are accepting
        let (m1, q1v) = masked_constraint_terms(&r1cs, &z, &y1);
        let (m2, q2v) = masked_constraint_terms(&r1cs, &z, &y2);
        let p1 = Z2Proof {
            d: d1.clone(),
            z_prime: zp1.clone(),
            t_star: ring_combine(&m1, &g1),
            q_star: ring_combine(&q1v, &g1),
        };
        let p2 = Z2Proof {
            d: d2.clone(),
            z_prime: zp2.clone(),
            t_star: ring_combine(&m2, &g2),
            q_star: ring_combine(&q2v, &g2),
        };
        assert!(verify(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &c,
            &p1
        ));
        assert!(verify(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &c,
            &p2
        ));

        // extractor relation: A·(z'1 − z'2) == X1·d1 − X2·d2  (c eliminated)
        let dz: Vec<Z2Ring> = zp1
            .iter()
            .zip(&zp2)
            .map(|(a, b)| a.clone() - b.clone())
            .collect();
        let lhs = key.commit(&dz);
        let dx: Vec<Z2Ring> = d1
            .iter()
            .zip(&d2)
            .map(|(a, b)| x1.clone() * a.clone() - x2.clone() * b.clone())
            .collect();
        let folded: Vec<Z2Ring> = lhs
            .iter()
            .zip(&dx)
            .map(|(l, r)| l.clone() - r.clone())
            .collect();
        let zero: Vec<Z2Ring> = vec![Z2Ring::zero(); N_COMMIT];
        assert_eq!(folded, zero);

        // honest-case refinement: dz == (X1 − X2)·y
        let dx2 = sub_ring(&x1, &x2);
        let expected: Vec<Z2Ring> = y1
            .iter()
            .zip(&y2)
            .map(|(a, b)| dx2.clone() * a.clone() + x2.clone() * (a.clone() - b.clone()))
            .collect();
        assert_eq!(dz, expected);
    }

    fn sub_ring(a: &Z2Ring, b: &Z2Ring) -> Z2Ring {
        a.clone() - b.clone()
    }

    fn mask_from(xof: &mut Shake128Xof) -> Vec<Z2Ring> {
        (0..M_VARS)
            .map(|_| {
                let mut coeffs = [0u32; D];
                let mut buf = [0u8; 4];
                for c in &mut coeffs {
                    xof.squeeze(&mut buf);
                    *c = u32::from_le_bytes(buf);
                }
                ring_from_u32(&coeffs)
            })
            .collect()
    }

    /// Soundness regression: a prover committing to a FALSE witness can
    /// satisfy the binding link (z' = z_fake + C·y with c = A_com·z_fake)
    /// and — before the non-unit challenge fix — could always absorb the
    /// residual junk into `t*` because the challenge `X` was a unit. With
    /// the non-unit challenge `C = X − a` (a odd) the crafted terms must
    /// make `Σγ^k R_k(z') ∈ C·R`, which a forged statement does not.
    #[test]
    fn forged_statement_rejected_despite_binding_link() {
        let (r1cs, _z_true) = instance_and_witness();
        // A witness that does NOT satisfy the gates.
        let mut z_fake = _z_true.clone();
        z_fake[0] = z_fake[0].clone() + Z2Ring::one();
        assert!(!r1cs.is_satisfied(&z_fake));

        let mut key_seed = [0u8; 32];
        key_seed[..13].copy_from_slice(b"z2-commit-key");
        let key = Z2CommitKey::setup(&key_seed);
        let c = key.commit(&z_fake);
        let r1cs_seed = b"z2-r1cs0000000000000000000000000";

        // Grind several masks: each gives a fresh challenge; the old
        // unit-challenge proof passed for *every* mask.
        let mut accepted = 0;
        for trial in 0u8..16 {
            let mut xof = Shake128Xof::new(&[]);
            xof.absorb(b"forge");
            xof.absorb(&[trial; 32]);
            let y = mask_from(&mut xof);
            let d = key.commit(&y);
            let (chall, gamma) = challenges(&key_seed, r1cs_seed, &c, &d);
            let z_prime: Vec<Z2Ring> = z_fake
                .iter()
                .zip(&y)
                .map(|(zf, yi)| zf.clone() + chall.clone() * yi.clone())
                .collect();
            // Craft t*, q* with the honest-formula shape for the fake mask.
            let (m, q) = masked_constraint_terms(&r1cs, &z_fake, &y);
            let proof = Z2Proof {
                d: d.clone(),
                z_prime: z_prime.clone(),
                t_star: ring_combine(&m, &gamma),
                q_star: ring_combine(&q, &gamma),
            };
            if verify(&key, &key_seed, r1cs_seed, &r1cs, &c, &proof) {
                accepted += 1;
            }
        }
        assert_eq!(
            accepted, 0,
            "a forged statement must not verify (unit-challenge regression)"
        );
    }

    #[test]
    fn z2_z3_crosscheck_and_benchmarks() {
        use crate::instance::r1cs::gen_toy_instance;
        use crate::sumcheck::{prove as sc_prove, verify as sc_verify, FsChallenger};

        const GATES: usize = 1024; // 2^10: matches the sumcheck arity

        // The SAME toy instance and witness feed both proof paths.
        let (r1cs, z) = gen_toy_instance(b"crosscheck-000000000000000000000", GATES, M_VARS);
        assert!(r1cs.is_satisfied(&z));
        let mut key_seed = [0u8; 32];
        key_seed[..13].copy_from_slice(b"z2-commit-key");
        let key = Z2CommitKey::setup(&key_seed);

        // --- Z2: batched opening ---
        let t0 = std::time::Instant::now();
        let (c, proof) = prove(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &z,
            &[9u8; 32],
        );
        let z2_prove_time = t0.elapsed();
        let z2_size = proof.encoded_len();
        let t1 = std::time::Instant::now();
        let ok_z2 = verify(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &c,
            &proof,
        );
        let z2_verify_time = t1.elapsed();
        assert!(ok_z2);

        // --- Z3: ring-sumcheck over the response's gate-residual table ---
        // The response is revealed by Z2, so the residual table is public;
        // the sumcheck proves Σ residuals == claimed with round-by-round
        // folding (the GreyHound-style alternative to Z2's γ-combination).
        let table = constraint_residuals(&r1cs, &proof.z_prime);
        let claimed: Z2Ring = table.iter().fold(
            Z2Ring {
                inner: algebra::poly::UniPolynomial::zero(),
            },
            |a, b| a + b.clone(),
        );

        let mut ch_prove = FsChallenger::<Shake128Xof, Z2Ring>::new(b"z3-sumcheck");
        let t2 = std::time::Instant::now();
        let sc = sc_prove::<Z2Ring, 10>(&table, &mut ch_prove);
        let z3_prove_time = t2.elapsed();
        let z3_size = 10 * 2 * D * 4 + D * 4; // 10 rounds × 2 ring elems + final eval

        let mut ch_verify = FsChallenger::<Shake128Xof, Z2Ring>::new(b"z3-sumcheck");
        let t3 = std::time::Instant::now();
        let out = sc_verify::<Z2Ring, 10>(&sc, claimed.clone(), &mut ch_verify);
        let z3_verify_time = t3.elapsed();
        // Close the soundness loop: the sumcheck reduces the sum claim to
        // `T(r) = final_eval` — the verifier evaluates the public table at
        // the derived challenge point itself.
        let (challenges, final_eval) = out.expect("honest sumcheck must verify");
        let mut folded = table.clone();
        for r in &challenges {
            let half = folded.len() / 2;
            for j in 0..half {
                let lo = folded[j].clone();
                let hi = folded[j + half].clone();
                folded[j] = lo.clone() + r.clone() * (hi - lo);
            }
            folded.truncate(half);
        }
        assert_eq!(
            folded[0], final_eval,
            "sumcheck must evaluate the table at r"
        );
        // The claimed sum itself must match the independently summed table.
        let true_sum: Z2Ring = table.iter().fold(Z2Ring::zero(), |a, b| a + b.clone());
        assert_eq!(claimed, true_sum, "claimed sum must equal the table sum");

        println!("Z2 (batched opening): size={z2_size}B prove={z2_prove_time:?} verify={z2_verify_time:?}");
        println!("Z3 (sumcheck):        size={z3_size}B prove={z3_prove_time:?} verify={z3_verify_time:?}");

        assert_eq!(z2_size, 3072, "Z2 proof must stay at 3072 B");
        assert_eq!(z3_size, 5376, "Z3 sumcheck transcript must stay at 5376 B");
    }

    /// Pins the exact semantics of the masked-consistency check: the
    /// coefficient-sum map `χ(f) = Σ f_i (mod 2)` is a well-defined
    /// homomorphism `R → F_2` (it kills `2` and `X^64 + 1`), `C` lies in
    /// its kernel, and the honest combined residual satisfies it — while a
    /// false residual's parity is ~balanced (the ½-per-grind soundness
    /// loss that the LaBRADOR recursion closes).
    #[test]
    fn verifier_equation_is_single_bit_parity() {
        let chi = |f: &[u32; D]| -> u32 { f.iter().map(|v| v & 1).sum::<u32>() & 1 };

        let (r1cs, z) = instance_and_witness();
        let mut key_seed = [0u8; 32];
        key_seed[..13].copy_from_slice(b"z2-commit-key");
        let key = Z2CommitKey::setup(&key_seed);
        let (c, proof) = prove(
            &key,
            &key_seed,
            b"z2-r1cs0000000000000000000000000",
            &r1cs,
            &z,
            &[9u8; 32],
        );
        let (challenge, gamma) =
            challenges(&key_seed, b"z2-r1cs0000000000000000000000000", &c, &proof.d);

        // C lies in the kernel: χ(C) = χ(X − a) = (1 − a) mod 2 = 0
        assert_eq!(chi(&ring_to_u32(&challenge)), 0);

        // the honest combined residual satisfies the verifier equation,
        // hence lies in C·R ⊆ ker χ
        let residuals = constraint_residuals(&r1cs, &proof.z_prime);
        let combined = ring_combine(&residuals, &gamma);
        assert_eq!(chi(&ring_to_u32(&combined)), 0);

        // The single-bit loss, pinned precisely. χ is multiplicative, so
        // χ(Σ_k γ^k·R_k) = χ(R_0) + χ(γ)·Σ_{k≥1} χ(R_k): the whole
        // constraint check reduces to two F_2-linear functionals of the
        // witness's coefficient-sum vector. For this instance's challenge
        // χ(γ) = 0, so only gate 0's parity is visible — perturbing gate 0
        // flips the bit, perturbing any later gate does not. A false prover
        // that satisfies the parity conditions on its witness passes
        // deterministically; otherwise it grinds at ~½ per attempt. This is
        // exactly the slack the LaBRADOR recursion (Z2 milestone) closes.
        assert_eq!(chi(&ring_to_u32(&gamma)), 0, "this instance: χ(γ) = 0");
        let one = ring_from_u32(&{
            let mut c = [0u32; D];
            c[0] = 1;
            c
        });
        let mut flip_gate0 = residuals.clone();
        flip_gate0[0] = flip_gate0[0].clone() + one.clone();
        assert_eq!(
            chi(&ring_to_u32(&ring_combine(&flip_gate0, &gamma))),
            1,
            "gate 0's parity is the certified bit"
        );
        let mut flip_gate1 = residuals.clone();
        flip_gate1[1] = flip_gate1[1].clone() + one;
        assert_eq!(
            chi(&ring_to_u32(&ring_combine(&flip_gate1, &gamma))),
            0,
            "gates k ≥ 1 are invisible when χ(γ) = 0"
        );
    }

    /// The recursive mode's headline property: a false witness is rejected
    /// **deterministically** — the masked terms are pinned to their
    /// pre-challenge commitments, so the compact mode's ½-per-grind
    /// adaptivity gap is gone (contrast
    /// `forged_statement_rejected_despite_binding_link`).
    #[test]
    fn recursive_mode_rejects_false_witness_deterministically() {
        let (r1cs, z_true) = instance_and_witness();
        let mut z_fake = z_true.clone();
        z_fake[0] = z_fake[0].clone() + Z2Ring::one();
        assert!(!r1cs.is_satisfied(&z_fake));

        let mut key_seed = [0u8; 32];
        key_seed[..13].copy_from_slice(b"z2-commit-key");
        let key = Z2CommitKey::setup(&key_seed);
        let r1cs_seed = b"z2-r1cs0000000000000000000000000";

        // the strongest possible cheat in this mode: the honest-formula
        // masked terms for the false witness (any other choice fails the
        // A₂ links even earlier)
        let mut accepted = 0;
        for trial in 0..8u8 {
            let mut rnd = [0u8; 32];
            rnd[..1].copy_from_slice(&[trial]);
            let (c, proof) = prove_recursive(&key, &key_seed, r1cs_seed, &r1cs, &z_fake, &rnd);
            if verify_recursive(&key, &key_seed, r1cs_seed, &r1cs, &c, &proof) {
                accepted += 1;
            }
        }
        assert_eq!(accepted, 0, "recursive mode must reject the false witness");

        // the honest witness passes (completeness)
        let (c, proof) = prove_recursive(&key, &key_seed, r1cs_seed, &r1cs, &z_true, &[9u8; 32]);
        assert!(verify_recursive(
            &key, &key_seed, r1cs_seed, &r1cs, &c, &proof
        ));
    }

    #[test]
    fn recursive_mode_rejects_tampered_masked_terms() {
        let (r1cs, z) = instance_and_witness();
        let mut key_seed = [0u8; 32];
        key_seed[..13].copy_from_slice(b"z2-commit-key");
        let key = Z2CommitKey::setup(&key_seed);
        let r1cs_seed = b"z2-r1cs0000000000000000000000000";
        let (c, mut proof) = prove_recursive(&key, &key_seed, r1cs_seed, &r1cs, &z, &[9u8; 32]);

        // shift one revealed masked term: the A₂ link must fail
        let mut coeffs = ring_to_u32(&proof.masked[3]);
        coeffs[0] ^= 1;
        proof.masked[3] = ring_from_u32(&coeffs);
        assert!(!verify_recursive(
            &key, &key_seed, r1cs_seed, &r1cs, &c, &proof
        ));
    }
}
