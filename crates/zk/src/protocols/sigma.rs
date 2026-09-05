//! Lyubashevsky-style approximate-knowledge Σ-protocol over module
//! lattices, compiled to an FS-NIZK (L5, Z1).
//!
//! # Relation (relaxed / approximate knowledge)
//!
//! Instance: commitment key `A ∈ R_q^{K×L}` (from a seed) and `t ∈ R_q^K`.
//! The prover demonstrates knowledge of a short `s` with `t = A·s`
//! (`‖s‖∞ ≤ B_S`). The extracted relation is the relaxed one:
//!
//! ```text
//! A·s_ext = v·t   with  ‖s_ext‖∞ ≤ 2·B_Z,  v sparse, ‖v‖∞ ≤ 2, ‖v‖₁ ≤ 2·TAU
//! ```
//!
//! # Protocol (interactive core, then Fiat–Shamir)
//!
//! ```text
//! prover                              verifier
//! y ← D_y (mask, ‖y‖∞ < B_Y)
//! w = A·y                    --w-->   store w
//!                            <--c--   c ← SampleInBall(τ)   (FS: H(instance‖w))
//! z = y + c·s                --z-->   A·z = w + c·t  and  ‖z‖∞ ≤ B_Z
//! ```
//!
//! # Slack analysis (norm accounting)
//!
//! | quantity | bound | source |
//! | --- | --- | --- |
//! | witness `‖s‖∞` | ≤ B_S = 4 | relation |
//! | mask `‖y‖∞` | < B_Y = 2^19 | centered-uniform sampler |
//! | challenge `‖c‖₁` | = TAU = 39 | sparse ±1 |
//! | `‖c·s‖∞` | ≤ TAU·B_S = 156 | convolution spread |
//! | response `‖z‖∞` | ≤ B_Z = B_Y − TAU·B_S = 524132 | prover rejection loop |
//! | extracted `‖s_ext‖∞ = ‖z−z′‖∞` | ≤ 2·B_Z = 1048264 | forking extractor |
//! | multiplier `‖v‖₁ = ‖c−c′‖₁` | ≤ 2·TAU = 78, `‖v‖∞ ≤ 2` | forking extractor |
//!
//! Soundness: answering a fresh sparse challenge without the witness
//! requires solving the associated Module-SIS instance (short `s_ext` with
//! `A·s_ext = v·t`, small `v`) or guessing the challenge from a space of
//! size ≈ `C(256, τ)·2^τ`. Concrete MSIS parameters must be confirmed with
//! the lattice-estimator before any security level is claimed.
//!
//! Zero-knowledge: the rejection loop on `‖z‖∞` makes the protocol
//! honest-verifier zero-knowledge (HVZK); malicious-verifier ZK and
//! blinding are deferred (Z3).

use crate::protocols::commitment::{CommitmentKey, LatticeCommitment, SisParams};
use algebra::crypto::sampling::{sample_in_ball_signs, sample_rej_bounded, BitStream};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::module::ModuleVector;
use algebra::poly::sparse::SparsePolynomial;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;

const Q: i64 = 8_380_417;

/// Errors surfaced by the protocol (ADR-7: typed rejection, no panics on
/// secret-dependent paths).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofError {
    /// The rejection loop failed too many times (statistically ≈ never).
    RejectionLimit,
    /// Witness exceeds the `B_S` bound.
    WitnessTooLong,
}

/// Ring element from centered coefficients.
fn rq_from_i64<const N: usize>(coeffs: &[i64; N]) -> PolyRing<Zq<8380417>, N> {
    PolyRing::from_coefficients(
        coeffs
            .iter()
            .map(|&c| Zq::<8380417>::new(c.rem_euclid(Q) as u64))
            .collect(),
    )
}

/// Samples one mask polynomial with coefficients in `(−B_Y, B_Y)` via
/// centered-uniform sampling over a dedicated bit stream.
fn sample_mask<P: SisParams, const N: usize>(
    stream: &mut BitStream<'_, impl Xof>,
) -> PolyRing<Zq<8380417>, N> {
    let mut coeffs = [0i64; N];
    for c in &mut coeffs {
        *c = sample_rej_bounded::<Zq<8380417>>(stream, P::B_Y as u32);
    }
    rq_from_i64(&coeffs)
}

/// Derives `(c̃, c)` — the commitment hash and the sparse challenge — from a
/// challenge seed.
fn sample_challenge<P: SisParams, const N: usize>(
    seed: &[u8],
) -> (Vec<u8>, PolyRing<Zq<8380417>, N>) {
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(seed);
    let c_tilde = xof.squeeze_vec(32);
    let mut xof2 = Shake256Xof::new(&[]);
    xof2.absorb(&c_tilde);
    let mut stream = BitStream::new(&mut xof2);
    let signs = sample_in_ball_signs(&mut stream, P::TAU, N);
    let sparse = SparsePolynomial::<Zq<8380417>>::from_sign_vector(&signs, N);
    let c = PolyRing::from_coefficients(sparse.to_coeff_vec());
    (c_tilde, c)
}

/// First prover message: the mask commitment `w = A·y`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaskCommitment<const K: usize, const N: usize> {
    w: ModuleVector<Zq<8380417>, K, N>,
}

impl<const K: usize, const N: usize> MaskCommitment<K, N> {
    /// Borrows the committed mask `w`.
    pub fn w(&self) -> &ModuleVector<Zq<8380417>, K, N> {
        &self.w
    }
}

/// Full Fiat–Shamir proof: mask commitment + response + commitment hash.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof<const K: usize, const L: usize, const N: usize> {
    w: ModuleVector<Zq<8380417>, K, N>,
    z: ModuleVector<Zq<8380417>, L, N>,
    c_tilde: Vec<u8>,
}

/// FS-NIZK verification: `A·z = w + c·t` and `‖z‖∞ ≤ B_Z`.
pub fn fs_verify<P: SisParams, const K: usize, const L: usize, const N: usize>(
    key: &CommitmentKey<P, K, L, N>,
    t: &ModuleVector<Zq<8380417>, K, N>,
    proof: &Proof<K, L, N>,
) -> bool
where
    CommitmentKey<P, K, L, N>:
        LatticeCommitment<Zq<8380417>, K, L, N, Witness = ModuleVector<Zq<8380417>, L, N>>,
{
    let b_z = u64::try_from(P::B_Z).expect("B_Z positive");
    if proof.z.infinity_norm() > b_z {
        return false;
    }
    // Recompute the challenge from the instance + mask commitment.
    let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z1/sigma");
    tr.absorb(b"key", key.seed());
    for p in t.polys() {
        tr.absorb(b"t", &coeff_bytes(&p.coefficients()));
    }
    for p in proof.w.polys() {
        tr.absorb(b"w", &coeff_bytes(&p.coefficients()));
    }
    let seed = tr.challenge_bytes(32);
    let (c_tilde_check, c) = sample_challenge::<P, N>(&seed);
    if c_tilde_check != proof.c_tilde {
        return false;
    }
    // A·z == w + c·t (exact, in the ring).
    let op = algebra::ntt::NttOperatorOptimized::<Zq<8380417>, N>::new();
    let az = key.a_hat().mul_vec_ntt(&proof.z.to_ntt(&op)).from_ntt(&op);
    let ct = t.mul_scalar(&c);
    let rhs = proof.w.clone() + ct;
    az.polys() == rhs.polys()
}

fn coeff_bytes(coeffs: &[Zq<8380417>]) -> Vec<u8> {
    let mut out = Vec::with_capacity(coeffs.len() * 4);
    for c in coeffs {
        out.extend_from_slice(&(c.to_u128() as u32).to_le_bytes());
    }
    out
}

/// One-shot FS-NIZK prover: relaxed knowledge of a short `s` with
/// `t = A·s`. Rejection-samples the mask until the response norm gate
/// holds, re-seeding deterministically per attempt.
pub fn fs_prove<P: SisParams, const K: usize, const L: usize, const N: usize>(
    key: &CommitmentKey<P, K, L, N>,
    s: &ModuleVector<Zq<8380417>, L, N>,
    t: &ModuleVector<Zq<8380417>, K, N>,
    randomness: &[u8; 32],
) -> Result<Proof<K, L, N>, ProofError>
where
    CommitmentKey<P, K, L, N>:
        LatticeCommitment<Zq<8380417>, K, L, N, Witness = ModuleVector<Zq<8380417>, L, N>>,
{
    // Witness bound sanity.
    for p in s.polys() {
        for cc in p.coefficients() {
            if cc.centered().abs() > P::B_S {
                return Err(ProofError::WitnessTooLong);
            }
        }
    }

    let b_z = u64::try_from(P::B_Z).expect("B_Z positive");
    let op = algebra::ntt::NttOperatorOptimized::<Zq<8380417>, N>::new();
    let mut rng_seed = *randomness;

    for _ in 0..128 {
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(b"mask");
        xof.absorb(&rng_seed);
        let mut stream = BitStream::new(&mut xof);
        let y: ModuleVector<Zq<8380417>, L, N> =
            ModuleVector::from_fn(|_| sample_mask::<P, N>(&mut stream));
        let w = key.a_hat().mul_vec_ntt(&y.to_ntt(&op)).from_ntt(&op);

        // FS challenge bound to (key, t, w).
        let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z1/sigma");
        tr.absorb(b"key", key.seed());
        for p in t.polys() {
            tr.absorb(b"t", &coeff_bytes(&p.coefficients()));
        }
        for p in w.polys() {
            tr.absorb(b"w", &coeff_bytes(&p.coefficients()));
        }
        let seed = tr.challenge_bytes(32);
        let (c_tilde, c) = sample_challenge::<P, N>(&seed);

        let z = y.clone() + s.mul_scalar(&c);
        if z.infinity_norm() <= b_z {
            return Ok(Proof { w, z, c_tilde });
        }

        // Deterministic re-seed for the next attempt (rejection sampling).
        let mut x = Shake256Xof::new(&[]);
        x.absorb(&rng_seed);
        x.absorb(b"retry");
        x.squeeze(&mut rng_seed);
    }
    Err(ProofError::RejectionLimit)
}

/// Forking extractor: from two accepting transcripts that share the mask
/// commitment `w` but differ in the challenge, recover the relaxed witness.
///
/// Returns `(s_ext, v)` with `A·s_ext = v·t`, where `s_ext = z1 − z2` and
/// `v = c1 − c2`; norm bounds are documented in the module slack table.
pub fn extract<P: SisParams, const K: usize, const L: usize, const N: usize>(
    z1: &ModuleVector<Zq<8380417>, L, N>,
    z2: &ModuleVector<Zq<8380417>, L, N>,
    c1: &PolyRing<Zq<8380417>, N>,
    c2: &PolyRing<Zq<8380417>, N>,
) -> (ModuleVector<Zq<8380417>, L, N>, PolyRing<Zq<8380417>, N>) {
    (z1.clone() - z2.clone(), c1.clone() - c2.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocols::commitment::{Z1Instance, RING_DIM};

    const K: usize = 8;
    const L: usize = 6;
    type Key = CommitmentKey<Z1Instance, K, L, RING_DIM>;
    type Witness = ModuleVector<Zq<8380417>, L, RING_DIM>;
    type Statement = ModuleVector<Zq<8380417>, K, RING_DIM>;

    fn setup_instance(seed: u8) -> (Key, Witness, Statement) {
        let key: Key = CommitmentKey::setup(&[seed; 32]);
        let mut rows = Vec::new();
        for i in 0..L {
            let mut row = [0i64; RING_DIM];
            for (j, c) in row.iter_mut().enumerate() {
                *c = ((seed as i64 + i as i64 * 5 + j as i64 * 11) % 9) - 4;
            }
            rows.push(row);
        }
        let s = ModuleVector::from_fn(|i| rq_from_i64(&rows[i]));
        let t = key.commit(&s);
        (key, s, t)
    }

    #[test]
    fn honest_prove_verify() {
        let (key, s, t) = setup_instance(9);
        let proof = fs_prove::<Z1Instance, K, L, RING_DIM>(&key, &s, &t, &[0x11u8; 32])
            .expect("prove should succeed");
        assert!(fs_verify::<Z1Instance, K, L, RING_DIM>(&key, &t, &proof));
    }

    #[test]
    fn deterministic_proof() {
        let (key, s, t) = setup_instance(9);
        let p1 = fs_prove::<Z1Instance, K, L, RING_DIM>(&key, &s, &t, &[0x22u8; 32]).unwrap();
        let p2 = fs_prove::<Z1Instance, K, L, RING_DIM>(&key, &s, &t, &[0x22u8; 32]).unwrap();
        assert_eq!(p1, p2);
    }

    #[test]
    fn rejects_wrong_statement() {
        let (key, s, _t) = setup_instance(5);
        let (_k2, _s2, t_other) = setup_instance(6);
        // Proof is bound to (key, t_other); verifying against a different
        // statement must fail.
        let proof = fs_prove::<Z1Instance, K, L, RING_DIM>(&key, &s, &t_other, &[0u8; 32]).unwrap();
        assert!(!fs_verify::<Z1Instance, K, L, RING_DIM>(&key, &_t, &proof));
    }

    #[test]
    fn rejects_tampered_response() {
        let (key, s, t) = setup_instance(5);
        let mut proof =
            fs_prove::<Z1Instance, K, L, RING_DIM>(&key, &s, &t, &[0x33u8; 32]).unwrap();
        // Add a small ring element to one response polynomial: breaks the
        // linear check while (typically) staying inside the norm bound.
        let mut arr = [0i64; RING_DIM];
        arr[0] = 1;
        let perturbed = rq_from_i64(&arr);
        let mut polys = proof.z.polys().clone();
        polys[0] = polys[0].clone() + perturbed;
        proof.z = ModuleVector::new(polys);
        assert!(!fs_verify::<Z1Instance, K, L, RING_DIM>(&key, &t, &proof));
    }

    #[test]
    fn witness_bound_enforced() {
        let (key, _s, t) = setup_instance(7);
        let mut big = [0i64; RING_DIM];
        big[0] = Z1Instance::B_S + 1;
        let mut rows = Vec::new();
        for i in 0..L {
            rows.push(if i == 0 { big } else { [0i64; RING_DIM] });
        }
        let s_bad = ModuleVector::from_fn(|i| rq_from_i64(&rows[i]));
        assert_eq!(
            fs_prove::<Z1Instance, K, L, RING_DIM>(&key, &s_bad, &t, &[0u8; 32]),
            Err(ProofError::WitnessTooLong)
        );
    }

    #[test]
    fn extractor_recovers_relaxed_relation() {
        // Two transcripts sharing the mask commitment with different
        // challenges (adversarial forking simulation): the extractor must
        // output (s_ext, v) with A·s_ext = v·t and the documented norms.
        let (key, s, t) = setup_instance(11);

        let op = algebra::ntt::NttOperatorOptimized::<Zq<8380417>, RING_DIM>::new();
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(b"extractor-mask");
        let mut stream = BitStream::new(&mut xof);
        let y: Witness =
            ModuleVector::from_fn(|_| sample_mask::<Z1Instance, RING_DIM>(&mut stream));
        let w = key.a_hat().mul_vec_ntt(&y.to_ntt(&op)).from_ntt(&op);
        let _ = w;

        let (c_t1, c1) = sample_challenge::<Z1Instance, RING_DIM>(b"challenge-1");
        let (c_t2, c2) = sample_challenge::<Z1Instance, RING_DIM>(b"challenge-2");
        assert_ne!(c1, c2, "distinct challenges required for extraction");
        let _ = (c_t1, c_t2);

        let z1 = y.clone() + s.mul_scalar(&c1);
        let z2 = y.clone() + s.mul_scalar(&c2);

        let (s_ext, v) = extract::<Z1Instance, K, L, RING_DIM>(&z1, &z2, &c1, &c2);

        // Exact relaxed relation: A·s_ext == v·t.
        let lhs = key.commit(&s_ext);
        let rhs = t.mul_scalar(&v);
        assert_eq!(lhs.polys(), rhs.polys(), "A·s_ext must equal v·t");

        // Honest-case refinement: s_ext == v·s exactly.
        let expected = s.mul_scalar(&v);
        assert_eq!(s_ext.polys(), expected.polys());

        // Slack bounds: ‖s_ext‖∞ ≤ 2·B_Z, ‖v‖∞ ≤ 2, ‖v‖₁ ≤ 2·TAU.
        assert!(s_ext.infinity_norm() <= 2 * u64::try_from(Z1Instance::B_Z).unwrap());
        let v_inf = v
            .coefficients()
            .iter()
            .map(|&x| x.centered().abs())
            .max()
            .unwrap();
        let v_l1: i64 = v.coefficients().iter().map(|&x| x.centered().abs()).sum();
        assert!(v_inf <= 2, "‖v‖∞ = {v_inf}");
        assert!(v_l1 <= 2 * i64::from(Z1Instance::TAU), "‖v‖₁ = {v_l1}");
        let _ = w;
    }

    #[test]
    fn challenge_is_sparse() {
        // Statistical soundness comes from the challenge space; assert the
        // challenge shape: exactly TAU non-zero ±1 coefficients.
        let (_, c) = sample_challenge::<Z1Instance, RING_DIM>(b"shape");
        let nonzeros = c
            .coefficients()
            .iter()
            .filter(|&&x| x != Zq::<8380417>::ZERO)
            .count();
        assert_eq!(nonzeros, Z1Instance::TAU as usize);
    }
}
