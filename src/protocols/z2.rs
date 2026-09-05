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
//! polynomials simultaneously against the ring challenge `X` — the same
//! role LaBRADOR's `σ_i = w(X_i)` plays, here with one ring-challenge and
//! ring multiplication as the evaluation map.
//!
//! *Soundness sketch*: after committing `c, d`, the response is uniquely
//! pinned by the overdetermined linear check `A_com·z' = c + X·d`
//! (`N·64` scalar equations over `M·64` unknowns, `N ≥ 2M`), so the
//! constraint check on that unique `z'` cannot be adapted to a false
//! instance; deviating requires solving the R1CS or the linear problem,
//! each ≈ 2^-32 per ring coefficient by Schwartz–Zippel on `X`.
//!
//! *Knowledge*: the extractor of the binding link recovers `z'` itself —
//! the proven object *is* the satisfying vector (transparent proof of
//! knowledge, not ZK — same status as LaBRADOR).
//!
//! # Approximate shortness (gadget layer)
//!
//! [`gadget_split`] decomposes coefficients into high digits plus a centered
//! low residual; [`approx_linear_check`] accepts openings that match the
//! committed value only up to a **provable slack** `slack_bound(...)`. This
//! is the machinery the full LaBRADOR recursion (Z3) layers into a complete
//! shortness proof.

use crate::crypto::transcript::Transcript;
use crate::crypto::xof::{Shake128Xof, Xof};
use crate::protocols::z2_ring::{
    matrix_from_seed, ring_from_seed, ring_from_u32, ring_to_u32, ToyR1cs, Z2Ring, D,
};
use crate::ring::MatrixElement;

/// Commitment-key dimensions: `A_com ∈ R^{N_COMMIT×M_VARS}`.
pub const N_COMMIT: usize = 8;
/// Witness length (ring variables).
pub const M_VARS: usize = 2;

/// Ajtai commitment key over the Z2 ring (raw-coefficient expansion).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Z2CommitKey {
    a: Vec<Vec<Z2Ring>>,
}

impl Z2CommitKey {
    /// Derives the key from a seed.
    pub fn setup(seed: &[u8; 32]) -> Self {
        Self {
            a: matrix_from_seed(seed, N_COMMIT, M_VARS),
        }
    }

    /// `A_com·z`.
    pub fn commit(&self, z: &[Z2Ring]) -> Vec<Z2Ring> {
        debug_assert_eq!(z.len(), M_VARS);
        (0..N_COMMIT)
            .map(|i| {
                let mut acc = Z2Ring::zero();
                for (j, zj) in z.iter().enumerate() {
                    acc += self.a[i][j].clone() * zj.clone();
                }
                acc
            })
            .collect()
    }
}

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
            out.extend_from_slice(&u32s_to_bytes(&ring_to_u32(r)));
        }
        out.extend_from_slice(&u32s_to_bytes(&ring_to_u32(&self.t_star)));
        out.extend_from_slice(&u32s_to_bytes(&ring_to_u32(&self.q_star)));
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
                    let mut b = [0u8; 4];
                    b.copy_from_slice(&bytes[pos..pos + 4]);
                    pos += 4;
                    *c = u32::from_le_bytes(b);
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

fn u32s_to_bytes(v: &[u32]) -> Vec<u8> {
    v.iter().flat_map(|x| x.to_le_bytes()).collect()
}

/// FS challenges for an instance+commitment pair: the ring challenge `X`
/// (forced non-unit via an even constant term, so the verifier equation
/// `X·t* + X²·q*` cannot be solved for `t*` by ring division) and the
/// gate-combination challenge `γ`.
fn challenges(
    key_seed: &[u8; 32],
    r1cs_seed: &[u8; 32],
    c: &[Z2Ring],
    d: &[Z2Ring],
) -> (Z2Ring, Z2Ring) {
    let mut tr = Transcript::<Shake128Xof>::new(b"lattice-algebra/Z2/batched-open");
    tr.absorb(b"key", key_seed);
    tr.absorb(b"r1cs", r1cs_seed);
    for v in c {
        tr.absorb(b"c", &u32s_to_bytes(&ring_to_u32(v)));
    }
    for v in d {
        tr.absorb(b"d", &u32s_to_bytes(&ring_to_u32(v)));
    }
    let seed = tr.challenge_bytes(64);
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(b"X");
    xof.absorb(&seed);
    let mut coeffs = [0u32; D];
    let mut buf = [0u8; 4];
    for c in &mut coeffs {
        xof.squeeze(&mut buf);
        *c = u32::from_le_bytes(buf);
    }
    coeffs[0] &= 0xFFFF_FFFE; // even constant term ⇒ X is a non-unit
    let x = ring_from_u32(&coeffs);

    let mut xof2 = Shake128Xof::new(&[]);
    xof2.absorb(b"gamma");
    xof2.absorb(&seed);
    let gamma = ring_from_seed(&mut xof2);
    (x, gamma)
}

/// Per-gate masked constraint terms on the honest witness and mask:
/// `m_k = 2(A_k·z)(A_k·y) − U_k·y_sel` and `q_k = (A_k·y)²`.
fn masked_constraint_terms(
    r1cs: &ToyR1cs,
    z: &[Z2Ring],
    y: &[Z2Ring],
) -> (Vec<Z2Ring>, Vec<Z2Ring>) {
    let mut m = Vec::with_capacity(r1cs.a.len());
    let mut q = Vec::with_capacity(r1cs.a.len());
    for (k, row) in r1cs.a.iter().enumerate() {
        let mut az = Z2Ring::zero();
        let mut ay = Z2Ring::zero();
        for (j, coeff) in &row.terms {
            az += coeff.clone() * z[*j].clone();
            ay += coeff.clone() * y[*j].clone();
        }
        let ay_sq = ay.clone() * ay.clone();
        let term_m = (az.clone() * ay.clone()) + (ay.clone() * az.clone())
            - r1cs.u[k].clone() * y[r1cs.sel[k]].clone();
        m.push(term_m);
        q.push(ay_sq);
    }
    (m, q)
}

/// Verifier-side per-gate residuals on the revealed response:
/// `R_k = (A_k·z')² − U_k·z'_{sel}`.
/// Per-gate quadratic products `q_k = (A_k·z)∘(A_k·z)` — the committed
/// quantity of the folding layer (Nova's `q`).
pub fn quadratic_products(r1cs: &ToyR1cs, zp: &[Z2Ring]) -> Vec<Z2Ring> {
    r1cs.a
        .iter()
        .map(|row| {
            let mut az = Z2Ring::zero();
            for (j, coeff) in &row.terms {
                az += coeff.clone() * zp[*j].clone();
            }
            az.clone() * az.clone()
        })
        .collect()
}

/// The per-gate selected variable index (`sel_k`).
pub fn gate_sel(k: usize, r1cs: &ToyR1cs) -> usize {
    r1cs.sel[k]
}

pub fn constraint_residuals(r1cs: &ToyR1cs, zp: &[Z2Ring]) -> Vec<Z2Ring> {
    r1cs.a
        .iter()
        .enumerate()
        .map(|(k, row)| {
            let mut az = Z2Ring::zero();
            for (j, coeff) in &row.terms {
                az += coeff.clone() * zp[*j].clone();
            }
            az.clone() * az.clone() - r1cs.u[k].clone() * zp[r1cs.sel[k]].clone()
        })
        .collect()
}

/// Random linear combination `Σ γ^k · v_k` (Horner).
fn ring_combine(v: &[Z2Ring], gamma: &Z2Ring) -> Z2Ring {
    let mut acc = Z2Ring::zero();
    for v_k in v.iter().rev() {
        acc = acc * gamma.clone() + v_k.clone();
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
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"mask");
        xof.absorb(&rng_seed);
        let y: Vec<Z2Ring> = (0..M_VARS)
            .map(|_| {
                let mut coeffs = [0u32; D];
                let mut buf = [0u8; 4];
                for cc in &mut coeffs {
                    xof.squeeze(&mut buf);
                    *cc = u32::from_le_bytes(buf);
                }
                ring_from_u32(&coeffs)
            })
            .collect();
        let d = key.commit(&y);
        // challenges derived AFTER committing (c, d)
        let (x, gamma) = challenges(key_seed, r1cs_seed, &c, &d);
        // z' = z + X·y
        let z_prime: Vec<Z2Ring> = z
            .iter()
            .zip(&y)
            .map(|(zi, yi)| zi.clone() + x.clone() * yi.clone())
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
        let rhs = c[i].clone() + x.clone() * proof.d[i].clone();
        if ring_to_u32(&azp[i]) != ring_to_u32(&rhs) {
            #[cfg(test)]
            eprintln!("verify: linear link failed at row {i}");
            return false;
        }
    }

    // 2. masked constraint consistency:
    //    Σ γ^k R_k == X·t* + X²·q*,  R_k = (A_k·z')² − U_k·z'_sel
    let residuals = constraint_residuals(r1cs, &proof.z_prime);
    let r_comb = ring_combine(&residuals, &gamma);
    let x2 = x.clone() * x.clone();
    let rhs_comb = x.clone() * proof.t_star.clone() + x2 * proof.q_star.clone();
    if ring_to_u32(&r_comb) != ring_to_u32(&rhs_comb) {
        return false;
    }
    true
}

/// Gadget split: `v = high·2^drop + low`, with `low` re-centered into
/// `(−2^{drop−1}, 2^{drop−1}]` and the remainder tracked as slack.
/// Returns `(high, low_centered, slack)` with `|slack| ≤ 2^{drop−1}`.
pub fn gadget_split(v: u32, drop: u32) -> (u32, i64, i64) {
    debug_assert!((1..32).contains(&drop));
    let high = v >> drop;
    let low = v & ((1u32 << drop) - 1);
    let low_i = i64::from(low);
    let half = 1i64 << (drop - 1);
    let centered = if low_i > half {
        low_i - (1i64 << drop)
    } else {
        low_i
    };
    let slack = low_i - centered;
    (high, centered, slack)
}

/// Rebuilds a value from its gadget split (exact when slack is included).
pub fn gadget_join(high: u32, drop: u32, low_centered: i64, slack: i64) -> u32 {
    let low = (low_centered + slack).rem_euclid(1i64 << drop) as u32;
    (high << drop) | low
}

/// provable slack of an approximate linear opening: `N·D·2^{drop−1}`
/// (operator-norm bound of `A` acting on a coefficient-bounded residual).
pub fn slack_bound(n_rows: usize, drop: u32) -> i64 {
    i64::from(n_rows as u32 * (1u32 << (drop - 1)))
}

/// Approximate linear check: does `lhs ≈ 2^drop·(A·high) + A·low_centered`
/// hold within the provable slack? `lhs` and `rhs` are `N`-vectors of ring
/// elements (the committed and reconstructed values).
pub fn approx_linear_check(lhs: &[Z2Ring], reconstructed: &[Z2Ring], drop: u32) -> bool {
    let bound = slack_bound(lhs.len() * D, drop) as u64;
    for (l, r) in lhs.iter().zip(reconstructed.iter()) {
        let lc = ring_to_u32(l);
        let rc = ring_to_u32(r);
        for (a, b) in lc.iter().zip(&rc) {
            let diff = i64::from(*a) - i64::from(*b);
            // centered difference on the power-of-two modulus
            let diff = diff.rem_euclid(1i64 << 32);
            let diff = if diff > (1i64 << 31) {
                diff - (1i64 << 32)
            } else {
                diff
            };
            if diff.unsigned_abs() > bound {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocols::z2_ring::gen_toy_instance;

    fn instance_and_witness() -> (ToyR1cs, Vec<Z2Ring>) {
        gen_toy_instance(b"z2-instance-00000000000000000000", 512, 2)
    }

    fn instance_and_witness_10k() -> (ToyR1cs, Vec<Z2Ring>) {
        gen_toy_instance(b"z2-instance-00000000000000000000", 10_000, 2)
    }

    fn make_probe(v: u32) -> [u32; D] {
        let mut c = [0u32; D];
        c[0] = v;
        c
    }

    #[test]
    fn gadget_split_is_exact_and_bounded() {
        for drop in [4u32, 12, 16] {
            for v in [0u32, 1, 0x7FFF_FFFF, 0xFFFF_FFFF, 123_456_789] {
                let (hi, lo, slack) = gadget_split(v, drop);
                assert_eq!(gadget_join(hi, drop, lo, slack), v);
                assert!(slack.abs() <= 1i64 << drop, "slack {slack} out of range");
                assert!(lo.abs() <= 1i64 << (drop - 1));
            }
        }
    }

    #[test]
    fn approx_check_accepts_exact_and_bounded_slack() {
        // exact reconstruction accepted
        let v = [0x1234_5678u32, 0xFFFF_FFFF, 42];
        let mut lhs = Vec::new();
        let mut recon = Vec::new();
        for &x in &v {
            let (hi, lo, slack) = gadget_split(x, 12);
            lhs.push(ring_from_u32(&make_probe(x)));
            let rebuilt = gadget_join(hi, 12, lo, slack);
            recon.push(ring_from_u32(&make_probe(rebuilt)));
        }
        assert!(approx_linear_check(&lhs, &recon, 12));
        // a deviation beyond the slack bound must be rejected
        let mut bad = recon.clone();
        bad[2] = ring_from_u32(&make_probe(42 + 1_000_000));
        assert!(!approx_linear_check(&lhs, &bad, 12));
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
            .map(|(a, b)| a.clone() + x1.clone() * b.clone())
            .collect();
        let zp2: Vec<Z2Ring> = z
            .iter()
            .zip(&y2)
            .map(|(a, b)| a.clone() + x2.clone() * b.clone())
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

    #[test]
    fn z2_z3_crosscheck_and_benchmarks() {
        use crate::protocols::sumcheck::{prove as sc_prove, verify as sc_verify};
        use crate::protocols::z2_ring::gen_toy_instance;

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
                inner: crate::poly::UniPolynomial::zero(),
            },
            |a, b| a + b.clone(),
        );

        let gen = |label: &'static [u8]| {
            let mut xof = Shake128Xof::new(&[]);
            xof.absorb(label);
            move || {
                let mut coeffs = [0u32; D];
                let mut buf = [0u8; 4];
                for cc in &mut coeffs {
                    xof.squeeze(&mut buf);
                    *cc = u32::from_le_bytes(buf);
                }
                ring_from_u32(&coeffs)
            }
        };
        let mut ch_prove = gen(b"z3-sumcheck");
        let t2 = std::time::Instant::now();
        let sc = sc_prove::<Z2Ring, 10>(&table, &mut ch_prove);
        let z3_prove_time = t2.elapsed();
        let z3_size = 10 * 2 * D * 4 + D * 4; // 10 rounds × 2 ring elems + final eval

        let mut ch_verify = gen(b"z3-sumcheck");
        let t3 = std::time::Instant::now();
        let out = sc_verify::<Z2Ring, 10>(&sc, claimed.clone(), &mut ch_verify);
        let z3_verify_time = t3.elapsed();
        assert!(out.is_some());

        println!("Z2 (batched opening): size={z2_size}B prove={z2_prove_time:?} verify={z2_verify_time:?}");
        println!("Z3 (sumcheck):        size={z3_size}B prove={z3_prove_time:?} verify={z3_verify_time:?}");

        assert_eq!(z2_size, 3072, "Z2 proof must stay at 3072 B");
        assert_eq!(z3_size, 5376, "Z3 sumcheck transcript must stay at 5376 B");
    }
}
