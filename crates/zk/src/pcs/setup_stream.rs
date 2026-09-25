//! The shared setup vector and its overlapping prefix views (eprint
//! 2026/1983 §4.3, Eq. (65)-(67), Figure 3).
//!
//! Akita does **not** store a matrix per level. Every public matrix — the inner
//! `A`, the outer `B`, the shared opening `D`, and each compression map — is one
//! *prefix* of a single flat coefficient vector `S`, reinterpreted at its own
//! `(n, m, d)`:
//!
//! ```text
//! M[i, j] = sum_{ell < d} S_{((i*m + j)*d + ell)} X^ell        (Eq. 66)
//! ```
//!
//! Three properties make that legal, and all three are what this module
//! guarantees rather than leaving to the caller:
//!
//! * **prefix consistency** — a length-`n` expansion is a prefix of every longer
//!   expansion of the same seed, which is what "smaller instances read shorter
//!   prefixes of the same vector" (below Eq. 65) requires. It holds because each
//!   coefficient is derived from its own flat index, not from a stream position.
//! * **zero coefficient bias** — each `S_i` is drawn by exact rejection, so
//!   `S_i` is uniform on `[0, q)`. §4.3 allows a statistical distance of
//!   `q * 2^-w` with a recorded draw width, but adds that "exact rejection
//!   sampling has zero coefficient bias"; this takes that route, so no
//!   aggregate-bias term ever has to be accounted.
//! * **one seed, many views** — `View` names the shapes the schedule admits, so
//!   the *active prefix* `N_active = max_I n_I m_I d_I` (Eq. 173) and its
//!   power-of-two envelope (Eq. 65) are computed from the same data the matrices
//!   are built from. Those two numbers are the entire cost accounting behind
//!   setup offloading (§9.2: offload only while the scan is the expensive part),
//!   and they cannot drift from the matrices they describe.
//!
//! Layering: `pcs` support, parallel to [`crate::pcs::key`]; the difference is
//! that [`crate::pcs::key::RingMatrixKey::setup`] derives *per entry*, which
//! gives independent matrices, while this module derives *per flat index*,
//! which is the overlapping-prefix structure Akita's security proof is stated
//! for (§10.2: "The public key distribution is the stacked-prefix distribution
//! of Section 4.3, not a product distribution over independent matrices").
//!
//! # What the paper fixes here, verbatim
//!
//! §4.3 "Setup" (p. 45): "We construct all of them from one public vector
//! `S = (S_0, …, S_{N_setup−1}) ∈ F_q^{N_setup}`, expanded from a public seed.
//! To obtain a particular matrix, we take the required number of entries from
//! the beginning of this vector and arrange them into ring elements." The
//! matrix inventory (p. 46, Table 3) is five roles — `A` inner folding, `B`
//! outer commitment, `D` partial evaluation, and the two compression chains
//! `F`, `H` — each with **its own** ring dimension `d_A, d_B, d_D, d_F, d_H`
//! and its own `(n, m)` shape, which is exactly what a single const-generic
//! `pcs` instance cannot express (gap G1 in `docs/open-milestones.md`).
//! [`View`] carries `dim` as a *value*, so this layer already admits per-role
//! dimensions; what does not is the protocol layer above it.

use crate::pcs::key::RingMatrixKey;
use algebra::crypto::sampling::BitStream;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;
use alloc::vec::Vec;

/// Domain-separation label for the setup-expansion namespace (§4.3, "S_i :=
/// XOF_q(seed; setup, i)"). Independent from the Fiat-Shamir namespace, which is
/// what lets the query bound `Qmax` exclude setup recomputations.
const SETUP_DOMAIN: &[u8] = b"lattice-algebra/akita/setup";

/// The seed-expanded flat setup vector `S`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetupStream {
    seed: [u8; 32],
}

impl SetupStream {
    /// Binds the stream to the public 256-bit seed.
    pub fn new(seed: &[u8; 32]) -> Self {
        Self { seed: *seed }
    }

    /// The public seed everything expands from.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// `S_index`, uniform on `[0, q)` by exact rejection.
    ///
    /// Deriving from the index rather than from a shared byte stream is what
    /// makes every prefix of an expansion a prefix of a longer one.
    ///
    /// # Panics
    /// If the index is out of the `u64` range the encoding supports.
    pub fn coeff<R: Ring>(&self, index: usize) -> R {
        let mut xof = Shake256Xof::new(SETUP_DOMAIN);
        xof.absorb(&self.seed);
        xof.absorb(&(index as u64).to_le_bytes());
        let mut stream = BitStream::new(&mut xof);
        let bits = bit_width(R::MODULUS);
        let mut raw = stream.read_bits(bits) as u128;
        while raw >= u128::from(R::MODULUS) {
            raw = stream.read_bits(bits) as u128;
        }
        R::from(raw as u64)
    }

    /// `S[0..count]`.
    pub fn coeffs<R: Ring>(&self, count: usize) -> Vec<R> {
        (0..count).map(|i| self.coeff::<R>(i)).collect()
    }

    /// The `(rows, cols, D)` prefix view of `S` as a matrix over
    /// `R_{q,D}` (Eq. 66): `rows * cols * D` coefficients, row-major, each ring
    /// element's `D` coefficients consecutive.
    ///
    /// # Panics
    /// If `rows` or `cols` is zero.
    pub fn matrix<R: Ring, const D: usize>(&self, rows: usize, cols: usize) -> RingMatrixKey<R, D> {
        assert!(rows > 0 && cols > 0, "a matrix view must be non-empty");
        let flat = self.coeffs::<R>(rows * cols * D);
        let entries = flat
            .chunks(D)
            .map(|c| PolyRing::<R, D>::from_coefficients(c.to_vec()))
            .collect();
        RingMatrixKey::from_entries(rows, cols, entries)
    }

    /// The longest flat prefix an admitted view reads: `max_I n_I m_I d_I`
    /// (Eq. 173's `N_active`).
    pub fn active_prefix(views: &[View]) -> usize {
        views
            .iter()
            .map(|v| v.rows * v.cols * v.dim)
            .max()
            .unwrap_or(0)
    }

    /// The provisioned envelope `N_setup = 2^ceil(log2 N_active)` (Eq. 65), and
    /// the same rounding for a setup prefix's padded Boolean domain (Eq. 174).
    ///
    /// An `N_active` that is already a power of two needs **no** headroom:
    /// `ceil(log2 256) = 8`, so the envelope is `256`, not `512`. That is why
    /// this is not [`bit_width`], which is `ceil(log2 (limit + 1))` — the
    /// rejection-sampling width, one bit wider at an exact power of two.
    ///
    /// # Panics
    /// If `active` is zero.
    pub fn padded_len(active: usize) -> usize {
        assert!(active > 0, "an empty prefix has no envelope");
        active.next_power_of_two()
    }

    /// `S_flat`: the canonical zero-padded setup source of §9.1, whose Boolean
    /// evaluations the setup-product sum-check runs over.
    pub fn pad_to_boolean<R: Ring>(prefix: &[R]) -> Vec<R> {
        let mut out = prefix.to_vec();
        out.resize(Self::padded_len(prefix.len()), R::ZERO);
        out
    }
}

/// One admitted matrix instance: its role, and the `(n, m, d)` that fixes its
/// prefix length.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct View {
    /// Which map this view instantiates, for the schedule record.
    pub role: &'static str,
    /// Module rank `n`.
    pub rows: usize,
    /// Column count `m`.
    pub cols: usize,
    /// Ring dimension `d`.
    pub dim: usize,
}

impl View {
    /// Declares a view.
    pub const fn new(role: &'static str, rows: usize, cols: usize, dim: usize) -> Self {
        Self {
            role,
            rows,
            cols,
            dim,
        }
    }

    /// How many setup coefficients this view reads.
    pub const fn reads(&self) -> usize {
        self.rows * self.cols * self.dim
    }

    /// The Module-SIS instance this view *is*, at the shared modulus.
    ///
    /// A view already carries the `(n_I, m_I, d_I)` of Theorem 10.33's
    /// `Adv^{MSIS}_{q,d_I}(n_I, m_I, eta_I)` sum, so asking it for the instance
    /// rather than restating the shape is what keeps p. 56's admission test
    /// ("the fixed ranks and security contract of the *pre-existing commitment*
    /// cover these exact bounds") honest: the ranks the estimator prices are
    /// literally the ranks the prefix was provisioned at, and a schedule cannot
    /// price a radius against a wider `A` than it built.
    ///
    /// Only the `A`-role view is ever a collision target — the extractor returns
    /// a short kernel vector of the map the response was folded through — but the
    /// conversion is shape arithmetic, so it is offered for every role and the
    /// caller names which one it is querying.
    pub const fn msis_instance(&self, modulus: u64) -> crate::pcs::norm_route::MsisInstance {
        crate::pcs::norm_route::MsisInstance {
            role: self.role,
            modulus,
            ring_dim: self.dim,
            rows: self.rows,
            cols: self.cols,
        }
    }
}

/// `ceil(log2(n + 1))`: the number of bits a rejection draw must read so that
/// every residue in `[0, q)` is reachable and rejection keeps the distribution
/// exactly uniform.
const fn bit_width(limit: u64) -> u32 {
    let mut bits = 0u32;
    while (1u128 << bits) <= (limit as u128) {
        bits += 1;
    }
    bits
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::traits::CenteredRing;
    use algebra::ring::zq::Zq;

    type Q32 = Zq<4_294_967_197>;
    type Z1 = Zq<8_380_417>;
    type R8 = PolyRing<Q32, 8>;

    fn stream() -> SetupStream {
        SetupStream::new(&[0xA5u8; 32])
    }

    #[test]
    fn expansion_is_prefix_consistent_across_lengths() {
        // The whole overlapping-view design rests on this: a shorter read must
        // be a literal prefix of a longer one, or two matrices would disagree
        // about a coefficient they share.
        let s = stream();
        let short = s.coeffs::<Q32>(7);
        let long = s.coeffs::<Q32>(400);
        assert_eq!(&long[..7], &short[..]);
        assert_eq!(s.coeff::<Q32>(0), short[0]);
        // and the seed binds it
        assert_ne!(
            s.coeff::<Q32>(3),
            SetupStream::new(&[0xA6u8; 32]).coeff::<Q32>(3)
        );
        assert_eq!(s.coeff::<Q32>(3), stream().coeff::<Q32>(3));
    }

    #[test]
    fn matrix_view_places_coefficients_row_major_per_eq_66() {
        // A silent transpose or an element-major layout survives a random-matrix
        // round trip, so pin one off-diagonal entry against the formula.
        let s = stream();
        let (rows, cols, d) = (2usize, 3usize, 8usize);
        let m: RingMatrixKey<Q32, 8> = s.matrix(rows, cols);
        let flat = s.coeffs::<Q32>(rows * cols * d);
        for (i, j) in [(0usize, 0usize), (1usize, 2usize), (1usize, 0usize)] {
            let base = (i * cols + j) * d;
            let want: R8 = PolyRing::from_coefficients(flat[base..base + d].to_vec());
            assert_eq!(*m.get(i, j).unwrap(), want, "entry ({i},{j})");
        }
        assert_eq!(m.rows(), rows);
        assert_eq!(m.cols(), cols);
    }

    #[test]
    fn two_views_of_one_seed_share_prefixes_and_differ_by_dimension() {
        // The point of Figure 3: the same flat coefficient acquires different
        // ring-element memberships in a d=8 view and a d=4 view.
        let s = stream();
        let a: RingMatrixKey<Q32, 8> = s.matrix(1, 2);
        let b: RingMatrixKey<Q32, 4> = s.matrix(2, 2);
        let flat = s.coeffs::<Q32>(16);
        assert_eq!(a.get(0, 1).unwrap().coefficients()[0], flat[8]);
        assert_eq!(b.get(1, 0).unwrap().coefficients()[0], flat[8]);
        // Index 12 is where the two groupings actually part: (element, slot) is
        // (1, 4) at d = 8 but (3, 0) at d = 4, so the same coefficient lands in
        // a different ring element *and* a different power of X.
        let idx = 12usize;
        let (a_elem, a_slot) = (idx / 8, idx % 8);
        let (b_elem, b_slot) = (idx / 4, idx % 4);
        assert_eq!((a_elem, a_slot), (1, 4));
        assert_eq!((b_elem, b_slot), (3, 0));
        assert_eq!(a.get(a_elem / 2, a_elem % 2).unwrap().coefficients()[a_slot], flat[idx]);
        assert_eq!(b.get(b_elem / 2, b_elem % 2).unwrap().coefficients()[b_slot], flat[idx]);
        // and the views read different prefix lengths of one stream
        assert_eq!(View::new("A", 1, 2, 8).reads(), 16);
        assert_eq!(View::new("B", 2, 2, 4).reads(), 16);
        assert_eq!(SetupStream::active_prefix(&[
            View::new("A", 1, 2, 8),
            View::new("B", 2, 2, 4),
        ]), 16);
    }

    #[test]
    fn active_prefix_and_envelope_follow_the_paper_formulas() {
        let views = [
            View::new("A", 1, 8, 8),
            View::new("B", 1, 40, 4),
            View::new("D", 1, 33, 4),
        ];
        assert_eq!(SetupStream::active_prefix(&views), 160, "max n*m*d");
        assert_eq!(SetupStream::padded_len(160), 256, "least power of two");
        assert_eq!(SetupStream::padded_len(256), 256, "already exact");
        assert_eq!(SetupStream::padded_len(1), 1);
        assert_eq!(SetupStream::padded_len(257), 512);
        assert_eq!(SetupStream::padded_len(255), 256);
        // Eq. (174): N_prefix < 2 N_active unless N_active is itself a power of two
        assert!(SetupStream::padded_len(160) < 2 * 160);
        // The envelope is `ceil(log2 N)`, not the rejection-sampling width
        // `ceil(log2 (N + 1))`: they part at an exact power of two, and taking
        // the latter would double a provisioned setup for no reason.
        assert_eq!(bit_width(255), 8);
        assert_eq!(bit_width(256), 9, "one bit wider at a power of two");
        assert_eq!(SetupStream::padded_len(256), 1 << bit_width(255));
    }

    #[test]
    fn a_view_names_the_msis_instance_it_provisions() {
        // The radius the schedule prices and the matrix it built must come from
        // one record, or "the fixed ranks of the pre-existing commitment cover
        // this bound" (p. 56) could be checked against a different `A`.
        let view = View::new("A", 1, 8, 8);
        let inst = view.msis_instance(8_380_417);
        assert_eq!(inst.role, "A");
        assert_eq!((inst.modulus, inst.rows, inst.cols, inst.ring_dim), (8_380_417, 1, 8, 8));
        assert_eq!(inst.flat_rows(), view.rows * view.dim);
        assert_eq!(inst.flat_cols(), view.reads(), "n m d flattened is what it reads");
    }

    #[test]
    fn padded_boolean_source_keeps_the_active_prefix() {

        let s = stream();
        let prefix = s.coeffs::<Q32>(5);
        let padded = SetupStream::pad_to_boolean::<Q32>(&prefix);
        assert_eq!(padded.len(), 8);
        assert_eq!(&padded[..5], &prefix[..]);
        assert!(padded[5..].iter().all(|v| *v == Q32::ZERO));
    }

    #[test]
    fn rejection_draws_stay_in_range_over_both_rings() {
        // A mod bias here would silently change the key distribution the
        // security proof is stated against.
        for i in 0..500usize {
            let v = stream().coeff::<Q32>(i);
            assert!(u128::from(v.to_u128()) < u128::from(Q32::MODULUS));
            let z = stream().coeff::<Z1>(i);
            assert!(u128::from(z.to_u128()) < u128::from(Z1::MODULUS));
        }
        assert_eq!(bit_width(4_294_967_196), 32);
        assert_eq!(bit_width(8_380_416), 23);
        assert_eq!(bit_width(1), 1);
        // and the stream is not degenerate
        let spread: Vec<Q32> = stream().coeffs(64);
        assert!(spread.windows(2).any(|w| w[0] != w[1]));
        assert!(spread.iter().any(|v| v.centered() < 0));
    }

    #[test]
    #[should_panic(expected = "non-empty")]
    fn an_empty_view_is_refused() {
        let s = stream();
        let _: RingMatrixKey<Q32, 8> = s.matrix(0, 3);
    }
}
