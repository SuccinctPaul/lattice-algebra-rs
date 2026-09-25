//! Scheme-facing abstraction (Z7): the traits a polynomial commitment
//! scheme is assembled against.
//!
//! The crate's layering rule is that `src` provides **capabilities** (the
//! Ajtai keys, the gadget, the √N-split machinery, the norm arguments) and
//! that a *scheme* is an assembly that only calls them. These traits are the
//! seam that keeps that rule checkable: a scheme under `examples/` is
//! written once against [`Pcs`] / [`BatchPcs`] / [`WeightPcs`], so swapping
//! the underlying commitment mode — or adding a new scheme built from the
//! same parts — does not rewrite the assembly.
//!
//! Three shapes cover the landscape surveyed in
//! `docs/survey-lattice-pcs.md`:
//!
//! - [`Pcs`] — commit to a coefficient vector, open at one point;
//! - [`BatchPcs`] — `k` polynomials opened at one shared point in one proof
//!   (LaBRADOR's amortized opening in PCS form, Greyhound's batch mode,
//!   Akita's batched openings);
//! - [`WeightPcs`] — open against an **arbitrary weight table**
//!   `y = ⟨w, F⟩`, the multilinear/eq-weight shape whose tables do not
//!   factor as an outer product (see [`crate::pcs::batched`] for why that
//!   non-factoring is what forces a separate mode).
//!
//! # Example
//!
//! A scheme assembly written only against the abstraction, not against
//! Greyhound directly:
//!
//! ```rust
//! use algebra::ring::PolynomialQuotientRing;
//! use zk::pcs::{Pcs, Z1Coeff, GreyhoundKey, PackedGreyhound, N_DEG, DIM};
//!
//! /// Proves and re-checks one evaluation claim through the trait only.
//! fn round_trip<P: Pcs>(p: &P, f: &[P::Coeff], point: &P::Point) -> P::Value {
//!     let com = p.commit(f).expect("commit");
//!     let (y, proof) = p.open(f, point).expect("open");
//!     p.verify(&com, point, &y, &proof).expect("verify");
//!     y
//! }
//!
//! let key = PackedGreyhound::new(GreyhoundKey::setup(&[7u8; 32]));
//! let f: Vec<Z1Coeff> = (0..N_DEG * DIM)
//!     .map(|i| Z1Coeff::from((i % 7) as u64))
//!     .collect();
//! let point = Z1Coeff::from(3u64);
//! let com = key.commit(&f).expect("commit");
//! let (y, proof) = key.open(&f, &point).expect("open");
//! assert_eq!(y, round_trip(&key, &f, &point));
//!
//! // The trait object really is checking the claim, not echoing it: a value
//! // off by one must be rejected.
//! let wrong = y + Z1Coeff::from(1u64);
//! assert!(key.verify(&com, &point, &wrong, &proof).is_err());
//! ```

use crate::pcs::batched::{open_batch, verify_batch, BatchedOpeningProof};
use crate::pcs::greyhound::{
    commit, commit_packed, open, open_packed, verify, verify_packed, GreyhoundKey, OpeningProof,
    PcsError, PolyCommitment,
};
use crate::pcs::mle::{
    claim, commit_mle, open_mle_proof, verify_mle_proof, MleCommitment, MleError, MleKey,
    MleOpenProof,
};
use crate::pcs::{RingElt, Z1Coeff};
use alloc::vec::Vec;

/// Commit to a coefficient vector; later open it at a point.
pub trait Pcs {
    /// The coefficient representation this mode commits over (ring elements
    /// for the plain mode, scalars for the packed mode).
    type Coeff;
    /// An evaluation point.
    type Point;
    /// An evaluation value.
    type Value: PartialEq;
    /// A commitment to one polynomial.
    type Commitment: Clone + PartialEq;
    /// An opening proof.
    type Proof: Clone;
    /// Typed rejection.
    type Error: core::fmt::Debug;

    /// Commits to `f`.
    fn commit(&self, f: &[Self::Coeff]) -> Result<Self::Commitment, Self::Error>;

    /// Evaluates and proves: returns `y = f(point)` and the opening proof.
    fn open(
        &self,
        f: &[Self::Coeff],
        point: &Self::Point,
    ) -> Result<(Self::Value, Self::Proof), Self::Error>;

    /// Checks `proof` for the claim `value = f(point)` against `com`.
    fn verify(
        &self,
        com: &Self::Commitment,
        point: &Self::Point,
        value: &Self::Value,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error>;
}

/// The output of a batched opening: one value per committed polynomial plus
/// the single proof covering them all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchOpening<V, P> {
    /// The claimed values, in the order the polynomials were passed in.
    pub values: Vec<V>,
    /// The one proof for the whole batch.
    pub proof: P,
}

/// Open `k` independently committed polynomials at one shared point with a
/// single combined proof.
pub trait BatchPcs {
    /// The coefficient representation this mode commits over.
    type Coeff;
    /// An evaluation point.
    type Point;
    /// An evaluation value.
    type Value: PartialEq;
    /// A commitment to one polynomial.
    type Commitment: Clone + PartialEq;
    /// A batched opening proof covering every claim.
    type Proof: Clone;
    /// Typed rejection.
    type Error: core::fmt::Debug;

    /// Commits to each of `fs`, returning them in the same order.
    fn commit_many(&self, fs: &[&[Self::Coeff]]) -> Result<Vec<Self::Commitment>, Self::Error>;

    /// Proves all `k` claims at `point` at once.
    fn open_batch(
        &self,
        fs: &[&[Self::Coeff]],
        point: &Self::Point,
    ) -> Result<BatchOpening<Self::Value, Self::Proof>, Self::Error>;

    /// Checks the batch against its `(commitment, value)` pairs.
    fn verify_batch(
        &self,
        coms: &[Self::Commitment],
        point: &Self::Point,
        values: &[Self::Value],
        proof: &Self::Proof,
    ) -> Result<(), Self::Error>;
}

/// Open a commitment against an **arbitrary weight table**: the claim is
/// `y = ⟨w, F⟩ for the committed `F`, for any `w` the verifier can write
/// down — power tables, `eq` tensors, range-check functionals.
///
/// This is the shape the sumcheck line lands in: after `ℓ` folding rounds
/// the surviving claim is `Σ_g eq(r, g)·F[g]`, whose weight table does not
/// factor. The cost of admitting non-factored tables is documented on
/// [`crate::pcs::mle`]: the key is tall, which makes verification exact but
/// the commitment transparent rather than hiding.
pub trait WeightPcs {
    /// The committed coefficient representation.
    type Coeff;
    /// The weight-table entry representation (usually the same ring as
    /// `Coeff`).
    type Weight;
    /// The claimed value.
    type Value: PartialEq;
    /// A commitment to one vector.
    type Commitment: Clone + PartialEq;
    /// An opening proof for one weight table.
    type Proof: Clone;
    /// Typed rejection.
    type Error: core::fmt::Debug;

    /// Commits to `f`.
    fn commit(&self, f: &[Self::Coeff]) -> Result<Self::Commitment, Self::Error>;

    /// Proves `⟨weight, F⟩ = y` against the commitment to `f`.
    fn open(
        &self,
        f: &[Self::Coeff],
        weight: &[Self::Weight],
    ) -> Result<(Self::Value, Self::Proof), Self::Error>;

    /// Checks `proof` for the claim `value = ⟨weight, F⟩` against `com`.
    fn verify(
        &self,
        com: &Self::Commitment,
        weight: &[Self::Weight],
        value: &Self::Value,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error>;
}

/// The two things a **tall-key** mode can do and a short-key commitment
/// structurally cannot, split out of [`WeightPcs`] on 2026-09-24.
///
/// Before that split `WeightPcs` was implementable by exactly one family: it
/// demanded `value_of(com, weight)`, which recovers the committed witness from
/// the commitment — possible only when the key is tall (`rows ≥ 2·cols`, see
/// [`crate::pcs::mle`], and the price is a transparent, non-hiding
/// commitment) — and it demanded a `mask_seed` on every opening, which presumes
/// a blinding step that e.g. Orbweaver's `Open(ck, f, x)` simply does not have.
/// Both are real capabilities of one mode, not of a weight-table PCS.
pub trait WeightPcsExt: WeightPcs {
    /// The value `⟨weight, F⟩` implied by a commitment — the honest prover's
    /// statement for that table. Requires recovering the witness.
    fn value_of(
        &self,
        com: &Self::Commitment,
        weight: &[Self::Weight],
    ) -> Result<Self::Value, Self::Error>;

    /// [`WeightPcs::open`] with a blinding mask. `mask_seed` randomizes it, so
    /// two openings of the same claim produce different transcripts.
    fn open_masked(
        &self,
        f: &[Self::Coeff],
        weight: &[Self::Weight],
        mask_seed: &[u8; 32],
    ) -> Result<(Self::Value, Self::Proof), Self::Error>;
}

impl Pcs for GreyhoundKey {
    type Coeff = RingElt;
    type Point = RingElt;
    type Value = RingElt;
    type Commitment = PolyCommitment;
    type Proof = OpeningProof;
    type Error = PcsError;

    fn commit(&self, f: &[RingElt]) -> Result<PolyCommitment, PcsError> {
        commit(self, f)
    }

    fn open(&self, f: &[RingElt], point: &RingElt) -> Result<(RingElt, OpeningProof), PcsError> {
        open(self, f, point)
    }

    fn verify(
        &self,
        com: &PolyCommitment,
        point: &RingElt,
        value: &RingElt,
        proof: &OpeningProof,
    ) -> Result<(), PcsError> {
        verify(self, com, point, value, proof)
    }
}

impl BatchPcs for GreyhoundKey {
    type Coeff = RingElt;
    type Point = RingElt;
    type Value = RingElt;
    type Commitment = PolyCommitment;
    type Proof = BatchedOpeningProof;
    type Error = PcsError;

    fn commit_many(&self, fs: &[&[RingElt]]) -> Result<Vec<PolyCommitment>, PcsError> {
        fs.iter().map(|f| commit(self, f)).collect()
    }

    fn open_batch(
        &self,
        fs: &[&[RingElt]],
        point: &RingElt,
    ) -> Result<BatchOpening<RingElt, BatchedOpeningProof>, PcsError> {
        let (values, proof) = open_batch(self, fs, point)?;
        Ok(BatchOpening { values, proof })
    }

    fn verify_batch(
        &self,
        coms: &[PolyCommitment],
        point: &RingElt,
        values: &[RingElt],
        proof: &BatchedOpeningProof,
    ) -> Result<(), PcsError> {
        verify_batch(self, coms, point, values, proof)
    }
}

/// The σ-packing mode: the same two-layer Ajtai pipeline carrying `d` scalar
/// coefficients per ring element, opened at **scalar** points.
///
/// Wraps a [`GreyhoundKey`]; implements [`Pcs`] with scalar
/// `Coeff`/`Point`/`Value`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackedGreyhound {
    key: GreyhoundKey,
}

impl PackedGreyhound {
    /// Wraps a Greyhound key for the packed scalar-coefficient mode.
    pub fn new(key: GreyhoundKey) -> Self {
        Self { key }
    }

    /// The wrapped key.
    pub fn key(&self) -> &GreyhoundKey {
        &self.key
    }
}

impl Pcs for PackedGreyhound {
    type Coeff = Z1Coeff;
    type Point = Z1Coeff;
    type Value = Z1Coeff;
    type Commitment = PolyCommitment;
    type Proof = OpeningProof;
    type Error = PcsError;

    fn commit(&self, f: &[Z1Coeff]) -> Result<PolyCommitment, PcsError> {
        commit_packed(&self.key, f)
    }

    fn open(&self, f: &[Z1Coeff], point: &Z1Coeff) -> Result<(Z1Coeff, OpeningProof), PcsError> {
        open_packed(&self.key, f, *point)
    }

    fn verify(
        &self,
        com: &PolyCommitment,
        point: &Z1Coeff,
        value: &Z1Coeff,
        proof: &OpeningProof,
    ) -> Result<(), PcsError> {
        verify_packed(&self.key, com, *point, *value, proof)
    }
}

impl WeightPcs for MleKey {
    type Coeff = Z1Coeff;
    type Weight = Z1Coeff;
    type Value = Z1Coeff;
    type Commitment = MleCommitment;
    type Proof = MleOpenProof;
    type Error = MleError;

    fn commit(&self, f: &[Z1Coeff]) -> Result<MleCommitment, MleError> {
        commit_mle(self, f)
    }

    fn open(
        &self,
        f: &[Z1Coeff],
        weight: &[Z1Coeff],
    ) -> Result<(Z1Coeff, MleOpenProof), MleError> {
        // The reference opening: mask on, but with a fixed (zero) seed, so the
        // trait stays implementable by schemes that blind at all. The
        // per-invocation randomized form is `WeightPcsExt::open_masked`.
        self.open_masked(f, weight, &[0u8; 32])
    }

    fn verify(
        &self,
        com: &MleCommitment,
        weight: &[Z1Coeff],
        value: &Z1Coeff,
        proof: &MleOpenProof,
    ) -> Result<(), MleError> {
        verify_mle_proof(self, com, weight, *value, proof)
    }
}

impl WeightPcsExt for MleKey {
    fn value_of(&self, com: &MleCommitment, weight: &[Z1Coeff]) -> Result<Z1Coeff, MleError> {
        claim(self, com, weight)
    }

    fn open_masked(
        &self,
        f: &[Z1Coeff],
        weight: &[Z1Coeff],
        mask_seed: &[u8; 32],
    ) -> Result<(Z1Coeff, MleOpenProof), MleError> {
        let com = commit_mle(self, f)?;
        let y = claim(self, &com, weight)?;
        let proof = open_mle_proof(self, f, weight, mask_seed)?;
        Ok((y, proof))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::greyhound::eval_point;
    use crate::pcs::{packing, DIM, N_DEG};

    fn scalars(tag: u64) -> Vec<Z1Coeff> {
        (0..N_DEG * DIM)
            .map(|i| Z1Coeff::from((i as u64 + tag) % 5))
            .collect()
    }

    #[test]
    fn batch_dispatch_opens_shared_point_claims() {
        let key = GreyhoundKey::setup(&[11u8; 32]);
        let (fa, fb) = (scalars(0), scalars(1));
        let (ra, rb) = (packing::pack_scalars(&fa), packing::pack_scalars(&fb));
        let fs: [&[RingElt]; 2] = [&ra, &rb];

        let coms = key.commit_many(&fs).expect("commit_many");
        assert_eq!(coms.len(), 2);
        let point = eval_point(3);
        let batch = key.open_batch(&fs, &point).expect("open_batch");
        key.verify_batch(&coms, &point, &batch.values, &batch.proof)
            .expect("honest batch verifies through the trait");

        // Swapping which value belongs to which polynomial must be caught.
        let swapped: Vec<RingElt> = batch.values.iter().rev().cloned().collect();
        assert!(key
            .verify_batch(&coms, &point, &swapped, &batch.proof)
            .is_err());
    }

    #[test]
    fn weight_dispatch_round_trips_and_rejects() {
        let key = MleKey::setup(&[12u8; 32], 16);
        let f: Vec<Z1Coeff> = (0..16).map(|i| Z1Coeff::from(i as u64 + 1)).collect();
        let w: Vec<Z1Coeff> = (0..16).map(|i| Z1Coeff::from(i as u64 + 2)).collect();

        let com = key.commit(&f).expect("commit");
        // `value_of` and the seeded opening now live on `WeightPcsExt`, so this
        // test is also the proof that the split is reachable: `key.open` is the
        // base-trait reference opening and must agree with the masked one.
        let y = key.value_of(&com, &w).expect("value_of");
        let (y_ref, proof_ref) = key.open(&f, &w).expect("base open");
        let (y_masked, proof_masked) = key.open_masked(&f, &w, &[4u8; 32]).expect("open_masked");
        assert_eq!(y, y_ref, "the trait's two paths agree on the claim");
        assert_eq!(y_ref, y_masked, "masking must not move the claimed value");
        key.verify(&com, &w, &y, &proof_ref)
            .expect("honest reference opening verifies");
        key.verify(&com, &w, &y, &proof_masked)
            .expect("honest masked opening verifies");
        assert!(
            proof_ref != proof_masked,
            "a different mask seed must give a different transcript"
        );
        assert!(key
            .verify(&com, &w, &(y + Z1Coeff::from(1u64)), &proof_ref)
            .is_err());
    }

    #[test]
    fn packed_dispatch_matches_the_packed_free_functions() {
        let packed = PackedGreyhound::new(GreyhoundKey::setup(&[13u8; 32]));
        let f = scalars(2);
        let point = Z1Coeff::from(5u64);
        let com = packed.commit(&f).expect("commit");
        let (y, proof) = packed.open(&f, &point).expect("open");
        packed
            .verify(&com, &point, &y, &proof)
            .expect("packed round trip through the trait");
        assert_eq!(
            com,
            crate::pcs::commit_packed(packed.key(), &f).expect("same")
        );
    }
}
