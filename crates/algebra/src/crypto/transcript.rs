//! Fiat–Shamir transcripts (L4).
//!
//! A transcript turns an interactive identification protocol into a
//! non-interactive signature/proof by deriving challenges from a hash of
//! everything the prover has produced so far. The API shape — absorb before
//! challenge, state carried forward — makes the classic mistakes (forgetting
//! to bind the public key, ambiguous concatenations) structurally hard.
//!
//! Domain labels are supplied by the scheme parameter sets; see the design
//! docs (`design/hash-fiat-shamir`) for the labeling protocol.

use crate::crypto::xof::Xof;

/// Fiat–Shamir transcript over an [`Xof`].
#[derive(Clone)]
pub struct Transcript<X: Xof> {
    xof: X,
}

impl<X: Xof> Transcript<X> {
    /// Starts a transcript bound to the scheme-level domain label
    /// (e.g. `b"ML-DSA-65 sign"`).
    pub fn new(domain: &[u8]) -> Self {
        Self {
            xof: X::new(domain),
        }
    }

    /// Absorbs `data` under a label (length-prefixed, see
    /// [`Xof::absorb_labeled`]).
    pub fn absorb(&mut self, label: &[u8], data: &[u8]) {
        self.xof.absorb_labeled(label, data);
    }

    /// Squeezes `n` challenge bytes. The transcript state advances, so two
    /// consecutive calls yield different challenges.
    pub fn challenge_bytes(&mut self, n: usize) -> Vec<u8> {
        self.xof.squeeze_vec(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::xof::Shake256Xof;

    #[test]
    fn binding_public_key_changes_challenge() {
        let mut t = Transcript::<Shake256Xof>::new(b"test-scheme");
        t.absorb(b"pk", &[1u8; 32]);
        t.absorb(b"commit", &[2u8; 32]);
        let c1 = t.challenge_bytes(32);

        let mut t2 = Transcript::<Shake256Xof>::new(b"test-scheme");
        t2.absorb(b"pk", &[3u8; 32]); // different key
        t2.absorb(b"commit", &[2u8; 32]);
        let c2 = t2.challenge_bytes(32);
        assert_ne!(c1, c2);
    }

    #[test]
    fn challenges_advance_state() {
        let mut t = Transcript::<Shake256Xof>::new(b"s");
        t.absorb(b"x", b"y");
        let a = t.challenge_bytes(32);
        let b = t.challenge_bytes(32);
        assert_ne!(a, b, "two challenges without fresh absorbs must differ");
    }

    #[test]
    fn order_matters() {
        let mut t1 = Transcript::<Shake256Xof>::new(b"s");
        t1.absorb(b"a", b"1");
        t1.absorb(b"b", b"2");
        let a = t1.challenge_bytes(32);

        let mut t2 = Transcript::<Shake256Xof>::new(b"s");
        t2.absorb(b"b", b"2");
        t2.absorb(b"a", b"1");
        let b = t2.challenge_bytes(32);
        assert_ne!(a, b, "FS must be order-sensitive");
    }
}
