//! Lane-digit packing (Z7 support): the encoding that lets an Ajtai commitment
//! carry messages from a **large** prime field inside ring elements with
//! **small** coefficients.
//!
//! Basic Ajtai (`m = A₀·h + A₁·η`) is only binding while the *message* is
//! short, but a polynomial commitment's messages live in the soundness field
//! `Z_p` — 255 bits in every serious SNARK. Putting one `Z_p` element per
//! coefficient therefore forces `log q = Ω(log p)`, and the commitment grows
//! with it. Hwang–Seo–Song (2024/306, §3.1) fix this with a different
//! embedding, so this module is a genuinely separate capability from
//! [`crate::pcs::packing`] (which packs *same-field* coefficients `d` per
//! element) and from [`crate::pcs::gadget`] (which decomposes one element into
//! `⌈log q⌉` digits *inside* `R_q`, i.e. keeps the message in the
//! commitment's own ring).
//!
//! # The lemma this implements
//!
//! Fix a ring degree `d`, a base `b ≥ 2` and a digit count `r` with `p = bʳ+1`
//! prime, and write `R = Z[X]/(Xᵈ+1)`. Because `Xᵈ+1 = (X^{d/r})ʳ+1` and
//! `bʳ ≡ −1 (mod p)`, the polynomial `X^{d/r} − b` maps to `0`, and Lemma 9
//! gives an isomorphism of `Z`-modules
//!
//! ```text
//! φ : R/(X^{d/r} − b) ──≅── Z_p^{d/r},
//!     φ(a)_i = Σ_{j<r} a_{(d/r)j + i} · bʲ       for a = Σₖ aₖ Xᵏ
//! ```
//!
//! `R` itself is the *representation set* of the quotient, so `d` small integer
//! coefficients stand for `d/r` field elements: coefficient slot `(i, j)` —
//! index `(d/r)·j + i` — is digit `j` of **lane** `i`. Encoding is Alg. 1: read
//! each field element in base `b`, then center every digit at `0`, paying for
//! each centering with a `+1` carried into slot `j+1` of the *same* lane (and
//! `Xᵈ = −1` turns the last slot's overflow into a `−1` in slot `0`). The two
//! directions exported here are [`LanePacking::encode`] (`Ecd`) and
//! [`LanePacking::decode`] (`Dcd`).
//!
//! # The three identities the scheme runs on
//!
//! 1. **Section.** `Dcd(Ecd(⃗a)) = ⃗a`, including the `a = p − 1` branch of
//!    Alg. 1 (`round_trip_recovers_the_message`).
//! 2. **Homomorphism.** `Dcd` is `Z`-linear and a *ring* map
//!    `R → Z_p[X]/(X^{d/r} − b)`, so a ring product survives decoding as the
//!    twisted product of the decoded vectors (`decode_is_a_ring_homomorphism`).
//! 3. **Pinning** — the load-bearing one. For a *scalar* input, `Ecd(a)` is
//!    Alg. 1 applied to `⃗a = (a, 0, …, 0)`, which represents the **constant**
//!    polynomial `a` of `Z_p[X]/(X^{d/r} − b)`. Hence
//!
//!    ```text
//!    Dcd(Ecd(s) · u) = s · Dcd(u)      (componentwise, mod p)
//!    ```
//!
//!    (`scalar_pinning`). This is why `PC.Eval` may form
//!    `e = Σᵢ Ecd(xⁿⁱ)·hhᵢ` out of `d`-sized ring multiplications and still have
//!    the verifier recover `y = ⟨Dcd(e), (1, x, …, xⁿ⁻¹)⟩ = h(x)`: each weight
//!    scales the whole decoded block instead of scrambling the lane structure
//!    the way a generic ring product would (`the_sqrt_split_evaluation_claim`).
//!
//! # Norm accounting (§3.1 under Alg. 1; Thm. 7)
//!
//! [`LanePacking::coefficient_bound`] is `‖Ecd(⃗a)‖∞ ≤ (b+2)/2` and
//! [`LanePacking::scalar_l1_bound`] is `‖Ecd(a)‖₁ ≤ (b+2)r/2` for a scalar
//! input. Both are asserted over sampled inputs below rather than assumed, and
//! they are the factors every `β` bound in the scheme layer is built from.
//!
//! # What this module deliberately does *not* do
//!
//! §3.2 defines a *randomized* encoding `R.Ecd(⃗a, s)` sampling
//! `D_{Ecd(⃗a) + P·Zᵈ, sP}` for `P` the negacyclic matrix of `X^{d/r} − b`; that
//! is what buys the paper's rejection-sampling-free zero knowledge. This repo
//! has no discrete-Gaussian-over-a-coset-of-an-arbitrary-lattice sampler
//! ([`algebra::crypto::sampling::DiscreteGaussian`] is spherical over `Z`), so
//! only deterministic `Ecd` is implemented and the gap is recorded in
//! `examples/celpc.rs`. Everything here is generic over the commitment ring, so
//! a coset sampler would be *added* to the scheme layer, not rewired into it.
//!
//! Layering: `foundation → pcs::digit_pack`. Nothing here is scheme-specific:
//! the same `(Ecd, Dcd)` pair is what leveled-Ajtai SNARKs and any future
//! large-field PCS need.

use crate::foundation::fs::seed_stream;
use crate::foundation::sampling::from_centered;
use crate::pcs::projection::to_coeffs;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::number_theory::is_prime_u64;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{CenteredRing, PolynomialQuotientRing, Ring};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Largest message modulus this layer represents: every `Z_p` element is a
/// `u64` and every intermediate a `u128`, so `p ≤ 2³²` keeps the field
/// arithmetic exact and compatible with the crate's `u32` wire encoding.
///
/// The paper's `p` is 255 bits, which needs a big-integer field type this repo
/// does not have (gap G7). Only the *size* is affected: `p = bʳ+1`, `r` digits
/// per element and `d/r` lanes per ring element are all preserved.
pub const MAX_MESSAGE_MODULUS: u64 = 1 << 32;

/// Why a packing could not be built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParamError {
    /// `b < 2`: there are no digits to decompose into.
    BaseTooSmall(u64),
    /// `r = 0` or `r ∤ d`, so `d` coefficients do not split into lanes.
    DigitsNotDivisor {
        /// Digit count supplied.
        digits: usize,
        /// Ring degree supplied.
        ring_degree: usize,
    },
    /// `bʳ` overflowed `u64`.
    ModulusOverflow {
        /// Base supplied.
        base: u64,
        /// Digit count supplied.
        digits: usize,
    },
    /// `p = bʳ + 1` is not prime, so `Z_p` is not a field and `bʳ ≡ −1 (mod p)`
    /// does not identify the negacyclic wrap.
    NotAField(u64),
    /// `p` exceeds [`MAX_MESSAGE_MODULUS`].
    ModulusTooLarge {
        /// The `bʳ + 1` that was computed.
        modulus: u64,
        /// The representable ceiling.
        limit: u64,
    },
}

impl fmt::Display for ParamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamError::BaseTooSmall(b) => write!(f, "base {b} must be at least 2"),
            ParamError::DigitsNotDivisor {
                digits,
                ring_degree,
            } => write!(
                f,
                "digit count {digits} must be positive and divide the ring degree {ring_degree}"
            ),
            ParamError::ModulusOverflow { base, digits } => {
                write!(f, "{base}^{digits} overflows u64")
            }
            ParamError::NotAField(p) => write!(f, "p = {p} = bʳ+1 is not prime"),
            ParamError::ModulusTooLarge { modulus, limit } => {
                write!(f, "message modulus {modulus} exceeds the ceiling {limit}")
            }
        }
    }
}

/// Why an encode/decode call refused its input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum PackError {
    /// A message vector is not a whole number of lanes.
    Misaligned {
        /// Element count supplied.
        got: usize,
        /// Lanes per ring element, `d/r`.
        lane: usize,
    },
    /// A field element reached `p`.
    OutOfRange {
        /// The offending value.
        value: u64,
        /// The message modulus.
        modulus: u64,
    },
    /// The packing's `d` disagrees with the ring the caller presented.
    WrongRingDegree {
        /// Degree the packing was built for.
        expected: usize,
        /// Degree the call presented.
        got: usize,
    },
    /// A block split left a remainder.
    RaggedBlocks {
        /// Coefficient count supplied.
        got: usize,
        /// Requested block count.
        blocks: usize,
    },
    /// A stack of blocks was not uniformly wide.
    RaggedRows {
        /// Narrowest block supplied.
        got: usize,
        /// Required width.
        expected: usize,
    },
}

impl fmt::Display for PackError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PackError::Misaligned { got, lane } => {
                write!(f, "{got} message elements do not fill lanes of {lane}")
            }
            PackError::OutOfRange { value, modulus } => {
                write!(f, "message {value} is outside Z_{modulus}")
            }
            PackError::WrongRingDegree { expected, got } => {
                write!(f, "packing is built for degree {expected}, got {got}")
            }
            PackError::RaggedBlocks { got, blocks } => {
                write!(f, "{got} coefficients do not split into {blocks} blocks")
            }
            PackError::RaggedRows { got, expected } => {
                write!(
                    f,
                    "a block of {got} coefficients against the required {expected}"
                )
            }
        }
    }
}

/// The packing parameters `(b, r, d)` and the derived message field `Z_p`.
///
/// `d/r` ([`lanes`](Self::lanes)) is the number of field elements one ring
/// element carries; `r` is the number of base-`b` digits each is spread over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LanePacking {
    base: u64,
    digits: usize,
    ring_degree: usize,
    modulus: u64,
}

/// One ring element's coefficients, padded to exactly `D` ([`PolyRing`] trims
/// trailing zeros, so every slot index below must go through this).
fn flat<R: Ring, const D: usize>(elt: &PolyRing<R, D>) -> Vec<R> {
    to_coeffs::<R, D>(core::slice::from_ref(elt))
}

/// `a + b·Xᵈ`-style scalar multiple of a ring element: `c·a` coefficientwise.
fn scaled<R: Ring, const D: usize>(elt: &PolyRing<R, D>, c: R) -> PolyRing<R, D> {
    PolyRing::from_coefficients(flat(elt).iter().map(|x| *x * c).collect())
}

impl LanePacking {
    /// Builds the packing for `(base, digits, ring_degree)`, checking each side
    /// condition Lemma 9 needs: `b ≥ 2`, `r ∣ d`, `p = bʳ+1` prime, `p`
    /// representable.
    ///
    /// # Errors
    /// The matching [`ParamError`] variant for whichever condition fails, in
    /// the order above.
    pub fn new(base: u64, digits: usize, ring_degree: usize) -> Result<Self, ParamError> {
        if base < 2 {
            return Err(ParamError::BaseTooSmall(base));
        }
        if digits == 0 || ring_degree % digits != 0 {
            return Err(ParamError::DigitsNotDivisor {
                digits,
                ring_degree,
            });
        }
        let digits32 =
            u32::try_from(digits).map_err(|_| ParamError::ModulusOverflow { base, digits })?;
        let power = base
            .checked_pow(digits32)
            .ok_or(ParamError::ModulusOverflow { base, digits })?;
        let modulus = power.saturating_add(1);
        if !is_prime_u64(modulus) {
            return Err(ParamError::NotAField(modulus));
        }
        if modulus > MAX_MESSAGE_MODULUS {
            return Err(ParamError::ModulusTooLarge {
                modulus,
                limit: MAX_MESSAGE_MODULUS,
            });
        }
        Ok(Self {
            base,
            digits,
            ring_degree,
            modulus,
        })
    }

    /// The base `b`.
    pub const fn base(&self) -> u64 {
        self.base
    }

    /// The digit count `r`.
    pub const fn digits(&self) -> usize {
        self.digits
    }

    /// The ring degree `d`.
    pub const fn ring_degree(&self) -> usize {
        self.ring_degree
    }

    /// The message modulus `p = bʳ + 1`.
    pub const fn modulus(&self) -> u64 {
        self.modulus
    }

    /// `d/r`: field elements per ring element.
    pub const fn lanes(&self) -> usize {
        self.ring_degree / self.digits
    }

    /// `‖Ecd(⃗a)‖∞ ≤ (b+2)/2` — the sentence after Alg. 1 ("`|a_{i,j}| ≤ ½b` and
    /// `|c_{i,j}| ≤ 1`"), widened by the one slot a lane-internal carry hits.
    pub const fn coefficient_bound(&self) -> u64 {
        (self.base + 2) / 2
    }

    /// `‖Ecd(a)‖₁ ≤ (b+2)r/2` for a scalar input, the factor `PC.Eval`'s bound
    /// is built from ("since `‖Ecd(xᵏ)‖ ≤ (b+1)r/2` for any `k`" in Thm. 7).
    ///
    /// The paper writes `½(b+1)r` there and `½(b+2)r` in §3.1; this returns the
    /// larger, which is the one that keeps the derived bounds valid.
    pub const fn scalar_l1_bound(&self) -> u64 {
        // `b` is even whenever `p = bʳ+1` is an odd prime, so `b + 2` is even.
        (self.base + 2) * (self.digits as u64) / 2
    }

    /// `2⁻¹ = (p+1)/2 mod p`, the inverse `PC.Open` applies to undo its own
    /// doubling. Prime `p = bʳ+1` is odd because `b` is even.
    pub const fn half(&self) -> u64 {
        self.modulus.div_ceil(2)
    }

    /// Alg. 1 steps 1–5: the `r` base-`b` digits of `a`, including the special
    /// case `a = p − 1 ↦ (0, …, 0, b)` that keeps the top of the range inside
    /// `r` digits (`bʳ = p − 1` needs `r+1` plain digits otherwise).
    ///
    /// # Errors
    /// [`PackError::OutOfRange`] if `a ≥ p`.
    pub fn digits_of(&self, a: u64) -> Result<Vec<i64>, PackError> {
        if a >= self.modulus {
            return Err(PackError::OutOfRange {
                value: a,
                modulus: self.modulus,
            });
        }
        if a == self.modulus - 1 {
            let mut out = vec![0i64; self.digits];
            let last = out.len() - 1;
            out[last] = self.base as i64;
            return Ok(out);
        }
        let mut rest = a;
        let mut out = Vec::with_capacity(self.digits);
        for _ in 0..self.digits {
            out.push((rest % self.base) as i64);
            rest /= self.base;
        }
        debug_assert_eq!(rest, 0, "a < bʳ on the branch above");
        Ok(out)
    }

    /// `Ecd(⃗a)`: one ring element per `d/r` message elements, lane-major, so
    /// `⃗a = a₀ ‖ … ‖ a_{ℓ−1}` maps to `(Ecd(a₀), …, Ecd(a_{ℓ−1}))` as §3.2
    /// spells out for the vector case.
    ///
    /// Output coefficients are *integer* digits centered at `0` (each within
    /// [`coefficient_bound`](Self::coefficient_bound) in magnitude) mapped into
    /// `R_q` by [`from_centered`], so the encoding does not depend on the
    /// commitment modulus `q` at all — which is the whole point.
    ///
    /// # Errors
    /// [`PackError::WrongRingDegree`] if `D != d`,
    /// [`PackError::Misaligned`] unless `values.len() % lanes == 0`,
    /// [`PackError::OutOfRange`] for a value `≥ p`.
    pub fn encode<R: Ring, const D: usize>(
        &self,
        values: &[u64],
    ) -> Result<Vec<PolyRing<R, D>>, PackError> {
        self.check_degree(D)?;
        let lanes = self.lanes();
        if values.len() % lanes != 0 {
            return Err(PackError::Misaligned {
                got: values.len(),
                lane: lanes,
            });
        }
        let mut out = Vec::with_capacity(values.len() / lanes);
        for chunk in values.chunks(lanes) {
            let mut ints = vec![0i64; D];
            for (lane, &value) in chunk.iter().enumerate() {
                let digits = self.digits_of(value)?;
                let mut carry = 0i64;
                for (slot, &digit) in digits.iter().enumerate() {
                    // Steps 9–13: center the digit, paying with a carry into
                    // the next digit slot of the *same* lane.
                    let (centered, next) =
                        if digit > i64::try_from(self.base / 2).expect("b < 2^63") {
                            (digit - i64::try_from(self.base).expect("b < 2^63"), 1i64)
                        } else {
                            (digit, 0i64)
                        };
                    ints[lane + lanes * slot] += centered + carry;
                    carry = next;
                }
                if carry == 1 {
                    // `X^{(d/r)r + i} = X^{d+i} = −Xⁱ` under `Xᵈ = −1`, which is
                    // the same statement as `bʳ ≡ −1 (mod p)`.
                    ints[lane] -= 1;
                }
            }
            out.push(PolyRing::from_coefficients(
                ints.iter().map(|&c| from_centered::<R>(c)).collect(),
            ));
        }
        Ok(out)
    }

    /// `Ecd(a)` for a *single* field element — §3.1's "as an abuse of notation,
    /// we often put an integer `a ∈ Z_p` as an input", i.e. `⃗a = (a, 0, …, 0)`.
    /// The result represents the constant `a` of `Z_p[X]/(X^{d/r} − b)`, which
    /// is exactly what makes [`Self::decode`] pin scalars.
    ///
    /// # Errors
    /// As [`Self::encode`].
    pub fn encode_scalar<R: Ring, const D: usize>(
        &self,
        a: u64,
    ) -> Result<PolyRing<R, D>, PackError> {
        self.check_degree(D)?;
        let mut padded = vec![0u64; self.lanes()];
        padded[0] = a;
        Ok(self
            .encode::<R, D>(&padded)?
            .into_iter()
            .next()
            .expect("one full lane group"))
    }

    /// `Dcd(⃗a)` = `φ`: reduce each ring element mod `X^{d/r} − b` over `Z_p`
    /// and read off the power basis, i.e. lane `i` is
    /// `Σ_{j<r} a_{(d/r)j+i}·bʲ mod p`.
    ///
    /// Coefficients are read as the **centered representative mod `q`** — the
    /// same reading the paper's `‖2·‖₂` gates use. That is well defined only
    /// while no committed coefficient has wrapped past `q/2`, which is the
    /// small-message side condition of Ajtai binding; the scheme layer enforces
    /// it with the `β` gates, not this layer.
    ///
    /// # Errors
    /// [`PackError::WrongRingDegree`] if `D != d`.
    pub fn decode<R: CenteredRing, const D: usize>(
        &self,
        rings: &[PolyRing<R, D>],
    ) -> Result<Vec<u64>, PackError> {
        self.check_degree(D)?;
        let stride = self.lanes();
        let mut out = Vec::with_capacity(rings.len() * stride);
        for elt in rings {
            let coeffs = flat(elt);
            for lane in 0..stride {
                let mut acc: i128 = 0;
                let mut weight: u128 = 1;
                for digit in 0..self.digits {
                    let coef = i128::from(coeffs[lane + stride * digit].centered());
                    acc += coef * i128::try_from(weight).expect("bʳ ≤ p ≤ 2³²");
                    weight *= u128::from(self.base);
                }
                out.push(self.reduce(acc));
            }
        }
        Ok(out)
    }

    /// `PC.Open` step 4's decode: `(p+1)/2 · Dcd(2·⃗hhh) mod p`, the message
    /// recovered from the *doubled* witness the extractor hands over (§3.3
    /// Thm. 3: `⃗mᵢ = (p+1)/2 · Dcd(2⃗mmmᵢ)`).
    ///
    /// By `Z`-linearity this equals [`Self::decode`] on the undoubled witness,
    /// which `decode_doubled_matches_decode` pins — otherwise a flipped doubling
    /// convention would only surface as an honest opening that fails.
    ///
    /// # Errors
    /// As [`Self::decode`].
    pub fn decode_doubled<R: CenteredRing, const D: usize>(
        &self,
        rings: &[PolyRing<R, D>],
    ) -> Result<Vec<u64>, PackError> {
        self.check_degree(D)?;
        let two = R::ONE + R::ONE;
        let doubled: Vec<PolyRing<R, D>> = rings.iter().map(|elt| scaled(elt, two)).collect();
        let half = self.half();
        Ok(self
            .decode(&doubled)?
            .iter()
            .map(|v| self.mul(*v, half))
            .collect())
    }

    /// The `√` decomposition of `PC.Com` step 1: `N = n·m` coefficients become
    /// `m` blocks `⃗hᵢ = (h_{ni}, …, h_{n(i+1)−1})`.
    ///
    /// # Errors
    /// [`PackError::RaggedBlocks`] unless `blocks ∣ coeffs.len()`.
    pub fn blocks<'a>(
        &self,
        coeffs: &'a [u64],
        blocks: usize,
    ) -> Result<Vec<&'a [u64]>, PackError> {
        if blocks == 0 || coeffs.len() % blocks != 0 {
            return Err(PackError::RaggedBlocks {
                got: coeffs.len(),
                blocks,
            });
        }
        Ok(coeffs.chunks(coeffs.len() / blocks).collect())
    }

    /// `PC.Open` step 4's right-hand side: the polynomial
    /// `Σᵢ Xⁿⁱ·⟨⃗hᵢ, ⃗X⟩` rebuilt from its blocks, i.e. the concatenation
    /// `⃗h₀ ‖ … ‖ ⃗h_{m−1}`.
    ///
    /// # Errors
    /// [`PackError::RaggedRows`] if a block is not `block_len` wide,
    /// [`PackError::OutOfRange`] for a decoded value `≥ p`.
    pub fn recombine(&self, blocks: &[&[u64]], block_len: usize) -> Result<Vec<u64>, PackError> {
        if blocks.iter().any(|b| b.len() != block_len) {
            return Err(PackError::RaggedRows {
                got: blocks.iter().map(|b| b.len()).min().unwrap_or(0),
                expected: block_len,
            });
        }
        let mut out = Vec::with_capacity(blocks.len() * block_len);
        for b in blocks {
            for &v in *b {
                if v >= self.modulus {
                    return Err(PackError::OutOfRange {
                        value: v,
                        modulus: self.modulus,
                    });
                }
            }
            out.extend_from_slice(b);
        }
        Ok(out)
    }

    /// The weights `PC.Eval` encodes: `(xⁿⁱ)_{i<m} mod p`, built as powers of
    /// `xⁿ` so the table costs `O(m)` field products.
    pub fn block_weights(&self, x: u64, block_len: usize, blocks: usize) -> Vec<u64> {
        let step = self.pow(x, block_len as u64);
        let mut out = Vec::with_capacity(blocks);
        let mut acc = 1u64;
        for _ in 0..blocks {
            out.push(acc);
            acc = self.mul(acc, step);
        }
        out
    }

    /// `⟨Dcd(⃗e), (1, x, …, xⁿ⁻¹)⟩ mod p` — the second half of `PC.Eval` step 2,
    /// and the verifier's only route to `y`.
    pub fn eval_fold(&self, decoded: &[u64], x: u64) -> u64 {
        let mut acc = 0u64;
        let mut power = 1u64;
        for &v in decoded {
            acc = self.add(acc, self.mul(v, power));
            power = self.mul(power, x);
        }
        acc
    }

    /// Plain Horner `Σₖ cₖ xᵏ mod p` over a coefficient vector: the reference
    /// evaluation the fold above is checked against.
    pub fn eval_at(&self, coeffs: &[u64], x: u64) -> u64 {
        let mut acc = 0u64;
        for &c in coeffs.iter().rev() {
            acc = self.add(self.mul(acc, x), c);
        }
        acc
    }

    /// `⃗g ← U(Z_p^count)`: the uniformly random mask preimage of Fig. 1 step 2
    /// (`⃗gⱼ ← U(Z_pⁿ)`), and the blinder source `PC.Com` step 2 uses in the
    /// hiding variant.
    pub fn uniform_preimages(&self, label: &[u8], seed: &[u8; 32], count: usize) -> Vec<u64> {
        let mut xof = seed_stream::<Shake256Xof>(label, seed);
        (0..count)
            .map(|_| uniform_below(&mut xof, self.modulus))
            .collect()
    }

    /// `a + b mod p`.
    pub const fn add(&self, a: u64, b: u64) -> u64 {
        ((a as u128 + b as u128) % self.modulus as u128) as u64
    }

    /// `a · b mod p`.
    pub const fn mul(&self, a: u64, b: u64) -> u64 {
        ((a as u128 * b as u128) % self.modulus as u128) as u64
    }

    /// `base^exp mod p` by square-and-multiply.
    pub const fn pow(&self, mut base: u64, mut exp: u64) -> u64 {
        let p = self.modulus;
        let mut acc = 1u64;
        base %= p;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = ((acc as u128 * base as u128) % p as u128) as u64;
            }
            base = ((base as u128 * base as u128) % p as u128) as u64;
            exp >>= 1;
        }
        acc
    }

    /// A centered accumulation reduced to a `Z_p` representative.
    fn reduce(&self, acc: i128) -> u64 {
        acc.rem_euclid(i128::from(self.modulus)) as u64
    }

    fn check_degree(&self, got: usize) -> Result<(), PackError> {
        if got != self.ring_degree {
            return Err(PackError::WrongRingDegree {
                expected: self.ring_degree,
                got,
            });
        }
        Ok(())
    }
}

/// An exactly uniform draw from `[0, bound)` over a 128-bit stream.
///
/// Rejection over the partial top period, so no modulo bias reaches a challenge
/// or a mask; the expected number of squeezes is `1 + O(bound/2¹²⁸)`, and for a
/// power-of-two `bound` nothing is ever rejected.
pub fn uniform_below<X: Xof>(xof: &mut X, bound: u64) -> u64 {
    assert!(bound > 0, "an empty range cannot be sampled");
    let bound128 = u128::from(bound);
    // Largest multiple of `bound` inside the representable range.
    let limit = (u128::MAX / bound128) * bound128;
    loop {
        let mut buf = [0u8; 16];
        xof.squeeze(&mut buf);
        let raw = u128::from_le_bytes(buf);
        if raw < limit {
            return (raw % bound128) as u64;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    /// The house non-NTT prime `2³² − 99 ≡ 5 (mod 8)`: 2-adicity 2, so no NTT
    /// of degree `≥ 4` exists and every product here is schoolbook.
    type Q5 = Zq<4294967197>;
    /// An NTT-friendly modulus, to show the encoding is indifferent to it.
    type Z1 = Zq<8380417>;

    const D: usize = 64;
    /// `b = 210, r = 4 ⇒ p = 210⁴ + 1 = 1_944_810_001` (prime, 31 bits).
    const BASE: u64 = 210;
    const DIGITS: usize = 4;
    const P: u64 = 1_944_810_001;

    fn packing() -> LanePacking {
        LanePacking::new(BASE, DIGITS, D).expect("valid toy packing")
    }

    /// Deterministic pseudo-random field elements (splitmix64), so the tests
    /// need no `std` RNG.
    fn values(seed: u64, count: usize) -> Vec<u64> {
        (0..count)
            .map(|i| {
                let mut x = seed
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .wrapping_add(i as u64 + 1);
                x ^= x >> 30;
                x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
                x ^= x >> 27;
                x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
                x ^ (x >> 31)
            })
            .map(|x| x % P)
            .collect()
    }

    #[test]
    fn the_instance_satisfies_p_equals_b_pow_r_plus_one() {
        let pack = packing();
        assert_eq!(pack.modulus(), P);
        assert_eq!(pack.base().pow(pack.digits() as u32) + 1, P);
        assert!(is_prime_u64(P));
        // `bʳ ≡ −1 (mod p)` is exactly the reduction the negacyclic wrap mirrors.
        assert_eq!(pack.pow(BASE, DIGITS as u64), P - 1);
        assert_eq!(pack.lanes(), D / DIGITS);
        assert_eq!(pack.coefficient_bound(), (BASE + 2) / 2);
        assert_eq!(pack.scalar_l1_bound(), (BASE + 2) * DIGITS as u64 / 2);
    }

    #[test]
    fn round_trip_recovers_the_message() {
        // Identity 1, with the `p − 1` digit branch forced in.
        let pack = packing();
        for seed in 0..12u64 {
            let mut msg = values(seed, 3 * pack.lanes());
            for slot in msg.iter_mut().take(4) {
                *slot = P - 1;
            }
            let rings: Vec<PolyRing<Q5, D>> = pack.encode(&msg).expect("aligned");
            assert_eq!(rings.len(), 3, "one ring element per lane group");
            assert_eq!(pack.decode(&rings).expect("decode"), msg, "seed {seed}");
        }
    }

    #[test]
    fn digits_and_norms_stay_inside_the_paper_bounds() {
        let pack = packing();
        let mut worst_inf = 0u64;
        let mut worst_l1 = 0u64;
        for seed in 0..200u64 {
            let msg = values(seed, pack.lanes());
            let rings: Vec<PolyRing<Q5, D>> = pack.encode(&msg).expect("aligned");
            for c in to_coeffs::<Q5, D>(&rings) {
                worst_inf = worst_inf.max(c.abs_infinity());
            }
            let one = pack.encode_scalar::<Q5, D>(msg[0]).expect("aligned");
            worst_l1 = worst_l1.max(flat(&one).iter().map(|c| c.abs_infinity()).sum::<u64>());
        }
        assert!(
            worst_inf <= pack.coefficient_bound(),
            "‖Ecd‖∞ {worst_inf} exceeds (b+2)/2 = {}",
            pack.coefficient_bound()
        );
        assert!(
            worst_l1 <= pack.scalar_l1_bound(),
            "‖Ecd(a)‖₁ {worst_l1} exceeds (b+2)r/2 = {}",
            pack.scalar_l1_bound()
        );
    }

    /// The `p − 1` branch of Alg. 1 collapses to the single monomial `−Xⁱ`:
    /// digit `b` centered to `0`, its carry pushed through `Xᵈ = −1`.
    #[test]
    fn the_top_of_the_range_encodes_to_one_negative_monomial() {
        let pack = packing();
        let mut msg = vec![0u64; pack.lanes()];
        msg[3] = P - 1;
        let rings: Vec<PolyRing<Q5, D>> = pack.encode(&msg).expect("aligned");
        let coeffs = flat(&rings[0]);
        assert_eq!(coeffs[3].centered(), -1, "lane 3 must hold −X³");
        for (i, c) in coeffs.iter().enumerate() {
            if i != 3 {
                assert_eq!(c.centered(), 0, "stray coefficient at {i}");
            }
        }
        assert_eq!(pack.decode(&rings).expect("decode"), msg);
    }

    #[test]
    fn decode_is_additive_over_the_ring() {
        // `Dcd` is a Z-module map, so `Dcd(a + a') = Dcd(a) + Dcd(a')` — the
        // linearity behind `A₀·e = Σᵢ Ecd(xⁿⁱ)·mᵢ` being checkable at all.
        let pack = packing();
        let a = values(1, pack.lanes());
        let b = values(2, pack.lanes());
        let ra: Vec<PolyRing<Q5, D>> = pack.encode(&a).expect("ok");
        let rb: Vec<PolyRing<Q5, D>> = pack.encode(&b).expect("ok");
        let sum: Vec<PolyRing<Q5, D>> = ra
            .iter()
            .zip(rb.iter())
            .map(|(x, y)| {
                PolyRing::from_coefficients(
                    flat(x).iter().zip(flat(y)).map(|(p, q)| *p + q).collect(),
                )
            })
            .collect();
        let want: Vec<u64> = a
            .iter()
            .zip(b.iter())
            .map(|(x, y)| pack.add(*x, *y))
            .collect();
        assert_eq!(pack.decode(&sum).expect("decode"), want);
    }

    #[test]
    fn decode_is_a_ring_homomorphism() {
        // Identity 2: `Dcd(a·u) = Dcd(a) ⊛ Dcd(u)` in `Z_p[X]/(X^{d/r} − b)`,
        // where `⊛` multiplies the lane polynomials and folds degree `d/r` back
        // with weight `b` — i.e. literally `X^{d/r} = b`.
        let pack = packing();
        let stride = pack.lanes();
        for seed in 0..8u64 {
            let a = values(seed, stride);
            let u = values(seed + 100, stride);
            let ua: Vec<PolyRing<Q5, D>> = pack.encode(&a).expect("ok");
            let uu: Vec<PolyRing<Q5, D>> = pack.encode(&u).expect("ok");
            let product = vec![ua[0].clone() * uu[0].clone()];
            let lhs = pack.decode(&product).expect("ok");
            let mut tmp = vec![0u128; 2 * stride - 1];
            for i in 0..stride {
                for j in 0..stride {
                    tmp[i + j] += u128::from(a[i]) * u128::from(u[j]);
                }
            }
            for k in (stride..tmp.len()).rev() {
                tmp[k - stride] += tmp[k] * u128::from(pack.base());
            }
            let rhs: Vec<u64> = tmp[..stride]
                .iter()
                .map(|v| (v % u128::from(P)) as u64)
                .collect();
            assert_eq!(lhs, rhs, "seed {seed}");
        }
    }

    #[test]
    fn scalar_pinning() {
        // Identity 3, the one `PC.Eval` cannot be written without: multiplying
        // by `Ecd(s)` scales *every* decoded lane by `s` rather than scrambling
        // the lane structure the way a generic ring product would.
        let pack = packing();
        for seed in 0..10u64 {
            let s = values(seed, 1)[0];
            let msg = values(seed + 50, 2 * pack.lanes());
            let alpha = pack.encode_scalar::<Q5, D>(s).expect("aligned");
            let hh: Vec<PolyRing<Q5, D>> = pack.encode(&msg).expect("aligned");
            let e: Vec<PolyRing<Q5, D>> = hh.iter().map(|h| alpha.clone() * h.clone()).collect();
            let want: Vec<u64> = msg.iter().map(|v| pack.mul(*v, s)).collect();
            assert_eq!(pack.decode(&e).expect("decode"), want, "seed {seed}");
        }
    }

    #[test]
    fn decode_doubled_matches_decode() {
        let pack = packing();
        let msg = values(9, 2 * pack.lanes());
        let rings: Vec<PolyRing<Q5, D>> = pack.encode(&msg).expect("ok");
        assert_eq!(pack.decode_doubled(&rings).expect("ok"), msg);
        let two = Q5::ONE + Q5::ONE;
        let doubled: Vec<PolyRing<Q5, D>> = rings.iter().map(|r| scaled(r, two)).collect();
        assert_eq!(
            pack.decode(&doubled).expect("ok"),
            msg.iter().map(|v| pack.mul(*v, 2)).collect::<Vec<_>>(),
            "Dcd must be Z-linear in the doubling"
        );
    }

    #[test]
    fn the_sqrt_split_evaluation_claim_holds() {
        // Identities 2+3 composed at the shape §4.1 `PC.Eval` uses: with
        // `e = Σᵢ Ecd(xⁿⁱ)·hhᵢ`, the fold of `Dcd(e)` against `(1,x,…,xⁿ⁻¹)` is
        // exactly `h(x)`, and each decoded entry is the folded block sum.
        let pack = packing();
        let (blocks, per_block) = (4usize, 2 * pack.lanes());
        for seed in 0..6u64 {
            let h = values(seed, blocks * per_block);
            let x = values(seed + 77, 1)[0];
            let encoded: Vec<Vec<PolyRing<Q5, D>>> = pack
                .blocks(&h, blocks)
                .expect("aligned")
                .iter()
                .map(|b| pack.encode(b).expect("aligned"))
                .collect();
            let weights = pack.block_weights(x, per_block, blocks);
            let zero = PolyRing::<Q5, D>::from_coefficients(vec![Q5::ZERO; D]);
            let mut e = vec![zero.clone(); encoded[0].len()];
            for (row, w) in encoded.iter().zip(weights.iter()) {
                let alpha = pack.encode_scalar::<Q5, D>(*w).expect("aligned");
                for (acc, v) in e.iter_mut().zip(row.iter()) {
                    *acc = acc.clone() + alpha.clone() * v.clone();
                }
            }
            let decoded = pack.decode(&e).expect("decode");
            let folded: Vec<u64> = (0..per_block)
                .map(|j| {
                    weights.iter().enumerate().fold(0u64, |acc, (i, w)| {
                        pack.add(acc, pack.mul(*w, h[i * per_block + j]))
                    })
                })
                .collect();
            assert_eq!(decoded, folded, "decoded blocks differ, seed {seed}");
            assert_eq!(
                pack.eval_fold(&decoded, x),
                pack.eval_at(&h, x),
                "y != h(x), seed {seed}"
            );
        }
    }

    #[test]
    fn blocks_and_recombine_round_trip() {
        let pack = packing();
        let h = values(4, 8 * pack.lanes());
        let split = pack.blocks(&h, 4).expect("divides");
        assert_eq!(split.len(), 4);
        assert_eq!(split[2].len(), 2 * pack.lanes());
        assert_eq!(pack.recombine(&split, split[0].len()).expect("uniform"), h);
        // `PC.Open` step 4 is literally "the recombined decode equals `h`".
        let encoded: Vec<PolyRing<Q5, D>> = split
            .iter()
            .flat_map(|b| pack.encode(b).expect("aligned"))
            .collect();
        let decoded = pack.decode(&encoded).expect("decode");
        let per = decoded.len() / 4;
        let rows: Vec<&[u64]> = decoded.chunks(per).collect();
        assert_eq!(pack.recombine(&rows, per).expect("uniform"), h);
    }

    #[test]
    fn field_helpers_agree_with_a_typed_prime_field() {
        // `p` is a *runtime* modulus here, so the arithmetic is hand written;
        // pin it against the crate's const-generic `Zq<p>`.
        type ZP = Zq<1_944_810_001>;
        let pack = packing();
        assert!(<ZP as Ring>::IS_PRIME, "the typed ring must agree");
        for seed in 0..40u64 {
            let a = values(seed, 1)[0];
            let b = values(seed + 1, 1)[0];
            let ta = <ZP as From<u64>>::from(a);
            let tb = <ZP as From<u64>>::from(b);
            assert_eq!(pack.add(a, b), (ta + tb).to_u128() as u64, "add");
            assert_eq!(pack.mul(a, b), (ta * tb).to_u128() as u64, "mul");
            assert_eq!(pack.pow(a, 3), (ta * ta * ta).to_u128() as u64, "pow");
        }
        assert_eq!(pack.mul(2, pack.half()), 1, "half must be 2⁻¹ mod p");
    }

    #[test]
    fn works_on_a_non_ntt_friendly_ring() {
        // CELPC's own modulus is 112 bits, unrepresentable here, so the toy
        // `q` is a structural stand-in — and deliberately the *house non-NTT*
        // one: `2³² − 99 ≡ 5 (mod 8)` has 2-adicity 2, hence no NTT at degree
        // `≥ 4`, so every ring product in the identities above runs schoolbook.
        assert_eq!(Q5::MODULUS % 8, 5);
        assert_eq!((Q5::MODULUS - 1).trailing_zeros(), 2);
        assert!(
            !PolyRing::<Q5, D>::is_ntt_available(),
            "this instance must have no NTT, or the test proves nothing"
        );
        assert!(PolyRing::<Z1, 8>::is_ntt_available());

        let pack = packing();
        for seed in 0..3u64 {
            let msg = values(seed, 2 * pack.lanes());
            let s = values(seed + 9, 1)[0];
            let a: Vec<PolyRing<Q5, D>> = pack.encode(&msg).expect("ok");
            let b: Vec<PolyRing<Z1, D>> = pack.encode(&msg).expect("same digits, other q");
            let centered = |v: &[Q5]| -> Vec<i64> { v.iter().map(|c| c.centered()).collect() };
            let centered1 = |v: &[Z1]| -> Vec<i64> { v.iter().map(|c| c.centered()).collect() };
            assert_eq!(
                centered(&to_coeffs::<Q5, D>(&a)),
                centered1(&to_coeffs::<Z1, D>(&b)),
                "the digits must not depend on q"
            );
            let alpha = pack.encode_scalar::<Q5, D>(s).expect("ok");
            let e: Vec<PolyRing<Q5, D>> = a.iter().map(|h| alpha.clone() * h.clone()).collect();
            let want: Vec<u64> = msg.iter().map(|v| pack.mul(*v, s)).collect();
            assert_eq!(
                pack.decode(&e).expect("ok"),
                want,
                "pinning on d=64, no NTT"
            );
        }
    }

    #[test]
    fn parameter_validation_reports_each_condition_separately() {
        assert_eq!(LanePacking::new(1, 4, 64), Err(ParamError::BaseTooSmall(1)));
        assert_eq!(
            LanePacking::new(210, 0, 64),
            Err(ParamError::DigitsNotDivisor {
                digits: 0,
                ring_degree: 64
            })
        );
        assert_eq!(
            LanePacking::new(210, 5, 64),
            Err(ParamError::DigitsNotDivisor {
                digits: 5,
                ring_degree: 64
            })
        );
        // r odd ⇒ bʳ+1 = (b+1)(…): composite for every b ≥ 2.
        assert_eq!(
            LanePacking::new(210, 3, 60),
            Err(ParamError::NotAField(210u64.pow(3) + 1))
        );
        // 266⁴+1 is prime but past the 2³² ceiling.
        assert_eq!(
            LanePacking::new(266, 4, 64),
            Err(ParamError::ModulusTooLarge {
                modulus: 266u64.pow(4) + 1,
                limit: MAX_MESSAGE_MODULUS
            })
        );
        assert_eq!(
            LanePacking::new(1u64 << 32, 2, 64),
            Err(ParamError::ModulusOverflow {
                base: 1u64 << 32,
                digits: 2
            })
        );
    }

    #[test]
    fn inputs_outside_the_message_field_are_refused() {
        let pack = packing();
        let lanes = pack.lanes();
        assert_eq!(
            pack.encode::<Q5, D>(&[0; 3]),
            Err(PackError::Misaligned {
                got: 3,
                lane: lanes
            })
        );
        let mut bad = vec![0u64; lanes];
        bad[2] = P;
        assert_eq!(
            pack.encode::<Q5, D>(&bad),
            Err(PackError::OutOfRange {
                value: P,
                modulus: P
            })
        );
        assert_eq!(
            pack.encode_scalar::<Q5, D>(P),
            Err(PackError::OutOfRange {
                value: P,
                modulus: P
            })
        );
        // A packing built for another degree must not be used on this ring.
        let other = LanePacking::new(BASE, DIGITS, 32).expect("valid at d = 32");
        assert_eq!(
            other.encode::<Q5, D>(&values(1, lanes)),
            Err(PackError::WrongRingDegree {
                expected: 32,
                got: 64
            })
        );
        assert_eq!(
            pack.blocks(&values(1, 10), 4),
            Err(PackError::RaggedBlocks { got: 10, blocks: 4 })
        );
        let row = values(1, 4);
        assert_eq!(
            pack.recombine(&[row.as_slice(), row.as_slice()], 5),
            Err(PackError::RaggedRows {
                got: 4,
                expected: 5
            })
        );
    }

    #[test]
    fn uniform_preimages_are_in_range_and_bound_to_the_seed() {
        let pack = packing();
        let a = pack.uniform_preimages(b"g", &[1u8; 32], 64);
        assert_eq!(a, pack.uniform_preimages(b"g", &[1u8; 32], 64));
        assert_ne!(
            a,
            pack.uniform_preimages(b"g", &[2u8; 32], 64),
            "the seed must bind the masks"
        );
        assert_ne!(
            a,
            pack.uniform_preimages(b"h", &[1u8; 32], 64),
            "the label must domain-separate the mask streams"
        );
        assert!(a.iter().all(|v| *v < P));
    }

    #[test]
    fn uniform_below_is_exact_over_a_power_of_two_bound() {
        // `bound | 2¹²⁸` means no draw is ever rejected, so the output is
        // uniform by construction; check coverage over a small bound anyway.
        let mut xof = Shake256Xof::new(b"ub");
        let mut seen = [0u32; 8];
        for _ in 0..8000 {
            let v = uniform_below(&mut xof, 8);
            seen[usize::try_from(v).expect("in range")] += 1;
        }
        assert!(seen.iter().all(|c| *c > 700), "skewed: {seen:?}");
        assert_eq!(uniform_below(&mut Shake256Xof::new(b"x"), 1), 0);
    }
}
