//! Fold geometry: the challenge subring, the carrier contraction, sparse
//! folding challenges and the response envelopes (eprint 2026/1983 §3.1, §3.2,
//! §5.2, §5.4, Appendix G).
//!
//! # One challenge, two rings
//!
//! Akita's split-and-fold samples each block challenge `c_i` in the *challenge
//! subring* `S = Z_q[Y]/(Y^{d_car} + 1)` and lets the same polynomial act twice:
//! as `c_i(Y)` in the carrier consistency row and as `iota(c_i) = c_i(X^{kh})`
//! in the inner-commitment rows (Eq. 90). That is only sound because the
//! embedding `iota: Y -> X^{kh}` (Eq. 47) preserves units, coefficient norms and
//! the multiplication operator norm (Lemma 3.2), and it only *works* because the
//! contraction `L` of Eq. (87) is `S`-linear:
//!
//! ```text
//! L(iota(c) * F) = c * L(F)   in S                      (Eq. 91)
//! L(Z)           = sum_i c_i L(F_i)   for Z = sum_i iota(c_i) F_i   (Eq. 93)
//! ```
//!
//! so evaluating before folding equals folding before evaluating. Eq. (150)'s
//! consequence — the *same* challenge is read as `c_i(alpha)` in the carrier row
//! and as `c_i(alpha^{kh})` in the `A` rows — is pinned here, because reusing one
//! evaluation for both is a silent soundness break that no test of either row
//! alone would catch.
//!
//! # Challenges are sparse, signed, and filtered
//!
//! §3.2's family draws a uniform support, assigns fixed magnitudes to disjoint
//! blocks of it, and randomizes signs, giving `|C| = binom(d,s) * s!/prod(n_a!)
//! * 2^s` members with `||c||_inf = c_max` and `||c||_1 = omega`. Euclidean
//! profiles may restrict it further to an operator-norm subfamily
//! `C_acc = {c in C_0 : OpNormAccept(c)}` (Eq. 49). Two obligations come with
//! that, and both are computed here rather than assumed:
//!
//! * a **certified lower bound on `|C_acc|`** — the cardinality function and the
//!   exhaustive enumeration agree, so the special-soundness denominator the
//!   schedule charges is real;
//! * **invertibility of every nonzero pairwise difference** (§3.2: "the admitted
//!   challenge family must satisfy this condition at the selected modulus",
//!   Appendix D's pairwise-unit certificate) — checked exhaustively through the
//!   negacyclic multiplication matrix, and the test shows the certificate
//!   *rejecting* a family that is one magnitude too wide.
//!
//! # The two response bounds are different numbers
//!
//! §5.4: the honest prover's canonical digits give `[-M_f, T_f]` (Eq. 111), but
//! the verifier only enforces the wider `A_{b*}` alphabet, so every *accepted*
//! response sits inside [`cert_envelope`] and two accepted responses inside
//! [`cert_difference`]. Those, not the honest threshold, feed the Module-SIS
//! collision radius (Eq. 79). [`envelope`] implements Corollary G.6's deterministic
//! honest bounds `U = sum_a K_1,a B_a` and `D = (sum_a Gamma_a sqrt(E_a))^2` that
//! make the honest admission probability one.

use crate::pcs::ring_reduce::nega_mul;
use algebra::crypto::sampling::BitStream;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::traits::CenteredRing;
use algebra::ring::Field;
use algebra::ring::Ring;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Why a geometry or sampling request was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeomError {
    /// `d_A != k * h_car * d_car`, so the subring does not embed (Eq. 84).
    BadPacking {
        /// Ambient dimension supplied.
        d_a: usize,
        /// `k * h_car * d_car` the packing requires.
        required: usize,
    },
    /// A padding factor vanished, so the padded claim carries no information
    /// (§5.1: such a claim "must remain in a separate natural-dimension
    /// instance").
    ZeroPaddingFactor,
    /// The bounded fixed-filter sampler produced no accepted challenge within
    /// its draw allowance (§10.1's `1 - (1 - alpha)^L` failure event).
    SamplerExhausted {
        /// Coordinates the sampler was asked for.
        coordinates: usize,
    },
    /// A pairwise difference of two family members is not invertible.
    ZeroDivisorDifference {
        /// Index of the first member.
        left: usize,
        /// Index of the second member.
        right: usize,
    },
}

impl fmt::Display for GeomError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GeomError::BadPacking { d_a, required } => write!(
                f,
                "d_A = {d_a} but the packing requires k*h_car*d_car = {required}"
            ),
            GeomError::ZeroPaddingFactor => {
                f.write_str("a claim with a zero padding factor cannot be batched")
            }
            GeomError::SamplerExhausted { coordinates } => {
                write!(f, "no accepted challenge for {coordinates} coordinates")
            }
            GeomError::ZeroDivisorDifference { left, right } => write!(
                f,
                "members {left} and {right} differ by a non-unit, so extraction breaks"
            ),
        }
    }
}

/// The coefficient-packing geometry of Eq. (84)-(86): `d_A = k * h_car * d_car`.
///
/// `k` is the extension degree (this crate can only run `k = 1`, see the module
/// notes in [`crate::pcs::split_fold`]), `h_car` the base-field width reduction
/// and `d_car` the carrier dimension that decides the challenge family (§3.2:
/// "it is `d_car`, rather than the A-ring dimension `d_A`, that determines the
/// family").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Packing {
    /// Extension degree `k`.
    pub k: usize,
    /// Embedding height `h_car`.
    pub h_car: usize,
    /// Carrier / challenge-subring dimension `d_car`.
    pub d_car: usize,
}

impl Packing {
    /// The ambient `A`-ring dimension this packing requires.
    pub const fn d_a(&self) -> usize {
        self.k * self.h_car * self.d_car
    }

    /// The stride of the embedding `iota: Y -> X^{k h_car}` (Eq. 47).
    pub const fn stride(&self) -> usize {
        self.k * self.h_car
    }

    /// Checks `d_A = k h_car d_car` (Eq. 84) — the divisibility the schedule
    /// calls "admissible".
    ///
    /// # Errors
    /// [`GeomError::BadPacking`] if the ambient dimension does not match.
    pub const fn admit(&self, d_a: usize) -> Result<(), GeomError> {
        if d_a == self.d_a() {
            Ok(())
        } else {
            Err(GeomError::BadPacking {
                d_a,
                required: self.d_a(),
            })
        }
    }

    /// Splits an ambient coefficient index `ell < d_A` into the carrier index
    /// `j` and the packed index `a` of Eq. (86): `ell = a + k h_car j`.
    ///
    /// # Panics
    /// If `ell >= d_a()`.
    pub const fn split_index(&self, ell: usize) -> (usize, usize) {
        assert!(
            ell < self.d_a(),
            "coefficient index outside the ambient ring"
        );
        (ell % self.h_car, ell / self.h_car)
    }
}

/// `iota(c)`: `c(Y)` embedded into `R` by `Y -> X^stride` (Eq. 47).
///
/// A carrier of degree below `d_car` is just a sparse carrier, so short input
/// is legal — the zero-padded image is what the embedding of that polynomial
/// *is*. `c.len() * stride == d_a` is the *full*-tiling case and is what
/// [`Packing::admit`] pins for a packing, not a precondition here.
///
/// # Panics
/// If the image would not fit the ambient ring (`c.len() * stride > d_a`).
pub fn embed<R: Ring>(c: &[R], stride: usize, d_a: usize) -> Vec<R> {
    assert!(
        c.len() * stride <= d_a,
        "the carrier does not fit the ambient ring: {} coefficients at stride \
         {} need {}, but d_a = {}",
        c.len(),
        stride,
        c.len() * stride,
        d_a,
    );
    let mut out = vec![R::ZERO; d_a];
    for (j, &x) in c.iter().enumerate() {
        out[stride * j] = x;
    }
    out
}

/// The contraction `L` of Eq. (87) applied to one ring polynomial: the packed
/// axis is evaluated at `rpack`, the carrier axis survives.
///
/// # Panics
/// If `p.len() != d_a()`.
pub fn contract_polynomial<R: Ring>(p: &[R], eqpack: &[R], packing: &Packing) -> Vec<R> {
    assert_eq!(p.len(), packing.d_a(), "one ambient ring polynomial");
    assert_eq!(eqpack.len(), packing.h_car * packing.k, "eqpack arity");
    let mut out = vec![R::ZERO; packing.d_car];
    for (ell, &coef) in p.iter().enumerate() {
        let (a, j) = packing.split_index(ell);
        out[j] += eqpack[a] * coef;
    }
    out
}

/// The block partial `e_i(Y)` of Eq. (87): contract the within-block position
/// axis with `eqpos` and the packed axis with `eqpack`.
///
/// `block` holds `m` ambient ring polynomials, flat, `m * d_A` coefficients.
///
/// # Panics
/// If `block.len() != m * d_a`.
pub fn block_partial<R: Ring>(
    block: &[R],
    m: usize,
    eqpos: &[R],
    eqpack: &[R],
    packing: &Packing,
) -> Vec<R> {
    assert_eq!(block.len(), m * packing.d_a(), "block flat length");
    assert_eq!(eqpos.len(), m, "one position weight per ring element");
    let mut out = vec![R::ZERO; packing.d_car];
    for x in 0..m {
        let part = contract_polynomial(
            &block[x * packing.d_a()..(x + 1) * packing.d_a()],
            eqpack,
            packing,
        );
        for (acc, v) in out.iter_mut().zip(part) {
            *acc += eqpos[x] * v;
        }
    }
    out
}

/// The folded response of Eq. (104): `z[col] = sum_{c,i} c_{c,i} * s_{c,i}[col]`
/// with each product taken in the `A` ring.
///
/// `sources` is one flat `m_A * d_A` vector per challenged block; `challenges`
/// is the matching list of ambient-ring challenges (already embedded with
/// [`embed`] when the fold is a packing fold).
///
/// # Panics
/// If the lists have different lengths or a source is mis-sized.
pub fn fold_sources<R: Ring>(
    challenges: &[Vec<R>],
    sources: &[Vec<R>],
    m_a: usize,
    d_a: usize,
) -> Vec<R> {
    assert_eq!(challenges.len(), sources.len(), "one challenge per block");
    let mut out = vec![R::ZERO; m_a * d_a];
    for (c, s) in challenges.iter().zip(sources.iter()) {
        assert_eq!(s.len(), m_a * d_a, "source block flat length");
        for col in 0..m_a {
            let prod = nega_mul(c, &s[col * d_a..(col + 1) * d_a], d_a);
            for (acc, v) in out[col * d_a..(col + 1) * d_a]
                .iter_mut()
                .zip(prod.into_iter())
            {
                *acc += v;
            }
        }
    }
    out
}

/// `eqq(r, index)` — the multilinear equality polynomial at the `bits`-bit
/// encoding of `index`, most significant bit first (the convention every
/// address map in this module uses).
///
/// # Panics
/// If `bits > r.len()` or `index >= 2^bits`.
pub fn eq_weight<R: Ring>(r: &[R], index: usize, bits: usize) -> R {
    assert!(r.len() >= bits, "the point needs one coordinate per bit");
    assert!(
        bits >= 64 || index < (1usize << bits),
        "index outside the bit width"
    );
    let mut acc = R::ONE;
    for j in 0..bits {
        let bit = (index >> (bits - 1 - j)) & 1 == 1;
        acc *= if bit { r[j] } else { R::ONE - r[j] };
    }
    acc
}

/// The `2^bits` table of `eqq(r, .)`, i.e. the Boolean evaluations of the
/// equality polynomial — a sum-check factor.
pub fn eq_table<R: Ring>(r: &[R], bits: usize) -> Vec<R> {
    (0..1usize << bits).map(|x| eq_weight(r, x, bits)).collect()
}

/// The flat address of Eq. (107): a value of base-field width `D` stored in
/// native blocks of dimension `d`, item `j`, native subcolumn `y`, digit `u`,
/// coefficient `k`.
///
/// # Panics
/// If any index is outside its declared range.
pub fn address(j: usize, y: usize, u: usize, k: usize, s: usize, delta: usize, d: usize) -> usize {
    assert!(y < s && u < delta && k < d, "address index out of range");
    ((j * s + y) * delta + u) * d + k
}

/// Eq. (71): the equality weight on a flat address `i * m + x` separates into
/// its block factor and its within-block factor.
pub fn eq_factorization<R: Ring>(r_blk: &[R], i: usize, r_pos: &[R], x: usize) -> R {
    eq_weight(r_blk, i, r_blk.len()) * eq_weight(r_pos, x, r_pos.len())
}

/// All `k`-subsets of `items`, ascending within each subset.
fn combinations(items: &[usize], k: usize) -> Vec<Vec<usize>> {
    let mut out: Vec<Vec<usize>> = Vec::new();
    let mut chosen: Vec<usize> = Vec::with_capacity(k);
    combine_from(items, 0, k, &mut chosen, &mut out);
    out
}

fn combine_from(
    items: &[usize],
    start: usize,
    k: usize,
    chosen: &mut Vec<usize>,
    out: &mut Vec<Vec<usize>>,
) {
    if chosen.len() == k {
        out.push(chosen.clone());
        return;
    }
    let remaining = k - chosen.len();
    for i in start..items.len() {
        if items.len() - i < remaining {
            break;
        }
        chosen.push(items[i]);
        combine_from(items, i + 1, k, chosen, out);
        chosen.pop();
    }
}

/// `ceil(log2(n + 1))`: the bit width a rejection draw must read to reach every
/// value in `[0, n)`.
const fn bit_width_of(limit: u64) -> u32 {
    let mut bits = 0u32;
    while (1u128 << bits) <= limit as u128 {
        bits += 1;
    }
    bits
}

/// The signed-sparse folding-challenge shell of §3.2: dimension `dim`, and for
/// each allowed magnitude `a` the number `n_a` of support coordinates carrying
/// it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Shell {
    /// The ring dimension the family lives in (`d_car` at a packing fold).
    pub dim: usize,
    /// `(magnitude, count)` pairs, magnitudes ascending and positive.
    pub magnitudes: Vec<(u64, usize)>,
}

impl Shell {
    /// Declares a shell, rejecting the degenerate shapes the protocol never
    /// admits.
    ///
    /// # Panics
    /// If a magnitude is zero, a count is zero, magnitudes repeat or are
    /// unordered, or the support exceeds the dimension.
    pub fn new(dim: usize, magnitudes: &[(u64, usize)]) -> Self {
        assert!(dim >= 1, "a challenge needs at least one coefficient");
        assert!(!magnitudes.is_empty(), "an empty family has no challenges");
        for w in magnitudes.windows(2) {
            assert!(w[0].0 < w[1].0, "magnitudes must be ascending and distinct");
        }
        assert!(magnitudes[0].0 >= 1, "a zero magnitude is not a magnitude");
        let s: usize = magnitudes.iter().map(|&(_, n)| n).sum();
        assert!(s >= 1 && s <= dim, "the support must lie in [1, d]");
        Self {
            dim,
            magnitudes: magnitudes.to_vec(),
        }
    }

    /// Total support size `s = sum_a n_a`.
    pub fn support(&self) -> usize {
        self.magnitudes.iter().map(|&(_, n)| n).sum()
    }

    /// The mass `omega = sum_a a * n_a`, which bounds `||c||_1` and hence the
    /// deterministic response growth (§3.2, §4.4's challenge norms).
    pub fn omega(&self) -> u64 {
        self.magnitudes.iter().map(|&(a, n)| a * n as u64).sum()
    }

    /// `c_max = max A+`.
    pub fn c_max(&self) -> u64 {
        self.magnitudes.iter().map(|&(a, _)| a).max().unwrap_or(0)
    }

    /// `|C| = binom(d, s) * s! / prod_a n_a! * 2^s` (§3.2).
    pub fn cardinality(&self) -> u128 {
        let s = self.support();
        let choose = binomial(self.dim, s);
        let mut multinomial = factorial(s);
        for &(_, n) in self.magnitudes.iter() {
            multinomial /= factorial(n);
        }
        choose
            .saturating_mul(multinomial)
            .saturating_mul(1u128 << s)
    }

    /// Every member of the shell, exhaustively (the fixture the cardinality and
    /// unit-difference certificates are checked against).
    ///
    /// Enumerates ordered tuples `(S_a)_a` of disjoint supports of the declared
    /// sizes — `d! / ((d-s)! prod_a n_a!)` of them — times `2^s` sign patterns,
    /// which is exactly the family counted by [`Shell::cardinality`].
    pub fn enumerate<R: Ring>(&self) -> Vec<Vec<R>> {
        let mut assignments: Vec<Vec<(usize, u64)>> = vec![Vec::new()];
        for &(magnitude, count) in self.magnitudes.iter() {
            let mut next: Vec<Vec<(usize, u64)>> = Vec::new();
            for chosen in assignments.iter() {
                let used: Vec<bool> = {
                    let mut u = vec![false; self.dim];
                    for &(p, _) in chosen.iter() {
                        u[p] = true;
                    }
                    u
                };
                let free: Vec<usize> = (0..self.dim).filter(|p| !used[*p]).collect();
                for sub in combinations(&free, count) {
                    let mut grown = chosen.clone();
                    grown.extend(sub.into_iter().map(|p| (p, magnitude)));
                    next.push(grown);
                }
            }
            assignments = next;
        }
        let s = self.support();
        let mut out = Vec::with_capacity(assignments.len() * (1 << s));
        for chosen in assignments.iter() {
            for signs in 0..(1u32 << s) {
                let mut c = vec![R::ZERO; self.dim];
                for (idx, &(pos, mag)) in chosen.iter().enumerate() {
                    let v = R::from(mag);
                    c[pos] = if (signs >> idx) & 1 == 1 { -v } else { v };
                }
                out.push(c);
            }
        }
        out
    }

    /// Whether `c` lies in the shell's *operator-norm accepted subfamily* with
    /// squared threshold `gamma_sq` (Eq. 49's predicate, with the certified
    /// upper bound of [`op_norm_upper_sq`] in place of the exact spectral norm).
    pub fn accepts<R: CenteredRing>(&self, c: &[R], gamma_sq: u128) -> bool {
        self.in_shell(c) && op_norm_upper_sq(c) <= gamma_sq
    }

    /// Whether `c` is a shell member at all (support, magnitudes, nothing extra).
    pub fn in_shell<R: CenteredRing>(&self, c: &[R]) -> bool {
        if c.len() != self.dim {
            return false;
        }
        let mut need: Vec<(u64, usize)> = self.magnitudes.clone();
        for x in c {
            if x.centered() == 0 {
                continue;
            }
            let mag = x.abs_infinity();
            match need.iter_mut().find(|(a, n)| *a == mag && *n > 0) {
                Some((_, n)) => *n -= 1,
                None => return false,
            }
        }
        need.iter().all(|&(_, n)| n == 0)
    }

    /// Draws one shell challenge, exactly as §3.2's three steps: a uniform
    /// support via partial Fisher-Yates with exact bounded integers, magnitudes
    /// assigned in class order, then `s` independent sign bits. Draws come from
    /// a domain-separated XOF stream indexed by `(seed, nonce, coordinate)`,
    /// which is what makes each coordinate a separately indexed query (§4.2's
    /// transcript rule) rather than one absorbed vector.
    ///
    /// `allowance` bounds the completed shell draws when `gamma_sq` filters
    /// (Lemma 10.1's `L`); an unfiltered call uses `allowance = 1`.
    ///
    /// # Errors
    /// [`GeomError::SamplerExhausted`] if no draw passes the filter.
    pub fn sample<R: Ring + CenteredRing>(
        &self,
        seed: &[u8; 32],
        nonce: u64,
        coordinate: usize,
        allowance: usize,
        gamma_sq: Option<u128>,
    ) -> Result<Vec<R>, GeomError> {
        let mut xof = Shake256Xof::new(b"lattice-algebra/akita/challenge");
        xof.absorb(seed);
        xof.absorb(&nonce.to_le_bytes());
        xof.absorb(&(coordinate as u64).to_le_bytes());
        let mut stream = BitStream::new(&mut xof);
        let draws = if gamma_sq.is_some() {
            allowance.max(1)
        } else {
            1
        };
        for _ in 0..draws {
            let c = self.draw_one(&mut stream);
            let accepted = match gamma_sq {
                Some(g) => op_norm_upper_sq(&c) <= g,
                None => true,
            };
            if accepted {
                return Ok(c);
            }
        }
        Err(GeomError::SamplerExhausted {
            coordinates: coordinate + 1,
        })
    }

    fn draw_one<R: Ring + CenteredRing>(&self, stream: &mut BitStream<'_, Shake256Xof>) -> Vec<R> {
        let s = self.support();
        let mut positions: Vec<usize> = (0..self.dim).collect();
        // partial Fisher-Yates over the first s slots, each an exact uniform
        // integer in the remaining range
        for slot in 0..s {
            let pick = bounded_index(stream, (self.dim - slot) as u64) as usize + slot;
            positions.swap(slot, pick);
        }
        let mut c = vec![R::ZERO; self.dim];
        let mut slot = 0usize;
        for &(magnitude, count) in self.magnitudes.iter() {
            for _ in 0..count {
                let sign = bounded_index(stream, 2) == 1;
                let v = R::from(magnitude);
                c[positions[slot]] = if sign { -v } else { v };
                slot += 1;
            }
        }
        c
    }
}

/// A uniform index in `[0, n)` by bit-level rejection (never modulo bias).
///
/// # Panics
/// If `n == 0`.
fn bounded_index<X: Xof>(stream: &mut BitStream<'_, X>, n: u64) -> u64 {
    assert!(n > 0, "cannot draw from an empty range");
    if n == 1 {
        return 0;
    }
    let bits = bit_width_of(n - 1);
    loop {
        let mut raw = 0u64;
        for _ in 0..bits {
            raw = (raw << 1) | u64::from(stream.read_bits(1));
        }
        if raw < n {
            return raw;
        }
    }
}

/// The `||c||_1` and `||c||_inf` invariants §3.2 claims for every member.
pub fn norms<R: CenteredRing>(c: &[R]) -> (u64, u64) {
    c.iter().fold((0u64, 0u64), |(l1, linf), x| {
        (l1 + x.abs_infinity(), linf.max(x.abs_infinity()))
    })
}

/// An exact certified upper bound on `||c||_{mul,2}^2`, the squared spectral
/// norm of negacyclic multiplication by `c`: the Gershgorin disk bound on the
/// integer matrix `M_c^T M_c`, all of whose entries are computed exactly.
///
/// This is the deterministic, witness-independent predicate Eq. (49) needs. It
/// replaces the general `||c||_{mul,2} <= ||c||_1` with an enforced threshold
/// `Gamma`, and it never claims more than it proves: the bound is an upper bound
/// on the same quantity Lemma 3.1's second Euclidean inequality prices, and the
/// test pins it against the cases whose spectral norm is exactly known
/// (monomials, `1 + X`).
pub fn op_norm_upper_sq<R: CenteredRing>(c: &[R]) -> u128 {
    let d = c.len();
    if d == 0 {
        return 0;
    }
    let cols: Vec<Vec<i128>> = (0..d)
        .map(|j| {
            (0..d)
                .map(|i| {
                    let src = if i >= j { i - j } else { i + d - j };
                    let sign = if i >= j { 1i128 } else { -1i128 };
                    sign * i128::from(c[src].centered())
                })
                .collect()
        })
        .collect();
    let mut best: u128 = 0;
    for i in 0..d {
        let mut row_sum: u128 = 0;
        for j in 0..d {
            let entry: i128 = (0..d).map(|t| cols[i][t] * cols[j][t]).sum();
            row_sum += entry.unsigned_abs();
        }
        best = best.max(row_sum);
    }
    best
}

/// Whether every nonzero pairwise difference of `members` is a unit in
/// `R_{q,d}` — the invertibility certificate §3.2 requires for extraction, and
/// the reason the admitted family must satisfy `2 c_max < q^{1/s}/sqrt(s)`.
///
/// Invertibility is decided exactly, by ranking the negacyclic multiplication
/// matrix over the prime field.
///
/// # Errors
/// [`GeomError::ZeroDivisorDifference`] naming the first offending pair.
pub fn pairwise_unit_certificate<R: Field>(members: &[Vec<R>], d: usize) -> Result<(), GeomError> {
    for (left, a) in members.iter().enumerate() {
        for (right, b) in members.iter().enumerate().skip(left + 1) {
            let diff: Vec<R> = a.iter().zip(b).map(|(x, y)| *x - *y).collect();
            if diff.iter().all(|v| *v == R::ZERO) {
                continue;
            }
            if !is_unit(&diff, d) {
                return Err(GeomError::ZeroDivisorDifference { left, right });
            }
        }
    }
    Ok(())
}

/// Whether multiplication by `c` is invertible in `R_{q,d}`, by exact Gaussian
/// elimination on its negacyclic convolution matrix.
pub fn is_unit<R: Field>(c: &[R], d: usize) -> bool {
    let mut m: Vec<Vec<R>> = (0..d)
        .map(|j| {
            (0..d)
                .map(|i| {
                    let src = if i >= j { i - j } else { i + d - j };
                    let sign = if i >= j { R::ONE } else { -R::ONE };
                    sign * c[src]
                })
                .collect()
        })
        .collect();
    let mut rank_row = 0usize;
    for col in 0..d {
        let pivot = (rank_row..d).find(|&r| m[r][col] != R::ZERO);
        let Some(pivot) = pivot else { continue };
        m.swap(rank_row, pivot);
        let inv = m[rank_row][col]
            .inverse()
            .expect("nonzero pivot in a field");
        for v in m[rank_row].iter_mut() {
            *v *= inv;
        }
        for r in 0..d {
            if r != rank_row && m[r][col] != R::ZERO {
                let factor = m[r][col];
                let pivot: Vec<R> = m[rank_row].iter().copied().collect();
                for (dst, &pv) in m[r].iter_mut().zip(pivot.iter()) {
                    *dst -= factor * pv;
                }
            }
        }
        rank_row += 1;
    }
    rank_row == d
}

/// Corollary G.6's deterministic honest envelopes: the coefficient bound
/// `U = sum_a K_1,a * B_a` and the squared-norm bound
/// `D = (sum_a Gamma_a * sqrt(E_a))^2`.
///
/// `sqrt` is taken as a ceiling, so `D` over-estimates the paper's quantity: a
/// valid `S_max`, never an under-estimate that would let an honest response fail
/// admission. `gammas[i] = None` uses the unfiltered `Gamma = K_1` (§G.2:
/// "Without an operator filter one may always use Gamma = K1").
///
/// # Panics
/// If the input lists do not line up.
pub fn envelope(
    masses: &[u64],
    source_infs: &[u64],
    source_energies: &[u128],
    gammas: &[Option<u64>],
) -> (u128, u128) {
    assert!(
        masses.len() == source_infs.len()
            && masses.len() == source_energies.len()
            && masses.len() == gammas.len(),
        "one entry per challenged source"
    );
    let mut u: u128 = 0;
    let mut sqrt_sum: u128 = 0;
    for i in 0..masses.len() {
        let k1 = u128::from(masses[i]);
        u += k1 * u128::from(source_infs[i]);
        let gamma = u128::from(gammas[i].unwrap_or(masses[i]));
        sqrt_sum += gamma * ceil_sqrt(source_energies[i]);
    }
    (u, sqrt_sum.saturating_mul(sqrt_sum))
}

/// `ceil(sqrt(n))`, exact on `u128`.
pub fn ceil_sqrt(n: u128) -> u128 {
    if n == 0 {
        return 0;
    }
    let mut x = 1u128 << 64;
    loop {
        let next = (x + n / x) / 2;
        if next >= x {
            break;
        }
        x = next;
    }
    let root = x;
    if root.saturating_mul(root) >= n {
        root
    } else {
        root + 1
    }
}

fn binomial(n: usize, k: usize) -> u128 {
    if k > n {
        return 0;
    }
    let mut acc: u128 = 1;
    for i in 0..k {
        acc = acc * (n - i) as u128 / (i as u128 + 1);
    }
    acc
}

fn factorial(n: usize) -> u128 {
    (1..=n).fold(1u128, |a, b| a * b as u128)
}

/// §5.1's public admission condition on a padded claim: the verifier derives the
/// padding factor `phi` from the public layout and "rejects if it is zero",
/// because a claim with a vanishing factor authenticates no value at all. The
/// ordinary single opening has no semantic padding, so `phi = 1`.
///
/// # Errors
/// [`GeomError::ZeroPaddingFactor`] if the factor vanishes.
pub fn admit_padding<R: Ring>(phi: R) -> Result<R, GeomError> {
    if phi == R::ZERO {
        Err(GeomError::ZeroPaddingFactor)
    } else {
        Ok(phi)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    type Q32 = Zq<4_294_967_197>;
    type F17 = Zq<17>;

    fn packing() -> Packing {
        Packing {
            k: 1,
            h_car: 2,
            d_car: 4,
        }
    }

    fn rand_coeffs<R: Ring>(d: usize, seed: &mut u64) -> Vec<R> {
        (0..d)
            .map(|_| {
                *seed = seed
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                R::from((*seed >> 33) % R::MODULUS)
            })
            .collect()
    }

    #[test]
    fn packing_admits_only_the_stretched_dimension() {
        let p = packing();
        assert_eq!(p.d_a(), 8);
        assert_eq!(p.stride(), 2);
        assert_eq!(p.admit(8), Ok(()));
        assert_eq!(
            p.admit(16),
            Err(GeomError::BadPacking {
                d_a: 16,
                required: 8
            })
        );
        assert_eq!(p.split_index(5), (1, 2), "ell = a + stride * j");
        assert_eq!(p.split_index(0), (0, 0));
    }

    #[test]
    fn the_embedding_preserves_norms_and_multiplies() {
        // Lemma 3.2 parts 1-3 plus the Eq. (150) double evaluation.
        let p = packing();
        let mut seed = 2u64;
        for _ in 0..20 {
            let c: Vec<Q32> = rand_coeffs(p.d_car, &mut seed);
            let d: Vec<Q32> = rand_coeffs(p.d_car, &mut seed);
            let alpha: Q32 = rand_coeffs(1, &mut seed)[0];
            let (l1, linf) = norms(&c);
            let (el1, elinf) = norms(&embed(&c, p.stride(), p.d_a()));
            assert_eq!((l1, linf), (el1, elinf), "coefficient norms are preserved");
            // iota is a ring map
            let left = nega_mul(
                &embed(&c, p.stride(), p.d_a()),
                &embed(&d, p.stride(), p.d_a()),
                p.d_a(),
            );
            let right = embed(&nega_mul(&c, &d, p.d_car), p.stride(), p.d_a());
            assert_eq!(left, right, "iota(c) iota(d) = iota(cd)");
            // and it is evaluated at alpha^{kh} in the A ring
            let at_alpha = crate::pcs::ring_reduce::eval_poly(&left, alpha);
            let via_carrier = crate::pcs::ring_reduce::eval_poly(
                &nega_mul(&c, &d, p.d_car),
                alpha.pow(p.stride() as u64),
            );
            assert_eq!(at_alpha, via_carrier, "Eq. (150)'s two readings");
            // a unit stays a unit: iota(1) = 1
            let one = embed(&[Q32::ONE], p.stride(), p.d_a());
            assert_eq!(one[0], Q32::ONE);
            assert!(one[1..].iter().all(|v| *v == Q32::ZERO));
        }
    }

    #[test]
    fn the_contraction_commutes_with_a_subring_challenge() {
        // Eq. (91) and (93), over the non-NTT prime.
        let p = packing();
        let m = 3usize;
        let mut seed = 7u64;
        let eqpack: Vec<Q32> = rand_coeffs(p.h_car * p.k, &mut seed);
        let eqpos: Vec<Q32> = rand_coeffs(m, &mut seed);
        for _ in 0..10 {
            let c: Vec<Q32> = rand_coeffs(p.d_car, &mut seed);
            let ca = embed(&c, p.stride(), p.d_a());
            let block: Vec<Q32> = rand_coeffs(m * p.d_a(), &mut seed);
            // L(iota(c) F) == c L(F)
            let mut folded = vec![Q32::ZERO; m * p.d_a()];
            for x in 0..m {
                let prod = nega_mul(&ca, &block[x * p.d_a()..(x + 1) * p.d_a()], p.d_a());
                for (d, v) in folded[x * p.d_a()..(x + 1) * p.d_a()].iter_mut().zip(prod) {
                    *d = v;
                }
            }
            let lhs = block_partial(&folded, m, &eqpos, &eqpack, &p);
            let e = block_partial(&block, m, &eqpos, &eqpack, &p);
            let rhs = nega_mul(&c, &e, p.d_car);
            assert_eq!(lhs, rhs, "L(sum_x eq(x) iota(c) F_x) = c L(F)");
        }
    }

    #[test]
    fn shell_cardinality_matches_an_exhaustive_enumeration() {
        for (dim, counts) in [
            (4usize, vec![(1u64, 2usize)]),
            (4, vec![(1, 1), (2, 1)]),
            (4, vec![(1, 1), (2, 1), (3, 1)]),
            (8, vec![(1, 4)]),
            (8, vec![(2, 3)]),
        ] {
            let shell = Shell::new(dim, &counts);
            let members = shell.enumerate::<Q32>();
            assert_eq!(members.len() as u128, shell.cardinality(), "{counts:?}");
            let omega = shell.omega();
            let cmax = shell.c_max();
            for c in &members {
                let (l1, linf) = norms(c);
                assert_eq!(l1, omega, "||c||_1 = omega for every member");
                assert_eq!(linf, cmax, "||c||_inf = c_max for every member");
                assert!(shell.in_shell(c));
            }
            assert!(members.len() > 1, "the family must not be degenerate");
        }
    }

    #[test]
    fn pairwise_differences_are_units_in_the_admitted_shell() {
        let shell = Shell::new(4, &[(1, 2)]);
        let members = shell.enumerate::<Q32>();
        assert_eq!(members.len(), 24);
        assert_eq!(
            pairwise_unit_certificate(&members, 4),
            Ok(()),
            "2 c_max = 2 << q^{{1/2}}/sqrt(2) for this modulus"
        );
    }

    #[test]
    fn the_certificate_rejects_a_family_that_is_one_magnitude_too_wide() {
        // Over F_17, X - 2 divides X^4 + 1 (2^4 = -1), so a family whose
        // difference set contains X - 2 cannot support extraction. Built by
        // hand: (0,1,0,0) - (2,0,0,0) = (-2,1,0,0).
        let a: Vec<F17> = vec![F17::from(0u64), F17::from(1u64), F17::ZERO, F17::ZERO];
        let b: Vec<F17> = vec![F17::from(2u64), F17::ZERO, F17::ZERO, F17::ZERO];
        assert!(!is_unit(
            &[a[0] - b[0], a[1] - b[1], F17::ZERO, F17::ZERO],
            4
        ));
        assert_eq!(
            pairwise_unit_certificate(&[a.clone(), b.clone()], 4),
            Err(GeomError::ZeroDivisorDifference { left: 0, right: 1 })
        );
        // and the same pair *is* fine over the big prime, where the threshold
        // 2 c_max < q^{1/s}/sqrt(s) holds
        let big: Vec<Q32> = vec![Q32::from(2u64), Q32::ZERO, Q32::ZERO, Q32::ZERO];
        let big2: Vec<Q32> = vec![Q32::ZERO, Q32::ONE, Q32::ZERO, Q32::ZERO];
        assert!(is_unit(
            &[big2[0] - big[0], big2[1] - big[1], Q32::ZERO, Q32::ZERO],
            4
        ));
    }

    #[test]
    fn sampled_challenges_are_shell_members_and_deterministic() {
        let shell = Shell::new(8, &[(1, 2), (2, 1)]);
        let seed = [0x5Au8; 32];
        let c: Vec<Q32> = shell
            .sample(&seed, 0, 3, 1, None)
            .expect("unfiltered always succeeds");
        assert_eq!(c.len(), 8);
        assert!(shell.in_shell(&c));
        let again = shell.sample::<Q32>(&seed, 0, 3, 1, None).expect("same");
        assert_eq!(
            c, again,
            "the sampler is deterministic in (seed, nonce, coord)"
        );
        assert_ne!(
            c,
            shell
                .sample::<Q32>(&seed, 1, 3, 1, None)
                .expect("other nonce"),
            "a different nonce must redraw"
        );
        assert_ne!(
            shell
                .sample::<Q32>(&seed, 0, 2, 1, None)
                .expect("other coord"),
            shell
                .sample::<Q32>(&seed, 0, 3, 1, None)
                .expect("other coord"),
            "coordinates must be derived separately, not sliced from one stream"
        );
    }

    #[test]
    fn operator_norm_filter_is_exact_on_the_cases_with_known_spectral_norm() {
        // A monomial acts as a signed permutation, so ||c||_{mul,2} = 1 exactly.
        for j in 0..4usize {
            let mut c = vec![Q32::ZERO; 4];
            c[j] = Q32::ONE;
            assert_eq!(op_norm_upper_sq(&c), 1, "monomial X^{j}");
        }
        // 1 + X over d = 2 is orthogonal up to the factor sqrt(2): its matrix is
        // [[1,-1],[1,1]], so M^T M = 2I and the bound is exactly 2.
        let c: Vec<Q32> = vec![Q32::ONE, Q32::ONE];
        assert_eq!(op_norm_upper_sq(&c), 2);
        // and 0 has norm 0
        assert_eq!(op_norm_upper_sq(&vec![Q32::ZERO; 4]), 0);
    }

    #[test]
    fn the_filter_narrows_the_family_without_losing_everything() {
        let shell = Shell::new(4, &[(1, 2)]);
        let members = shell.enumerate::<Q32>();
        assert_eq!(members.len(), 24, "C(4,2)·2² = 24 members");
        // `Γ² = 1` is not a narrowing threshold, it is below a floor no member
        // can beat: column 0 of `M_c` *is* the coefficient vector of `c`, so
        // `σ_max(M_c)² ≥ ‖c‖₂² = 2` for every two-term unit member. This test
        // used to claim disjoint monomial pairs "have operator norm 1" and so
        // kept 0 of 24 — an empty accepted family, which is the opposite of
        // what a filter is supposed to demonstrate.
        assert_eq!(
            members
                .iter()
                .filter(|c| shell.accepts::<Q32>(c, 1))
                .count(),
            0,
            "nothing sits under the Euclidean floor σ² ≥ ‖c‖₂² = 2"
        );
        // The separating threshold is `Γ² = 2`: the pairs `d/2` apart, for
        // which `M_cᵗ M_c = 2I` and the certified bound is met with equality.
        let kept = members
            .iter()
            .filter(|c| shell.accepts::<Q32>(c, 2))
            .count();
        assert!(
            kept > 0 && kept < members.len(),
            "kept {kept} of {}",
            members.len()
        );
        assert_eq!(
            kept, 8,
            "2 support pairs at distance d/2, 4 sign patterns each"
        );
        for c in members.iter().filter(|c| shell.accepts::<Q32>(c, 2)) {
            let pos: Vec<usize> = c
                .iter()
                .enumerate()
                .filter(|(_, x)| x.centered() != 0)
                .map(|(i, _)| i)
                .collect();
            assert_eq!(
                (pos[0] + shell.dim / 2) % shell.dim,
                pos[1],
                "an accepted member must be the d/2-separated kind, got {pos:?}"
            );
        }
        // a threshold of ||c||_1^2 never rejects
        let all = members
            .iter()
            .filter(|c| {
                shell.accepts::<Q32>(c, u128::from(shell.omega()) * u128::from(shell.omega()))
            })
            .count();
        assert_eq!(all, members.len(), "||c||_mul,2 <= ||c||_1 (Lemma 3.1)");
        // and exhaustion is reported, not approximated
        assert_eq!(
            shell.sample::<Q32>(&[1u8; 32], 0, 0, 1, Some(0)),
            Err(GeomError::SamplerExhausted { coordinates: 1 })
        );
    }

    #[test]
    fn equality_weights_factor_over_the_block_split() {
        // Eq. (71): eqq(r, i*M + x) = eqq(rblk, i) eqq(rpos, x) with the block
        // axis in the high bits.
        let mut seed = 31u64;
        let r: Vec<Q32> = rand_coeffs(5, &mut seed);
        let (rblk, rpos) = (&r[..2], &r[2..]);
        for i in 0..4usize {
            for x in 0..8usize {
                let flat = i * 8 + x;
                assert_eq!(
                    eq_weight(&r, flat, 5),
                    eq_factorization(rblk, i, rpos, x),
                    "i = {i}, x = {x}"
                );
            }
        }
        // the eq table really is the Boolean restriction
        let t = eq_table(rpos, 3);
        assert_eq!(t.len(), 8);
        assert_eq!(
            t[0],
            rpos.iter()
                .copied()
                .rev()
                .fold(Q32::ONE, |a, b| a * (Q32::ONE - b))
        );
    }

    #[test]
    fn address_maps_are_injective_and_respect_the_native_dimension() {
        // Eq. (107): distinct (j, y, u, k) must give distinct flat addresses, or
        // two witness cells would share a slot and the whole row assembly lies.
        let (s, delta, d) = (2usize, 3usize, 4usize);
        let mut seen = Vec::new();
        for j in 0..5usize {
            for y in 0..s {
                for u in 0..delta {
                    for k in 0..d {
                        let a = address(j, y, u, k, s, delta, d);
                        assert!(!seen.contains(&a), "duplicate address {a}");
                        seen.push(a);
                    }
                }
            }
        }
        assert_eq!(seen.len(), 5 * s * delta * d);
        assert_eq!(address(0, 0, 0, 0, s, delta, d), 0);
    }

    #[test]
    fn envelopes_match_the_paper_formulas_and_never_underestimate() {
        // Corollary G.6: U = sum K1 B, D = (sum Gamma sqrt(E))^2.
        let masses = [3u64, 3];
        let infs = [4u64, 4];
        let energies = [256u128, 256];
        let gammas = [None, None];
        let (u, dd) = envelope(&masses, &infs, &energies, &gammas);
        assert_eq!(u, 24, "2 * 3 * 4");
        assert_eq!(
            dd,
            (3 * 16 + 3 * 16) * (3 * 16 + 3 * 16),
            "D = (sum Gamma sqrt E)^2"
        );
        // with an operator filter the bound is at least as tight
        let (_, dd_filtered) = envelope(&masses, &infs, &energies, &[Some(2), Some(2)]);
        assert!(dd_filtered < dd);
        assert_eq!(ceil_sqrt(0), 0);
        assert_eq!(ceil_sqrt(1), 1);
        assert_eq!(ceil_sqrt(2), 2);
        assert_eq!(ceil_sqrt(256), 16);
        assert_eq!(ceil_sqrt(257), 17);
        assert_eq!(ceil_sqrt(u128::from(u64::MAX)), 1u128 << 32);
    }

    #[test]
    fn padding_factor_zero_is_admitted_as_a_rejection() {
        // §5.1: the verifier "rejects if it is zero"; a claim that vanishes on
        // the padding must never enter a batch, and the ordinary opening's
        // phi = 1 must pass.
        assert_eq!(admit_padding(Q32::ZERO), Err(GeomError::ZeroPaddingFactor));
        assert_eq!(admit_padding(Q32::ONE), Ok(Q32::ONE));
        // a point that lands exactly on a padding coordinate zeroes the factor
        let r = [Q32::ZERO, Q32::ZERO, Q32::ONE];
        let phi = eq_weight(&r, 0b011, 3); // eq((0,0,1),(0,1,1)) = 0
        assert_eq!(phi, Q32::ZERO);
        assert_eq!(admit_padding(phi), Err(GeomError::ZeroPaddingFactor));
        assert_ne!(eq_weight(&r, 0b001, 3), Q32::ZERO);
    }
}
