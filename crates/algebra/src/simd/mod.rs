//! Safe explicit SIMD kernels shared by the scheme crates (L0 utility).
//!
//! All kernels are written on [`wide`] fixed-width lane types, which keeps the
//! whole workspace inside its **no-`unsafe`** CI policy: `wide` lowers to
//! AVX2 registers under `target-feature=+avx2` and otherwise decomposes into
//! two baseline-register halves (SSE2 on x86_64, NEON on aarch64), so the
//! lane path is safe to execute on every supported CPU without runtime feature
//! detection. Other targets compile the portable scalar fallback instead.
//!
//! Kernel choice mirrors where vector lanes actually pay off in this
//! workspace:
//!
//! - the [`wrapping_dot_u16`](crate::simd::wrapping_dot_u16) kernel:
//!   power-of-two-modulus inner products (FrodoKEM matrix products, NTRU
//!   convolution steps). Wrapping 16-bit accumulation is exact whenever the
//!   consumer masks the low `logq ≤ 16` bits.
//! - the [`mod_add_u32`](crate::simd::mod_add_u32) family: branch-free slice
//!   arithmetic for moduli below 2³¹ (ML-KEM butterfly pair updates,
//!   commitment accumulators).
//!
//! The scalar and lane paths compute bit-identical results; the tests assert
//! agreement against independent scalar references so correctness never
//! depends on the building CPU.

/// Element count of the 16×16-bit lane type used by [`wrapping_dot_u16`].
const U16_LANES: usize = 16;

/// Element count of the 8×32-bit lane type used by the modular kernels.
const U32_LANES: usize = 8;

/// Below this input length the lane path's setup cost dominates and the
/// scalar path runs instead.
const MIN_LANE_LEN: usize = 32;

// ===========================================================================
// Wrapping 16-bit dot products (power-of-two-modulus inner products)
// ===========================================================================

/// Wrapping 16-bit axpy: `acc[i] += scalar·a[i] (mod 2^16)`.
///
/// Exact for power-of-two moduli for the same reason as
/// [`wrapping_dot_u16`]: with `q ≤ 2^16` a power of two, every wrapped
/// lane value keeps the low `logq` bits of the true accumulation, provided
/// consumers add into the destination in the same scalar order (FrodoKEM's
/// `S·A + E`-style products do exactly that).
///
/// # Panics
/// If `acc.len() != a.len()`.
pub fn wrapping_axpy_u16(acc: &mut [u16], a: &[u16], scalar: u16) {
    assert_eq!(acc.len(), a.len(), "axpy operands must have equal length");

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if acc.len() >= MIN_LANE_LEN {
        use wide::u16x16;

        let vs = u16x16::new([scalar; U16_LANES]);
        let mut it_acc = acc.chunks_exact_mut(U16_LANES);
        let mut it_a = a.chunks_exact(U16_LANES);
        for (ca, va) in it_acc.by_ref().zip(it_a.by_ref()) {
            let mut lanes = u16x16::new(ca.try_into().unwrap());
            lanes += vs * u16x16::new(va.try_into().unwrap());
            ca.copy_from_slice(&lanes.to_array());
        }
        let tail = it_acc.into_remainder();
        for (&x, px) in it_a.remainder().iter().zip(tail.iter_mut()) {
            *px = px.wrapping_add(scalar.wrapping_mul(x));
        }
        return;
    }
    for (pa, &x) in acc.iter_mut().zip(a.iter()) {
        *pa = pa.wrapping_add(scalar.wrapping_mul(x));
    }
}

/// Wrapping 16-bit dot product: `Σ a[i]·b[i] (mod 2^16)`.
///
/// Exact for power-of-two moduli: wrapping addition and multiplication are
/// the ring operations of `Z/2^16`, so the low `logq ≤ 16` bits of the
/// result equal the true inner product mod `q`. This is precisely the
/// FrodoKEM accumulation discipline (sum first, mask at the end).
///
/// # Panics
/// If `a.len() != b.len()`.
#[must_use]
pub fn wrapping_dot_u16(a: &[u16], b: &[u16]) -> u16 {
    assert_eq!(
        a.len(),
        b.len(),
        "dot product operands must have equal length"
    );

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if a.len() >= MIN_LANE_LEN {
        return lane_dot_u16(a, b);
    }
    scalar_dot_u16(a, b)
}

/// Scalar reference for [`wrapping_dot_u16`].
fn scalar_dot_u16(a: &[u16], b: &[u16]) -> u16 {
    let mut acc = 0u16;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc = acc.wrapping_add(x.wrapping_mul(y));
    }
    acc
}

/// 16-lane path for [`wrapping_dot_u16`].
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn lane_dot_u16(a: &[u16], b: &[u16]) -> u16 {
    use wide::u16x16;

    let mut lanes = u16x16::new([0u16; U16_LANES]);
    let mut it_a = a.chunks_exact(U16_LANES);
    let mut it_b = b.chunks_exact(U16_LANES);
    for (ca, cb) in it_a.by_ref().zip(it_b.by_ref()) {
        // `try_into` cannot fail: chunks_exact yields exactly 16 elements.
        let va = u16x16::new(ca.try_into().unwrap());
        let vb = u16x16::new(cb.try_into().unwrap());
        lanes += va * vb;
    }
    let mut acc = 0u16;
    for &lane in &lanes.to_array() {
        acc = acc.wrapping_add(lane);
    }
    for (&x, &y) in it_a.remainder().iter().zip(it_b.remainder()) {
        acc = acc.wrapping_add(x.wrapping_mul(y));
    }
    acc
}

/// Wrapping 32-bit dot product: `Σ a[i]·b[i] (mod 2^32)`.
///
/// Exact for power-of-two moduli up to `2^32` — the ring arithmetic of
/// `Z/2^32` (raw `u32` coefficients) is exactly wrapping lane math, so this
/// is the inner-product step of the ZK crate's Z2 ring
/// `Z_{2^32}[X]/(X^64+1)` and of any FrodoKEM-style `q = 2^32` product.
///
/// # Panics
/// If `a.len() != b.len()`.
#[must_use]
pub fn wrapping_dot_u32(a: &[u32], b: &[u32]) -> u32 {
    assert_eq!(
        a.len(),
        b.len(),
        "dot product operands must have equal length"
    );

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if a.len() >= MIN_LANE_LEN {
        return lane_dot_u32(a, b);
    }
    scalar_dot_u32(a, b)
}

/// Scalar reference for [`wrapping_dot_u32`].
fn scalar_dot_u32(a: &[u32], b: &[u32]) -> u32 {
    let mut acc = 0u32;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc = acc.wrapping_add(x.wrapping_mul(y));
    }
    acc
}

/// 8-lane path for [`wrapping_dot_u32`].
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn lane_dot_u32(a: &[u32], b: &[u32]) -> u32 {
    use wide::u32x8;

    let mut lanes = u32x8::new([0u32; U32_LANES]);
    let mut it_a = a.chunks_exact(U32_LANES);
    let mut it_b = b.chunks_exact(U32_LANES);
    for (ca, cb) in it_a.by_ref().zip(it_b.by_ref()) {
        let va = load_u32x8(ca);
        let vb = load_u32x8(cb);
        lanes += va * vb;
    }
    let mut acc = 0u32;
    for &lane in &lanes.to_array() {
        acc = acc.wrapping_add(lane);
    }
    for (&x, &y) in it_a.remainder().iter().zip(it_b.remainder()) {
        acc = acc.wrapping_add(x.wrapping_mul(y));
    }
    acc
}

// ===========================================================================
// Modular 32-bit slice arithmetic (moduli below 2^31)
// ===========================================================================

/// Slice-wise modular addition: `dst[i] = (a[i] + b[i]) mod q`.
///
/// All inputs must satisfy `a[i], b[i] < q ≤ 2^31`, so the sum never
/// overflows the 32-bit lanes and a single conditional subtract normalizes.
///
/// # Panics
/// If the slices differ in length, or any operand lane is `>= q` (debug
/// builds only; release runs wrap, which would silently corrupt results).
#[inline]
pub fn mod_add_u32(dst: &mut [u32], a: &[u32], b: &[u32], q: u32) {
    assert_eq!(
        a.len(),
        b.len(),
        "mod_add_u32 operands must have equal length"
    );
    assert_eq!(
        dst.len(),
        a.len(),
        "mod_add_u32 destination must match input length"
    );

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if a.len() >= MIN_LANE_LEN {
        lane_mod_add_sub_u32(dst, a, b, q, Op::Add);
        return;
    }
    scalar_mod_add_sub_u32(dst, a, b, q, Op::Add);
}

/// Slice-wise modular subtraction: `dst[i] = (a[i] − b[i]) mod q`.
///
/// Precondition as [`mod_add_u32`]: every lane of `a` and `b` is below
/// `q ≤ 2^31`.
///
/// # Panics
/// If the slices differ in length, or any operand lane is `>= q` (debug
/// builds only).
#[inline]
pub fn mod_sub_u32(dst: &mut [u32], a: &[u32], b: &[u32], q: u32) {
    assert_eq!(
        a.len(),
        b.len(),
        "mod_sub_u32 operands must have equal length"
    );
    assert_eq!(
        dst.len(),
        a.len(),
        "mod_sub_u32 destination must match input length"
    );

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if a.len() >= MIN_LANE_LEN {
        lane_mod_add_sub_u32(dst, a, b, q, Op::Sub);
        return;
    }
    scalar_mod_add_sub_u32(dst, a, b, q, Op::Sub);
}

/// In-place modular addition: `x[i] = (x[i] + y[i]) mod q`.
///
/// The accumulating counterpart of [`mod_add_u32`] — the natural shape of
/// NTT butterfly pair updates. Precondition as [`mod_add_u32`]: every lane
/// of `x` and `y` is below `q ≤ 2^31`.
///
/// # Panics
/// If the slices differ in length, or any operand lane is `>= q` (debug
/// builds only).
#[inline]
pub fn mod_add_assign_u32(x: &mut [u32], y: &[u32], q: u32) {
    assert_eq!(
        x.len(),
        y.len(),
        "mod_add_assign_u32 operands must have equal length"
    );

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if x.len() >= MIN_LANE_LEN {
        let qv = wide::u32x8::new([q; U32_LANES]);
        let mut it_x = x.chunks_exact_mut(U32_LANES);
        let mut it_y = y.chunks_exact(U32_LANES);
        for (cx, cy) in it_x.by_ref().zip(it_y.by_ref()) {
            debug_assert!(
                cx.iter().chain(cy.iter()).all(|&v| v < q),
                "operand lane >= q"
            );
            let sum = load_u32x8(cx) + load_u32x8(cy);
            store_reduced(cx, sum, qv);
        }
        scalar_mod_add_assign_u32(it_x.into_remainder(), it_y.remainder(), q, Op::Add);
        return;
    }
    scalar_mod_add_assign_u32(x, y, q, Op::Add);
}

/// In-place modular subtraction: `x[i] = (x[i] − y[i]) mod q`.
///
/// Precondition as [`mod_add_assign_u32`].
///
/// # Panics
/// If the slices differ in length, or any operand lane is `>= q` (debug
/// builds only).
#[inline]
pub fn mod_sub_assign_u32(x: &mut [u32], y: &[u32], q: u32) {
    assert_eq!(
        x.len(),
        y.len(),
        "mod_sub_assign_u32 operands must have equal length"
    );

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if x.len() >= MIN_LANE_LEN {
        let qv = wide::u32x8::new([q; U32_LANES]);
        let mut it_x = x.chunks_exact_mut(U32_LANES);
        let mut it_y = y.chunks_exact(U32_LANES);
        for (cx, cy) in it_x.by_ref().zip(it_y.by_ref()) {
            debug_assert!(
                cx.iter().chain(cy.iter()).all(|&v| v < q),
                "operand lane >= q"
            );
            // x + q − y ∈ (0, 2q): one conditional subtract normalizes.
            let sum = load_u32x8(cx) + qv - load_u32x8(cy);
            store_reduced(cx, sum, qv);
        }
        scalar_mod_add_assign_u32(it_x.into_remainder(), it_y.remainder(), q, Op::Sub);
        return;
    }
    scalar_mod_add_assign_u32(x, y, q, Op::Sub);
}

/// Selects the arithmetic of [`mod_add_u32`] vs [`mod_sub_u32`].
#[derive(Clone, Copy)]
enum Op {
    /// `a + b`
    Add,
    /// `a − b`
    Sub,
}

/// Scalar reference for [`mod_add_u32`] / [`mod_sub_u32`].
fn scalar_mod_add_sub_u32(dst: &mut [u32], a: &[u32], b: &[u32], q: u32, op: Op) {
    debug_assert!(
        a.iter().chain(b.iter()).all(|&v| v < q),
        "operand lane >= q"
    );
    match op {
        Op::Add => {
            for ((d, &x), &y) in dst.iter_mut().zip(a.iter()).zip(b.iter()) {
                let s = x + y;
                *d = if s >= q { s - q } else { s };
            }
        }
        Op::Sub => {
            for ((d, &x), &y) in dst.iter_mut().zip(a.iter()).zip(b.iter()) {
                *d = if x >= y { x - y } else { q - (y - x) };
            }
        }
    }
}

/// Scalar reference for [`mod_add_assign_u32`] / [`mod_sub_assign_u32`].
fn scalar_mod_add_assign_u32(x: &mut [u32], y: &[u32], q: u32, op: Op) {
    debug_assert!(
        x.iter().chain(y.iter()).all(|&v| v < q),
        "operand lane >= q"
    );
    match op {
        Op::Add => {
            for (px, &py) in x.iter_mut().zip(y.iter()) {
                let s = *px + py;
                *px = if s >= q { s - q } else { s };
            }
        }
        Op::Sub => {
            for (px, &py) in x.iter_mut().zip(y.iter()) {
                *px = if *px >= py { *px - py } else { q - (py - *px) };
            }
        }
    }
}

/// 8-lane path for [`mod_add_u32`] / [`mod_sub_u32`].
///
/// Subtraction is computed as `(a + q − b) mod q` so both operations share
/// the branch-free conditional-subtract epilogue: with every lane below
/// `q ≤ 2^31` the intermediate stays below 2^31 and the single masked
/// subtract fully normalizes.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn lane_mod_add_sub_u32(dst: &mut [u32], a: &[u32], b: &[u32], q: u32, op: Op) {
    use wide::u32x8;

    let qv = u32x8::new([q; U32_LANES]);
    let mut it_d = dst.chunks_exact_mut(U32_LANES);
    let mut it_a = a.chunks_exact(U32_LANES);
    let mut it_b = b.chunks_exact(U32_LANES);
    for ((cd, ca), cb) in it_d.by_ref().zip(it_a.by_ref()).zip(it_b.by_ref()) {
        debug_assert!(
            ca.iter().chain(cb.iter()).all(|&v| v < q),
            "operand lane >= q"
        );
        let vb = match op {
            Op::Add => load_u32x8(cb),
            Op::Sub => qv - load_u32x8(cb),
        };
        let sum = load_u32x8(ca) + vb;
        store_reduced(cd, sum, qv);
    }
    scalar_mod_add_sub_u32(
        it_d.into_remainder(),
        it_a.remainder(),
        it_b.remainder(),
        q,
        op,
    );
}

/// Loads 8 lanes from a full chunk (`try_into` cannot fail by construction).
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn load_u32x8(chunk: &[u32]) -> wide::u32x8 {
    wide::u32x8::new(chunk.try_into().unwrap())
}

/// Branch-free `if sum >= q { sum − q }` written back into `cd`.
///
/// `blend` keeps `sum` where the `sum < q` mask is set and picks the reduced
/// lane elsewhere.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn store_reduced(cd: &mut [u32], sum: wide::u32x8, qv: wide::u32x8) {
    let reduced = (sum.cmp_lt(qv)).blend(sum, sum - qv);
    cd.copy_from_slice(&reduced.to_array());
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Deterministic xorshift so failures are reproducible.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            let mut s = self.0;
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            self.0 = s;
            s
        }

        fn below(&mut self, bound: u64) -> u64 {
            self.next() % bound
        }
    }

    const MODULI: [u32; 5] = [2, 17, 3329, 8380417, 1 << 31];

    #[test]
    fn axpy_matches_scalar_reference() {
        let mut rng = Rng(0x99AA_00BB);
        for len in [0usize, 1, 3, 15, 16, 17, 31, 32, 100, 640] {
            let mut acc: Vec<u16> = (0..len).map(|_| rng.next() as u16).collect();
            let a: Vec<u16> = (0..len).map(|_| rng.next() as u16).collect();
            let scalar = rng.next() as u16;

            let mut want = acc.clone();
            for i in 0..len {
                want[i] = want[i].wrapping_add(scalar.wrapping_mul(a[i]));
            }
            wrapping_axpy_u16(&mut acc, &a, scalar);
            assert_eq!(acc, want, "len {len}");
        }
    }

    #[test]
    fn dot_matches_scalar_reference_across_lengths() {
        let mut rng = Rng(0x5EED_1234);
        for len in [0usize, 1, 3, 15, 16, 17, 31, 32, 100, 701] {
            let a: Vec<u16> = (0..len).map(|_| rng.next() as u16).collect();
            let b: Vec<u16> = (0..len).map(|_| rng.next() as u16).collect();
            assert_eq!(
                wrapping_dot_u16(&a, &b),
                scalar_dot_u16(&a, &b),
                "len {len}"
            );
        }
    }

    #[test]
    fn dot_u32_matches_scalar_reference_across_lengths() {
        let mut rng = Rng(0x5EED_9E37);
        for len in [0usize, 1, 3, 7, 8, 9, 31, 32, 33, 64, 100, 701] {
            let a: Vec<u32> = (0..len).map(|_| rng.next() as u32).collect();
            let b: Vec<u32> = (0..len).map(|_| rng.next() as u32).collect();
            assert_eq!(
                wrapping_dot_u32(&a, &b),
                scalar_dot_u32(&a, &b),
                "len {len}"
            );
        }
    }

    #[test]
    fn dot_u32_is_exact_modulo_power_of_two() {
        // The low 32 bits must equal the wide integer sum; the low 16 must
        // agree with the u16 kernel's view of the same operands.
        let mut rng = Rng(0x0F1E_2D3C);
        let a: Vec<u32> = (0..256).map(|_| rng.next() as u32).collect();
        let b: Vec<u32> = (0..256).map(|_| rng.next() as u32).collect();
        let wide: u64 = a
            .iter()
            .zip(&b)
            .fold(0, |acc, (&x, &y)| acc.wrapping_add(x as u64 * y as u64));
        assert_eq!(wrapping_dot_u32(&a, &b) as u64, wide & 0xFFFF_FFFF);
        let a16: Vec<u16> = a.iter().map(|&v| v as u16).collect();
        let b16: Vec<u16> = b.iter().map(|&v| v as u16).collect();
        assert_eq!(
            (wrapping_dot_u32(&a, &b) & 0xFFFF) as u16,
            wrapping_dot_u16(&a16, &b16),
        );
    }

    #[test]
    #[should_panic(expected = "equal length")]
    fn dot_u32_rejects_mismatched_lengths() {
        let _ = wrapping_dot_u32(&[1, 2], &[1]);
    }

    #[test]
    fn dot_is_exact_modulo_power_of_two() {
        // For q = 2^15 the low 15 bits must equal the wide integer sum.
        let mut rng = Rng(0xABCD_EF01);
        let a: Vec<u16> = (0..256).map(|_| rng.next() as u16).collect();
        let b: Vec<u16> = (0..256).map(|_| rng.next() as u16).collect();
        let wide: u64 = a.iter().zip(&b).map(|(&x, &y)| x as u64 * y as u64).sum();
        assert_eq!(wrapping_dot_u16(&a, &b) as u64, wide & 0xFFFF);
        assert_eq!((wrapping_dot_u16(&a, &b) & 0x7FFF) as u64, wide & 0x7FFF);
    }

    #[test]
    fn mod_add_matches_scalar_reference() {
        let mut rng = Rng(0x0F1E_2D3C);
        for &q in &MODULI {
            for len in [0usize, 1, 7, 8, 9, 31, 32, 33, 100] {
                let a: Vec<u32> = (0..len).map(|_| rng.below(q as u64) as u32).collect();
                let b: Vec<u32> = (0..len).map(|_| rng.below(q as u64) as u32).collect();
                let mut want = vec![0u32; len];
                let mut got = vec![0u32; len];
                scalar_mod_add_sub_u32(&mut want, &a, &b, q, Op::Add);
                mod_add_u32(&mut got, &a, &b, q);
                assert_eq!(got, want, "q {q}, len {len}");
            }
        }
    }

    #[test]
    fn mod_sub_matches_scalar_reference() {
        let mut rng = Rng(0x77AA_55BB);
        for &q in &MODULI {
            for len in [0usize, 1, 7, 8, 9, 31, 32, 33, 100] {
                let a: Vec<u32> = (0..len).map(|_| rng.below(q as u64) as u32).collect();
                let b: Vec<u32> = (0..len).map(|_| rng.below(q as u64) as u32).collect();
                let mut want = vec![0u32; len];
                let mut got = vec![0u32; len];
                scalar_mod_add_sub_u32(&mut want, &a, &b, q, Op::Sub);
                mod_sub_u32(&mut got, &a, &b, q);
                assert_eq!(got, want, "q {q}, len {len}");
            }
        }
    }

    #[test]
    fn mod_assign_matches_out_of_place_kernels() {
        let mut rng = Rng(0x2468_ACE0);
        for &q in &MODULI {
            for len in [0usize, 1, 7, 8, 9, 31, 32, 33, 100, 256] {
                let a: Vec<u32> = (0..len).map(|_| rng.below(q as u64) as u32).collect();
                let b: Vec<u32> = (0..len).map(|_| rng.below(q as u64) as u32).collect();

                let mut sum = a.clone();
                mod_add_assign_u32(&mut sum, &b, q);
                let mut want_sum = vec![0u32; len];
                scalar_mod_add_sub_u32(&mut want_sum, &a, &b, q, Op::Add);
                assert_eq!(sum, want_sum, "add-assign, q {q}, len {len}");

                let mut diff = a.clone();
                mod_sub_assign_u32(&mut diff, &b, q);
                let mut want_diff = vec![0u32; len];
                scalar_mod_add_sub_u32(&mut want_diff, &a, &b, q, Op::Sub);
                assert_eq!(diff, want_diff, "sub-assign, q {q}, len {len}");
            }
        }
    }

    #[test]
    fn mod_sub_is_negation_of_add() {
        let mut rng = Rng(0x1234_5678_9ABC);
        let q = 8380417u32;
        let a: Vec<u32> = (0..70).map(|_| rng.below(q as u64) as u32).collect();
        let b: Vec<u32> = (0..70).map(|_| rng.below(q as u64) as u32).collect();
        let mut sum = a.clone();
        mod_add_assign_u32(&mut sum, &b, q);
        let mut back = sum.clone();
        mod_sub_assign_u32(&mut back, &b, q);
        assert_eq!(back, a, "(a + b) − b must recover a mod q");
    }

    #[test]
    #[should_panic(expected = "equal length")]
    fn dot_rejects_mismatched_lengths() {
        let _ = wrapping_dot_u16(&[1, 2], &[1]);
    }

    #[test]
    #[should_panic(expected = "destination must match input length")]
    fn mod_add_rejects_mismatched_destination() {
        let mut dst = vec![0u32; 3];
        mod_add_u32(&mut dst, &[1, 2, 3, 4], &[1, 2, 3, 4], 17);
    }
}
