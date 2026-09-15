//! Streamlined NTRU Prime parameter sets (round-3 submission,
//! `ntruprime-20201007`, `params.h`).
//!
//! The scheme is generic over this trait; concrete parameter sets are
//! zero-sized types. All sets share `p ≡ 1 (mod 4)` and `q ≡ 1 (mod 3)`
//! with `q ≈ 6–10·p`, ring `Z_q[x]/(x^p − x − 1)`.

/// Per-parameter-set constants (round-3 reference `params.h`).
pub trait SntrupParams: 'static {
    /// Ring dimension `p` (prime).
    const P: usize;
    /// Modulus `q`.
    const Q: u16;
    /// Weight of short polynomials.
    const W: usize;

    /// Encoded rounded polynomial (reference `Rounded_bytes`): `p`
    /// coefficients of `ceil((q+1)/3)` values fed through the mixed-radix
    /// `Encode`.
    const ROUNDED_BYTES: usize;
    /// Encoded `Rq` polynomial (reference `Rq_bytes`): `p` coefficients of
    /// `q` values through the same mixed-radix `Encode`.
    const RQ_BYTES: usize;
    /// Packed small polynomial `(p+3)/4`.
    const SMALL_BYTES: usize = Self::P.div_ceil(4);

    /// Secret key: `f ‖ ginv ‖ pk ‖ rho ‖ hash(pk)`.
    const SECRETKEY_BYTES: usize = 2 * Self::SMALL_BYTES + Self::RQ_BYTES + Self::SMALL_BYTES + 32;
    /// Ciphertext: rounded polynomial + 32-byte confirmation.
    const CIPHERTEXT_BYTES: usize = Self::ROUNDED_BYTES + 32;
}

macro_rules! sntrup_params {
    ($name:ident, $p:literal, $q:literal, $w:literal, $rounded:literal, $rq:literal) => {
        #[doc = concat!("Streamlined NTRU Prime over p = ", stringify!($p),
                                ", q = ", stringify!($q), " (weight w = ", stringify!($w), ").")]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub struct $name;
        impl SntrupParams for $name {
            const P: usize = $p;
            const Q: u16 = $q;
            const W: usize = $w;
            const ROUNDED_BYTES: usize = $rounded;
            const RQ_BYTES: usize = $rq;
        }
    };
}

// Rounded_bytes / Rq_bytes from the round-3 submission `paramsmenu.h`.
sntrup_params!(Sntrup653, 653, 4621, 288, 865, 994);
sntrup_params!(Sntrup761, 761, 4591, 286, 1007, 1158);
sntrup_params!(Sntrup857, 857, 5167, 322, 1152, 1322);
sntrup_params!(Sntrup953, 953, 6343, 396, 1317, 1505);
sntrup_params!(Sntrup1013, 1013, 7177, 448, 1423, 1623);
sntrup_params!(Sntrup1277, 1277, 7879, 492, 1815, 2067);
