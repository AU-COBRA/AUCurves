//! X25519 Diffie-Hellman: verified Jasmin assembly + CryptOpt superoptimized field ops.
//!
//! # Two backends
//!
//! - **Pure Jasmin** (`x25519_jasmin`): Full scalar multiplication in a single Jasmin
//!   function from libjade/formosa-25519 (mulx variant, ~144K cycles). Everything
//!   is inlined and compiled by jasminc. Verified: EasyCrypt (Jazzline CCS 2025)
//!   + jasminc (EasyCrypt-verified compiler). Constant-time by construction.
//!
//! - **Hybrid** (`x25519_hybrid`): Montgomery ladder in Rust calling CryptOpt-
//!   superoptimized mul/square + Jasmin add/sub/cswap/mul_a24/tobytes. Field ops
//!   verified in Coq (fiat-crypto check_equivalence) and EasyCrypt (jasminc).
//!
//! # Verification chain
//!
//! ```text
//! Jasmin path:  formosa-25519 EasyCrypt proof → jasminc (verified) → x86-64
//! CryptOpt:     fiat-crypto Coq spec → CryptOpt search → check_equivalence (Coq)
//! Rust wrapper:  borrow checker enforces non-aliasing (= bedrock2 sep-logic)
//! ```
//!
//! # Panic-freeness lints (`docs/performance-and-panic-freeness-2026-05-13.md` §2.3 step a)
//!
//! We deny the standard panic-able patterns at the crate level.  Production
//! code is panic-free; the surviving `try_into().unwrap()` sites have been
//! audited against fixed-length byte slices and carry per-site `#[allow]`
//! attributes citing the audit (`docs/performance-and-panic-freeness-2026-05-13.md`
//! §2.1).
//!
//! `clippy::indexing_slicing` and `clippy::arithmetic_side_effects` are
//! intentionally NOT denied — they are aggressive lints that fire on many
//! provably-safe sites in this crate (inventory under
//! `--features dalek_leaves`: 32 indexing-slicing hits, 41 arithmetic-side-
//! effects hits across 7 files).  Gating these globally would require
//! per-site allows on extracted IR code that we do not hand-edit (the
//! field-arithmetic leaves and the Lean-emitted bodies in `*_emitted.rs`).
//! Wrapping arithmetic (`.wrapping_*`) is already used pervasively; the
//! arithmetic-side-effects hits are on `+`/`-` with proven non-overflow.
//!
//! # FFI centralization (status doc §6.3, Phase B)
//!
//! Every `extern "C"` symbol called from this file is wrapped once in
//! `crate::ffi_safe`; the wrappers provide a safe Rust signature
//! (`&[u8; N]` / `&mut [T; N]`) so the call sites below carry **no**
//! inline `unsafe { ... }` blocks.

#![allow(non_camel_case_types)]
// Stacked `#[kani::stub(..)]` attributes on the Ristretto Kani
// harnesses (`ristretto_rustcmd::kani_proofs`) expand recursively; 8+
// stubs on one harness blow the default macro recursion limit of 128.
// Gated on `kani` so the normal build is byte-for-byte unaffected.
#![cfg_attr(kani, recursion_limit = "512")]
#![deny(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::unreachable,
)]

/// Centralized safe wrappers around every `extern "C"` symbol called
/// from this crate's hand-written Rust code.  See module header for
/// the Phase B reduction-plan context.
pub mod ffi_safe;

pub mod xeddsa;

/// Montgomery → Edwards y-coordinate conversion, used by XEdDSA verify.
/// Built only on fiat-crypto verified primitives (no dalek glue).
pub mod mont_to_edwards;

/// Lean-emitted field-arithmetic core for `mont_u_to_edwards_compressed`.
/// AST source: `SSProve-lean/CatCrypt/Crypto/Jasmin/Examples/MontUToEdwards.lean`.
/// Trust: single Lean axiom `RustcExec_correct`.  KAT'd against
/// the hand-coded `mont_to_edwards` version in unit tests.
#[cfg(feature = "lean_emitted_mont_to_edwards")]
pub mod mont_to_edwards_emitted;

/// Scalar arithmetic mod L (curve order), used by XEdDSA sign.  Built
/// on fiat-crypto's verified curve25519_scalar_64 (Montgomery form).
pub mod scalar25519;

/// Bernstein-Yang divstep modular inversion (proxy benchmark for fe25519_invert).
/// Uses fiat-crypto's verified scalar-field divstep functions to compute inverses
/// mod L (253-bit prime), as a stand-in for what a future divstep-based fe25519
/// invert (mod p25519, 255-bit) would look like.  See module docs.
pub mod divstep_proxy;

/// Generic Bernstein-Yang divstep modular inversion (const-generic limb count).
/// Port of libsecp256k1 `secp256k1_modinv64` (MIT, Pieter Dettman 2020),
/// parameterized so every prime curve shares the same algorithm core.
/// See per-curve wrappers `safegcd25519`, `safegcd_secp256k1`, `safegcd_p256`,
/// `safegcd_bn254`.  Implements EUROCRYPT 2026 paper's δ₀=1/2 + 590 divsteps.
pub mod safegcd;

/// Per-curve safegcd inversion for p25519.
pub mod safegcd25519;
/// Per-curve safegcd inversion for the secp256k1 base prime.
pub mod safegcd_secp256k1;
/// Per-curve safegcd inversion for P-256.
pub mod safegcd_p256;
/// Per-curve safegcd inversion for NIST P-224 (Track Q).
pub mod safegcd_p224;
/// Per-curve safegcd inversion for NIST P-384 (Track Q).
pub mod safegcd_p384;
/// Per-curve safegcd inversion for NIST P-521 (Track Q, 9-limb).
pub mod safegcd_p521;
/// Per-curve safegcd inversion for BN254 base prime.
pub mod safegcd_bn254;
/// Per-curve safegcd inversion for BLS12-377 base prime (7 limbs).
pub mod safegcd_bls12_377;
/// Per-curve safegcd inversion for BLS12-381 base prime (7 limbs).
pub mod safegcd_bls12_381;
/// Per-curve safegcd inversion for BLS24-509 base prime (9 limbs).
pub mod safegcd_bls24_509;
/// Per-curve safegcd inversion for Pallas base prime (Pasta-cycle, 5 limbs).
pub mod safegcd_pallas;
/// Per-curve safegcd inversion for Vesta base prime (Pasta-cycle, 5 limbs).
pub mod safegcd_vesta;
/// Per-curve safegcd inversion for BN256 base prime (5 limbs).
pub mod safegcd_bn256;
/// Per-curve safegcd inversion for BN446 base prime (9 limbs, 8×u64 padded).
pub mod safegcd_bn446;
/// Per-curve safegcd inversion for BW6-761 base prime (13 limbs).
pub mod safegcd_bw6_761;

/// Lean-emitted per-method bodies for `Scalar25519`.
/// AST source: `SSProve-lean/CatCrypt/Crypto/Jasmin/Examples/Scalar25519Ops.lean`.
/// Trust: single Lean axiom `RustcExec_correct`.  KAT'd against
/// the hand-coded `Scalar25519::*` API in unit tests.
#[cfg(feature = "lean_emitted_scalar25519")]
pub mod scalar25519_emitted;

/// Symmetric crypto building blocks (Track B5+B6 of the Signal
/// end-to-end plan): SHA-256, SHA-512 (libjade Jasmin), HMAC and
/// HKDF (composed over the verified hashes).
pub mod symmetric;

/// X3DH session-setup composition (Track C1).  Composes X25519 +
/// signed-prekey verify + HKDF-SHA256 into Signal's initial key
/// agreement protocol.
pub mod x3dh;

/// Double Ratchet message protocol (Track C2 demo).  Composes
/// X25519 + HKDF-SHA256 + HMAC-SHA256 + AES-256-GCM into Signal's
/// per-message ratchet with forward secrecy and post-compromise
/// security.
pub mod double_ratchet;

/// PQXDH (Track C3): X3DH + ML-KEM-768 for post-quantum-augmented
/// session setup.
pub mod pqxdh;

/// Sender Keys (Track C4): group symmetric ratchet for multi-recipient
/// messages.
pub mod sender_keys;

/// zkgroup primitives (Track C5): Pedersen commitments + Schnorr
/// proofs over Ristretto255.
pub mod zkgroup_demo;

/// Ed25519 sign/verify generated directly from the verified `rust_cmd_ed`
/// AST (see `AUCurves/src/Bedrock/RustCmdToRust.v`).  Off by default —
/// gated on `feature = "ed25519_rustcmd"`.
pub mod ed25519_rustcmd;

/// Ristretto255 decode/encode, also generated from the verified
/// `rust_cmd_ed` AST.  Currently scaffold + path-(b) leaves
/// (constant setters, pack_xyzt5); decode/encode stubs return
/// `None`/`[0xFF; 32]` until the AST authoring lands.
pub mod ristretto_rustcmd;

/// GF(2^255 - 19) field element, 4 × u64 saturated representation.
///
/// Limb layout: value = limbs[0] + limbs[1]*2^64 + limbs[2]*2^128 + limbs[3]*2^192
/// Not necessarily fully reduced — may be in [0, 2^256) with lazy reduction by 38.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fe25519(pub [u64; 4]);

impl Fe25519 {
    #[inline]
    pub const fn zero() -> Self { Fe25519([0u64; 4]) }

    #[inline]
    pub const fn from_limbs(limbs: [u64; 4]) -> Self { Fe25519(limbs) }

    #[inline]
    pub fn as_ptr(&self) -> *const u64 { self.0.as_ptr() }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u64 { self.0.as_mut_ptr() }
}

// ================================================================
// FFI: all `extern "C"` declarations and their `unsafe { ... }` call
// sites live in `crate::ffi_safe`.  This file calls them through the
// safe Rust wrappers there.  See `src/ffi_safe.rs` and the status
// doc §6.3 (Phase B of the unsafe-reduction plan).
// ================================================================

/// 5-limb unsaturated Solinas field element (bedrock2/fiat-crypto convention).
/// Matches [u64; 5] layout used by both bedrock2-C and bedrock2-Jasmin ops.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fe25519_5limb(pub [u64; 5]);

/// Safe wrappers for the bedrock2-Jasmin field ops.
/// These call functions compiled from bedrock2 WP-verified source via
/// jasminc (Rocq-verified compiler).
///
/// Phase B refactor: every wrapper here is now a one-liner delegating
/// to `ffi_safe::fe25519_5_*` (no inline `unsafe`).
pub mod bedrock2_jasmin {
    use super::Fe25519_5limb;
    use super::ffi_safe;

    /// out = a + b mod p (5-limb unsaturated Solinas).
    pub fn add(out: &mut Fe25519_5limb, a: &Fe25519_5limb, b: &Fe25519_5limb) {
        ffi_safe::fe25519_5_add(&mut out.0, &a.0, &b.0)
    }

    /// out = a - b mod p.
    pub fn sub(out: &mut Fe25519_5limb, a: &Fe25519_5limb, b: &Fe25519_5limb) {
        ffi_safe::fe25519_5_sub(&mut out.0, &a.0, &b.0)
    }

    /// out = a * a24 mod p (Montgomery ladder constant, a24 = 121665).
    pub fn scmula24(out: &mut Fe25519_5limb, a: &Fe25519_5limb) {
        ffi_safe::fe25519_5_scmula24(&mut out.0, &a.0)
    }

    /// Constant-time conditional swap.
    pub fn cswap(mask: u64, a: &mut Fe25519_5limb, b: &mut Fe25519_5limb) {
        ffi_safe::felem_5_cswap(mask, &mut a.0, &mut b.0)
    }

    /// out := a.
    pub fn copy(out: &mut Fe25519_5limb, a: &Fe25519_5limb) {
        ffi_safe::fe25519_5_copy(&mut out.0, &a.0)
    }

    /// out := (u64) w (sign-extended into u64[5]).
    pub fn from_word(out: &mut Fe25519_5limb, w: u64) {
        ffi_safe::fe25519_5_from_word(&mut out.0, w)
    }

    /// RFC 7748 scalar clamping in-place on a 32-byte (4 × u64) scalar buffer.
    /// u64[0] &= 0xFFFFFFFFFFFFFFF8; u64[3] = (u64[3] & 0x7FFF...FFFF) | 0x4000...0000
    pub fn clamp(sk: &mut [u64; 4]) {
        ffi_safe::clamp_scalar_u64(sk)
    }
}

// ================================================================
// Safe wrappers: field operations
// ================================================================

/// out = a + b mod p
#[inline]
pub fn fe_add(out: &mut Fe25519, a: &Fe25519, b: &Fe25519) {
    ffi_safe::curve25519_add_4(&mut out.0, &a.0, &b.0)
}

/// out = a - b mod p
#[inline]
pub fn fe_sub(out: &mut Fe25519, a: &Fe25519, b: &Fe25519) {
    ffi_safe::curve25519_sub_4(&mut out.0, &a.0, &b.0)
}

/// out = a * b mod p  (CryptOpt superoptimized)
#[inline]
pub fn fe_mul(out: &mut Fe25519, a: &Fe25519, b: &Fe25519) {
    ffi_safe::fiat_solinas_mul(&mut out.0, &a.0, &b.0)
}

/// out = a^2 mod p  (CryptOpt superoptimized)
#[inline]
pub fn fe_square(out: &mut Fe25519, a: &Fe25519) {
    ffi_safe::fiat_solinas_square(&mut out.0, &a.0)
}

/// out = a * 121665 mod p  (Montgomery ladder constant a24)
#[inline]
pub fn fe_mul_a24(out: &mut Fe25519, a: &Fe25519) {
    ffi_safe::curve25519_mul_a24_4(&mut out.0, &a.0)
}

/// Canonically reduce and encode: out = a mod (2^255-19) as little-endian bytes
#[inline]
pub fn fe_tobytes(out: &mut Fe25519, a: &Fe25519) {
    ffi_safe::curve25519_tobytes_4(&mut out.0, &a.0)
}

/// Constant-time swap: if swap != 0, exchange a and b
#[inline]
pub fn fe_cswap(a: &mut Fe25519, b: &mut Fe25519, swap: u64) {
    ffi_safe::curve25519_cswap_4(&mut a.0, &mut b.0, swap)
}

/// Square returning result (avoids aliasing issues)
#[inline]
fn sq(a: &Fe25519) -> Fe25519 {
    let mut out = Fe25519::zero();
    fe_square(&mut out, a);
    out
}

/// Multiply returning result (avoids aliasing issues)
#[inline]
fn mul(a: &Fe25519, b: &Fe25519) -> Fe25519 {
    let mut out = Fe25519::zero();
    fe_mul(&mut out, a, b);
    out
}

// ================================================================
// X25519: Pure Jasmin path
// ================================================================

/// X25519 scalar multiplication using the pure Jasmin path (libjade mulx).
///
/// Computes `q = clamp(scalar) * point` on Curve25519.
/// Returns the 32-byte x-coordinate of the result.
pub fn x25519_jasmin(scalar: &[u8; 32], point: &[u8; 32]) -> [u8; 32] {
    let mut q = [0u64; 4];
    let n = u8x32_to_u64x4(scalar);
    let p = u8x32_to_u64x4(point);
    let _ = ffi_safe::jade_scalarmult_mulx(&mut q, &n, &p);
    u64x4_to_u8x32(&q)
}

/// X25519 base-point multiplication using the pure Jasmin path.
///
/// Computes `q = clamp(scalar) * 9`.
pub fn x25519_jasmin_base(scalar: &[u8; 32]) -> [u8; 32] {
    let mut q = [0u64; 4];
    let n = u8x32_to_u64x4(scalar);
    let _ = ffi_safe::jade_scalarmult_mulx_base(&mut q, &n);
    u64x4_to_u8x32(&q)
}

// ================================================================
// X25519: CryptOpt-inlined Jasmin path
// ================================================================

/// X25519 using the CryptOpt-style Jasmin variant.
///
/// Same verified algorithm as `x25519_jasmin`, but with MULX/ADCX/ADOX
/// instruction schedule optimized following CryptOpt's patterns.
/// Everything compiles through jasminc (Rocq-verified compiler).
pub fn x25519_cryptopt(scalar: &[u8; 32], point: &[u8; 32]) -> [u8; 32] {
    let mut q = [0u64; 4];
    let n = u8x32_to_u64x4(scalar);
    let p = u8x32_to_u64x4(point);
    let _ = ffi_safe::jade_scalarmult_cryptopt(&mut q, &n, &p);
    u64x4_to_u8x32(&q)
}

/// CryptOpt-style base-point multiplication.
pub fn x25519_cryptopt_base(scalar: &[u8; 32]) -> [u8; 32] {
    let mut q = [0u64; 4];
    let n = u8x32_to_u64x4(scalar);
    let _ = ffi_safe::jade_scalarmult_cryptopt_base(&mut q, &n);
    u64x4_to_u8x32(&q)
}

// ================================================================
// X25519: bedrock2 ToCString extraction (exact verified code)
// ================================================================

/// X25519 from bedrock2's ToCString — the exact code that fiat-crypto's
/// WP proofs verify, extracted to C and compiled by clang -O3.
///
/// Note: bedrock2's x25519 clamps the scalar in-place, so we pass a copy.
pub fn x25519_bedrock2(scalar: &[u8; 32], point: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut sk_copy = *scalar;
    ffi_safe::bedrock2_x25519(&mut out, &mut sk_copy, point);
    out
}

// ================================================================
// X25519: fiat-crypto C path (bedrock2-equivalent)
// ================================================================

/// X25519 using fiat-crypto verified C field arithmetic.
///
/// This uses the same 5-limb unsaturated Solinas representation and
/// Montgomery ladder as bedrock2's MontgomeryLadder.v, compiled via
/// clang -O3. Represents the performance of the bedrock2 -> ToJasmin
/// verification chain (same algorithm, different backend compiler).
pub fn x25519_fiat_c(scalar: &[u8; 32], point: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    ffi_safe::fiat_x25519_bytes(&mut out, scalar, point);
    out
}

// ================================================================
// X25519: Hybrid path (Rust ladder + CryptOpt/Jasmin field ops)
// ================================================================

/// X25519 scalar multiplication using the hybrid path.
///
/// Montgomery ladder in Rust calling CryptOpt mul/square + Jasmin add/sub.
pub fn x25519_hybrid(scalar: &[u8; 32], point: &[u8; 32]) -> [u8; 32] {
    let mut k = *scalar;
    // Clamp scalar
    k[0] &= 248;
    k[31] &= 127;
    k[31] |= 64;

    let mut u = Fe25519::zero();
    u.0 = u8x32_to_u64x4(point);
    u.0[3] &= 0x7fffffffffffffff; // clear high bit

    let result = montgomery_ladder(&k, &u);

    let mut out = Fe25519::zero();
    fe_tobytes(&mut out, &result);
    u64x4_to_u8x32(&out.0)
}

/// Montgomery ladder: 255 iterations of add-and-double.
fn montgomery_ladder(k: &[u8; 32], u: &Fe25519) -> Fe25519 {
    let mut x2 = Fe25519::from_limbs([1, 0, 0, 0]);
    let mut z2 = Fe25519::zero();
    let mut x3 = *u;
    let mut z3 = Fe25519::from_limbs([1, 0, 0, 0]);

    let mut swap: u64 = 0;

    for i in (0..255).rev() {
        let byte_idx = (i >> 3) as usize;
        let bit_idx = i & 7;
        let bit = ((k[byte_idx] >> bit_idx) & 1) as u64;

        let s = swap ^ bit;
        fe_cswap(&mut x2, &mut x3, s);
        fe_cswap(&mut z2, &mut z3, s);
        swap = bit;

        ladder_step(u, &mut x2, &mut z2, &mut x3, &mut z3);
    }

    fe_cswap(&mut x2, &mut x3, swap);
    fe_cswap(&mut z2, &mut z3, swap);

    // x2 / z2
    let z_inv = fe_invert(&z2);
    let mut result = Fe25519::zero();
    fe_mul(&mut result, &x2, &z_inv);
    result
}

/// Combined add-and-double step of the Montgomery ladder.
///
/// Given the projective x-coordinates (X2:Z2) and (X3:Z3) of two points
/// whose difference is u, compute the next pair.
fn ladder_step(
    u: &Fe25519,
    x2: &mut Fe25519, z2: &mut Fe25519,
    x3: &mut Fe25519, z3: &mut Fe25519,
) {
    let mut a = Fe25519::zero();
    let mut b = Fe25519::zero();
    let mut c = Fe25519::zero();
    let mut d = Fe25519::zero();
    let mut e = Fe25519::zero();
    let mut aa = Fe25519::zero();
    let mut bb = Fe25519::zero();
    let mut da = Fe25519::zero();
    let mut cb = Fe25519::zero();
    let mut t = Fe25519::zero();

    fe_add(&mut a, x2, z2);       // A = X2 + Z2
    fe_sub(&mut b, x2, z2);       // B = X2 - Z2
    fe_add(&mut c, x3, z3);       // C = X3 + Z3
    fe_sub(&mut d, x3, z3);       // D = X3 - Z3

    fe_square(&mut aa, &a);       // AA = A^2
    fe_square(&mut bb, &b);       // BB = B^2
    fe_mul(&mut da, &d, &a);      // DA = D * A
    fe_mul(&mut cb, &c, &b);      // CB = C * B

    fe_sub(&mut e, &aa, &bb);     // E = AA - BB
    fe_mul(x2, &aa, &bb);         // X4 = AA * BB

    fe_add(&mut t, &da, &cb);     // DA + CB
    fe_square(x3, &t);            // X5 = (DA + CB)^2

    fe_sub(&mut t, &da, &cb);     // DA - CB
    t = sq(&t);                    // (DA - CB)^2
    fe_mul(z3, u, &t);            // Z5 = u * (DA - CB)^2

    fe_mul_a24(&mut t, &e);       // a24 * E
    t = { let c = t; let mut r = Fe25519::zero(); fe_add(&mut r, &c, &aa); r }; // AA + a24*E
    fe_mul(z2, &e, &t);           // Z4 = E * (AA + a24*E)
}

/// Field inversion via Fermat's little theorem: a^(p-2) mod p.
///
/// Uses the same addition chain as libjade (Bernstein's chain for 2^255-21).
fn fe_invert(a: &Fe25519) -> Fe25519 {
    fn sqn(a: &Fe25519, n: usize) -> Fe25519 {
        let mut r = sq(a);
        for _ in 1..n { r = sq(&r); }
        r
    }

    let z2 = sq(a);                         // z1^2
    let z8 = sq(&sq(&z2));                  // z2^4
    let z9 = mul(a, &z8);                   // z1*z8
    let z11 = mul(&z2, &z9);               // z2*z9
    let z22 = sq(&z11);                     // z11^2
    let z_5_0 = mul(&z9, &z22);            // z9*z22

    let z_10_0 = mul(&z_5_0, &sqn(&z_5_0, 5));
    let z_20_0 = mul(&z_10_0, &sqn(&z_10_0, 10));
    let z_40_0 = mul(&z_20_0, &sqn(&z_20_0, 20));
    let z_50_0 = mul(&z_10_0, &sqn(&z_40_0, 10));
    let z_100_0 = mul(&z_50_0, &sqn(&z_50_0, 50));
    let z_200_0 = mul(&z_100_0, &sqn(&z_100_0, 100));
    let z_250_0 = mul(&z_50_0, &sqn(&z_200_0, 50));
    let z_255_5 = sqn(&z_250_0, 5);
    mul(&z11, &z_255_5)                     // z_255_21
}

// ================================================================
// Byte/limb conversion helpers
// ================================================================

/// Read a little-endian `u64` from `bytes[OFFSET..OFFSET+8]`.
///
/// Total function: the slice indices are checked at compile time (the input
/// is `&[u8; 32]` and `OFFSET + 8 <= 32` for every call site — enforced by
/// `static_assertions::const_assert!` below).  No `unwrap` / `unsafe`.
///
/// See `docs/performance-and-panic-freeness-2026-05-13.md` §2.3 step (b):
/// total-function rewrite that removes the `try_into().unwrap()` pattern.
#[inline(always)]
fn u64_from_le_at_32<const OFFSET: usize>(bytes: &[u8; 32]) -> u64 {
    // Compile-time bound check: ensures `OFFSET + 8 <= 32`.  If a caller
    // ever instantiates with a bad offset, this fires at monomorphisation.
    const { assert!(OFFSET + 8 <= 32, "OFFSET out of range for [u8; 32]") };
    let chunk: [u8; 8] = [
        bytes[OFFSET],
        bytes[OFFSET + 1],
        bytes[OFFSET + 2],
        bytes[OFFSET + 3],
        bytes[OFFSET + 4],
        bytes[OFFSET + 5],
        bytes[OFFSET + 6],
        bytes[OFFSET + 7],
    ];
    u64::from_le_bytes(chunk)
}

#[inline]
fn u8x32_to_u64x4(bytes: &[u8; 32]) -> [u64; 4] {
    [
        u64_from_le_at_32::<0>(bytes),
        u64_from_le_at_32::<8>(bytes),
        u64_from_le_at_32::<16>(bytes),
        u64_from_le_at_32::<24>(bytes),
    ]
}

#[inline]
fn u64x4_to_u8x32(limbs: &[u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..8].copy_from_slice(&limbs[0].to_le_bytes());
    out[8..16].copy_from_slice(&limbs[1].to_le_bytes());
    out[16..24].copy_from_slice(&limbs[2].to_le_bytes());
    out[24..32].copy_from_slice(&limbs[3].to_le_bytes());
    out
}

// ================================================================
// Tests
// ================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // RFC 7748 test vector
    const SCALAR: [u8; 32] = [
        0xa5, 0x46, 0xe3, 0x6b, 0xf0, 0x52, 0x7c, 0x9d,
        0x3b, 0x16, 0x15, 0x4b, 0x82, 0x46, 0x5e, 0xdd,
        0x62, 0x14, 0x4c, 0x0a, 0xc1, 0xfc, 0x5a, 0x18,
        0x50, 0x6a, 0x22, 0x44, 0xba, 0x44, 0x9a, 0xc4,
    ];
    const U_COORD: [u8; 32] = [
        0xe6, 0xdb, 0x68, 0x67, 0x58, 0x30, 0x30, 0xdb,
        0x35, 0x94, 0xc1, 0xa4, 0x24, 0xb1, 0x5f, 0x7c,
        0x72, 0x66, 0x24, 0xec, 0x26, 0xb3, 0x35, 0x3b,
        0x10, 0xa9, 0x03, 0xa6, 0xd0, 0xab, 0x1c, 0x4c,
    ];
    const EXPECTED: [u8; 32] = [
        0xc3, 0xda, 0x55, 0x37, 0x9d, 0xe9, 0xc6, 0x90,
        0x8e, 0x94, 0xea, 0x4d, 0xf2, 0x8d, 0x08, 0x4f,
        0x32, 0xec, 0xcf, 0x03, 0x49, 0x1c, 0x71, 0xf7,
        0x54, 0xb4, 0x07, 0x55, 0x77, 0xa2, 0x85, 0x52,
    ];

    #[test]
    fn test_x25519_jasmin_rfc7748() {
        let result = x25519_jasmin(&SCALAR, &U_COORD);
        assert_eq!(result, EXPECTED, "pure Jasmin path failed RFC 7748 vector");
    }

    #[test]
    fn test_x25519_fiat_c_rfc7748() {
        let result = x25519_fiat_c(&SCALAR, &U_COORD);
        assert_eq!(result, EXPECTED, "fiat-c path failed RFC 7748 vector");
    }

    #[test]
    fn test_x25519_bedrock2_rfc7748() {
        let result = x25519_bedrock2(&SCALAR, &U_COORD);
        assert_eq!(result, EXPECTED, "bedrock2 path failed RFC 7748 vector");
    }

    // Tests for the bedrock2 -> Jasmin field ops (Phase 1 hybrid backend).
    // These verify the 7 jasminc-compiled functions produce correct output.

    #[test]
    fn test_bedrock2_jasmin_clamp() {
        // Same scalar bytes as SCALAR, interpreted as u64[4] little-endian.
        let mut sk = [
            u64::from_le_bytes(SCALAR[0..8].try_into().unwrap()),
            u64::from_le_bytes(SCALAR[8..16].try_into().unwrap()),
            u64::from_le_bytes(SCALAR[16..24].try_into().unwrap()),
            u64::from_le_bytes(SCALAR[24..32].try_into().unwrap()),
        ];
        let original_byte0 = SCALAR[0];
        let original_byte31 = SCALAR[31];

        bedrock2_jasmin::clamp(&mut sk);

        // Check the clamp produced RFC 7748 requirements:
        let result_byte0 = (sk[0] & 0xFF) as u8;
        let result_byte31 = ((sk[3] >> 56) & 0xFF) as u8;
        assert_eq!(result_byte0, original_byte0 & 248,
                   "clamp: byte 0 should be original & 248");
        assert_eq!(result_byte31, (original_byte31 & 127) | 64,
                   "clamp: byte 31 should be (original & 127) | 64");
    }

    #[test]
    fn test_bedrock2_jasmin_copy_and_from_word() {
        let mut a = Fe25519_5limb([0; 5]);
        bedrock2_jasmin::from_word(&mut a, 42);
        assert_eq!(a.0[0], 42, "from_word: low limb should be w");

        let mut b = Fe25519_5limb([0; 5]);
        bedrock2_jasmin::copy(&mut b, &a);
        assert_eq!(a, b, "copy: output must equal input");
    }

    #[test]
    fn test_bedrock2_jasmin_add_symmetry() {
        // fe25519_add is commutative even under unsaturated Solinas
        // because the output is just a limb-wise sum.
        let a = Fe25519_5limb([1, 2, 3, 4, 5]);
        let b = Fe25519_5limb([10, 20, 30, 40, 50]);
        let mut ab = Fe25519_5limb([0; 5]);
        let mut ba = Fe25519_5limb([0; 5]);
        bedrock2_jasmin::add(&mut ab, &a, &b);
        bedrock2_jasmin::add(&mut ba, &b, &a);
        assert_eq!(ab, ba, "add should be commutative limb-wise");
    }

    #[test]
    fn test_bedrock2_jasmin_cswap() {
        let mut a = Fe25519_5limb([1, 2, 3, 4, 5]);
        let mut b = Fe25519_5limb([10, 20, 30, 40, 50]);
        let a_orig = a;
        let b_orig = b;

        // mask = 0: no swap
        bedrock2_jasmin::cswap(0, &mut a, &mut b);
        assert_eq!(a, a_orig);
        assert_eq!(b, b_orig);

        // mask = 1: swap
        bedrock2_jasmin::cswap(1, &mut a, &mut b);
        assert_eq!(a, b_orig);
        assert_eq!(b, a_orig);
    }

    #[test]
    fn test_x25519_hybrid_rfc7748() {
        let result = x25519_hybrid(&SCALAR, &U_COORD);
        assert_eq!(result, EXPECTED, "hybrid path failed RFC 7748 vector");
    }

    #[test]
    fn test_x25519_cryptopt_rfc7748() {
        let result = x25519_cryptopt(&SCALAR, &U_COORD);
        assert_eq!(result, EXPECTED, "cryptopt path failed RFC 7748 vector");
    }

    // RFC 7748 second test vector
    #[test]
    fn test_x25519_vector2() {
        let scalar: [u8; 32] = [
            0x4b, 0x66, 0xe9, 0xd4, 0xd1, 0xb4, 0x67, 0x3c,
            0x5a, 0xd2, 0x26, 0x91, 0x95, 0x7d, 0x6a, 0xf5,
            0xc1, 0x1b, 0x64, 0x21, 0xe0, 0xea, 0x01, 0xd4,
            0x2c, 0xa4, 0x16, 0x9e, 0x79, 0x18, 0xba, 0x0d,
        ];
        let u_coord: [u8; 32] = [
            0xe5, 0x21, 0x0f, 0x12, 0x78, 0x68, 0x11, 0xd3,
            0xf4, 0xb7, 0x95, 0x9d, 0x05, 0x38, 0xae, 0x2c,
            0x31, 0xdb, 0xe7, 0x10, 0x6f, 0xc0, 0x3c, 0x3e,
            0xfc, 0x4c, 0xd5, 0x49, 0xc7, 0x15, 0xa4, 0x93,
        ];
        let expected: [u8; 32] = [
            0x95, 0xcb, 0xde, 0x94, 0x76, 0xe8, 0x90, 0x7d,
            0x7a, 0xad, 0xe4, 0x5c, 0xb4, 0xb8, 0x73, 0xf8,
            0x8b, 0x59, 0x5a, 0x68, 0x79, 0x9f, 0xa1, 0x52,
            0xe6, 0xf8, 0xf7, 0x64, 0x7a, 0xac, 0x79, 0x57,
        ];

        let r1 = x25519_jasmin(&scalar, &u_coord);
        assert_eq!(r1, expected, "jasmin vector 2");

        let r2 = x25519_hybrid(&scalar, &u_coord);
        assert_eq!(r2, expected, "hybrid vector 2");
    }

    // Cross-check: both paths agree on random-looking inputs
    #[test]
    fn test_jasmin_hybrid_agree() {
        // Use a fixed "random" scalar and point
        let scalar: [u8; 32] = {
            let mut s = [0u8; 32];
            for i in 0..32 { s[i] = (i as u8).wrapping_mul(37).wrapping_add(13); }
            s
        };
        let point: [u8; 32] = {
            let mut p = [0u8; 32];
            for i in 0..32 { p[i] = (i as u8).wrapping_mul(53).wrapping_add(7); }
            p[31] &= 0x7f;
            p
        };

        let r1 = x25519_jasmin(&scalar, &point);
        let r2 = x25519_hybrid(&scalar, &point);
        assert_eq!(r1, r2, "jasmin and hybrid paths disagree");
    }

    // Base point multiplication
    #[test]
    fn test_x25519_base() {
        let scalar = SCALAR;
        let base = {
            let mut b = [0u8; 32];
            b[0] = 9; // base point
            b
        };

        let r1 = x25519_jasmin_base(&scalar);
        let r2 = x25519_jasmin(&scalar, &base);
        assert_eq!(r1, r2, "base vs explicit base point");

        let r3 = x25519_hybrid(&scalar, &base);
        assert_eq!(r1, r3, "base jasmin vs hybrid");
    }
}
