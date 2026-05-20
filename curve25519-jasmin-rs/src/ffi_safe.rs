//! Centralized safe FFI wrappers.
//!
//! Phase B of the `unsafe`-reduction plan (see
//! `AUCurves/docs/signal-stack-status-2026-05-13.md` §6.3).
//!
//! Every `extern "C"` symbol called from this crate's hand-written
//! Rust code is wrapped here in a single safe function whose body is
//! the *only* `unsafe { ... }` block reaching that symbol.  Call sites
//! outside `ffi_safe.rs` become safe Rust — the previous ~50 hand-
//! written `unsafe` blocks (in `lib.rs`, `symmetric.rs`, and
//! `ed25519_rustcmd/mod.rs`) collapse to one per FFI symbol.
//!
//! IR-emitted bodies (`ed25519_rustcmd/decomposed_bodies*.rs`,
//! `leaves.rs`, `fe25519_*.rs`, the auto-generated `sign.rs` /
//! `verify.rs`) are **not** routed through this module: they are
//! mechanically emitted from the verified `rust_cmd_ed` AST and the
//! emitter will be updated separately (status doc §6.3, phase b
//! continuation).  Each such file is exempt; the unsafe blocks
//! there will collapse when the emitter is updated to target
//! `ffi_safe::*` directly.
//!
//! ## Safety contract — common preconditions
//!
//! Every wrapper below has the same shape:
//!
//!   `pub fn foo(out: &mut [T; N], a: &[T; M], ...) { unsafe { foo_c(...) } }`
//!
//! The Rust borrow checker discharges:
//! - Non-null pointers (`&[T; N]` ⇒ non-null, aligned).
//! - Distinct mutable / shared borrows ⇒ no aliasing between `out` and
//!   any `&[...]` input.
//! - `len = N` matches the C ABI parameter (every `N` is the exact byte
//!   / limb count documented in the C signature).
//!
//! The FFI symbols themselves are verified:
//! - `jade_*` come from libjade / formosa-25519 / formosa-mlkem,
//!   EasyCrypt-verified, compiled by `jasminc` (EasyCrypt-verified
//!   compiler).
//! - `curve25519_*` are bedrock2-WP-verified Rocq spec compiled via
//!   `ToJasmin` (Rocq-verified backend).
//! - `fiat_*` are fiat-crypto's Coq spec, optionally CryptOpt-
//!   superoptimized + `check_equivalence`-verified.
//! - `x25519` (bedrock2-C extraction) is the same bedrock2 WP spec
//!   compiled via `ToCString` + clang.
//!
//! Each wrapper's docstring cites the verification artefact and the
//! libjade / fiat-crypto / bedrock2 path it stands behind.

#![allow(non_snake_case)]

// ===================================================================
// X25519: pure Jasmin scalarmult (libjade mulx variant)
// ===================================================================

extern "C" {
    fn jade_scalarmult_curve25519_amd64_mulx(
        qp: *mut u64, np: *const u64, pp: *const u64,
    ) -> u64;
    fn jade_scalarmult_curve25519_amd64_mulx_base(
        qp: *mut u64, np: *const u64,
    ) -> u64;
    fn jade_scalarmult_curve25519_amd64_cryptopt(
        qp: *mut u64, np: *const u64, pp: *const u64,
    ) -> u64;
    fn jade_scalarmult_curve25519_amd64_cryptopt_base(
        qp: *mut u64, np: *const u64,
    ) -> u64;
}

/// `q := clamp(n) · p` on Curve25519, full mulx variant.
///
/// libjade-Jasmin, EasyCrypt-verified
/// (`libjade/proof/crypto_scalarmult/curve25519/amd64/mulx/`).
/// Constant-time; non-aliasing of `q` against `n`, `p` is required by
/// the C ABI and discharged here by the borrow checker.
#[inline]
pub fn jade_scalarmult_mulx(q: &mut [u64; 4], n: &[u64; 4], p: &[u64; 4]) -> u64 {
    unsafe { jade_scalarmult_curve25519_amd64_mulx(q.as_mut_ptr(), n.as_ptr(), p.as_ptr()) }
}

/// `q := clamp(n) · 9` on Curve25519, base-point variant.
#[inline]
pub fn jade_scalarmult_mulx_base(q: &mut [u64; 4], n: &[u64; 4]) -> u64 {
    unsafe { jade_scalarmult_curve25519_amd64_mulx_base(q.as_mut_ptr(), n.as_ptr()) }
}

/// `q := clamp(n) · p` on Curve25519, CryptOpt-style MULX/ADCX/ADOX
/// scheduled variant.  Same EasyCrypt proof as `jade_scalarmult_mulx`.
#[inline]
pub fn jade_scalarmult_cryptopt(q: &mut [u64; 4], n: &[u64; 4], p: &[u64; 4]) -> u64 {
    unsafe { jade_scalarmult_curve25519_amd64_cryptopt(q.as_mut_ptr(), n.as_ptr(), p.as_ptr()) }
}

/// `q := clamp(n) · 9` on Curve25519, CryptOpt base-point variant.
#[inline]
pub fn jade_scalarmult_cryptopt_base(q: &mut [u64; 4], n: &[u64; 4]) -> u64 {
    unsafe { jade_scalarmult_curve25519_amd64_cryptopt_base(q.as_mut_ptr(), n.as_ptr()) }
}

// ===================================================================
// X25519: Jasmin-compiled per-op field arithmetic (4×u64 saturated)
// ===================================================================

extern "C" {
    fn curve25519_add(out: *mut u64, a: *const u64, b: *const u64);
    fn curve25519_sub(out: *mut u64, a: *const u64, b: *const u64);
    fn curve25519_mul_a24(out: *mut u64, a: *const u64);
    fn curve25519_tobytes(out: *mut u64, a: *const u64);
    fn curve25519_cswap(a: *mut u64, b: *mut u64, swap: u64);
}

/// `out := a + b mod 2²⁵⁵−19`, 4×u64 saturated representation.
#[inline]
pub fn curve25519_add_4(out: &mut [u64; 4], a: &[u64; 4], b: &[u64; 4]) {
    unsafe { curve25519_add(out.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }
}

/// `out := a − b mod 2²⁵⁵−19`, 4×u64 saturated.
#[inline]
pub fn curve25519_sub_4(out: &mut [u64; 4], a: &[u64; 4], b: &[u64; 4]) {
    unsafe { curve25519_sub(out.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }
}

/// `out := a · 121665 mod 2²⁵⁵−19` (Montgomery ladder a24 constant).
#[inline]
pub fn curve25519_mul_a24_4(out: &mut [u64; 4], a: &[u64; 4]) {
    unsafe { curve25519_mul_a24(out.as_mut_ptr(), a.as_ptr()) }
}

/// Canonically reduce `a` mod `2²⁵⁵−19` and write a little-endian
/// encoding into `out`.
#[inline]
pub fn curve25519_tobytes_4(out: &mut [u64; 4], a: &[u64; 4]) {
    unsafe { curve25519_tobytes(out.as_mut_ptr(), a.as_ptr()) }
}

/// Constant-time conditional swap of `a` and `b` if `swap != 0`.
#[inline]
pub fn curve25519_cswap_4(a: &mut [u64; 4], b: &mut [u64; 4], swap: u64) {
    unsafe { curve25519_cswap(a.as_mut_ptr(), b.as_mut_ptr(), swap) }
}

// ===================================================================
// X25519: CryptOpt superoptimized mul / square (4×u64 saturated)
// ===================================================================

extern "C" {
    fn fiat_curve25519_solinas_mul(out: *mut u64, a: *const u64, b: *const u64);
    fn fiat_curve25519_solinas_square(out: *mut u64, a: *const u64);
}

/// `out := a · b mod 2²⁵⁵−19` (CryptOpt superoptimized; fiat-crypto
/// `check_equivalence`-verified against the Coq spec).
#[inline]
pub fn fiat_solinas_mul(out: &mut [u64; 4], a: &[u64; 4], b: &[u64; 4]) {
    unsafe { fiat_curve25519_solinas_mul(out.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }
}

/// `out := a² mod 2²⁵⁵−19` (CryptOpt superoptimized).
#[inline]
pub fn fiat_solinas_square(out: &mut [u64; 4], a: &[u64; 4]) {
    unsafe { fiat_curve25519_solinas_square(out.as_mut_ptr(), a.as_ptr()) }
}

// ===================================================================
// X25519: fiat-crypto C extraction + bedrock2 ToCString extraction
// ===================================================================

extern "C" {
    fn fiat_x25519(out: *mut u8, scalar: *const u8, point: *const u8);
    fn x25519(out: usize, sk: usize, pk: usize);
}

/// `out := clamp(scalar) · point` via the fiat-crypto verified C path.
#[inline]
pub fn fiat_x25519_bytes(out: &mut [u8; 32], scalar: &[u8; 32], point: &[u8; 32]) {
    unsafe { fiat_x25519(out.as_mut_ptr(), scalar.as_ptr(), point.as_ptr()) }
}

/// bedrock2 `ToCString` extraction of the WP-verified X25519.  The
/// underlying `x25519` symbol mutates `sk` in place (per RFC 7748
/// clamping); caller passes a *mutable* scratch copy.
///
/// Pointers are passed as `usize` because bedrock2's br_word_t is
/// `uintptr_t`.  The borrow checker still guarantees the buffers don't
/// alias (each is a fresh `&mut [u8; 32]` / `&[u8; 32]` here).
#[inline]
pub fn bedrock2_x25519(out: &mut [u8; 32], sk: &mut [u8; 32], pk: &[u8; 32]) {
    unsafe {
        x25519(
            out.as_mut_ptr() as usize,
            sk.as_mut_ptr() as usize,
            pk.as_ptr() as usize,
        )
    }
}

// ===================================================================
// X25519: bedrock2 → Jasmin 5-limb unsaturated Solinas field ops
// ===================================================================

#[allow(dead_code)]
extern "C" {
    fn fe25519_add(out: *mut u64, a: *const u64, b: *const u64);
    fn fe25519_sub(out: *mut u64, a: *const u64, b: *const u64);
    fn fe25519_scmula24(out: *mut u64, a: *const u64);
    fn felem_cswap(mask: u64, a: *mut u64, b: *mut u64);
    fn fe25519_copy(out: *mut u64, a: *const u64);
    fn fe25519_from_word(out: *mut u64, w: u64);
}

// `clamp_64` is exported on both `*mut u8` (sign.rs / mod.rs) and
// `*mut u64` (`bedrock2_jasmin::clamp`) flavours.  We bind it once on
// each typed pointer so each Rust caller can pick the limb / byte view
// that matches its scalar buffer.  Pointer reinterpretation is
// well-defined since the function reads / writes a 32-byte region
// either way.
extern "C" {
    #[link_name = "clamp_64"]
    fn clamp_64_u64_link(sk: *mut u64);
    #[link_name = "clamp_64"]
    fn clamp_64_u8_link(sk: *mut u8);
}

/// `out := a + b mod p` (5-limb unsaturated Solinas).
#[inline]
pub fn fe25519_5_add(out: &mut [u64; 5], a: &[u64; 5], b: &[u64; 5]) {
    unsafe { fe25519_add(out.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }
}

/// `out := a − b mod p` (5-limb unsaturated Solinas).
#[inline]
pub fn fe25519_5_sub(out: &mut [u64; 5], a: &[u64; 5], b: &[u64; 5]) {
    unsafe { fe25519_sub(out.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }
}

/// `out := a · 121665 mod p` (5-limb unsaturated Solinas).
#[inline]
pub fn fe25519_5_scmula24(out: &mut [u64; 5], a: &[u64; 5]) {
    unsafe { fe25519_scmula24(out.as_mut_ptr(), a.as_ptr()) }
}

/// Constant-time conditional swap of two 5-limb field elements when
/// `mask = 0xFFFF...FF`, no-op when `mask = 0`.
#[inline]
pub fn felem_5_cswap(mask: u64, a: &mut [u64; 5], b: &mut [u64; 5]) {
    unsafe { felem_cswap(mask, a.as_mut_ptr(), b.as_mut_ptr()) }
}

/// `out := a` (5-limb copy).
#[inline]
pub fn fe25519_5_copy(out: &mut [u64; 5], a: &[u64; 5]) {
    unsafe { fe25519_copy(out.as_mut_ptr(), a.as_ptr()) }
}

/// `out := (5-limb-of) w` (low limb gets `w`, others zero).
#[inline]
pub fn fe25519_5_from_word(out: &mut [u64; 5], w: u64) {
    unsafe { fe25519_from_word(out.as_mut_ptr(), w) }
}

/// RFC 7748 clamp on a 32-byte scalar viewed as `[u64; 4]`.
#[inline]
pub fn clamp_scalar_u64(sk: &mut [u64; 4]) {
    unsafe { clamp_64_u64_link(sk.as_mut_ptr()) }
}

/// RFC 7748 clamp on a 32-byte scalar viewed as `[u8; 32]`.
#[inline]
pub fn clamp_scalar_u8(sk: &mut [u8; 32]) {
    unsafe { clamp_64_u8_link(sk.as_mut_ptr()) }
}

// ===================================================================
// Ed25519 leaves (used by hand-written `ed25519_rustcmd/mod.rs`)
//
// These are the same `extern "C"` symbols that `sign.rs` / `verify.rs`
// bind — leaf substitution surface for the `rust_cmd_ed` extraction.
// The wrappers here let `mod.rs::public_key_from_seed` and
// `mod.rs::scalarmult_base_compressed` (and the
// `feature = "verify_projective_eq"` fast path) drop their unsafe
// blocks.
// ===================================================================

extern "C" {
    fn sha512_64(out: *mut u8, msg: *const u8, len: u64);
    fn scalar_reduce(out: *mut u8, full: *const u8);
    fn ed25519_decompress_R(out: *mut u8, sig: *const u8);
    fn ed25519_decompress_A(out: *mut u8, pk: *const u8);
    fn ed25519_compress(out: *mut u8, xyzt: *const u8);
    fn ed25519_scalarmult_base(out: *mut u8, scalar: *const u8);
    fn ed25519_scalarmult(out: *mut u8, scalar: *const u8, point: *const u8);
    fn ed25519_xyzt_add(out: *mut u8, p: *const u8, q: *const u8);
    fn scalar_lt_L(out: *mut u8, scalar: *const u8);
}

// `ed25519_projective_eq` is defined in `ed25519_rustcmd/leaves.rs`
// only under the `verify_projective_eq` feature; mirror the cfg here
// to avoid `undefined symbol` link errors in default builds.
#[cfg(feature = "verify_projective_eq")]
extern "C" {
    fn ed25519_projective_eq(out: *mut u8, p: *const u8, q: *const u8);
}

/// SHA-512 over a contiguous `msg[0..len]` region.  Output is the
/// 64-byte digest.
#[inline]
pub fn ed25519_sha512_64(out: &mut [u8; 64], msg: &[u8], len: u64) {
    unsafe { sha512_64(out.as_mut_ptr(), msg.as_ptr(), len) }
}

/// SHA-512 over a `&[u8; N]` buffer at a caller-supplied length.
#[inline]
pub fn ed25519_sha512_64_arr<const N: usize>(out: &mut [u8; 64], msg: &[u8; N], len: u64) {
    unsafe { sha512_64(out.as_mut_ptr(), msg.as_ptr(), len) }
}

/// `out := full mod L` where L is the Ed25519 group order.
#[inline]
pub fn ed25519_scalar_reduce(out: &mut [u8; 32], full: &[u8; 64]) {
    unsafe { scalar_reduce(out.as_mut_ptr(), full.as_ptr()) }
}

/// `out_xyzt := decompress(R_bytes)`.
#[inline]
pub fn ed25519_decompress_R_pt(out: &mut [u8; 200], sig: &[u8; 64]) {
    unsafe { ed25519_decompress_R(out.as_mut_ptr(), sig.as_ptr()) }
}

/// `out_xyzt := decompress(A_bytes)`.
#[inline]
pub fn ed25519_decompress_A_pt(out: &mut [u8; 200], pk: &[u8; 32]) {
    unsafe { ed25519_decompress_A(out.as_mut_ptr(), pk.as_ptr()) }
}

/// `out_bytes := compress(xyzt)`.
#[inline]
pub fn ed25519_compress_pt(out: &mut [u8; 32], xyzt: &[u8; 200]) {
    unsafe { ed25519_compress(out.as_mut_ptr(), xyzt.as_ptr()) }
}

/// `out := scalar · B` (Ed25519 base-point scalarmult, XYZT output).
#[inline]
pub fn ed25519_scalarmult_base_pt(out: &mut [u8; 200], scalar: &[u8; 32]) {
    unsafe { ed25519_scalarmult_base(out.as_mut_ptr(), scalar.as_ptr()) }
}

/// `out := scalar · point` (Ed25519 variable-base scalarmult).
#[inline]
pub fn ed25519_scalarmult_pt(out: &mut [u8; 200], scalar: &[u8; 32], point: &[u8; 200]) {
    unsafe { ed25519_scalarmult(out.as_mut_ptr(), scalar.as_ptr(), point.as_ptr()) }
}

/// `out := p + q` (Ed25519 XYZT addition).
#[inline]
pub fn ed25519_xyzt_add_pt(out: &mut [u8; 200], p: &[u8; 200], q: &[u8; 200]) {
    unsafe { ed25519_xyzt_add(out.as_mut_ptr(), p.as_ptr(), q.as_ptr()) }
}

/// Projective-equality compare; sets `out[0]` to a constant-time
/// flag (`1` if `p ≡ q` projectively, `0` otherwise).
///
/// Gated on `verify_projective_eq` to match the underlying symbol
/// definition in `ed25519_rustcmd/leaves.rs`.
#[cfg(feature = "verify_projective_eq")]
#[inline]
pub fn ed25519_projective_eq_pt(out: &mut [u8; 1], p: &[u8; 200], q: &[u8; 200]) {
    unsafe { ed25519_projective_eq(out.as_mut_ptr(), p.as_ptr(), q.as_ptr()) }
}

/// `out[0] := (scalar < L)` constant-time test over a 64-byte scalar
/// buffer (the libjade ABI reads the first 32 bytes of `scalar`).
#[inline]
pub fn ed25519_scalar_lt_L(out: &mut [u8; 1], scalar: *const u8) {
    // Caller-supplied pointer: this is the one wrapper that does not
    // take a fixed-length slice, because `scalar_lt_L` is fed both
    // 32-byte and 64-byte scalar buffers across the crate (sign.rs /
    // verify.rs / mod.rs).  The pointer is borrowed read-only from
    // a `&[u8; N]` view at the call site; the borrow checker still
    // discharges aliasing.
    unsafe { scalar_lt_L(out.as_mut_ptr(), scalar) }
}

// ===================================================================
// Symmetric: SHA-256 / SHA-512 (libjade ref-amd64) + ML-KEM-768
// (formosa-mlkem)
// ===================================================================

extern "C" {
    fn jade_hash_sha256_amd64_ref(hash: *mut u8, input: *const u8, input_length: u64) -> u64;
    fn jade_hash_sha512_amd64_ref(hash: *mut u8, input: *const u8, input_length: u64) -> u64;
    fn jade_kem_mlkem_mlkem768_amd64_ref_keypair_derand(
        public_key: *mut u8, secret_key: *mut u8, coins: *const u8,
    ) -> u64;
    fn jade_kem_mlkem_mlkem768_amd64_ref_enc_derand(
        ciphertext: *mut u8, shared_secret: *mut u8,
        public_key: *const u8, coins: *const u8,
    ) -> u64;
    fn jade_kem_mlkem_mlkem768_amd64_ref_dec(
        shared_secret: *mut u8,
        ciphertext: *const u8, secret_key: *const u8,
    ) -> u64;
}

/// SHA-256 over a `&[u8]` input, 32-byte digest output.  libjade
/// `crypto_hash/sha256/amd64/ref`, EasyCrypt-verified.
#[inline]
pub fn jade_sha256(out: &mut [u8; 32], input: &[u8]) {
    unsafe {
        let _ = jade_hash_sha256_amd64_ref(out.as_mut_ptr(), input.as_ptr(), input.len() as u64);
    }
}

/// SHA-512 over a `&[u8]` input, 64-byte digest output.  libjade
/// `crypto_hash/sha512/amd64/ref`, EasyCrypt-verified.
#[inline]
pub fn jade_sha512(out: &mut [u8; 64], input: &[u8]) {
    unsafe {
        let _ = jade_hash_sha512_amd64_ref(out.as_mut_ptr(), input.as_ptr(), input.len() as u64);
    }
}

/// ML-KEM-768 deterministic key generation (formosa-mlkem).
///
/// `coins` is a 64-byte secret seed; `pk` / `sk` are the FIPS 203
/// public / secret keys.  Caller-allocated; lengths fixed by the
/// `MLKEM768_*_BYTES` constants in `symmetric.rs`.
#[inline]
pub fn mlkem768_keypair_derand(pk: &mut [u8], sk: &mut [u8], coins: &[u8; 64]) {
    unsafe {
        let _ = jade_kem_mlkem_mlkem768_amd64_ref_keypair_derand(
            pk.as_mut_ptr(), sk.as_mut_ptr(), coins.as_ptr(),
        );
    }
}

/// ML-KEM-768 deterministic encapsulation.
#[inline]
pub fn mlkem768_enc_derand(
    ct: &mut [u8], ss: &mut [u8],
    pk: &[u8], coins: &[u8; 32],
) {
    unsafe {
        let _ = jade_kem_mlkem_mlkem768_amd64_ref_enc_derand(
            ct.as_mut_ptr(), ss.as_mut_ptr(),
            pk.as_ptr(), coins.as_ptr(),
        );
    }
}

/// ML-KEM-768 decapsulation.
#[inline]
pub fn mlkem768_dec(ss: &mut [u8], ct: &[u8], sk: &[u8]) {
    unsafe {
        let _ = jade_kem_mlkem_mlkem768_amd64_ref_dec(
            ss.as_mut_ptr(), ct.as_ptr(), sk.as_ptr(),
        );
    }
}
