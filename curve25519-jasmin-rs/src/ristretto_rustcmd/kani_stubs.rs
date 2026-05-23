//! Abstract Kani stub models for the extern-"C" field/Ristretto leaves
//! called by the extracted `decode.rs` / `encode.rs`.
//!
//! ## Why these exist
//!
//! Kani cannot execute the real field-arithmetic leaves for two
//! reasons:
//!
//!   1. They are reached via `unsafe extern "C" { fn ... }`
//!      declarations in `decode.rs`/`encode.rs`.  Even though Rust
//!      definitions exist in the same crate (`fe25519_portable.rs`,
//!      `leaves.rs`, `encode_leaves.rs`), Kani treats an `extern`
//!      declaration without a stub as an opaque foreign function
//!      (`unsupported_construct`, kani#2423).
//!   2. The real bodies run the ~270-op `pow22523` addition chain and
//!      fiat radix-2^51 multiplies — intractable for the SMT backend
//!      and, more importantly, IRRELEVANT to the property under test.
//!
//! The Kani harnesses verify the decode/encode **GLUE**:
//! the slot byte-shuffling, the leaf-call dispatch, the
//! `copy_from_slice` lengths, and the `REdFor` / `REdSelect` index
//! arithmetic — i.e. exactly where the two real B.5c bring-up bugs
//! lived (the 32-vs-40-byte felem buffer overrun and the
//! `copy_from_slice` length-mismatch panic).  So each leaf is replaced
//! by an ABSTRACT model that returns `kani::any()`-filled buffers of
//! the EXACT declared length.  The model is itself memory-safe (writes
//! precisely the contract length: 40 for felems, 32 for the canonical
//! pack output, 1 for status / was-square, 200 for the packed xyzt),
//! so any out-of-bounds write the harness reports is a bug in the
//! CALLER glue, not in the stub.
//!
//! These functions are wired in by `#[kani::stub(target, replacement)]`
//! on each harness in `kani_proofs.rs`.  Kani resolves the `target`
//! (the `extern "C"` declaration's Rust path, e.g.
//! `super::decode::fe25519_mul`) and substitutes the replacement body
//! at every call site WITHIN that harness only.  Nothing here is
//! `#[no_mangle]`, so there is no duplicate-symbol clash with the real
//! leaves, and the whole module is `#[cfg(kani)]`-gated so the normal
//! (non-Kani) build never compiles it.

#![allow(dead_code, unused_variables)]

/// Fill `len` bytes at `out` with arbitrary (symbolic) data.
///
/// Writes EXACTLY `len` bytes — the declared contract length of the
/// felem / buffer.  This is the only thing the stub asserts about the
/// real leaf: it touches its declared output region and nothing more.
#[inline]
unsafe fn write_any_bytes(out: *mut u8, len: usize) {
    let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(out, len) };
    for b in dst.iter_mut() {
        *b = kani::any();
    }
}

// ----------------------------------------------------------------
// Field arithmetic (byte ABI, 40-byte felems).  Real bodies live in
// `ed25519_rustcmd::fe25519_portable` and are stubbed away here.
// ----------------------------------------------------------------

/// Abstract `fe25519_mul(out, a, b)`: out := any 40-byte felem.
pub unsafe extern "C" fn fe25519_mul_stub(out: *mut u8, _a: *const u8, _b: *const u8) {
    unsafe { write_any_bytes(out, 40) };
}

/// Abstract `fe25519_add(out, a, b)`: out := any 40-byte felem.
pub unsafe extern "C" fn fe25519_add_stub(out: *mut u8, _a: *const u8, _b: *const u8) {
    unsafe { write_any_bytes(out, 40) };
}

/// Abstract `fe25519_sub(out, a, b)`: out := any 40-byte felem.
pub unsafe extern "C" fn fe25519_sub_stub(out: *mut u8, _a: *const u8, _b: *const u8) {
    unsafe { write_any_bytes(out, 40) };
}

/// Abstract `fe25519_sq(out, a)`: out := any 40-byte felem.
pub unsafe extern "C" fn fe25519_sq_stub(out: *mut u8, _a: *const u8) {
    unsafe { write_any_bytes(out, 40) };
}

/// Abstract `fe25519_inv(out, a)`: out := any 40-byte felem.
pub unsafe extern "C" fn fe25519_inv_stub(out: *mut u8, _a: *const u8) {
    unsafe { write_any_bytes(out, 40) };
}

// ----------------------------------------------------------------
// Ristretto algorithmic leaves.
// ----------------------------------------------------------------

/// Abstract `ristretto_parse_canonical_felem(s_out, status_out, bs_in)`:
/// writes any 40-byte felem to `s_out` and any status byte to
/// `status_out`.  The harness must be panic-free for BOTH status
/// values (accept / reject), so the symbolic status byte exercises
/// both decode branches.
pub unsafe extern "C" fn ristretto_parse_canonical_felem_stub(
    s_out: *mut u8,
    status_out: *mut u8,
    _bs_in: *const u8,
) {
    unsafe { write_any_bytes(s_out, 40) };
    unsafe { *status_out = kani::any() };
}

/// Abstract `ristretto_sqrt_ratio_m1(ws_out, r_out, u_in, v_in)`:
/// writes any was-square byte to `ws_out` and any 40-byte root to
/// `r_out`.  The symbolic `ws` byte exercises both the square /
/// non-square decode/encode branches.
pub unsafe extern "C" fn ristretto_sqrt_ratio_m1_stub(
    ws_out: *mut u8,
    r_out: *mut u8,
    _u_in: *const u8,
    _v_in: *const u8,
) {
    unsafe { *ws_out = kani::any() };
    unsafe { write_any_bytes(r_out, 40) };
}

/// Abstract `ristretto_pack_canonical_felem(out, s_in)`: writes any
/// 32-byte canonical encoding to `out`.
pub unsafe extern "C" fn ristretto_pack_canonical_felem_stub(out: *mut u8, _s_in: *const u8) {
    unsafe { write_any_bytes(out, 32) };
}

// ----------------------------------------------------------------
// Data-movement leaves (memmove-class).
// ----------------------------------------------------------------

/// Abstract `pack_xyzt5(out, x, y, z, ta, tb)`: writes any 200-byte
/// packed buffer to `out`.  (We only need memory-safety of the caller
/// glue; the real packer's exact layout is checked by its own unit
/// test in `leaves.rs`.)
pub unsafe extern "C" fn pack_xyzt5_stub(
    out: *mut u8,
    _x: *const u8,
    _y: *const u8,
    _z: *const u8,
    _ta: *const u8,
    _tb: *const u8,
) {
    unsafe { write_any_bytes(out, 200) };
}

/// Abstract `unpack_xyzt5(x_out, y_out, z_out, ta_out, tb_out, xyzt_in)`:
/// writes any 40-byte felem to each of the five output slots.
pub unsafe extern "C" fn unpack_xyzt5_stub(
    x_out: *mut u8,
    y_out: *mut u8,
    z_out: *mut u8,
    ta_out: *mut u8,
    tb_out: *mut u8,
    _xyzt_in: *const u8,
) {
    unsafe { write_any_bytes(x_out, 40) };
    unsafe { write_any_bytes(y_out, 40) };
    unsafe { write_any_bytes(z_out, 40) };
    unsafe { write_any_bytes(ta_out, 40) };
    unsafe { write_any_bytes(tb_out, 40) };
}
