//! Leaf FFI implementations for the extracted Ristretto255
//! decode/encode.
//!
//! Companion to [`leaves.rs`](../ed25519_rustcmd/leaves.rs) of the
//! Ed25519 path.  Field-arithmetic leaves (`fe25519_mul`,
//! `fe25519_add`, `fe25519_sub`, `fe25519_sq`) are SHARED with the
//! Ed25519 leaves module — no need to redeclare here.
//!
//! Constants (`1`, `2`, Curve25519 `d`) are NO LONGER leaves: as of
//! T1 (2026-05-23) the decoder AST writes them via the verified
//! `REdSetBytes` IR constructor, which emits a literal `[b0u8, ...]`
//! array assignment in `decode.rs`.  The former `fe25519_const_*`
//! trusted setters were deleted — see `HAND_WRITTEN_AUDIT.md`.
//!
//! What this module still provides:
//!
//! - **5-felem packer** (memmove-class data movement, matches
//!   `End2End/Ed25519/XyztAddVerified.v:pack_xyzt5`):
//!     - `pack_xyzt5(out: *mut u8, x, y, z, ta, tb: *const u8)` —
//!       writes 5 × 40 bytes (each felem padded with 8 zero bytes)
//!       into the 200-byte output slot.  Spec `pack_xyzt5_spec` +
//!       `strong_callee_post_pack_xyzt5` in `RistrettoBridges.v`.
//!
//! - **Scaffold shims** for the not-yet-decomposed algorithmic leaves
//!   (`ristretto_parse/pack_canonical/negate/sqrt_ratio`), which exist
//!   ONLY so the partial `decode.rs` links.  They compute nothing and
//!   are deleted as tasks T3/T4/T6 decompose them into field ops.

#![allow(dead_code, unused_variables)]

// ----------------------------------------------------------------
// pack_xyzt5: 5-felem packer (memmove-class)
// ----------------------------------------------------------------

/// Write the concatenation of 5 felems (32 bytes each, LE) as a
/// 200-byte buffer, padding each to 40 bytes with 8 trailing zero
/// bytes.  Matches `XyztAddVerified.pack_xyzt5` exactly:
///
/// ```text
/// out[0..40]    := x  ‖ [0u8; 8]
/// out[40..80]   := y  ‖ [0u8; 8]
/// out[80..120]  := z  ‖ [0u8; 8]
/// out[120..160] := ta ‖ [0u8; 8]
/// out[160..200] := tb ‖ [0u8; 8]
/// ```
///
/// # Safety
/// All input pointers must point to 32 readable bytes.  `out` must
/// point to 200 writable bytes.  Aliasing between any input and `out`
/// is undefined behaviour.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pack_xyzt5(
    out: *mut u8,
    x: *const u8,
    y: *const u8,
    z: *const u8,
    ta: *const u8,
    tb: *const u8,
) {
    let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(out, 200) };
    let src_x: &[u8] = unsafe { core::slice::from_raw_parts(x, 32) };
    let src_y: &[u8] = unsafe { core::slice::from_raw_parts(y, 32) };
    let src_z: &[u8] = unsafe { core::slice::from_raw_parts(z, 32) };
    let src_ta: &[u8] = unsafe { core::slice::from_raw_parts(ta, 32) };
    let src_tb: &[u8] = unsafe { core::slice::from_raw_parts(tb, 32) };
    // Zero the whole buffer first so the high-8 of each 40-byte slot
    // is guaranteed zero.
    for byte in dst.iter_mut() {
        *byte = 0;
    }
    dst[0..32].copy_from_slice(src_x);
    dst[40..72].copy_from_slice(src_y);
    dst[80..112].copy_from_slice(src_z);
    dst[120..152].copy_from_slice(src_ta);
    dst[160..192].copy_from_slice(src_tb);
}

// ----------------------------------------------------------------
// Shim leaves consumed by the extracted decode.rs (Phase B.5c MVP).
//
// `fe25519_sq` is an alias for the existing `fe25519_sqr` byte-pointer
// ABI (the Coq side uses the shorter name).
//
// The ristretto_* shims are SCAFFOLDS — they zero their outputs.  The
// AST emitted today is a partial decoder (not a §A.2-correct decoder),
// so KAT tests would fail regardless of these shim contents.  The
// shims exist solely so the emitted `decode.rs` LINKS, validating the
// Rocq-→-Rust extraction pipeline end-to-end.  Replace with real
// implementations (e.g. from a future hand-port of `RistrettoHelpers.v`
// to Rust, or via additional `REdCall` decomposition of the algorithm
// into existing fe25519 leaves) before claiming correctness.
// ----------------------------------------------------------------

// ----------------------------------------------------------------
// Field-element helpers over canonical 32-byte LE reps.
//
// These call the fe25519 byte-ABI ops (canonical output via fiat
// to_bytes), so a `[u8;32]` is always the canonical representative and
// byte-equality is field-equality.  This is the INTERIM real
// implementation of the two algorithmic decoder leaves
// (`ristretto_parse_canonical_felem`, `ristretto_sqrt_ratio_m1`),
// faithful to the verified Gallina specs in `RistrettoHelpers.v`.  The
// `pow22523` chain is the ref10 / T5-verified addition chain for
// `(p-5)/8 = 2^252-3`.  Trust class: matches a verified spec; slated
// for replacement by verified extraction (T6-AST/T4).
// ----------------------------------------------------------------

unsafe extern "C" {
    fn fe25519_mul(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_sub(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_sqr(out: *mut u8, a: *const u8);
}

// Felems are 40-BYTE buffers: the fe25519 byte-ABI (read_tight_ptr /
// write_tight_ptr in fe25519_portable.rs) reads/writes 40 bytes per
// felem (the Ed25519 xyzt convention = 32 value bytes + 8 zero pad).
// Using 32-byte buffers here would make every fe25519_* call overrun
// by 8 bytes and corrupt adjacent stack — see the B.5c migration note.
type Fe = [u8; 40];

/// 40-byte LE encoding of p = 2^255 - 19 (32 value + 8 zero pad).
const FE25519_P_LE: Fe = [
    0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
    0, 0, 0, 0, 0, 0, 0, 0,
];

/// 40-byte LE encoding of SQRT_M1 = 2^((p-1)/4) mod p.
const FE25519_SQRT_M1_LE: Fe = [
    0xb0, 0xa0, 0x0e, 0x4a, 0x27, 0x1b, 0xee, 0xc4,
    0x78, 0xe4, 0x2f, 0xad, 0x06, 0x18, 0x43, 0x2f,
    0xa7, 0xd7, 0xfb, 0x3d, 0x99, 0x00, 0x4d, 0x2b,
    0x0b, 0xdf, 0xc1, 0x4f, 0x80, 0x24, 0x83, 0x2b,
    0, 0, 0, 0, 0, 0, 0, 0,
];

/// Read a 40-byte felem from a raw pointer.
#[inline]
unsafe fn fe_read(p: *const u8) -> Fe {
    let s: &[u8] = unsafe { core::slice::from_raw_parts(p, 40) };
    let mut r = [0u8; 40]; r.copy_from_slice(s); r
}

#[inline]
fn fe_mul(a: &Fe, b: &Fe) -> Fe {
    let mut r = [0u8; 40];
    unsafe { fe25519_mul(r.as_mut_ptr(), a.as_ptr(), b.as_ptr()) };
    r
}
#[inline]
fn fe_sqr(a: &Fe) -> Fe {
    let mut r = [0u8; 40];
    unsafe { fe25519_sqr(r.as_mut_ptr(), a.as_ptr()) };
    r
}
/// (p - a) mod p = canonical_negate.  fe25519_sub(P, a) computes
/// (P - a) mod p, and P ≡ 0 (mod p), so the result is (-a) mod p.
#[inline]
fn fe_neg(a: &Fe) -> Fe {
    let mut r = [0u8; 40];
    unsafe { fe25519_sub(r.as_mut_ptr(), FE25519_P_LE.as_ptr(), a.as_ptr()) };
    r
}
#[inline]
fn fe_is_negative(a: &Fe) -> bool {
    (a[0] & 1) == 1
}

/// `a^((p-5)/8) = a^(2^252-3) mod p`, via the ref10 / T5-verified
/// addition chain (250 squarings + 11 multiplications).
fn fe_pow22523(z: &Fe) -> Fe {
    let mut t0 = fe_sqr(z);                       // z^2
    let mut t1 = fe_sqr(&fe_sqr(&t0));            // z^8
    t1 = fe_mul(z, &t1);                          // z^9
    t0 = fe_mul(&t0, &t1);                        // z^11
    t0 = fe_sqr(&t0);                             // z^22
    t0 = fe_mul(&t1, &t0);                        // z^(2^5 - 1)
    t1 = fe_sqr(&t0);
    for _ in 0..4 { t1 = fe_sqr(&t1); }
    t0 = fe_mul(&t1, &t0);                        // z^(2^10 - 1)
    t1 = fe_sqr(&t0);
    for _ in 0..9 { t1 = fe_sqr(&t1); }
    t1 = fe_mul(&t1, &t0);                        // z^(2^20 - 1)
    let mut t2 = fe_sqr(&t1);
    for _ in 0..19 { t2 = fe_sqr(&t2); }
    t1 = fe_mul(&t2, &t1);                        // z^(2^40 - 1)
    for _ in 0..10 { t1 = fe_sqr(&t1); }
    t0 = fe_mul(&t1, &t0);                        // z^(2^50 - 1)
    t1 = fe_sqr(&t0);
    for _ in 0..49 { t1 = fe_sqr(&t1); }
    t1 = fe_mul(&t1, &t0);                        // z^(2^100 - 1)
    t2 = fe_sqr(&t1);
    for _ in 0..99 { t2 = fe_sqr(&t2); }
    t1 = fe_mul(&t2, &t1);                        // z^(2^200 - 1)
    for _ in 0..50 { t1 = fe_sqr(&t1); }
    t0 = fe_mul(&t1, &t0);                        // z^(2^250 - 1)
    t0 = fe_sqr(&fe_sqr(&t0));                    // z^(2^252 - 4)
    fe_mul(z, &t0)                                // z^(2^252 - 3)
}

/// Whole-felem byte equality (both args are canonical reps, so the
/// 8-byte pad is zero on both — byte equality is field equality).
#[inline]
fn fe_eq(a: &Fe, b: &Fe) -> bool { a == b }

/// Field inversion `a^(p-2) mod p`, reusing the verified `fe_pow22523`
/// chain.  Since `p-2 = 2^255-21 = 8·(2^252-3) + 3`,
///   inv(a) = (a^(2^252-3))^8 · a^3 = pow22523(a)^8 · a^3.
fn fe_inv(a: &Fe) -> Fe {
    let p58 = fe_pow22523(a);                 // a^(2^252 - 3)
    let p8 = fe_sqr(&fe_sqr(&fe_sqr(&p58)));  // ^8 = a^(2^255 - 24)
    let a3 = fe_mul(&fe_sqr(a), a);           // a^3
    fe_mul(&p8, &a3)                          // a^(2^255 - 21) = a^(p-2)
}

/// `fe25519_inv(out, a) = a^(p-2) mod p` (multiplicative inverse).
/// Used by the extracted encoder's `extended_T = ta·tb/z`.  40-byte ABI.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_inv(out: *mut u8, a: *const u8) {
    let r = fe_inv(&unsafe { fe_read(a) });
    let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(out, 40) };
    dst.copy_from_slice(&r);
}

/// `z >= p` for a 32-byte value already known to satisfy `z < 2^255`
/// (bit 255 clear).  Little-endian magnitude compare against p.
fn fe_ge_p_32(bs: &[u8; 32]) -> bool {
    let mut i = 31usize;
    loop {
        if bs[i] > FE25519_P_LE[i] { return true; }
        if bs[i] < FE25519_P_LE[i] { return false; }
        if i == 0 { return true; } // all equal => z == p => >= p
        i -= 1;
    }
}

/// fe25519_sq alias for the extracted decoder (Coq side uses the
/// shorter name).  Forwards to the canonical 40-byte `fe25519_sqr`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_sq(out: *mut u8, a: *const u8) {
    unsafe { fe25519_sqr(out, a) }
}

/// RFC 9496 §3.2.1 parse: reject if bit 255 set, if z >= p
/// (non-canonical), or if z is "negative" (bit 0 set).  Input `bs_in`
/// is the 32-byte ristretto encoding; output `s_out` is a 40-byte
/// felem slot (32 value + 8 zero pad).  Faithful to
/// `ristretto_parse_canonical_felem` in RistrettoHelpers.v.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ristretto_parse_canonical_felem(
    s_out: *mut u8,
    status_out: *mut u8,
    bs_in: *const u8,
) {
    let bs: &[u8] = unsafe { core::slice::from_raw_parts(bs_in, 32) };
    let mut z = [0u8; 32];
    z.copy_from_slice(bs);
    let s: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(s_out, 40) };
    let reject = ((z[31] & 0x80) != 0)        // bit 255
        || fe_ge_p_32(&z)                      // non-canonical
        || ((z[0] & 1) != 0);                  // is_negative
    for byte in s.iter_mut() { *byte = 0; }
    if reject {
        unsafe { *status_out = 1; }
    } else {
        s[0..32].copy_from_slice(&z);          // low 32 = value, high 8 = 0
        unsafe { *status_out = 0; }
    }
}

/// RFC 9496 §3.1.3 sqrt_ratio_m1.  All felems are 40-byte.  Writes
/// ws_out = 1 iff a genuine square root of u/v exists, and r_out = the
/// canonical (is_negative = false) root.  Faithful to
/// `ristretto_sqrt_ratio_m1` in RistrettoHelpers.v.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ristretto_sqrt_ratio_m1(
    ws_out: *mut u8,
    r_out: *mut u8,
    u_in: *const u8,
    v_in: *const u8,
) {
    let ub = unsafe { fe_read(u_in) };
    let vb = unsafe { fe_read(v_in) };
    let sqrt_m1 = FE25519_SQRT_M1_LE;

    let v3 = fe_mul(&fe_sqr(&vb), &vb);          // v^3
    let v7 = fe_mul(&fe_sqr(&v3), &vb);          // v^7
    let uv7 = fe_mul(&ub, &v7);
    let pow_val = fe_pow22523(&uv7);
    let r0 = fe_mul(&fe_mul(&ub, &v3), &pow_val);
    let check = fe_mul(&fe_mul(&vb, &r0), &r0);  // v * r0^2

    let neg_u = fe_neg(&ub);
    let neg_iu = fe_neg(&fe_mul(&sqrt_m1, &ub));
    let correct_sign = fe_eq(&check, &ub);
    let flipped_sign = fe_eq(&check, &neg_u);
    let flipped_sign_i = fe_eq(&check, &neg_iu);

    let r1 = if correct_sign {
        r0
    } else if flipped_sign || flipped_sign_i {
        fe_mul(&r0, &sqrt_m1)
    } else {
        r0
    };
    let r = if fe_is_negative(&r1) { fe_neg(&r1) } else { r1 };

    let was_square = correct_sign || flipped_sign;
    unsafe { *ws_out = if was_square { 1 } else { 0 }; }
    let rd: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(r_out, 40) };
    rd.copy_from_slice(&r);
}

// ----------------------------------------------------------------
// Self-tests
// ----------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn fe2() -> Fe { let mut a = [0u8; 40]; a[0] = 2; a }
    fn fe_one() -> Fe { let mut a = [0u8; 40]; a[0] = 1; a }
    fn pad40(v32: [u8; 32]) -> Fe { let mut a = [0u8; 40]; a[0..32].copy_from_slice(&v32); a }

    #[test]
    fn pow22523_of_2_matches_reference() {
        let got = fe_pow22523(&fe2());
        let want = pad40([79,80,7,165,147,13,119,98,60,242,151,86,3,140,161,151,
                          211,235,253,158,76,128,166,149,133,239,224,39,64,146,193,85]);
        assert_eq!(got, want, "pow22523(2) wrong");
    }

    #[test]
    fn inv_of_2_matches_reference() {
        let got = fe_inv(&fe2());
        let want = pad40([247,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,
                          255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,63]);
        assert_eq!(got, want, "inv(2) wrong");
        assert_eq!(fe_mul(&fe2(), &got), fe_one(), "2 * inv(2) != 1");
    }

    #[test]
    fn sqrt_ratio_nonsquare_was_false() {
        // 1/2 is a non-residue mod p (p ≡ 5 mod 8 ⇒ 2 is a non-QR),
        // so sqrt_ratio_m1(1, 2) must report was_square = 0.
        let one = fe_one();
        let two = fe2();
        let mut ws = [0u8; 1]; let mut r = [0u8; 40];
        unsafe { ristretto_sqrt_ratio_m1(ws.as_mut_ptr(), r.as_mut_ptr(),
                                         one.as_ptr(), two.as_ptr()); }
        assert_eq!(ws[0], 0, "sqrt_ratio(1,2): 1/2 is non-square, was_square must be 0");
    }

    #[test]
    fn sqrt_ratio_square_was_true() {
        // 1/4 is a square (=（1/2)^2); sqrt_ratio_m1(1, 4) must give was_square=1.
        let one = fe_one();
        let mut four = [0u8; 40]; four[0] = 4;
        let mut ws = [0u8; 1]; let mut r = [0u8; 40];
        unsafe { ristretto_sqrt_ratio_m1(ws.as_mut_ptr(), r.as_mut_ptr(),
                                         one.as_ptr(), four.as_ptr()); }
        assert_eq!(ws[0], 1, "sqrt_ratio(1,4): 1/4 is square, was_square must be 1");
        // r^2 * 4 == 1  (v * r^2 == u)
        assert_eq!(fe_mul(&four, &fe_sqr(&r)), one, "v*r^2 should == u");
    }

    #[test]
    fn sqrt_ratio_one_one() {
        let one = fe_one();
        let mut ws = [0u8; 1]; let mut r = [0u8; 40];
        unsafe { ristretto_sqrt_ratio_m1(ws.as_mut_ptr(), r.as_mut_ptr(),
                                         one.as_ptr(), one.as_ptr()); }
        assert_eq!(ws[0], 1, "sqrt_ratio(1,1) was_square should be 1");
        // r is the CANONICAL (even-LSB / is_negative=false) root of 1.
        // is_negative(1)=true, so the canonical root is -1 = p-1.
        let mut neg_one = FE25519_P_LE; neg_one[0] -= 1; // p-1
        assert_eq!(r, neg_one, "sqrt_ratio(1,1) r should be p-1 (canonical)");
        assert_eq!(fe_sqr(&r), one, "r^2 should be 1");
    }

    #[test]
    fn pack_xyzt5_lays_out_with_padding() {
        let x = [0x11u8; 32];
        let y = [0x22u8; 32];
        let z = [0x33u8; 32];
        let ta = [0x44u8; 32];
        let tb = [0x55u8; 32];
        let mut out = [0xFFu8; 200];
        unsafe {
            pack_xyzt5(
                out.as_mut_ptr(),
                x.as_ptr(), y.as_ptr(), z.as_ptr(),
                ta.as_ptr(), tb.as_ptr(),
            );
        }
        // Each 40-byte slot: first 32 bytes are the felem, last 8 are zero.
        for i in 0..32 { assert_eq!(out[i], 0x11); }
        for i in 32..40 { assert_eq!(out[i], 0); }
        for i in 40..72 { assert_eq!(out[i], 0x22); }
        for i in 72..80 { assert_eq!(out[i], 0); }
        for i in 80..112 { assert_eq!(out[i], 0x33); }
        for i in 112..120 { assert_eq!(out[i], 0); }
        for i in 120..152 { assert_eq!(out[i], 0x44); }
        for i in 152..160 { assert_eq!(out[i], 0); }
        for i in 160..192 { assert_eq!(out[i], 0x55); }
        for i in 192..200 { assert_eq!(out[i], 0); }
    }
}
