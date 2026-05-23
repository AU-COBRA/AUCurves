//! Kani proof harnesses for the extracted Ristretto255 decode/encode.
//!
//! PRIMARY value: Kani statically checks for undefined behaviour
//! (out-of-bounds reads/writes, pointer misuse) and panics over ALL
//! symbolic inputs.  It would have caught both runtime bugs from the
//! B.5c bring-up automatically:
//!   - the 32-vs-40-byte felem buffer overrun (an OOB write in the
//!     fe25519 byte-ABI when felem slots were 32 bytes);
//!   - the `copy_from_slice` length-mismatch panic in `REdSetBytes`.
//!
//! SCOPE: these harnesses verify memory-safety / panic-freedom, NOT
//! full functional equivalence to dalek.  Full `decode == dalek` over
//! all 2^256 inputs is out of reach for the SMT backend (the fiat
//! radix-2^51 field ops + the ~270-op `pow22523` chain), and that
//! all-input equivalence is what the Coq simulation theorems are for.
//! Differential testing against dalek (see
//! `tests/ristretto_rfc9496_kat.rs::differential_vs_dalek_random_and_valid`)
//! covers random sampling; Kani covers the UB/panic class exhaustively.
//!
//! Run with: `cargo kani --features 'ristretto_rustcmd decomposed_leaves'`.
//!
//! MECHANISM (2026-05-23): the emitted `decode.rs`/`encode.rs` reach
//! the field / Ristretto leaves through `unsafe extern "C" { fn ... }`
//! declarations.  Kani treats an un-stubbed `extern` declaration as an
//! opaque foreign function (`unsupported_construct`, kani#2423), AND
//! the real bodies run the intractable ~270-op `pow22523` chain.  Both
//! are resolved by `#[kani::stub(target, replacement)]`: each harness
//! maps the leaf's `extern`-declaration path (e.g.
//! `super::decode::fe25519_mul`) to an ABSTRACT model in
//! `super::kani_stubs` that writes `kani::any()`-filled buffers of the
//! exact declared length (40 for felems, 32 for the canonical pack
//! output, 1 for status / was-square, 200 for the packed xyzt).  Kani
//! substitutes the model at every call site within the harness, so it
//! reasons about the decode/encode GLUE — the slot byte-shuffling, the
//! leaf-call dispatch, the `copy_from_slice` lengths, the `REdFor` /
//! `REdSelect` index arithmetic — which is exactly where the 32/40
//! buffer overrun and the `copy_from_slice` length-mismatch panic
//! lived.  Symbolic `status` / `ws` bytes from the parse / sqrt-ratio
//! stubs force BOTH the accept and reject decode branches.  Full
//! functional `decode == dalek` stays with the Coq simulation + the
//! dalek differential test.  The `unwind(256)` covers every bounded
//! loop once the leaves are stubbed: the `REdFor` 40-byte felem masks,
//! the abstract stubs' ≤200-byte fills, and the 200-byte
//! `out == BAD_POINT` memcmp in the public `ristretto_decode` wrapper
//! (each needs `len + 1` unwinds; 256 > 201).
//!
//! Stubs are referenced by their `extern`-declaration path because
//! Kani's stub targeting uses Rust name resolution; using
//! `#[kani::stub]` (rather than `#[cfg(kani)] #[no_mangle]` abstract
//! definitions) means we never touch `fe25519_portable.rs` and incur
//! no duplicate-symbol clash with the real leaves.

#![cfg(kani)]

use super::kani_stubs;
use super::{ristretto_decode, ristretto_encode};

/// Decoding ANY 32-byte input is memory-safe and panic-free.
#[kani::proof]
#[kani::unwind(256)]
#[kani::stub(super::decode::fe25519_mul, kani_stubs::fe25519_mul_stub)]
#[kani::stub(super::decode::fe25519_add, kani_stubs::fe25519_add_stub)]
#[kani::stub(super::decode::fe25519_sub, kani_stubs::fe25519_sub_stub)]
#[kani::stub(super::decode::fe25519_sq, kani_stubs::fe25519_sq_stub)]
#[kani::stub(
    super::decode::ristretto_parse_canonical_felem,
    kani_stubs::ristretto_parse_canonical_felem_stub
)]
#[kani::stub(
    super::decode::ristretto_sqrt_ratio_m1,
    kani_stubs::ristretto_sqrt_ratio_m1_stub
)]
#[kani::stub(super::decode::pack_xyzt5, kani_stubs::pack_xyzt5_stub)]
fn decode_no_ub_or_panic() {
    let bs: [u8; 32] = kani::any();
    let _ = ristretto_decode(&bs);
}

/// Encoding ANY 200-byte xyzt buffer is memory-safe and panic-free.
#[kani::proof]
#[kani::unwind(256)]
#[kani::stub(super::encode::fe25519_mul, kani_stubs::fe25519_mul_stub)]
#[kani::stub(super::encode::fe25519_add, kani_stubs::fe25519_add_stub)]
#[kani::stub(super::encode::fe25519_sub, kani_stubs::fe25519_sub_stub)]
#[kani::stub(super::encode::fe25519_sq, kani_stubs::fe25519_sq_stub)]
#[kani::stub(super::encode::fe25519_inv, kani_stubs::fe25519_inv_stub)]
#[kani::stub(
    super::encode::ristretto_sqrt_ratio_m1,
    kani_stubs::ristretto_sqrt_ratio_m1_stub
)]
#[kani::stub(
    super::encode::ristretto_pack_canonical_felem,
    kani_stubs::ristretto_pack_canonical_felem_stub
)]
#[kani::stub(super::encode::unpack_xyzt5, kani_stubs::unpack_xyzt5_stub)]
fn encode_no_ub_or_panic() {
    let xyzt: [u8; 200] = kani::any();
    let _ = ristretto_encode(&xyzt);
}

/// Decode-then-encode is panic-free and the encode of any decoded
/// point is a well-formed 32-byte array (length is structural, but the
/// harness also exercises the full decode→encode pipeline for UB).
#[kani::proof]
#[kani::unwind(256)]
#[kani::stub(super::decode::fe25519_mul, kani_stubs::fe25519_mul_stub)]
#[kani::stub(super::decode::fe25519_add, kani_stubs::fe25519_add_stub)]
#[kani::stub(super::decode::fe25519_sub, kani_stubs::fe25519_sub_stub)]
#[kani::stub(super::decode::fe25519_sq, kani_stubs::fe25519_sq_stub)]
#[kani::stub(
    super::decode::ristretto_parse_canonical_felem,
    kani_stubs::ristretto_parse_canonical_felem_stub
)]
#[kani::stub(
    super::decode::ristretto_sqrt_ratio_m1,
    kani_stubs::ristretto_sqrt_ratio_m1_stub
)]
#[kani::stub(super::decode::pack_xyzt5, kani_stubs::pack_xyzt5_stub)]
#[kani::stub(super::encode::fe25519_mul, kani_stubs::fe25519_mul_stub)]
#[kani::stub(super::encode::fe25519_add, kani_stubs::fe25519_add_stub)]
#[kani::stub(super::encode::fe25519_sub, kani_stubs::fe25519_sub_stub)]
#[kani::stub(super::encode::fe25519_sq, kani_stubs::fe25519_sq_stub)]
#[kani::stub(super::encode::fe25519_inv, kani_stubs::fe25519_inv_stub)]
#[kani::stub(
    super::encode::ristretto_sqrt_ratio_m1,
    kani_stubs::ristretto_sqrt_ratio_m1_stub
)]
#[kani::stub(
    super::encode::ristretto_pack_canonical_felem,
    kani_stubs::ristretto_pack_canonical_felem_stub
)]
#[kani::stub(super::encode::unpack_xyzt5, kani_stubs::unpack_xyzt5_stub)]
fn decode_then_encode_no_ub() {
    let bs: [u8; 32] = kani::any();
    if let Some(xyzt) = ristretto_decode(&bs) {
        let _out: [u8; 32] = ristretto_encode(&xyzt);
    }
}
