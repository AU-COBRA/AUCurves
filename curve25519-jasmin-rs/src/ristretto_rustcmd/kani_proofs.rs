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
//! STATUS (2026-05-23 feasibility run): Kani builds this crate fine
//! (the `jasminc` build script and `blst` C dep are OK), and it DOES
//! check the panic class we care about — it surfaced
//! `core::slice::copy_from_slice_impl::len_mismatch_fail::do_panic`
//! (exactly the `REdSetBytes` bug).  BUT the emitted `decode.rs`/
//! `encode.rs` call the field/leaf primitives via `extern "C"` FFI
//! (`fe25519_mul/add/sq`, `ristretto_sqrt_ratio_m1`,
//! `ristretto_parse_canonical_felem`, `pack_xyzt5`, `fe25519_inv`,
//! `unpack_xyzt5`), and Kani does NOT support calls to foreign "C"
//! functions (`unsupported_construct`, kani#2423).  So verification
//! cannot complete as-is.
//!
//! NEXT STEP to get a green proof: add `#[kani::stub(<extern_fn>,
//! <rust_shim>)]` for each of the ~6 leaves, where the shim is an
//! ABSTRACT model (returns `kani::any()` 40-byte felem / arbitrary
//! status byte) rather than the real field arithmetic.  This verifies
//! the memory-safety + panic-freedom of the decode/encode GLUE (the
//! slot byte-shuffling, the dispatch, the `copy_from_slice` lengths,
//! the `REdFor`/`REdSelect` index arithmetic) — which is where the
//! 32/40 overrun and the copy_from_slice panic lived — WITHOUT the
//! intractable symbolic field arithmetic.  Full functional
//! `decode == dalek` stays with the Coq simulation + the dalek
//! differential test.  The `unwind(101)` covers the pow-chain's
//! bounded loops once the leaves are stubbed away.

#![cfg(kani)]

use super::{ristretto_decode, ristretto_encode};

/// Decoding ANY 32-byte input is memory-safe and panic-free.
#[kani::proof]
#[kani::unwind(101)]
fn decode_no_ub_or_panic() {
    let bs: [u8; 32] = kani::any();
    let _ = ristretto_decode(&bs);
}

/// Encoding ANY 200-byte xyzt buffer is memory-safe and panic-free.
#[kani::proof]
#[kani::unwind(101)]
fn encode_no_ub_or_panic() {
    let xyzt: [u8; 200] = kani::any();
    let _ = ristretto_encode(&xyzt);
}

/// Decode-then-encode is panic-free and the encode of any decoded
/// point is a well-formed 32-byte array (length is structural, but the
/// harness also exercises the full decode→encode pipeline for UB).
#[kani::proof]
#[kani::unwind(101)]
fn decode_then_encode_no_ub() {
    let bs: [u8; 32] = kani::any();
    if let Some(xyzt) = ristretto_decode(&bs) {
        let _out: [u8; 32] = ristretto_encode(&xyzt);
    }
}
