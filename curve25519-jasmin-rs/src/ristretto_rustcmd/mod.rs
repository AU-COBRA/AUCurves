//! Ristretto255 encode / decode, **Rust-direct** path from `rust_cmd_ed`.
//!
//! Mirrors `src/ed25519_rustcmd/mod.rs`.  Sibling files `decode.rs`
//! and `encode.rs` are AUTO-GENERATED from the verified `rust_cmd_ed`
//! AST in `AUCurves/src/Bedrock/End2End/Ristretto/Ristretto_RustCmd.v`
//! by the `RustCmdToRust.rs_func_emit` emitter.  Regenerate via:
//!
//! ```bash
//! cd AUCurves
//! rocq compile <usual flags> src/Bedrock/ExtractRistrettoCmdRs.v
//! ```
//!
//! followed by the strip script in the crate's repo notes.
//!
//! ## Status (2026-05-22)
//!
//! This directory is **SCAFFOLD**: the emitted `decode.rs` /
//! `encode.rs` files do not yet exist because the Rocq `Derive` block
//! in `Ristretto_RustCmd.v` is pending its Tier-4 sugar lemma
//! discharge (see `RustCmdRupicolaRistretto.v`).  This `mod.rs`
//! declares the public surface so that downstream callers
//! (`tests/ristretto_rfc9496_kat.rs`, `src/zkgroup_demo.rs`) can be
//! written and reviewed against the final shape.
//!
//! Until the emitted files land, every public function in this module
//! is a stub returning [`STUB_ERROR`] (a 200-byte buffer of 0xFF, NOT
//! the production "bad_point" of 0x00 — chosen to make accidental
//! reliance on stubs detectable in tests).
//!
//! ## Verification chain (when complete)
//!
//! ```text
//! ristretto_decode_rs : rust_cmd_ed
//!     ↓ safe_cmd_correct_ed       (Qed in SafeRustEd25519Sim.v —
//!                                  shared with Ed25519 path)
//! bedrock_exec_ed callee_post (translate ristretto_decode_rs)
//!     ↓ to_bedrock_cmd_semantic_correct  (Qed in RustCmdToC.v)
//! bedrock2 fnspec composition w/ ristretto bridges
//!     ↓ rs_func_emit (RustCmdToRust.rs_func_emit)
//! src/ristretto_rustcmd/decode.rs (when this module is regenerated)
//! ```
//!
//! And the corresponding chain for `encode`.
//!
//! ## Public surface (final, after extraction)
//!
//! - `ristretto_decode(bytes: &[u8; 32]) -> Option<[u8; 200]>`
//!     - returns the canonical 200-byte xyzt encoding of the decoded
//!       point on success, `None` on any rejection (non-canonical
//!       field encoding, sign-bit set, non-square `u² · v`,
//!       negative `t`, or `y = 0`).
//!     - Matches RFC 9496 §4.3.1 EXACTLY (cross-checked against the
//!       24 §A.2 rejection vectors in
//!       `tests/ristretto_rfc9496_kat.rs`).
//!
//! - `ristretto_encode(xyzt: &[u8; 200]) -> [u8; 32]`
//!     - returns the canonical 32-byte LE compression.
//!     - Matches RFC 9496 §4.3.2 EXACTLY (cross-checked against the
//!       §A.1 basepoint and the 16 multiples-of-basepoint vectors).
//!
//! ## Leaf dependencies
//!
//! The extracted `decode.rs` and `encode.rs` will call these leaf
//! FFI symbols (declared in `leaves.rs`, definitions in the existing
//! curve25519-jasmin static lib + a small ristretto-specific glue
//! module):
//!
//! - `fe25519_add`, `fe25519_sub`, `fe25519_mul`, `fe25519_sq`  —
//!   shared with the Ed25519 path; from `c/fe25519_*.c` or the
//!   Jasmin extraction.
//! - `fe25519_pow_pm5d8` — sqrt-ratio's `s^((p-5)/8)`.  New leaf:
//!   bedrock2 source pending in
//!   `src/Bedrock/End2End/Lizard/Fe25519PowPM5d8.v` (to be added).
//! - `ristretto_sqrt_ratio_m1(out_ws: *mut u8, out_r: *mut u8,
//!                            u: *const u8, v: *const u8)` — high-
//!   level leaf wrapping the §3.1.3 algorithm.  Composed from the
//!   above field ops; not yet emitted.
//! - `ristretto_is_negative`, `ristretto_abs`, `ristretto_negate` —
//!   pure-bit / pure-Z helpers, direct Rust impl in `helpers.rs`.
//! - `ristretto_parse_canonical_felem`, `ristretto_pack_canonical_felem`
//!   — LE byte-array ↔ field-element bridges, direct Rust impl
//!   in `helpers.rs`.

#![allow(dead_code, unused_variables)]

// Constant setters + pack_xyzt5 (B.5b path b — sub-blocker #2/#3 fixes).
// Always compiled because the extracted decode.rs / encode.rs will
// reference these by C-ABI symbol name once the AST lands.
pub mod leaves;

/// 32-byte canonical ristretto255 encoding.
pub type RistrettoPoint32 = [u8; 32];

/// 200-byte extended-twisted-Edwards xyzt slot (matches the Ed25519
/// `rust_cmd_ed` xyzt convention: 40 bytes per coordinate, 5
/// coordinates = `x, y, z, ta, tb`).
pub type RistrettoXyzt200 = [u8; 200];

/// Stub-output sentinel for the scaffold phase.  When the emitted
/// decode/encode land, this constant is removed.
#[allow(dead_code)]
const STUB_OUTPUT: RistrettoXyzt200 = [0xFFu8; 200];

/// Bad-point sentinel.  RFC 9496 §4.3.1's rejection branch is
/// modeled in the Rocq Z-mirror as a 200-byte buffer of 0x00.  The
/// Rust API surfaces this as `None`, so the constant is only used
/// internally by the extracted decode.rs.
#[allow(dead_code)]
const BAD_POINT: RistrettoXyzt200 = [0x00u8; 200];

// ----------------------------------------------------------------
// PUBLIC SURFACE (stubs until extraction lands)
// ----------------------------------------------------------------

/// Decode a 32-byte canonical ristretto encoding.
///
/// Returns `Some(xyzt)` on success, `None` on any RFC 9496 §4.3.1
/// rejection branch.
///
/// **SCAFFOLD STUB** — always returns `None` until the emitted
/// `decode.rs` lands.  Tests that depend on positive results will
/// fail with a clear message.
pub fn ristretto_decode(_bytes: &RistrettoPoint32) -> Option<RistrettoXyzt200> {
    // TODO(B.5b): replace this body with a call to the emitted
    // `decode::ristretto_decode` once `Ristretto_RustCmd.v` lands.
    None
}

/// Encode a 200-byte extended-twisted-Edwards xyzt to a 32-byte
/// canonical ristretto encoding.
///
/// **SCAFFOLD STUB** — always returns 32 bytes of `0xFF` until the
/// emitted `encode.rs` lands.  Distinct from the legitimate
/// all-zero encoding (the ristretto identity) and from any RFC test
/// vector, so tests can detect reliance on the stub.
pub fn ristretto_encode(_xyzt: &RistrettoXyzt200) -> RistrettoPoint32 {
    // TODO(B.5b): replace this body with a call to the emitted
    // `encode::ristretto_encode` once `Ristretto_RustCmd.v` lands.
    [0xFFu8; 32]
}

// ----------------------------------------------------------------
// LIVE MODULE STRUCTURE (pending extraction)
//
// When the extracted files land, this section will look like:
//
//     mod decode;     // AUTO-GENERATED
//     mod encode;     // AUTO-GENERATED
//     mod helpers;    // hand-written Rust glue
//     mod leaves;     // FFI declarations + thin wrappers
//
// and the public `ristretto_decode` / `ristretto_encode` above are
// replaced by re-exports:
//
//     pub use decode::ristretto_decode;
//     pub use encode::ristretto_encode;
//
// Today: stubs only.  The structural test suite in
// `tests/ristretto_rfc9496_kat.rs` is correct for both layouts.
// ----------------------------------------------------------------
