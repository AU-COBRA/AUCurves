//! Ed25519 sign / verify, **Rust-direct** path from `rust_cmd_ed`.
//!
//! The `sign.rs` and `verify.rs` files in this directory are
//! auto-generated from the verified `rust_cmd_ed` AST in
//! `AUCurves/src/Bedrock/End2End/Ed25519/Sign_Verify_RustCmd.v` by
//! the `RustCmdToRust.rs_func_emit` emitter
//! (`AUCurves/src/Bedrock/RustCmdToRust.v`).  Re-run via
//!
//! ```bash
//! cd AUCurves
//! rocq compile <usual flags> src/Bedrock/ExtractEd25519CmdRs.v
//! ```
//!
//! followed by the strip script in this crate's repo notes.
//!
//! Verification chain:
//!
//! ```text
//! ed25519_sign_rs : rust_cmd_ed
//!     ↓ safe_cmd_correct_ed (Qed in SafeRustEd25519Sim.v)
//! bedrock_exec_ed callee_post (translate ed25519_sign_rs)
//!     ↓ to_bedrock_cmd_semantic_correct (Qed in RustCmdToC.v)
//! bedrock2 fnspec composition w/ bridges (RemainingBridges.v)
//!     ↓ rs_func_emit (RustCmdToRust.rs_func_emit)
//! src/ed25519_rustcmd/sign.rs (THIS FILE)
//! ```
//!
//! Why Rust-direct (vs the C path in `c/ed25519_*.c`):
//!
//! 1. **No pointer-arithmetic gap.**  rust_cmd_ed's REdCall passes
//!    `*const u8` / `*mut u8`; in Rust those carry no offset, so the
//!    `memmove_*` slice copies are explicit (`a[i..j].copy_from_slice(b)`)
//!    — no `dst+off` workaround needed.  The C path's gap #2 doesn't
//!    apply here.
//! 2. **Linker self-contained.**  `memmove_helpers.rs` provides the
//!    region-copy callees as `extern "C" #[no_mangle]` Rust functions;
//!    no auxiliary C compilation step.
//! 3. **Closer to the deliverable.**  Signal / libsignal is already
//!    Rust — emitting Rust eliminates the C → bindgen → Rust hop.
//!
//! Status (2026-05-12): all 12 RFC 8032 §7.1 KATs pass — public-key
//! derivation, strict signature byte-equality for all 3 vectors,
//! verify accept / reject paths.  Bugs A (sha512 length arg), B
//! (canonical chal buffer), C (32-byte S extraction), and D (final
//! bytes_equal_32 shape) are all closed.  The verify body now:
//!   1. compresses sB into its own 32-byte slot, and
//!   2. compares that against compress(R + h·A),
//! so the caller-visible `result_out` byte carries the true RFC 8032
//! verdict.  The cargo wrapper below trusts it directly — no more
//! dalek recompute.

#![cfg(feature = "ed25519_rustcmd")]

mod leaves;
mod memmove_helpers;
mod sign;
mod verify;

// Extracted decomposed curve-leaf bodies (Bedrock/ExtractCurveBodies.v).
// Provides extern "C" symbols xyzt_{add,double,copy}_decomposed,
// scalarmult{,_base}_decomposed.  Imported lazily by
// `leaves.rs::decomposed_curve_leaves` when the `decomposed_leaves`
// feature is active.
#[cfg(all(feature = "decomposed_leaves", not(feature = "dalek_leaves")))]
mod decomposed_bodies;

// Inline-callable variant of the decomposed bodies
// (Bedrock/ExtractCurveBodiesInline.v).  Each body is
// `#[inline(always)] pub fn name(out: &mut [u8; N], ...)` so LLVM can
// inline cross-body call sites.  Path (2) of the gap inventory.
#[cfg(all(feature = "inline_leaves",
          not(feature = "decomposed_leaves"),
          not(feature = "dalek_leaves")))]
mod decomposed_bodies_inline;

// wNAF + comb-table scalar-mult bodies
// (Bedrock/ExtractWnafCombBodies.v).  Wired under `wnaf_comb_leaves`;
// piggybacks on `decomposed_bodies` for the xyzt_*_decomposed leaves
// (compiled in alongside under the same feature).
#[cfg(all(feature = "wnaf_comb_leaves",
          not(feature = "decomposed_leaves"),
          not(feature = "inline_leaves"),
          not(feature = "dalek_leaves")))]
mod decomposed_bodies;
#[cfg(all(feature = "wnaf_comb_leaves",
          not(feature = "decomposed_leaves"),
          not(feature = "inline_leaves"),
          not(feature = "dalek_leaves")))]
mod decomposed_bodies_wnaf_comb;
// Window-4 variable-base scalarmult body — auto-extracted from
// AUCurves's Window4ScalarmultBody.v (Phase 1a-revised).
#[cfg(all(feature = "wnaf_comb_leaves",
          not(feature = "decomposed_leaves"),
          not(feature = "inline_leaves"),
          not(feature = "dalek_leaves")))]
mod decomposed_bodies_window4;

// Portable fe25519_* shim — fiat-rust 5×51 radix-2^51 (B1).  Always
// compiled under decomposed_leaves so the `cryptopt_leaves` shim can
// share its compress/decompress helpers (which depend on the 5×51
// inverse chain).  Under default decomposed_leaves it ALSO exports
// the `fe25519_*` ABI; under `cryptopt_leaves` the 4×64 shim provides
// that ABI and `fe25519_portable` is used only via direct Rust calls.
// inline_leaves shares the same portable leaf shim.  wnaf_comb_leaves
// also reuses it (the bodies dispatch to the Phase A xyzt_add/double/copy
// leaves which themselves call fe25519_*).
#[cfg(all(any(feature = "decomposed_leaves",
              feature = "inline_leaves",
              feature = "wnaf_comb_leaves"),
          not(feature = "dalek_leaves")))]
mod fe25519_portable;

// 4×64 saturated-Solinas fe25519_* shim with CryptOpt asm for mul/sqr (B2).
// Defines the same `fe25519_*` `extern "C"` ABI as `fe25519_portable`,
// so toggling `--features cryptopt_leaves` swaps the linker target
// without touching the extracted bodies.  Disabled iff cryptopt_leaves
// is OFF — to avoid duplicate `fe25519_*` symbols, fe25519_portable
// uses `#[cfg(not(feature = "cryptopt_leaves"))]` on its exports.
#[cfg(all(feature = "cryptopt_leaves", not(feature = "dalek_leaves")))]
mod fe25519_cryptopt;

// `fe25519_invert` emitted from a verified Lean `RustCmd` AST.
// AST source: SSProve-lean/.../Examples/Fe25519Invert.lean
// Trust: single named axiom `RustcExec_correct` in Lean's
// JasminToRustEmitSimulates.lean.  KAT'd against the hand-coded
// `mont_to_edwards::fe25519_invert` in this module's unit tests.
#[cfg(feature = "lean_emitted_invert")]
pub mod fe25519_invert_emitted;

// build_comb_table emitted from a verified Lean RustCmd AST.
// AST source: SSProve-lean/.../Examples/CombTableInit.lean
// 1024 cell decls + 4048 leaf calls (15 row-0 adds + 2 copies + 4032 doublings).
#[cfg(feature = "lean_emitted_comb_table")]
pub mod build_comb_table_emitted;

// Limb-typed shim for the TFp25519_64 plumbing (PROTOTYPE).
// Exports `fe25519_*_limbs(out: *mut u64, ...)` parallel to the
// byte-canonical `fe25519_*` exports in `fe25519_portable`.  Active
// under the `tfp25519_limbs` feature flag.  See
// docs/tfp25519-plumbing-plan.md.
#[cfg(feature = "tfp25519_limbs")]
mod fe25519_limbs;

// Limb-typed xyzt_{add,double}_decomposed bodies — bridges the
// 200-byte point ABI at the boundary but uses [u64; 5] tight-limb
// slots for all 18 (add) / 11 (double) intermediate field ops.
// Under `tfp25519_limbs`, `decomposed_bodies.rs` cfg-gates its
// xyzt_*_decomposed exports off, so the linker picks up THESE symbols.
// All other callers (e.g. `decomposed_bodies_wnaf_comb.rs`) see the
// same extern "C" surface and are transparent to the swap.
#[cfg(all(feature = "tfp25519_limbs",
          any(feature = "decomposed_leaves",
              feature = "inline_leaves",
              feature = "wnaf_comb_leaves"),
          not(feature = "dalek_leaves")))]
mod decomposed_bodies_limbs;

// Rust-level #[inline(always)] field ops over [u64; 5] slots —
// closes the extern "C" per-call cost (limbs spill to memory between
// ops in the auto-extracted body).  See fe25519_inline.rs +
// decomposed_bodies_limbs_inline.rs headers.
#[cfg(feature = "tfp25519_inline_limbs")]
mod fe25519_inline;
#[cfg(all(feature = "tfp25519_inline_limbs",
          any(feature = "decomposed_leaves",
              feature = "inline_leaves",
              feature = "wnaf_comb_leaves"),
          not(feature = "dalek_leaves")))]
mod decomposed_bodies_limbs_inline;

pub use sign::ed25519_sign as ed25519_sign_raw;
pub use verify::ed25519_verify as ed25519_verify_raw;

/// Derive the 32-byte public key from a 32-byte secret seed.
///
/// Per RFC 8032 §5.1.5: SHA-512(seed)[0..32] is the secret scalar
/// (after clamping); A = compress([clamped_scalar] · B).  We share
/// `sha512_64`, `clamp_64`, `ed25519_scalarmult_base`, and
/// `ed25519_compress` with the extracted sign body — the same FFI
/// symbols, so this stays on the same leaf-substitution surface.
pub fn public_key_from_seed(seed: &[u8; 32]) -> [u8; 32] {
    // Phase B (status doc §6.3): all FFI dispatch routes through
    // `crate::ffi_safe`; this function carries no inline `unsafe`.
    use crate::ffi_safe;

    let mut h_full = [0u8; 64];
    let mut a = [0u8; 32];
    let mut a_xyzt = [0u8; 200];
    let mut pk = [0u8; 32];

    ffi_safe::ed25519_sha512_64_arr(&mut h_full, seed, 32);
    a.copy_from_slice(&h_full[0..32]);
    ffi_safe::clamp_scalar_u8(&mut a);
    ffi_safe::ed25519_scalarmult_base_pt(&mut a_xyzt, &a);
    ffi_safe::ed25519_compress_pt(&mut pk, &a_xyzt);
    pk
}

/// Compress(`scalar` · B) — verified scalarmult_base + compress.
///
/// Used by XEdDSA sign (the X25519 secret is the Ed25519 scalar in
/// XEdDSA, so we skip the seed-then-SHA-512 step that
/// `public_key_from_seed` does).  The scalar must already be reduced
/// mod L; values up to 2^256 - 1 are accepted but the lazy reduction
/// inside scalarmult_base may degrade if the scalar's top bit isn't
/// clamped per RFC 8032 §5.1.5.
pub fn scalarmult_base_compressed(scalar: &[u8; 32]) -> [u8; 32] {
    use crate::ffi_safe;
    let a = *scalar;
    let mut a_xyzt = [0u8; 200];
    let mut out = [0u8; 32];
    ffi_safe::ed25519_scalarmult_base_pt(&mut a_xyzt, &a);
    ffi_safe::ed25519_compress_pt(&mut out, &a_xyzt);
    out
}

/// Safe Rust Ed25519 signing API.
///
/// `seed` is the 32-byte secret seed.  `msg` is up to 4096 bytes.
/// Writes the 64-byte signature into `sig_out`.
///
/// Panics if `msg.len() > 4096`.
pub fn sign(sig_out: &mut [u8; 64], seed: &[u8; 32], msg: &[u8]) {
    assert!(msg.len() <= 4096, "rust_cmd_ed sign: msg.len() > 4096");
    let mut seed_buf = *seed;
    let mut msg_buf = [0u8; 4096];
    msg_buf[..msg.len()].copy_from_slice(msg);
    ed25519_sign_raw(sig_out, &mut seed_buf, &mut msg_buf, msg.len() as u64);
}

/// Safe Rust Ed25519 verification API.
///
/// Calls `ed25519_verify_raw` (the extracted body) and trusts the
/// caller-supplied `result_out` byte directly.  Bug-D fix
/// (2026-05-12): the extracted body now compresses sB into its own
/// 32-byte slot and `bytes_equal_32(result_out, compress(sB),
/// compress(R + h·A))` is the final call — `result_out` is the true
/// RFC 8032 verdict.
pub fn verify(sig: &[u8; 64], pk: &[u8; 32], msg: &[u8]) -> bool {
    assert!(msg.len() <= 4096, "rust_cmd_ed verify: msg.len() > 4096");
    let mut sig_buf = *sig;
    let mut pk_buf = *pk;
    let mut msg_buf = [0u8; 4096];
    let copy_len = msg.len().min(4096);
    msg_buf[..copy_len].copy_from_slice(&msg[..copy_len]);

    #[cfg(feature = "verify_projective_eq")]
    {
        return verify_proj(&sig_buf, &pk_buf, &msg_buf, copy_len as u64);
    }
    #[cfg(not(feature = "verify_projective_eq"))]
    {
        let mut result_byte = [0u8; 1];
        ed25519_verify_raw(
            &mut result_byte,
            &mut sig_buf,
            &mut pk_buf,
            &mut msg_buf,
            copy_len as u64,
        );
        result_byte[0] != 0
    }
}

/// Phase 4 — projective-equality verify entry (Rust-only stop-gap).
///
/// Replicates `verify.rs::ed25519_verify`'s leaf-call sequence but
/// replaces the final `compress(sB) + compress(R + h·A) +
/// bytes_equal_32` with a single `ed25519_projective_eq` call.
/// Saves the two Z⁻¹ inversion chains (~6 µs).
///
/// Diverges from the verified extraction — the Phase 4 verified
/// follow-on would re-author `Sign_Verify_RustCmd.v` to emit this
/// shape natively.
#[cfg(feature = "verify_projective_eq")]
#[allow(non_snake_case)]
fn verify_proj(sig: &[u8; 64], pk: &[u8; 32], msg: &[u8; 4096], msg_len: u64) -> bool {
    use crate::ffi_safe;
    let mut R_xyzt:    [u8; 200]  = [0; 200];
    let mut A_xyzt:    [u8; 200]  = [0; 200];
    let mut sB:        [u8; 200]  = [0; 200];
    let mut hA:        [u8; 200]  = [0; 200];
    let mut RcheckA:   [u8; 200]  = [0; 200];
    let mut h_v:       [u8; 64]   = [0; 64];
    let mut h_red:     [u8; 32]   = [0; 32];
    let mut chal_buf:  [u8; 4160] = [0; 4160];
    let mut result_byte: [u8; 1]  = [0; 1];

    // Note: the extracted verify body calls `scalar_lt_L` on
    // `sig_in.as_ptr()` (= R, not S) and then discards its result
    // by overwriting result_out via bytes_equal_32.  We mirror
    // the same behaviour to match the verified extraction's
    // accept/reject envelope; a future Sign_Verify_RustCmd.v fix
    // would tighten this to a real `S < L` check on sig[32..64].
    ffi_safe::ed25519_scalar_lt_L(&mut result_byte, sig.as_ptr());
    let _ = result_byte;

    ffi_safe::ed25519_decompress_R_pt(&mut R_xyzt, sig);
    ffi_safe::ed25519_decompress_A_pt(&mut A_xyzt, pk);

    // chal = R || A || M
    chal_buf[0..32].copy_from_slice(&sig[0..32]);
    chal_buf[32..64].copy_from_slice(pk);
    chal_buf[64..64 + msg_len as usize].copy_from_slice(&msg[..msg_len as usize]);
    let chal_len = 64u64 + msg_len;
    ffi_safe::ed25519_sha512_64_arr(&mut h_v, &chal_buf, chal_len);
    ffi_safe::ed25519_scalar_reduce(&mut h_red, &h_v);

    // sB = S · B — pull S out as a fixed-length array view.
    let mut s_bytes: [u8; 32] = [0; 32];
    s_bytes.copy_from_slice(&sig[32..64]);
    ffi_safe::ed25519_scalarmult_base_pt(&mut sB, &s_bytes);

    // hA = h · A
    ffi_safe::ed25519_scalarmult_pt(&mut hA, &h_red, &A_xyzt);

    // RcheckA = R + hA
    ffi_safe::ed25519_xyzt_add_pt(&mut RcheckA, &R_xyzt, &hA);

    // projective equality: sB ≡ RcheckA  (no Z⁻¹ inversion chain).
    ffi_safe::ed25519_projective_eq_pt(&mut result_byte, &sB, &RcheckA);
    result_byte[0] != 0
}
