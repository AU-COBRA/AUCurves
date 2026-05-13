(** * OCaml extraction of inlined Ed25519 sign as a single [jasmin_func].
 *
 *  Empirical gate for the whole-protocol Jasmin emission plan
 *  (docs/whole-protocol-jasmin-plan.md / roadmap #9): pipe the
 *  [ed25519_sign_rs] body (Sign_Verify_RustCmd.v) through the chain
 *
 *      rust_cmd_ed
 *        ↓ inline_callfn_n 4 ftab               (InlineCallFn.v)
 *        ↓ rust_cmd_ed_to_jasmin                (RustCmdEdToJasmin.v
 *                                                = tr_cmd ∘ to_bedrock_cmd ∘ normalize_select)
 *      jasmin_cmd
 *        ↓ polish_func ∘ wrap-as-[jasmin_func]  (Jasmin/Core.v)
 *      jasmin_func
 *        ↓ Extraction (OCaml)
 *        ↓ ocaml_compile.ml driver              (jasminc compiler pipeline)
 *      x86-64 .s
 *
 *  STATUS: The current [ed25519_sign_rs] (in Sign_Verify_RustCmd.v) has
 *  NO [REdCallFn] sites — every callee is [REdCall] (FFI leaf), so
 *  [inline_callfn_n 4 empty_ftab _ = id].  We apply it anyway so the
 *  glue is forward-compatible with the [_with_callfn_clamp] variant
 *  (and future REdCallFn-rich bodies emitted by RustCmdRupicola).
 *
 *  The 25 FFI leaves (sha512_64, ed25519_scalarmult_base, ...) become
 *  Jasmin [JCcall] sites referring to functions NOT present in the
 *  extracted [jasmin_func] list.  Acceptable for the gate: jasminc's
 *  [func_filter] machinery (ocaml_compile.ml) lets the driver pick
 *  which function to compile; missing transitive callees are reported.
 *)

From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
From Stdlib Require Import ZArith String List.
Import ListNotations.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.InlineCallFn.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Empty function table — [ed25519_sign_rs] has no [REdCallFn] sites,
    so [inline_callfn_n] is a no-op.  This still exercises the inliner
    pass end-to-end (proven Qed in InlineCallFn.v) on the protocol
    body, so the glue is ready for [_with_callfn_clamp]-style bodies. *)
Definition ed25519_sign_ftab : function_table_ed := nil.

(** Inline depth 4 covers Ed25519 sign / verify callgraphs per
    InlineCallFn.v's per-protocol metaproperty note (sign → scalarmult_base
    → fe25519_mul → leaf ≤ 3 + 1 buffer). *)
Definition ed25519_sign_inlined_rs : rust_cmd_ed :=
  inline_callfn_n 4 ed25519_sign_ftab ed25519_sign_rs.

(** Lift to [jasmin_cmd] via the verified chain
    [tr_cmd ∘ to_bedrock_cmd ∘ normalize_select]. *)
Definition ed25519_sign_inlined_jcmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin ed25519_sign_inlined_rs.

(** Wrap as a [jasmin_func].  The protocol takes four byte-buffer
    parameters: [sig_out] (64B), [seed] (32B), [msg] (4096B), [msg_len]
    (u64 scalar).  We declare all four as [u64] params — the actual
    sizes are recovered downstream from the [stackalloc] nodes emitted
    by [to_bedrock_cmd] (each [REdLetZero] becomes [JCdecl]).

    [polish_func] runs the codegen-polish pipeline (lower binops,
    normalize, lift literals, simplify, lower mulx, chunk, carry,
    lower comparisons) on the body. *)
Definition ed25519_sign_inlined_func : jasmin_func :=
  polish_func {|
    jf_name := "ed25519_sign";
    jf_params := [("sig_out", JTptr 8); ("seed", JTptr 4); ("msg", JTptr 512);
                  ("msg_len", JTptr 1)];
    jf_locals := nil;
    jf_body := ed25519_sign_inlined_jcmd;
  |}.

(** Wrap in a single-element list so the driver consumes it the same
    way it consumes [bls12_all_jasmin] / [x25519_64_all_jasmin].  Pre-
    reduce with [vm_compute] so all typeclass-projected size constants
    become Z literals (required by stackalloc → JCdecl translation). *)
Definition ed25519_sign_all_jasmin : list jasmin_func :=
  Eval vm_compute in [ed25519_sign_inlined_func].

(** Field-size is informational for the driver.  Ed25519 uses 5-limb
    unsaturated solinas for fe25519 but the sign body itself only
    references opaque FFI leaves, so this constant is decorative
    (kept for symmetry with [x25519_64_field_size]). *)
Definition ed25519_sign_field_size : Z := 5.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "ed25519_sign_jasmin_extracted"
  ed25519_sign_all_jasmin ed25519_sign_field_size
  pp_func pp_module.
