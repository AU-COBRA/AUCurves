(** * OCaml extraction of inlined Ed25519 sign — STACK-AWARE variant
 *
 *  Sibling of [Ed25519_Sign_Inlined.v] (A6) that opts in to the
 *  [polish_func_hoist] pass (added 2026-05-14 in
 *  [Bedrock/Jasmin/Core.v]).  The hoist pass lifts every
 *  [JCdecl x (JTstack n) body] node in the function body up to the
 *  function-level [jf_locals] field, leaving the body with the
 *  [JCdecl] nodes erased.
 *
 *  ## Why this exists
 *
 *  [Ed25519_Sign_Inlined.v]'s [ed25519_sign_inlined_func] uses
 *  [polish_func] (no hoist), so the 13 stack-array declarations
 *  produced by [REdLetZero] → [cmd.stackalloc] → [JCdecl x (JTstack
 *  nwords) body] remain INLINE in the body.  The downstream OCaml
 *  driver / [JasminBridgeReal.to_jasmin_cmd] both erase those
 *  [JCdecl] nodes when they encounter them, dropping the type
 *  information completely.  The named variables (h_full[64],
 *  A_xyzt[200], nonce_buf[4128], …) are then created as bare
 *  [Reg/u64] vars by the OCaml driver's [mk_var], and jasminc's
 *  register allocator assigns them to arbitrary GPRs.  The emitted
 *  asm consequently dereferences register-garbage on the first
 *  call → SIGSEGV (the A103 sign-segfaults symptom).
 *
 *  ## What the hoist achieves
 *
 *  After [polish_func_hoist] the structurally-equivalent body has
 *  every [JCdecl JTstack] node erased, but the [(name, JTstack n)]
 *  entries are preserved in [jf_locals].  A downstream extraction
 *  pass / OCaml driver enhancement can read [jf_locals] to
 *  materialise these as [Stack-kind / Arr (U U64) N] vars in the
 *  Jasmin function record, where jasminc's StackAllocation pass
 *  then lowers them to [rsp+N] addressing in the emitted asm.
 *
 *  ## Trust posture
 *
 *  The hoist is a syntactic AST rewrite proved sound at the
 *  [BridgeReal.to_jasmin_cmd] level by [to_jasmin_cmd_decl] (Qed,
 *  BridgeReal.v line 198): [to_jasmin_cmd (JCdecl x ty body) =
 *  to_jasmin_cmd body].  Hoisting the decl out of the body and into
 *  the function's [jf_locals] is observationally equivalent at the
 *  [psem.sem] level.  No new axioms.
 *
 *  ## Backward compatibility
 *
 *  [Ed25519_Sign_Inlined.v]'s extraction targets are unchanged.
 *  This file produces a parallel extraction target
 *  [ed25519_sign_hoist_jasmin_extracted] which a downstream driver
 *  can opt in to.
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
    so [inline_callfn_n] is a no-op. *)
Definition ed25519_sign_hoist_ftab : function_table_ed := nil.

(** Inline depth 4 covers Ed25519 sign / verify callgraphs. *)
Definition ed25519_sign_hoist_inlined_rs : rust_cmd_ed :=
  inline_callfn_n 4 ed25519_sign_hoist_ftab ed25519_sign_rs.

(** Lift to [jasmin_cmd] via the verified chain. *)
Definition ed25519_sign_hoist_inlined_jcmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin ed25519_sign_hoist_inlined_rs.

(** Wrap as a [jasmin_func], then run the stack-aware polish pipeline.
    Unlike [Ed25519_Sign_Inlined.ed25519_sign_inlined_func] which uses
    [polish_func], we use [polish_func_hoist] so the 13 stack-array
    declarations land in [jf_locals]. *)
Definition ed25519_sign_hoist_inlined_func : jasmin_func :=
  polish_func_hoist {|
    jf_name := "ed25519_sign";
    jf_params := [("sig_out", JTptr 8); ("seed", JTptr 4); ("msg", JTptr 512);
                  ("msg_len", JTptr 1)];
    jf_locals := nil;
    jf_body := ed25519_sign_hoist_inlined_jcmd;
  |}.

(** Wrap in a single-element list.  Pre-reduce with [vm_compute]
    so all typeclass-projected size constants become Z literals. *)
Definition ed25519_sign_hoist_all_jasmin : list jasmin_func :=
  Eval vm_compute in [ed25519_sign_hoist_inlined_func].

Definition ed25519_sign_hoist_field_size : Z := 5.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "ed25519_sign_hoist_jasmin_extracted"
  ed25519_sign_hoist_all_jasmin ed25519_sign_hoist_field_size
  pp_func pp_module.
