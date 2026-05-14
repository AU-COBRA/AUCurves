(** * OCaml extraction of Lizard inject as a single [jasmin_func].
 *
 *  Sibling of [Ed25519_Sign_Inlined.v] / [Ed25519_Sign_Inlined_Hoist.v]
 *  (A6 / A105) — pipes [lizard_inject_rs] (End2End/Lizard/Inject_RustCmd.v)
 *  through the same chain:
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
 *  ## Why Lizard is the natural next protocol after Ed25519 sign
 *
 *  Lizard inject is structurally MUCH simpler than Ed25519 sign:
 *    - 2 stack-allocated buffers (buf32, xyzt) vs. Ed25519 sign's 13
 *    - 3 FFI calls (lizard_pack, elligator2_to_edwards, ristretto_encode)
 *      vs. Ed25519 sign's ~14
 *    - No SHA-512 register-coalescing problem (A99): the FFI leaves are
 *      called once each, with distinct first arguments, no aliasing.
 *
 *  This means register pressure (A120's Blocker D for whole-Ed25519-sign
 *  Jasmin) is unlikely to bite here.  Lizard inject is the empirical
 *  test of whether the Rocq → Jasmin Bridge produces working .jazz for
 *  a simpler-than-Ed25519 Signal protocol.
 *
 *  ## FFI leaves
 *
 *  Same Tier-4 / path-(b) treatment as the stubbed Ed25519 sign:
 *  jasminc's MakeReferenceArguments pass (pass 16/30) needs every
 *  callee declared.  The driver ([lizard_inject_main.ml]) prepends
 *  empty-body [JCskip] stubs for the 3 leaves (or a separate
 *  [Lizard_Inject_StubLeaves.v] extraction analog to
 *  [Ed25519_Sign_StubLeaves.v]).
 *
 *  ## Status
 *
 *  STATUS (2026-05-14): Empirical gate.  Compositional definitions all
 *  Qed-clean via the same chain Ed25519 sign uses.  The blocker A120
 *  Phantom-Reg-as-ptr refactor is NOT needed here — the function has
 *  only 4 named buffer params (pt, out) and 2 stack locals (buf32,
 *  xyzt), comfortably within x86-64's GPR budget.
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
Require Import Bedrock.End2End.Lizard.Inject_RustCmd.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Empty function table — [lizard_inject_rs] has no [REdCallFn] sites,
    every callee is a [REdCall] FFI leaf.  Inliner is a no-op here but
    we apply it for shape symmetry with [Ed25519_Sign_Inlined]. *)
Definition lizard_inject_ftab : function_table_ed := nil.

(** Inline depth 4 mirrors [Ed25519_Sign_Inlined.v]'s budget.  Lizard
    inject is leaf-shallow so any depth ≥ 0 suffices. *)
Definition lizard_inject_inlined_rs : rust_cmd_ed :=
  inline_callfn_n 4 lizard_inject_ftab lizard_inject_rs.

(** Lift to [jasmin_cmd] via the verified chain
    [tr_cmd ∘ to_bedrock_cmd ∘ normalize_select]. *)
Definition lizard_inject_inlined_jcmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin lizard_inject_inlined_rs.

(** Wrap as a [jasmin_func].  Lizard inject takes two byte-buffer
    parameters:
      [pt] : 16B plaintext input
      [out] : 32B Ristretto output
    plus two stack locals (buf32:32B, xyzt:200B) allocated via
    [REdLetZero] → [JCdecl] in the body.  We use [polish_func_hoist]
    (the A105 hoist variant) so the 2 stack-array decls land in
    [jf_locals] rather than remaining inline as [JCdecl] nodes — same
    fix that unblocked Ed25519 sign's stackalloc lowering. *)
Definition lizard_inject_inlined_func : jasmin_func :=
  polish_func_hoist {|
    jf_name := "lizard_inject";
    jf_params := [("pt", JTptr 2); ("out", JTptr 4)];
    jf_locals := nil;
    jf_body := lizard_inject_inlined_jcmd;
  |}.

(** Wrap in a single-element list.  Pre-reduce with [vm_compute] so
    all typeclass-projected size constants become Z literals. *)
Definition lizard_inject_all_jasmin : list jasmin_func :=
  Eval vm_compute in [lizard_inject_inlined_func].

Definition lizard_inject_field_size : Z := 5.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "lizard_inject_jasmin_extracted"
  lizard_inject_all_jasmin lizard_inject_field_size
  pp_func pp_module.
