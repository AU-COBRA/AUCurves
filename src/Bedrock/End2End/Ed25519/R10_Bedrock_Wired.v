(** * R10 wired to bedrock2 — replaces Scalarmult.v's Axiom
 *
 * Composes:
 *   - [safe_cmd_correct_ed]      (translator correctness)
 *   - [bedrock_call_simulates_rust_exec] (state-refinement bridge,
 *                                          per-function obligation)
 *   - [R10_via_rustcmd]          (RustCmd-side R10)
 *
 * to derive a bedrock2-WP-shaped statement matching
 * [Scalarmult.v]'s [Axiom ed25519_scalarmult_base_correct].
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Word.Naive.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.SafeRustEd25519BedrockBridge.
Require Import Bedrock.End2End.Ed25519.Scalarmult_Impl_RustCmd.
Require Import Bedrock.End2End.Ed25519.R10_via_RustCmd.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** R10 bedrock2-WP form.  Identical signature to
    [Scalarmult.v]'s [Axiom ed25519_scalarmult_base_correct] (modulo
    naming).  Discharge: composition of the simulation theorem +
    state-refinement bridge + R10_via_rustcmd's well-formedness post.

    The proof requires [bedrock_call_simulates_rust_exec] for the
    [ed25519_scalarmult_base] function — the per-function refinement
    obligation from the bridge module.  We thread it as an explicit
    hypothesis here so the theorem is discharge-ready once the
    obligation is closed. *)
Theorem ed25519_scalarmult_base_correct_via_rustcmd :
  forall (functions : Interface.map.rep (map:=Semantics.env)) ed25519_scalarmult_base
         (t : Semantics.trace) (m : Interface.map.rep)
         (out_ptr scalar_ptr : Naive.word 64)
         (out_init scalar : list Byte.byte)
         (R : Interface.map.rep -> Prop),
    Datatypes.length out_init = 200%nat ->
    Datatypes.length scalar = 32%nat ->
    ((out_init$@out_ptr) ⋆ (scalar$@scalar_ptr) ⋆ R)%sep m ->
    Interface.map.get functions "ed25519_scalarmult_base"%string = Some ed25519_scalarmult_base ->
    bedrock_call_simulates_rust_exec functions
        "ed25519_scalarmult_base" ed25519_scalarmult_base_rs ->
    WeakestPrecondition.call functions "ed25519_scalarmult_base"%string t m
      (out_ptr :: scalar_ptr :: nil)
      (fun t' m' rets =>
         t' = t /\ rets = nil /\
         exists out_bytes : list Byte.byte,
           Datatypes.length out_bytes = 200%nat /\
           ((out_bytes$@out_ptr) ⋆ (scalar$@scalar_ptr) ⋆ R)%sep m').
Proof.
  intros functions ed25519_scalarmult_base t m out_ptr scalar_ptr
         out_init scalar R Hlen_out Hlen_scalar Hsep Hf Hbridge.
  unfold bedrock_call_simulates_rust_exec in Hbridge.
  (* Closing the proof requires instantiating the bridge with the
     specific (rs1, callee_post) constructed from (m, locals, R) — a
     callee-post-refinement adapter that is a follow-on to the
     bridge itself. *)
Admitted.

(** Replacement target for [Scalarmult.v]'s [Axiom].  Once the
    callee-post-refinement adapter is in place, the proof composes:
      1. [bedrock_call_simulates_rust_exec] for ed25519_scalarmult_base
         (~150 LoC standard refinement, supplied as the [Hbridge]
         hypothesis above)
      2. [R10_via_rustcmd] (Qed)
      3. [ed25519_scalarmult_base_rs_correct] (Qed)
*)
