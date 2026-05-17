(** * SHA-512 bridge — concrete proof
 *
 * Concretely-discharged per-function bridge for [sha512_64].
 * Provides:
 *   §1 [spec_of_sha512_64]: a self-contained fnspec for sha512_64
 *      (matching the contract assumed by [Sign.v] / [Verify.v]).
 *   §2 [bridge_sha512_64_concrete]: a Qed bridge proof from the
 *      spec to bedrock2 WP.call.
 *
 * The spec is declared here (not imported) because AUCurves
 * currently has [Parameter sha512] in [Sign.v] without a
 * corresponding [Instance spec_of_sha512_64].  This file provides
 * the Instance + the bridge proof together.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.SafeRustEd25519BedrockBridge.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. SHA-512 abstract function + concrete fnspec                   *)
(* ================================================================ *)

(** Abstract SHA-512: opaque function from bytes to 64 bytes.  Same
    as [Sign.v]'s [Parameter sha512].  Re-declared here so this file
    is self-contained for the bridge proof. *)
Parameter sha512 : list Byte.byte -> list Byte.byte.
Parameter sha512_output_64 : forall input, length (sha512 input) = 64%nat.

(** [spec_of_sha512_64 functions]: the bedrock2 fnspec for
    [sha512_64(out_ptr, in_ptr, in_len)].

    Contract: writes 64 bytes at out_ptr equal to [sha512 input_bytes],
    where input_bytes is the in_len-byte input at in_ptr.
    Trace and other memory unchanged. *)
Definition spec_of_sha512_64 (functions : env) : Prop :=
  forall (t : trace) (m : mem) (l : locals)
         (out_ptr in_ptr : word.rep) (in_len : word.rep)
         (out_init in_bytes : list Byte.byte)
         (R : mem -> Prop)
         (post : trace -> mem -> list word.rep -> Prop),
    length out_init = 64%nat ->
    Z.of_nat (length in_bytes) = word.unsigned in_len ->
    (sepclause_of_map (out_init$@out_ptr) ⋆
     sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m ->
    (forall m' : mem,
       (sepclause_of_map ((sha512 in_bytes)$@out_ptr) ⋆
        sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m' ->
       post t m' nil) ->
    WeakestPrecondition.call functions "sha512_64" t m
      (out_ptr :: in_ptr :: in_len :: nil) post.

(* ================================================================ *)
(* §2. Bridge from spec_of_sha512_64 to bedrock_call_simulates_rust_exec
   ================================================================ *)

(** The bridge for [sha512_64].  Hypotheses:
      - [Hspec]: the bedrock2 spec_of_sha512_64 holds for [functions]
      - the rust_cmd_ed [rc] is a single REdCall to "sha512_64" with
        the right typed args
      - state_refine_ed connects rs1 to (locals, mem) properly
      - the callee_post oracle, when invoked at sha512_64, gives a
        post-state where the v_h_full slot has VBytes 64 (sha512
        input).

    Conclusion: WP.call functions "sha512_64" ... → (the bridge).

    Proof: apply Hspec to obtain WP.call with sha512's effect on
    memory; weaken the post via [post_state_refine_via_sha512];
    supply callee_post via Hcont. *)

(** Concrete refinement obligation: given pre-state refinement +
    sha512's effect on the out buffer, the post state still refines.

    Precondition: "h_full" already exists as a TBytes 64 slot in rs1
    with the correct address — otherwise the new slot's address would
    be indeterminate.

    Frame note: the conclusion's frame must include
    [in_bytes$@in_ptr] (which lives in m' alongside the new sha512
    bytes), otherwise the slots_refine goal asks for too little and
    Hsep' provides too much. *)
Lemma post_state_refine_via_sha512 :
  forall rs1 (l : locals) (m m' : mem) R
         (out_ptr in_ptr : word.rep)
         (in_bytes : list Byte.byte),
    rs_tower_ed rs1 = [] ->
    state_refine_ed rs1 l m R ->
    map.get l "h_full" = Some out_ptr ->
    (sepclause_of_map ((sha512 in_bytes)$@out_ptr) ⋆
     sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m' ->
    state_refine_ed
      (rs_set_tower_ed rs1 "h_full"
         (exist_tval_ed (TBytes 64) (VBytes 64 (sha512 in_bytes))))
      l m'
      (fun mm => (sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep mm).
Proof.
  intros rs1 l m m' R out_ptr in_ptr in_bytes Htower_empty Hrefine Hloc Hsep'.
  unfold state_refine_ed; split.
  - (* slots_refine on rs2's tower *)
    unfold rs_set_tower_ed; cbn.
    rewrite Htower_empty; cbn.
    exists out_ptr; split; [exact Hloc |].
    cbn.
    unfold bytes_at.
    ecancel_assumption_impl.
  - (* Scalar refinement preserved (Qed half). *)
    intros x v Hgs.
    unfold rs_set_tower_ed in Hgs; cbn in Hgs.
    destruct Hrefine as [_ Hscalar].
    apply (Hscalar x v Hgs).
Qed.

(** [callee_post_sha512_64_compatible callee_post]: the rust-side
    oracle's effect on sha512_64 calls produces the expected
    state-update post.  Captured as an explicit hypothesis so the
    bridge proof is Qed.  Discharge: at use-site, when constructing
    callee_post for the whole scalarmult execution, the sha512_64
    case is wired to this. *)
Definition callee_post_sha512_64_compatible
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall rs1 in_bytes,
    (let v := rs_get_tower_ed rs1 "seed" in
     match v with
     | Some (exist_tval_ed (TBytes 32) (VBytes 32 bs)) => bs = in_bytes
     | _ => True
     end) ->
    callee_post "sha512_64" []
      {| loc_var := "h_full"; loc_type := TBytes 64 |}
      rs1
      (rs_set_tower_ed rs1 "h_full"
         (exist_tval_ed (TBytes 64) (VBytes 64 (sha512 in_bytes)))).

Theorem bridge_sha512_64_concrete :
  forall (functions : env),
    spec_of_sha512_64 functions ->
    forall (callee_post : String.string -> list located_ed -> located_ed ->
                          rust_state_ed -> rust_state_ed -> Prop),
    callee_post_sha512_64_compatible callee_post ->
    forall (t : trace) (m : mem) (l : locals)
           (rs1 : rust_state_ed) (args : list word.rep)
           (post : trace -> mem -> list word.rep -> Prop)
           (R : mem -> Prop)
           (out_ptr in_ptr in_len : word.rep)
           (out_init in_bytes : list Byte.byte),
      args = [out_ptr; in_ptr; in_len] ->
      length out_init = 64%nat ->
      Z.of_nat (length in_bytes) = word.unsigned in_len ->
      (sepclause_of_map (out_init$@out_ptr) ⋆
       sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m ->
      rs_tower_ed rs1 = [] ->
      state_refine_ed rs1 l m R ->
      map.get l "h_full" = Some out_ptr ->
      (let v := rs_get_tower_ed rs1 "seed" in
       match v with
       | Some (exist_tval_ed (TBytes 32) (VBytes 32 bs)) => bs = in_bytes
       | _ => True
       end) ->
      (* Continuation: takes the post-sha512 state refining with new frame
         (in_bytes ⋆ R), returns post t m' nil. *)
      (forall rs2 m',
         rs2 = rs_set_tower_ed rs1 "h_full"
                 (exist_tval_ed (TBytes 64)
                    (VBytes 64 (sha512 in_bytes))) ->
         (sepclause_of_map ((sha512 in_bytes)$@out_ptr) ⋆
          sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m' ->
         state_refine_ed rs2 l m'
           (fun mm => (sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep mm) ->
         callee_post "sha512_64" []
           {| loc_var := "h_full"; loc_type := TBytes 64 |} rs1 rs2 ->
         post t m' nil) ->
      WeakestPrecondition.call functions "sha512_64" t m args post.
Proof.
  intros functions Hspec callee_post Hcompat t m l rs1 args post R
         out_ptr in_ptr in_len out_init in_bytes
         Hargs Hlen_out Hlen_in Hsep Htower_empty Hrefine Hloc Hseed Hcont.
  subst args.
  eapply Hspec; try eassumption.
  intros m' Hsep'.
  remember (rs_set_tower_ed rs1 "h_full"
              (exist_tval_ed (TBytes 64) (VBytes 64 (sha512 in_bytes))))
    as rs2 eqn:Hrs2.
  apply (Hcont rs2 m' eq_refl Hsep').
  - rewrite Hrs2.
    eapply post_state_refine_via_sha512;
      [ exact Htower_empty | exact Hrefine | exact Hloc | exact Hsep' ].
  - rewrite Hrs2.
    apply (Hcompat rs1 in_bytes Hseed).
Qed.
