(** * The remaining 4 per-function bridges
 *
 * Following the [SHA512Bridge.v] pattern, this file discharges
 * [bedrock_call_simulates_rust_exec] for:
 *   §1 scalar_reduce         (64 byte → 32 byte, mod L)
 *   §2 scalar_muladd         (3×32 byte → 32 byte, r+k·a mod L)
 *   §3 ed25519_compress      (200 byte → 32 byte)
 *   §4 ed25519_scalarmult_base (32 byte → 200 byte)
 *
 * Each one: spec_of_FNAME + callee_post_FNAME_compatible +
 * post_state_refine_via_FNAME (Qed via ecancel_assumption_impl) +
 * bridge_FNAME_concrete (Qed via composition).
 *
 * Plan: [R10_RUSTCMD_PORT_PLAN.md] D26.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
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
Require Export Bedrock.End2End.Ed25519.CompressVerified.
Require Export Bedrock.End2End.Ed25519.ScalarmultBaseVerified.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. scalar_reduce — 64 byte → 32 byte mod L                       *)
(* ================================================================ *)

(** Ed25519 curve order:
      L = 2^252 + 27742317777372353535851937790883648493.

    [scalar_reduce_spec] is the standard mathematical reduction
    [n mod L] for [n = le_combine bs64], re-encoded as 32 LE bytes.
    This is the same definition as RFC 8032's [sc_reduce] at the
    Z level — independent of how an optimized implementation
    computes it (Barrett, Montgomery, schoolbook).

    NOT an axiom: concrete Definition, reduces by [vm_compute] on
    any concrete input.  A duplicate Definition (with the long-form
    name [scalar_reduce_gallina]) is re-exported from
    [Bedrock.End2End.Ed25519.ScalarReduceVerified] for backward
    compatibility, but the canonical name is [scalar_reduce_spec]. *)
Definition L_curve_order : Z :=
  2 ^ 252 + 27742317777372353535851937790883648493.

Lemma L_curve_order_pos : 0 < L_curve_order.
Proof. cbv [L_curve_order]. lia. Qed.

Definition scalar_reduce_spec (bs64 : list Byte.byte) : list Byte.byte :=
  let n : Z := le_combine bs64 in
  let r : Z := Z.modulo n L_curve_order in
  le_split 32 r.

Lemma scalar_reduce_output_32 :
  forall input, length (scalar_reduce_spec input) = 32%nat.
Proof.
  intros input. cbv [scalar_reduce_spec].
  apply length_le_split.
Qed.

Definition spec_of_scalar_reduce (functions : env) : Prop :=
  forall (t : trace) (m : mem) (l : locals)
         (out_ptr in_ptr : word.rep)
         (out_init in_bytes : list Byte.byte)
         (R : mem -> Prop)
         (post : trace -> mem -> list word.rep -> Prop),
    length out_init = 32%nat ->
    length in_bytes = 64%nat ->
    (sepclause_of_map (out_init$@out_ptr) ⋆
     sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m ->
    (forall m' : mem,
       (sepclause_of_map ((scalar_reduce_spec in_bytes)$@out_ptr) ⋆
        sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m' ->
       post t m' nil) ->
    WeakestPrecondition.call functions "scalar_reduce" t m
      (out_ptr :: in_ptr :: nil) post.

Definition callee_post_scalar_reduce_compatible
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall rs1 in_bytes (out_var : String.string),
    callee_post "scalar_reduce" []
      {| loc_var := out_var; loc_type := TBytes 32 |}
      rs1
      (rs_set_tower_ed rs1 out_var
         (exist_tval_ed (TBytes 32) (VBytes 32 (scalar_reduce_spec in_bytes)))).

Lemma post_state_refine_via_scalar_reduce :
  forall rs1 (l : locals) (m m' : mem) R
         (out_ptr in_ptr : word.rep)
         (in_bytes : list Byte.byte)
         (out_var : String.string),
    rs_tower_ed rs1 = [] ->
    state_refine_ed rs1 l m R ->
    map.get l out_var = Some out_ptr ->
    (sepclause_of_map ((scalar_reduce_spec in_bytes)$@out_ptr) ⋆
     sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m' ->
    state_refine_ed
      (rs_set_tower_ed rs1 out_var
         (exist_tval_ed (TBytes 32) (VBytes 32 (scalar_reduce_spec in_bytes))))
      l m'
      (fun mm => (sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep mm).
Proof.
  intros rs1 l m m' R out_ptr in_ptr in_bytes out_var
         Htower_empty Hrefine Hloc Hsep'.
  unfold state_refine_ed; split.
  - unfold rs_set_tower_ed; cbn.
    rewrite Htower_empty; cbn.
    exists out_ptr; split; [exact Hloc |].
    cbn.
    unfold bytes_at.
    match goal with
    | |- (?P ⋆ (fun m => ?Q m))%sep ?z => change ((P ⋆ Q)%sep z)
    end; ecancel_assumption_impl.
  - intros x v Hgs.
    unfold rs_set_tower_ed in Hgs; cbn in Hgs.
    destruct Hrefine as [_ Hscalar].
    apply (Hscalar x v Hgs).
Qed.

(* ================================================================ *)
(* §2. scalar_muladd — out := (r + k·a) mod L                        *)
(* ================================================================ *)

(** [scalar_muladd_spec r k a] computes [(r + k*a) mod L] over
    32-byte little-endian scalars, returning a 32-byte little-endian
    output.  This is the standard mathematical definition used in
    Ed25519 signing (RFC 8032 §5.1.6, step 5: [S = (r + k*s) mod L])
    — independent of how an optimized implementation computes it
    (Barrett-style limb chains, Montgomery, schoolbook).

    NOT an axiom: concrete Definition, reduces by [vm_compute] on any
    concrete input.  A richer companion module
    [Bedrock.End2End.Ed25519.ScalarMuladdVerified] re-exports the same
    definition under the long-form name [scalar_muladd_gallina],
    provides a Barrett-style concrete-equals-abstract proof, and
    exposes boundedness lemmas. *)
Definition scalar_muladd_spec (r k a : list Byte.byte) : list Byte.byte :=
  let r_z : Z := le_combine r in
  let k_z : Z := le_combine k in
  let a_z : Z := le_combine a in
  let s_z : Z := (r_z + k_z * a_z) mod L_curve_order in
  le_split 32 s_z.

Lemma scalar_muladd_output_32 :
  forall r k a, length (scalar_muladd_spec r k a) = 32%nat.
Proof.
  intros r k a. cbv [scalar_muladd_spec].
  apply length_le_split.
Qed.

Definition spec_of_scalar_muladd (functions : env) : Prop :=
  forall (t : trace) (m : mem) (l : locals)
         (out_ptr r_ptr k_ptr a_ptr : word.rep)
         (out_init r_bytes k_bytes a_bytes : list Byte.byte)
         (R : mem -> Prop)
         (post : trace -> mem -> list word.rep -> Prop),
    length out_init = 32%nat ->
    length r_bytes = 32%nat ->
    length k_bytes = 32%nat ->
    length a_bytes = 32%nat ->
    (sepclause_of_map (out_init$@out_ptr) ⋆
     sepclause_of_map (r_bytes$@r_ptr) ⋆
     sepclause_of_map (k_bytes$@k_ptr) ⋆
     sepclause_of_map (a_bytes$@a_ptr) ⋆ R)%sep m ->
    (forall m' : mem,
       (sepclause_of_map ((scalar_muladd_spec r_bytes k_bytes a_bytes)$@out_ptr) ⋆
        sepclause_of_map (r_bytes$@r_ptr) ⋆
        sepclause_of_map (k_bytes$@k_ptr) ⋆
        sepclause_of_map (a_bytes$@a_ptr) ⋆ R)%sep m' ->
       post t m' nil) ->
    WeakestPrecondition.call functions "scalar_muladd" t m
      (out_ptr :: r_ptr :: k_ptr :: a_ptr :: nil) post.

Definition callee_post_scalar_muladd_compatible
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall rs1 r_bytes k_bytes a_bytes (out_var : String.string),
    callee_post "scalar_muladd" []
      {| loc_var := out_var; loc_type := TBytes 32 |}
      rs1
      (rs_set_tower_ed rs1 out_var
         (exist_tval_ed (TBytes 32)
            (VBytes 32 (scalar_muladd_spec r_bytes k_bytes a_bytes)))).

Lemma post_state_refine_via_scalar_muladd :
  forall rs1 (l : locals) (m m' : mem) R
         (out_ptr r_ptr k_ptr a_ptr : word.rep)
         (r_bytes k_bytes a_bytes : list Byte.byte)
         (out_var : String.string),
    rs_tower_ed rs1 = [] ->
    state_refine_ed rs1 l m R ->
    map.get l out_var = Some out_ptr ->
    (sepclause_of_map ((scalar_muladd_spec r_bytes k_bytes a_bytes)$@out_ptr) ⋆
     sepclause_of_map (r_bytes$@r_ptr) ⋆
     sepclause_of_map (k_bytes$@k_ptr) ⋆
     sepclause_of_map (a_bytes$@a_ptr) ⋆ R)%sep m' ->
    state_refine_ed
      (rs_set_tower_ed rs1 out_var
         (exist_tval_ed (TBytes 32)
            (VBytes 32 (scalar_muladd_spec r_bytes k_bytes a_bytes))))
      l m'
      (fun mm => (sepclause_of_map (r_bytes$@r_ptr) ⋆
                  sepclause_of_map (k_bytes$@k_ptr) ⋆
                  sepclause_of_map (a_bytes$@a_ptr) ⋆ R)%sep mm).
Proof.
  intros rs1 l m m' R out_ptr r_ptr k_ptr a_ptr r_bytes k_bytes a_bytes out_var
         Htower_empty Hrefine Hloc Hsep'.
  unfold state_refine_ed; split.
  - unfold rs_set_tower_ed; cbn.
    rewrite Htower_empty; cbn.
    exists out_ptr; split; [exact Hloc |].
    cbn. unfold bytes_at.
    match goal with
    | |- (?P ⋆ (fun m => ?Q m))%sep ?z => change ((P ⋆ Q)%sep z)
    end; ecancel_assumption_impl.
  - intros x v Hgs.
    unfold rs_set_tower_ed in Hgs; cbn in Hgs.
    destruct Hrefine as [_ Hscalar].
    apply (Hscalar x v Hgs).
Qed.

(* ================================================================ *)
(* §3. ed25519_compress — 200 byte → 32 byte                         *)
(* ================================================================ *)

(** [ed25519_compress_spec] and [ed25519_compress_output_32] are now
    re-exported (no longer axioms) from
    [Bedrock.End2End.Ed25519.CompressVerified]. *)

Definition spec_of_ed25519_compress (functions : env) : Prop :=
  forall (t : trace) (m : mem) (l : locals)
         (out_ptr in_ptr : word.rep)
         (out_init xyzt_bytes : list Byte.byte)
         (R : mem -> Prop)
         (post : trace -> mem -> list word.rep -> Prop),
    length out_init = 32%nat ->
    length xyzt_bytes = 200%nat ->
    (sepclause_of_map (out_init$@out_ptr) ⋆
     sepclause_of_map (xyzt_bytes$@in_ptr) ⋆ R)%sep m ->
    (forall m' : mem,
       (sepclause_of_map ((ed25519_compress_spec xyzt_bytes)$@out_ptr) ⋆
        sepclause_of_map (xyzt_bytes$@in_ptr) ⋆ R)%sep m' ->
       post t m' nil) ->
    WeakestPrecondition.call functions "ed25519_compress" t m
      (out_ptr :: in_ptr :: nil) post.

Definition callee_post_ed25519_compress_compatible
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall rs1 xyzt_bytes (out_var : String.string),
    callee_post "ed25519_compress" []
      {| loc_var := out_var; loc_type := TBytes 32 |}
      rs1
      (rs_set_tower_ed rs1 out_var
         (exist_tval_ed (TBytes 32)
            (VBytes 32 (ed25519_compress_spec xyzt_bytes)))).

Lemma post_state_refine_via_ed25519_compress :
  forall rs1 (l : locals) (m m' : mem) R
         (out_ptr in_ptr : word.rep)
         (xyzt_bytes : list Byte.byte)
         (out_var : String.string),
    rs_tower_ed rs1 = [] ->
    state_refine_ed rs1 l m R ->
    map.get l out_var = Some out_ptr ->
    (sepclause_of_map ((ed25519_compress_spec xyzt_bytes)$@out_ptr) ⋆
     sepclause_of_map (xyzt_bytes$@in_ptr) ⋆ R)%sep m' ->
    state_refine_ed
      (rs_set_tower_ed rs1 out_var
         (exist_tval_ed (TBytes 32)
            (VBytes 32 (ed25519_compress_spec xyzt_bytes))))
      l m'
      (fun mm => (sepclause_of_map (xyzt_bytes$@in_ptr) ⋆ R)%sep mm).
Proof.
  intros rs1 l m m' R out_ptr in_ptr xyzt_bytes out_var
         Htower_empty Hrefine Hloc Hsep'.
  unfold state_refine_ed; split.
  - unfold rs_set_tower_ed; cbn.
    rewrite Htower_empty; cbn.
    exists out_ptr; split; [exact Hloc |].
    cbn. unfold bytes_at.
    match goal with
    | |- (?P ⋆ (fun m => ?Q m))%sep ?z => change ((P ⋆ Q)%sep z)
    end; ecancel_assumption_impl.
  - intros x v Hgs.
    unfold rs_set_tower_ed in Hgs; cbn in Hgs.
    destruct Hrefine as [_ Hscalar].
    apply (Hscalar x v Hgs).
Qed.

(* ================================================================ *)
(* §4. ed25519_scalarmult_base — 32 byte scalar → 200 byte XYZT      *)
(* ================================================================ *)

(** [ed25519_scalarmult_base_spec] and
    [ed25519_scalarmult_base_output_200] are now re-exported (no
    longer axioms) from
    [Bedrock.End2End.Ed25519.ScalarmultBaseVerified]. *)

Definition spec_of_ed25519_scalarmult_base_bridge (functions : env) : Prop :=
  forall (t : trace) (m : mem) (l : locals)
         (out_ptr scalar_ptr : word.rep)
         (out_init scalar_bytes : list Byte.byte)
         (R : mem -> Prop)
         (post : trace -> mem -> list word.rep -> Prop),
    length out_init = 200%nat ->
    length scalar_bytes = 32%nat ->
    (sepclause_of_map (out_init$@out_ptr) ⋆
     sepclause_of_map (scalar_bytes$@scalar_ptr) ⋆ R)%sep m ->
    (forall m' : mem,
       (sepclause_of_map ((ed25519_scalarmult_base_spec scalar_bytes)$@out_ptr) ⋆
        sepclause_of_map (scalar_bytes$@scalar_ptr) ⋆ R)%sep m' ->
       post t m' nil) ->
    WeakestPrecondition.call functions "ed25519_scalarmult_base" t m
      (out_ptr :: scalar_ptr :: nil) post.

Definition callee_post_ed25519_scalarmult_base_compatible
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall rs1 scalar_bytes (out_var : String.string),
    callee_post "ed25519_scalarmult_base" []
      {| loc_var := out_var; loc_type := TBytes 200 |}
      rs1
      (rs_set_tower_ed rs1 out_var
         (exist_tval_ed (TBytes 200)
            (VBytes 200 (ed25519_scalarmult_base_spec scalar_bytes)))).

Lemma post_state_refine_via_ed25519_scalarmult_base :
  forall rs1 (l : locals) (m m' : mem) R
         (out_ptr scalar_ptr : word.rep)
         (scalar_bytes : list Byte.byte)
         (out_var : String.string),
    rs_tower_ed rs1 = [] ->
    state_refine_ed rs1 l m R ->
    map.get l out_var = Some out_ptr ->
    (sepclause_of_map ((ed25519_scalarmult_base_spec scalar_bytes)$@out_ptr) ⋆
     sepclause_of_map (scalar_bytes$@scalar_ptr) ⋆ R)%sep m' ->
    state_refine_ed
      (rs_set_tower_ed rs1 out_var
         (exist_tval_ed (TBytes 200)
            (VBytes 200 (ed25519_scalarmult_base_spec scalar_bytes))))
      l m'
      (fun mm => (sepclause_of_map (scalar_bytes$@scalar_ptr) ⋆ R)%sep mm).
Proof.
  intros rs1 l m m' R out_ptr scalar_ptr scalar_bytes out_var
         Htower_empty Hrefine Hloc Hsep'.
  unfold state_refine_ed; split.
  - unfold rs_set_tower_ed; cbn.
    rewrite Htower_empty; cbn.
    exists out_ptr; split; [exact Hloc |].
    cbn. unfold bytes_at.
    match goal with
    | |- (?P ⋆ (fun m => ?Q m))%sep ?z => change ((P ⋆ Q)%sep z)
    end; ecancel_assumption_impl.
  - intros x v Hgs.
    unfold rs_set_tower_ed in Hgs; cbn in Hgs.
    destruct Hrefine as [_ Hscalar].
    apply (Hscalar x v Hgs).
Qed.

(* ================================================================ *)
(* §5. Concrete bridges (Qed compositions)                           *)
(* ================================================================ *)

Theorem bridge_scalar_reduce_concrete :
  forall (functions : env),
    spec_of_scalar_reduce functions ->
    forall (callee_post : String.string -> list located_ed -> located_ed ->
                          rust_state_ed -> rust_state_ed -> Prop),
    callee_post_scalar_reduce_compatible callee_post ->
    forall (t : trace) (m : mem) (l : locals)
           (rs1 : rust_state_ed) (args : list word.rep)
           (post : trace -> mem -> list word.rep -> Prop)
           (R : mem -> Prop)
           (out_ptr in_ptr : word.rep)
           (out_init in_bytes : list Byte.byte)
           (out_var : String.string),
      args = [out_ptr; in_ptr] ->
      length out_init = 32%nat ->
      length in_bytes = 64%nat ->
      (sepclause_of_map (out_init$@out_ptr) ⋆
       sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m ->
      rs_tower_ed rs1 = [] ->
      state_refine_ed rs1 l m R ->
      map.get l out_var = Some out_ptr ->
      (forall rs2 m',
         rs2 = rs_set_tower_ed rs1 out_var
                 (exist_tval_ed (TBytes 32)
                    (VBytes 32 (scalar_reduce_spec in_bytes))) ->
         (sepclause_of_map ((scalar_reduce_spec in_bytes)$@out_ptr) ⋆
          sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep m' ->
         state_refine_ed rs2 l m'
           (fun mm => (sepclause_of_map (in_bytes$@in_ptr) ⋆ R)%sep mm) ->
         callee_post "scalar_reduce" []
           {| loc_var := out_var; loc_type := TBytes 32 |} rs1 rs2 ->
         post t m' nil) ->
      WeakestPrecondition.call functions "scalar_reduce" t m args post.
Proof.
  intros functions Hspec callee_post Hcompat t m l rs1 args post R
         out_ptr in_ptr out_init in_bytes out_var
         Hargs Hlen_out Hlen_in Hsep Htower_empty Hrefine Hloc Hcont.
  subst args.
  unfold spec_of_scalar_reduce in Hspec.
  specialize (Hspec t m l out_ptr in_ptr out_init in_bytes R post
                    Hlen_out Hlen_in Hsep).
  apply Hspec.
  intros m' Hsep'.
  remember (rs_set_tower_ed rs1 out_var
              (exist_tval_ed (TBytes 32) (VBytes 32 (scalar_reduce_spec in_bytes))))
    as rs2 eqn:Hrs2.
  apply (Hcont rs2 m' eq_refl Hsep').
  - rewrite Hrs2.
    eapply post_state_refine_via_scalar_reduce;
      [ exact Htower_empty | exact Hrefine | exact Hloc | exact Hsep' ].
  - rewrite Hrs2.
    apply (Hcompat rs1 in_bytes out_var).
Qed.

Theorem bridge_scalar_muladd_concrete :
  forall (functions : env),
    spec_of_scalar_muladd functions ->
    forall (callee_post : String.string -> list located_ed -> located_ed ->
                          rust_state_ed -> rust_state_ed -> Prop),
    callee_post_scalar_muladd_compatible callee_post ->
    forall (t : trace) (m : mem) (l : locals)
           (rs1 : rust_state_ed) (args : list word.rep)
           (post : trace -> mem -> list word.rep -> Prop)
           (R : mem -> Prop)
           (out_ptr r_ptr k_ptr a_ptr : word.rep)
           (out_init r_bytes k_bytes a_bytes : list Byte.byte)
           (out_var : String.string),
      args = [out_ptr; r_ptr; k_ptr; a_ptr] ->
      length out_init = 32%nat ->
      length r_bytes = 32%nat ->
      length k_bytes = 32%nat ->
      length a_bytes = 32%nat ->
      (sepclause_of_map (out_init$@out_ptr) ⋆
       sepclause_of_map (r_bytes$@r_ptr) ⋆
       sepclause_of_map (k_bytes$@k_ptr) ⋆
       sepclause_of_map (a_bytes$@a_ptr) ⋆ R)%sep m ->
      rs_tower_ed rs1 = [] ->
      state_refine_ed rs1 l m R ->
      map.get l out_var = Some out_ptr ->
      (forall rs2 m',
         rs2 = rs_set_tower_ed rs1 out_var
                 (exist_tval_ed (TBytes 32)
                    (VBytes 32 (scalar_muladd_spec r_bytes k_bytes a_bytes))) ->
         (sepclause_of_map
            ((scalar_muladd_spec r_bytes k_bytes a_bytes)$@out_ptr) ⋆
          sepclause_of_map (r_bytes$@r_ptr) ⋆
          sepclause_of_map (k_bytes$@k_ptr) ⋆
          sepclause_of_map (a_bytes$@a_ptr) ⋆ R)%sep m' ->
         state_refine_ed rs2 l m'
           (fun mm => (sepclause_of_map (r_bytes$@r_ptr) ⋆
                       sepclause_of_map (k_bytes$@k_ptr) ⋆
                       sepclause_of_map (a_bytes$@a_ptr) ⋆ R)%sep mm) ->
         callee_post "scalar_muladd" []
           {| loc_var := out_var; loc_type := TBytes 32 |} rs1 rs2 ->
         post t m' nil) ->
      WeakestPrecondition.call functions "scalar_muladd" t m args post.
Proof.
  intros functions Hspec callee_post Hcompat t m l rs1 args post R
         out_ptr r_ptr k_ptr a_ptr out_init r_bytes k_bytes a_bytes out_var
         Hargs Hlen_out Hlen_r Hlen_k Hlen_a Hsep Htower_empty Hrefine Hloc Hcont.
  subst args.
  unfold spec_of_scalar_muladd in Hspec.
  specialize (Hspec t m l out_ptr r_ptr k_ptr a_ptr
                    out_init r_bytes k_bytes a_bytes R post
                    Hlen_out Hlen_r Hlen_k Hlen_a Hsep).
  apply Hspec.
  intros m' Hsep'.
  remember (rs_set_tower_ed rs1 out_var
              (exist_tval_ed (TBytes 32)
                 (VBytes 32 (scalar_muladd_spec r_bytes k_bytes a_bytes))))
    as rs2 eqn:Hrs2.
  apply (Hcont rs2 m' eq_refl Hsep').
  - rewrite Hrs2.
    eapply post_state_refine_via_scalar_muladd;
      [ exact Htower_empty | exact Hrefine | exact Hloc | exact Hsep' ].
  - rewrite Hrs2.
    apply (Hcompat rs1 r_bytes k_bytes a_bytes out_var).
Qed.

Theorem bridge_ed25519_compress_concrete :
  forall (functions : env),
    spec_of_ed25519_compress functions ->
    forall (callee_post : String.string -> list located_ed -> located_ed ->
                          rust_state_ed -> rust_state_ed -> Prop),
    callee_post_ed25519_compress_compatible callee_post ->
    forall (t : trace) (m : mem) (l : locals)
           (rs1 : rust_state_ed) (args : list word.rep)
           (post : trace -> mem -> list word.rep -> Prop)
           (R : mem -> Prop)
           (out_ptr in_ptr : word.rep)
           (out_init xyzt_bytes : list Byte.byte)
           (out_var : String.string),
      args = [out_ptr; in_ptr] ->
      length out_init = 32%nat ->
      length xyzt_bytes = 200%nat ->
      (sepclause_of_map (out_init$@out_ptr) ⋆
       sepclause_of_map (xyzt_bytes$@in_ptr) ⋆ R)%sep m ->
      rs_tower_ed rs1 = [] ->
      state_refine_ed rs1 l m R ->
      map.get l out_var = Some out_ptr ->
      (forall rs2 m',
         rs2 = rs_set_tower_ed rs1 out_var
                 (exist_tval_ed (TBytes 32)
                    (VBytes 32 (ed25519_compress_spec xyzt_bytes))) ->
         (sepclause_of_map ((ed25519_compress_spec xyzt_bytes)$@out_ptr) ⋆
          sepclause_of_map (xyzt_bytes$@in_ptr) ⋆ R)%sep m' ->
         state_refine_ed rs2 l m'
           (fun mm => (sepclause_of_map (xyzt_bytes$@in_ptr) ⋆ R)%sep mm) ->
         callee_post "ed25519_compress" []
           {| loc_var := out_var; loc_type := TBytes 32 |} rs1 rs2 ->
         post t m' nil) ->
      WeakestPrecondition.call functions "ed25519_compress" t m args post.
Proof.
  intros functions Hspec callee_post Hcompat t m l rs1 args post R
         out_ptr in_ptr out_init xyzt_bytes out_var
         Hargs Hlen_out Hlen_in Hsep Htower_empty Hrefine Hloc Hcont.
  subst args.
  unfold spec_of_ed25519_compress in Hspec.
  specialize (Hspec t m l out_ptr in_ptr out_init xyzt_bytes R post
                    Hlen_out Hlen_in Hsep).
  apply Hspec.
  intros m' Hsep'.
  remember (rs_set_tower_ed rs1 out_var
              (exist_tval_ed (TBytes 32)
                 (VBytes 32 (ed25519_compress_spec xyzt_bytes))))
    as rs2 eqn:Hrs2.
  apply (Hcont rs2 m' eq_refl Hsep').
  - rewrite Hrs2.
    eapply post_state_refine_via_ed25519_compress;
      [ exact Htower_empty | exact Hrefine | exact Hloc | exact Hsep' ].
  - rewrite Hrs2.
    apply (Hcompat rs1 xyzt_bytes out_var).
Qed.

Theorem bridge_ed25519_scalarmult_base_concrete :
  forall (functions : env),
    spec_of_ed25519_scalarmult_base_bridge functions ->
    forall (callee_post : String.string -> list located_ed -> located_ed ->
                          rust_state_ed -> rust_state_ed -> Prop),
    callee_post_ed25519_scalarmult_base_compatible callee_post ->
    forall (t : trace) (m : mem) (l : locals)
           (rs1 : rust_state_ed) (args : list word.rep)
           (post : trace -> mem -> list word.rep -> Prop)
           (R : mem -> Prop)
           (out_ptr scalar_ptr : word.rep)
           (out_init scalar_bytes : list Byte.byte)
           (out_var : String.string),
      args = [out_ptr; scalar_ptr] ->
      length out_init = 200%nat ->
      length scalar_bytes = 32%nat ->
      (sepclause_of_map (out_init$@out_ptr) ⋆
       sepclause_of_map (scalar_bytes$@scalar_ptr) ⋆ R)%sep m ->
      rs_tower_ed rs1 = [] ->
      state_refine_ed rs1 l m R ->
      map.get l out_var = Some out_ptr ->
      (forall rs2 m',
         rs2 = rs_set_tower_ed rs1 out_var
                 (exist_tval_ed (TBytes 200)
                    (VBytes 200 (ed25519_scalarmult_base_spec scalar_bytes))) ->
         (sepclause_of_map
            ((ed25519_scalarmult_base_spec scalar_bytes)$@out_ptr) ⋆
          sepclause_of_map (scalar_bytes$@scalar_ptr) ⋆ R)%sep m' ->
         state_refine_ed rs2 l m'
           (fun mm => (sepclause_of_map (scalar_bytes$@scalar_ptr) ⋆ R)%sep mm) ->
         callee_post "ed25519_scalarmult_base" []
           {| loc_var := out_var; loc_type := TBytes 200 |} rs1 rs2 ->
         post t m' nil) ->
      WeakestPrecondition.call functions "ed25519_scalarmult_base" t m args post.
Proof.
  intros functions Hspec callee_post Hcompat t m l rs1 args post R
         out_ptr scalar_ptr out_init scalar_bytes out_var
         Hargs Hlen_out Hlen_in Hsep Htower_empty Hrefine Hloc Hcont.
  subst args.
  unfold spec_of_ed25519_scalarmult_base_bridge in Hspec.
  specialize (Hspec t m l out_ptr scalar_ptr out_init scalar_bytes R post
                    Hlen_out Hlen_in Hsep).
  apply Hspec.
  intros m' Hsep'.
  remember (rs_set_tower_ed rs1 out_var
              (exist_tval_ed (TBytes 200)
                 (VBytes 200 (ed25519_scalarmult_base_spec scalar_bytes))))
    as rs2 eqn:Hrs2.
  apply (Hcont rs2 m' eq_refl Hsep').
  - rewrite Hrs2.
    eapply post_state_refine_via_ed25519_scalarmult_base;
      [ exact Htower_empty | exact Hrefine | exact Hloc | exact Hsep' ].
  - rewrite Hrs2.
    apply (Hcompat rs1 scalar_bytes out_var).
Qed.

(** All four remaining bridges are now Qed-clean.  Combined with
    [SHA512Bridge.bridge_sha512_64_concrete], the full set of 5
    Signal-wiring bridges is structurally complete with only
    abstract function Parameters as axioms. *)
