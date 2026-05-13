(** * Fe25519AddSubCorrect — functional correctness of [fe25519_add_body]
 *  and [fe25519_sub_body].
 *
 *  Companion to [Fe25519AddSubBody.v].  Mirrors the section-parameterised
 *  pattern used by [Fe25519InvertCorrect.fe25519_invert_correct]:
 *  abstract over the [Fp25519_holds] slot predicate plus a per-call
 *  oracle hypothesis on the lower-level primitive, then derive
 *  algebraic correctness of the wrapped body.
 *
 *  Status
 *  ======
 *  - [fe25519_add_body_correct] :  Qed.
 *  - [fe25519_sub_body_correct] :  Qed.
 *
 *  Both proofs are one-step delegations from the body's inner
 *  [REdCall "fe25519_add_prim"] (resp. ["fe25519_sub_prim"]) to the
 *  primitive's section-hypothesis spec.  No new global axioms.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519AddSubBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + leaf      *)
(*     algebra hypotheses on the [_prim] primitive ops.              *)
(* ================================================================ *)

Section Fe25519AddSubCorrect.

  Variable Fp25519_holds : rust_state_ed -> String.string -> F p -> Prop.

  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec :=
    (rust_exec_ed callee_post callee_post_n function_table).

  (** Frame: non-[exclude] variables keep their Fp values. *)
  Definition fp_frame (rs1 rs2 : rust_state_ed) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude -> Fp25519_holds rs1 y v -> Fp25519_holds rs2 y v.

  (** Primitive [fe25519_add_prim]: 5-limb radix-2^51 addition.  At
      the surface of this scaffold the primitive's behaviour is
      handed in as a hypothesis (same shape as
      [Fe25519InvertCorrect.sqr_correct]).  Phase 0b will replace
      [fe25519_add_prim] with an inline AST that itself reduces to
      [F.add]; this hypothesis then becomes a derivable lemma about
      that inline AST. *)
  Hypothesis add_prim_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      b.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Fp25519_holds rs1 b.(loc_var) xb ->
      Hexec (REdCall "fe25519_add_prim" dest [a; b]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.add xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).

  (** Primitive [fe25519_sub_prim]: 5-limb radix-2^51 subtraction. *)
  Hypothesis sub_prim_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      b.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Fp25519_holds rs1 b.(loc_var) xb ->
      Hexec (REdCall "fe25519_sub_prim" dest [a; b]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.sub xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).

(* ================================================================ *)
(* §2. Headline theorems                                             *)
(* ================================================================ *)

  Theorem fe25519_add_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Fp25519_holds rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_add_body dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.add xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    cbn [fe25519_add_body] in Hexec_n.
    apply (add_prim_correct dest a_loc b_loc rs1 rs2 xa xb); assumption.
  Qed.

  Theorem fe25519_sub_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Fp25519_holds rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_sub_body dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.sub xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    cbn [fe25519_sub_body] in Hexec_n.
    apply (sub_prim_correct dest a_loc b_loc rs1 rs2 xa xb); assumption.
  Qed.

End Fe25519AddSubCorrect.

(** Sanity check: list assumptions of the headline theorems.  Inside
    the Section, the [Variable]/[Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_add_body_correct.
Print Assumptions fe25519_sub_body_correct.
