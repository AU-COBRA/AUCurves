(** * Fe25519BoundLeafProducers — Phase 0e step 2.
 *
 *  Real [Hexec_b] inhabitants for the [fe25519_sqr] / [fe25519_mul] /
 *  [fe25519_copy] leaves consumed by [Fe25519InvertBoundInstantiation.v].
 *
 *  This file is now a thin set of instantiations of the parametric
 *  [oracle_unop_producer] / [oracle_binop_producer] templates from
 *  [OracleLeafTemplate.v].  The encoder, state helpers, framing,
 *  determinism, and the [rexec_call]-then-collapse pattern all live
 *  in the template; this file just plugs in the concrete [fname] +
 *  algebraic spec for each leaf.
 *
 *  Postcondition algebra (target field-element):
 *    sqr  — [F.pow x 2 = F.mul x x]
 *    mul  — [F.mul xa xb]
 *    copy — [x]
 *
 *  STATUS
 *  ======
 *  3 producer lemmas: [sqr_producer_bound], [mul_producer_bound],
 *  [copy_producer_bound] — all Qed modulo the 2 named encoder
 *  [Admitted]s from [OracleLeafTemplate.v]
 *  ([encode_target_decodes], [encode_target_bounded]).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBody.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBoundInstantiation.
Require Import Bedrock.End2End.Ed25519.OracleLeafTemplate.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation Hexec_b :=
  (rust_exec_ed callee_post_bound callee_post_n_bound function_table_bound).

(* ================================================================ *)
(* §1. Leaf producers via the parametric templates                   *)
(* ================================================================ *)

(** Producer for [fe25519_sqr] : [F.pow x 2]. *)
Lemma sqr_producer_bound :
  forall (rs1 : rust_state_ed) (dest src : located_ed) (x : F p),
    dest.(loc_type) = TFp25519 ->
    src.(loc_type) = TFp25519 ->
    dest.(loc_var) <> src.(loc_var) ->
    Fp25519_holds_bound rs1 src.(loc_var) x ->
    exists rs2 : rust_state_ed,
      Hexec_b (REdCall "fe25519_sqr" dest [src]) rs1 rs2 /\
      Fp25519_holds_bound rs2 dest.(loc_var) (F.pow x 2) /\
      (forall y v, y <> dest.(loc_var) ->
                   Fp25519_holds_bound rs1 y v ->
                   Fp25519_holds_bound rs2 y v).
Proof.
  apply (oracle_unop_producer "fe25519_sqr" (fun x => F.pow x 2)).
  intros args dst rs1 rs2 src ->. cbn [callee_post_bound]. exact (fun H => H).
Qed.

(** Producer for [fe25519_mul] : [F.mul xa xb]. *)
Lemma mul_producer_bound :
  forall (rs1 : rust_state_ed) (dest a b : located_ed) (xa xb : F p),
    dest.(loc_type) = TFp25519 ->
    a.(loc_type) = TFp25519 ->
    b.(loc_type) = TFp25519 ->
    dest.(loc_var) <> a.(loc_var) ->
    dest.(loc_var) <> b.(loc_var) ->
    Fp25519_holds_bound rs1 a.(loc_var) xa ->
    Fp25519_holds_bound rs1 b.(loc_var) xb ->
    exists rs2 : rust_state_ed,
      Hexec_b (REdCall "fe25519_mul" dest [a; b]) rs1 rs2 /\
      Fp25519_holds_bound rs2 dest.(loc_var) (F.mul xa xb) /\
      (forall y v, y <> dest.(loc_var) ->
                   Fp25519_holds_bound rs1 y v ->
                   Fp25519_holds_bound rs2 y v).
Proof.
  apply (oracle_binop_producer "fe25519_mul" F.mul).
  intros args dst rs1 rs2 a b ->. cbn [callee_post_bound]. exact (fun H => H).
Qed.

(** Producer for [fe25519_copy] : identity [x]. *)
Lemma copy_producer_bound :
  forall (rs1 : rust_state_ed) (dest src : located_ed) (x : F p),
    dest.(loc_type) = TFp25519 ->
    src.(loc_type) = TFp25519 ->
    dest.(loc_var) <> src.(loc_var) ->
    Fp25519_holds_bound rs1 src.(loc_var) x ->
    exists rs2 : rust_state_ed,
      Hexec_b (REdCall "fe25519_copy" dest [src]) rs1 rs2 /\
      Fp25519_holds_bound rs2 dest.(loc_var) x /\
      (forall y v, y <> dest.(loc_var) ->
                   Fp25519_holds_bound rs1 y v ->
                   Fp25519_holds_bound rs2 y v).
Proof.
  apply (oracle_unop_producer "fe25519_copy" (fun x => x)).
  intros args dst rs1 rs2 src ->. cbn [callee_post_bound]. exact (fun H => H).
Qed.

(* ================================================================ *)
(* §2. Print Assumptions                                             *)
(* ================================================================ *)

Print Assumptions sqr_producer_bound.
Print Assumptions mul_producer_bound.
Print Assumptions copy_producer_bound.
