(* Generic lemmas proving addition chains equal scalar multiplication in a field.
   Used across multiple curve Fp2 proof files. *)

Require Import ZArith.
Require Import Coq.setoid_ring.Field.

Section SmallZMul.

  Context {F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv}
          {std_field: @field_theory F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv (@eq F)}.

  Add Field F : std_field.

  (* Notation for readability *)
  Local Notation "0" := Fzero.
  Local Notation "1" := Fone.
  Local Notation "x + y" := (Fadd x y).
  Local Notation "x * y" := (Fmul x y).
  Local Notation "x - y" := (Fsub x y).
  Local Notation "- x" := (Fopp x).

  (* Helper to build field constants *)
  Local Definition c2 := 1 + 1.
  Local Definition c3 := c2 + 1.
  Local Definition c4 := c2 + c2.
  Local Definition c5 := c4 + 1.
  Local Definition c6 := c3 + c3.
  Local Definition c7 := c6 + 1.
  Local Definition c8 := c4 + c4.
  Local Definition c9 := c8 + 1.
  Local Definition c10 := c5 + c5.
  Local Definition c11 := c10 + 1.
  Local Definition c12 := c6 + c6.
  Local Definition c13 := c12 + 1.

  Lemma mul_by_2 x : x + x = c2 * x.
  Proof. unfold c2. field. Qed.

  Lemma mul_by_3 x : (x + x) + x = c3 * x.
  Proof. unfold c3, c2. field. Qed.

  Lemma mul_by_4 x : (x + x) + (x + x) = c4 * x.
  Proof. unfold c4, c2. field. Qed.

  Lemma mul_by_5 x : ((x + x) + (x + x)) + x = c5 * x.
  Proof. unfold c5, c4, c2. field. Qed.

  Lemma mul_by_6 x : ((x + x) + x) + ((x + x) + x) = c6 * x.
  Proof. unfold c6, c3, c2. field. Qed.

  Lemma mul_by_7 x : (((x + x) + x) + ((x + x) + x)) + x = c7 * x.
  Proof. unfold c7, c6, c3, c2. field. Qed.

  Lemma mul_by_8 x : ((x + x) + (x + x)) + ((x + x) + (x + x)) = c8 * x.
  Proof. unfold c8, c4, c2. field. Qed.

  Lemma mul_by_9 x : (((x + x) + (x + x)) + ((x + x) + (x + x))) + x = c9 * x.
  Proof. unfold c9, c8, c4, c2. field. Qed.

  Lemma mul_by_10 x : (((x + x) + (x + x)) + x) + (((x + x) + (x + x)) + x) = c10 * x.
  Proof. unfold c10, c5, c4, c2. field. Qed.

  Lemma mul_by_11 x : ((((x + x) + (x + x)) + x) + (((x + x) + (x + x)) + x)) + x = c11 * x.
  Proof. unfold c11, c10, c5, c4, c2. field. Qed.

  Lemma mul_by_12 x : (((x + x) + x) + ((x + x) + x)) + (((x + x) + x) + ((x + x) + x)) = c12 * x.
  Proof. unfold c12, c6, c3, c2. field. Qed.

  Lemma mul_by_13 x : ((((x + x) + x) + ((x + x) + x)) + (((x + x) + x) + ((x + x) + x))) + x = c13 * x.
  Proof. unfold c13, c12, c6, c3, c2. field. Qed.

  (* Negation distributes into scalar multiplication *)
  Lemma opp_mul n x : -(n * x) = (-n) * x.
  Proof. field. Qed.

  (* Subtraction as addition of negation *)
  Lemma sub_as_add_opp a b : a - b = a + (-b).
  Proof. field. Qed.

  (* Subtraction with a scalar multiple *)
  Lemma sub_mul_opp a n b : a - (n * b) = a + ((-n) * b).
  Proof. field. Qed.

End SmallZMul.
