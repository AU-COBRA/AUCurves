(* BW6-761 instantiation of CurveSpecsEquivalence:
   proves that the Gallina spec of BW6-761 point addition
   is equivalent to fiat-crypto's Projective.add.

   Curve: y^2 = x^3 - 1 over a 761-bit prime field. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Theory.WordByWordMontgomery.CurveSpecsEquivalence.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Require Import Theory.Fields.FieldsUtil.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Crypto.Algebra.Hierarchy.
From Coqprime Require Import GZnZ.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bw6_761_prime_certif.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Section BW6_761_Equiv.

  (* BW6-761 parameters *)
  Local Definition m := bw6_761_modulus.
  Local Definition bw := 64.
  Local Definition n := 12%nat.
  Local Definition a := 0%Z.
  Local Definition b := Eval vm_compute in (m - 1)%Z.   (* b = -1 mod m *)
  Local Definition three_b := Eval vm_compute in (m - 3)%Z. (* 3b = -3 mod m *)

  Local Notation r := (MontgomeryRingTheory.r bw).
  Local Notation r' := (WordByWordMontgomery.r' m bw).
  Local Notation m' := (@WordByWordMontgomery.m' m bw).

  (* Parameter correctness proofs *)
  Lemma a_small : a = a mod m. Proof. vm_compute. reflexivity. Qed.
  Lemma b_small : b = b mod m. Proof. vm_compute. reflexivity. Qed.
  Lemma three_b_small : three_b = three_b mod m. Proof. vm_compute. reflexivity. Qed.
  Lemma three_b_correct : three_b = b + b + b.
  Proof. vm_compute. reflexivity. Qed.

  Lemma r'_correct : (r * r') mod m = 1. Proof. vm_compute. reflexivity. Qed.
  Lemma m'_correct : (m * m') mod r = (-1) mod r. Proof. vm_compute. reflexivity. Qed.
  Lemma bw_big : 0 < bw. Proof. cbv. lia. Qed.
  Lemma n_nz : n <> 0%nat. Proof. cbv. discriminate. Qed.
  Lemma m_small : m < r ^ (Z.of_nat n). Proof. vm_compute. reflexivity. Qed.
  Lemma m_big : 1 < m. Proof. vm_compute. lia. Qed.
  Lemma twenty1_small : 21 < m. Proof. vm_compute. lia. Qed.

  Lemma m_prime : prime m.
  Proof. exact prime_bw6_761. Qed.

  (* Discriminant: 4a^3 + 27b^2 = 27*(-1)^2 = 27 != 0 mod m *)
  Local Notation fp_a := (mkznz m a a_small).
  Local Notation fp_b := (mkznz m b b_small).
  Local Notation four := (one m +m one m +m one m +m one m)%Z.
  Local Notation twenty7 := (four *m four +m four +m four +m one m +m one m +m one m)%Z.

  Lemma discriminant_nonzero :
    id ((four *m fp_a *m fp_a *m fp_a +m twenty7 *m fp_b *m fp_b) <> zero m).
  Proof.
    unfold id. intro H. inversion H.
    vm_compute in H0. discriminate.
  Qed.

End BW6_761_Equiv.
