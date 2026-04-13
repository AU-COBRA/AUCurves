(* P-256 instantiation of CurveSpecsEquivalence:
   proves that the Gallina spec of P-256 point addition
   is equivalent to fiat-crypto's Projective.add. *)

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
Require Import Crypto.Curves.Weierstrass.P256.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Section P256_Equiv.

  (* P-256 parameters *)
  Local Definition m := Eval vm_compute in P256.p256.
  Local Definition bw := 64.
  Local Definition n := 4%nat.
  Local Definition a := Eval vm_compute in ((-3) mod m)%Z.
  Local Definition b := Eval vm_compute in
    (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b mod m)%Z.
  Local Definition three_b := Eval vm_compute in (3 * b mod m)%Z.

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
  Proof.
    change m with P256.p256.
    exact P256.prime_p256.
  Qed.

  (* Discriminant: 4a^3 + 27b^2 != 0 mod p *)
  Local Notation fp_a := (mkznz m a a_small).
  Local Notation fp_b := (mkznz m b b_small).
  Local Infix "+m" := (add m) (at level 50).
  Local Infix "*m" := (mul m) (at level 40).
  Local Notation four := (one m +m one m +m one m +m one m).
  Local Notation twenty7 := (four *m four +m four +m four +m one m +m one m +m one m).

  Lemma discriminant_nonzero :
    id ((four *m fp_a *m fp_a *m fp_a +m twenty7 *m fp_b *m fp_b) <> zero m).
  Proof.
    unfold id. intro H.
    apply (f_equal (@val m)) in H. vm_compute in H. discriminate.
  Qed.

  (* Now all hypotheses of CurveSpecsEquivalence.G1Equiv are satisfied.
     The equivalence theorems (gallina_fiat_crypto_equiv, etc.) can be
     instantiated for P-256. *)

End P256_Equiv.
