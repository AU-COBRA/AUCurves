(* secp256k1 instantiation of CurveSpecsEquivalence:
   proves that the Gallina spec of secp256k1 point addition
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
Require Import Bedrock.Curve.Secp256k1_prime_certif.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Section Secp256k1_Equiv.

  (* secp256k1 parameters *)
  Local Definition m := Eval vm_compute in (2^256 - 2^32 - 977)%Z.
  Local Definition bw := 64.
  Local Definition n := 4%nat.
  Local Definition a := 0%Z.
  Local Definition b := 7%Z.
  Local Definition three_b := 21%Z.

  Local Notation r := (MontgomeryRingTheory.r bw).
  (* r' = modinv(r, m) satisfying (r * r') mod m = 1 *)
  Local Definition r' :=
    97798581649299591516383885342152904135335272353249846763749256112567415731113%Z.
  (* m' = modinv(-m, r) satisfying (m * m') mod r = (-1) mod r *)
  Local Definition m' := 15580212934572586289%Z.

  (* Parameter correctness proofs *)
  Lemma a_small : a = a mod m. Proof. vm_compute. reflexivity. Qed.
  Lemma b_small : b = b mod m. Proof. vm_compute. reflexivity. Qed.
  Lemma three_b_small : three_b = three_b mod m. Proof. vm_compute. reflexivity. Qed.
  Lemma three_b_correct : three_b = b + b + b.
  Proof. vm_compute. reflexivity. Qed.

  Lemma r'_correct : (r * r') mod m = 1. Proof. vm_compute. reflexivity. Qed.
  Lemma m'_correct : (m * m') mod r = (-1) mod r. Proof. vm_compute. reflexivity. Qed.
  Lemma bw_big : 0 < bw. Proof. unfold bw. lia. Qed.
  Lemma n_nz : n <> 0%nat. Proof. unfold n. discriminate. Qed.
  Lemma m_small : m < r ^ (Z.of_nat n). Proof. vm_compute. reflexivity. Qed.
  Lemma m_big : 1 < m. Proof. unfold m. lia. Qed.
  Lemma twenty1_small : 21 < m. Proof. unfold m. lia. Qed.

  Lemma m_prime : prime m.
  Proof.
    change m with secp256k1_modulus.
    exact prime_secp256k1.
  Qed.

  (* Discriminant: 4a^3 + 27b^2 != 0 mod p
     For secp256k1: 4*0^3 + 27*7^2 = 1323, which is nonzero mod p. *)
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

  (* All hypotheses of CurveSpecsEquivalence.G1Equiv are satisfied.
     The equivalence theorems (gallina_fiat_crypto_equiv, etc.) can be
     instantiated for secp256k1. *)

  (* Convenient aliases for the instantiated equivalence results *)
  Definition secp256k1_gallina_fiat_equiv :=
    gallina_fiat_crypto_equiv m bw n m' a b three_b
      a_small b_small three_b_small three_b_correct
      bw_big n_nz m_small m_big twenty1_small m_prime
      discriminant_nonzero.

  Definition secp256k1_gallina_fiat_equiv' :=
    gallina_fiat_crypto_equiv' m bw n m' a b three_b
      a_small b_small three_b_small three_b_correct
      bw_big n_nz m_small m_big twenty1_small m_prime
      discriminant_nonzero.

  Definition secp256k1_gallina_fiat_equiv'' :=
    gallina_fiat_crypto_equiv'' m bw n r' m' a b three_b
      a_small b_small three_b_small three_b_correct
      r'_correct m'_correct bw_big n_nz m_small m_big twenty1_small m_prime
      discriminant_nonzero.

End Secp256k1_Equiv.
