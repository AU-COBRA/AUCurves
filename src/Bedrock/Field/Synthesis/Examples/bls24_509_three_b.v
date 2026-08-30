(** * bls24_509_three_b — the 3b curve constant for BLS24-509, in
      Montgomery form, with the validity facts the G1 chain needs.

    Line-for-line the BN254 file [bn254_three_b.v] with the curve
    constant changed (b = 1 rather than 3) and the instances pointed
    at [bls24_509_Fp].  Everything else is curve-generic. *)

Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_Fp.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.ArrayUtil.
Require Import Bedrock.Field.Synthesis.Examples.ScalarsUtil.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope sep_scope.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Bedrock.Arithmetic.WordByWordMontgomeryUtil.
Require Import Crypto.Util.ZUtil.ModInv.

Section FromListF.

  Existing Instances
      Bitwidth64.BW64
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

  Local Notation F := (F M_pos).

  Existing Instance bls24_509_field_parameters.
  Existing Instance bls24_509_frep.

  (* BLS24-509 curve: y² = x³ + 1, so b = 1 and 3b = 3.
     b is the [curve_b] field of
     src/Bedrock/Field/PairingTheory/Curves/BLS24_509_params.v. *)
  Definition b := 1.
  Definition three_b := 3.
  Definition uw := (uweight 64).
  Definition n := felem_size_in_words.
  Definition three_b_list := Partition.partition uw n three_b.

  Definition r' := Z.modinv (2^64) M.
  Definition m' := Z.modinv (- M) (2^64).

  Definition three_b_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n M m' three_b_list).
  Definition three_b_words := List.map (@word.of_Z 64 BasicC64Semantics.word) three_b_mont.
  Definition wo := @word.of_Z 64 BasicC64Semantics.word 0.

  Lemma r'_correct : (2 ^ 64 * r' mod M = 1).
  Proof. auto. Qed.

  Lemma m'_correct : ((M * m') mod 2 ^ 64 = -1 mod 2 ^ 64).
  Proof.
      cbv [m'].
      assert (M = (-1) * (-M))%Z by auto.
      remember (ModInv.Z.modinv (- M) (2 ^ 64)) as x.
      rewrite H. subst x. rewrite <- Z.mul_assoc.
      rewrite Z.mul_mod.
      1: {
          pose proof (ModInv.Z.modinv_correct (- M) (2 ^ 64)).
          assert (0 < 2 ^ 64) by lia.
          specialize (H0 H1).
          assert (Z.gcd (Z.abs (-M)) (2 ^ 64) = 1) by auto.
          specialize (H0 H2).
          destruct H0.
          unfold M in *.
          rewrite H0. rewrite <- Z.mul_mod; try lia.
      }
      lia.
  Qed.

  Lemma M_small : (M < (2 ^ 64) ^ Z.of_nat (WordByWordMontgomery.n M 64)).
  Proof. reflexivity. Qed.

  Lemma bw_big : 0 < 64.
  Proof. reflexivity. Qed.

  Lemma M_big : 1 < M.
  Proof. reflexivity. Qed.

  Lemma n_nz : n <> 0%nat.
  Proof. cbv. congruence. Qed.

  Definition from_mont_correct := WordByWordMontgomery.from_montgomerymod_correct 64 n M r' m' r'_correct m'_correct bw_big M_big n_nz M_small.
  Definition to_mont_correct :=  WordByWordMontgomery.to_montgomerymod_correct 64 n M r' m' r'_correct m'_correct bw_big M_big n_nz M_small.

  Lemma unsigned_of_Z_valid : forall (l : list Z), WordByWordMontgomery.valid 64 n M l -> List.map word.unsigned (List.map (@word.of_Z 64 BasicC64Semantics.word) l) = l.
  Proof.
      intros.
      erewrite Util.map_unsigned_of_Z. eapply MaxBounds.map_word_wrap_bounded'.
      1: eapply BasicLemmas.ZRange.is_tighter_than_bool_Reflexive.
      eapply valid_max_bounds. eapply H.
  Qed.

  Lemma three_b_mont_eq : three_b_mont = (@WordByWordMontgomery.to_montgomerymod 64 n M m' three_b_list).
  Proof. vm_compute; auto. Qed.

  Lemma three_b_list_valid : WordByWordMontgomery.valid 64 n M three_b_list.
  Proof.
      split.
      1: {
          eapply WordByWordMontgomery.WordByWordMontgomery.small_m_enc; try lia; cbv [three_b]; try lia.
          cbv [n felem_size_in_words]. simpl; lia.
      }
      unfold three_b_list.
      erewrite <- WordByWordMontgomery.WordByWordMontgomery.m_enc_correct_montgomery; try lia; cbv [three_b M]; try (simpl; lia).
  Qed.

  Lemma three_b_mont_valid : WordByWordMontgomery.valid 64 n M three_b_mont.
  Proof.
      rewrite three_b_mont_eq.
      eapply to_mont_correct.
      eapply three_b_list_valid.
  Qed.

End FromListF.
