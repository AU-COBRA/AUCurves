(** * Montgomery decoding of the BLS12-381 Frobenius constant limbs.

    For each limb list stored by a constant loader of [BLS12_Pairing.v],
    the fiat-crypto field evaluation of the stored words ([Field.feval] of
    [bls12_frep], i.e. Positional.eval of from_montgomerymod) equals
    [BLS12_381_Frob.mont_to_F] of the limbs.  One lemma per distinct limb
    list, proved by vm_compute (from_montgomerymod costs about 6 s in the
    VM, so the loader proofs reuse these lemmas instead of recomputing). *)

From Stdlib Require Import ZArith.ZArith Lists.List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FrobConstants.

Local Open Scope Z_scope.

Module BLS12_381_FrobDecode.
  Import BLS12_381_Frob.

  Local Notation feval := (@Field.feval _ _ _ _ _ bls12_frep).

  Lemma decode_zero :
    feval (List.map word.of_Z limbs_zero) = mont_to_F limbs_zero.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma decode_gamma1_p2 :
    feval (List.map word.of_Z limbs_gamma1_p2) = mont_to_F limbs_gamma1_p2.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma decode_gamma2_p2 :
    feval (List.map word.of_Z limbs_gamma2_p2) = mont_to_F limbs_gamma2_p2.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma decode_w_frob_p2_c1 :
    feval (List.map word.of_Z limbs_w_frob_p2_c1) = mont_to_F limbs_w_frob_p2_c1.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma decode_gamma1_im :
    feval (List.map word.of_Z limbs_gamma1_im) = mont_to_F limbs_gamma1_im.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma decode_gamma2 :
    feval (List.map word.of_Z limbs_gamma2) = mont_to_F limbs_gamma2.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma decode_w_frob_c1_re :
    feval (List.map word.of_Z limbs_w_frob_c1_re) = mont_to_F limbs_w_frob_c1_re.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma decode_w_frob_c1_im :
    feval (List.map word.of_Z limbs_w_frob_c1_im) = mont_to_F limbs_w_frob_c1_im.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

End BLS12_381_FrobDecode.
