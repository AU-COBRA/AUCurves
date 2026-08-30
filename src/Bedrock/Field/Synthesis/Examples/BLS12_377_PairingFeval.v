(** * DSD pairing feval correctness for BLS12-377.
 *
 *  Imports pre-compiled bridge lemmas from BLS12_377_Fp12Feval.vo.
 *
 *  Unlike the BLS12-381 version, we do NOT bridge against Pairing.v
 *  (which hard-codes beta=-1). Instead we bridge against "spec" Fp12
 *  operations defined in BLS12_377_Fp12Feval that use Fp6.fp6_sqr
 *  (Chung-Hasan SQR3) where the bedrock2 model uses Fp6.fp6_mul x x.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Spec.BLS12Pairing.Fp6.
Require Import Spec.BLS12Pairing.Fp12.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_Fp12Feval.

Local Open Scope Z_scope.

(* ================================================================ *)
(** ** Generic DSD final exponentiation                              *)
(* ================================================================ *)

(** The DSD hard part parameterized by Fp12 operations.
    This allows proving the bridge by congruence without
    unfolding let-bindings (which would cause term explosion). *)
Section GenericDSD.
  Variable Fp12' : Type.
  Variable sq : Fp12' -> Fp12'.
  Variable ml : Fp12' -> Fp12' -> Fp12'.
  Variable conj : Fp12' -> Fp12'.
  Variable inv : Fp12' -> Fp12'.
  Variable frob : Fp12' -> Fp12'.
  Variable frob_p2 : Fp12' -> Fp12'.
  Variable pow_x_s : Fp12' -> Fp12'.
  Variable pow_x_hs : Fp12' -> Fp12'.

  Definition generic_final_exp_hard_dsd (f : Fp12') : Fp12' :=
    let t0 := sq f in
    let t1 := pow_x_hs t0 in
    let t2 := conj f in
    let t1 := ml t1 t2 in
    let t2 := pow_x_s t1 in
    let t1 := conj t1 in
    let t1 := ml t1 t2 in
    let t2 := pow_x_s t1 in
    let t1 := frob t1 in
    let t1 := ml t1 t2 in
    let result := ml f t0 in
    let t0 := pow_x_s t1 in
    let t2 := pow_x_s t0 in
    let t0 := frob_p2 t1 in
    let t1 := conj t1 in
    let t1 := ml t1 t2 in
    let t1 := ml t1 t0 in
    ml result t1.

  Definition generic_final_exp_dsd (f : Fp12') : Fp12' :=
    let f_conj := conj f in
    let f_inv := inv f in
    let result := ml f_conj f_inv in
    let result_p2 := frob_p2 result in
    let result' := ml result_p2 result in
    generic_final_exp_hard_dsd result'.

End GenericDSD.

(* ================================================================ *)
(** ** Congruence lemma for generic DSD                              *)
(* ================================================================ *)

Lemma generic_dsd_congr :
  forall (T : Type)
         (sq1 sq2 : T -> T) (ml1 ml2 : T -> T -> T)
         (conj1 conj2 : T -> T) (inv1 inv2 : T -> T)
         (frob1 frob2 : T -> T) (frob_p21 frob_p22 : T -> T)
         (pow_x_s1 pow_x_s2 : T -> T) (pow_x_hs1 pow_x_hs2 : T -> T),
    (forall x, sq1 x = sq2 x) ->
    (forall x y, ml1 x y = ml2 x y) ->
    (forall x, conj1 x = conj2 x) ->
    (forall x, inv1 x = inv2 x) ->
    (forall x, frob1 x = frob2 x) ->
    (forall x, frob_p21 x = frob_p22 x) ->
    (forall x, pow_x_s1 x = pow_x_s2 x) ->
    (forall x, pow_x_hs1 x = pow_x_hs2 x) ->
    forall f,
      generic_final_exp_dsd T sq1 ml1 conj1 inv1 frob1 frob_p21 pow_x_s1 pow_x_hs1 f =
      generic_final_exp_dsd T sq2 ml2 conj2 inv2 frob2 frob_p22 pow_x_s2 pow_x_hs2 f.
Proof.
  intros T sq1 sq2 ml1 ml2 conj1 conj2 inv1 inv2
         frob1 frob2 frob_p21 frob_p22 pow_x_s1 pow_x_s2 pow_x_hs1 pow_x_hs2
         Hsq Hml Hconj Hinv Hfrob Hfrob_p2 Hpow_x Hpow_xh f.
  unfold generic_final_exp_dsd, generic_final_exp_hard_dsd.
  rewrite Hconj, Hinv, Hml.
  rewrite Hfrob_p2, Hml.
  rewrite Hsq, Hpow_xh.
  rewrite Hconj, Hml.
  rewrite Hpow_x, Hconj, Hml.
  rewrite Hpow_x, Hfrob, Hml, Hml.
  rewrite Hpow_x, Hpow_x.
  rewrite Hfrob_p2, Hconj, Hml, Hml, Hml.
  reflexivity.
Qed.

(* ================================================================ *)
(** ** BLS12-377 instantiation                                       *)
(* ================================================================ *)

Local Opaque Fp6.fp6_add Fp6.fp6_sub Fp6.fp6_neg Fp6.fp6_mul
  Fp6.fp6_sqr Fp6.fp6_mul_by_v Fp6.fp6_inv Fp6.fp6_mul_fp2
  Fp6.fp6_frobenius Fp6.fp6_frobenius_p2.
Local Opaque Fp12.fp12_mul Fp12.fp12_sqr Fp12.fp12_add Fp12.fp12_sub
  Fp12.fp12_neg Fp12.fp12_conjugate Fp12.fp12_inv
  Fp12.fp12_frobenius Fp12.fp12_frobenius_p2.

Section DSDPairingFeval.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6' := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12' := (Fp6' * Fp6')%type.

  Variable beta : Fp.
  Variable xi_re xi_im : Fp.

  Variable fg1 fg2 fg1_p2 fg2_p2 : Fp2.
  Variable w_frob_c1 w_frob_p2_c1 : Fp2.

  (* The only non-trivial hypothesis: schoolbook squaring = Chung-Hasan *)
  Hypothesis fp6_mul_self_eq_sqr : forall a : Fp6',
    Fp6.fp6_mul p beta xi_re xi_im a a = Fp6.fp6_sqr p beta xi_re xi_im a.

  (* Bridge lemmas from BLS12_377_Fp12Feval *)
  Local Lemma sqr_eq : forall a,
    Fp12.fp12_sqr p beta xi_re xi_im a = spec_fp12_sqr p beta xi_re xi_im a.
  Proof. apply fp12_sqr_eq; exact fp6_mul_self_eq_sqr. Qed.

  Local Lemma mul_eq : forall a b,
    Fp12.fp12_mul p beta xi_re xi_im a b = spec_fp12_mul p beta xi_re xi_im a b.
  Proof. apply fp12_mul_eq. Qed.

  Local Lemma conjugate_eq' : forall a,
    Fp12.fp12_conjugate p a = spec_fp12_conjugate p a.
  Proof. apply fp12_conjugate_eq. Qed.

  Local Lemma inv_eq' : forall a,
    Fp12.fp12_inv p beta xi_re xi_im a = spec_fp12_inv p beta xi_re xi_im a.
  Proof. apply fp12_inv_eq; exact fp6_mul_self_eq_sqr. Qed.

  Local Lemma frobenius_eq' : forall a,
    Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1 a =
    spec_fp12_frobenius p beta fg1 fg2 w_frob_c1 a.
  Proof. apply fp12_frobenius_eq. Qed.

  Local Lemma frobenius_p2_eq' : forall a,
    Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 a =
    spec_fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 a.
  Proof. apply fp12_frobenius_p2_eq. Qed.

  Local Lemma pow_x_signed_eq : forall f,
    bedrock2_pow_bls_x_signed p beta xi_re xi_im f =
    spec_pow_bls_x_signed p beta xi_re xi_im f.
  Proof. apply pow_bls_x_signed_feval; exact fp6_mul_self_eq_sqr. Qed.

  Local Lemma pow_x_half_signed_eq : forall f,
    bedrock2_pow_bls_x_half_signed p beta xi_re xi_im f =
    spec_pow_bls_x_half_signed p beta xi_re xi_im f.
  Proof. apply pow_bls_x_half_signed_feval; exact fp6_mul_self_eq_sqr. Qed.

  (* Bedrock2 final exp = generic DSD with bedrock2 operations *)
  Definition bedrock2_final_exp_dsd : Fp12' -> Fp12' :=
    generic_final_exp_dsd Fp12'
      (Fp12.fp12_sqr p beta xi_re xi_im)
      (Fp12.fp12_mul p beta xi_re xi_im)
      (Fp12.fp12_conjugate p)
      (Fp12.fp12_inv p beta xi_re xi_im)
      (Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1)
      (Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1)
      (bedrock2_pow_bls_x_signed p beta xi_re xi_im)
      (bedrock2_pow_bls_x_half_signed p beta xi_re xi_im).

  (* Spec final exp = generic DSD with spec operations *)
  Definition spec_final_exp_dsd : Fp12' -> Fp12' :=
    generic_final_exp_dsd Fp12'
      (spec_fp12_sqr p beta xi_re xi_im)
      (spec_fp12_mul p beta xi_re xi_im)
      (spec_fp12_conjugate p)
      (spec_fp12_inv p beta xi_re xi_im)
      (spec_fp12_frobenius p beta fg1 fg2 w_frob_c1)
      (spec_fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1)
      (spec_pow_bls_x_signed p beta xi_re xi_im)
      (spec_pow_bls_x_half_signed p beta xi_re xi_im).

  Theorem final_exp_dsd_feval_correct : forall f : Fp12',
    bedrock2_final_exp_dsd f = spec_final_exp_dsd f.
  Proof.
    unfold bedrock2_final_exp_dsd, spec_final_exp_dsd.
    apply generic_dsd_congr;
      first [ exact sqr_eq
            | exact mul_eq
            | exact conjugate_eq'
            | exact inv_eq'
            | exact frobenius_eq'
            | exact frobenius_p2_eq'
            | exact pow_x_signed_eq
            | exact pow_x_half_signed_eq ].
  Qed.

End DSDPairingFeval.
