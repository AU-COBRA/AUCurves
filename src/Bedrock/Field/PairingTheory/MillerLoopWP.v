(** * MillerLoopWP: strengthened WP spec for [bn254_miller_loop].

    This file provides the strengthened postcondition that connects
    the bedrock2 Miller loop output to the Gallina reference via
    [feval]:

      [fp12_to_Z (Fp12_feval out) = affine_miller bn254_zmod_ops (6u+2) P Q]

    It consists of:

    (1) A [spec_of] instance with the mathematical postcondition
    (2) A loop invariant that tracks:
        - [f_val = affine_miller_aux n i P Q f_init Qx Qy]  (the Fp12 accumulator)
        - [T_val = [n_{top..i}] * Q]                        (the running point)
    (3) Proof obligations that discharge each call in the loop body
        against the corresponding [affine_miller_aux] step

    STATUS: the spec and invariant are STATED but the proof is ADMITTED.
    Closing it requires:
    - Per-call bridging lemmas (one per Fp2/Fp12 operation)
    - The [make_line] bridging lemma (which will fail until the bedrock2
      source uses the D-twist layout — exactly as predicted by
      [ZModTest.line_form_matters])
    - Loop invariant induction via [Loops.while_localsmap]

    This is the file that Rupicola's structured proof approach would
    simplify: instead of manually walking 1667 lines of [straightline],
    the proof would declare the invariant and let Rupicola verify each
    loop body step against it. The existing [mcall] tactic pattern
    from [BN254_MillerLoop.v] can be adapted to additionally track
    the [feval] chain.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.

Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.Curves.BN254_params.
Require Import Bedrock.Field.PairingTheory.Curves.BLS12_381_params.
Require Import Bedrock.Field.PairingTheory.Curves.BN256_params.
Require Import Bedrock.Field.PairingTheory.Curves.BN446_params.
Require Import Bedrock.Field.PairingTheory.Curves.BLS12_377_params.
Require Import Bedrock.Field.PairingTheory.FevalBridge.
Require Import Bedrock.Field.PairingTheory.LoopInvariant.
Require Import Bedrock.Field.PairingTheory.PairingSpec.

Local Open Scope Z_scope.

(** The strengthened postcondition for [bn254_miller_loop]:
    after the call, [feval(out)] equals the Gallina reference. *)

Section MillerLoopWP.

  (** The BN254 loop parameter. *)
  Let loop_param := loop_abs bn254_params.  (* = 6u+2 *)
  Let bn254_M_pos := Z.to_pos (prime_p bn254_params).

  (** The mathematical value the Miller loop should compute,
      given inputs P = (Px, Py) in Fp and Q = (Qx, Qy) in Fp2.
      This is the REFERENCE: any correct implementation must produce
      this exact Fp12 value. *)
  Definition bn254_miller_loop_spec
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    affine_miller bn254_zmod_ops loop_param Px Py Qx Qy.

  (** L4 obligation, parametric form. The bedrock2 Miller loop, when
      called with field elements whose [feval]s are [Px,Py,Qx,Qy], must
      produce an output [out] whose Fp12 value satisfies the equation
      below. This Definition is what the bedrock2 WP postcondition will
      ultimately reference, once a strengthened [spec_of] is plugged in. *)
  Definition L4_miller_obligation
      (out : Fp12_Z) (Px Py : Z) (Qx Qy : Fp2_Z) : Prop :=
    out = bn254_miller_loop_spec Px Py Qx Qy.

  (** L4 sufficiency lemma (Qed): if a bedrock2 Miller loop body
      establishes the [LoopInvariant.cont_inv] continuation invariant
      at exit (i = 0), then the L4 obligation is satisfied for the
      output [f]. This reduces the bedrock2 proof obligation to:
      "show the loop body preserves [cont_inv]" — which is the
      remaining substantive Phase 4 work. *)
  Lemma cont_inv_at_exit_implies_L4
        (Px Py : Z) (Qx Qy : Fp2_Z)
        (f_out : Fp12_Z) (Tx_out Ty_out : Fp2_Z) :
    LoopInvariant.cont_inv bn254_zmod_ops loop_param Px Py Qx Qy
                           0 f_out Tx_out Ty_out ->
    L4_miller_obligation f_out Px Py Qx Qy.
  Proof.
    intros Hinv. unfold L4_miller_obligation, bn254_miller_loop_spec.
    exact (LoopInvariant.cont_inv_gives_affine_miller
             bn254_zmod_ops loop_param Px Py Qx Qy f_out Tx_out Ty_out Hinv).
  Qed.

  (** L4 readiness via [feval] bridge: same statement, but with the inputs
      typed as field elements [F bn254_M_pos] / [Fp2] and bridged into Z
      via [fp_to_Z]/[fp2_to_Z]. This is the form a bedrock2 caller will
      use to discharge a strong postcondition like
        [fp12_to_Z M_pos (Fp12_feval out) = bn254_miller_loop_spec ...]
      from a per-iteration cont_inv. *)
  Lemma L4_via_bridge
        (Px Py : F bn254_M_pos) (Qx Qy : F bn254_M_pos * F bn254_M_pos)
        (f_out : Fp12_Z) (Tx_out Ty_out : Fp2_Z) :
    LoopInvariant.cont_inv bn254_zmod_ops loop_param
        (fp_to_Z bn254_M_pos Px) (fp_to_Z bn254_M_pos Py)
        (fp2_to_Z bn254_M_pos Qx) (fp2_to_Z bn254_M_pos Qy)
        0 f_out Tx_out Ty_out ->
    f_out = bn254_miller_loop_spec
              (fp_to_Z bn254_M_pos Px) (fp_to_Z bn254_M_pos Py)
              (fp2_to_Z bn254_M_pos Qx) (fp2_to_Z bn254_M_pos Qy).
  Proof.
    intros Hinv.
    exact (cont_inv_at_exit_implies_L4 _ _ _ _ _ _ _ Hinv).
  Qed.

End MillerLoopWP.

(** ================================================================ *)
(** BLS12-381 analog                                                  *)
(** ================================================================ *)

Section BLS12_381_MillerLoopWP.

  Let bls12_loop_param := loop_abs bls12_381_params.  (* = |x|, the BLS12-381 seed *)
  Let bls12_M_pos := Z.to_pos (prime_p bls12_381_params).

  Definition bls12_381_miller_loop_spec
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    affine_miller bls12_381_zmod_ops bls12_loop_param Px Py Qx Qy.

  (** L4 obligation for the BLS12-381 bare Miller loop (no Frob corrections,
      since [optimal_ate_extras bls12_381_params = []]). *)
  Definition L4_bls12_miller_obligation
      (out : Fp12_Z) (Px Py : Z) (Qx Qy : Fp2_Z) : Prop :=
    out = bls12_381_miller_loop_spec Px Py Qx Qy.

  Lemma bls12_cont_inv_at_exit_implies_L4
        (Px Py : Z) (Qx Qy : Fp2_Z)
        (f_out : Fp12_Z) (Tx_out Ty_out : Fp2_Z) :
    LoopInvariant.cont_inv bls12_381_zmod_ops bls12_loop_param Px Py Qx Qy
                           0 f_out Tx_out Ty_out ->
    L4_bls12_miller_obligation f_out Px Py Qx Qy.
  Proof.
    intros Hinv. unfold L4_bls12_miller_obligation, bls12_381_miller_loop_spec.
    exact (LoopInvariant.cont_inv_gives_affine_miller
             bls12_381_zmod_ops bls12_loop_param Px Py Qx Qy
             f_out Tx_out Ty_out Hinv).
  Qed.

  Lemma bls12_L4_via_bridge
        (Px Py : F bls12_M_pos) (Qx Qy : F bls12_M_pos * F bls12_M_pos)
        (f_out : Fp12_Z) (Tx_out Ty_out : Fp2_Z) :
    LoopInvariant.cont_inv bls12_381_zmod_ops bls12_loop_param
        (fp_to_Z bls12_M_pos Px) (fp_to_Z bls12_M_pos Py)
        (fp2_to_Z bls12_M_pos Qx) (fp2_to_Z bls12_M_pos Qy)
        0 f_out Tx_out Ty_out ->
    f_out = bls12_381_miller_loop_spec
              (fp_to_Z bls12_M_pos Px) (fp_to_Z bls12_M_pos Py)
              (fp2_to_Z bls12_M_pos Qx) (fp2_to_Z bls12_M_pos Qy).
  Proof.
    intros Hinv.
    exact (bls12_cont_inv_at_exit_implies_L4 _ _ _ _ _ _ _ Hinv).
  Qed.

End BLS12_381_MillerLoopWP.

(** ================================================================ *)
(** Strong loop invariant — parametric over bedrock2 felem types     *)
(** ================================================================ *)

(** This Section defines the [cont_inv]-tracking strong invariant that
    a strengthened bedrock2 [bn254_miller_loop_ok] proof would need to
    establish. It is parametric over the bedrock2 felem types and the
    [feval]→[Z] composition, so MillerLoopWP.v stays light (no bedrock2
    imports). The bedrock2-side instantiation lives in
    [Synthesis/Examples/BN254_MillerLoop.v]. *)

Section BN254_StrongInvariant.

  (** Abstract bedrock2 felem types and bridges to Z. *)
  Variable Felem_Fp Felem_Fp2 Felem_Fp12 : Type.
  Variable feval_z   : Felem_Fp   -> Z.
  Variable feval_z2  : Felem_Fp2  -> Fp2_Z.
  Variable feval_z12 : Felem_Fp12 -> Fp12_Z.

  Let loop_param := loop_abs bn254_params.

  (** The strong loop invariant: at iteration [i] (counting down), the
      bedrock2 felems [(f, tx, ty)] are such that completing [i] more
      ZModTower iterations from their feval values gives the full Miller
      result. *)
  Definition bn254_strong_inv
      (i : nat)
      (f : Felem_Fp12) (tx ty : Felem_Fp2)
      (px py : Felem_Fp) (qx qy : Felem_Fp2) : Prop :=
    LoopInvariant.cont_inv bn254_zmod_ops loop_param
      (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
      i (feval_z12 f) (feval_z2 tx) (feval_z2 ty).

  (** Initialization: at loop entry (i = nbits, f = 1, T = Q), the strong
      invariant holds, ASSUMING the bedrock2 [f] felem represents Fp12 1
      and [(tx, ty)] represent Q. *)
  Lemma bn254_strong_inv_init
      (f : Felem_Fp12) (tx ty : Felem_Fp2)
      (px py : Felem_Fp) (qx qy : Felem_Fp2)
      (Hf : feval_z12 f = fp12_one bn254_zmod_ops)
      (Htx : feval_z2 tx = feval_z2 qx)
      (Hty : feval_z2 ty = feval_z2 qy) :
    bn254_strong_inv (Z.to_nat (Z.log2 loop_param)) f tx ty px py qx qy.
  Proof.
    unfold bn254_strong_inv. rewrite Hf, Htx, Hty.
    apply LoopInvariant.cont_inv_init.
  Qed.

  (** Exit: at i = 0, the strong invariant gives the L4 obligation
      directly, expressed via the bedrock2 feval bridge. *)
  Lemma bn254_strong_inv_at_exit
      (f : Felem_Fp12) (tx ty : Felem_Fp2)
      (px py : Felem_Fp) (qx qy : Felem_Fp2) :
    bn254_strong_inv 0 f tx ty px py qx qy ->
    feval_z12 f = bn254_miller_loop_spec
                    (feval_z px) (feval_z py)
                    (feval_z2 qx) (feval_z2 qy).
  Proof.
    unfold bn254_strong_inv. intro Hinv.
    exact (LoopInvariant.cont_inv_gives_affine_miller
             bn254_zmod_ops loop_param
             (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
             (feval_z12 f) (feval_z2 tx) (feval_z2 ty) Hinv).
  Qed.

End BN254_StrongInvariant.

Section BLS12_381_StrongInvariant.

  Variable Felem_Fp Felem_Fp2 Felem_Fp12 : Type.
  Variable feval_z   : Felem_Fp   -> Z.
  Variable feval_z2  : Felem_Fp2  -> Fp2_Z.
  Variable feval_z12 : Felem_Fp12 -> Fp12_Z.

  Let bls12_loop_param := loop_abs bls12_381_params.

  Definition bls12_strong_inv
      (i : nat)
      (f : Felem_Fp12) (tx ty : Felem_Fp2)
      (px py : Felem_Fp) (qx qy : Felem_Fp2) : Prop :=
    LoopInvariant.cont_inv bls12_381_zmod_ops bls12_loop_param
      (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
      i (feval_z12 f) (feval_z2 tx) (feval_z2 ty).

  Lemma bls12_strong_inv_init
      (f : Felem_Fp12) (tx ty : Felem_Fp2)
      (px py : Felem_Fp) (qx qy : Felem_Fp2)
      (Hf : feval_z12 f = fp12_one bls12_381_zmod_ops)
      (Htx : feval_z2 tx = feval_z2 qx)
      (Hty : feval_z2 ty = feval_z2 qy) :
    bls12_strong_inv (Z.to_nat (Z.log2 bls12_loop_param)) f tx ty px py qx qy.
  Proof.
    unfold bls12_strong_inv. rewrite Hf, Htx, Hty.
    apply LoopInvariant.cont_inv_init.
  Qed.

  Lemma bls12_strong_inv_at_exit
      (f : Felem_Fp12) (tx ty : Felem_Fp2)
      (px py : Felem_Fp) (qx qy : Felem_Fp2) :
    bls12_strong_inv 0 f tx ty px py qx qy ->
    feval_z12 f = bls12_381_miller_loop_spec
                    (feval_z px) (feval_z py)
                    (feval_z2 qx) (feval_z2 qy).
  Proof.
    unfold bls12_strong_inv. intro Hinv.
    exact (LoopInvariant.cont_inv_gives_affine_miller
             bls12_381_zmod_ops bls12_loop_param
             (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
             (feval_z12 f) (feval_z2 tx) (feval_z2 ty) Hinv).
  Qed.

End BLS12_381_StrongInvariant.

(** ================================================================ *)
(** Full pairing spec (Miller + Frobenius corrections + final exp)   *)
(** ================================================================ *)

(** This Section instantiates [PairingSpec.optimal_ate] with the
    ZModTower implementations of all the extra tower operations
    ([zfp12_conj], [zfp12_inv], etc., from ZModTower.v). The result
    is the FULL Gallina spec for the BN254/BLS12-381 optimal ate
    pairing — what every correct implementation must produce. *)

Section BN254_FullPairing.

  Let bn254_p := prime_p bn254_params.
  Let bn254_xi : Fp2_Z := (xi_re bn254_params, xi_im bn254_params).

  (** The BN254 optimal-ate pairing as a Gallina function over Z. *)
  Definition bn254_optimal_ate_spec
      (gamma1 gamma_y gamma1_p2 : Fp2_Z)
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    PairingSpec.optimal_ate
      bn254_zmod_ops
      (zfp12_conj bn254_p)         (* fp12_conj *)
      (zfp12_inv bn254_p bn254_xi) (* fp12_inv  *)
      (zfp12_frob_p2 bn254_p bn254_xi) (* fp12_frob_p2 *)
      (zfp12_pow bn254_p bn254_xi) (* fp12_pow *)
      (zfp2_conj bn254_p)          (* fp2_conj *)
      (zfp2_mul_const bn254_p)     (* fp2_mul_const *)
      bn254_params
      gamma1 gamma_y gamma1_p2
      Px Py Qx Qy.

  (** L4 obligation for the FULL pairing. *)
  Definition L4_bn254_full_obligation
      (out : Fp12_Z) (gamma1 gamma_y gamma1_p2 : Fp2_Z)
      (Px Py : Z) (Qx Qy : Fp2_Z) : Prop :=
    out = bn254_optimal_ate_spec gamma1 gamma_y gamma1_p2 Px Py Qx Qy.

  (** Spec connection: [bn254_optimal_ate_spec] is exactly
      [PairingSpec.optimal_ate] applied to the bn254 ZModTower instance.
      A trivial Qed contribution; mostly documents the connection. *)
  Lemma bn254_optimal_ate_spec_unfold
      (gamma1 gamma_y gamma1_p2 : Fp2_Z)
      (Px Py : Z) (Qx Qy : Fp2_Z) :
    bn254_optimal_ate_spec gamma1 gamma_y gamma1_p2 Px Py Qx Qy =
    PairingSpec.optimal_ate
      bn254_zmod_ops
      (zfp12_conj bn254_p)
      (zfp12_inv bn254_p bn254_xi)
      (zfp12_frob_p2 bn254_p bn254_xi)
      (zfp12_pow bn254_p bn254_xi)
      (zfp2_conj bn254_p)
      (zfp2_mul_const bn254_p)
      bn254_params
      gamma1 gamma_y gamma1_p2
      Px Py Qx Qy.
  Proof. reflexivity. Qed.

End BN254_FullPairing.

Section BLS12_381_FullPairing.

  Let bls12_p := prime_p bls12_381_params.
  Let bls12_xi : Fp2_Z := (xi_re bls12_381_params, xi_im bls12_381_params).

  Definition bls12_381_optimal_ate_spec
      (gamma1 gamma_y gamma1_p2 : Fp2_Z)
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    PairingSpec.optimal_ate
      bls12_381_zmod_ops
      (zfp12_conj bls12_p)
      (zfp12_inv bls12_p bls12_xi)
      (zfp12_frob_p2 bls12_p bls12_xi)
      (zfp12_pow bls12_p bls12_xi)
      (zfp2_conj bls12_p)
      (zfp2_mul_const bls12_p)
      bls12_381_params
      gamma1 gamma_y gamma1_p2
      Px Py Qx Qy.

  Definition L4_bls12_full_obligation
      (out : Fp12_Z) (gamma1 gamma_y gamma1_p2 : Fp2_Z)
      (Px Py : Z) (Qx Qy : Fp2_Z) : Prop :=
    out = bls12_381_optimal_ate_spec gamma1 gamma_y gamma1_p2 Px Py Qx Qy.

  Lemma bls12_381_optimal_ate_spec_unfold
      (gamma1 gamma_y gamma1_p2 : Fp2_Z)
      (Px Py : Z) (Qx Qy : Fp2_Z) :
    bls12_381_optimal_ate_spec gamma1 gamma_y gamma1_p2 Px Py Qx Qy =
    PairingSpec.optimal_ate
      bls12_381_zmod_ops
      (zfp12_conj bls12_p)
      (zfp12_inv bls12_p bls12_xi)
      (zfp12_frob_p2 bls12_p bls12_xi)
      (zfp12_pow bls12_p bls12_xi)
      (zfp2_conj bls12_p)
      (zfp2_mul_const bls12_p)
      bls12_381_params
      gamma1 gamma_y gamma1_p2
      Px Py Qx Qy.
  Proof. reflexivity. Qed.

End BLS12_381_FullPairing.

(** ================================================================ *)
(** Cross-curve L4 wiring: BN256, BN446, BLS12-377                   *)
(**                                                                   *)
(** Each curve gets:                                                  *)
(**   - [<curve>_miller_loop_spec]   : the L2 affine miller spec     *)
(**   - [L4_<curve>_miller_obligation] : equation form               *)
(**   - [<curve>_strong_inv]         : feval-bridged loop invariant  *)
(**   - [<curve>_strong_inv_init]    : Qed lemma at loop entry       *)
(**   - [<curve>_strong_inv_at_exit] : Qed lemma at i = 0            *)
(**   - [<curve>_optimal_ate_spec]   : full pairing spec via PairingSpec *)
(**   - [<curve>_optimal_ate_spec_unfold] : Qed unfold lemma         *)
(** ================================================================ *)

Section BN256_MillerLoopWP.

  Let bn256_loop_param := loop_abs bn256_params.
  Let bn256_M_pos := Z.to_pos (prime_p bn256_params).
  Let bn256_p := prime_p bn256_params.
  Let bn256_xi : Fp2_Z := (xi_re bn256_params, xi_im bn256_params).

  Definition bn256_miller_loop_spec
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    affine_miller bn256_zmod_ops bn256_loop_param Px Py Qx Qy.

  Definition L4_bn256_miller_obligation
      (out : Fp12_Z) (Px Py : Z) (Qx Qy : Fp2_Z) : Prop :=
    out = bn256_miller_loop_spec Px Py Qx Qy.

  Section BN256_StrongInv.
    Variable Felem_Fp Felem_Fp2 Felem_Fp12 : Type.
    Variable feval_z   : Felem_Fp   -> Z.
    Variable feval_z2  : Felem_Fp2  -> Fp2_Z.
    Variable feval_z12 : Felem_Fp12 -> Fp12_Z.

    Definition bn256_strong_inv
        (i : nat)
        (f : Felem_Fp12) (tx ty : Felem_Fp2)
        (px py : Felem_Fp) (qx qy : Felem_Fp2) : Prop :=
      LoopInvariant.cont_inv bn256_zmod_ops bn256_loop_param
        (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
        i (feval_z12 f) (feval_z2 tx) (feval_z2 ty).

    Lemma bn256_strong_inv_init
        (f : Felem_Fp12) (tx ty : Felem_Fp2)
        (px py : Felem_Fp) (qx qy : Felem_Fp2)
        (Hf : feval_z12 f = fp12_one bn256_zmod_ops)
        (Htx : feval_z2 tx = feval_z2 qx)
        (Hty : feval_z2 ty = feval_z2 qy) :
      bn256_strong_inv (Z.to_nat (Z.log2 bn256_loop_param)) f tx ty px py qx qy.
    Proof.
      unfold bn256_strong_inv. rewrite Hf, Htx, Hty.
      apply LoopInvariant.cont_inv_init.
    Qed.

    Lemma bn256_strong_inv_at_exit
        (f : Felem_Fp12) (tx ty : Felem_Fp2)
        (px py : Felem_Fp) (qx qy : Felem_Fp2) :
      bn256_strong_inv 0 f tx ty px py qx qy ->
      feval_z12 f = bn256_miller_loop_spec
                      (feval_z px) (feval_z py)
                      (feval_z2 qx) (feval_z2 qy).
    Proof.
      unfold bn256_strong_inv. intro Hinv.
      exact (LoopInvariant.cont_inv_gives_affine_miller
               bn256_zmod_ops bn256_loop_param
               (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
               (feval_z12 f) (feval_z2 tx) (feval_z2 ty) Hinv).
    Qed.
  End BN256_StrongInv.

  Definition bn256_optimal_ate_spec
      (gamma1 gamma_y gamma1_p2 : Fp2_Z)
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    PairingSpec.optimal_ate
      bn256_zmod_ops
      (zfp12_conj bn256_p)
      (zfp12_inv bn256_p bn256_xi)
      (zfp12_frob_p2 bn256_p bn256_xi)
      (zfp12_pow bn256_p bn256_xi)
      (zfp2_conj bn256_p)
      (zfp2_mul_const bn256_p)
      bn256_params
      gamma1 gamma_y gamma1_p2 Px Py Qx Qy.

  Lemma bn256_optimal_ate_spec_unfold
      (gamma1 gamma_y gamma1_p2 : Fp2_Z) (Px Py : Z) (Qx Qy : Fp2_Z) :
    bn256_optimal_ate_spec gamma1 gamma_y gamma1_p2 Px Py Qx Qy =
    PairingSpec.optimal_ate
      bn256_zmod_ops
      (zfp12_conj bn256_p) (zfp12_inv bn256_p bn256_xi)
      (zfp12_frob_p2 bn256_p bn256_xi) (zfp12_pow bn256_p bn256_xi)
      (zfp2_conj bn256_p) (zfp2_mul_const bn256_p)
      bn256_params gamma1 gamma_y gamma1_p2 Px Py Qx Qy.
  Proof. reflexivity. Qed.

End BN256_MillerLoopWP.

Section BN446_MillerLoopWP.

  Let bn446_loop_param := loop_abs bn446_params.
  Let bn446_M_pos := Z.to_pos (prime_p bn446_params).
  Let bn446_p := prime_p bn446_params.
  Let bn446_xi : Fp2_Z := (xi_re bn446_params, xi_im bn446_params).

  Definition bn446_miller_loop_spec
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    affine_miller bn446_zmod_ops bn446_loop_param Px Py Qx Qy.

  Definition L4_bn446_miller_obligation
      (out : Fp12_Z) (Px Py : Z) (Qx Qy : Fp2_Z) : Prop :=
    out = bn446_miller_loop_spec Px Py Qx Qy.

  Section BN446_StrongInv.
    Variable Felem_Fp Felem_Fp2 Felem_Fp12 : Type.
    Variable feval_z   : Felem_Fp   -> Z.
    Variable feval_z2  : Felem_Fp2  -> Fp2_Z.
    Variable feval_z12 : Felem_Fp12 -> Fp12_Z.

    Definition bn446_strong_inv
        (i : nat)
        (f : Felem_Fp12) (tx ty : Felem_Fp2)
        (px py : Felem_Fp) (qx qy : Felem_Fp2) : Prop :=
      LoopInvariant.cont_inv bn446_zmod_ops bn446_loop_param
        (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
        i (feval_z12 f) (feval_z2 tx) (feval_z2 ty).

    Lemma bn446_strong_inv_init
        (f : Felem_Fp12) (tx ty : Felem_Fp2)
        (px py : Felem_Fp) (qx qy : Felem_Fp2)
        (Hf : feval_z12 f = fp12_one bn446_zmod_ops)
        (Htx : feval_z2 tx = feval_z2 qx)
        (Hty : feval_z2 ty = feval_z2 qy) :
      bn446_strong_inv (Z.to_nat (Z.log2 bn446_loop_param)) f tx ty px py qx qy.
    Proof.
      unfold bn446_strong_inv. rewrite Hf, Htx, Hty.
      apply LoopInvariant.cont_inv_init.
    Qed.

    Lemma bn446_strong_inv_at_exit
        (f : Felem_Fp12) (tx ty : Felem_Fp2)
        (px py : Felem_Fp) (qx qy : Felem_Fp2) :
      bn446_strong_inv 0 f tx ty px py qx qy ->
      feval_z12 f = bn446_miller_loop_spec
                      (feval_z px) (feval_z py)
                      (feval_z2 qx) (feval_z2 qy).
    Proof.
      unfold bn446_strong_inv. intro Hinv.
      exact (LoopInvariant.cont_inv_gives_affine_miller
               bn446_zmod_ops bn446_loop_param
               (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
               (feval_z12 f) (feval_z2 tx) (feval_z2 ty) Hinv).
    Qed.
  End BN446_StrongInv.

  Definition bn446_optimal_ate_spec
      (gamma1 gamma_y gamma1_p2 : Fp2_Z)
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    PairingSpec.optimal_ate
      bn446_zmod_ops
      (zfp12_conj bn446_p) (zfp12_inv bn446_p bn446_xi)
      (zfp12_frob_p2 bn446_p bn446_xi) (zfp12_pow bn446_p bn446_xi)
      (zfp2_conj bn446_p) (zfp2_mul_const bn446_p)
      bn446_params gamma1 gamma_y gamma1_p2 Px Py Qx Qy.

  Lemma bn446_optimal_ate_spec_unfold
      (gamma1 gamma_y gamma1_p2 : Fp2_Z) (Px Py : Z) (Qx Qy : Fp2_Z) :
    bn446_optimal_ate_spec gamma1 gamma_y gamma1_p2 Px Py Qx Qy =
    PairingSpec.optimal_ate
      bn446_zmod_ops
      (zfp12_conj bn446_p) (zfp12_inv bn446_p bn446_xi)
      (zfp12_frob_p2 bn446_p bn446_xi) (zfp12_pow bn446_p bn446_xi)
      (zfp2_conj bn446_p) (zfp2_mul_const bn446_p)
      bn446_params gamma1 gamma_y gamma1_p2 Px Py Qx Qy.
  Proof. reflexivity. Qed.

End BN446_MillerLoopWP.

Section BLS12_377_MillerLoopWP.

  Let bls12_377_loop_param := loop_abs bls12_377_params.
  Let bls12_377_M_pos := Z.to_pos (prime_p bls12_377_params).
  Let bls12_377_p := prime_p bls12_377_params.
  Let bls12_377_xi : Fp2_Z := (xi_re bls12_377_params, xi_im bls12_377_params).

  Definition bls12_377_miller_loop_spec
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    affine_miller bls12_377_zmod_ops bls12_377_loop_param Px Py Qx Qy.

  Definition L4_bls12_377_miller_obligation
      (out : Fp12_Z) (Px Py : Z) (Qx Qy : Fp2_Z) : Prop :=
    out = bls12_377_miller_loop_spec Px Py Qx Qy.

  Section BLS12_377_StrongInv.
    Variable Felem_Fp Felem_Fp2 Felem_Fp12 : Type.
    Variable feval_z   : Felem_Fp   -> Z.
    Variable feval_z2  : Felem_Fp2  -> Fp2_Z.
    Variable feval_z12 : Felem_Fp12 -> Fp12_Z.

    Definition bls12_377_strong_inv
        (i : nat)
        (f : Felem_Fp12) (tx ty : Felem_Fp2)
        (px py : Felem_Fp) (qx qy : Felem_Fp2) : Prop :=
      LoopInvariant.cont_inv bls12_377_zmod_ops bls12_377_loop_param
        (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
        i (feval_z12 f) (feval_z2 tx) (feval_z2 ty).

    Lemma bls12_377_strong_inv_init
        (f : Felem_Fp12) (tx ty : Felem_Fp2)
        (px py : Felem_Fp) (qx qy : Felem_Fp2)
        (Hf : feval_z12 f = fp12_one bls12_377_zmod_ops)
        (Htx : feval_z2 tx = feval_z2 qx)
        (Hty : feval_z2 ty = feval_z2 qy) :
      bls12_377_strong_inv
        (Z.to_nat (Z.log2 bls12_377_loop_param)) f tx ty px py qx qy.
    Proof.
      unfold bls12_377_strong_inv. rewrite Hf, Htx, Hty.
      apply LoopInvariant.cont_inv_init.
    Qed.

    Lemma bls12_377_strong_inv_at_exit
        (f : Felem_Fp12) (tx ty : Felem_Fp2)
        (px py : Felem_Fp) (qx qy : Felem_Fp2) :
      bls12_377_strong_inv 0 f tx ty px py qx qy ->
      feval_z12 f = bls12_377_miller_loop_spec
                      (feval_z px) (feval_z py)
                      (feval_z2 qx) (feval_z2 qy).
    Proof.
      unfold bls12_377_strong_inv. intro Hinv.
      exact (LoopInvariant.cont_inv_gives_affine_miller
               bls12_377_zmod_ops bls12_377_loop_param
               (feval_z px) (feval_z py) (feval_z2 qx) (feval_z2 qy)
               (feval_z12 f) (feval_z2 tx) (feval_z2 ty) Hinv).
    Qed.
  End BLS12_377_StrongInv.

  Definition bls12_377_optimal_ate_spec
      (gamma1 gamma_y gamma1_p2 : Fp2_Z)
      (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
    PairingSpec.optimal_ate
      bls12_377_zmod_ops
      (zfp12_conj bls12_377_p) (zfp12_inv bls12_377_p bls12_377_xi)
      (zfp12_frob_p2 bls12_377_p bls12_377_xi)
      (zfp12_pow bls12_377_p bls12_377_xi)
      (zfp2_conj bls12_377_p) (zfp2_mul_const bls12_377_p)
      bls12_377_params gamma1 gamma_y gamma1_p2 Px Py Qx Qy.

  Lemma bls12_377_optimal_ate_spec_unfold
      (gamma1 gamma_y gamma1_p2 : Fp2_Z) (Px Py : Z) (Qx Qy : Fp2_Z) :
    bls12_377_optimal_ate_spec gamma1 gamma_y gamma1_p2 Px Py Qx Qy =
    PairingSpec.optimal_ate
      bls12_377_zmod_ops
      (zfp12_conj bls12_377_p) (zfp12_inv bls12_377_p bls12_377_xi)
      (zfp12_frob_p2 bls12_377_p bls12_377_xi)
      (zfp12_pow bls12_377_p bls12_377_xi)
      (zfp2_conj bls12_377_p) (zfp2_mul_const bls12_377_p)
      bls12_377_params gamma1 gamma_y gamma1_p2 Px Py Qx Qy.
  Proof. reflexivity. Qed.

End BLS12_377_MillerLoopWP.

(** ================================================================ *)
(** Loop invariant for the Miller loop WP proof                      *)
(**                                                                   *)
(** The loop body processes one bit of the loop parameter [n].        *)
(** After processing bits [top..i] (where top = MSB), the invariant  *)
(** states:                                                           *)
(**                                                                   *)
(**   feval(f)  = affine_miller_aux n i Px Py Qx Qy 1 Qx Qy         *)
(**   feval(Tx) = Tx_ref (the running x-coord from affine_miller_aux) *)
(**   feval(Ty) = Ty_ref (the running y-coord from affine_miller_aux) *)
(**   i         = i (the loop counter, a scalar, not a field element) *)
(**                                                                   *)
(** The invariant is established at loop entry (i = Z.log2 n,         *)
(** f = 1, T = Q) and preserved by each iteration (which calls        *)
(** double_step and conditionally add_step from Affine.v).            *)
(**                                                                   *)
(** Discharging the invariant for one iteration requires showing:     *)
(**   feval(Fp12_mul(Fp12_sqr f, make_line lam T P))                  *)
(**     = Affine.double_step ops (feval f) (feval Tx) (feval Ty) Px Py *)
(**                                                                   *)
(** This reduces to per-call bridging lemmas:                         *)
(**   feval(Fp2_sqr out)   = zfp2_sqr p (feval x)                    *)
(**   feval(Fp2_mul out)   = zfp2_mul p (feval x) (feval y)          *)
(**   feval(make_line out) = dtwist_make_line p (feval lam) ...       *)
(**   feval(Fp12_mul out)  = zfp12_mul p xi (feval x) (feval y)      *)
(**   etc.                                                            *)
(**                                                                   *)
(** Each of these is a straightforward consequence of the existing    *)
(** [spec_of_Fp2_mul], [spec_of_Fp12_mul] postconditions (which      *)
(** already include [feval out = model (feval x) (feval y)]) and      *)
(** the [FevalBridge] round-trip lemma.                               *)
(** ================================================================ *)

(** Per-call bridging lemma templates.
    These would live in a separate file [BridgingLemmas.v] and would
    be discharged by [rewrite F.to_Z_add] / [F.to_Z_mul] / etc.
    from [PrimeFieldTheorems.v]. *)

(** Example (not proved, just stated for documentation):

    Lemma fp2_mul_bridge :
      forall p (x y : F p * F p),
        fp2_to_Z p (F.mul (fst x) (fst y) - F.mul (snd x) (snd y),
                     F.mul (fst x) (snd y) + F.mul (snd x) (fst y))
        = zfp2_mul (Z.pos p) (fp2_to_Z p x) (fp2_to_Z p y).
*)
