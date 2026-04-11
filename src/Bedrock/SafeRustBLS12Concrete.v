(** * SafeRustBLS12Concrete.v
 *
 * Instantiates [SafeRustWBWConcrete] for BLS12-381.
 *
 * BLS12-381 is a 381-bit prime field, so [p_nlimbs = 6] (not 4 as
 * for BN254). Same structure as [SafeRustBN254Concrete.v] — only
 * the constants and side-condition proofs are curve-specific.
 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime_certif.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustBedrockBridge.
Require Import Bedrock.SafeRustLeafRefinement.
Require Import Bedrock.SafeRustWBWConcrete.

(* ================================================================ *)
(* §1. BLS12-381 parameters                                          *)
(* ================================================================ *)

Definition bls12_bitwidth : Z := 64%Z.
Definition bls12_nlimbs : nat := 6%nat.  (* 381 bits / 64 = 6 limbs *)
Definition bls12_modp : Z := bls12_381_modulus.
Definition bls12_r : Z := 2^bls12_bitwidth.
Definition bls12_rprime : Z := Eval vm_compute in (Z.invmod bls12_r bls12_modp).
Definition bls12_mprime : Z := Eval vm_compute in (Z.invmod (- bls12_modp) bls12_r).

(* ================================================================ *)
(* §2. BLS12-381 side conditions (discharged by vm_compute)          *)
(* ================================================================ *)

Lemma bls12_bitwidth_big : (0 < bls12_bitwidth)%Z.
Proof. unfold bls12_bitwidth. lia. Qed.

Lemma bls12_m_big : (1 < bls12_modp)%Z.
Proof. unfold bls12_modp, bls12_381_modulus. lia. Qed.

Lemma bls12_nlimbs_nz : bls12_nlimbs <> 0%nat.
Proof. unfold bls12_nlimbs. discriminate. Qed.

Lemma bls12_m_small : (bls12_modp < bls12_r ^ Z.of_nat bls12_nlimbs)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_rprime_correct :
  ((bls12_r * bls12_rprime) mod bls12_modp = 1)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_mprime_correct :
  ((bls12_modp * bls12_mprime) mod bls12_r = (-1) mod bls12_r)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §3. BLS12-381 specializations                                     *)
(* ================================================================ *)

Definition bls12_fp_eval : rust_val TFp -> Z :=
  fp_eval_rust_concrete bls12_bitwidth bls12_nlimbs bls12_modp bls12_mprime.

Definition bls12_fp_valid : rust_val TFp -> Prop :=
  fp_valid bls12_bitwidth bls12_nlimbs bls12_modp.

Definition bls12_add_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  add_impl_concrete bls12_bitwidth bls12_nlimbs bls12_modp.

Definition bls12_sub_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  sub_impl_concrete bls12_bitwidth bls12_nlimbs bls12_modp.

Definition bls12_opp_impl : rust_val TFp -> rust_val TFp :=
  opp_impl_concrete bls12_bitwidth bls12_nlimbs bls12_modp.

Definition bls12_mul_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  mul_impl_concrete bls12_bitwidth bls12_nlimbs bls12_modp bls12_mprime.

Definition bls12_square_impl : rust_val TFp -> rust_val TFp :=
  square_impl_concrete bls12_bitwidth bls12_nlimbs bls12_modp bls12_mprime.

Definition bls12_copy_impl : rust_val TFp -> rust_val TFp :=
  copy_impl_concrete.

(* ================================================================ *)
(* §4. BLS12-381 correctness lemmas via parametric instantiation    *)
(* ================================================================ *)

Lemma bls12_copy_correct : forall x,
  bls12_fp_eval (bls12_copy_impl x) = bls12_fp_eval x.
Proof. reflexivity. Qed.

Lemma bls12_add_correct : forall x y,
  bls12_fp_valid x -> bls12_fp_valid y ->
  bls12_fp_eval (bls12_add_impl x y)
  = (bls12_fp_eval x + bls12_fp_eval y) mod bls12_modp.
Proof.
  apply (add_impl_correct bls12_bitwidth bls12_nlimbs bls12_modp
           bls12_rprime bls12_mprime
           bls12_bitwidth_big bls12_m_big bls12_nlimbs_nz bls12_m_small
           bls12_rprime_correct bls12_mprime_correct).
Qed.

Lemma bls12_sub_correct : forall x y,
  bls12_fp_valid x -> bls12_fp_valid y ->
  bls12_fp_eval (bls12_sub_impl x y)
  = (bls12_fp_eval x - bls12_fp_eval y) mod bls12_modp.
Proof.
  apply (sub_impl_correct bls12_bitwidth bls12_nlimbs bls12_modp
           bls12_rprime bls12_mprime
           bls12_bitwidth_big bls12_m_big bls12_nlimbs_nz bls12_m_small
           bls12_rprime_correct bls12_mprime_correct).
Qed.

Lemma bls12_opp_correct : forall x,
  bls12_fp_valid x ->
  bls12_fp_eval (bls12_opp_impl x)
  = (- bls12_fp_eval x) mod bls12_modp.
Proof.
  apply (opp_impl_correct bls12_bitwidth bls12_nlimbs bls12_modp
           bls12_rprime bls12_mprime
           bls12_bitwidth_big bls12_m_big bls12_nlimbs_nz bls12_m_small
           bls12_rprime_correct bls12_mprime_correct).
Qed.

Lemma bls12_mul_correct : forall x y,
  bls12_fp_valid x -> bls12_fp_valid y ->
  bls12_fp_eval (bls12_mul_impl x y)
  = (bls12_fp_eval x * bls12_fp_eval y) mod bls12_modp.
Proof.
  apply (mul_impl_correct bls12_bitwidth bls12_nlimbs bls12_modp
           bls12_rprime bls12_mprime
           bls12_bitwidth_big bls12_m_big bls12_nlimbs_nz bls12_m_small
           bls12_rprime_correct bls12_mprime_correct).
Qed.

Lemma bls12_square_correct : forall x,
  bls12_fp_valid x ->
  bls12_fp_eval (bls12_square_impl x)
  = (bls12_fp_eval x * bls12_fp_eval x) mod bls12_modp.
Proof.
  apply (square_impl_correct bls12_bitwidth bls12_nlimbs bls12_modp
           bls12_rprime bls12_mprime
           bls12_bitwidth_big bls12_m_big bls12_nlimbs_nz bls12_m_small
           bls12_rprime_correct bls12_mprime_correct).
Qed.

(* ================================================================ *)
(* §5. Refinement witnesses                                          *)
(* ================================================================ *)

Theorem bls12_copy_refines :
  leaf_refines_copy_valid bls12_fp_valid bls12_fp_eval bls12_copy_impl.
Proof. unfold leaf_refines_copy_valid. intros. apply bls12_copy_correct. Qed.

Theorem bls12_add_refines :
  leaf_refines_binop_valid bls12_fp_valid bls12_fp_eval
    bls12_add_impl
    (fun a b => (a + b) mod bls12_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bls12_add_correct; assumption.
Qed.

Theorem bls12_sub_refines :
  leaf_refines_binop_valid bls12_fp_valid bls12_fp_eval
    bls12_sub_impl
    (fun a b => (a - b) mod bls12_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bls12_sub_correct; assumption.
Qed.

Theorem bls12_opp_refines :
  leaf_refines_unop_valid bls12_fp_valid bls12_fp_eval
    bls12_opp_impl
    (fun a => (- a) mod bls12_modp).
Proof.
  unfold leaf_refines_unop_valid. intros. apply bls12_opp_correct; assumption.
Qed.

Theorem bls12_mul_refines :
  leaf_refines_binop_valid bls12_fp_valid bls12_fp_eval
    bls12_mul_impl
    (fun a b => (a * b) mod bls12_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bls12_mul_correct; assumption.
Qed.

Theorem bls12_square_refines :
  leaf_refines_unop_valid bls12_fp_valid bls12_fp_eval
    bls12_square_impl
    (fun a => (a * a) mod bls12_modp).
Proof.
  unfold leaf_refines_unop_valid. intros. apply bls12_square_correct; assumption.
Qed.

(* ================================================================ *)
(* §6. End-to-end theorem                                            *)
(* ================================================================ *)

(** The concrete BLS12-381 leaf_spec. Uses the same BN254 simulation
    infrastructure (the simulation is curve-agnostic). *)
Definition bls12_leaf_spec_concrete :=
  bn254_leaf_spec
    bls12_add_impl
    bls12_sub_impl
    bls12_mul_impl
    bls12_square_impl
    bls12_opp_impl
    (fun _ => bls12_copy_impl (VFp nil))
    (fun _ _ _ => bls12_copy_impl (VFp nil)).

Theorem bls12_tower_correct :
  forall c rs1 rs2,
    cmd_clean c ->
    state_ac_fresh rs1 ->
    bedrock_exec bn254_N bn254_u64_max bls12_leaf_spec_concrete c rs1 rs2 ->
    rust_exec bn254_N bn254_u64_max bls12_leaf_spec_concrete
              (btranslate c) rs1 rs2.
Proof.
  intros c rs1 rs2 Hclean Hfresh Hexec.
  exact (SafeRustSimulation.safe_cmd_correct
           bn254_N bn254_u64_max bls12_leaf_spec_concrete
           c rs1 rs2 Hclean Hfresh Hexec).
Qed.
