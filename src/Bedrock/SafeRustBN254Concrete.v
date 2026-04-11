(** * SafeRustBN254Concrete.v
 *
 * Instantiates [SafeRustWBWConcrete] for BN254.
 *
 * Supplies the 5 curve-specific constants and 6 side-condition
 * proofs; inherits all curve-agnostic definitions and correctness
 * lemmas from [SafeRustWBWConcrete].
 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime_certif.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustBedrockBridge.
Require Import Bedrock.SafeRustLeafRefinement.
Require Import Bedrock.SafeRustWBWConcrete.

(* ================================================================ *)
(* §1. BN254 parameters                                              *)
(* ================================================================ *)

Definition bn254_bitwidth : Z := 64%Z.
Definition bn254_nlimbs : nat := 4%nat.
Definition bn254_modp : Z := bn254_modulus.
Definition bn254_r : Z := 2^bn254_bitwidth.
Definition bn254_rprime : Z := Eval vm_compute in (Z.invmod bn254_r bn254_modp).
Definition bn254_mprime : Z := Eval vm_compute in (Z.invmod (- bn254_modp) bn254_r).

(* ================================================================ *)
(* §2. BN254 side conditions (discharged by vm_compute)              *)
(* ================================================================ *)

Lemma bn254_bitwidth_big : (0 < bn254_bitwidth)%Z.
Proof. unfold bn254_bitwidth. lia. Qed.

Lemma bn254_m_big : (1 < bn254_modp)%Z.
Proof. unfold bn254_modp, bn254_modulus. lia. Qed.

Lemma bn254_nlimbs_nz : bn254_nlimbs <> 0%nat.
Proof. unfold bn254_nlimbs. discriminate. Qed.

Lemma bn254_m_small : (bn254_modp < bn254_r ^ Z.of_nat bn254_nlimbs)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bn254_rprime_correct :
  ((bn254_r * bn254_rprime) mod bn254_modp = 1)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bn254_mprime_correct :
  ((bn254_modp * bn254_mprime) mod bn254_r = (-1) mod bn254_r)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §3. BN254 specializations                                          *)
(* ================================================================ *)

(** Concrete BN254 definitions by specialization of the parametric
    wrapper. *)

Definition bn254_fp_eval : rust_val TFp -> Z :=
  fp_eval_rust_concrete bn254_bitwidth bn254_nlimbs bn254_modp bn254_mprime.

Definition bn254_fp_valid : rust_val TFp -> Prop :=
  fp_valid bn254_bitwidth bn254_nlimbs bn254_modp.

Definition bn254_add_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  add_impl_concrete bn254_bitwidth bn254_nlimbs bn254_modp.

Definition bn254_sub_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  sub_impl_concrete bn254_bitwidth bn254_nlimbs bn254_modp.

Definition bn254_opp_impl : rust_val TFp -> rust_val TFp :=
  opp_impl_concrete bn254_bitwidth bn254_nlimbs bn254_modp.

Definition bn254_mul_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  mul_impl_concrete bn254_bitwidth bn254_nlimbs bn254_modp bn254_mprime.

Definition bn254_square_impl : rust_val TFp -> rust_val TFp :=
  square_impl_concrete bn254_bitwidth bn254_nlimbs bn254_modp bn254_mprime.

Definition bn254_copy_impl : rust_val TFp -> rust_val TFp :=
  copy_impl_concrete.

(* ================================================================ *)
(* §4. BN254 correctness lemmas via parametric instantiation         *)
(* ================================================================ *)

Lemma bn254_copy_correct : forall x,
  bn254_fp_eval (bn254_copy_impl x) = bn254_fp_eval x.
Proof. reflexivity. Qed.

Lemma bn254_add_correct : forall x y,
  bn254_fp_valid x -> bn254_fp_valid y ->
  bn254_fp_eval (bn254_add_impl x y)
  = (bn254_fp_eval x + bn254_fp_eval y) mod bn254_modp.
Proof.
  apply (add_impl_correct bn254_bitwidth bn254_nlimbs bn254_modp
           bn254_rprime bn254_mprime
           bn254_bitwidth_big bn254_m_big bn254_nlimbs_nz bn254_m_small
           bn254_rprime_correct bn254_mprime_correct).
Qed.

Lemma bn254_sub_correct : forall x y,
  bn254_fp_valid x -> bn254_fp_valid y ->
  bn254_fp_eval (bn254_sub_impl x y)
  = (bn254_fp_eval x - bn254_fp_eval y) mod bn254_modp.
Proof.
  apply (sub_impl_correct bn254_bitwidth bn254_nlimbs bn254_modp
           bn254_rprime bn254_mprime
           bn254_bitwidth_big bn254_m_big bn254_nlimbs_nz bn254_m_small
           bn254_rprime_correct bn254_mprime_correct).
Qed.

Lemma bn254_opp_correct : forall x,
  bn254_fp_valid x ->
  bn254_fp_eval (bn254_opp_impl x)
  = (- bn254_fp_eval x) mod bn254_modp.
Proof.
  apply (opp_impl_correct bn254_bitwidth bn254_nlimbs bn254_modp
           bn254_rprime bn254_mprime
           bn254_bitwidth_big bn254_m_big bn254_nlimbs_nz bn254_m_small
           bn254_rprime_correct bn254_mprime_correct).
Qed.

Lemma bn254_mul_correct : forall x y,
  bn254_fp_valid x -> bn254_fp_valid y ->
  bn254_fp_eval (bn254_mul_impl x y)
  = (bn254_fp_eval x * bn254_fp_eval y) mod bn254_modp.
Proof.
  apply (mul_impl_correct bn254_bitwidth bn254_nlimbs bn254_modp
           bn254_rprime bn254_mprime
           bn254_bitwidth_big bn254_m_big bn254_nlimbs_nz bn254_m_small
           bn254_rprime_correct bn254_mprime_correct).
Qed.

Lemma bn254_square_correct : forall x,
  bn254_fp_valid x ->
  bn254_fp_eval (bn254_square_impl x)
  = (bn254_fp_eval x * bn254_fp_eval x) mod bn254_modp.
Proof.
  apply (square_impl_correct bn254_bitwidth bn254_nlimbs bn254_modp
           bn254_rprime bn254_mprime
           bn254_bitwidth_big bn254_m_big bn254_nlimbs_nz bn254_m_small
           bn254_rprime_correct bn254_mprime_correct).
Qed.

(* ================================================================ *)
(* §5. Refinement witnesses                                           *)
(* ================================================================ *)

Theorem bn254_copy_refines :
  leaf_refines_copy_valid bn254_fp_valid bn254_fp_eval bn254_copy_impl.
Proof. unfold leaf_refines_copy_valid. intros. apply bn254_copy_correct. Qed.

Theorem bn254_add_refines :
  leaf_refines_binop_valid bn254_fp_valid bn254_fp_eval
    bn254_add_impl
    (fun a b => (a + b) mod bn254_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bn254_add_correct; assumption.
Qed.

Theorem bn254_sub_refines :
  leaf_refines_binop_valid bn254_fp_valid bn254_fp_eval
    bn254_sub_impl
    (fun a b => (a - b) mod bn254_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bn254_sub_correct; assumption.
Qed.

Theorem bn254_opp_refines :
  leaf_refines_unop_valid bn254_fp_valid bn254_fp_eval
    bn254_opp_impl
    (fun a => (- a) mod bn254_modp).
Proof.
  unfold leaf_refines_unop_valid. intros. apply bn254_opp_correct; assumption.
Qed.

Theorem bn254_mul_refines :
  leaf_refines_binop_valid bn254_fp_valid bn254_fp_eval
    bn254_mul_impl
    (fun a b => (a * b) mod bn254_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bn254_mul_correct; assumption.
Qed.

Theorem bn254_square_refines :
  leaf_refines_unop_valid bn254_fp_valid bn254_fp_eval
    bn254_square_impl
    (fun a => (a * a) mod bn254_modp).
Proof.
  unfold leaf_refines_unop_valid. intros. apply bn254_square_correct; assumption.
Qed.

(* ================================================================ *)
(* §6. End-to-end theorem                                             *)
(* ================================================================ *)

(** The concrete BN254 leaf_spec built from our 7 concrete impls. *)
Definition bn254_leaf_spec_concrete :=
  bn254_leaf_spec
    bn254_add_impl
    bn254_sub_impl
    bn254_mul_impl
    bn254_square_impl
    bn254_opp_impl
    (fun _ => bn254_copy_impl (VFp nil))  (* from_word placeholder *)
    (fun _ _ _ => bn254_copy_impl (VFp nil)).  (* select_znz placeholder *)

(** End-to-end theorem: the simulation applied with concrete impls. *)
Theorem bn254_tower_correct :
  forall c rs1 rs2,
    cmd_clean c ->
    state_ac_fresh rs1 ->
    bedrock_exec bn254_N bn254_u64_max bn254_leaf_spec_concrete c rs1 rs2 ->
    rust_exec bn254_N bn254_u64_max bn254_leaf_spec_concrete
              (btranslate c) rs1 rs2.
Proof.
  intros c rs1 rs2 Hclean Hfresh Hexec.
  exact (SafeRustSimulation.safe_cmd_correct
           bn254_N bn254_u64_max bn254_leaf_spec_concrete
           c rs1 rs2 Hclean Hfresh Hexec).
Qed.
