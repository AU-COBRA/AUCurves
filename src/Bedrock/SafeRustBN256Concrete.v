(** * SafeRustBN256Concrete.v
 *
 * Instantiates [SafeRustWBWConcrete] for BN256-381.
 *
 * BN256-381 is a 381-bit prime field, so [p_nlimbs = 6] (not 4 as
 * for BN254). Same structure as [SafeRustBN254Concrete.v] — only
 * the constants and side-condition proofs are curve-specific.
 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime_certif.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustBedrockBridge.
Require Import Bedrock.SafeRustLeafRefinement.
Require Import Bedrock.SafeRustWBWConcrete.

(* ================================================================ *)
(* §1. BN256-381 parameters                                          *)
(* ================================================================ *)

Definition bn256_bitwidth : Z := 64%Z.
Definition bn256_nlimbs : nat := 5%nat.  (* 258 bits / 64 = 5 limbs *)
Definition bn256_modp : Z := bn256_modulus.
Definition bn256_r : Z := 2^bn256_bitwidth.
Definition bn256_rprime : Z := Eval vm_compute in (Z.invmod bn256_r bn256_modp).
Definition bn256_mprime : Z := Eval vm_compute in (Z.invmod (- bn256_modp) bn256_r).

(* ================================================================ *)
(* §2. BN256-381 side conditions (discharged by vm_compute)          *)
(* ================================================================ *)

Lemma bn256_bitwidth_big : (0 < bn256_bitwidth)%Z.
Proof. unfold bn256_bitwidth. lia. Qed.

Lemma bn256_m_big : (1 < bn256_modp)%Z.
Proof. unfold bn256_modp, bn256_modulus. lia. Qed.

Lemma bn256_nlimbs_nz : bn256_nlimbs <> 0%nat.
Proof. unfold bn256_nlimbs. discriminate. Qed.

Lemma bn256_m_small : (bn256_modp < bn256_r ^ Z.of_nat bn256_nlimbs)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bn256_rprime_correct :
  ((bn256_r * bn256_rprime) mod bn256_modp = 1)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bn256_mprime_correct :
  ((bn256_modp * bn256_mprime) mod bn256_r = (-1) mod bn256_r)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §3. BN256-381 specializations                                     *)
(* ================================================================ *)

Definition bn256_fp_eval : rust_val TFp -> Z :=
  fp_eval_rust_concrete bn256_bitwidth bn256_nlimbs bn256_modp bn256_mprime.

Definition bn256_fp_valid : rust_val TFp -> Prop :=
  fp_valid bn256_bitwidth bn256_nlimbs bn256_modp.

Definition bn256_add_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  add_impl_concrete bn256_bitwidth bn256_nlimbs bn256_modp.

Definition bn256_sub_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  sub_impl_concrete bn256_bitwidth bn256_nlimbs bn256_modp.

Definition bn256_opp_impl : rust_val TFp -> rust_val TFp :=
  opp_impl_concrete bn256_bitwidth bn256_nlimbs bn256_modp.

Definition bn256_mul_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  mul_impl_concrete bn256_bitwidth bn256_nlimbs bn256_modp bn256_mprime.

Definition bn256_square_impl : rust_val TFp -> rust_val TFp :=
  square_impl_concrete bn256_bitwidth bn256_nlimbs bn256_modp bn256_mprime.

Definition bn256_copy_impl : rust_val TFp -> rust_val TFp :=
  copy_impl_concrete.

(* ================================================================ *)
(* §4. BN256-381 correctness lemmas via parametric instantiation    *)
(* ================================================================ *)

Lemma bn256_copy_correct : forall x,
  bn256_fp_eval (bn256_copy_impl x) = bn256_fp_eval x.
Proof. reflexivity. Qed.

Lemma bn256_add_correct : forall x y,
  bn256_fp_valid x -> bn256_fp_valid y ->
  bn256_fp_eval (bn256_add_impl x y)
  = (bn256_fp_eval x + bn256_fp_eval y) mod bn256_modp.
Proof.
  apply (add_impl_correct bn256_bitwidth bn256_nlimbs bn256_modp
           bn256_rprime bn256_mprime
           bn256_bitwidth_big bn256_m_big bn256_nlimbs_nz bn256_m_small
           bn256_rprime_correct bn256_mprime_correct).
Qed.

Lemma bn256_sub_correct : forall x y,
  bn256_fp_valid x -> bn256_fp_valid y ->
  bn256_fp_eval (bn256_sub_impl x y)
  = (bn256_fp_eval x - bn256_fp_eval y) mod bn256_modp.
Proof.
  apply (sub_impl_correct bn256_bitwidth bn256_nlimbs bn256_modp
           bn256_rprime bn256_mprime
           bn256_bitwidth_big bn256_m_big bn256_nlimbs_nz bn256_m_small
           bn256_rprime_correct bn256_mprime_correct).
Qed.

Lemma bn256_opp_correct : forall x,
  bn256_fp_valid x ->
  bn256_fp_eval (bn256_opp_impl x)
  = (- bn256_fp_eval x) mod bn256_modp.
Proof.
  apply (opp_impl_correct bn256_bitwidth bn256_nlimbs bn256_modp
           bn256_rprime bn256_mprime
           bn256_bitwidth_big bn256_m_big bn256_nlimbs_nz bn256_m_small
           bn256_rprime_correct bn256_mprime_correct).
Qed.

Lemma bn256_mul_correct : forall x y,
  bn256_fp_valid x -> bn256_fp_valid y ->
  bn256_fp_eval (bn256_mul_impl x y)
  = (bn256_fp_eval x * bn256_fp_eval y) mod bn256_modp.
Proof.
  apply (mul_impl_correct bn256_bitwidth bn256_nlimbs bn256_modp
           bn256_rprime bn256_mprime
           bn256_bitwidth_big bn256_m_big bn256_nlimbs_nz bn256_m_small
           bn256_rprime_correct bn256_mprime_correct).
Qed.

Lemma bn256_square_correct : forall x,
  bn256_fp_valid x ->
  bn256_fp_eval (bn256_square_impl x)
  = (bn256_fp_eval x * bn256_fp_eval x) mod bn256_modp.
Proof.
  apply (square_impl_correct bn256_bitwidth bn256_nlimbs bn256_modp
           bn256_rprime bn256_mprime
           bn256_bitwidth_big bn256_m_big bn256_nlimbs_nz bn256_m_small
           bn256_rprime_correct bn256_mprime_correct).
Qed.

(* ================================================================ *)
(* §5. Refinement witnesses                                          *)
(* ================================================================ *)

Theorem bn256_copy_refines :
  leaf_refines_copy_valid bn256_fp_valid bn256_fp_eval bn256_copy_impl.
Proof. unfold leaf_refines_copy_valid. intros. apply bn256_copy_correct. Qed.

Theorem bn256_add_refines :
  leaf_refines_binop_valid bn256_fp_valid bn256_fp_eval
    bn256_add_impl
    (fun a b => (a + b) mod bn256_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bn256_add_correct; assumption.
Qed.

Theorem bn256_sub_refines :
  leaf_refines_binop_valid bn256_fp_valid bn256_fp_eval
    bn256_sub_impl
    (fun a b => (a - b) mod bn256_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bn256_sub_correct; assumption.
Qed.

Theorem bn256_opp_refines :
  leaf_refines_unop_valid bn256_fp_valid bn256_fp_eval
    bn256_opp_impl
    (fun a => (- a) mod bn256_modp).
Proof.
  unfold leaf_refines_unop_valid. intros. apply bn256_opp_correct; assumption.
Qed.

Theorem bn256_mul_refines :
  leaf_refines_binop_valid bn256_fp_valid bn256_fp_eval
    bn256_mul_impl
    (fun a b => (a * b) mod bn256_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bn256_mul_correct; assumption.
Qed.

Theorem bn256_square_refines :
  leaf_refines_unop_valid bn256_fp_valid bn256_fp_eval
    bn256_square_impl
    (fun a => (a * a) mod bn256_modp).
Proof.
  unfold leaf_refines_unop_valid. intros. apply bn256_square_correct; assumption.
Qed.

(* ================================================================ *)
(* §6. End-to-end theorem                                            *)
(* ================================================================ *)

(** The concrete BN256-381 leaf_spec. Uses the same BN254 simulation
    infrastructure (the simulation is curve-agnostic). *)
Definition bn256_leaf_spec_concrete :=
  bn254_leaf_spec
    bn256_add_impl
    bn256_sub_impl
    bn256_mul_impl
    bn256_square_impl
    bn256_opp_impl
    (fun _ => bn256_copy_impl (VFp nil))
    (fun _ _ _ => bn256_copy_impl (VFp nil)).

Theorem bn256_tower_correct :
  forall c rs1 rs2,
    cmd_clean c ->
    state_ac_fresh rs1 ->
    bedrock_exec bn254_N bn254_u64_max bn256_leaf_spec_concrete c rs1 rs2 ->
    rust_exec bn254_N bn254_u64_max bn256_leaf_spec_concrete
              (btranslate c) rs1 rs2.
Proof.
  intros c rs1 rs2 Hclean Hfresh Hexec.
  exact (SafeRustSimulation.safe_cmd_correct
           bn254_N bn254_u64_max bn256_leaf_spec_concrete
           c rs1 rs2 Hclean Hfresh Hexec).
Qed.
