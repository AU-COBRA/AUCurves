(** * SafeRustBN446Concrete.v
 *
 * Instantiates [SafeRustWBWConcrete] for BN446-381.
 *
 * BN446-381 is a 381-bit prime field, so [p_nlimbs = 6] (not 4 as
 * for BN254). Same structure as [SafeRustBN254Concrete.v] — only
 * the constants and side-condition proofs are curve-specific.
 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime_certif.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustBedrockBridge.
Require Import Bedrock.SafeRustLeafRefinement.
Require Import Bedrock.SafeRustWBWConcrete.

(* ================================================================ *)
(* §1. BN446-381 parameters                                          *)
(* ================================================================ *)

Definition bn446_bitwidth : Z := 64%Z.
Definition bn446_nlimbs : nat := 7%nat.  (* 446 bits / 64 = 7 limbs *)
Definition bn446_modp : Z := bn446_modulus.
Definition bn446_r : Z := 2^bn446_bitwidth.
Definition bn446_rprime : Z := Eval vm_compute in (Z.invmod bn446_r bn446_modp).
Definition bn446_mprime : Z := Eval vm_compute in (Z.invmod (- bn446_modp) bn446_r).

(* ================================================================ *)
(* §2. BN446-381 side conditions (discharged by vm_compute)          *)
(* ================================================================ *)

Lemma bn446_bitwidth_big : (0 < bn446_bitwidth)%Z.
Proof. unfold bn446_bitwidth. lia. Qed.

Lemma bn446_m_big : (1 < bn446_modp)%Z.
Proof. unfold bn446_modp, bn446_modulus. lia. Qed.

Lemma bn446_nlimbs_nz : bn446_nlimbs <> 0%nat.
Proof. unfold bn446_nlimbs. discriminate. Qed.

Lemma bn446_m_small : (bn446_modp < bn446_r ^ Z.of_nat bn446_nlimbs)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bn446_rprime_correct :
  ((bn446_r * bn446_rprime) mod bn446_modp = 1)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bn446_mprime_correct :
  ((bn446_modp * bn446_mprime) mod bn446_r = (-1) mod bn446_r)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §3. BN446-381 specializations                                     *)
(* ================================================================ *)

Definition bn446_fp_eval : rust_val TFp -> Z :=
  fp_eval_rust_concrete bn446_bitwidth bn446_nlimbs bn446_modp bn446_mprime.

Definition bn446_fp_valid : rust_val TFp -> Prop :=
  fp_valid bn446_bitwidth bn446_nlimbs bn446_modp.

Definition bn446_add_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  add_impl_concrete bn446_bitwidth bn446_nlimbs bn446_modp.

Definition bn446_sub_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  sub_impl_concrete bn446_bitwidth bn446_nlimbs bn446_modp.

Definition bn446_opp_impl : rust_val TFp -> rust_val TFp :=
  opp_impl_concrete bn446_bitwidth bn446_nlimbs bn446_modp.

Definition bn446_mul_impl : rust_val TFp -> rust_val TFp -> rust_val TFp :=
  mul_impl_concrete bn446_bitwidth bn446_nlimbs bn446_modp bn446_mprime.

Definition bn446_square_impl : rust_val TFp -> rust_val TFp :=
  square_impl_concrete bn446_bitwidth bn446_nlimbs bn446_modp bn446_mprime.

Definition bn446_copy_impl : rust_val TFp -> rust_val TFp :=
  copy_impl_concrete.

(* ================================================================ *)
(* §4. BN446-381 correctness lemmas via parametric instantiation    *)
(* ================================================================ *)

Lemma bn446_copy_correct : forall x,
  bn446_fp_eval (bn446_copy_impl x) = bn446_fp_eval x.
Proof. reflexivity. Qed.

Lemma bn446_add_correct : forall x y,
  bn446_fp_valid x -> bn446_fp_valid y ->
  bn446_fp_eval (bn446_add_impl x y)
  = (bn446_fp_eval x + bn446_fp_eval y) mod bn446_modp.
Proof.
  apply (add_impl_correct bn446_bitwidth bn446_nlimbs bn446_modp
           bn446_rprime bn446_mprime
           bn446_bitwidth_big bn446_m_big bn446_nlimbs_nz bn446_m_small
           bn446_rprime_correct bn446_mprime_correct).
Qed.

Lemma bn446_sub_correct : forall x y,
  bn446_fp_valid x -> bn446_fp_valid y ->
  bn446_fp_eval (bn446_sub_impl x y)
  = (bn446_fp_eval x - bn446_fp_eval y) mod bn446_modp.
Proof.
  apply (sub_impl_correct bn446_bitwidth bn446_nlimbs bn446_modp
           bn446_rprime bn446_mprime
           bn446_bitwidth_big bn446_m_big bn446_nlimbs_nz bn446_m_small
           bn446_rprime_correct bn446_mprime_correct).
Qed.

Lemma bn446_opp_correct : forall x,
  bn446_fp_valid x ->
  bn446_fp_eval (bn446_opp_impl x)
  = (- bn446_fp_eval x) mod bn446_modp.
Proof.
  apply (opp_impl_correct bn446_bitwidth bn446_nlimbs bn446_modp
           bn446_rprime bn446_mprime
           bn446_bitwidth_big bn446_m_big bn446_nlimbs_nz bn446_m_small
           bn446_rprime_correct bn446_mprime_correct).
Qed.

Lemma bn446_mul_correct : forall x y,
  bn446_fp_valid x -> bn446_fp_valid y ->
  bn446_fp_eval (bn446_mul_impl x y)
  = (bn446_fp_eval x * bn446_fp_eval y) mod bn446_modp.
Proof.
  apply (mul_impl_correct bn446_bitwidth bn446_nlimbs bn446_modp
           bn446_rprime bn446_mprime
           bn446_bitwidth_big bn446_m_big bn446_nlimbs_nz bn446_m_small
           bn446_rprime_correct bn446_mprime_correct).
Qed.

Lemma bn446_square_correct : forall x,
  bn446_fp_valid x ->
  bn446_fp_eval (bn446_square_impl x)
  = (bn446_fp_eval x * bn446_fp_eval x) mod bn446_modp.
Proof.
  apply (square_impl_correct bn446_bitwidth bn446_nlimbs bn446_modp
           bn446_rprime bn446_mprime
           bn446_bitwidth_big bn446_m_big bn446_nlimbs_nz bn446_m_small
           bn446_rprime_correct bn446_mprime_correct).
Qed.

(* ================================================================ *)
(* §5. Refinement witnesses                                          *)
(* ================================================================ *)

Theorem bn446_copy_refines :
  leaf_refines_copy_valid bn446_fp_valid bn446_fp_eval bn446_copy_impl.
Proof. unfold leaf_refines_copy_valid. intros. apply bn446_copy_correct. Qed.

Theorem bn446_add_refines :
  leaf_refines_binop_valid bn446_fp_valid bn446_fp_eval
    bn446_add_impl
    (fun a b => (a + b) mod bn446_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bn446_add_correct; assumption.
Qed.

Theorem bn446_sub_refines :
  leaf_refines_binop_valid bn446_fp_valid bn446_fp_eval
    bn446_sub_impl
    (fun a b => (a - b) mod bn446_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bn446_sub_correct; assumption.
Qed.

Theorem bn446_opp_refines :
  leaf_refines_unop_valid bn446_fp_valid bn446_fp_eval
    bn446_opp_impl
    (fun a => (- a) mod bn446_modp).
Proof.
  unfold leaf_refines_unop_valid. intros. apply bn446_opp_correct; assumption.
Qed.

Theorem bn446_mul_refines :
  leaf_refines_binop_valid bn446_fp_valid bn446_fp_eval
    bn446_mul_impl
    (fun a b => (a * b) mod bn446_modp).
Proof.
  unfold leaf_refines_binop_valid. intros. apply bn446_mul_correct; assumption.
Qed.

Theorem bn446_square_refines :
  leaf_refines_unop_valid bn446_fp_valid bn446_fp_eval
    bn446_square_impl
    (fun a => (a * a) mod bn446_modp).
Proof.
  unfold leaf_refines_unop_valid. intros. apply bn446_square_correct; assumption.
Qed.

(* ================================================================ *)
(* §6. End-to-end theorem                                            *)
(* ================================================================ *)

(** The concrete BN446-381 leaf_spec. Uses the same BN254 simulation
    infrastructure (the simulation is curve-agnostic). *)
Definition bn446_leaf_spec_concrete :=
  bn254_leaf_spec
    bn446_add_impl
    bn446_sub_impl
    bn446_mul_impl
    bn446_square_impl
    bn446_opp_impl
    (fun _ => bn446_copy_impl (VFp nil))
    (fun _ _ _ => bn446_copy_impl (VFp nil)).

Theorem bn446_tower_correct :
  forall c rs1 rs2,
    cmd_clean c ->
    state_ac_fresh rs1 ->
    bedrock_exec bn254_N bn254_u64_max bn446_leaf_spec_concrete c rs1 rs2 ->
    rust_exec bn254_N bn254_u64_max bn446_leaf_spec_concrete
              (btranslate c) rs1 rs2.
Proof.
  intros c rs1 rs2 Hclean Hfresh Hexec.
  exact (SafeRustSimulation.safe_cmd_correct
           bn254_N bn254_u64_max bn446_leaf_spec_concrete
           c rs1 rs2 Hclean Hfresh Hexec).
Qed.
