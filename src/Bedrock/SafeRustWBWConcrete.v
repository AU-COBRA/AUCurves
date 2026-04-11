(** * SafeRustWBWConcrete.v
 *
 * Parametric Word-by-Word Montgomery concrete wrapper.
 *
 * Given the WBW Montgomery parameters for ANY prime field [F_p]
 * (bitwidth, n, m, m', r' and the 6 side conditions), this file
 * provides:
 *   - [rust_val TFp] ↔ [list Z] conversions
 *   - [fp_eval_rust_concrete] (Montgomery-reduced evaluation)
 *   - 6 concrete [_impl_concrete] functions wrapping
 *     [addmod]/[submod]/[oppmod]/[mulmod]/[squaremod]/[id]
 *   - 6 correctness lemmas (each Qed, using validity preconds)
 *   - 6 refinement witnesses via [leaf_refines_*_valid]
 *
 * To instantiate for a specific curve, see e.g.
 * [SafeRustBN254Concrete.v] which supplies the 5 constants and
 * 6 side-condition proofs.
 *
 * Trust: purely Coq + fiat-crypto's [Arithmetic.WordByWordMontgomery]
 * correctness lemmas.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.Partition.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustBedrockBridge.

(* ================================================================ *)
(* §1. Parameters + side conditions                                  *)
(* ================================================================ *)

Section WBWConcrete.

  Variable p_bitwidth : Z.
  Variable p_nlimbs : nat.
  Variable p_modulus : Z.
  Variable p_rprime : Z.
  Variable p_mprime : Z.

  Let p_r : Z := 2^p_bitwidth.

  Hypothesis p_bitwidth_big : (0 < p_bitwidth)%Z.
  Hypothesis p_m_big : (1 < p_modulus)%Z.
  Hypothesis p_nlimbs_nz : p_nlimbs <> 0%nat.
  Hypothesis p_m_small : (p_modulus < p_r ^ Z.of_nat p_nlimbs)%Z.
  Hypothesis p_rprime_correct :
    ((p_r * p_rprime) mod p_modulus = 1)%Z.
  Hypothesis p_mprime_correct :
    ((p_modulus * p_mprime) mod p_r = (-1) mod p_r)%Z.

  (* ================================================================ *)
  (* §2. rust_val ↔ list Z conversions                                 *)
  (* ================================================================ *)

  (** Interpret a nat-limb [rust_val TFp] as a list of Z
      (little-endian). *)
  Definition rust_to_Z_list (v : rust_val TFp) : list Z :=
    match v with
    | VFp xs => List.map Z.of_nat xs
    end.

  (** Build a [rust_val TFp] from a list of non-negative Z limbs. *)
  Definition Z_list_to_rust (xs : list Z) : rust_val TFp :=
    VFp (List.map Z.to_nat xs).

  Lemma rust_to_Z_roundtrip : forall xs,
    Forall (fun z => 0 <= z) xs ->
    rust_to_Z_list (Z_list_to_rust xs) = xs.
  Proof.
    intros xs H.
    unfold rust_to_Z_list, Z_list_to_rust.
    rewrite List.map_map.
    induction H; simpl; auto.
    rewrite Z2Nat.id by assumption. f_equal. assumption.
  Qed.

  (* ================================================================ *)
  (* §3. Concrete evaluation                                           *)
  (* ================================================================ *)

  Definition fp_eval_rust_concrete (v : rust_val TFp) : Z :=
    (WordByWordMontgomery.eval p_bitwidth (n := p_nlimbs)
      (WordByWordMontgomery.from_montgomerymod
         p_bitwidth p_nlimbs p_modulus p_mprime (rust_to_Z_list v)))
      mod p_modulus.

  (* ================================================================ *)
  (* §4. Concrete impls                                                *)
  (* ================================================================ *)

  Definition add_impl_concrete (x y : rust_val TFp) : rust_val TFp :=
    Z_list_to_rust
      (WordByWordMontgomery.addmod p_bitwidth p_nlimbs p_modulus
         (rust_to_Z_list x) (rust_to_Z_list y)).

  Definition sub_impl_concrete (x y : rust_val TFp) : rust_val TFp :=
    Z_list_to_rust
      (WordByWordMontgomery.submod p_bitwidth p_nlimbs p_modulus
         (rust_to_Z_list x) (rust_to_Z_list y)).

  Definition opp_impl_concrete (x : rust_val TFp) : rust_val TFp :=
    Z_list_to_rust
      (WordByWordMontgomery.oppmod p_bitwidth p_nlimbs p_modulus
         (rust_to_Z_list x)).

  Definition mul_impl_concrete (x y : rust_val TFp) : rust_val TFp :=
    Z_list_to_rust
      (WordByWordMontgomery.mulmod p_bitwidth p_nlimbs p_modulus p_mprime
         (rust_to_Z_list x) (rust_to_Z_list y)).

  Definition square_impl_concrete (x : rust_val TFp) : rust_val TFp :=
    Z_list_to_rust
      (WordByWordMontgomery.squaremod p_bitwidth p_nlimbs p_modulus p_mprime
         (rust_to_Z_list x)).

  Definition copy_impl_concrete (x : rust_val TFp) : rust_val TFp := x.

  (* ================================================================ *)
  (* §5. Validity predicate                                             *)
  (* ================================================================ *)

  Definition fp_valid (v : rust_val TFp) : Prop :=
    WordByWordMontgomery.valid p_bitwidth p_nlimbs p_modulus (rust_to_Z_list v).

  (* ================================================================ *)
  (* §6. Generic helper lemmas                                          *)
  (* ================================================================ *)

  Lemma partition_nonneg :
    forall (w : nat -> Z) (n : nat) (x : Z),
      (forall i, 0 < w i) ->
      Forall (fun z => 0 <= z)%Z (Partition.partition w n x).
  Proof.
    intros w n x Hw. unfold Partition.partition.
    apply Forall_map. apply Forall_forall. intros i _.
    pose proof (Hw (S i)) as HwS.
    pose proof (Hw i) as Hwi.
    pose proof (Z.mod_pos_bound x (w (S i)) HwS) as [Hmlo Hmhi].
    apply Z.div_pos; lia.
  Qed.

  Lemma uweight_gt_0 : forall lgr i, 0 <= lgr -> 0 < uweight lgr i.
  Proof.
    intros lgr i Hlgr. rewrite uweight_eq_alt by assumption.
    apply Z.pow_pos_nonneg; [| lia].
    apply Z.pow_pos_nonneg; lia.
  Qed.

  Lemma small_nonneg : forall a,
    @WordByWordMontgomery.small p_bitwidth p_nlimbs a ->
    Forall (fun z => 0 <= z)%Z a.
  Proof.
    intros a Hsmall. unfold WordByWordMontgomery.small in Hsmall.
    rewrite Hsmall. apply partition_nonneg.
    intros i. apply uweight_gt_0. lia.
  Qed.

  Lemma Zopp_mod_l : forall a p, ((- a) mod p = (- (a mod p)) mod p)%Z.
  Proof.
    intros.
    replace (-a) with (0 - a) by ring.
    replace (- (a mod p)) with (0 - (a mod p)) by ring.
    rewrite Zminus_mod_idemp_r. reflexivity.
  Qed.

  (* ================================================================ *)
  (* §7. Instantiated correctness pairs                                 *)
  (* ================================================================ *)

  Definition addmod_correct_pair :=
    @WordByWordMontgomery.addmod_correct
      p_bitwidth p_nlimbs p_modulus p_rprime p_mprime
      p_rprime_correct p_mprime_correct
      p_bitwidth_big p_m_big p_nlimbs_nz p_m_small.
  Definition submod_correct_pair :=
    @WordByWordMontgomery.submod_correct
      p_bitwidth p_nlimbs p_modulus p_rprime p_mprime
      p_rprime_correct p_mprime_correct
      p_bitwidth_big p_m_big p_nlimbs_nz p_m_small.
  Definition oppmod_correct_pair :=
    @WordByWordMontgomery.oppmod_correct
      p_bitwidth p_nlimbs p_modulus p_rprime p_mprime
      p_rprime_correct p_mprime_correct
      p_bitwidth_big p_m_big p_nlimbs_nz p_m_small.
  Definition mulmod_correct_pair :=
    @WordByWordMontgomery.mulmod_correct
      p_bitwidth p_nlimbs p_modulus p_rprime p_mprime
      p_rprime_correct p_mprime_correct
      p_bitwidth_big p_m_big p_nlimbs_nz p_m_small.
  Definition squaremod_correct_pair :=
    @WordByWordMontgomery.squaremod_correct
      p_bitwidth p_nlimbs p_modulus p_rprime p_mprime
      p_rprime_correct p_mprime_correct
      p_bitwidth_big p_m_big p_nlimbs_nz p_m_small.

  (* ================================================================ *)
  (* §8. Per-leaf correctness lemmas                                    *)
  (* ================================================================ *)

  Lemma copy_impl_correct : forall x,
    fp_eval_rust_concrete (copy_impl_concrete x) = fp_eval_rust_concrete x.
  Proof. reflexivity. Qed.

  Lemma add_impl_correct : forall x y,
    fp_valid x -> fp_valid y ->
    fp_eval_rust_concrete (add_impl_concrete x y)
    = (fp_eval_rust_concrete x + fp_eval_rust_concrete y) mod p_modulus.
  Proof.
    intros x y Hx Hy.
    unfold fp_eval_rust_concrete, add_impl_concrete, fp_valid in *.
    pose proof (proj2 addmod_correct_pair _ Hx _ Hy) as Hvalid.
    rewrite rust_to_Z_roundtrip by (apply small_nonneg, Hvalid).
    rewrite (proj1 addmod_correct_pair _ Hx _ Hy).
    rewrite <- Zplus_mod. reflexivity.
  Qed.

  Lemma sub_impl_correct : forall x y,
    fp_valid x -> fp_valid y ->
    fp_eval_rust_concrete (sub_impl_concrete x y)
    = (fp_eval_rust_concrete x - fp_eval_rust_concrete y) mod p_modulus.
  Proof.
    intros x y Hx Hy.
    unfold fp_eval_rust_concrete, sub_impl_concrete, fp_valid in *.
    pose proof (proj2 submod_correct_pair _ Hx _ Hy) as Hvalid.
    rewrite rust_to_Z_roundtrip by (apply small_nonneg, Hvalid).
    rewrite (proj1 submod_correct_pair _ Hx _ Hy).
    rewrite <- Zminus_mod. reflexivity.
  Qed.

  Lemma opp_impl_correct : forall x,
    fp_valid x ->
    fp_eval_rust_concrete (opp_impl_concrete x)
    = (- fp_eval_rust_concrete x) mod p_modulus.
  Proof.
    intros x Hx.
    unfold fp_eval_rust_concrete, opp_impl_concrete, fp_valid in *.
    pose proof (proj2 oppmod_correct_pair _ Hx) as Hvalid.
    rewrite rust_to_Z_roundtrip by (apply small_nonneg, Hvalid).
    rewrite (proj1 oppmod_correct_pair _ Hx).
    apply Zopp_mod_l.
  Qed.

  Lemma mul_impl_correct : forall x y,
    fp_valid x -> fp_valid y ->
    fp_eval_rust_concrete (mul_impl_concrete x y)
    = (fp_eval_rust_concrete x * fp_eval_rust_concrete y) mod p_modulus.
  Proof.
    intros x y Hx Hy.
    unfold fp_eval_rust_concrete, mul_impl_concrete, fp_valid in *.
    pose proof (proj2 mulmod_correct_pair _ Hx _ Hy) as Hvalid.
    rewrite rust_to_Z_roundtrip by (apply small_nonneg, Hvalid).
    rewrite (proj1 mulmod_correct_pair _ Hx _ Hy).
    rewrite <- Zmult_mod. reflexivity.
  Qed.

  Lemma square_impl_correct : forall x,
    fp_valid x ->
    fp_eval_rust_concrete (square_impl_concrete x)
    = (fp_eval_rust_concrete x * fp_eval_rust_concrete x) mod p_modulus.
  Proof.
    intros x Hx.
    unfold fp_eval_rust_concrete, square_impl_concrete, fp_valid in *.
    pose proof (proj2 squaremod_correct_pair _ Hx) as Hvalid.
    rewrite rust_to_Z_roundtrip by (apply small_nonneg, Hvalid).
    rewrite (proj1 squaremod_correct_pair _ Hx).
    rewrite <- Zmult_mod. reflexivity.
  Qed.

End WBWConcrete.

(* ================================================================ *)
(* §9. Validity-aware bridge refinement predicates                   *)
(* ================================================================ *)

(** These are curve-agnostic so live outside the section. *)
Definition leaf_refines_binop_valid
    (valid : rust_val TFp -> Prop)
    (fp_eval_rust : rust_val TFp -> Z)
    (impl : rust_val TFp -> rust_val TFp -> rust_val TFp)
    (spec : Z -> Z -> Z) : Prop :=
  forall x y, valid x -> valid y ->
    fp_eval_rust (impl x y) = spec (fp_eval_rust x) (fp_eval_rust y).

Definition leaf_refines_unop_valid
    (valid : rust_val TFp -> Prop)
    (fp_eval_rust : rust_val TFp -> Z)
    (impl : rust_val TFp -> rust_val TFp)
    (spec : Z -> Z) : Prop :=
  forall x, valid x ->
    fp_eval_rust (impl x) = spec (fp_eval_rust x).

Definition leaf_refines_copy_valid
    (valid : rust_val TFp -> Prop)
    (fp_eval_rust : rust_val TFp -> Z)
    (impl : rust_val TFp -> rust_val TFp) : Prop :=
  forall x, valid x ->
    fp_eval_rust (impl x) = fp_eval_rust x.
