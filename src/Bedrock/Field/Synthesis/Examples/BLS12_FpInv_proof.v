(** Proof of fp_inv_correct_ax, replacing the axiom in BLS12_FpInv.v. *)

From Stdlib Require Import ZArith Lia Znumtheory.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpInv.

Local Open Scope Z_scope.
Local Notation p := bls12_p.

Lemma Zmod_sub_zero : forall a b m,
  m <> 0 -> (a - b) mod m = 0 -> a mod m = b mod m.
Proof.
  intros a b m Hm H.
  apply Zmod_divides in H; [| exact Hm].
  destruct H as [k Hk].
  assert (a = b + k * m) by lia.
  subst a. rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Zmod_mod. reflexivity.
Qed.

(** If a ≡ b (mod m), then a*c ≡ b*c (mod m) *)
Lemma Zmul_mod_compat : forall a b c m,
  a mod m = b mod m -> (a * c) mod m = (b * c) mod m.
Proof.
  intros a b c m H.
  destruct (Z.eq_dec m 0) as [->|Hm].
  { rewrite !Zmod_0_r in *. subst. reflexivity. }
  assert (Hdiff : (a - b) mod m = 0).
  { rewrite Zminus_mod, H, Z.sub_diag, Z.mod_0_l; [reflexivity | exact Hm]. }
  apply Zmod_divides in Hdiff; [| exact Hm].
  destruct Hdiff as [k Hk].
  (* Hk : a - b = m * k, so a = b + m * k *)
  replace a with (b + m * k) by lia.
  replace ((b + m * k) * c) with (b * c + k * c * m) by ring.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(** Reduce ((v mod m * c) mod m * x) mod m to (v * x * c) mod m *)
Lemma mod_mul_rearrange : forall v c x m,
  ((v mod m * c) mod m * x) mod m = (v * x * c) mod m.
Proof.
  intros.
  rewrite Zmult_mod_idemp_l with (a := v mod m * c) (b := x).
  replace (v mod m * c * x) with (v mod m * (c * x)) by ring.
  rewrite Zmult_mod_idemp_l with (a := v) (b := c * x).
  f_equal. ring.
Qed.

Theorem fp_inv_correct_proved : forall x,
  0 < x < p ->
  Z.gcd x p = 1 ->
  (fp_inv_spec x * x) mod p = 1.
Proof.
  intros x Hx Hgcd.
  unfold fp_inv_spec.
  set (N := Z.to_nat bls12_divstep_iters).
  destruct (iter_divstep_spec p N 1 p x 0 1) as [[[[d_N f_N] g_N] v_N] r_N] eqn:Espec.
  (* Loop invariant: v_N * x ≡ 2^N * f_N (mod p) *)
  pose proof (iter_invariant p N 1 p x 0 1 x p_pos p_odd) as Hinv.
  assert (Hv0 : (0 * x - p) mod p = 0).
  { replace (0 * x - p) with ((-1) * p) by ring.
    rewrite Z_mod_mult. reflexivity. }
  assert (Hr0 : (1 * x - x) mod p = 0) by (replace (1 * x - x) with 0 by ring; reflexivity).
  specialize (Hinv Hv0 Hr0). rewrite Espec in Hinv.
  destruct Hinv as [Hinv_v _].
  (* Convergence: g_N = 0, f_N = ±1 *)
  pose proof (iter_dfg_agree N p 1 p x 0 1) as Hagree.
  rewrite Espec in Hagree.
  destruct (iter_divstep_dfg N 1 p x) as [[d2 f2] g2] eqn:Edfg.
  destruct Hagree as [_ [Hf_eq Hg_eq]]. subst f2 g2.
  pose proof (by_convergence_dfg x Hx Hgcd) as Hconv.
  unfold N in Edfg. rewrite Edfg in Hconv.
  destruct Hconv as [Hg0 Hf_pm1]. subst g_N.
  assert (Hp : p <> 0) by (pose proof p_pos; lia).
  (* Make p opaque NOW to prevent proof term blowup in modular arithmetic.
     All computational facts (p_pos, p_odd, convergence) are already obtained. *)
  Opaque bls12_p.
  destruct Hf_pm1 as [Hf1 | Hf_neg1].
  - (* f_N = 1 *)
    subst f_N. rewrite Z.mul_1_r in Hinv_v.
    change (1 <? 0) with false. simpl (if false then _ else _).
    assert (Hvx : (v_N * x) mod p = (2 ^ Z.of_nat N) mod p)
      by (apply Zmod_sub_zero; auto).
    rewrite mod_mul_rearrange.
    (* Goal: (v_N * x * precomp_val) mod p = 1 *)
    transitivity ((2 ^ Z.of_nat N * precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hvx. }
    rewrite Z.mul_comm. exact precomp_times_pow2.
  - (* f_N = -1 *)
    subst f_N.
    change (-1 <? 0) with true. simpl (if true then _ else _).
    replace (2 ^ Z.of_nat N * -1) with (-(2 ^ Z.of_nat N)) in Hinv_v by ring.
    assert (Hpvx : ((p - v_N) * x) mod p = (2 ^ Z.of_nat N) mod p).
    { assert (Hvx_neg : (v_N * x) mod p = (-(2 ^ Z.of_nat N)) mod p)
        by (apply Zmod_sub_zero; auto).
      replace ((p - v_N) * x) with (-(v_N * x) + x * p) by ring.
      rewrite Z_mod_plus_full.
      (* Goal: (-(v_N * x)) mod p = (2^N) mod p *)
      rewrite Z.opp_eq_mul_m1.
      (* Goal: (v_N * x * -1) mod p = ... *)
      (* Use Zmul_mod_compat: v_N * x ≡ -(2^N) → v_N * x * (-1) ≡ -(2^N) * (-1) *)
      apply Zmul_mod_compat with (c := -1) in Hvx_neg.
      replace (v_N * x * -1) with ((v_N * x) * -1) by ring.
      rewrite Hvx_neg.
      replace (-(2 ^ Z.of_nat N) * -1) with (2 ^ Z.of_nat N) by ring.
      reflexivity. }
    rewrite mod_mul_rearrange.
    transitivity ((2 ^ Z.of_nat N * precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hpvx. }
    rewrite Z.mul_comm. exact precomp_times_pow2.
Qed.
