(** * Closes [BN256_FpInv.by_convergence_dfg_bn256] axiom via the existing bridge.

    Mirrors [BN254_FpInv_closed.v] for BN256.  Composes:

    - The generic [divsteps_bridge.oconnor_bridge] (parametric in the
      prime [M] and iteration count [N]),
    - The BN256-specific cert axiom [divsteps_bn256.bn256_certificate]
      (741 iterations),
    - A re-proof of the convergence-monotone lemma for BN256
      (parallel to [divsteps_bridge.convergence_monotone] which is
      hardcoded to BLS12), with
    - A trivial [iter_divstep_dfg_eq] (the two definitions in
      [divsteps_bridge.v] and [BN256_FpInv.v] are syntactically
      identical → defining-equation reflexivity).

    Result: [by_convergence_dfg_bn256_closed] has the exact statement
    of [BN256_FpInv.by_convergence_dfg_bn256], discharging the axiom.

    Net axiom in the chain: just [bn256_certificate] (axiomatized in
    [divsteps_bn256.v] in parallel to [bls12_certificate] /
    [bn254_certificate]). *)

From Stdlib Require Import ZArith Lia Znumtheory.
Require Import divsteps_def.
Require Import divsteps_bridge.
Require Import divsteps_bn256.
Require Import Crypto.Arithmetic.BYInv.
Require Import Bedrock.Field.Synthesis.Examples.BN256_FpInv.

Local Open Scope Z_scope.

(** The two [iter_divstep_dfg] definitions (one in [divsteps_bridge.v],
    one in [BN256_FpInv.v]) have identical bodies; they coincide. *)
Lemma iter_divstep_dfg_eq : forall n d f g,
  divsteps_bridge.iter_divstep_dfg n d f g =
  BN256_FpInv.iter_divstep_dfg n d f g.
Proof.
  induction n as [|k IH]; intros d f g; simpl; [reflexivity|].
  destruct (divstep_spec d f g) as [[d' f'] g'].
  apply IH.
Qed.

(** *** BN256-specific O'Connor convergence (parallel to
    [divsteps_bridge.oconnor_implies_convergence] for BLS12). *)
Theorem oconnor_implies_convergence_bn256 : forall x,
  0 < x < BN256_FpInv.bn256_p ->
  Z.gcd x BN256_FpInv.bn256_p = 1 ->
  let '(_, f_N, g_N) :=
    divsteps_bridge.iter_divstep_dfg (N.to_nat 741) 1 BN256_FpInv.bn256_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  apply (divsteps_bridge.oconnor_bridge 741 divsteps_bn256.bn256_M).
  - exists (BN256_FpInv.bn256_p / 2). vm_compute. reflexivity.
  - unfold divsteps_bn256.bn256_M, divsteps_bn256.bn256_p, BN256_FpInv.bn256_p. lia.
  - lia.
  - apply Zgcd_1_rel_prime. rewrite Z.gcd_comm. exact Hgcd.
  - exact divsteps_bn256.bn256_certificate.
Qed.

Theorem convergence_monotone_bn256 : forall N x,
  (N.to_nat 741 <= N)%nat ->
  0 < x < BN256_FpInv.bn256_p ->
  Z.gcd x BN256_FpInv.bn256_p = 1 ->
  let '(_, f_N, g_N) := divsteps_bridge.iter_divstep_dfg N 1 BN256_FpInv.bn256_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros N x HN Hx Hgcd.
  pose proof (oconnor_implies_convergence_bn256 x Hx Hgcd) as H741.
  destruct (divsteps_bridge.iter_divstep_dfg (N.to_nat 741) 1 BN256_FpInv.bn256_p x)
    as [[d741 f741] g741] eqn:E741.
  destruct H741 as [Hg0 Hf_pm1].
  assert (exists extra, N = (N.to_nat 741 + extra)%nat) as [extra Hextra].
  { exists (N - N.to_nat 741)%nat. lia. }
  subst N. rewrite divsteps_bridge.iter_divstep_dfg_decompose, E741, Hg0.
  assert (Hf_odd : Z.Odd f741).
  { destruct Hf_pm1 as [-> | ->]; [exists 0; lia | exists (-1); lia]. }
  pose proof (divsteps_bridge.iter_dfg_stable_at_zero extra d741 f741 Hf_odd) as Hstab.
  destruct (divsteps_bridge.iter_divstep_dfg extra d741 f741 0) as [[d_N f_N] g_N].
  destruct Hstab as [Hg Hf]. rewrite Hf. auto.
Qed.

(** Discharges [BN256_FpInv.by_convergence_dfg_bn256]. *)
Theorem by_convergence_dfg_bn256_closed : forall x,
  0 < x < BN256_FpInv.bn256_p ->
  Z.gcd x BN256_FpInv.bn256_p = 1 ->
  let '(_, f_N, g_N) :=
    BN256_FpInv.iter_divstep_dfg
      (Z.to_nat BN256_FpInv.bn256_divstep_iters) 1 BN256_FpInv.bn256_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  rewrite <- iter_divstep_dfg_eq.
  apply convergence_monotone_bn256; auto.
Qed.

(* ================================================================ *)
(* Helper lemmas (mirrored from BN254_FpInv_closed.v).               *)
(* ================================================================ *)

Local Notation p := BN256_FpInv.bn256_p.

Lemma Zmod_sub_zero : forall a b m,
  m <> 0 -> (a - b) mod m = 0 -> a mod m = b mod m.
Proof.
  intros a b m Hm H.
  apply Zmod_divides in H; [| exact Hm].
  destruct H as [k Hk].
  assert (a = b + k * m) by lia.
  subst a. rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Zmod_mod. reflexivity.
Qed.

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
  replace a with (b + m * k) by lia.
  replace ((b + m * k) * c) with (b * c + k * c * m) by ring.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma mod_mul_rearrange : forall v c x m,
  ((v mod m * c) mod m * x) mod m = (v * x * c) mod m.
Proof.
  intros.
  rewrite Zmult_mod_idemp_l with (a := v mod m * c) (b := x).
  replace (v mod m * c * x) with (v mod m * (c * x)) by ring.
  rewrite Zmult_mod_idemp_l with (a := v) (b := c * x).
  f_equal. ring.
Qed.

(* ================================================================ *)
(* The headline: fp_inv_correct without the by_convergence axiom    *)
(* ================================================================ *)

Theorem fp_inv_correct_closed : forall x,
  0 < x < p ->
  Z.gcd x p = 1 ->
  (BN256_FpInv.fp_inv_spec x * x) mod p = 1.
Proof.
  intros x Hx Hgcd.
  unfold BN256_FpInv.fp_inv_spec.
  set (N := Z.to_nat BN256_FpInv.bn256_divstep_iters).
  destruct (BN256_FpInv.iter_divstep_spec p N 1 p x 0 1)
    as [[[[d_N f_N] g_N] v_N] r_N] eqn:Espec.
  pose proof (BN256_FpInv.iter_invariant p N 1 p x 0 1 x
                BN256_FpInv.p_pos BN256_FpInv.p_odd) as Hinv.
  assert (Hv0 : (0 * x - p) mod p = 0).
  { replace (0 * x - p) with ((-1) * p) by ring.
    rewrite Z_mod_mult. reflexivity. }
  assert (Hr0 : (1 * x - x) mod p = 0)
    by (replace (1 * x - x) with 0 by ring; reflexivity).
  specialize (Hinv Hv0 Hr0). rewrite Espec in Hinv.
  destruct Hinv as [Hinv_v _].
  pose proof (BN256_FpInv.iter_dfg_agree N p 1 p x 0 1) as Hagree.
  rewrite Espec in Hagree.
  destruct (BN256_FpInv.iter_divstep_dfg N 1 p x) as [[d2 f2] g2] eqn:Edfg.
  destruct Hagree as [_ [Hf_eq Hg_eq]]. subst f2 g2.
  pose proof (by_convergence_dfg_bn256_closed x Hx Hgcd) as Hconv.
  unfold N in Edfg. rewrite Edfg in Hconv.
  destruct Hconv as [Hg0 Hf_pm1]. subst g_N.
  assert (Hp : p <> 0) by (pose proof BN256_FpInv.p_pos; lia).
  Opaque BN256_FpInv.bn256_p.
  destruct Hf_pm1 as [Hf1 | Hf_neg1].
  - subst f_N. rewrite Z.mul_1_r in Hinv_v.
    change (1 <? 0) with false. simpl (if false then _ else _).
    assert (Hvx : (v_N * x) mod p = (2 ^ Z.of_nat N) mod p)
      by (apply Zmod_sub_zero; auto).
    rewrite mod_mul_rearrange.
    transitivity ((2 ^ Z.of_nat N * BN256_FpInv.precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hvx. }
    rewrite Z.mul_comm.
    unfold N.
    rewrite Z2Nat.id by (unfold BN256_FpInv.bn256_divstep_iters; vm_compute; discriminate).
    exact BN256_FpInv.precomp_times_pow2.
  - subst f_N.
    change (-1 <? 0) with true. simpl (if true then _ else _).
    replace (2 ^ Z.of_nat N * -1) with (-(2 ^ Z.of_nat N)) in Hinv_v by ring.
    assert (Hpvx : ((p - v_N) * x) mod p = (2 ^ Z.of_nat N) mod p).
    { assert (Hvx_neg : (v_N * x) mod p = (-(2 ^ Z.of_nat N)) mod p)
        by (apply Zmod_sub_zero; auto).
      replace ((p - v_N) * x) with (-(v_N * x) + x * p) by ring.
      rewrite Z_mod_plus_full.
      rewrite Z.opp_eq_mul_m1.
      apply Zmul_mod_compat with (c := -1) in Hvx_neg.
      replace (v_N * x * -1) with ((v_N * x) * -1) by ring.
      rewrite Hvx_neg.
      replace (-(2 ^ Z.of_nat N) * -1) with (2 ^ Z.of_nat N) by ring.
      reflexivity. }
    rewrite mod_mul_rearrange.
    transitivity ((2 ^ Z.of_nat N * BN256_FpInv.precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hpvx. }
    rewrite Z.mul_comm.
    unfold N.
    rewrite Z2Nat.id by (unfold BN256_FpInv.bn256_divstep_iters; vm_compute; discriminate).
    exact BN256_FpInv.precomp_times_pow2.
Qed.
