(** * Closes [BN254_FpInv.by_convergence_dfg_bn254] axiom via the existing bridge.

    Mirrors [BLS12_FpInv_closed.v] for BN254 (alt_bn128).  Composes:

    - The generic [divsteps_bridge.oconnor_bridge] (parametric in the
      prime [M] and iteration count [N]),
    - The BN254-specific cert axiom [divsteps_bn254.bn254_certificate]
      (735 iterations),
    - A re-proof of the convergence-monotone lemma for BN254
      (parallel to [divsteps_bridge.convergence_monotone] which is
      hardcoded to BLS12), with
    - A trivial [iter_divstep_dfg_eq] (the two definitions in
      [divsteps_bridge.v] and [BN254_FpInv.v] are syntactically
      identical → defining-equation reflexivity).

    Result: [by_convergence_dfg_bn254_closed] has the exact statement
    of [BN254_FpInv.by_convergence_dfg_bn254], discharging the axiom.

    Net axiom in the chain: just [bn254_certificate] (axiomatized in
    [divsteps_bn254.v] in parallel to [bls12_certificate]; both can be
    independently verified by OCaml extraction via
    [Arithmetic/safegcd/multi_curve_driver]).
*)

From Stdlib Require Import ZArith Lia Znumtheory.
Require Import divsteps_def.
Require Import divsteps_bridge.
Require Import divsteps_bn254.
Require Import Crypto.Arithmetic.BYInv.
Require Import Bedrock.Field.Synthesis.Examples.BN254_FpInv.

Local Open Scope Z_scope.

(** The two [iter_divstep_dfg] definitions (one in [divsteps_bridge.v],
    one in [BN254_FpInv.v]) have identical bodies; they coincide. *)
Lemma iter_divstep_dfg_eq : forall n d f g,
  divsteps_bridge.iter_divstep_dfg n d f g =
  BN254_FpInv.iter_divstep_dfg n d f g.
Proof.
  induction n as [|k IH]; intros d f g; simpl; [reflexivity|].
  destruct (divstep_spec d f g) as [[d' f'] g'].
  apply IH.
Qed.

(** *** BN254-specific O'Connor convergence (parallel to
    [divsteps_bridge.oconnor_implies_convergence] for BLS12). *)
Theorem oconnor_implies_convergence_bn254 : forall x,
  0 < x < BN254_FpInv.bn254_p ->
  Z.gcd x BN254_FpInv.bn254_p = 1 ->
  let '(_, f_N, g_N) :=
    divsteps_bridge.iter_divstep_dfg (N.to_nat 735) 1 BN254_FpInv.bn254_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  (* [BN254_FpInv.bn254_p] and [divsteps_bn254.bn254_p] are both
     literal Z constants for the same prime; the cert is stated in
     terms of [divsteps_bn254.bn254_M = divsteps_bn254.bn254_p]. *)
  apply (divsteps_bridge.oconnor_bridge 735 divsteps_bn254.bn254_M).
  - (* Z.Odd bn254_p *) exists (BN254_FpInv.bn254_p / 2). vm_compute. reflexivity.
  - (* bn254_p <= bn254_M *) unfold divsteps_bn254.bn254_M, divsteps_bn254.bn254_p, BN254_FpInv.bn254_p. lia.
  - (* 0 <= x <= bn254_p *) lia.
  - (* rel_prime *) apply Zgcd_1_rel_prime. rewrite Z.gcd_comm. exact Hgcd.
  - exact divsteps_bn254.bn254_certificate.
Qed.

(** *** Stable-at-zero + monotonicity helpers (re-stated here, parallel
    to those in [divsteps_bridge.v] for BLS12). *)
Theorem convergence_monotone_bn254 : forall N x,
  (N.to_nat 735 <= N)%nat ->
  0 < x < BN254_FpInv.bn254_p ->
  Z.gcd x BN254_FpInv.bn254_p = 1 ->
  let '(_, f_N, g_N) := divsteps_bridge.iter_divstep_dfg N 1 BN254_FpInv.bn254_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros N x HN Hx Hgcd.
  pose proof (oconnor_implies_convergence_bn254 x Hx Hgcd) as H735.
  destruct (divsteps_bridge.iter_divstep_dfg (N.to_nat 735) 1 BN254_FpInv.bn254_p x)
    as [[d735 f735] g735] eqn:E735.
  destruct H735 as [Hg0 Hf_pm1].
  assert (exists extra, N = (N.to_nat 735 + extra)%nat) as [extra Hextra].
  { exists (N - N.to_nat 735)%nat. lia. }
  subst N. rewrite divsteps_bridge.iter_divstep_dfg_decompose, E735, Hg0.
  assert (Hf_odd : Z.Odd f735).
  { destruct Hf_pm1 as [-> | ->]; [exists 0; lia | exists (-1); lia]. }
  pose proof (divsteps_bridge.iter_dfg_stable_at_zero extra d735 f735 Hf_odd) as Hstab.
  destruct (divsteps_bridge.iter_divstep_dfg extra d735 f735 0) as [[d_N f_N] g_N].
  destruct Hstab as [Hg Hf]. rewrite Hf. auto.
Qed.

(** Discharges [BN254_FpInv.by_convergence_dfg_bn254]: the convergence
    statement with the exact shape of the axiom. *)
Theorem by_convergence_dfg_bn254_closed : forall x,
  0 < x < BN254_FpInv.bn254_p ->
  Z.gcd x BN254_FpInv.bn254_p = 1 ->
  let '(_, f_N, g_N) :=
    BN254_FpInv.iter_divstep_dfg
      (Z.to_nat BN254_FpInv.bn254_divstep_iters) 1 BN254_FpInv.bn254_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  rewrite <- iter_divstep_dfg_eq.
  apply convergence_monotone_bn254; auto.
Qed.

(* ================================================================ *)
(* Helper lemmas (mirrored from BLS12_FpInv_closed.v).               *)
(* ================================================================ *)

Local Notation p := BN254_FpInv.bn254_p.

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
(* The headline: fp_inv_correct without the by_convergence_dfg_bn254 *)
(* axiom — goes through by_convergence_dfg_bn254_closed instead.     *)
(* ================================================================ *)

(** Mirror of [BN254_FpInv.fp_inv_correct_ax] with the single line
    [by_convergence_dfg_bn254] replaced by [by_convergence_dfg_bn254_closed]. *)
Theorem fp_inv_correct_closed : forall x,
  0 < x < p ->
  Z.gcd x p = 1 ->
  (BN254_FpInv.fp_inv_spec x * x) mod p = 1.
Proof.
  intros x Hx Hgcd.
  unfold BN254_FpInv.fp_inv_spec.
  set (N := Z.to_nat BN254_FpInv.bn254_divstep_iters).
  destruct (BN254_FpInv.iter_divstep_spec p N 1 p x 0 1)
    as [[[[d_N f_N] g_N] v_N] r_N] eqn:Espec.
  pose proof (BN254_FpInv.iter_invariant p N 1 p x 0 1 x
                BN254_FpInv.p_pos BN254_FpInv.p_odd) as Hinv.
  assert (Hv0 : (0 * x - p) mod p = 0).
  { replace (0 * x - p) with ((-1) * p) by ring.
    rewrite Z_mod_mult. reflexivity. }
  assert (Hr0 : (1 * x - x) mod p = 0)
    by (replace (1 * x - x) with 0 by ring; reflexivity).
  specialize (Hinv Hv0 Hr0). rewrite Espec in Hinv.
  destruct Hinv as [Hinv_v _].
  pose proof (BN254_FpInv.iter_dfg_agree N p 1 p x 0 1) as Hagree.
  rewrite Espec in Hagree.
  destruct (BN254_FpInv.iter_divstep_dfg N 1 p x) as [[d2 f2] g2] eqn:Edfg.
  destruct Hagree as [_ [Hf_eq Hg_eq]]. subst f2 g2.
  pose proof (by_convergence_dfg_bn254_closed x Hx Hgcd) as Hconv.
  unfold N in Edfg. rewrite Edfg in Hconv.
  destruct Hconv as [Hg0 Hf_pm1]. subst g_N.
  assert (Hp : p <> 0) by (pose proof BN254_FpInv.p_pos; lia).
  Opaque BN254_FpInv.bn254_p.
  destruct Hf_pm1 as [Hf1 | Hf_neg1].
  - subst f_N. rewrite Z.mul_1_r in Hinv_v.
    change (1 <? 0) with false. simpl (if false then _ else _).
    assert (Hvx : (v_N * x) mod p = (2 ^ Z.of_nat N) mod p)
      by (apply Zmod_sub_zero; auto).
    rewrite mod_mul_rearrange.
    transitivity ((2 ^ Z.of_nat N * BN254_FpInv.precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hvx. }
    rewrite Z.mul_comm.
    unfold N.
    rewrite Z2Nat.id by (unfold BN254_FpInv.bn254_divstep_iters; vm_compute; discriminate).
    exact BN254_FpInv.precomp_times_pow2.
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
    transitivity ((2 ^ Z.of_nat N * BN254_FpInv.precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hpvx. }
    rewrite Z.mul_comm.
    unfold N.
    rewrite Z2Nat.id by (unfold BN254_FpInv.bn254_divstep_iters; vm_compute; discriminate).
    exact BN254_FpInv.precomp_times_pow2.
Qed.

(** [Print Assumptions fp_inv_correct_closed]: should report only
    [bn254_certificate] (the convex-hull cert from [divsteps_bn254.v],
    independently verifiable by OCaml extraction).  No
    [by_convergence_dfg_bn254] axiom — the chain goes through
    [by_convergence_dfg_bn254_closed], which goes through the
    convex-hull bridge and the cert directly. *)
