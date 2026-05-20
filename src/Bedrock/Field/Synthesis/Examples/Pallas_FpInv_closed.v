(** * Closes [Pallas_FpInv.by_convergence_dfg_pallas] axiom via the existing bridge.

    Mirrors [BN254_FpInv_closed.v] for Pallas (pasta_fp).  Composes:

    - The generic [divsteps_bridge.oconnor_bridge] (parametric in the
      prime [M] and iteration count [N]),
    - The Pallas-specific cert axiom [divsteps_pallas.pallas_certificate]
      (738 iterations),
    - A re-proof of the convergence-monotone lemma for Pallas
      (parallel to [divsteps_bridge.convergence_monotone] which is
      hardcoded to BLS12), with
    - A trivial [iter_divstep_dfg_eq] (the two definitions in
      [divsteps_bridge.v] and [Pallas_FpInv.v] are syntactically
      identical → defining-equation reflexivity).

    Result: [by_convergence_dfg_pallas_closed] has the exact statement
    of [Pallas_FpInv.by_convergence_dfg_pallas], discharging the axiom.

    Net axiom in the chain: just [pallas_certificate] (axiomatized in
    [divsteps_pallas.v] in parallel to [bls12_certificate] /
    [bn254_certificate]; all can be independently verified by OCaml
    extraction via [Arithmetic/safegcd/multi_curve_driver]).
*)

From Stdlib Require Import ZArith Lia Znumtheory.
Require Import divsteps_def.
Require Import divsteps_bridge.
Require Import divsteps_pallas.
Require Import Crypto.Arithmetic.BYInv.
Require Import Bedrock.Field.Synthesis.Examples.Pallas_FpInv.

Local Open Scope Z_scope.

(** The two [iter_divstep_dfg] definitions (one in [divsteps_bridge.v],
    one in [Pallas_FpInv.v]) have identical bodies; they coincide. *)
Lemma iter_divstep_dfg_eq : forall n d f g,
  divsteps_bridge.iter_divstep_dfg n d f g =
  Pallas_FpInv.iter_divstep_dfg n d f g.
Proof.
  induction n as [|k IH]; intros d f g; simpl; [reflexivity|].
  destruct (divstep_spec d f g) as [[d' f'] g'].
  apply IH.
Qed.

(** *** Pallas-specific O'Connor convergence (parallel to
    [divsteps_bridge.oconnor_implies_convergence] for BLS12). *)
Theorem oconnor_implies_convergence_pallas : forall x,
  0 < x < Pallas_FpInv.pallas_p ->
  Z.gcd x Pallas_FpInv.pallas_p = 1 ->
  let '(_, f_N, g_N) :=
    divsteps_bridge.iter_divstep_dfg (N.to_nat 738) 1 Pallas_FpInv.pallas_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  (* [Pallas_FpInv.pallas_p] and [divsteps_pallas.pallas_p] are both
     literal Z constants for the same prime; the cert is stated in
     terms of [divsteps_pallas.pallas_M = divsteps_pallas.pallas_p]. *)
  apply (divsteps_bridge.oconnor_bridge 738 divsteps_pallas.pallas_M).
  - (* Z.Odd pallas_p *) exists (Pallas_FpInv.pallas_p / 2). vm_compute. reflexivity.
  - (* pallas_p <= pallas_M *) unfold divsteps_pallas.pallas_M, divsteps_pallas.pallas_p, Pallas_FpInv.pallas_p. lia.
  - (* 0 <= x <= pallas_p *) lia.
  - (* rel_prime *) apply Zgcd_1_rel_prime. rewrite Z.gcd_comm. exact Hgcd.
  - exact divsteps_pallas.pallas_certificate.
Qed.

(** *** Stable-at-zero + monotonicity helpers (re-stated here, parallel
    to those in [divsteps_bridge.v] for BLS12). *)
Theorem convergence_monotone_pallas : forall N x,
  (N.to_nat 738 <= N)%nat ->
  0 < x < Pallas_FpInv.pallas_p ->
  Z.gcd x Pallas_FpInv.pallas_p = 1 ->
  let '(_, f_N, g_N) := divsteps_bridge.iter_divstep_dfg N 1 Pallas_FpInv.pallas_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros N x HN Hx Hgcd.
  pose proof (oconnor_implies_convergence_pallas x Hx Hgcd) as H738.
  destruct (divsteps_bridge.iter_divstep_dfg (N.to_nat 738) 1 Pallas_FpInv.pallas_p x)
    as [[d738 f738] g738] eqn:E738.
  destruct H738 as [Hg0 Hf_pm1].
  assert (exists extra, N = (N.to_nat 738 + extra)%nat) as [extra Hextra].
  { exists (N - N.to_nat 738)%nat. lia. }
  subst N. rewrite divsteps_bridge.iter_divstep_dfg_decompose, E738, Hg0.
  assert (Hf_odd : Z.Odd f738).
  { destruct Hf_pm1 as [-> | ->]; [exists 0; lia | exists (-1); lia]. }
  pose proof (divsteps_bridge.iter_dfg_stable_at_zero extra d738 f738 Hf_odd) as Hstab.
  destruct (divsteps_bridge.iter_divstep_dfg extra d738 f738 0) as [[d_N f_N] g_N].
  destruct Hstab as [Hg Hf]. rewrite Hf. auto.
Qed.

(** Discharges [Pallas_FpInv.by_convergence_dfg_pallas]: the convergence
    statement with the exact shape of the axiom. *)
Theorem by_convergence_dfg_pallas_closed : forall x,
  0 < x < Pallas_FpInv.pallas_p ->
  Z.gcd x Pallas_FpInv.pallas_p = 1 ->
  let '(_, f_N, g_N) :=
    Pallas_FpInv.iter_divstep_dfg
      (Z.to_nat Pallas_FpInv.pallas_divstep_iters) 1 Pallas_FpInv.pallas_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  rewrite <- iter_divstep_dfg_eq.
  apply convergence_monotone_pallas; auto.
Qed.

(* ================================================================ *)
(* Helper lemmas (mirrored from BN254_FpInv_closed.v).               *)
(* ================================================================ *)

Local Notation p := Pallas_FpInv.pallas_p.

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
(* The headline: fp_inv_correct without the by_convergence_dfg_pallas *)
(* axiom — goes through by_convergence_dfg_pallas_closed instead.    *)
(* ================================================================ *)

(** Mirror of [Pallas_FpInv.fp_inv_correct_ax] with the single line
    [by_convergence_dfg_pallas] replaced by [by_convergence_dfg_pallas_closed]. *)
Theorem fp_inv_correct_closed : forall x,
  0 < x < p ->
  Z.gcd x p = 1 ->
  (Pallas_FpInv.fp_inv_spec x * x) mod p = 1.
Proof.
  intros x Hx Hgcd.
  unfold Pallas_FpInv.fp_inv_spec.
  set (N := Z.to_nat Pallas_FpInv.pallas_divstep_iters).
  destruct (Pallas_FpInv.iter_divstep_spec p N 1 p x 0 1)
    as [[[[d_N f_N] g_N] v_N] r_N] eqn:Espec.
  pose proof (Pallas_FpInv.iter_invariant p N 1 p x 0 1 x
                Pallas_FpInv.p_pos Pallas_FpInv.p_odd) as Hinv.
  assert (Hv0 : (0 * x - p) mod p = 0).
  { replace (0 * x - p) with ((-1) * p) by ring.
    rewrite Z_mod_mult. reflexivity. }
  assert (Hr0 : (1 * x - x) mod p = 0)
    by (replace (1 * x - x) with 0 by ring; reflexivity).
  specialize (Hinv Hv0 Hr0). rewrite Espec in Hinv.
  destruct Hinv as [Hinv_v _].
  pose proof (Pallas_FpInv.iter_dfg_agree N p 1 p x 0 1) as Hagree.
  rewrite Espec in Hagree.
  destruct (Pallas_FpInv.iter_divstep_dfg N 1 p x) as [[d2 f2] g2] eqn:Edfg.
  destruct Hagree as [_ [Hf_eq Hg_eq]]. subst f2 g2.
  pose proof (by_convergence_dfg_pallas_closed x Hx Hgcd) as Hconv.
  unfold N in Edfg. rewrite Edfg in Hconv.
  destruct Hconv as [Hg0 Hf_pm1]. subst g_N.
  assert (Hp : p <> 0) by (pose proof Pallas_FpInv.p_pos; lia).
  Opaque Pallas_FpInv.pallas_p.
  destruct Hf_pm1 as [Hf1 | Hf_neg1].
  - subst f_N. rewrite Z.mul_1_r in Hinv_v.
    change (1 <? 0) with false. simpl (if false then _ else _).
    assert (Hvx : (v_N * x) mod p = (2 ^ Z.of_nat N) mod p)
      by (apply Zmod_sub_zero; auto).
    rewrite mod_mul_rearrange.
    transitivity ((2 ^ Z.of_nat N * Pallas_FpInv.precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hvx. }
    rewrite Z.mul_comm.
    unfold N.
    rewrite Z2Nat.id by (unfold Pallas_FpInv.pallas_divstep_iters; vm_compute; discriminate).
    exact Pallas_FpInv.precomp_times_pow2.
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
    transitivity ((2 ^ Z.of_nat N * Pallas_FpInv.precomp_val) mod p).
    { apply Zmul_mod_compat. exact Hpvx. }
    rewrite Z.mul_comm.
    unfold N.
    rewrite Z2Nat.id by (unfold Pallas_FpInv.pallas_divstep_iters; vm_compute; discriminate).
    exact Pallas_FpInv.precomp_times_pow2.
Qed.

(** [Print Assumptions fp_inv_correct_closed]: should report only
    [pallas_certificate] (the convex-hull cert from [divsteps_pallas.v],
    independently verifiable by OCaml extraction).  No
    [by_convergence_dfg_pallas] axiom — the chain goes through
    [by_convergence_dfg_pallas_closed], which goes through the
    convex-hull bridge and the cert directly. *)
