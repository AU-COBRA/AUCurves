(** * δ₀ = 1/2 bridge: O'Connor cert → divstep_spec_half convergence.

    Mirror of [divsteps_bridge.v] for the EUROCRYPT 2026 paper's
    δ₀ = 1/2 algorithm.  Composes:
      - [divsteps_theory_half.processDivstep_correct_half] /
        [divsteps_theory_half.processDivstep_inverse_half]
      - The (d, f, g)-only iteration over [divstep_spec_half] (matches
        [Fe25519_FpInv.iter_divstep_dfg_half] / Wuille zeta encoding)
      - The O'Connor cert at [N = 590] from [divsteps590.v] (or its
        [_native] variant).
    Discharges [by_convergence_dfg_half] from [Fe25519_FpInv.v].
*)

From Stdlib Require Import Bool ZArith Lia Znumtheory.
Require Import divsteps_def.
Require Import divsteps_def_half.
Require Import divsteps_base.
Require Import divsteps_base_half.
Require Import divsteps_theory.
Require Import divsteps_theory_half.

Local Open Scope Z_scope.

(** The [(d, f, g)]-only flavour of [divstep_spec_half] that
    [Fe25519_FpInv.v] uses.  Duplicated here to avoid a circular dep
    on [Bedrock.Field.Synthesis.Examples]. *)
Definition divstep_spec_half (d f g : Z) : Z * Z * Z :=
  if (d <? 0) && Z.odd g
  then (- d - 2, g, (g - f) / 2)
  else (d - 1, f, (g + (g mod 2) * f) / 2).

Fixpoint iter_divstep_dfg_half (nsteps : nat) (d f g : Z) : Z * Z * Z :=
  match nsteps with
  | O => (d, f, g)
  | S k =>
    let '(d', f', g') := divstep_spec_half d f g in
    iter_divstep_dfg_half k d' f' g'
  end.

(** *** Step equivalence: [divsteps_half.step] ≡ [divstep_spec_half]. *)

Lemma even_mod2 : forall g, Z.even g = true -> g mod 2 = 0.
Proof.
  intros g H. rewrite Z.even_spec in H. destruct H as [k Hk].
  subst. rewrite Z.mul_comm. rewrite Z.mod_mul by lia. reflexivity.
Qed.

Lemma odd_mod2 : forall g, Z.odd g = true -> g mod 2 = 1.
Proof.
  intros g H. rewrite Zodd_mod in H. destruct (g mod 2) eqn:E; try discriminate.
  destruct p; try discriminate. reflexivity.
Qed.

Lemma step_equiv_half : forall st,
  let '(d', f', g') := divstep_spec_half (divsteps_half.delta st)
                                          (divsteps_half.f st) (divsteps_half.g st) in
  divsteps_half.delta (divsteps_half.step st) = d' /\
  divsteps_half.f (divsteps_half.step st) = f' /\
  divsteps_half.g (divsteps_half.step st) = g'.
Proof.
  intros [delta0 f0 g0 d0 e0 m0].
  unfold divstep_spec_half, divsteps_half.step; simpl.
  destruct (Z.even g0) eqn:Heven.
  - assert (Hodd : Z.odd g0 = false) by (rewrite <- Z.negb_even, Heven; auto).
    rewrite Hodd; simpl; rewrite Bool.andb_false_r.
    rewrite (even_mod2 _ Heven); simpl; rewrite Z.add_0_r. auto.
  - assert (Hodd : Z.odd g0 = true) by (rewrite <- Z.negb_even, Heven; auto).
    rewrite Hodd; simpl.
    destruct (delta0 <? 0) eqn:Hd; simpl.
    + auto.
    + rewrite (odd_mod2 _ Hodd).
      cbv beta iota zeta delta [Z.mul Z.add Pos.mul].
      destruct f0; auto.
Qed.

(** *** Iterated step equivalence *)

Lemma iter_dfg_equiv_aux_half : forall n d0 f0 g0 st,
  divsteps_half.delta st = d0 -> divsteps_half.f st = f0 -> divsteps_half.g st = g0 ->
  let '(d', f', g') := iter_divstep_dfg_half n d0 f0 g0 in
  divsteps_half.delta (Nat.iter n divsteps_half.step st) = d' /\
  divsteps_half.f (Nat.iter n divsteps_half.step st) = f' /\
  divsteps_half.g (Nat.iter n divsteps_half.step st) = g'.
Proof.
  induction n as [|k IH]; intros d0 f0 g0 st Hd Hf Hg.
  - simpl. auto.
  - rewrite Nat.iter_succ_r.
    simpl iter_divstep_dfg_half.
    pose proof (step_equiv_half st) as Hstep.
    rewrite Hd, Hf, Hg in Hstep.
    destruct (divstep_spec_half d0 f0 g0) as [[d1 f1] g1].
    destruct Hstep as [Hd1 [Hf1 Hg1]].
    exact (IH d1 f1 g1 (divsteps_half.step st) Hd1 Hf1 Hg1).
Qed.

(** Init for the half framework places [delta := -1] (= Wuille zeta_0). *)
Lemma iter_dfg_equiv_half : forall n f0 g0,
  let '(d', f', g') := iter_divstep_dfg_half n (-1) f0 g0 in
  divsteps_half.delta (Nat.iter n divsteps_half.step (divsteps_half.init f0 g0)) = d' /\
  divsteps_half.f (Nat.iter n divsteps_half.step (divsteps_half.init f0 g0)) = f' /\
  divsteps_half.g (Nat.iter n divsteps_half.step (divsteps_half.init f0 g0)) = g'.
Proof. intros. apply iter_dfg_equiv_aux_half; reflexivity. Qed.

Lemma Z_abs_1 : forall n, Z.abs n = 1 -> n = 1 \/ n = -1.
Proof. intros [|p|p] H; simpl in H; try lia; destruct p; try discriminate; auto. Qed.

(** *** Generic bridge *)

Theorem oconnor_bridge_half : forall N M f0 g0,
  Z.Odd f0 ->
  (f0 <= M) ->
  (0 <= g0 <= f0) ->
  rel_prime f0 g0 ->
  ZMap.Empty (N.iter N (processDivstep_half M) state0_half) ->
  let '(_, f_N, g_N) := iter_divstep_dfg_half (N.to_nat N) (-1) f0 g0 in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros N M f0 g0 Hodd HM Hgx Hrel Hempty.
  pose proof (processDivstep_correct_half N M f0 g0 Hodd HM Hgx Hempty) as Hg0.
  pose proof (processDivstep_inverse_half N M f0 g0 Hodd HM Hgx Hrel Hempty)
    as [Habs _].
  rewrite Nnat.N2Nat.inj_iter in Hg0, Habs.
  pose proof (iter_dfg_equiv_half (N.to_nat N) f0 g0) as Hequiv.
  destruct (iter_divstep_dfg_half (N.to_nat N) (-1) f0 g0) as [[d_N f_N] g_N].
  destruct Hequiv as [_ [Hf_eq Hg_eq]].
  split.
  - rewrite <- Hg_eq. exact Hg0.
  - apply Z_abs_1. rewrite <- Hf_eq. exact Habs.
Qed.

(** *** Monotonicity: once g hits 0 and f is ±1, further iterations are fixed. *)

Lemma iter_divstep_dfg_half_decompose : forall a b d f g,
  iter_divstep_dfg_half (a + b) d f g =
  let '(d', f', g') := iter_divstep_dfg_half a d f g in
  iter_divstep_dfg_half b d' f' g'.
Proof.
  induction a as [|a IH]; intros; simpl.
  - reflexivity.
  - destruct (divstep_spec_half d f g) as [[d1 f1] g1]. apply IH.
Qed.

Lemma iter_dfg_stable_at_zero_half : forall k d f,
  Z.Odd f ->
  let '(_, f', g') := iter_divstep_dfg_half k d f 0 in g' = 0 /\ f' = f.
Proof.
  induction k as [|k IH]; intros d f Hf.
  - simpl. auto.
  - simpl. unfold divstep_spec_half; simpl.
    rewrite Bool.andb_false_r. simpl. rewrite Z.div_0_l by lia.
    apply IH. exact Hf.
Qed.

Theorem convergence_monotone_half : forall N N0 M f0 g0,
  Z.Odd f0 ->
  (f0 <= M) ->
  (0 <= g0 <= f0) ->
  rel_prime f0 g0 ->
  ZMap.Empty (N.iter N0 (processDivstep_half M) state0_half) ->
  (N.to_nat N0 <= N)%nat ->
  let '(_, f_N, g_N) := iter_divstep_dfg_half N (-1) f0 g0 in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros N N0 M f0 g0 Hodd HM Hgx Hrel Hempty HN.
  pose proof (oconnor_bridge_half N0 M f0 g0 Hodd HM Hgx Hrel Hempty) as Hbase.
  destruct (iter_divstep_dfg_half (N.to_nat N0) (-1) f0 g0) as [[d0 f0'] g0'] eqn:E0.
  destruct Hbase as [Hg0' Hf0_pm1].
  assert (exists extra, N = (N.to_nat N0 + extra)%nat) as [extra Hextra].
  { exists (N - N.to_nat N0)%nat. lia. }
  subst N. rewrite iter_divstep_dfg_half_decompose, E0, Hg0'.
  assert (Hf_odd : Z.Odd f0').
  { destruct Hf0_pm1 as [-> | ->]; [exists 0; lia | exists (-1); lia]. }
  pose proof (iter_dfg_stable_at_zero_half extra d0 f0' Hf_odd) as Hstab.
  destruct (iter_divstep_dfg_half extra d0 f0' 0) as [[d_N f_N] g_N].
  destruct Hstab as [Hg Hf]. rewrite Hf. auto.
Qed.
