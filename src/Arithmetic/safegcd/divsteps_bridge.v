(** * Bridge between O'Connor's divsteps framework and BYInv's divstep_spec.

    Shows that O'Connor's [divsteps.step] and fiat-crypto's [divstep_spec]
    compute identical (delta, f, g) sequences. Combined with the O'Connor
    certificate, this discharges the convergence axiom in BLS12_FpInv.v. *)

From Stdlib Require Import ZArith Lia Znumtheory.
Require Import divsteps_def.
Require Import divsteps_theory.
Require Import divsteps_bls12.
Require Import Crypto.Arithmetic.BYInv.

Local Open Scope Z_scope.

(** Iterate the (d,f,g) part of divstep_spec.
    Duplicated from BLS12_FpInv.v to avoid circular dependency. *)
Fixpoint iter_divstep_dfg (nsteps : nat) (d f g : Z) : Z * Z * Z :=
  match nsteps with
  | O => (d, f, g)
  | S k =>
    let '(d', f', g') := divstep_spec d f g in
    iter_divstep_dfg k d' f' g'
  end.

(** *** Step equivalence *)

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

Lemma step_equiv : forall st,
  let '(d', f', g') := divstep_spec (divsteps.delta st) (divsteps.f st) (divsteps.g st) in
  divsteps.delta (divsteps.step st) = d' /\
  divsteps.f (divsteps.step st) = f' /\
  divsteps.g (divsteps.step st) = g'.
Proof.
  intros [delta0 f0 g0 d0 e0 m0].
  unfold divstep_spec, divsteps.step; simpl; unfold INC.
  destruct (Z.even g0) eqn:Heven.
  - assert (Hodd : Z.odd g0 = false) by (rewrite <- Z.negb_even, Heven; auto).
    rewrite Hodd; simpl; rewrite Bool.andb_false_r.
    rewrite (even_mod2 _ Heven); simpl; rewrite Z.add_0_r. auto.
  - assert (Hodd : Z.odd g0 = true) by (rewrite <- Z.negb_even, Heven; auto).
    rewrite Hodd; simpl.
    destruct (0 <? delta0) eqn:Hd; simpl.
    + auto.
    + rewrite (odd_mod2 _ Hodd).
      (* After rewrite: goal involves g0 + 1 * f0. Simplify 1 * f0 = f0 *)
      cbv beta iota zeta delta [Z.mul Z.add Pos.mul].
      destruct f0; auto.
Qed.

(** *** Iterated step equivalence *)

Lemma iter_dfg_equiv_aux : forall n d0 f0 g0 st,
  divsteps.delta st = d0 -> divsteps.f st = f0 -> divsteps.g st = g0 ->
  let '(d', f', g') := iter_divstep_dfg n d0 f0 g0 in
  divsteps.delta (Nat.iter n divsteps.step st) = d' /\
  divsteps.f (Nat.iter n divsteps.step st) = f' /\
  divsteps.g (Nat.iter n divsteps.step st) = g'.
Proof.
  induction n as [|k IH]; intros d0 f0 g0 st Hd Hf Hg.
  - simpl. auto.
  - rewrite Nat.iter_succ_r.
    simpl iter_divstep_dfg.
    pose proof (step_equiv st) as Hstep.
    rewrite Hd, Hf, Hg in Hstep.
    destruct (divstep_spec d0 f0 g0) as [[d1 f1] g1].
    destruct Hstep as [Hd1 [Hf1 Hg1]].
    exact (IH d1 f1 g1 (divsteps.step st) Hd1 Hf1 Hg1).
Qed.

Lemma iter_dfg_equiv : forall n f0 g0,
  let '(d', f', g') := iter_divstep_dfg n 1 f0 g0 in
  divsteps.delta (Nat.iter n divsteps.step (divsteps.init f0 g0)) = d' /\
  divsteps.f (Nat.iter n divsteps.step (divsteps.init f0 g0)) = f' /\
  divsteps.g (Nat.iter n divsteps.step (divsteps.init f0 g0)) = g'.
Proof. intros. apply iter_dfg_equiv_aux; reflexivity. Qed.

Lemma Z_abs_1 : forall n, Z.abs n = 1 -> n = 1 \/ n = -1.
Proof. intros [|p|p] H; simpl in H; try lia; destruct p; try discriminate; auto. Qed.

(** *** Generic bridge: O'Connor convergence → iter_divstep_dfg convergence *)

(** This is stated for arbitrary N to avoid instantiating Nat.iter at
    large concrete values (which causes stack overflow). *)
Theorem oconnor_bridge : forall N M f0 g0,
  Z.Odd f0 ->
  (f0 <= M) ->
  (0 <= g0 <= f0) ->
  rel_prime f0 g0 ->
  divsteps_base.ZMap.Empty (N.iter N (divsteps_base.processDivstep M) divsteps_base.state0) ->
  let '(_, f_N, g_N) := iter_divstep_dfg (N.to_nat N) 1 f0 g0 in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros N M f0 g0 Hodd HM Hgx Hrel Hempty.
  pose proof (processDivstep_correct N M f0 g0 Hodd HM Hgx Hempty) as Hg0.
  pose proof (processDivstep_inverse N M f0 g0 Hodd HM Hgx Hrel Hempty) as [Habs _].
  (* Convert N.iter to Nat.iter *)
  rewrite Nnat.N2Nat.inj_iter in Hg0, Habs.
  pose proof (iter_dfg_equiv (N.to_nat N) f0 g0) as Hequiv.
  destruct (iter_divstep_dfg (N.to_nat N) 1 f0 g0) as [[d_N f_N] g_N].
  destruct Hequiv as [_ [Hf_eq Hg_eq]].
  split.
  - rewrite <- Hg_eq. exact Hg0.
  - apply Z_abs_1. rewrite <- Hf_eq. exact Habs.
Qed.

(** *** BLS12-specific convergence *)

Theorem oconnor_implies_convergence : forall x,
  0 < x < bls12_p ->
  Z.gcd x bls12_p = 1 ->
  let '(_, f_N, g_N) := iter_divstep_dfg (N.to_nat 1078) 1 bls12_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  apply (oconnor_bridge 1078 bls12_M).
  - exists (bls12_p / 2). vm_compute. reflexivity.
  - unfold bls12_M. lia.
  - lia.
  - apply Zgcd_1_rel_prime. rewrite Z.gcd_comm. exact Hgcd.
  - exact bls12_certificate.
Qed.

(** *** Monotonicity *)

Lemma iter_divstep_dfg_decompose : forall a b d f g,
  iter_divstep_dfg (a + b) d f g =
  let '(d', f', g') := iter_divstep_dfg a d f g in
  iter_divstep_dfg b d' f' g'.
Proof.
  induction a as [|a IH]; intros; simpl.
  - reflexivity.
  - destruct (divstep_spec d f g) as [[d1 f1] g1]. apply IH.
Qed.

Lemma iter_dfg_stable_at_zero : forall k d f,
  Z.Odd f ->
  let '(_, f', g') := iter_divstep_dfg k d f 0 in g' = 0 /\ f' = f.
Proof.
  induction k as [|k IH]; intros d f Hf.
  - simpl. auto.
  - simpl. unfold divstep_spec; simpl.
    rewrite Bool.andb_false_r. simpl. rewrite Z.div_0_l by lia.
    apply IH. exact Hf.
Qed.

Theorem convergence_monotone : forall N x,
  (N.to_nat 1078 <= N)%nat ->
  0 < x < bls12_p ->
  Z.gcd x bls12_p = 1 ->
  let '(_, f_N, g_N) := iter_divstep_dfg N 1 bls12_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros N x HN Hx Hgcd.
  pose proof (oconnor_implies_convergence x Hx Hgcd) as H1078.
  destruct (iter_divstep_dfg (N.to_nat 1078) 1 bls12_p x) as [[d1078 f1078] g1078] eqn:E1078.
  destruct H1078 as [Hg0 Hf_pm1].
  assert (exists extra, N = (N.to_nat 1078 + extra)%nat) as [extra Hextra].
  { exists (N - N.to_nat 1078)%nat. lia. }
  subst N. rewrite iter_divstep_dfg_decompose, E1078, Hg0.
  assert (Hf_odd : Z.Odd f1078).
  { destruct Hf_pm1 as [-> | ->]; [exists 0; lia | exists (-1); lia]. }
  pose proof (iter_dfg_stable_at_zero extra d1078 f1078 Hf_odd) as Hstab.
  destruct (iter_divstep_dfg extra d1078 f1078 0) as [[d_N f_N] g_N].
  destruct Hstab as [Hg Hf]. rewrite Hf. auto.
Qed.

(** *** Main theorem: discharges Axiom by_convergence_dfg *)

Theorem by_convergence_dfg_proved : forall x,
  0 < x < bls12_p ->
  Z.gcd x bls12_p = 1 ->
  let '(_, f_N, g_N) :=
    iter_divstep_dfg (Z.to_nat 1101) 1 bls12_p x in
  g_N = 0 /\ (f_N = 1 \/ f_N = -1).
Proof.
  intros x Hx Hgcd.
  apply convergence_monotone; auto.
  vm_compute. lia.
Qed.
