(** * Safegcd_InRange — InRange invariant bookkeeping for the
 *    safegcd outer-loop chain.
 *
 *  Key lemmas:
 *
 *    [iter_preserves]                  generic Nat.iter invariant-
 *                                       preservation (4-line induction).
 *
 *    [init_state_in_InRange]            the chain's initial state
 *                                       (d = -1, F = p25519, G = x,
 *                                       V = 0, R = 1) lies in [InRange]
 *                                       for any [0 < x < p25519].
 *                                       Decidable / vm_compute.
 *
 *    [divstep_full_half_p25519_preserves_loose]
 *                                       single-step preservation of a
 *                                       *strengthened* [InRange_loose k]
 *                                       invariant that carries [k]
 *                                       divsteps of slack on the [d]
 *                                       component.  Direct case split
 *                                       on the two branches of
 *                                       [divstep_spec_full_half].
 *
 *    [iter_divstep_full_half_p25519_preserves_loose]
 *                                       chained: [InRange_loose k]
 *                                       implies [InRange_loose (k - n)]
 *                                       after [n ≤ k] divsteps.  Direct
 *                                       induction on [n].
 *
 *    [safegcd_step59_preserves_InRange_strong]
 *                                       one [safegcd_step59_spec_Z]
 *                                       iteration started from
 *                                       [InRange_loose sg_chunk] lands
 *                                       in [InRange].  This is the
 *                                       *working* invariant for the
 *                                       outer-loop chain: the loose
 *                                       slack carries through.
 *
 *  Notes on [safegcd_step59_preserves_InRange] (Admitted):
 *    The literal statement
 *      [InRange d F G V R -> InRange (safegcd_step59_spec_Z p25519 ...)]
 *    is *false* at the lower edge of [d]'s range.  Concretely take
 *      d = -2^61, G even, V = R = 0.
 *    Then [(d <? 0) && Z.odd G = false], so the no-swap branch fires
 *    and [d' = d - 1 = -2^61 - 1], which violates [-2^61 <= d'].
 *    The fix is to thread a strengthened invariant ([InRange_loose])
 *    that gives [d] enough slack to absorb 59 divsteps' drift; the
 *    [_strong] variant above does exactly that and is closed by
 *    direct calculation.  The original [InRange]-shape lemma is
 *    retained as scaffolding for the documented Z-level contract;
 *    callers should use [_strong].
 *
 *  Downstream composition lemmas
 *    [step59_iter_pack_preserves_InRange_loose] and
 *    [outer_iter_pack_preserves_InRange_loose]
 *  thread [InRange_loose sg_chunk] through the 10-chunk outer loop;
 *  the initial state easily satisfies [InRange_loose 590] (in fact
 *  [InRange_loose (Z.to_nat p25519_divstep_iters)]) since |d| = 1.
 *
 *  Current scope:
 *    [safegcd_outer_chain_inverts] in [Safegcd_Outer_Loop_Chain.v]
 *    does *not* depend on [InRange] (only [by_convergence_dfg_half]),
 *    so this file's role is forward-looking infrastructure for the
 *    bedrock2-level chain proof.
 *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
Require Import Bedrock.End2End.Ed25519.Safegcd_Step59_Spec.
Require Import Bedrock.Field.Synthesis.Examples.Fe25519_FpInv.

Local Open Scope Z_scope.

(* ================================================================== *)
(* §1.  Generic Nat.iter invariant preservation                        *)
(* ================================================================== *)

(** If [P] is preserved by [step], it is preserved by [Nat.iter n step]
    for any [n]. *)
Lemma iter_preserves {A : Type} (P : A -> Prop) (step : A -> A) :
  (forall s, P s -> P (step s)) ->
  forall n s, P s -> P (Nat.iter n step s).
Proof.
  intros Hstep n.
  induction n as [|n IH]; intros s Hs.
  - exact Hs.
  - cbn. apply Hstep. apply IH. exact Hs.
Qed.

(* ================================================================== *)
(* §2.  Initial state lies in InRange                                  *)
(* ================================================================== *)

(** The 5-tuple [(-1, p25519, x, 0, 1)] starting state for any [x] with
    [0 < x < p25519] satisfies [InRange].

    Justification (all by [vm_compute] / [lia]):
      * d  = -1     : |d| < 2^61  trivially.
      * f  = p25519 : p25519 = 2^255 - 19  <  2^309.
      * g  = x      : 0 < x < p25519 < 2^309.
      * v  = 0      : trivially in range.
      * r  = 1      : trivially in range.
*)
Lemma init_state_in_InRange : forall (x : Z),
  0 < x < p25519 ->
  InRange (-1) p25519 x 0 1.
Proof.
  intros x Hx.
  unfold InRange, sg_mw, sg_bw, sg_n.
  (* sg_mw - 1 = 61; sg_bw - 1 = 309 — after all unfolds the bounds
     are 2 ^ 61 and 2 ^ (62 * 5 - 1) = 2 ^ 309. *)
  assert (Hbig : 2 ^ 255 < 2 ^ (62 * Z.of_nat 5 - 1)).
  { apply Z.pow_lt_mono_r; lia. }
  assert (Hpos : 0 < 2 ^ (62 * Z.of_nat 5 - 1)).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hpos_m : 0 < 2 ^ (62 - 1)).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hm : 1 < 2 ^ (62 - 1)).
  { replace (62 - 1) with 61 by lia.
    change (1 < 2 ^ 61). apply Z.pow_gt_1; lia. }
  assert (Hpsmall : p25519 < 2 ^ 255).
  { unfold p25519. lia. }
  repeat split; unfold sg_mw; try lia.
Qed.

(* ================================================================== *)
(* §3.  Strengthened invariant [InRange_loose]                         *)
(* ================================================================== *)

(** [InRange_loose k d f g v r] : same shape as [InRange] but with [k]
    divsteps of slack on the [d] component.  After [k] divsteps the
    slack is consumed and we recover the full [InRange].  This is the
    invariant that propagates correctly through the divstep iteration
    — the bare [InRange] does *not* (see comment at top of file). *)
Definition InRange_loose (k : nat) (d f g v r : Z) : Prop :=
  - 2 ^ (sg_mw - 1) + 2 * Z.of_nat k <= d <= 2 ^ (sg_mw - 1) - 2 * Z.of_nat k - 1 /\
  - 2 ^ (sg_bw - 1) <= f < 2 ^ (sg_bw - 1) /\
  - 2 ^ (sg_bw - 1) <= g < 2 ^ (sg_bw - 1) /\
  - 2 ^ (sg_bw - 1) <= v < 2 ^ (sg_bw - 1) /\
  - 2 ^ (sg_bw - 1) <= r < 2 ^ (sg_bw - 1).

(** Concrete numerics for sg_mw and sg_bw envelopes. *)
Lemma sg_bw_minus_1_val : 2 ^ (sg_bw - 1) = 2 ^ 309.
Proof. vm_compute. reflexivity. Qed.

Lemma sg_mw_minus_1_val : 2 ^ (sg_mw - 1) = 2 ^ 61.
Proof. vm_compute. reflexivity. Qed.

Lemma sg_bw_huge_vs_p : 2 * p25519 < 2 ^ (sg_bw - 1).
Proof. unfold p25519. vm_compute. reflexivity. Qed.

(** [InRange_loose 0] is exactly [InRange]. *)
Lemma InRange_loose_0_iff_InRange : forall d f g v r,
  InRange_loose 0 d f g v r <-> InRange d f g v r.
Proof.
  intros. unfold InRange_loose, InRange. simpl.
  split; intros [Hd [Hf [Hg [Hv Hr]]]]; repeat split; try lia; tauto.
Qed.

(** Single-step preservation of [InRange_loose] for [m = p25519]:
    each [divstep_spec_full_half] consumes one unit of slack.

    Case analysis on the divstep branch:
    * swap branch ((d <? 0) && Z.odd g = true):
        d' = -d - 2, f' = g, g' = (g - f) / 2,
        v' = 2*r mod p25519, r' = (r - v) mod p25519
    * no-swap branch:
        d' = d - 1, f' = f, g' = (g + (g mod 2)*f) / 2,
        v' = 2*v mod p25519, r' = (r + (g mod 2)*v) mod p25519
    Each conjunct of [InRange_loose (k - 1)] follows from [lia] on
    the [InRange_loose k] hypotheses plus [Z.mod_pos_bound] for the
    [v', r'] residues and [Z.div_{le_lower,lt_upper}_bound] for the
    half-divisions. *)
Lemma divstep_full_half_p25519_preserves_loose :
  forall k d f g v r,
    (1 <= k)%nat ->
    InRange_loose k d f g v r ->
    let '(d', f', g', v', r') := divstep_spec_full_half p25519 d f g v r in
    InRange_loose (k - 1) d' f' g' v' r'.
Proof.
  intros k d f g v r Hk H.
  unfold InRange_loose in *.
  unfold divstep_spec_full_half.
  destruct H as [Hd [Hf [Hg [Hv Hr]]]].
  pose proof sg_mw_minus_1_val as Hmw.
  pose proof sg_bw_minus_1_val as Hbw.
  pose proof sg_bw_huge_vs_p as Hbw_p.
  assert (Hp : 0 < p25519) by (unfold p25519; lia).
  destruct ((d <? 0) && Z.odd g)%bool eqn:E.
  - apply andb_prop in E. destruct E as [Hdneg _]. apply Z.ltb_lt in Hdneg.
    repeat split.
    + lia.
    + lia.
    + apply Hg.
    + apply Hg.
    + apply Z.div_le_lower_bound; [lia|]. lia.
    + apply Z.div_lt_upper_bound; [lia|]. lia.
    + pose proof (Z.mod_pos_bound (2*r) p25519 Hp). lia.
    + pose proof (Z.mod_pos_bound (2*r) p25519 Hp). lia.
    + pose proof (Z.mod_pos_bound (r - v) p25519 Hp). lia.
    + pose proof (Z.mod_pos_bound (r - v) p25519 Hp). lia.
  - assert (Hgmod : 0 <= g mod 2 <= 1) by
      (pose proof (Z.mod_pos_bound g 2 ltac:(lia)); lia).
    repeat split.
    + lia.
    + lia.
    + apply Hf.
    + apply Hf.
    + apply Z.div_le_lower_bound; [lia|]. nia.
    + apply Z.div_lt_upper_bound; [lia|]. nia.
    + pose proof (Z.mod_pos_bound (2*v) p25519 Hp). lia.
    + pose proof (Z.mod_pos_bound (2*v) p25519 Hp). lia.
    + pose proof (Z.mod_pos_bound (r + g mod 2 * v) p25519 Hp). lia.
    + pose proof (Z.mod_pos_bound (r + g mod 2 * v) p25519 Hp). lia.
Qed.

(** Chained: after [n <= k] divsteps starting from [InRange_loose k],
    we have [InRange_loose (k - n)]. *)
Lemma iter_divstep_full_half_p25519_preserves_loose :
  forall n k d f g v r,
    (n <= k)%nat ->
    InRange_loose k d f g v r ->
    let '(d', f', g', v', r') :=
        iter_divstep_spec_half p25519 n d f g v r in
    InRange_loose (k - n) d' f' g' v' r'.
Proof.
  induction n as [|n IH]; intros k d f g v r Hnk H.
  - simpl. replace (k - 0)%nat with k by lia. exact H.
  - simpl.
    assert (Hk : (1 <= k)%nat) by lia.
    pose proof (divstep_full_half_p25519_preserves_loose k d f g v r Hk H) as Hstep.
    destruct (divstep_spec_full_half p25519 d f g v r) as [[[[d' f'] g'] v'] r'] eqn:E.
    specialize (IH (k - 1)%nat d' f' g' v' r' ltac:(lia) Hstep).
    destruct (iter_divstep_spec_half p25519 n d' f' g' v' r')
      as [[[[d'' f''] g''] v''] r''] eqn:E2.
    replace (k - S n)%nat with (k - 1 - n)%nat by lia.
    exact IH.
Qed.

(** The strong, working version: starting from [InRange_loose sg_chunk]
    (i.e., 59 divsteps of slack on [d]), one chunk lands in plain
    [InRange]. *)
Lemma safegcd_step59_preserves_InRange_strong :
  forall (d F G V R : Z),
    InRange_loose sg_chunk d F G V R ->
    let '(d', F', G', V', R') :=
        safegcd_step59_spec_Z p25519 d F G V R in
    InRange d' F' G' V' R'.
Proof.
  intros d F G V R H.
  unfold safegcd_step59_spec_Z.
  pose proof (iter_divstep_full_half_p25519_preserves_loose
                sg_chunk sg_chunk d F G V R (le_n _) H) as Hloose.
  destruct (iter_divstep_spec_half p25519 sg_chunk d F G V R)
    as [[[[d' F'] G'] V'] R'] eqn:E.
  replace (sg_chunk - sg_chunk)%nat with 0%nat in Hloose by lia.
  apply InRange_loose_0_iff_InRange. exact Hloose.
Qed.

(** Original [InRange]-shape statement, retained as documented
    scaffolding.  *Not* provable as stated — see explanatory comment
    at top of file (counterexample at the lower edge of d).  Callers
    should use [safegcd_step59_preserves_InRange_strong] instead. *)
Lemma safegcd_step59_preserves_InRange : forall (d F G V R : Z),
  InRange d F G V R ->
  let '(d', F', G', V', R') := safegcd_step59_spec_Z p25519 d F G V R in
  InRange d' F' G' V' R'.
Proof.
Admitted.

(* ================================================================== *)
(* §4.  Outer-chain invariant — composition via [InRange_loose]        *)
(* ================================================================== *)

(** The packed step function used by [outer_iter10_Z]. *)
Definition step59_iter_pack (m : Z) (st : Z * Z * Z * Z * Z)
  : Z * Z * Z * Z * Z :=
  let '(d, F, G, V, R) := st in
  safegcd_step59_spec_Z m d F G V R.

(** Lifted predicate over the 5-tuple form. *)
Definition InRange_pack (st : Z * Z * Z * Z * Z) : Prop :=
  let '(d, F, G, V, R) := st in InRange d F G V R.

(** Lifted strengthened predicate over the 5-tuple form. *)
Definition InRange_loose_pack (k : nat) (st : Z * Z * Z * Z * Z) : Prop :=
  let '(d, F, G, V, R) := st in InRange_loose k d F G V R.

(** [InRange_loose_pack k] for any [k >= 59] is preserved by one packed
    step at [m = p25519] in the sense that one chunk consumes 59 units
    of slack: starting in [InRange_loose k], we land in
    [InRange_loose (k - 59)].

    This is the *correct* preservation lemma for the 10-chunk outer
    loop: we start with enough slack on [d] to absorb all 590
    divsteps, and lose 59 slack per chunk. *)
Lemma step59_iter_pack_preserves_InRange_loose :
  forall k st,
    (sg_chunk <= k)%nat ->
    InRange_loose_pack k st ->
    InRange_loose_pack (k - sg_chunk) (step59_iter_pack p25519 st).
Proof.
  intros k [[[[d F] G] V] R] Hk H.
  unfold InRange_loose_pack, step59_iter_pack, safegcd_step59_spec_Z in *.
  pose proof (iter_divstep_full_half_p25519_preserves_loose sg_chunk k d F G V R Hk H)
    as Hstep.
  destruct (iter_divstep_spec_half p25519 sg_chunk d F G V R)
    as [[[[d' F'] G'] V'] R'].
  exact Hstep.
Qed.

(** Original [InRange]-shape packed version, retained as scaffolding;
    inherits the Admit on [safegcd_step59_preserves_InRange]. *)
Lemma step59_iter_pack_preserves_InRange :
  forall st, InRange_pack st -> InRange_pack (step59_iter_pack p25519 st).
Proof.
  intros [[[[d F] G] V] R] H.
  unfold InRange_pack, step59_iter_pack in *.
  pose proof (safegcd_step59_preserves_InRange d F G V R H) as Hstep.
  destruct (safegcd_step59_spec_Z p25519 d F G V R)
    as [[[[d' F'] G'] V'] R'].
  exact Hstep.
Qed.

(** Initial state lies in [InRange_loose k] for any reasonable [k]
    (specifically: [2 * Z.of_nat k + 1 <= 2^61], i.e., [k <= 2^60]).
    For the chain we use [k = sg_chunk * 10 = 590], far below this. *)
Lemma init_state_in_InRange_loose : forall (k : nat) (x : Z),
  (2 * Z.of_nat k + 1 <= 2 ^ (sg_mw - 1))%Z ->
  0 < x < p25519 ->
  InRange_loose k (-1) p25519 x 0 1.
Proof.
  intros k x Hk Hx.
  pose proof sg_mw_minus_1_val as Hmw.
  pose proof sg_bw_minus_1_val as Hbw.
  pose proof sg_bw_huge_vs_p as Hbw_p.
  unfold InRange_loose.
  assert (Hp : 0 < p25519) by (unfold p25519; lia).
  assert (Hbw_pos : 0 < 2 ^ (sg_bw - 1)) by lia.
  repeat split; lia.
Qed.

(** Composed via the strong (loose) invariant: [InRange_loose] is
    preserved along the outer chain, shrinking the slack by [sg_chunk]
    per step.

    After [n] outer chunks we have [InRange_loose (k - n * sg_chunk)]
    provided [n * sg_chunk <= k].

    Specialised to the chain initial state, this gives the
    [InRange_loose] invariant — and thereby [InRange] via
    [InRange_loose_0_iff_InRange] when [k = n * sg_chunk]. *)
Lemma outer_iter_pack_preserves_InRange_loose :
  forall (n : nat) (k : nat) (x : Z),
    (n * sg_chunk <= k)%nat ->
    (2 * Z.of_nat k + 1 <= 2 ^ (sg_mw - 1))%Z ->
    0 < x < p25519 ->
    InRange_loose_pack (k - n * sg_chunk)
      (Nat.iter n (step59_iter_pack p25519)
         (-1, p25519, x, 0, 1)).
Proof.
  induction n as [|n IH]; intros k x Hnk Hk Hx.
  - simpl. replace (k - 0)%nat with k by lia.
    unfold InRange_loose_pack.
    apply init_state_in_InRange_loose; assumption.
  - assert (Hn : (n * sg_chunk <= k)%nat) by lia.
    specialize (IH k x Hn Hk Hx).
    pose proof (step59_iter_pack_preserves_InRange_loose
                  (k - n * sg_chunk)%nat
                  (Nat.iter n (step59_iter_pack p25519)
                     (-1, p25519, x, 0, 1))) as Hstep.
    assert (Hslack : (sg_chunk <= k - n * sg_chunk)%nat) by lia.
    specialize (Hstep Hslack IH).
    change (Nat.iter (S n) (step59_iter_pack p25519) (-1, p25519, x, 0, 1))
      with (step59_iter_pack p25519
              (Nat.iter n (step59_iter_pack p25519) (-1, p25519, x, 0, 1))).
    replace (k - S n * sg_chunk)%nat with (k - n * sg_chunk - sg_chunk)%nat by lia.
    exact Hstep.
Qed.

(** Original [InRange]-shape outer composition; inherits the Admit on
    [safegcd_step59_preserves_InRange]. *)
Lemma outer_iter_pack_preserves_InRange : forall (n : nat) (x : Z),
  0 < x < p25519 ->
  InRange_pack
    (Nat.iter n (step59_iter_pack p25519)
       (-1, p25519, x, 0, 1)).
Proof.
  intros n x Hx.
  apply iter_preserves.
  - apply step59_iter_pack_preserves_InRange.
  - cbn. apply init_state_in_InRange. exact Hx.
Qed.

(** Headline corollary: after the full 10 chunks of safegcd, the state
    is in [InRange] — *unconditionally*, with no Admit dependency.
    This is the lemma the bedrock2-level chain proof actually needs.

    The slack budget is [10 * sg_chunk = 590 = p25519_divstep_iters],
    well within the [2^61] envelope on [d]. *)
Lemma outer_iter10_pack_in_InRange : forall (x : Z),
  0 < x < p25519 ->
  InRange_pack (Nat.iter 10 (step59_iter_pack p25519)
                  (-1, p25519, x, 0, 1)).
Proof.
  intros x Hx.
  pose proof (outer_iter_pack_preserves_InRange_loose 10 (10 * sg_chunk) x
                (le_n _)) as H.
  assert (Hbound : (2 * Z.of_nat (10 * sg_chunk) + 1 <= 2 ^ (sg_mw - 1))%Z).
  { pose proof sg_mw_minus_1_val as Hmw. unfold sg_chunk. lia. }
  specialize (H Hbound Hx).
  replace (10 * sg_chunk - 10 * sg_chunk)%nat with 0%nat in H by lia.
  unfold InRange_loose_pack, InRange_pack in *.
  destruct (Nat.iter 10 (step59_iter_pack p25519) (-1, p25519, x, 0, 1))
    as [[[[d F] G] V] R].
  apply InRange_loose_0_iff_InRange. exact H.
Qed.

(* ================================================================== *)
(* §5.  Print Assumptions                                              *)
(* ================================================================== *)

Print Assumptions iter_preserves.
Print Assumptions init_state_in_InRange.
Print Assumptions InRange_loose_0_iff_InRange.
Print Assumptions divstep_full_half_p25519_preserves_loose.
Print Assumptions iter_divstep_full_half_p25519_preserves_loose.
Print Assumptions safegcd_step59_preserves_InRange_strong.
Print Assumptions step59_iter_pack_preserves_InRange_loose.
Print Assumptions outer_iter_pack_preserves_InRange_loose.
Print Assumptions outer_iter10_pack_in_InRange.
(* The next two retain the documented Admit on
   [safegcd_step59_preserves_InRange]. *)
Print Assumptions step59_iter_pack_preserves_InRange.
Print Assumptions outer_iter_pack_preserves_InRange.
