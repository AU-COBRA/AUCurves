(** * δ₀ = 1/2 analogue of [divsteps_theory.v].
    Proves [processDivstep_correct_half] and [processDivstep_inverse_half]:
    if the convex-hull cert [processDivstep_half] empties out after N steps,
    then [divsteps_half.step] iterated N times has [g = 0] and (under the
    rel-prime hypothesis) [|f| = 1] with the modular inverse readable
    from [d * f].

    Structure mirrors [divsteps_theory.v]:
    - The δ-independent convex-hull machinery (Hull lemmas, State_lookup,
      Matrix, even/odd transitions) is IMPORTED from [divsteps_theory.v].
    - Only [in_State_step] needs re-proving: the delta-direction test
      changes from [(0 <? delta)] to [(delta <? 0)].  Body otherwise
      identical (the convex-hull arithmetic is δ-independent).
*)

Require Import List.
Require MSetProperties.
Require FMapFacts.
Require Import NArith.
Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import divsteps_base.
Require Import divsteps_base_half.
Require Import divsteps_def.
Require Import divsteps_def_half.
Require Import divsteps_convexhull.
Require Import divsteps_theory.

Module ZMapPropertiesHalf := FMapFacts.OrdProperties ZMap.

(** [in_State M ds st]: either [g ds = 0], or the rational point
    [(g/M, f/M)] lies in the convex hull stored in [st] at the
    delta-key [divsteps_half.delta ds]. *)
Definition in_State_half (M : Z) (ds : divsteps_half.State) (s : State) : Prop :=
  divsteps_half.g ds = 0%Z \/
  in_convex_hull (divsteps_half.g ds / M, divsteps_half.f ds / M)
   (DDSet.add (0:D,0:D)%Z (State_lookup (divsteps_half.delta ds) s)).

(** Single-step preservation: this is the δ₀ = 1/2 analogue of
    [divsteps_theory.in_State_step].  The only structural change is
    that the odd-and-swap branch is gated on [(delta <? 0)] (consistent
    with [divsteps_base_half.odd_map_half] and
    [divsteps_def_half.divsteps_half.step]).  Convex-hull arithmetic
    is identical to the δ₀=1 version because [even_trans],
    [odd_pos_trans], [odd_nonpos_trans] are shared verbatim
    (see [divsteps_base_half.v]). *)
Lemma in_State_step_half : forall M ds st, (0 < M)%Z ->
  Z.Odd (divsteps_half.f ds) ->
  in_State_half M ds st ->
  in_State_half M (divsteps_half.step ds) (processDivstep_half M st).
Proof.
intros M [delta f g] st HM Hf [Hst|Hst];
 [left; auto using divsteps_half.zero_step|].
rewrite <- Zodd_equiv in Hf.
simpl in *.
set (ds' := divsteps_half.step _).
pose (delta' := divsteps_half.delta ds').
pose (f' := divsteps_half.f ds').
pose (g' := divsteps_half.g ds').
unfold processDivstep_half.
set (fm2 := fun kv => _).
set (fm1 := fun kv => _).
set (st1 := State_fromList (flat_map fm1 _)).
set (st2 := State_fromList (flat_map fm2 _)).
case (Z.eq_dec g 0) as [Hg0|Hg0];
 [left;unfold ds'; auto using divsteps_half.zero_step|].
case (Z.eq_dec g' 0) as [Hg'0|Hg'0];
 [left;auto|].
assert (H : {s | ZMap.MapsTo delta s st}).
  clear - Hst Hg0 HM.
  unfold State_lookup in Hst.
  case (ZMap.find delta st) as [s|] eqn:Hfind;
    [exists s; auto using ZMap.find_2|].
  apply in_convex_hull_singleton in Hst.
  destruct Hst as [Hst _].
  simpl in Hst.
  rewrite <- inject_Z_injective in Hg0.
  rewrite Zlt_Qlt in HM.
  rewrite <- !inject_Z_D_Q in *.
  apply Qinv_lt_0_compat in HM.
  apply Qmult_integral_l in Hst; auto.
  rewrite Hst in HM.
  discriminate.
destruct H as [s Hs].
(** The transition choice: even g → even_trans; odd g + (delta < 0) →
    odd_pos_trans (= swap); otherwise odd_nonpos_trans.  This matches
    [odd_map_half] in [divsteps_base_half.v]. *)
pose (divstep_trans :=
  if Z.even g then even_trans
              else if (delta <? 0)%Z then odd_pos_trans else odd_nonpos_trans).
pose (divstep_matrix :=
  if Z.even g then even_matrix
              else if (delta <? 0)%Z then odd_pos_matrix else odd_nonpos_matrix).
set (zero := (0%Z:D,0%Z:D)) in *.
assert (Hst' : in_convex_hull (g' / M, f' / M)
                              (DDSet.add zero (State_lookup delta' st1))).
  assert (Hx := ZMap.elements_1 Hs).
  apply SetoidList.InA_altdef in Hx.
  apply Exists_exists in Hx.
  destruct Hx as [x [Hx1 Hx2]].
  apply State_in_convex_hull_fromList1 with (DDSet_map divstep_trans (snd x)).
  * apply in_convex_hull_map_ext with divstep_matrix (g / M, f / M).
    - intros p. clear.
      case (Z.even g) in *;[apply even_trans_matrix|].
      case (delta <? 0)%Z in *;[apply odd_pos_trans_matrix|].
      apply odd_nonpos_trans_matrix.
    - clear -Hf.
      unfold QQeq, g', f', ds', divsteps_half.step; simpl.
      case (Z.even g) eqn:Hg in *;[apply Zeven_bool_iff in Hg
                                  |apply (f_equal negb) in Hg;
                                   rewrite Z.negb_even in Hg;
                                   apply Zodd_bool_iff in Hg;
                                   case (delta <? 0)%Z in *];simpl;
        rewrite !Dhalf_Q;
        change (inject_D (-1)%Z:Q) with (-1);
        change (inject_D 1%Z:Q) with 1;
        change (inject_D 0%Z:Q) with 0;
        split; try ring;
        unfold Z.sub;
        rewrite !inject_Z_D_Q, inject_Z_half, ?inject_Z_plus, ?inject_Z_opp;
        try (unfold Qdiv; ring);
        apply Zeven_equiv;
        auto using Zodd_plus_Zodd, Zodd_opp.
    - clear -Hst Hs Hx2.
      destruct Hx2 as [_ Hx2].
      replace (snd x) with s.
      unfold State_lookup in Hst.
      rewrite (ZMap.find_1 Hs) in Hst.
      assumption.
  * apply in_flat_map.
    exists x; split; auto.
    clear -Hx2; destruct x; destruct Hx2 as [Hx1 Hx2].
    unfold divsteps_half.step in ds'; cbn -[Z.ltb Z.add Z.sub] in *.
    rewrite <- Hx1.
    case (Z.even g) in *;[left;reflexivity|].
    right;left.
    case (delta <? 0)%Z in *;
    reflexivity.
* clear s Hs.
  assert (H : {s | ZMap.MapsTo delta' s st1}).
   clear - Hst' Hg'0 HM.
   unfold State_lookup in Hst'.
   case (ZMap.find delta' st1) as [s|] eqn:Hfind;
     [exists s; auto using ZMap.find_2|].
   apply in_convex_hull_singleton in Hst'.
   destruct Hst' as [Hst' _].
   simpl in Hst'.
   rewrite <- inject_Z_injective in Hg'0.
   rewrite Zlt_Qlt in HM.
   rewrite <- !inject_Z_D_Q in *.
   apply Qinv_lt_0_compat in HM.
   apply Qmult_integral_l in Hst'; auto.
   rewrite Hst' in HM.
   discriminate.
  destruct H as [s Hs].
  assert (Hx := ZMap.elements_1 Hs).
  apply SetoidList.InA_altdef in Hx.
  apply Exists_exists in Hx.
  destruct Hx as [x [Hx1 Hx2]].
  unfold State_lookup in Hst'.
  rewrite (ZMap.find_1 Hs) in Hst'.
  case (narrow M s) eqn:Hnarrow;
  [left;
   apply (in_narrow _ _ _ _ HM Hnarrow Hst')
  |].
  right.
  fold g' f' delta'.
  apply State_in_convex_hull_fromList1 with (convexHull s).
    auto using in_convex_hull_convexHull.
  apply in_flat_map.
  exists x.
  split; try tauto.
  destruct x as [x0 x1].
  destruct Hx2 as [Hx2 Hx3]; simpl in *.
  rewrite <- Hx2, <- Hx3, Hnarrow.
  auto with *.
Qed.

(** Iterated convergence: cert empty → g iterates to 0. *)
Theorem processDivstep_correct_half : forall N M f g,
  Z.Odd f ->
  (f <= M)%Z -> (0 <= g <= f)%Z ->
  ZMap.Empty (N.iter N (processDivstep_half M) state0_half) ->
  divsteps_half.g (N.iter N divsteps_half.step (divsteps_half.init f g)) = 0%Z.
Proof.
intros N M f g HM Hf Hg H.
rewrite N2Nat.inj_iter.
rewrite <- N2Nat.inj_iter.
assert (HM0 : (0 < M)%Z).
 eapply Z.lt_le_trans;[|apply Hf].
 apply Z.le_neq.
 split; auto with *.
 intros <-.
 rewrite <- Zodd_equiv in HM.
 contradiction.
assert (HM2 : 0 < M).
 rewrite inject_Z_D_Q.
 change 0 with (inject_Z 0).
 rewrite <- Zlt_Qlt.
 assumption.
cut (in_State_half M (N.iter N divsteps_half.step (divsteps_half.init f g))
                     (N.iter N (processDivstep_half M) state0_half)).
 intros [H0|H0];auto.
 set (p := (_,_)) in *.
 set (st' := N.iter N divsteps_half.step _) in *.
 unfold State_lookup in H0.
 case (ZMap.find _ _) eqn:Hfind.
  apply ZMap.find_2 in Hfind.
  apply ZMap.elements_1 in Hfind.
  apply ZMapPropertiesHalf.P.elements_Empty in H.
  rewrite H in Hfind.
  apply SetoidList.InA_nil in Hfind.
  contradiction.
 apply in_convex_hull_singleton in H0.
 destruct H0 as [H0 _].
 simpl in *.
 apply inject_Z_injective.
 rewrite <- !inject_Z_D_Q.
 change (0%Z:Q) with 0 in *.
 apply Qmult_integral in H0.
 destruct H0 as [H0|H0]; auto.
 apply Qinv_lt_0_compat in HM2.
 rewrite H0 in HM2.
 discriminate.
clear H.
cut (in_State_half M (divsteps_half.init f g) state0_half).
 intros H.
 apply proj2 with (Z.Odd (divsteps_half.f (N.iter N divsteps_half.step (divsteps_half.init f g)))).
 elim N using N.induction;[intros x y ->| |];try tauto.
 intros n.
 intros H0.
 rewrite !N.iter_succ.
 split;[apply divsteps_half.odd_step;tauto|].
 apply in_State_step_half;auto with *; try tauto.
right.
unfold State_lookup, state0_half; simpl.
(* Lookup at delta_0 = -1 in [ZMap.add (-1) set0 empty].  Same shape as
   the δ₀=1 case (where state0 = ZMap.add 1 set0 empty) — convex-hull
   identity reasoning is identical. *)
pose (l := ((1-f/M),(0:D,0:D)%Z)
         ::(g / M,(1:D,1:D)%Z)
         ::((f - g)/M,(0:D,1:D)%Z)
         ::nil : list (Q*DD)).
exists l.
do 2 (try split).
* destruct H as [H|[H|[H|[]]]];inversion H.
  + apply -> Qle_minus_iff.
    apply Qle_shift_div_r; auto with *.
    ring_simplify.
    rewrite !inject_Z_D_Q.
    change 0 with (inject_Z 0).
    rewrite <- Zle_Qle.
    auto with *.
  + apply Qle_shift_div_l;auto with *.
    ring_simplify.
    rewrite inject_Z_D_Q.
    change 0 with (inject_Z 0).
    rewrite <- Zle_Qle.
    auto with *.
  + apply Qle_shift_div_l;auto with *.
    ring_simplify (0 * M).
    apply -> Qle_minus_iff.
    rewrite !inject_Z_D_Q.
    rewrite <- Zle_Qle.
    auto with *.
* destruct H as [H|[H|[H|[]]]];
    inversion H;
    apply DDSet.mem_spec;
    reflexivity.
* simpl; field.
  auto with *.
* simpl.
  change (0%Z:Q) with 0.
  change (1%Z:Q) with 1.
  split; simpl; try ring.
  field.
  auto with *.
Qed.

(** Iterated gcd preservation (no rel-prime hypothesis needed). *)
Corollary processDivstep_gcd_half : forall N M f g,
  Z.Odd f ->
  (f <= M)%Z -> (0 <= g <= f)%Z ->
  ZMap.Empty (N.iter N (processDivstep_half M) state0_half) ->
  Znumtheory.Zis_gcd f g
   (divsteps_half.f (N.iter N divsteps_half.step (divsteps_half.init f g))).
Proof.
intros N M f g HM Hf Hg H.
rewrite N2Nat.inj_iter.
apply (divsteps_half.gcd_spec _ (divsteps_half.init f g)); auto.
rewrite <- N2Nat.inj_iter.
eapply processDivstep_correct_half; eauto.
Qed.

(** Modular-inverse readout. *)
Corollary processDivstep_inverse_half : forall N M f g,
  Z.Odd f ->
  (f <= M)%Z -> (0 <= g <= f)%Z ->
  Znumtheory.rel_prime f g ->
  ZMap.Empty (N.iter N (processDivstep_half M) state0_half) ->
  let st' := N.iter N divsteps_half.step (divsteps_half.init f g) in
  Z.abs (divsteps_half.f st') = 1%Z /\
  eqm f ((divsteps_half.d st' * divsteps_half.f st') * g) 1.
Proof.
intros N M f g Hodd HM Hgf Hprime Hempty st'.
unfold st'; clear st'.
rewrite N2Nat.inj_iter.
apply divsteps_half.modulo_spec; auto using divsteps_half.modulo_init.
rewrite <- N2Nat.inj_iter.
eapply processDivstep_correct_half; eauto.
Qed.
