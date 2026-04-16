(** * wNAF Horner algebraic step — abstract proof from group axioms.

    This file proves [Hhorner_step], the central algebraic fact needed by
    [process_both_digits_ok] in BLS12_wNAF_ProcessDigits.v, from a minimal
    set of group-theoretic axioms:

    - [curve_add_id_l], [curve_add_id_r]  — identity
    - [curve_add_assoc], [curve_add_comm]  — associativity + commutativity
    - [point_opp_inverse]                  — [curve_add P (point_opp P) = id]

    Plus a signed-digit table correctness hypothesis:

    - [digit_point_signed_correct] : [digit_point d table = scmul_Z d P]

    where [scmul_Z : Z -> Point -> Point] is the signed extension of [scmul],
    defined via conditional [point_opp]. The proof composes the Horner step
    on [weighted_sum] with the group algebra.

    All lemmas are purely algebraic — no bedrock2. *)

From Stdlib Require Import ZArith Lia List.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
(* Note: We do NOT import BLS12_GLV_LoopInvariant here to avoid Section
   parameter aliasing issues. We redefine the needed lemmas locally. *)

(** Restated from BLS12_wNAF_GLV_LoopBody.v to avoid heavy bedrock2 imports. *)
Lemma skipn_cons_nth_Z (n : nat) (l : list Z) (d : Z) :
  (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l.
Proof.
  revert l. induction n as [|n' IH]; intros l Hlt.
  - destruct l; simpl in *; [lia|reflexivity].
  - destruct l as [|x rest]; simpl in *; [lia|].
    apply IH. lia.
Qed.
Import ListNotations.
Local Open Scope Z_scope.

Section HornerAlgebra.
  Context {F : Type}.
  Context (Fzero Fone : F).
  Let Point := (F * F * F)%type.
  Let id : Point := (Fzero, Fone, Fzero).
  Context (curve_add : Point -> Point -> Point).
  Context (point_opp : Point -> Point).

  Context (curve_add_id_r : forall x y z, curve_add (x, y, z) id = (x, y, z)).
  Context (curve_add_id_l : forall x y z, curve_add id (x, y, z) = (x, y, z)).
  Context (curve_add_assoc : forall P Q R,
    curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm : forall P Q, curve_add P Q = curve_add Q P).
  Context (point_opp_inverse : forall P, curve_add P (point_opp P) = id).

  Fixpoint sm (n : nat) (P : Point) : Point :=
    match n with O => id | S m => curve_add P (sm m P) end.

  (** Two helpers from BLS12_GLV_LoopInvariant — restated with specialized F *)
  Lemma add_id_r' : forall P, curve_add P id = P.
  Proof. intros [[x y] z]. apply curve_add_id_r. Qed.
  Lemma add_id_l' : forall P, curve_add id P = P.
  Proof. intros [[x y] z]. apply curve_add_id_l. Qed.

  Lemma sm_add : forall a b P, sm (a + b)%nat P = curve_add (sm a P) (sm b P).
  Proof.
    induction a as [|a' IH]; intros b P; simpl.
    - rewrite add_id_l'. reflexivity.
    - rewrite IH. rewrite curve_add_assoc. reflexivity.
  Qed.

  (** ** Group inverse properties *)

  (** [point_opp P] is a right inverse ⇒ it is also a left inverse. *)
  Lemma point_opp_inverse_l : forall P, curve_add (point_opp P) P = id.
  Proof.
    intros. rewrite curve_add_comm. apply point_opp_inverse.
  Qed.

  (** [point_opp] of [id] is [id]. *)
  Lemma point_opp_id : point_opp id = id.
  Proof.
    (* curve_add id (point_opp id) = id by inverse;
       curve_add id (point_opp id) = point_opp id by left-identity;
       so point_opp id = id. *)
    pose proof (point_opp_inverse id) as Hi.
    rewrite add_id_l' in Hi. exact Hi.
  Qed.

  (** Right-cancellation: [curve_add P Q = curve_add P R ⇒ Q = R]. *)
  Lemma curve_add_cancel_l : forall P Q R,
    curve_add P Q = curve_add P R -> Q = R.
  Proof.
    intros P Q R H.
    assert (Heq : curve_add (point_opp P) (curve_add P Q) =
                  curve_add (point_opp P) (curve_add P R)) by (rewrite H; reflexivity).
    rewrite !curve_add_assoc in Heq.
    rewrite point_opp_inverse_l in Heq.
    rewrite !add_id_l' in Heq. exact Heq.
  Qed.

  (** [point_opp (point_opp P) = P] *)
  Lemma point_opp_opp : forall P, point_opp (point_opp P) = P.
  Proof.
    intros P.
    apply (curve_add_cancel_l (point_opp P)).
    rewrite point_opp_inverse.
    rewrite point_opp_inverse_l. reflexivity.
  Qed.

  (** [point_opp (P + Q) = point_opp Q + point_opp P = point_opp P + point_opp Q] *)
  Lemma point_opp_add : forall P Q,
    point_opp (curve_add P Q) = curve_add (point_opp P) (point_opp Q).
  Proof.
    intros P Q.
    apply (curve_add_cancel_l (curve_add P Q)).
    rewrite point_opp_inverse.
    (* Goal: curve_add (P+Q) (point_opp P + point_opp Q) = id.
       Left-associate to expose the 4-element shape, then rearrange. *)
    rewrite curve_add_assoc.
    (* 4-term rearrangement: ((P+Q)+P')+Q' = (P+P')+(Q+Q') *)
    rewrite <- (curve_add_assoc (curve_add P Q) (point_opp P) (point_opp Q)).
    rewrite <- (curve_add_assoc P Q (curve_add (point_opp P) (point_opp Q))).
    rewrite (curve_add_assoc Q (point_opp P) (point_opp Q)).
    rewrite (curve_add_comm Q (point_opp P)).
    rewrite <- (curve_add_assoc (point_opp P) Q (point_opp Q)).
    rewrite (curve_add_assoc P (point_opp P) (curve_add Q (point_opp Q))).
    rewrite !point_opp_inverse. rewrite add_id_l'. reflexivity.
  Qed.

  (** [scmul] is compatible with [point_opp]: [point_opp (sm n P) = "sm (-n)" P] *)
  Lemma sm_point_opp : forall n P,
    curve_add (sm n P) (point_opp (sm n P)) = id.
  Proof. intros. apply point_opp_inverse. Qed.

  (** Subtraction: [a ≥ b ⇒ sm (a - b) P = curve_add (sm a P) (point_opp (sm b P))] *)
  Lemma sm_sub : forall a b P,
    (b <= a)%nat ->
    curve_add (sm a P) (point_opp (sm b P)) = sm (a - b)%nat P.
  Proof.
    intros a b P Hle.
    (* sm a = sm ((a-b) + b) = sm(a-b) + sm b *)
    replace a with ((a - b) + b)%nat at 1 by lia.
    rewrite sm_add.
    (* ((sm(a-b) + sm b) + point_opp (sm b)) = sm(a-b) + (sm b + point_opp (sm b)) = sm(a-b) + id *)
    rewrite <- curve_add_assoc.
    rewrite point_opp_inverse.
    apply add_id_r'.
  Qed.

  (** ** Signed scalar multiplication on Z *)

  (** Signed scalar multiplication: [sm_Z d P] represents [d * P] where
      negative d uses [point_opp]. *)
  Definition sm_Z (d : Z) (P : Point) : Point :=
    if (d <? 0)%Z then point_opp (sm (Z.to_nat (-d)) P)
    else sm (Z.to_nat d) P.

  Lemma sm_Z_nonneg : forall d P, 0 <= d -> sm_Z d P = sm (Z.to_nat d) P.
  Proof.
    intros d P Hd. unfold sm_Z.
    destruct (d <? 0) eqn:E; [apply Z.ltb_lt in E; lia|reflexivity].
  Qed.

  Lemma sm_Z_neg : forall d P, d < 0 -> sm_Z d P = point_opp (sm (Z.to_nat (-d)) P).
  Proof.
    intros d P Hd. unfold sm_Z.
    destruct (d <? 0) eqn:E; [reflexivity|apply Z.ltb_ge in E; lia].
  Qed.

  Lemma sm_Z_zero : forall P, sm_Z 0 P = id.
  Proof. intros. unfold sm_Z. simpl. reflexivity. Qed.

  (** [sm_Z (a + b) P = sm_Z a P + sm_Z b P] when the result is non-negative. *)
  Lemma sm_Z_add_nonneg : forall a b P,
    0 <= a + b ->
    sm_Z (a + b) P = curve_add (sm_Z a P) (sm_Z b P).
  Proof.
    intros a b P Hsum.
    rewrite sm_Z_nonneg by lia.
    (* Case on signs of a, b *)
    destruct (Z_lt_le_dec a 0) as [Ha|Ha]; destruct (Z_lt_le_dec b 0) as [Hb|Hb].
    - (* a < 0, b < 0: sum < 0, contradiction *)
      lia.
    - (* a < 0, b >= 0: sum = b + a = b - |a|, need b >= |a| *)
      rewrite sm_Z_neg by exact Ha.
      rewrite sm_Z_nonneg by exact Hb.
      rewrite curve_add_comm.
      rewrite sm_sub by (apply Z2Nat.inj_le; lia).
      f_equal. lia.
    - (* a >= 0, b < 0: sum = a - |b|, need a >= |b| *)
      rewrite sm_Z_nonneg by exact Ha.
      rewrite sm_Z_neg by exact Hb.
      rewrite sm_sub by (apply Z2Nat.inj_le; lia).
      f_equal. lia.
    - (* a, b >= 0 *)
      rewrite !sm_Z_nonneg by lia.
      rewrite <- sm_add. f_equal. lia.
  Qed.

  (** ** Main theorem: Horner step for a single digit *)

  (** If [acc = sm_Z(2 * ws_old) P + other] and [d + 2 * ws_old >= 0],
      then adding [sm_Z d P] to [acc] gives [sm_Z (d + 2*ws_old) P + other]. *)
  Lemma horner_add_digit : forall d ws_old other P,
    0 <= ws_old ->
    0 <= d + 2 * ws_old ->
    curve_add (curve_add (sm_Z (2 * ws_old) P) other) (sm_Z d P) =
    curve_add (sm_Z (d + 2 * ws_old) P) other.
  Proof.
    intros d ws_old other P Hws_old Hsum.
    (* (sm_Z(2ws) + other) + sm_Z d
       = sm_Z(2ws) + (other + sm_Z d)        [assoc]
       = sm_Z(2ws) + (sm_Z d + other)        [comm]
       = (sm_Z(2ws) + sm_Z d) + other        [assoc]
       = sm_Z(2ws + d) + other                [sm_Z_add_nonneg]
       = sm_Z(d + 2ws) + other                [Z.add_comm] *)
    rewrite <- curve_add_assoc.
    rewrite (curve_add_comm other (sm_Z d P)).
    rewrite curve_add_assoc.
    replace (d + 2 * ws_old) with (2 * ws_old + d) by lia.
    rewrite <- sm_Z_add_nonneg by lia.
    reflexivity.
  Qed.

  (** ** Connecting digit_point to sm_Z *)

  (** We assume the table is correct: [table[i] = sm(2*i+1) P] for i in [0..3].
      Then [digit_point d table = sm_Z d P] for d in [-7..7]. *)

  (** Restate digit_point locally (same definition as in ProcessDigits.v). *)
  Definition digit_point_local (d : Z) (entries : list Point) : Point :=
    if (d =? 0)%Z then id
    else
      let abs_d := Z.abs d in
      let idx := Z.to_nat ((abs_d - 1) / 2) in
      let pt := nth idx entries id in
      if (d <? 0)%Z then point_opp pt else pt.

  (** For valid wNAF digits in {-7,-5,-3,-1,0,1,3,5,7}, if the table holds
      [1*P, 3*P, 5*P, 7*P], then [digit_point_local d table = sm_Z d P]. *)
  Lemma digit_point_is_sm_Z : forall (table : list Point) P d,
    length table = 4%nat ->
    (forall i, (i < 4)%nat -> nth i table id = sm (2 * i + 1)%nat P) ->
    Z.odd d = true \/ d = 0 ->
    -7 <= d <= 7 ->
    digit_point_local d table = sm_Z d P.
  Proof.
    intros table P d Hlen Hcorr Hodd Hrange.
    unfold digit_point_local. unfold sm_Z.
    destruct (d =? 0) eqn:Ed.
    { apply Z.eqb_eq in Ed. subst d. simpl. reflexivity. }
    apply Z.eqb_neq in Ed.
    assert (Hodd_d : Z.odd d = true) by (destruct Hodd; [assumption|lia]).
    (* Enumerate d in [-7..7] and dispatch per case.
       Even values are eliminated by Z.odd d = true. *)
    assert (Hd : d = -7 \/ d = -5 \/ d = -3 \/ d = -1 \/
                 d = 1 \/ d = 3 \/ d = 5 \/ d = 7).
    { assert (d = -7 \/ d = -6 \/ d = -5 \/ d = -4 \/ d = -3 \/
              d = -2 \/ d = -1 \/ d = 1 \/ d = 2 \/ d = 3 \/
              d = 4 \/ d = 5 \/ d = 6 \/ d = 7) as H14 by lia.
      intuition; subst; try (simpl in Hodd_d; discriminate); auto. }
    decompose [or] Hd; subst; simpl;
      try f_equal; rewrite Hcorr by (simpl; lia);
      unfold sm; simpl; reflexivity.
  Qed.

  (** ** Main theorem: the Horner step for TWO accumulators (P and Phi) *)

  (** [horner_step_proof] discharges the [Hhorner_step] context of
      process_both_digits_ok. Given:
      - dk1, dk2: digit lists
      - (Ox,Oy,Oz) = (2*ws_old_1) * P + (2*ws_old_2) * Phi
      - digit tables for P and Phi
      the sequential conditional addition of [digit_point d1 table_P] and
      [digit_point d2 table_Phi] produces the accumulator for the Horner step. *)
  Theorem horner_step_proof :
    forall (dk1 dk2 : list Z) (Px Py Pz Phix Phiy Phiz : F)
           (table_P_entries table_Phi_entries : list Point),
    length table_P_entries = 4%nat ->
    (forall i, (i < 4)%nat ->
      nth i table_P_entries id = sm (2 * i + 1)%nat (Px,Py,Pz)) ->
    length table_Phi_entries = 4%nat ->
    (forall i, (i < 4)%nat ->
      nth i table_Phi_entries id = sm (2 * i + 1)%nat (Phix,Phiy,Phiz)) ->
    (forall i, (i < length dk1)%nat ->
      Z.odd (nth i dk1 0) = true \/ nth i dk1 0 = 0) ->
    (forall i, (i < length dk2)%nat ->
      Z.odd (nth i dk2 0) = true \/ nth i dk2 0 = 0) ->
    (forall i, (i < length dk1)%nat -> -7 <= nth i dk1 0 <= 7) ->
    (forall i, (i < length dk2)%nat -> -7 <= nth i dk2 0 <= 7) ->
    (forall n, (n <= length dk1)%nat -> 0 <= weighted_sum (skipn n dk1) 0) ->
    (forall n, (n <= length dk2)%nat -> 0 <= weighted_sum (skipn n dk2) 0) ->
    forall n (Ox Oy Oz : F),
      (n < length dk1)%nat ->
      (n < length dk2)%nat ->
      let ws1_old := weighted_sum (skipn (S n) dk1) 0 in
      let ws2_old := weighted_sum (skipn (S n) dk2) 0 in
      (Ox, Oy, Oz) = curve_add
        (sm (Z.to_nat (2 * ws1_old)) (Px, Py, Pz))
        (sm (Z.to_nat (2 * ws2_old)) (Phix, Phiy, Phiz)) ->
      let d1 := nth n dk1 0 in
      let d2 := nth n dk2 0 in
      let after_d1 := if (d1 =? 0)%Z then (Ox, Oy, Oz)
                      else curve_add (Ox, Oy, Oz) (digit_point_local d1 table_P_entries) in
      (if (d2 =? 0)%Z then after_d1
       else curve_add after_d1 (digit_point_local d2 table_Phi_entries))
      = curve_add
          (sm (Z.to_nat (weighted_sum (skipn n dk1) 0)) (Px, Py, Pz))
          (sm (Z.to_nat (weighted_sum (skipn n dk2) 0)) (Phix, Phiy, Phiz)).
  Proof.
    intros dk1 dk2 Px Py Pz Phix Phiy Phiz table_P table_Phi
           HlenP HcorrP HlenPhi HcorrPhi
           Hodd1 Hodd2 Hb1 Hb2 Hws1 Hws2
           n Ox Oy Oz Hn1 Hn2.
    intros ws1_old ws2_old Hacc d1 d2 after_d1.
    (* Horner recurrence on weighted_sum *)
    assert (Hhs1 : weighted_sum (skipn n dk1) 0 = d1 + 2 * ws1_old).
    { unfold ws1_old, d1.
      replace (skipn n dk1) with (nth n dk1 0 :: skipn (S n) dk1).
      2: { symmetry. apply skipn_cons_nth_Z. exact Hn1. }
      unfold weighted_sum at 1. fold weighted_sum.
      rewrite weighted_sum_succ.
      simpl Z.of_nat. lia. }
    assert (Hhs2 : weighted_sum (skipn n dk2) 0 = d2 + 2 * ws2_old).
    { unfold ws2_old, d2.
      replace (skipn n dk2) with (nth n dk2 0 :: skipn (S n) dk2).
      2: { symmetry. apply skipn_cons_nth_Z. exact Hn2. }
      unfold weighted_sum at 1. fold weighted_sum.
      rewrite weighted_sum_succ.
      simpl Z.of_nat. lia. }
    assert (Hw1old : 0 <= ws1_old) by (apply Hws1; lia).
    assert (Hw2old : 0 <= ws2_old) by (apply Hws2; lia).
    assert (Hw1new : 0 <= weighted_sum (skipn n dk1) 0) by (apply Hws1; lia).
    assert (Hw2new : 0 <= weighted_sum (skipn n dk2) 0) by (apply Hws2; lia).
    assert (Hd1b : -7 <= d1 <= 7) by (apply Hb1; lia).
    assert (Hd2b : -7 <= d2 <= 7) by (apply Hb2; lia).
    assert (Hd1odd : Z.odd d1 = true \/ d1 = 0) by (apply Hodd1; lia).
    assert (Hd2odd : Z.odd d2 = true \/ d2 = 0) by (apply Hodd2; lia).
    (* Express (Ox,Oy,Oz) using sm_Z *)
    assert (Hacc' : (Ox, Oy, Oz) = curve_add
                     (sm_Z (2 * ws1_old) (Px,Py,Pz))
                     (sm_Z (2 * ws2_old) (Phix,Phiy,Phiz))).
    { rewrite !sm_Z_nonneg by lia. exact Hacc. }
    (* Replace ws_new by d + 2*ws_old in goal's conclusion (which has sm(Z.to_nat ws_new)(P)).
       First rewrite ws_new, then convert sm to sm_Z for algebraic reasoning. *)
    replace (sm (Z.to_nat (weighted_sum (skipn n dk1) 0)) (Px,Py,Pz))
      with (sm_Z (d1 + 2 * ws1_old) (Px,Py,Pz))
      by (rewrite <- Hhs1; apply sm_Z_nonneg; lia).
    replace (sm (Z.to_nat (weighted_sum (skipn n dk2) 0)) (Phix,Phiy,Phiz))
      with (sm_Z (d2 + 2 * ws2_old) (Phix,Phiy,Phiz))
      by (rewrite <- Hhs2; apply sm_Z_nonneg; lia).
    (* Discharge digit_point to sm_Z *)
    assert (Hdp1 : d1 <> 0 ->
      digit_point_local d1 table_P = sm_Z d1 (Px, Py, Pz)).
    { intros _. apply digit_point_is_sm_Z; assumption. }
    assert (Hdp2 : d2 <> 0 ->
      digit_point_local d2 table_Phi = sm_Z d2 (Phix, Phiy, Phiz)).
    { intros _. apply digit_point_is_sm_Z; assumption. }
    (* Helper to normalize Z.add in the goal *)
    Ltac norm_zadd :=
      repeat match goal with
      | |- context [0 + ?x] => replace (0 + x) with x by lia
      | |- context [?x + 0] => replace (x + 0) with x by lia
      end.
    (* Case split on d1 = 0 *)
    unfold after_d1.
    destruct (d1 =? 0) eqn:Ed1.
    - apply Z.eqb_eq in Ed1.
      replace d1 with 0 in * by lia. norm_zadd.
      destruct (d2 =? 0) eqn:Ed2.
      + apply Z.eqb_eq in Ed2.
        replace d2 with 0 in * by lia. norm_zadd. exact Hacc'.
      + apply Z.eqb_neq in Ed2.
        rewrite Hdp2 by exact Ed2.
        rewrite Hacc'.
        rewrite curve_add_comm with (P := sm_Z (2*ws1_old) (Px,Py,Pz))
                                     (Q := sm_Z (2*ws2_old) (Phix,Phiy,Phiz)).
        rewrite horner_add_digit by lia.
        rewrite curve_add_comm. reflexivity.
    - apply Z.eqb_neq in Ed1.
      rewrite Hdp1 by exact Ed1.
      rewrite Hacc'.
      (* Goal: ((sm_Z(2ws1) P + sm_Z(2ws2) Phi) + sm_Z d1 P)
               = sm_Z(d1+2ws1) P + sm_Z(d2+2ws2) Phi
         Use assoc: = sm_Z(2ws1) P + (sm_Z(2ws2) Phi + sm_Z d1 P)
         Then comm inner: = sm_Z(2ws1) P + (sm_Z d1 P + sm_Z(2ws2) Phi)
         Then assoc back: = (sm_Z(2ws1) P + sm_Z d1 P) + sm_Z(2ws2) Phi
         Then sm_Z_add: = sm_Z(2ws1+d1) P + sm_Z(2ws2) Phi *)
      rewrite <- curve_add_assoc.
      rewrite (curve_add_comm (sm_Z (2*ws2_old) (Phix,Phiy,Phiz)) (sm_Z d1 (Px,Py,Pz))).
      rewrite curve_add_assoc.
      rewrite <- (sm_Z_add_nonneg (2*ws1_old) d1 (Px,Py,Pz) ltac:(lia)).
      replace (2 * ws1_old + d1) with (d1 + 2 * ws1_old) by lia.
      destruct (d2 =? 0) eqn:Ed2.
      + apply Z.eqb_eq in Ed2.
        replace d2 with 0 in * by lia. norm_zadd. reflexivity.
      + apply Z.eqb_neq in Ed2.
        rewrite Hdp2 by exact Ed2.
        (* Rearrange: (A + B) + C  →  A + (B + C)  →  A + sm_Z(d2+2ws2)(Phi) *)
        rewrite <- curve_add_assoc.
        rewrite <- (sm_Z_add_nonneg (2*ws2_old) d2 (Phix,Phiy,Phiz) ltac:(lia)).
        replace (2 * ws2_old + d2) with (d2 + 2 * ws2_old) by lia.
        reflexivity.
  Qed.

End HornerAlgebra.
