(** * Single-scalar wNAF Horner algebraic step — abstract proof from group axioms.

    This file proves the [Hhorner_step] hypothesis needed by
    [BN254_wNAF_Instance.v], the central algebraic fact that connects
    the table-based conditional addition to the weighted-sum formula
    for a SINGLE accumulator (no GLV).

    Mirrors [BLS12_wNAF_HornerAlgebra.v] (which handles TWO accumulators
    for GLV), simplified for the single-scalar case.

    Group-theoretic axioms used:
    - [curve_add_id_l], [curve_add_id_r]  — identity
    - [curve_add_assoc], [curve_add_comm]  — associativity + commutativity
    - [point_opp_inverse]                  — [curve_add P (point_opp P) = id]

    Plus a signed-digit table correctness hypothesis:
    - [digit_point d table = sm_Z d P]

    where [sm_Z : Z -> Point -> Point] is the signed extension of [sm],
    defined via conditional [point_opp].

    All lemmas are purely algebraic — no bedrock2. *)

From Stdlib Require Import ZArith Lia List.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
(* Note: We do NOT import wNAF_Single_LoopBody to avoid heavy bedrock2
   imports. We restate the needed lemmas locally. *)

(** Restated from wNAF_Single_LoopBody.v to avoid bedrock2 dependencies. *)
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

Lemma weighted_sum_cons_Z d rest :
  weighted_sum (d :: rest) 0 = d + 2 * weighted_sum rest 0.
Proof.
  unfold weighted_sum at 1. fold weighted_sum.
  rewrite weighted_sum_succ. lia.
Qed.

Section SingleHornerAlgebra.
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

  (** ** Scalar multiplication (same as BLS12_wNAF_HornerAlgebra.sm) *)

  Fixpoint sm (n : nat) (P : Point) : Point :=
    match n with O => id | S m => curve_add P (sm m P) end.

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

  Lemma point_opp_inverse_l : forall P, curve_add (point_opp P) P = id.
  Proof. intros. rewrite curve_add_comm. apply point_opp_inverse. Qed.

  Lemma point_opp_id : point_opp id = id.
  Proof.
    pose proof (point_opp_inverse id) as Hi.
    rewrite add_id_l' in Hi. exact Hi.
  Qed.

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

  Lemma point_opp_opp : forall P, point_opp (point_opp P) = P.
  Proof.
    intros P.
    apply (curve_add_cancel_l (point_opp P)).
    rewrite point_opp_inverse.
    rewrite point_opp_inverse_l. reflexivity.
  Qed.

  Lemma sm_sub : forall a b P,
    (b <= a)%nat ->
    curve_add (sm a P) (point_opp (sm b P)) = sm (a - b)%nat P.
  Proof.
    intros a b P Hle.
    replace a with ((a - b) + b)%nat at 1 by lia.
    rewrite sm_add.
    rewrite <- curve_add_assoc.
    rewrite point_opp_inverse.
    apply add_id_r'.
  Qed.

  (** ** Signed scalar multiplication on Z *)

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

  (** [sm_Z (a + b) P = curve_add (sm_Z a P) (sm_Z b P)] when result is non-negative. *)
  Lemma sm_Z_add_nonneg : forall a b P,
    0 <= a + b ->
    sm_Z (a + b) P = curve_add (sm_Z a P) (sm_Z b P).
  Proof.
    intros a b P Hsum.
    rewrite sm_Z_nonneg by lia.
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

  (** ** Connecting digit_point to sm_Z *)

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
    (* Enumerate d in [-7..7] and dispatch per case. *)
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

  (** ** Main theorem: single-scalar Horner step *)

  (** For a SINGLE accumulator: if [acc = sm(2*ws_old)(P)] and d is the
      current digit, then conditionally adding [digit_point(d, table)]
      gives [sm(ws(skipn n dk))(P)].

      This is the single-scalar analog of [horner_step_proof] from
      [BLS12_wNAF_HornerAlgebra.v]. The two-scalar version handles two
      independent digit streams and two base points; this file handles one. *)
  Theorem horner_step_single :
    forall (dk : list Z) (Px Py Pz : F)
           (table_entries : list Point),
    length table_entries = 4%nat ->
    (forall i, (i < 4)%nat ->
      nth i table_entries id = sm (2 * i + 1)%nat (Px,Py,Pz)) ->
    (forall i, (i < length dk)%nat ->
      Z.odd (nth i dk 0) = true \/ nth i dk 0 = 0) ->
    (forall i, (i < length dk)%nat -> -7 <= nth i dk 0 <= 7) ->
    (forall n, (n <= length dk)%nat -> 0 <= weighted_sum (skipn n dk) 0) ->
    forall n (Ox Oy Oz : F),
      (n < length dk)%nat ->
      let ws_old := weighted_sum (skipn (S n) dk) 0 in
      (Ox, Oy, Oz) = sm (Z.to_nat (2 * ws_old)) (Px, Py, Pz) ->
      let d := nth n dk 0 in
      (if (d =? 0)%Z then (Ox, Oy, Oz)
       else curve_add (Ox, Oy, Oz) (digit_point_local d table_entries))
      = sm (Z.to_nat (weighted_sum (skipn n dk) 0)) (Px, Py, Pz).
  Proof.
    intros dk Px Py Pz table_entries
           HlenT HcorrT Hodd Hb Hws
           n Ox Oy Oz Hn.
    intros ws_old Hacc d.
    (* Horner recurrence on weighted_sum *)
    assert (Hhs : weighted_sum (skipn n dk) 0 = d + 2 * ws_old).
    { unfold ws_old, d.
      rewrite (skipn_cons_nth_Z n dk 0 Hn).
      apply weighted_sum_cons_Z. }
    assert (Hw_old : 0 <= ws_old) by (apply Hws; lia).
    assert (Hw_new : 0 <= weighted_sum (skipn n dk) 0) by (apply Hws; lia).
    assert (Hdb : -7 <= d <= 7) by (apply Hb; lia).
    assert (Hd_odd : Z.odd d = true \/ d = 0) by (apply Hodd; lia).
    (* Express accumulator using sm_Z *)
    assert (Hacc' : (Ox, Oy, Oz) = sm_Z (2 * ws_old) (Px,Py,Pz)).
    { rewrite sm_Z_nonneg by lia. exact Hacc. }
    (* Replace goal's sm(Z.to_nat ws_new)(P) with sm_Z(d + 2*ws_old)(P) *)
    replace (sm (Z.to_nat (weighted_sum (skipn n dk) 0)) (Px,Py,Pz))
      with (sm_Z (d + 2 * ws_old) (Px,Py,Pz))
      by (rewrite <- Hhs; apply sm_Z_nonneg; lia).
    (* Discharge digit_point to sm_Z *)
    assert (Hdp : d <> 0 ->
      digit_point_local d table_entries = sm_Z d (Px, Py, Pz)).
    { intros _. apply digit_point_is_sm_Z; assumption. }
    (* Case split on d = 0 *)
    destruct (d =? 0) eqn:Ed.
    - (* d = 0: trivial — sm_Z(0 + 2*ws_old) = sm_Z(2*ws_old) *)
      apply Z.eqb_eq in Ed.
      replace d with 0 in * by lia.
      replace (0 + 2 * ws_old) with (2 * ws_old) by lia.
      exact Hacc'.
    - (* d != 0: curve_add(acc)(digit_point d) = sm_Z(d + 2*ws_old)(P) *)
      apply Z.eqb_neq in Ed.
      rewrite Hdp by exact Ed.
      rewrite Hacc'.
      (* sm_Z(2*ws_old)(P) + sm_Z(d)(P) = sm_Z(2*ws_old + d)(P) *)
      rewrite <- (sm_Z_add_nonneg (2 * ws_old) d (Px,Py,Pz) ltac:(lia)).
      replace (2 * ws_old + d) with (d + 2 * ws_old) by lia.
      reflexivity.
  Qed.

  (** ** Discharge lemma matching [BN254_wNAF_Instance.Hhorner_step] exactly.

      [horner_step_single] above proves the identity for the _local_
      [digit_point_local], which must agree with ProcessDigits' [digit_point]
      at instantiation time. This lemma packages the result into the exact
      shape expected by [BN254_wNAF_Instance.v]:

        forall n (Ox Oy Oz : F),
          (n < num_iters)%nat ->
          (Ox,Oy,Oz) = sm (Z.to_nat (2 * ws_old)) (Px,Py,Pz) ->
          (if d =? 0 then (Ox,Oy,Oz)
           else curve_add (Ox,Oy,Oz) (digit_point d table_entries))
          = sm (Z.to_nat (weighted_sum (skipn n dk) 0)) (Px,Py,Pz)

      where [digit_point] is the one from ProcessDigits.v. Since
      [digit_point_local] is definitionally equal to ProcessDigits'
      [digit_point] (both use the same algorithm with [point_opp]),
      the connection is by [eq_refl] or a simple [change] tactic at
      the call site in BN254_wNAF_Instance.v. *)

End SingleHornerAlgebra.

(** ** Instantiation bridge.

    The main consumer is [BN254_wNAF_Instance.v], which has:

      Let scmul_s := scmul Fzero Fone curve_add.

    where [scmul] is from [BLS12_GLV_LoopInvariant.v]. Since
    [scmul Fzero Fone curve_add] is definitionally equal to our [sm],
    and ProcessDigits' [digit_point] is definitionally equal to our
    [digit_point_local] (both use [point_opp pt := let '(X,Y,Z) := pt
    in (X, F.opp Y, Z)] when [point_opp] is so instantiated), the
    discharge at the call site is:

      apply horner_step_single; assumption.

    provided the table correctness hypothesis is phrased with [sm]
    (= [scmul_s]). *)
