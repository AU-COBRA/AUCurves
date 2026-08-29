(** * Single-scalar wNAF Horner algebraic step — abstract proof from group axioms.

    This file proves the [Hhorner_step] hypothesis needed by
    [BN254_wNAF_Instance.v] and [P256_wNAF_Instance.v]: the central
    algebraic fact that connects the table-based conditional addition to
    the weighted-sum formula for a SINGLE accumulator (no GLV).

    Mirrors [BLS12_wNAF_HornerAlgebra.v] (which handles TWO accumulators
    for GLV), simplified for the single-scalar case.

    ** G6: the algebra is stated up to a parametric equivalence **

    Point-level equality is the Section parameter [pt_eq], not Leibniz
    equality on raw triples.  Leibniz equality on triples is FALSE for
    the Renes-Costello-Batina projective addition
    (BLS12_wNAF_PointOppInverse.v); the RCB formula only satisfies the
    group laws up to projective equivalence.  Instantiating
    [pt_eq := eq], [oncurve := fun _ => True] recovers the previous
    (Leibniz) interface verbatim, so this generalisation is conservative
    for BN254/BN256/BN446.

    ** HONESTY: the hypotheses are STRICTLY STRONGER than before **

    Quotienting by [pt_eq] forces an on-curve side condition on every
    group law, because [pt_eq] is not a congruence for [curve_add] on
    arbitrary triples and because [oncurve] is not [pt_eq]-invariant
    (e.g. [pt_eq (0,0,0) (0,1,0)] holds but (0,0,0) is not a projective
    point).  Concretely:

      - every group-law hypothesis gained [oncurve] premises;
      - three NEW hypotheses appeared: [oncurve_id], [oncurve_curve_add],
        [oncurve_point_opp] (closure), plus the two congruences
        [curve_add_Proper] and [point_opp_Proper];
      - the table hypothesis of [digit_point_is_sm_Z] /
        [horner_step_single] gained an [oncurve] conjunct per entry, and
        its equation became [pt_eq];
      - [horner_step_single] gained [oncurve] on the base point and on
        the incoming accumulator, and its conclusion is now [pt_eq].

    A caller who instantiates [pt_eq := eq] and [oncurve := fun _ => True]
    must still supply the closure/congruence hypotheses; for [eq] they
    are [I]-style trivialities ([eq_Equivalence], [f_equal]).

    Group-theoretic axioms used:
    - [curve_add_id_l], [curve_add_id_r]  — identity
    - [curve_add_assoc], [curve_add_comm]  — associativity + commutativity
    - [point_opp_inverse]                  — [curve_add P (point_opp P) ~ id]

    Plus a signed-digit table correctness hypothesis:
    - [pt_eq (digit_point d table) (sm_Z d P)]

    where [sm_Z : Z -> Point -> Point] is the signed extension of [sm],
    defined via conditional [point_opp].

    All lemmas are purely algebraic — no bedrock2. *)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import RelationClasses.
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

  (** ** G6: the point-level equivalence and the on-curve predicate *)

  Context (pt_eq : Point -> Point -> Prop).
  Context (pt_eq_equiv : Equivalence pt_eq).
  Context (oncurve : Point -> Prop).

  (** Closure of [oncurve]. *)
  Context (oncurve_id : oncurve id).
  Context (oncurve_curve_add :
    forall P Q, oncurve P -> oncurve Q -> oncurve (curve_add P Q)).
  Context (oncurve_point_opp :
    forall P, oncurve P -> oncurve (point_opp P)).

  (** Congruence. *)
  Context (curve_add_Proper : forall P P' Q Q',
    oncurve P -> oncurve P' -> oncurve Q -> oncurve Q' ->
    pt_eq P P' -> pt_eq Q Q' -> pt_eq (curve_add P Q) (curve_add P' Q')).
  Context (point_opp_Proper : forall P P',
    oncurve P -> oncurve P' -> pt_eq P P' ->
    pt_eq (point_opp P) (point_opp P')).

  (** The group laws, up to [pt_eq]. *)
  Context (curve_add_id_r : forall x y z,
    oncurve (x, y, z) -> pt_eq (curve_add (x, y, z) id) (x, y, z)).
  Context (curve_add_id_l : forall x y z,
    oncurve (x, y, z) -> pt_eq (curve_add id (x, y, z)) (x, y, z)).
  Context (curve_add_assoc : forall P Q R,
    oncurve P -> oncurve Q -> oncurve R ->
    pt_eq (curve_add P (curve_add Q R)) (curve_add (curve_add P Q) R)).
  Context (curve_add_comm : forall P Q,
    oncurve P -> oncurve Q -> pt_eq (curve_add P Q) (curve_add Q P)).
  Context (point_opp_inverse : forall P,
    oncurve P -> pt_eq (curve_add P (point_opp P)) id).

  (** Explicit projections of [pt_eq_equiv].  Used instead of the setoid
      tactics because [curve_add_Proper] carries [oncurve] side
      conditions and so is not a [Proper] instance. *)
  Local Lemma pt_refl : forall P, pt_eq P P.
  Proof. destruct pt_eq_equiv as [Hr _ _]. exact Hr. Qed.
  Local Lemma pt_sym : forall P Q, pt_eq P Q -> pt_eq Q P.
  Proof. destruct pt_eq_equiv as [_ Hs _]. exact Hs. Qed.
  Local Lemma pt_trans : forall P Q R, pt_eq P Q -> pt_eq Q R -> pt_eq P R.
  Proof. destruct pt_eq_equiv as [_ _ Ht]. exact Ht. Qed.

  (** ** Scalar multiplication (same as BLS12_wNAF_HornerAlgebra.sm) *)

  Fixpoint sm (n : nat) (P : Point) : Point :=
    match n with O => id | S m => curve_add P (sm m P) end.

  Lemma oncurve_sm : forall n P, oncurve P -> oncurve (sm n P).
  Proof.
    induction n as [|n' IH]; intros P HP; simpl.
    - exact oncurve_id.
    - apply oncurve_curve_add; [exact HP | apply IH; exact HP].
  Qed.

  Lemma add_id_r' : forall P, oncurve P -> pt_eq (curve_add P id) P.
  Proof. intros [[x y] z] H. apply curve_add_id_r. exact H. Qed.
  Lemma add_id_l' : forall P, oncurve P -> pt_eq (curve_add id P) P.
  Proof. intros [[x y] z] H. apply curve_add_id_l. exact H. Qed.

  Lemma sm_add : forall a b P, oncurve P ->
    pt_eq (sm (a + b)%nat P) (curve_add (sm a P) (sm b P)).
  Proof.
    induction a as [|a' IH]; intros b P HP; simpl.
    - apply pt_sym. apply add_id_l'. apply oncurve_sm. exact HP.
    - apply (pt_trans
               (curve_add P (sm (a' + b)%nat P))
               (curve_add P (curve_add (sm a' P) (sm b P)))
               (curve_add (curve_add P (sm a' P)) (sm b P))).
      + apply curve_add_Proper;
          [ exact HP | exact HP
          | apply oncurve_sm; exact HP
          | apply oncurve_curve_add; apply oncurve_sm; exact HP
          | apply pt_refl
          | apply IH; exact HP ].
      + apply curve_add_assoc;
          [ exact HP | apply oncurve_sm; exact HP | apply oncurve_sm; exact HP ].
  Qed.

  (** ** Group inverse properties *)

  Lemma point_opp_inverse_l : forall P,
    oncurve P -> pt_eq (curve_add (point_opp P) P) id.
  Proof.
    intros P HP.
    apply (pt_trans (curve_add (point_opp P) P) (curve_add P (point_opp P)) id).
    - apply curve_add_comm; [apply oncurve_point_opp; exact HP | exact HP].
    - apply point_opp_inverse; exact HP.
  Qed.

  Lemma point_opp_id : pt_eq (point_opp id) id.
  Proof.
    apply (pt_trans (point_opp id) (curve_add id (point_opp id)) id).
    - apply pt_sym. apply add_id_l'. apply oncurve_point_opp. exact oncurve_id.
    - apply point_opp_inverse. exact oncurve_id.
  Qed.

  Local Lemma opp_add_cancel : forall P Q,
    oncurve P -> oncurve Q ->
    pt_eq (curve_add (point_opp P) (curve_add P Q)) Q.
  Proof.
    intros P Q HP HQ.
    assert (Hoc : oncurve (point_opp P)) by (apply oncurve_point_opp; exact HP).
    apply (pt_trans
             (curve_add (point_opp P) (curve_add P Q))
             (curve_add (curve_add (point_opp P) P) Q)
             Q).
    - apply curve_add_assoc; assumption.
    - apply (pt_trans (curve_add (curve_add (point_opp P) P) Q)
                      (curve_add id Q) Q).
      + apply curve_add_Proper;
          [ apply oncurve_curve_add; assumption
          | exact oncurve_id
          | exact HQ | exact HQ
          | apply point_opp_inverse_l; exact HP
          | apply pt_refl ].
      + apply add_id_l'; exact HQ.
  Qed.

  Lemma curve_add_cancel_l : forall P Q R,
    oncurve P -> oncurve Q -> oncurve R ->
    pt_eq (curve_add P Q) (curve_add P R) -> pt_eq Q R.
  Proof.
    intros P Q R HP HQ HR H.
    assert (Hoc : oncurve (point_opp P)) by (apply oncurve_point_opp; exact HP).
    apply (pt_trans Q (curve_add (point_opp P) (curve_add P Q)) R).
    - apply pt_sym. apply opp_add_cancel; assumption.
    - apply (pt_trans (curve_add (point_opp P) (curve_add P Q))
                      (curve_add (point_opp P) (curve_add P R)) R).
      + apply curve_add_Proper;
          [ exact Hoc | exact Hoc
          | apply oncurve_curve_add; assumption
          | apply oncurve_curve_add; assumption
          | apply pt_refl | exact H ].
      + apply opp_add_cancel; assumption.
  Qed.

  Lemma point_opp_opp : forall P,
    oncurve P -> pt_eq (point_opp (point_opp P)) P.
  Proof.
    intros P HP.
    assert (Hoc : oncurve (point_opp P)) by (apply oncurve_point_opp; exact HP).
    apply (curve_add_cancel_l (point_opp P));
      [ exact Hoc | apply oncurve_point_opp; exact Hoc | exact HP | ].
    apply (pt_trans (curve_add (point_opp P) (point_opp (point_opp P)))
                    id
                    (curve_add (point_opp P) P)).
    - apply point_opp_inverse; exact Hoc.
    - apply pt_sym. apply point_opp_inverse_l; exact HP.
  Qed.

  Lemma sm_sub : forall a b P,
    oncurve P -> (b <= a)%nat ->
    pt_eq (curve_add (sm a P) (point_opp (sm b P))) (sm (a - b)%nat P).
  Proof.
    intros a b P HP Hle.
    assert (HA : oncurve (sm (a - b)%nat P)) by (apply oncurve_sm; exact HP).
    assert (HB : oncurve (sm b P)) by (apply oncurve_sm; exact HP).
    assert (HoB : oncurve (point_opp (sm b P)))
      by (apply oncurve_point_opp; exact HB).
    replace a with ((a - b) + b)%nat at 1 by lia.
    apply (pt_trans
             (curve_add (sm ((a - b) + b)%nat P) (point_opp (sm b P)))
             (curve_add (curve_add (sm (a - b)%nat P) (sm b P))
                        (point_opp (sm b P)))
             (sm (a - b)%nat P)).
    - apply curve_add_Proper;
        [ apply oncurve_sm; exact HP
        | apply oncurve_curve_add; assumption
        | exact HoB | exact HoB
        | apply sm_add; exact HP
        | apply pt_refl ].
    - apply (pt_trans
               (curve_add (curve_add (sm (a - b)%nat P) (sm b P))
                          (point_opp (sm b P)))
               (curve_add (sm (a - b)%nat P)
                          (curve_add (sm b P) (point_opp (sm b P))))
               (sm (a - b)%nat P)).
      + apply pt_sym. apply curve_add_assoc; assumption.
      + apply (pt_trans
                 (curve_add (sm (a - b)%nat P)
                            (curve_add (sm b P) (point_opp (sm b P))))
                 (curve_add (sm (a - b)%nat P) id)
                 (sm (a - b)%nat P)).
        * apply curve_add_Proper;
            [ exact HA | exact HA
            | apply oncurve_curve_add; assumption
            | exact oncurve_id
            | apply pt_refl
            | apply point_opp_inverse; exact HB ].
        * apply add_id_r'; exact HA.
  Qed.

  (** ** Signed scalar multiplication on Z *)

  Definition sm_Z (d : Z) (P : Point) : Point :=
    if (d <? 0)%Z then point_opp (sm (Z.to_nat (-d)) P)
    else sm (Z.to_nat d) P.

  Lemma oncurve_sm_Z : forall d P, oncurve P -> oncurve (sm_Z d P).
  Proof.
    intros d P HP. unfold sm_Z. destruct (d <? 0)%Z.
    - apply oncurve_point_opp. apply oncurve_sm. exact HP.
    - apply oncurve_sm. exact HP.
  Qed.

  (** [sm_Z_nonneg], [sm_Z_neg], [sm_Z_zero] unfold the DEFINITION of
      [sm_Z]; no group law is involved, so they stay Leibniz. *)
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

  (** [sm_Z (a + b) P ~ curve_add (sm_Z a P) (sm_Z b P)] when the sum is
      non-negative. *)
  Lemma sm_Z_add_nonneg : forall a b P,
    oncurve P -> 0 <= a + b ->
    pt_eq (sm_Z (a + b) P) (curve_add (sm_Z a P) (sm_Z b P)).
  Proof.
    intros a b P HP Hsum.
    rewrite sm_Z_nonneg by lia.
    destruct (Z_lt_le_dec a 0) as [Ha|Ha]; destruct (Z_lt_le_dec b 0) as [Hb|Hb].
    - (* a < 0, b < 0: sum < 0, contradiction *)
      lia.
    - (* a < 0, b >= 0: sum = b - |a|, and |a| <= b *)
      rewrite sm_Z_neg by exact Ha.
      rewrite sm_Z_nonneg by exact Hb.
      assert (Hle : (Z.to_nat (- a) <= Z.to_nat b)%nat)
        by (apply Z2Nat.inj_le; lia).
      assert (Hidx : Z.to_nat (a + b) = (Z.to_nat b - Z.to_nat (- a))%nat)
        by lia.
      rewrite Hidx.
      apply pt_sym.
      apply (pt_trans
               (curve_add (point_opp (sm (Z.to_nat (- a)) P)) (sm (Z.to_nat b) P))
               (curve_add (sm (Z.to_nat b) P) (point_opp (sm (Z.to_nat (- a)) P)))
               (sm (Z.to_nat b - Z.to_nat (- a))%nat P)).
      + apply curve_add_comm;
          [ apply oncurve_point_opp; apply oncurve_sm; exact HP
          | apply oncurve_sm; exact HP ].
      + apply sm_sub; [exact HP | exact Hle].
    - (* a >= 0, b < 0: sum = a - |b|, and |b| <= a *)
      rewrite sm_Z_nonneg by exact Ha.
      rewrite sm_Z_neg by exact Hb.
      assert (Hle : (Z.to_nat (- b) <= Z.to_nat a)%nat)
        by (apply Z2Nat.inj_le; lia).
      assert (Hidx : Z.to_nat (a + b) = (Z.to_nat a - Z.to_nat (- b))%nat)
        by lia.
      rewrite Hidx.
      apply pt_sym. apply sm_sub; [exact HP | exact Hle].
    - (* a, b >= 0 *)
      rewrite !sm_Z_nonneg by lia.
      assert (Hidx : Z.to_nat (a + b) = (Z.to_nat a + Z.to_nat b)%nat) by lia.
      rewrite Hidx. apply sm_add; exact HP.
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

  (** The valid-digit enumeration shared by the two lemmas below. *)
  Local Lemma wnaf_digit_cases (d : Z) :
    d <> 0 -> Z.odd d = true \/ d = 0 -> -7 <= d <= 7 ->
    d = -7 \/ d = -5 \/ d = -3 \/ d = -1 \/
    d = 1 \/ d = 3 \/ d = 5 \/ d = 7.
  Proof.
    intros Ed Hodd Hrange.
    assert (Hodd_d : Z.odd d = true) by (destruct Hodd; [assumption|lia]).
    assert (d = -7 \/ d = -6 \/ d = -5 \/ d = -4 \/ d = -3 \/
            d = -2 \/ d = -1 \/ d = 1 \/ d = 2 \/ d = 3 \/
            d = 4 \/ d = 5 \/ d = 6 \/ d = 7) as H14 by lia.
    intuition; subst; try (simpl in Hodd_d; discriminate); auto.
  Qed.

  (** The table entries are on the curve, hence so is the digit point. *)
  Lemma digit_point_local_oncurve : forall (table : list Point) d,
    length table = 4%nat ->
    (forall i, (i < 4)%nat -> oncurve (nth i table id)) ->
    Z.odd d = true \/ d = 0 ->
    -7 <= d <= 7 ->
    oncurve (digit_point_local d table).
  Proof.
    intros table d Hlen Hoc Hodd Hrange.
    unfold digit_point_local.
    destruct (d =? 0) eqn:Ed.
    { exact oncurve_id. }
    apply Z.eqb_neq in Ed.
    pose proof (wnaf_digit_cases d Ed Hodd Hrange) as Hd.
    decompose [or] Hd; subst d; simpl;
      first
        [ exact (Hoc 0%nat ltac:(lia))
        | exact (Hoc 1%nat ltac:(lia))
        | exact (Hoc 2%nat ltac:(lia))
        | exact (Hoc 3%nat ltac:(lia))
        | exact (oncurve_point_opp _ (Hoc 0%nat ltac:(lia)))
        | exact (oncurve_point_opp _ (Hoc 1%nat ltac:(lia)))
        | exact (oncurve_point_opp _ (Hoc 2%nat ltac:(lia)))
        | exact (oncurve_point_opp _ (Hoc 3%nat ltac:(lia)))
        | lazymatch goal with
          | |- ?G => fail 99 "DIGIT-CASE UNHANDLED (oncurve):" G
          end ].
  Qed.

  (** Same statement, but with a proof term that mentions EVERY Section
      variable, so that its Section-discharged argument list is exactly
      the declaration order (like [horner_step_single]'s) and callers do
      not have to guess which variables the proof happens to use. *)
  Lemma digit_point_oncurve_full : forall (table : list Point) d,
    length table = 4%nat ->
    (forall i, (i < 4)%nat -> oncurve (nth i table id)) ->
    Z.odd d = true \/ d = 0 ->
    -7 <= d <= 7 ->
    oncurve (digit_point_local d table).
  Proof.
    intros table d Hlen Hoc Hodd Hrange.
    pose proof pt_refl as _Hrefl.
    pose proof oncurve_curve_add as _Hadd.
    pose proof curve_add_Proper as _HP.
    pose proof point_opp_Proper as _HoP.
    pose proof curve_add_id_r as _Hr.
    pose proof curve_add_id_l as _Hl.
    pose proof curve_add_assoc as _Ha.
    pose proof curve_add_comm as _Hc.
    pose proof point_opp_inverse as _Hi.
    apply digit_point_local_oncurve; assumption.
  Qed.

  (** For valid wNAF digits in {-7,-5,-3,-1,0,1,3,5,7}, if the table holds
      points [pt_eq]-equal to [1*P, 3*P, 5*P, 7*P], then
      [digit_point_local d table ~ sm_Z d P].

      HONESTY: the table hypothesis is strictly stronger than the
      Leibniz version it replaces — it demands [oncurve] of every entry
      in addition to the (weaker) [pt_eq] equation. *)
  Lemma digit_point_is_sm_Z : forall (table : list Point) P d,
    oncurve P ->
    length table = 4%nat ->
    (forall i, (i < 4)%nat ->
       oncurve (nth i table id)
       /\ pt_eq (nth i table id) (sm (2 * i + 1)%nat P)) ->
    Z.odd d = true \/ d = 0 ->
    -7 <= d <= 7 ->
    pt_eq (digit_point_local d table) (sm_Z d P).
  Proof.
    intros table P d HP Hlen Hcorr Hodd Hrange.
    unfold digit_point_local, sm_Z.
    destruct (d =? 0) eqn:Ed.
    { apply Z.eqb_eq in Ed. subst d. simpl. apply pt_refl. }
    apply Z.eqb_neq in Ed.
    pose proof (wnaf_digit_cases d Ed Hodd Hrange) as Hd.
    (* Each branch is a single [exact]: [simpl] has already unfolded [sm]
       on the right-hand side, so a tactic like [apply oncurve_sm] would
       have to RE-FOLD the fixpoint at an unknown exponent, which the
       unifier cannot do.  Supplying the exponent literally (table index
       i holds the (2i+1)-th multiple) turns every side condition into a
       closed-term conversion check, which [exact] discharges. *)
    decompose [or] Hd; subst d; simpl;
      first
        [ exact (proj2 (Hcorr 0%nat ltac:(lia)))
        | exact (proj2 (Hcorr 1%nat ltac:(lia)))
        | exact (proj2 (Hcorr 2%nat ltac:(lia)))
        | exact (proj2 (Hcorr 3%nat ltac:(lia)))
        | exact (point_opp_Proper _ _ (proj1 (Hcorr 0%nat ltac:(lia)))
                   (oncurve_sm 1%nat P HP) (proj2 (Hcorr 0%nat ltac:(lia))))
        | exact (point_opp_Proper _ _ (proj1 (Hcorr 1%nat ltac:(lia)))
                   (oncurve_sm 3%nat P HP) (proj2 (Hcorr 1%nat ltac:(lia))))
        | exact (point_opp_Proper _ _ (proj1 (Hcorr 2%nat ltac:(lia)))
                   (oncurve_sm 5%nat P HP) (proj2 (Hcorr 2%nat ltac:(lia))))
        | exact (point_opp_Proper _ _ (proj1 (Hcorr 3%nat ltac:(lia)))
                   (oncurve_sm 7%nat P HP) (proj2 (Hcorr 3%nat ltac:(lia))))
        | lazymatch goal with
          | |- ?G => fail 99 "DIGIT-CASE UNHANDLED:" G
          end ].
  Qed.

  (** ** Main theorem: single-scalar Horner step *)

  (** For a SINGLE accumulator: if [acc ~ sm(2*ws_old)(P)] and d is the
      current digit, then conditionally adding [digit_point(d, table)]
      gives a point [pt_eq] to [sm(ws(skipn n dk))(P)].

      This is the single-scalar analog of [horner_step_proof] from
      [BLS12_wNAF_HornerAlgebra.v]. The two-scalar version handles two
      independent digit streams and two base points; this file handles one. *)
  Theorem horner_step_single :
    forall (dk : list Z) (Px Py Pz : F)
           (table_entries : list Point),
    oncurve (Px, Py, Pz) ->
    length table_entries = 4%nat ->
    (forall i, (i < 4)%nat ->
       oncurve (nth i table_entries id)
       /\ pt_eq (nth i table_entries id) (sm (2 * i + 1)%nat (Px,Py,Pz))) ->
    (forall i, (i < length dk)%nat ->
      Z.odd (nth i dk 0) = true \/ nth i dk 0 = 0) ->
    (forall i, (i < length dk)%nat -> -7 <= nth i dk 0 <= 7) ->
    (forall n, (n <= length dk)%nat -> 0 <= weighted_sum (skipn n dk) 0) ->
    forall n (Ox Oy Oz : F),
      (n < length dk)%nat ->
      let ws_old := weighted_sum (skipn (S n) dk) 0 in
      oncurve (Ox, Oy, Oz) ->
      pt_eq (Ox, Oy, Oz) (sm (Z.to_nat (2 * ws_old)) (Px, Py, Pz)) ->
      let d := nth n dk 0 in
      pt_eq
        (if (d =? 0)%Z then (Ox, Oy, Oz)
         else curve_add (Ox, Oy, Oz) (digit_point_local d table_entries))
        (sm (Z.to_nat (weighted_sum (skipn n dk) 0)) (Px, Py, Pz)).
  Proof.
    intros dk Px Py Pz table_entries
           HPoc HlenT HcorrT Hodd Hb Hws
           n Ox Oy Oz Hn.
    intros ws_old Hoc Hacc d.
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
    assert (Hacc' : pt_eq (Ox, Oy, Oz) (sm_Z (2 * ws_old) (Px,Py,Pz))).
    { rewrite sm_Z_nonneg by lia. exact Hacc. }
    (* Replace goal's sm(Z.to_nat ws_new)(P) with sm_Z(d + 2*ws_old)(P) *)
    replace (sm (Z.to_nat (weighted_sum (skipn n dk) 0)) (Px,Py,Pz))
      with (sm_Z (d + 2 * ws_old) (Px,Py,Pz))
      by (rewrite <- Hhs; apply sm_Z_nonneg; lia).
    (* Case split on d = 0 *)
    destruct (d =? 0) eqn:Ed.
    - (* d = 0: trivial — sm_Z(0 + 2*ws_old) = sm_Z(2*ws_old) *)
      apply Z.eqb_eq in Ed.
      replace d with 0 in * by lia.
      replace (0 + 2 * ws_old) with (2 * ws_old) by lia.
      exact Hacc'.
    - (* d <> 0 *)
      apply Z.eqb_neq in Ed.
      assert (Hdp : pt_eq (digit_point_local d table_entries)
                          (sm_Z d (Px,Py,Pz)))
        by (apply digit_point_is_sm_Z; assumption).
      assert (HocD : oncurve (digit_point_local d table_entries)).
      { apply digit_point_local_oncurve; try assumption.
        intros i Hi. exact (proj1 (HcorrT i Hi)). }
      apply (pt_trans
               (curve_add (Ox,Oy,Oz) (digit_point_local d table_entries))
               (curve_add (sm_Z (2 * ws_old) (Px,Py,Pz)) (sm_Z d (Px,Py,Pz)))
               (sm_Z (d + 2 * ws_old) (Px,Py,Pz))).
      + apply curve_add_Proper;
          [ exact Hoc
          | apply oncurve_sm_Z; exact HPoc
          | exact HocD
          | apply oncurve_sm_Z; exact HPoc
          | exact Hacc'
          | exact Hdp ].
      + replace (d + 2 * ws_old) with (2 * ws_old + d) by lia.
        apply pt_sym. apply sm_Z_add_nonneg; [exact HPoc | lia].
  Qed.

End SingleHornerAlgebra.

(** ** Instantiation bridge.

    The main consumers are [BN254_wNAF_Instance.v] and
    [P256_wNAF_Instance.v], which have:

      Let scmul_s := scmul Fzero Fone curve_add.

    where [scmul] is from [BLS12_GLV_LoopInvariant.v]. Since
    [scmul Fzero Fone curve_add] is definitionally equal to our [sm],
    and ProcessDigits' [digit_point] is definitionally equal to our
    [digit_point_local] (both use [point_opp pt := let '(X,Y,Z) := pt
    in (X, F.opp Y, Z)] when [point_opp] is so instantiated), the
    discharge at the call site is:

      apply horner_step_single; assumption.

    provided the table correctness hypothesis is phrased with [sm]
    (= [scmul_s]) and carries the per-entry [oncurve] conjunct.

    For a curve whose addition satisfies the group laws on the nose
    (the historical BN254/BN256/BN446 interface), instantiate
    [pt_eq := eq], [pt_eq_equiv := eq_equivalence],
    [oncurve := fun _ => True]; every new hypothesis is then trivial and
    the old Leibniz statements are recovered. *)
