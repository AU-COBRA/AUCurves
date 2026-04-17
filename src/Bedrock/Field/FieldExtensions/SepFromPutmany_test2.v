(** Test flatten_putmany with left-nested chains *)
From Stdlib Require Import ZArith.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.

Section Test.
  Local Notation mem := (@Interface.map.rep _ _ BasicC64Semantics.mem).

  Context (P1 P2 P3 P4 : mem -> Prop)
          (m1 m2 m3 m4 : mem).

  Hypothesis Hd12 : map.disjoint m1 m2.
  Hypothesis Hd13 : map.disjoint m1 m3.
  Hypothesis Hd14 : map.disjoint m1 m4.
  Hypothesis Hd23 : map.disjoint m2 m3.
  Hypothesis Hd24 : map.disjoint m2 m4.
  Hypothesis Hd34 : map.disjoint m3 m4.

  Hypothesis HP1 : P1 m1.
  Hypothesis HP2 : P2 m2.
  Hypothesis HP3 : P3 m3.
  Hypothesis HP4 : P4 m4.

  (* Test: left-nested putmany + left-associated sep *)
  Lemma test_left_left :
    (P1 * P2 * P3 * P4)%sep
    (map.putmany (map.putmany (map.putmany m1 m2) m3) m4).
  Proof. build_sep_reorder. Qed.

  (* Test: left-nested putmany + right-associated sep *)
  Lemma test_left_right :
    (P1 * (P2 * (P3 * P4)))%sep
    (map.putmany (map.putmany (map.putmany m1 m2) m3) m4).
  Proof. build_sep_reorder. Qed.

  (* Test: evars in sep predicates *)
  Context (F : mem -> Prop -> mem -> Prop).
  Lemma test_evars :
    forall (Q : mem -> Prop),
    (forall m, Q m -> F m True m) ->
    Q m1 ->
    (F m1 True * (P2 * (P3 * P4)))%sep
    (map.putmany m1 (map.putmany m2 (map.putmany m3 m4))).
  Proof.
    intros Q HQ HQm1.
    apply HQ in HQm1.
    build_sep_reorder.
  Qed.

End Test.
