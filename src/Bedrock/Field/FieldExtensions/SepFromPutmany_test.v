(** Test the sep automation with bedrock2 concrete types. *)

From Stdlib Require Import ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.

Section Test.
  Local Notation mem := (@Interface.map.rep _ _ BasicC64Semantics.mem).

  Context (P1 P2 P3 P4 Rr : mem -> Prop)
          (m1 m2 m3 m4 m_rr : mem).

  Hypothesis Hd12 : map.disjoint m1 m2.
  Hypothesis Hd13 : map.disjoint m1 m3.
  Hypothesis Hd14 : map.disjoint m1 m4.
  Hypothesis Hd1r : map.disjoint m1 m_rr.
  Hypothesis Hd23 : map.disjoint m2 m3.
  Hypothesis Hd24 : map.disjoint m2 m4.
  Hypothesis Hd2r : map.disjoint m2 m_rr.
  Hypothesis Hd34 : map.disjoint m3 m4.
  Hypothesis Hd3r : map.disjoint m3 m_rr.
  Hypothesis Hd4r : map.disjoint m4 m_rr.

  Hypothesis HP1 : P1 m1.
  Hypothesis HP2 : P2 m2.
  Hypothesis HP3 : P3 m3.
  Hypothesis HP4 : P4 m4.
  Hypothesis HRr : Rr m_rr.

  (* Test 1: same order — no reordering needed *)
  Lemma test_same_order :
    (P1 * (P2 * (P3 * (P4 * Rr))))%sep
    (map.putmany m1 (map.putmany m2 (map.putmany m3 (map.putmany m4 m_rr)))).
  Proof. build_sep_reorder. Qed.

  (* Test 2: reversed — needs full reordering *)
  Lemma test_reversed :
    (P4 * (P3 * (P2 * (P1 * Rr))))%sep
    (map.putmany m1 (map.putmany m2 (map.putmany m3 (map.putmany m4 m_rr)))).
  Proof. build_sep_reorder. Qed.

  (* Test 3: arbitrary permutation *)
  Lemma test_permuted :
    (P3 * (P1 * (P4 * (P2 * Rr))))%sep
    (map.putmany m1 (map.putmany m2 (map.putmany m3 (map.putmany m4 m_rr)))).
  Proof. build_sep_reorder. Qed.

  (* Test 4: realistic mul_xi pattern — rewrite then build_sep_reorder *)
  (* Simulates: m'' = putmany m_n2 (putmany m_n1 (putmany m_o1 (putmany m_o2 m_rr)))
     with predicates on m_n1, m_n2, m_o1, m_o2, m_rr in NON-MATCHING order *)
  Context (m_n1 m_n2 m_o1 m_o2 : mem).

  Hypothesis Hd_n1_n2 : map.disjoint m_n1 m_n2.
  Hypothesis Hd_n1_o1 : map.disjoint m_n1 m_o1.
  Hypothesis Hd_n1_o2 : map.disjoint m_n1 m_o2.
  Hypothesis Hd_n1_rr : map.disjoint m_n1 m_rr.
  Hypothesis Hd_n2_o1 : map.disjoint m_n2 m_o1.
  Hypothesis Hd_n2_o2 : map.disjoint m_n2 m_o2.
  Hypothesis Hd_n2_rr : map.disjoint m_n2 m_rr.
  Hypothesis Hd_o1_o2 : map.disjoint m_o1 m_o2.
  Hypothesis Hd_o1_rr : map.disjoint m_o1 m_rr.
  Hypothesis Hd_o2_rr : map.disjoint m_o2 m_rr.

  Context (Q1 Q2 Q3 Q4 : mem -> Prop).
  Hypothesis Hn1 : Q1 m_n1.
  Hypothesis Hn2 : Q2 m_n2.
  Hypothesis Ho1 : Q3 m_o1.
  Hypothesis Ho2 : Q4 m_o2.

  (* The Hsep5 pattern: predicates in order Q1,Q2,Q3,Q4,Rr
     but putmany chain has m_n2 first, then m_n1, then m_o1, m_o2, m_rr *)
  Lemma test_hsep5_pattern :
    forall m'',
    m'' = map.putmany m_n2 (map.putmany m_n1
            (map.putmany m_o1 (map.putmany m_o2 m_rr))) ->
    (Q1 * (Q2 * (Q3 * (Q4 * Rr))))%sep m''.
  Proof.
    intros m'' Hmem_eq.
    rewrite Hmem_eq.
    build_sep_reorder.
  Qed.

End Test.
