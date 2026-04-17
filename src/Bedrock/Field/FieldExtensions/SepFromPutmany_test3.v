(** Comprehensive test: tail reordering + evar frame construction *)
From Stdlib Require Import ZArith.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.

Section Test.
  Local Notation mem := (@Interface.map.rep _ _ BasicC64Semantics.mem).

  Context (P Q R S T : mem -> Prop) (m1 m2 m3 m4 m5 : mem).
  Hypothesis Hd12 : map.disjoint m1 m2. Hypothesis Hd13 : map.disjoint m1 m3.
  Hypothesis Hd14 : map.disjoint m1 m4. Hypothesis Hd15 : map.disjoint m1 m5.
  Hypothesis Hd23 : map.disjoint m2 m3. Hypothesis Hd24 : map.disjoint m2 m4.
  Hypothesis Hd25 : map.disjoint m2 m5. Hypothesis Hd34 : map.disjoint m3 m4.
  Hypothesis Hd35 : map.disjoint m3 m5. Hypothesis Hd45 : map.disjoint m4 m5.
  Hypothesis HP : P m1. Hypothesis HQ : Q m2. Hypothesis HR : R m3.
  Hypothesis HS : S m4. Hypothesis HT : T m5.

  (* Test 1: same order as chain — no reordering *)
  Lemma test_same_order :
    (P * Q * R * (S * T))%sep
    (map.putmany m1 (map.putmany m2 (map.putmany m3 (map.putmany m4 m5)))).
  Proof. build_sep_reorder. Qed.

  (* Test 2: reversed — needs tail case fix *)
  Lemma test_reversed :
    (P * Q * R * (S * T))%sep
    (map.putmany m5 (map.putmany m4 (map.putmany m3 (map.putmany m2 m1)))).
  Proof. build_sep_reorder. Qed.

  (* Test 3: known predicates + evar frame *)
  Lemma test_evar_frame :
    exists (Frame : mem -> Prop),
      (P * Q * Frame)%sep
      (map.putmany m3 (map.putmany m4 (map.putmany m5 (map.putmany m1 m2)))).
  Proof. eexists _. build_sep_reorder. Qed.

  (* Test 4: multiple evar values with known "pointers" (like store_zero) *)
  Context (FE : nat -> nat -> mem -> Prop).
  Hypothesis HFE1 : FE 1 10 m1. Hypothesis HFE2 : FE 2 20 m2. Hypothesis HFE3 : FE 3 30 m3.

  Lemma test_evar_vals :
    exists v1 v2 v3 (Frame : mem -> Prop),
      (FE 1 v1 * FE 2 v2 * FE 3 v3 * Frame)%sep
      (map.putmany m4 (map.putmany m5 (map.putmany m1 (map.putmany m2 m3)))).
  Proof. eexists _, _, _, _. build_sep_reorder. Qed.

End Test.
