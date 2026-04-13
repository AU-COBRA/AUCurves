(* Pallas curve integration into AUCurves Montgomery framework.
   Instantiates MontgomeryCurveSpecs for y^2 = x^3 + 5 over the
   Pallas prime field (m = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001). *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

(* Pallas prime *)
Local Definition m := Eval vm_compute in (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001).
Local Definition bw := 64.
Local Definition n := 4%nat.

(* Curve equation: y^2 = x^3 + 5  (a = 0, b = 5) *)
Local Definition a := 0%Z.
Local Definition b_coeff := 5%Z.
Local Definition three_b := 15%Z.

(* Montgomery parameters -- r = 2^bw *)
Local Notation r := (MontgomeryRingTheory.r bw).
(* r' = modinv(r, m) satisfying (r * r') mod m = 1 *)
Local Definition r' :=
  17320927906121697692859042841402336979572641806530953073407455152633943081550%Z.
(* m' = modinv(-m, r) satisfying (m * m') mod r = (-1) mod r *)
Local Definition m' := 11037532056220336127%Z.

(* Correctness lemmas for Montgomery parameters *)
Lemma a_small : a = a mod m.
Proof. vm_compute. reflexivity. Qed.

Lemma three_b_small : three_b = three_b mod m.
Proof. vm_compute. reflexivity. Qed.

Lemma r'_correct : (r * r') mod m = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma m'_correct : (m * m') mod r = (-1) mod r.
Proof. vm_compute. reflexivity. Qed.

Lemma bw_big : 0 < bw.
Proof. unfold bw. lia. Qed.

Lemma n_nz : n <> 0%nat.
Proof. unfold n. discriminate. Qed.

Lemma m_small : m < r ^ (Z.of_nat n).
Proof. vm_compute. reflexivity. Qed.

Lemma m_big : 1 < m.
Proof. unfold m. lia. Qed.

(* Instantiate Montgomery curve specs for Pallas *)
Definition pallas_three_b_list := MontgomeryCurveSpecs.three_b_list bw n three_b.
Definition pallas_three_b_mont := Eval vm_compute in
  (MontgomeryCurveSpecs.three_b_mont_list m bw n m' three_b).
Definition pallas_a_list := MontgomeryCurveSpecs.a_list bw n a.
Definition pallas_a_mont_list := Eval vm_compute in
  (MontgomeryCurveSpecs.a_mont_list m bw n m' a).

(* Validity lemmas *)
Lemma pallas_three_b_list_valid : WordByWordMontgomery.valid bw n m pallas_three_b_list.
Proof.
  apply three_b_list_valid; try assumption.
  - exact three_b_small.
  - exact bw_big.
  - exact n_nz.
  - exact m_small.
  - exact m_big.
Qed.

Lemma pallas_three_b_mont_valid : WordByWordMontgomery.valid bw n m pallas_three_b_mont.
Proof.
  unfold pallas_three_b_mont. vm_compute. repeat split; try reflexivity; try discriminate; try lia.
Qed.

Lemma pallas_a_list_valid : WordByWordMontgomery.valid bw n m pallas_a_list.
Proof.
  apply a_list_valid; try assumption.
  - exact a_small.
  - exact bw_big.
  - exact n_nz.
  - exact m_small.
  - exact m_big.
Qed.

(* Notation for Gallina-level field operations *)
Local Notation my_mul := (my_mul m).
Local Notation my_add := (my_add m).
Local Notation my_sub := (my_sub m).
Local Infix "*'" := my_mul (at level 70).
Local Infix "+'" := my_add (at level 80).
Local Infix "-'" := my_sub (at level 80).

Local Notation eval := (@WordByWordMontgomery.eval bw n).
Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
Local Notation evfrom x := (eval (from_mont x)).

(* Gallina specification of Pallas point addition (projective coordinates).
   This is the generic spec from MontgomeryCurveSpecs, instantiated for Pallas. *)
Definition Pallas_add_Gallina_spec :=
  BLS12_add_Gallina_spec m bw n m' a three_b.

(* Specialized a=0 Gallina spec: since a=0, the a*t terms vanish,
   yielding a simpler addition formula. *)
Definition Pallas_add_Gallina_spec_a_0 X1 Y1 Z1 X2 Y2 Z2 outx outy outz :=
  let X1 := evfrom X1 in
  let Y1 := evfrom Y1 in
  let Z1 := evfrom Z1 in
  let X2 := evfrom X2 in
  let Y2 := evfrom Y2 in
  let Z2 := evfrom Z2 in
  let t0 := X1*'X2 in
  let t1 := Y1*'Y2 in
  let t2 := Z1*'Z2 in
  let t3 := X1+'Y1 in
  let t4 := X2+'Y2 in
  let t3 := t3*'t4 in
  let t4 := t0+'t1 in
  let t3 := t3-'t4 in
  let t4 := X1+'Z1 in
  let t5 := X2+'Z2 in
  let t4 := t4*'t5 in
  let t5 := t0+'t2 in
  let t4 := t4-'t5 in
  let t5 := Y1+'Z1 in
  let X3 := Y2+'Z2 in
  let t5 := t5*'X3 in
  let X3 := t1+'t2 in
  let t5 := t5-'X3 in
  let Z3 := eval pallas_three_b_list *'t2 in
  let X3 := t1-'Z3 in
  let Z3 := t1+'Z3 in
  let Y3 := X3*'Z3 in
  let t1 := t0+'t0 in
  let t1 := t1+'t0 in
  let t4 := eval pallas_three_b_list *'t4 in
  let t0 := t1*'t4 in
  let Y3 := Y3+'t0 in
  let t0 := t5*'t4 in
  let X3 := t3*'X3 in
  let X3 := X3-'t0 in
  let t0 := t3*'t1 in
  let Z3 := t5*'Z3 in
  let Z3 := Z3+'t0 in
  ( evfrom outx, evfrom outy, evfrom outz) = (X3, Y3, Z3).

(* The generic and a=0 specialized specs are equivalent for Pallas. *)
Lemma add_specs_equiv : forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz,
  Pallas_add_Gallina_spec X1 X2 Y1 Y2 Z1 Z2 outx outy outz
  <-> Pallas_add_Gallina_spec_a_0 X1 X2 Y1 Y2 Z1 Z2 outx outy outz.
Proof.
  intros X1 X2 Y1 Y2 Z1 Z2 outx outy outz.
  unfold Pallas_add_Gallina_spec, MontgomeryCurveSpecs.BLS12_add_Gallina_spec.
  unfold Pallas_add_Gallina_spec_a_0.
  assert (H0 : eval (a_list bw n a) = 0) by auto. rewrite H0.
  remember (evfrom X1) as x1.
  remember (evfrom X2) as x2.
  remember (evfrom Y1) as y1.
  remember (evfrom Y2) as y2.
  remember (evfrom Z1) as z1.
  remember (evfrom Z2) as z2.
  change (three_b_list bw n three_b) with pallas_three_b_list.
  remember (eval pallas_three_b_list) as tb.
  unfold my_mul, my_add, my_sub.
  pull_Zmod.
  split; (intros H; rewrite H; apply pair_equal_spec; split;
    [apply pair_equal_spec; split| ]; apply (f_equal (fun y => y mod m)); ring).
Qed.

(* Lemma: a_mont is the zero element (since a=0) *)
Lemma a_mont_zero : (a_mont m bw n r' m' a a_small
    r'_correct m'_correct bw_big n_nz m_small m_big) =
    (mont_zero m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
Proof.
  apply mont_enc_irr. simpl. cbv [a_mont_list]. apply f_equal. cbv [a_list].
  assert (a = 0) by (cbv; reflexivity). rewrite H. cbv. auto.
Qed.
