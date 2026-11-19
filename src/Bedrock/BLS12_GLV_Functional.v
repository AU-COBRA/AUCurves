(** * BLS12_GLV_Functional — the program-order GLV loop computes k1 P + k2 Q.

    [BLS12_GLV_Prog.glv_prog_output] (129 LSB-first iterations, see there)
    is, in any commutative monoid up to an equivalence, [k1] P + [k2] Q
    for 0 <= k1, k2 < 2^129 ([glv_prog_correct]).  Over the complete RCB
    formulas and on-curve inputs this gives, up to [pt_eq],
    [glv_prog_rcb_correct].  With Q = phi(P) = (omega X, Y, Z):
    - [oncurve_phi]: phi(P) is on the curve when omega^3 = 1 (a = 0);
    - [glv_eigen]: if phi(P) is [pt_eq] to [lambda] P, the output is
      (k1 + lambda k2) P;
    - [smul_mod_order]: if r P is the identity, k P = (k mod r) P.
    That phi(P) = [lambda] P for every P of the order-r subgroup is NOT
    proved here (it needs the structure of E(F_p)[r]); it is the premise
    of [glv_eigen].  The cube root of unity that pairs with
    lambda = 0xac45a4010001a40200000000ffffffff is omega^2 for the
    [BLS12_Endomorphism.bls12_omega]: with that omega itself, phi = [lambda^2].
    For the multiples of the standard generator the premise is proved
    (with [BLS12_Endomorphism.bls12_omega_glv]): [BLS12_GLV_ClosedGen.g1_eigen]. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith List Lia.
From Stdlib Require Import RelationClasses Morphisms Setoid.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Require Import Bedrock.BLS12_MSM_Functional.
Require Import Bedrock.BLS12_GLV_Prog.
Local Open Scope Z_scope.

(** ** 1. In a commutative monoid up to an equivalence *)
Section GlvMonoid.
  Context {G : Type} (eqv : G -> G -> Prop) {eqv_Equivalence : Equivalence eqv}.
  Context (id : G) (add : G -> G -> G) (dbl : G -> G).
  Context {add_Proper : Proper (eqv ==> eqv ==> eqv) add}.
  Context (add_assoc : forall a b c, eqv (add (add a b) c) (add a (add b c)))
          (add_comm : forall a b, eqv (add a b) (add b a))
          (add_id_l : forall a, eqv (add id a) a)
          (dbl_add : forall a, eqv (dbl a) (add a a)).

  Local Infix "==" := eqv (at level 70).
  Local Notation smul := (BLS12_MSM_Functional.smul id add).

  #[local] Instance smul_Proper_g n : Proper (eqv ==> eqv) (smul n).
  Proof.
    intros x y Hxy. induction n as [|n IH]; cbn [BLS12_MSM_Functional.smul];
      [reflexivity|]. apply add_Proper; assumption.
  Qed.

  Lemma low_step (k : Z) (n : nat) :
    0 <= k ->
    Z.to_nat (k mod 2 ^ Z.of_nat (S n))
    = (Z.to_nat (k mod 2 ^ Z.of_nat n)
       + (if Z.testbit k (Z.of_nat n) then 2 ^ n else 0))%nat.
  Proof.
    intros Hk.
    assert (Hp : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
    assert (E : k mod 2 ^ Z.of_nat (S n)
                = k mod 2 ^ Z.of_nat n
                  + (if Z.testbit k (Z.of_nat n) then 2 ^ Z.of_nat n else 0)).
    { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite (Z.mul_comm 2 (2 ^ Z.of_nat n)).
      rewrite Z.rem_mul_r by lia.
      assert (Hb : (k / 2 ^ Z.of_nat n) mod 2
                   = if Z.testbit k (Z.of_nat n) then 1 else 0).
      { rewrite Z.testbit_eqb by lia. rewrite <- Z.shiftr_div_pow2 by lia.
        pose proof (Z.mod_pos_bound (Z.shiftr k (Z.of_nat n)) 2 ltac:(lia)).
        destruct (Z.eqb_spec (Z.shiftr k (Z.of_nat n) mod 2) 1); lia. }
      rewrite Hb. destruct (Z.testbit k (Z.of_nat n)); ring. }
    rewrite E.
    pose proof (Z.mod_pos_bound k (2 ^ Z.of_nat n) Hp).
    destruct (Z.testbit k (Z.of_nat n)).
    - rewrite Z2Nat.inj_add by lia. rewrite Z2Nat.inj_pow by lia.
      rewrite Nat2Z.id. reflexivity.
    - rewrite Z.add_0_r, Nat.add_0_r. reflexivity.
  Qed.

  Lemma glv_state_inv (k1 k2 : Z) (p q : G) (n : nat) :
    0 <= k1 -> 0 <= k2 ->
    let s := glv_state id add dbl k1 k2 p q n in
    fst (fst s) == add (smul (Z.to_nat (k1 mod 2 ^ Z.of_nat n)) p)
                       (smul (Z.to_nat (k2 mod 2 ^ Z.of_nat n)) q)
    /\ snd (fst s) == smul (2 ^ n) p
    /\ snd s == smul (2 ^ n) q.
  Proof.
    intros Hk1 Hk2. induction n as [|n IH]; cbn zeta in *.
    - cbn [glv_state fst snd]. rewrite Z.pow_0_r, !Z.mod_1_r. cbn.
      split; [symmetry; apply add_id_l|].
      split; symmetry; apply (add_id_r eqv id add add_comm add_id_l).
    - destruct IH as (Ho & Hp & Hq).
      cbn [glv_state].
      destruct (glv_state id add dbl k1 k2 p q n) as [[o pp] qq].
      cbv [glv_step]. cbn [fst snd] in *.
      rewrite !low_step by assumption.
      rewrite !(smul_add eqv id add add_assoc add_id_l).
      assert (Hd : forall x y, x == smul (2 ^ n) y -> dbl x == smul (2 ^ S n) y).
      { intros x y Hx. rewrite dbl_add, Hx.
        replace (2 ^ S n)%nat with (2 ^ n + 2 ^ n)%nat by (cbn; lia).
        rewrite (smul_add eqv id add add_assoc add_id_l). reflexivity. }
      split; [| split; apply Hd; assumption].
      assert (Hc : forall (b : bool) x y, x == smul (2 ^ n) y ->
                   (if b then x else id) == smul (if b then 2 ^ n else 0)%nat y).
      { intros [|] x y Hx; [exact Hx | reflexivity]. }
      rewrite Ho, (Hc _ pp p Hp), (Hc _ qq q Hq).
      set (A := smul (Z.to_nat (k1 mod 2 ^ Z.of_nat n)) p).
      set (B := smul (Z.to_nat (k2 mod 2 ^ Z.of_nat n)) q).
      set (C := smul (if Z.testbit k1 (Z.of_nat n) then 2 ^ n else 0)%nat p).
      set (D := smul (if Z.testbit k2 (Z.of_nat n) then 2 ^ n else 0)%nat q).
      rewrite (add_assoc A B C), (add_comm B C), <- (add_assoc A C B).
      apply add_assoc.
  Qed.

  Theorem glv_prog_correct (k1 k2 : Z) (p q : G) :
    0 <= k1 < 2 ^ 129 -> 0 <= k2 < 2 ^ 129 ->
    glv_prog_output id add dbl k1 k2 p q
    == add (smul (Z.to_nat k1) p) (smul (Z.to_nat k2) q).
  Proof.
    intros Hk1 Hk2. unfold glv_prog_output.
    destruct (glv_state_inv k1 k2 p q 129 ltac:(lia) ltac:(lia)) as (H & _).
    rewrite H. change (Z.of_nat 129) with 129.
    rewrite !Z.mod_small by lia. reflexivity.
  Qed.
End GlvMonoid.

(** ** 2. A map commuting with the operations commutes with the loop *)
Section GlvTransfer.
  Context {A B : Type} (idA : A) (addA : A -> A -> A) (dblA : A -> A)
          (idB : B) (addB : B -> B -> B) (dblB : B -> B) (f : A -> B).
  Context (f_id : f idA = idB)
          (f_add : forall x y, f (addA x y) = addB (f x) (f y))
          (f_dbl : forall x, f (dblA x) = dblB (f x)).

  Lemma f_glv_state k1 k2 p q n :
    (fun s => (f (fst (fst s)), f (snd (fst s)), f (snd s)))
      (glv_state idA addA dblA k1 k2 p q n)
    = glv_state idB addB dblB k1 k2 (f p) (f q) n.
  Proof.
    induction n as [|n IH]; cbn [glv_state]; [cbn; rewrite f_id; reflexivity|].
    rewrite <- IH. destruct (glv_state idA addA dblA k1 k2 p q n) as [[o pp] qq].
    cbv [glv_step]. cbn [fst snd].
    rewrite !f_add, !f_dbl.
    destruct (Z.testbit k1 (Z.of_nat n)), (Z.testbit k2 (Z.of_nat n)); rewrite ?f_id; reflexivity.
  Qed.

  Lemma f_glv_prog_output k1 k2 p q :
    f (glv_prog_output idA addA dblA k1 k2 p q)
    = glv_prog_output idB addB dblB k1 k2 (f p) (f q).
  Proof.
    unfold glv_prog_output. rewrite <- f_glv_state. reflexivity.
  Qed.
End GlvTransfer.

(** ** 3. Over the RCB formulas *)
Section GlvRcb.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Local Notation F := (F M_pos).
  Local Open Scope F_scope.

  Add Ring Fp_ring_glv : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  Context (M_gt_27 : (27 < M_pos)%positive).
  Context (b three_b : F).
  Context (Hthree_b : three_b = b + b + b).
  Context (Hdisc : id
    ((((1 + 1 + 1 + 1) * 0 * 0 * 0
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) <> 0)%F)).
  Context (Hno2 : no_two_torsion 0 b).

  Local Notation oncurve := (RcbProjectiveLaws.oncurve 0 b).
  Local Notation add_raw := (ladderstep_triple three_b).
  Local Notation dbl_raw := (rcb_double_a0_triple three_b).
  Local Notation Gs := (@Gs _ b).
  Local Notation adds := (@adds _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2).
  Local Notation dbls := (@dbls _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2).
  Local Notation ids := (@ids _ field_parameters_ok M_gt_27 b three_b Hthree_b).
  Local Notation eqs := (@eqs _ b).
  Local Notation smul := (BLS12_MSM_Functional.smul id_pt add_raw).

  #[local] Instance eqs_Equiv : Equivalence eqs :=
    @eqs_Equivalence _ field_parameters_ok M_gt_27 b three_b Hthree_b.
  #[local] Instance adds_Prop : Proper (eqs ==> eqs ==> eqs) adds :=
    @adds_Proper _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2.
  #[local] Instance pt_eq_Equiv : Equivalence pt_eq :=
    pt_eq_Equivalence M_gt_27 b three_b Hthree_b.

  Local Notation assoc := (@adds_assoc _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2).
  Local Notation comm := (@adds_comm _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2).
  Local Notation idl := (@adds_id_l _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2).
  Local Notation dbla := (@dbls_add _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2).

  Local Notation sm := (BLS12_MSM_Functional.smul ids adds).

  Lemma smul_proj n (x : Gs) : proj1_sig (sm n x) = smul n (proj1_sig x).
  Proof.
    exact (f_smul ids adds id_pt add_raw (@proj1_sig _ _) eq_refl (fun _ _ => eq_refl) n x).
  Qed.

  (** The program-order GLV loop over the RCB formulas, on on-curve P, Q:
      projectively k1 P + k2 Q. *)
  Theorem glv_prog_rcb_correct (k1 k2 : Z) (P Q : F * F * F) :
    oncurve P -> oncurve Q ->
    (0 <= k1 < 2 ^ 129)%Z -> (0 <= k2 < 2 ^ 129)%Z ->
    pt_eq (glv_prog_output id_pt add_raw dbl_raw k1 k2 P Q)
          (add_raw (smul (Z.to_nat k1) P) (smul (Z.to_nat k2) Q)).
  Proof.
    intros HP HQ Hk1 Hk2.
    pose proof (glv_prog_correct eqs ids adds dbls assoc comm idl dbla
                  k1 k2 (exist oncurve P HP) (exist oncurve Q HQ) Hk1 Hk2) as H.
    unfold eqs in H.
    rewrite (f_glv_prog_output ids adds dbls id_pt add_raw dbl_raw (@proj1_sig _ _)
               eq_refl (fun _ _ => eq_refl) (fun _ => eq_refl)) in H.
    cbn [proj1_sig adds] in H. rewrite !smul_proj in H. exact H.
  Qed.

  (** The output is on the curve. *)
  Lemma oncurve_glv_prog_output (k1 k2 : Z) (P Q : F * F * F) :
    oncurve P -> oncurve Q ->
    oncurve (glv_prog_output id_pt add_raw dbl_raw k1 k2 P Q).
  Proof.
    intros HP HQ.
    pose proof (f_glv_prog_output ids adds dbls id_pt add_raw dbl_raw (@proj1_sig _ _)
               eq_refl (fun _ _ => eq_refl) (fun _ => eq_refl) k1 k2
               (exist oncurve P HP) (exist oncurve Q HQ)) as E.
    cbn [proj1_sig] in E. rewrite <- E. apply proj2_sig.
  Qed.

  Lemma oncurve_smul n P : oncurve P -> oncurve (smul n P).
  Proof.
    intros HP. pose proof (smul_proj n (exist oncurve P HP)) as E.
    cbn [proj1_sig] in E. rewrite <- E. apply proj2_sig.
  Qed.

  (** phi(X, Y, Z) = (omega X, Y, Z) maps the curve (a = 0) to itself. *)
  Lemma oncurve_phi (omega : F) (P : F * F * F) :
    omega * omega * omega = 1 -> oncurve P ->
    oncurve (let '(X, Y, Z) := P in (omega * X, Y, Z)).
  Proof.
    destruct P as [[X Y] Z]. cbv [RcbProjectiveLaws.oncurve].
    intros Hw [Hc Hz]. split; [| exact Hz].
    rewrite Hc.
    transitivity (X * (X * X) * (omega * omega * omega) + 0 * (omega * X) * (Z * Z)
                  + b * (Z * (Z * Z))); [| ring].
    rewrite Hw. ring.
  Qed.

  (** Scalar arithmetic up to [pt_eq] on on-curve points. *)
  Lemma smul_add_pt a c P : oncurve P ->
    pt_eq (smul (a + c) P) (add_raw (smul a P) (smul c P)).
  Proof.
    intros HP.
    pose proof (smul_add eqs ids adds assoc idl a c (exist oncurve P HP)) as H.
    unfold eqs in H. rewrite smul_proj in H. unfold adds in H. cbn [proj1_sig] in H.
    rewrite !smul_proj in H. exact H.
  Qed.

  Lemma smul_mul_pt a c P : oncurve P ->
    pt_eq (smul (a * c) P) (smul a (smul c P)).
  Proof.
    intros HP.
    pose proof (smul_mul eqs ids adds assoc idl a c (exist oncurve P HP)) as H.
    unfold eqs in H. rewrite !smul_proj in H. exact H.
  Qed.

  Lemma smul_Proper_pt n P Q : oncurve P -> oncurve Q -> pt_eq P Q ->
    pt_eq (smul n P) (smul n Q).
  Proof.
    intros HP HQ E.
    pose proof (smul_Proper_g eqs ids adds n (exist oncurve P HP) (exist oncurve Q HQ) E) as H.
    unfold eqs in H. rewrite !smul_proj in H. exact H.
  Qed.

  Lemma add_Proper_pt P P' Q Q' : oncurve P -> oncurve P' -> oncurve Q -> oncurve Q' ->
    pt_eq P P' -> pt_eq Q Q' -> pt_eq (add_raw P Q) (add_raw P' Q').
  Proof.
    intros HP HP' HQ HQ' E1 E2.
    exact (adds_Prop (exist oncurve P HP) (exist oncurve P' HP') E1
                     (exist oncurve Q HQ) (exist oncurve Q' HQ') E2).
  Qed.

  (** If phi(P) is [lambda] P, then k1 P + k2 phi(P) = (k1 + lambda k2) P. *)
  Theorem glv_eigen (lam k1 k2 : nat) (P Phi : F * F * F) :
    oncurve P -> oncurve Phi -> pt_eq (smul lam P) Phi ->
    pt_eq (add_raw (smul k1 P) (smul k2 Phi)) (smul (k1 + k2 * lam) P).
  Proof.
    intros HP HPhi E.
    pose proof (oncurve_smul lam P HP) as HlP.
    assert (E2 : pt_eq (smul k2 Phi) (smul k2 (smul lam P))).
    { apply smul_Proper_pt; [exact HPhi | exact HlP | symmetry; exact E]. }
    etransitivity.
    { apply (add_Proper_pt _ _ _ _ (oncurve_smul k1 P HP) (oncurve_smul k1 P HP)
               (oncurve_smul k2 Phi HPhi) (oncurve_smul k2 _ HlP)); [reflexivity | exact E2]. }
    symmetry. etransitivity; [apply smul_add_pt; exact HP|].
    apply (add_Proper_pt _ _ _ _ (oncurve_smul _ P HP) (oncurve_smul _ P HP)
             (oncurve_smul _ P HP) (oncurve_smul k2 _ HlP)); [reflexivity |].
    apply smul_mul_pt. exact HP.
  Qed.

  (** If r P is the identity, k P = (k mod r) P. *)
  Lemma smul_mod_order (r k : nat) (P : F * F * F) :
    oncurve P -> (0 < r)%nat -> pt_eq (smul r P) id_pt ->
    pt_eq (smul k P) (smul (k mod r) P).
  Proof.
    intros HP Hr E.
    pose proof (oncurve_id M_gt_27 0 b three_b Hthree_b) as Hid.
    rewrite (Nat.div_mod_eq k r) at 1.
    etransitivity; [apply smul_add_pt; exact HP|].
    assert (Hz : pt_eq (smul (r * (k / r)) P) id_pt).
    { rewrite Nat.mul_comm.
      etransitivity; [apply smul_mul_pt; exact HP|].
      etransitivity.
      - apply smul_Proper_pt; [apply oncurve_smul; exact HP | exact Hid | exact E].
      - pose proof (smul_id eqs ids adds idl (k / r)) as H.
        unfold eqs in H. rewrite smul_proj in H. exact H. }
    etransitivity.
    { exact (add_Proper_pt _ _ _ _ (oncurve_smul _ P HP) Hid (oncurve_smul _ P HP)
               (oncurve_smul _ P HP) Hz (reflexivity _)). }
    exact (idl (exist oncurve _ (oncurve_smul (k mod r) P HP))).
  Qed.
End GlvRcb.
