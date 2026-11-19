(** * BLS12_GLV_Eigen — phi = [lambda] on the multiples of the G1 generator.

    phi(X, Y, Z) = (omega X, Y, Z) with omega^3 = 1 and a = 0.

    Abstract field (section [PhiHom]):
    - [phi_add], [phi_dbl], [phi_id]: phi commutes with the raw RCB
      addition / doubling (Leibniz equality, any three_b) and fixes the
      identity triple; hence [phi_smul]: phi (k P) = k (phi P);
    - [phi_pt_eq]: phi respects [pt_eq];
    - [eigen_of_multiple]: if phi(G) is [pt_eq] to [lambda] G, then
      phi(P) is [pt_eq] to [lambda] P for every on-curve P [pt_eq] to
      [m] G (any m); [order_of_multiple]: likewise r G = O gives r P = O.
    No point counting: only the monoid laws up to [pt_eq] of
    [BLS12_MSM_Functional] / [BLS12_GLV_Functional].

    Further (section [PhiEigen]): [order_of_eigen] (if phi(G) is [L] G
    and G + phi(G) + phi(phi(G)) is O, then [1 + L + L^2] G is O),
    [glv_prog_single] (the GLV loop with k2 = 0 is [k] P), and (section
    [PtEqb]) the boolean test [pt_eqb] with [pt_eqb_sound], used for the
    VM checks.

    The BLS12-381 instances (the generator, omega = bls12_omega^2 mod p,
    phi(G) = [lambda] G, r G = O, [g1_eigen]) are in [BLS12_GLV_ClosedGen].

    The closed GLV theorem without the eigen premise is
    [BLS12_GLV_ClosedGen.g1_glv_closed_gen]. *)

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
Require Import Bedrock.BLS12_GLV_Functional.
Local Open Scope Z_scope.

(** ** 1. phi over an abstract field *)
Section PhiHom.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Local Notation F := (F M_pos).
  Local Open Scope F_scope.

  Add Ring Fp_ring_eig : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  Definition phi (w : F) (P : F * F * F) : F * F * F :=
    let '(X, Y, Z) := P in (w * X, Y, Z).

  Context (w three_b : F) (Hw : w * w * w = 1).

  Local Notation add_raw := (ladderstep_triple three_b).
  Local Notation dbl_raw := (rcb_double_a0_triple three_b).
  Local Notation smul := (BLS12_MSM_Functional.smul id_pt add_raw).

  Lemma phi_add P Q : phi w (add_raw P Q) = add_raw (phi w P) (phi w Q).
  Proof.
    destruct P as [[X1 Y1] Z1], Q as [[X2 Y2] Z2].
    cbv [phi ladderstep_triple ladderstep_gallina nlet stack P2.car P2.cdr].
    apply pair_equal_spec; split; [apply pair_equal_spec; split | ].
    - timeout 120 ring [Hw].
    - timeout 120 ring [Hw].
    - timeout 120 ring [Hw].
  Qed.

  Lemma phi_dbl P : phi w (dbl_raw P) = dbl_raw (phi w P).
  Proof.
    destruct P as [[X Y] Z].
    cbv [phi rcb_double_a0_triple rcb_double_a0_gallina nlet stack P2.car P2.cdr].
    apply pair_equal_spec; split; [apply pair_equal_spec; split | ]; ring.
  Qed.

  Lemma phi_id : phi w id_pt = id_pt.
  Proof.
    cbv [phi id_pt]. apply pair_equal_spec; split; [apply pair_equal_spec; split | ];
      ring.
  Qed.

  Lemma phi_smul n P : phi w (smul n P) = smul n (phi w P).
  Proof.
    induction n as [|n IH]; cbn [BLS12_MSM_Functional.smul]; [apply phi_id|].
    rewrite phi_add, IH. reflexivity.
  Qed.

  Lemma phi_pt_eq P Q : pt_eq P Q -> pt_eq (phi w P) (phi w Q).
  Proof.
    destruct P as [[X1 Y1] Z1], Q as [[X2 Y2] Z2]. cbv [phi pt_eq].
    repeat match goal with |- context [if ?d then _ else _] => destruct d end;
      try tauto.
    intros [Hx Hy]. split; [| exact Hy].
    transitivity (w * (X1 * Z2)); [ring|]. rewrite Hx. ring.
  Qed.
End PhiHom.

Section PhiEigen.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Local Notation F := (F M_pos).
  Local Open Scope F_scope.

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
  Local Notation smul := (BLS12_MSM_Functional.smul id_pt add_raw).

  #[local] Instance pt_eq_Equiv_eig : Equivalence pt_eq :=
    pt_eq_Equivalence M_gt_27 b three_b Hthree_b.
  #[local] Instance eqs_Equiv_eig : Equivalence (@eqs _ b) :=
    @eqs_Equivalence _ field_parameters_ok M_gt_27 b three_b Hthree_b.
  #[local] Instance adds_Prop_eig :
    Proper (@eqs _ b ==> @eqs _ b ==> @eqs _ b)
      (@adds _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2) :=
    @adds_Proper _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2.

  Local Notation osmul := (oncurve_smul M_gt_27 b three_b Hthree_b Hdisc Hno2).
  Local Notation smul_mul := (smul_mul_pt M_gt_27 b three_b Hthree_b Hdisc Hno2).
  Local Notation smul_Prop := (smul_Proper_pt M_gt_27 b three_b Hthree_b Hdisc Hno2).

  (** phi(G) = [lambda] G gives phi(P) = [lambda] P for every P = [m] G
      (up to [pt_eq]). *)
  Theorem eigen_of_multiple (w : F) (lam m : nat) (G P : F * F * F) :
    w * w * w = 1 -> oncurve G -> oncurve P ->
    pt_eq (phi w G) (smul lam G) -> pt_eq P (smul m G) ->
    pt_eq (smul lam P) (phi w P).
  Proof.
    intros Hw HG HP Eg Ep.
    pose proof (oncurve_phi b w G Hw HG) as HphiG. fold (phi w G) in HphiG.
    etransitivity; [apply (smul_Prop lam _ _ HP (osmul m G HG) Ep)|].
    etransitivity; [symmetry; apply smul_mul; exact HG|].
    rewrite Nat.mul_comm.
    etransitivity; [apply smul_mul; exact HG|].
    etransitivity;
      [apply (smul_Prop m _ _ (osmul lam G HG) HphiG); symmetry; exact Eg|].
    rewrite <- (phi_smul w three_b Hw).
    apply phi_pt_eq. symmetry. exact Ep.
  Qed.

  (** r G = O gives r P = O for every P = [m] G. *)
  Theorem order_of_multiple (r m : nat) (G P : F * F * F) :
    oncurve G -> oncurve P ->
    pt_eq (smul r G) id_pt -> pt_eq P (smul m G) ->
    pt_eq (smul r P) id_pt.
  Proof.
    intros HG HP Er Ep.
    pose proof (oncurve_id M_gt_27 0 b three_b Hthree_b) as Hid.
    etransitivity; [apply (smul_Prop r _ _ HP (osmul m G HG) Ep)|].
    etransitivity; [symmetry; apply smul_mul; exact HG|].
    rewrite Nat.mul_comm.
    etransitivity; [apply smul_mul; exact HG|].
    etransitivity; [apply (smul_Prop m _ _ (osmul r G HG) Hid Er)|].
    pose proof (smul_id (@eqs _ b) (@ids _ field_parameters_ok M_gt_27 b three_b Hthree_b)
                  (@adds _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2)
                  (@adds_id_l _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2) m) as H.
    unfold eqs in H. rewrite (smul_proj M_gt_27 b three_b Hthree_b Hdisc Hno2) in H. exact H.
  Qed.

  Lemma oncurve_add_raw P Q : oncurve P -> oncurve Q -> oncurve (add_raw P Q).
  Proof.
    intros HP HQ.
    exact (proj2_sig (@adds _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2
                        (exist _ _ HP) (exist _ _ HQ))).
  Qed.

  Lemma smul_one_pt P : oncurve P -> pt_eq (smul 1 P) P.
  Proof.
    intros HP. change (smul 1 P) with (add_raw P id_pt).
    exact (add_id_r (@eqs _ b) (@ids _ field_parameters_ok M_gt_27 b three_b Hthree_b)
             (@adds _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2)
             (@adds_comm _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2)
             (@adds_id_l _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2)
             (exist _ _ HP)).
  Qed.

  (** If phi(G) = [lambda] G and G + phi(G) + phi^2(G) = O, then
      [1 + lambda + lambda^2] G = O. *)
  Theorem order_of_eigen (w : F) (L : nat) (G : F * F * F) :
    w * w * w = 1 -> oncurve G -> pt_eq (phi w G) (smul L G) ->
    pt_eq (add_raw G (add_raw (phi w G) (phi w (phi w G)))) id_pt ->
    pt_eq (smul (1 + (L + L * L)) G) id_pt.
  Proof.
    intros Hw HG E Hsum.
    assert (H1 : oncurve (phi w G)) by exact (oncurve_phi b w G Hw HG).
    assert (H2 : oncurve (phi w (phi w G))) by exact (oncurve_phi b w _ Hw H1).
    assert (HL : oncurve (smul L G)) by exact (osmul L G HG).
    assert (E2 : pt_eq (smul (L * L) G) (phi w (phi w G))).
    { etransitivity; [ exact (smul_mul L L G HG) | ].
      etransitivity; [ exact (smul_Prop L _ _ HL H1 (symmetry E)) | ].
      rewrite <- (phi_smul w three_b Hw).
      apply phi_pt_eq. symmetry. exact E. }
    assert (E3 : pt_eq (smul (L + L * L) G) (add_raw (phi w G) (phi w (phi w G)))).
    { etransitivity; [ exact (smul_add_pt M_gt_27 b three_b Hthree_b Hdisc Hno2 L (L * L) G HG) | ].
      exact (add_Proper_pt M_gt_27 b three_b Hthree_b Hdisc Hno2 _ _ _ _ HL H1
               (osmul (L * L) G HG) H2 (symmetry E) E2). }
    etransitivity; [ exact (smul_add_pt M_gt_27 b three_b Hthree_b Hdisc Hno2 1 (L + L * L) G HG) | ].
    etransitivity; [ | exact Hsum ].
    exact (add_Proper_pt M_gt_27 b three_b Hthree_b Hdisc Hno2 _ _ _ _ (osmul 1 G HG) HG
             (osmul _ G HG) (oncurve_add_raw _ _ H1 H2) (smul_one_pt G HG) E3).
  Qed.

  (** A loop run with k2 = 0 is [k1] P. *)
  Lemma glv_prog_single (k : Z) (P : F * F * F) :
    oncurve P -> (0 <= k < 2 ^ 129)%Z ->
    pt_eq (glv_prog_output id_pt add_raw dbl_raw k 0 P P) (smul (Z.to_nat k) P).
  Proof.
    intros HP Hk.
    etransitivity;
      [apply (glv_prog_rcb_correct M_gt_27 b three_b Hthree_b Hdisc Hno2); auto; lia|].
    change (smul (Z.to_nat 0) P) with (@id_pt field_parameters).
    exact (add_id_r (@eqs _ b) (@ids _ field_parameters_ok M_gt_27 b three_b Hthree_b)
             (@adds _ field_parameters_ok M_gt_27 b three_b Hthree_b Hdisc Hno2)
             (@adds_comm _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2)
             (@adds_id_l _ _ M_gt_27 b three_b Hthree_b Hdisc Hno2)
             (exist _ _ (osmul (Z.to_nat k) P HP))).
  Qed.

End PhiEigen.

(** ** 2. A boolean projective equality, sound for [pt_eq] *)
Section PtEqb.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Local Notation F := (F M_pos).

  Definition pt_eqb (P Q : F * F * F) : bool :=
    let '(X1, Y1, Z1) := P in
    let '(X2, Y2, Z2) := Q in
    negb (Z.eqb (F.to_Z Z1) 0) && negb (Z.eqb (F.to_Z Z2) 0)
    && Z.eqb (F.to_Z (X1 * Z2)%F) (F.to_Z (X2 * Z1)%F)
    && Z.eqb (F.to_Z (Y1 * Z2)%F) (F.to_Z (Y2 * Z1)%F).

  Lemma F_to_Z_0 : F.to_Z (0 : F)%F = 0.
  Proof. reflexivity. Qed.

  Lemma pt_eqb_sound P Q : pt_eqb P Q = true -> pt_eq P Q.
  Proof.
    destruct P as [[X1 Y1] Z1], Q as [[X2 Y2] Z2]. cbv [pt_eqb pt_eq].
    rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, !Z.eqb_neq, !Z.eqb_eq.
    intros [[[H1 H2] Hx] Hy].
    repeat match goal with |- context [if ?d then _ else _] => destruct d as [E|_] end;
      try (subst; exfalso; (apply H1 + apply H2); reflexivity).
    split; apply F.eq_to_Z_iff; assumption.
  Qed.

  Lemma pt_eq_id_of_z P : F.to_Z (snd P) = 0 -> pt_eq P id_pt.
  Proof.
    destruct P as [[X Y] Z]. cbn [snd]. intros H. cbv [pt_eq id_pt].
    assert (Z = 0%F) by (apply F.eq_to_Z_iff; exact H).
    match goal with |- context [if ?d then _ else _] => destruct d end;
      [reflexivity | contradiction].
  Qed.
End PtEqb.
