(** * BLS12-381 G2: the emitted complete addition and doubling on the twist.

    E' : y^2 = x^3 + b'  over  Fp2 = Fp[u]/(u^2 + 1),  b' = 4 (1 + u).

    The two bodies are the field-generic Rupicola derivations of
    [CurveAddAF.v] instantiated at the BLS12 Fp2 representation
    [bls12_Fp2] (12 words, c0 then c1, field leaves ["bls12_Fp2_mul"],
    ["bls12_Fp2_add"], ["bls12_Fp2_sub"]), with the proved loader
    ["bls12_Fp2_three_b"] of [BLS12_G2_ThreeB.v].

    Main results (Qed, closed):
    - [g2_curve_add_closed]: for on-curve P, Q with tight coordinates,
      ["g2_curve_add"] returns tight (X, Y, Z) EQUAL (Leibniz) to
      [proj1_sig (Projective.add P Q)], fiat-crypto's complete projective
      addition on E'(Fp2).
    - [g2_curve_double_closed]: ["g2_curve_double"] returns
      [proj1_sig (Projective.add P P)].
    The premises are the environment entries of the printed bodies and the
    three Fp2 leaf contracts ([AbstractField.binop_spec] for mul/add/sub at
    the Fp2 representation) that the Rust runtime supplies.

    BLS12 side conditions proved here: Fp2 is a field with decidable
    equality and characteristic p (> 21); 3b' = b' + b' + b'; the
    discriminant 27 b'^2 is nonzero; and E'(Fp2) has no point of order two:
    if z^3 = -b' then the norm N(z) = z0^2 + z1^2 satisfies N(z)^3 = N(-b') = 32,
    so -N(z)/2 would be a cube root of -4 in Fp, which
    [BLS12_MSM_Closed.bls12_no_two_torsion] excludes. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith Lia List.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
Require Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Bedrock.Field.FieldExtensions.Compilation2_Fp2.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Import Bedrock.Group.CurveAdd.CurveAddAF.
Require Import Bedrock.Group.CurveAdd.RcbLawsAF.
Require Import Bedrock.BLS12_G2_ThreeB.
Require Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Bedrock.BLS12_MSM_Closed.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section G2.
  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls12_prime_parameters bls12_field_representation
    bls12_Fp2_field_parameters bls12_Fp2_field_representation
    bls12_prime_parameters_ok bls12_field_representation_ok.
  Existing Instance prime_field_parameters.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation AFElem := Compilation2_Fp2.AFElem.

  #[local] Instance prime_M : Znumtheory.prime (Z.pos PrimeField.M_pos) :=
    prime_bls12_381.

  Add Ring Fp_ring_g2 : (F.ring_theory PrimeField.M_pos)
    (morphism (F.ring_morph PrimeField.M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory PrimeField.M_pos),
     power_tac (F.power_theory PrimeField.M_pos) [F.is_pow_constant]).

  Local Notation Fzero := (@AbstractField.Fzero Fp2 bls12_Fp2_field_parameters).
  Local Notation Fone := (@AbstractField.Fone Fp2 bls12_Fp2_field_parameters).
  Local Notation Fopp := (@AbstractField.Fopp Fp2 bls12_Fp2_field_parameters).
  Local Notation Fadd := (@AbstractField.Fadd Fp2 bls12_Fp2_field_parameters).
  Local Notation Fsub := (@AbstractField.Fsub Fp2 bls12_Fp2_field_parameters).
  Local Notation Fmul := (@AbstractField.Fmul Fp2 bls12_Fp2_field_parameters).
  Local Notation Finv := (@AbstractField.Finv Fp2 bls12_Fp2_field_parameters).
  Local Notation Fdiv := (@AbstractField.Fdiv Fp2 bls12_Fp2_field_parameters).

  (** ** Fp2 is a field with Leibniz equality *)

  Definition g2_fld : @Hierarchy.field Fp2 eq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv :=
    @AbstractField.fld _ _
      (Fp2_field_parameters_ok _ bls12_beta_nz bls12_beta_qnr bls12_M_big "bls12_Fp2_").

  Definition g2_dec : DecidableRel (@eq Fp2) := @AbstractField.Feq_dec _ bls12_Fp2_field_parameters.

  Lemma of_nat_Fp2 (n : nat) :
    @Ring.of_nat Fp2 Fzero Fone Fadd n = (@Ring.of_nat Fp F.zero F.one F.add n, F.zero).
  Proof.
    induction n as [|n IH]; [ reflexivity | ].
    cbn [Ring.of_nat]. rewrite IH.
    cbv [AbstractField.Fadd AbstractField.Fone bls12_Fp2_field_parameters
         Fp2_field_parameters addp2 onep2 fst snd].
    f_equal; try ring.
  Qed.

  Lemma g2_char_ge (C : positive) :
    (C <= PrimeField.M_pos)%positive ->
    @Ring.char_ge Fp2 eq Fzero Fone Fopp Fadd Fsub Fmul C.
  Proof.
    intros HC p Hp H.
    cbv [Ring.of_Z] in H. rewrite of_nat_Fp2 in H.
    cbv [AbstractField.Fzero bls12_Fp2_field_parameters Fp2_field_parameters zerop2] in H.
    injection H as H1.
    apply (@F.char_gt PrimeField.M_pos p); [ exact (Pos.lt_le_trans _ _ _ Hp HC) | ].
    cbv [Ring.of_Z]. exact H1.
  Qed.

  Lemma M_big_28 : (28 <= PrimeField.M_pos)%positive.
  Proof. vm_compute. discriminate. Qed.

  #[local] Instance g2_char_ge_3 :
    @Ring.char_ge Fp2 eq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.two).
  Proof. apply g2_char_ge. vm_compute. discriminate. Qed.
  #[local] Instance g2_char_ge_12 : @Ring.char_ge Fp2 eq Fzero Fone Fopp Fadd Fsub Fmul 12%positive.
  Proof. apply g2_char_ge. vm_compute. discriminate. Qed.
  #[local] Instance g2_char_ge_21 : @Ring.char_ge Fp2 eq Fzero Fone Fopp Fadd Fsub Fmul 21%positive.
  Proof. apply g2_char_ge. vm_compute. discriminate. Qed.

  (** ** The twist constants *)

  Definition g2_b : Fp2 := (F.of_Z _ 4, F.of_Z _ 4).

  Lemma g2_Hthree_b : g2_tb = Fadd (Fadd g2_b g2_b) g2_b.
  Proof.
    cbv [g2_tb g2_b AbstractField.Fadd bls12_Fp2_field_parameters Fp2_field_parameters addp2 fst snd].
    f_equal; apply F.eq_to_Z_iff; vm_compute; reflexivity.
  Qed.

  Lemma g2_Hdisc : id
    (Fadd (Fmul (Fmul (Fmul (Fadd (Fadd (Fadd Fone Fone) Fone) Fone) Fzero) Fzero) Fzero)
       (Fmul (Fmul (Fadd (Fadd (Fadd (Fadd (Fadd
          (Fmul (Fadd (Fadd (Fadd Fone Fone) Fone) Fone) (Fadd (Fadd (Fadd Fone Fone) Fone) Fone))
          (Fadd (Fadd (Fadd Fone Fone) Fone) Fone))
          (Fadd (Fadd (Fadd Fone Fone) Fone) Fone)) Fone) Fone) Fone) g2_b) g2_b)
     <> Fzero).
  Proof.
    cbv [id]. intros H. apply (f_equal (fun x => F.to_Z (snd x))) in H.
    vm_compute in H. discriminate H.
  Qed.

  (** ** No point of order two on E'(Fp2) *)

  Local Notation b4 := (BLS12_MSM_Closed.b4).

  Lemma lin2 (P1 P2 l r c1 c2 : Fp) :
    P1 = 0%F -> P2 = 0%F -> (l - r = c1 * P1 + c2 * P2)%F -> l = r.
  Proof.
    intros H1 H2 E. rewrite H1, H2 in E.
    transitivity ((l - r) + r)%F; [ ring | rewrite E; ring ].
  Qed.

  Lemma sub0 (a b : Fp) : a = b -> (a - b = 0)%F.
  Proof. intros ->. ring. Qed.

  Lemma g2_no_two_torsion :
    @RcbLawsAF.no_two_torsion Fp2 bls12_Fp2_field_parameters g2_b.
  Proof.
    cbv [RcbLawsAF.no_two_torsion]. intros [u v] H.
    pose proof (f_equal fst H) as Hre. pose proof (f_equal snd H) as Him. clear H.
    cbv [g2_b AbstractField.Fadd AbstractField.Fmul AbstractField.Fzero
         bls12_Fp2_field_parameters Fp2_field_parameters addp2 mulp2 zerop2 fst snd] in Hre, Him.
    set (w := (u * u + v * v)%F).
    assert (Hw3 : (w * w * w = F.of_Z _ 32)%F).
    { refine (lin2 _ _ _ _
        (u * u * u - F.of_Z _ 3 * u * v * v - F.of_Z _ 4)%F
        (F.of_Z _ 3 * u * u * v - v * v * v - F.of_Z _ 4)%F Hre Him _).
      subst w. ring. }
    set (h := F.of_Z PrimeField.M_pos ((Z.pos PrimeField.M_pos + 1) / 2)).
    assert (H2h : (F.of_Z _ 2 * h = 1)%F) by (apply F.eq_to_Z_iff; vm_compute; reflexivity).
    set (x := F.opp (w * h)).
    assert (Hfin : (x * x * x + 0 * x + F.of_Z PrimeField.M_pos 4 = 0)%F).
    { refine (lin2 _ _ _ _
        (F.opp (h * h * h))%F
        (F.opp (F.of_Z _ 4 * ((F.of_Z _ 2 * h) * (F.of_Z _ 2 * h) + F.of_Z _ 2 * h + 1)))%F
        (sub0 _ _ Hw3) (sub0 _ _ H2h) _).
      subst x. ring. }
    exact (BLS12_MSM_Closed.bls12_no_two_torsion x Hfin).
  Qed.

  Definition g2_Hexcept :=
    @RcbLawsAF.not_exceptional_of_no_two_torsion Fp2 bls12_Fp2_field_parameters g2_fld g2_dec
      g2_char_ge_3 g2_char_ge_12 g2_char_ge_21 g2_b g2_tb g2_Hthree_b g2_Hdisc
      g2_no_two_torsion.

  (** ** The emitted bodies and the closed theorems *)

  Definition g2_three_b_name : string := "bls12_Fp2_three_b".

  Definition g2_add_body : Syntax.func :=
    @af_curve_add_body 64 BW64 word mem _ _ Fp2 bls12_Fp2_field_parameters
      bls12_Fp2_field_representation g2_three_b_name.

  Definition g2_double_body : Syntax.func :=
    @af_curve_double_body 64 BW64 word mem _ _ Fp2 bls12_Fp2_field_parameters
      bls12_Fp2_field_representation g2_three_b_name.

  #[local] Instance g2_rep_ok :
    @AbstractField.FieldRepresentation_ok Fp2 _ _ _ _ _ bls12_Fp2_field_representation :=
    Fp2_field_representation_ok _ _.

  Lemma g2_bounds_eq :
    @AbstractField.loose_bounds Fp2 _ _ _ _ _ bls12_Fp2_field_representation
    = AbstractField.tight_bounds.
  Proof. reflexivity. Qed.

  Local Notation Ppoint := (@Projective.point Fp2 eq Fzero Fadd Fmul Fzero g2_b).

  Definition g2_oncurve : Fp2 * Fp2 * Fp2 -> Prop :=
    @RcbLawsAF.oncurve Fp2 bls12_Fp2_field_parameters g2_b.

  Definition g2_mkP (p : Fp2 * Fp2 * Fp2) (H : g2_oncurve p) : Ppoint := exist _ p H.

  (** fiat-crypto's complete projective addition on E'(Fp2), made total by
      [g2_Hexcept]. *)
  Definition g2_padd (P Q : Ppoint) : Ppoint :=
    @Projective.add Fp2 eq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv Fzero g2_b
      g2_fld g2_char_ge_3 g2_dec g2_tb g2_Hthree_b g2_Hdisc g2_char_ge_21
      P Q (g2_Hexcept P Q).

  Lemma g2_cadd_padd (p q : Fp2 * Fp2 * Fp2) (Hp : g2_oncurve p) (Hq : g2_oncurve q) :
    @RcbLawsAF.cadd Fp2 bls12_Fp2_field_parameters g2_tb p q
    = proj1_sig (g2_padd (g2_mkP p Hp) (g2_mkP q Hq)).
  Proof.
    exact (@RcbLawsAF.cadd_raw Fp2 bls12_Fp2_field_parameters g2_fld g2_dec
             g2_char_ge_3 g2_char_ge_21 g2_b g2_tb g2_Hthree_b g2_Hdisc g2_Hexcept
             p q Hp Hq).
  Qed.

  Lemma g2_cdbl_padd (p : Fp2 * Fp2 * Fp2) (Hp : g2_oncurve p) :
    @RcbLawsAF.cdbl Fp2 bls12_Fp2_field_parameters g2_tb p
    = proj1_sig (g2_padd (g2_mkP p Hp) (g2_mkP p Hp)).
  Proof.
    rewrite <- g2_cadd_padd.
    exact (@RcbLawsAF.cdbl_is_cadd Fp2 bls12_Fp2_field_parameters g2_fld g2_dec
             g2_b g2_tb g2_Hthree_b p Hp).
  Qed.

  Local Notation tight := (Some (@AbstractField.tight_bounds Fp2 _ _ _ _ _ bls12_Fp2_field_representation)).

  Theorem g2_curve_add_closed (functions : Semantics.env) :
    map.get functions "g2_curve_add" = Some g2_add_body ->
    map.get functions g2_three_b_name = Some g2_three_b_body ->
    spec_of_af_mul (F:=Fp2) functions ->
    spec_of_af_add (F:=Fp2) functions ->
    spec_of_af_sub (F:=Fp2) functions ->
    forall (pX1 pX2 pY1 pY2 pZ1 pZ2 pXout pYout pZout : word)
           (X1 Y1 Z1 X2 Y2 Z2 Xold Yold Zold : Fp2)
           (H1 : g2_oncurve (X1, Y1, Z1)) (H2 : g2_oncurve (X2, Y2, Z2))
           (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      (AFElem tight pX1 X1 * AFElem tight pX2 X2
       * AFElem tight pY1 Y1 * AFElem tight pY2 Y2
       * AFElem tight pZ1 Z1 * AFElem tight pZ2 Z2
       * AFElem None pXout Xold * AFElem None pYout Yold * AFElem None pZout Zold * R)%sep m ->
      Semantics.call functions "g2_curve_add" tr m
        [pX1; pX2; pY1; pY2; pZ1; pZ2; pXout; pYout; pZout]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists Xo Yo Zo : Fp2,
             (Xo, Yo, Zo) = proj1_sig (g2_padd (g2_mkP _ H1) (g2_mkP _ H2))
             /\ (AFElem tight pX1 X1 * AFElem tight pX2 X2
                 * AFElem tight pY1 Y1 * AFElem tight pY2 Y2
                 * AFElem tight pZ1 Z1 * AFElem tight pZ2 Z2
                 * AFElem tight pXout Xo * AFElem tight pYout Yo * AFElem tight pZout Zo
                 * R)%sep m').
  Proof.
    intros Henv Htb Hmul Hadd Hsub.
    pose proof (@af_curve_add_correct 64 BW64 word mem _ _ _ _ _ _ Fp2
                  bls12_Fp2_field_parameters bls12_Fp2_field_representation _
                  g2_bounds_eq g2_tb g2_three_b_name I functions Henv Hmul Hadd Hsub
                  (g2_three_b_ok functions Htb)) as Hspec.
    cbv [spec_of_af_curve_add] in Hspec.
    intros pX1 pX2 pY1 pY2 pZ1 pZ2 pXout pYout pZout X1 Y1 Z1 X2 Y2 Z2 Xold Yold Zold
           H1 H2 R tr m Hm.
    eapply Semantics.weaken_call;
      [ exact (Hspec pX1 pX2 pY1 pY2 pZ1 pZ2 pXout pYout pZout
                 X1 X2 Y1 Y2 Z1 Z2 Xold Yold Zold R tr m Hm) | ].
    cbv beta. intros tr' m' rets (Hr & Htr & Xo & Yo & Zo & Hgal & Hm').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists Xo, Yo, Zo. split; [ | exact Hm' ].
    rewrite <- g2_cadd_padd. cbv [RcbLawsAF.cadd]. rewrite Hgal. reflexivity.
  Qed.

  Theorem g2_curve_double_closed (functions : Semantics.env) :
    map.get functions "g2_curve_double" = Some g2_double_body ->
    map.get functions g2_three_b_name = Some g2_three_b_body ->
    spec_of_af_mul (F:=Fp2) functions ->
    spec_of_af_add (F:=Fp2) functions ->
    spec_of_af_sub (F:=Fp2) functions ->
    forall (pX pY pZ pXout pYout pZout : word) (X Y Z Xold Yold Zold : Fp2)
           (HP : g2_oncurve (X, Y, Z))
           (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      (AFElem tight pX X * AFElem tight pY Y * AFElem tight pZ Z
       * AFElem None pXout Xold * AFElem None pYout Yold * AFElem None pZout Zold * R)%sep m ->
      Semantics.call functions "g2_curve_double" tr m
        [pX; pY; pZ; pXout; pYout; pZout]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists Xo Yo Zo : Fp2,
             (Xo, Yo, Zo) = proj1_sig (g2_padd (g2_mkP _ HP) (g2_mkP _ HP))
             /\ (AFElem tight pX X * AFElem tight pY Y * AFElem tight pZ Z
                 * AFElem tight pXout Xo * AFElem tight pYout Yo * AFElem tight pZout Zo
                 * R)%sep m').
  Proof.
    intros Henv Htb Hmul Hadd Hsub.
    pose proof (@af_curve_double_correct 64 BW64 word mem _ _ _ _ _ _ Fp2
                  bls12_Fp2_field_parameters bls12_Fp2_field_representation _
                  g2_bounds_eq g2_tb g2_three_b_name I functions Henv Hmul Hadd Hsub
                  (g2_three_b_ok functions Htb)) as Hspec.
    cbv [spec_of_af_curve_double] in Hspec.
    intros pX pY pZ pXout pYout pZout X Y Z Xold Yold Zold HP R tr m Hm.
    eapply Semantics.weaken_call;
      [ exact (Hspec pX pY pZ pXout pYout pZout X Y Z Xold Yold Zold R tr m Hm) | ].
    cbv beta. intros tr' m' rets (Hr & Htr & Xo & Yo & Zo & Hgal & Hm').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists Xo, Yo, Zo. split; [ | exact Hm' ].
    rewrite <- g2_cdbl_padd. cbv [RcbLawsAF.cdbl]. rewrite Hgal. reflexivity.
  Qed.

End G2.
