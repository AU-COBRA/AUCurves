(** * BN254 field tower instances (Fp2 -> Fp6 -> Fp12).

    Provides FieldParameters, FieldRepresentation, and spec_of instances
    for BN254 with beta=-1, xi=(9,1).

    p = 3 mod 4, so -1 is a QNR (simpler than BLS12-377 beta=-5).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bn254_Fp2.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsFiat.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section BN254.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bn254_prime_parameters bn254_prime_parameters_ok
    bn254_field_representation bn254_field_representation_ok.
  Existing Instance prime_field_parameters.

  (* ================================================================ *)
  (* BN254 curve parameters                                            *)
  (* ================================================================ *)

  Definition bn254_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
  Definition bn254_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 9.
  Definition bn254_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

  Lemma bn254_beta_nz : bn254_beta <> @F.zero PrimeField.M_pos.
  Proof.
    unfold bn254_beta. intro H. apply (f_equal F.to_Z) in H.
    rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
  Qed.

  Lemma bn254_M_big : 2 < Z.pos PrimeField.M_pos.
  Proof. vm_compute. reflexivity. Qed.

  (* p = 3 mod 4 => -1 is a QNR. Euler criterion: (-1)^((p-1)/2) = -1 != 1. *)
  Lemma bn254_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bn254_beta).
  Proof.
    intro H.
    assert (Hprime : Znumtheory.prime (Z.pos PrimeField.M_pos))
      by exact prime_bn254.
    assert (Hbig : 2 < Z.pos PrimeField.M_pos) by exact bn254_M_big.
    apply (proj2 (@F.euler_criterion _ Hprime Hbig bn254_beta bn254_beta_nz)) in H.
    assert (Hcheck : (F.to_Z (@F.pow PrimeField.M_pos bn254_beta
      (Z.to_N (Z.pos PrimeField.M_pos / 2))) =? F.to_Z (@F.one PrimeField.M_pos))%Z = false).
    { vm_cast_no_check (eq_refl false). }
    apply (f_equal F.to_Z) in H. rewrite H in Hcheck.
    rewrite Z.eqb_refl in Hcheck. discriminate.
  Qed.

  Let fp2_prefix := "bn254_Fp2_".

  (* ================================================================ *)
  (* Fp2 instances                                                      *)
  (* ================================================================ *)

  Instance bn254_Fp2_params : AbstractField.FieldParameters (F PrimeField.M_pos * F PrimeField.M_pos) :=
    Fp2_field_parameters bn254_beta fp2_prefix.

  Instance bn254_Fp2_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos * F PrimeField.M_pos) :=
    Fp2_field_representation bn254_beta fp2_prefix.

  Instance bn254_Fp2_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos * F PrimeField.M_pos) :=
    Fp2_field_representation_ok bn254_beta fp2_prefix.

  Instance bn254_Fp2_names : FieldNames (F:=F PrimeField.M_pos * F PrimeField.M_pos) :=
    field_names_prefixed fp2_prefix.

  (* spec_of instances for Fp-level operations *)
  Instance spec_of_bn254_add : spec_of PrimeField.add :=
    AbstractField.binop_spec AbstractField.bin_add (F:=F PrimeField.M_pos).
  Instance spec_of_bn254_sub : spec_of PrimeField.sub :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=F PrimeField.M_pos).
  Instance spec_of_bn254_mul : spec_of PrimeField.mul :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=F PrimeField.M_pos).
  Instance spec_of_bn254_sqr : spec_of PrimeField.square :=
    AbstractField.unop_spec AbstractField.un_square (F:=F PrimeField.M_pos).
  Instance spec_of_bn254_inv : spec_of PrimeField.inv :=
    AbstractField.unop_spec AbstractField.un_inv (F:=F PrimeField.M_pos).
  Instance spec_of_bn254_copy : spec_of PrimeField.felem_copy :=
    AbstractField.spec_of_felem_copy (F:=F PrimeField.M_pos).

  (* spec_of instances for Fp2 operations *)
  Instance spec_of_bn254_Fp2_add : spec_of (AbstractField.add (F:=F PrimeField.M_pos * F PrimeField.M_pos)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=F PrimeField.M_pos * F PrimeField.M_pos).
  Instance spec_of_bn254_Fp2_sub : spec_of (AbstractField.sub (F:=F PrimeField.M_pos * F PrimeField.M_pos)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=F PrimeField.M_pos * F PrimeField.M_pos).
  Instance spec_of_bn254_Fp2_mul : spec_of (AbstractField.mul (F:=F PrimeField.M_pos * F PrimeField.M_pos)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=F PrimeField.M_pos * F PrimeField.M_pos).
  Instance spec_of_bn254_Fp2_copy : spec_of (AbstractField.felem_copy (F:=F PrimeField.M_pos * F PrimeField.M_pos)) :=
    AbstractField.spec_of_felem_copy (F:=F PrimeField.M_pos * F PrimeField.M_pos).

  (* ================================================================ *)
  (* Bridge hypotheses for beta=-1                                      *)
  (* ================================================================ *)

  Lemma bn254_mulp2_eq_fp2_mul : forall a b,
    QuadraticExtensions.mulp2 PrimeField.M_pos bn254_beta a b =
    Fp6.fp2_mul PrimeField.M_pos bn254_beta a b.
  Proof. intros [a0 a1] [b0 b1]. reflexivity. Qed.

  Let ftfst := @Field.field_theory_for_stdlib_tactic
    (F PrimeField.M_pos) (@eq (F PrimeField.M_pos))
    (@F.zero PrimeField.M_pos) (@F.one PrimeField.M_pos)
    (@F.opp PrimeField.M_pos) (@F.add PrimeField.M_pos)
    (@F.mul PrimeField.M_pos) (@F.sub PrimeField.M_pos)
    (@F.inv PrimeField.M_pos) (@F.div PrimeField.M_pos)
    (@F.field_modulo PrimeField.M_pos prime_bn254).
  Add Field Fp_field : ftfst.

  Let FFp2 := QuadraticExtensions.FFp2 PrimeField.M_pos prime_bn254
    bn254_M_big bn254_beta bn254_beta_nz bn254_beta_qnr.
  Add Field Fp2field : FFp2.

  Local Lemma Fp_sq_zero : forall a : F PrimeField.M_pos,
    @F.mul PrimeField.M_pos a a = @F.zero PrimeField.M_pos ->
    a = @F.zero PrimeField.M_pos.
  Proof.
    intros a Ha.
    destruct (F.eq_dec a (@F.zero PrimeField.M_pos)); [assumption|].
    exfalso. apply n.
    transitivity (@F.mul PrimeField.M_pos (@F.inv PrimeField.M_pos a)
                   (@F.mul PrimeField.M_pos a a)).
    - field. exact n.
    - rewrite Ha. ring.
  Qed.

  Local Lemma bn254_norm_nonzero : forall a0 a1 : F PrimeField.M_pos,
    (a0, a1) <> QuadraticExtensions.zerop2 PrimeField.M_pos ->
    @F.sub PrimeField.M_pos
      (@F.mul PrimeField.M_pos a0 a0)
      (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bn254_beta a1) a1)
      <> @F.zero PrimeField.M_pos.
  Proof.
    intros a0 a1 Hx Habs.
    apply bn254_beta_qnr.
    destruct (F.eq_dec a1 (@F.zero PrimeField.M_pos)) as [Ha1|Ha1].
    - subst a1.
      assert (Ha0sq : @F.mul PrimeField.M_pos a0 a0 = @F.zero PrimeField.M_pos).
      { replace (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bn254_beta (@F.zero PrimeField.M_pos)) (@F.zero PrimeField.M_pos))
          with (@F.zero PrimeField.M_pos) in Habs by ring.
        replace (@F.sub PrimeField.M_pos (@F.mul PrimeField.M_pos a0 a0) (@F.zero PrimeField.M_pos))
          with (@F.mul PrimeField.M_pos a0 a0) in Habs by ring.
        exact Habs. }
      apply Fp_sq_zero in Ha0sq. subst a0. exfalso. apply Hx. reflexivity.
    - exists (@F.mul PrimeField.M_pos a0 (@F.inv PrimeField.M_pos a1)).
      assert (Heq : @F.mul PrimeField.M_pos a0 a0 =
                     @F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bn254_beta a1) a1).
      { assert (@F.sub PrimeField.M_pos (@F.mul PrimeField.M_pos a0 a0)
                  (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bn254_beta a1) a1) =
                @F.zero PrimeField.M_pos) by exact Habs.
        assert (@F.mul PrimeField.M_pos a0 a0 =
                @F.sub PrimeField.M_pos (@F.zero PrimeField.M_pos)
                  (@F.opp PrimeField.M_pos (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bn254_beta a1) a1))).
        { rewrite <- H. ring. }
        rewrite H0. ring. }
      transitivity (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos a0 a0)
                     (@F.mul PrimeField.M_pos (@F.inv PrimeField.M_pos a1) (@F.inv PrimeField.M_pos a1))).
      + ring.
      + rewrite Heq. field. exact Ha1.
  Qed.

  Lemma bn254_invp2_eq_fp2_inv : forall x,
    x <> QuadraticExtensions.zerop2 PrimeField.M_pos ->
    QuadraticExtensions.invp2 PrimeField.M_pos bn254_beta x =
    Fp6.fp2_inv PrimeField.M_pos bn254_beta x.
  Proof.
    intros [a0 a1] Hx.
    pose proof (bn254_norm_nonzero a0 a1 Hx) as Hnorm.
    assert (Hinvp2 : QuadraticExtensions.mulp2 PrimeField.M_pos bn254_beta (a0,a1)
      (QuadraticExtensions.invp2 PrimeField.M_pos bn254_beta (a0,a1)) =
      QuadraticExtensions.onep2 PrimeField.M_pos).
    { pose proof (Finv_l FFp2 (a0,a1) Hx). rewrite <- H. ring. }
    assert (Hfpinv : QuadraticExtensions.mulp2 PrimeField.M_pos bn254_beta (a0,a1)
      (Fp6.fp2_inv PrimeField.M_pos bn254_beta (a0,a1)) =
      QuadraticExtensions.onep2 PrimeField.M_pos).
    { unfold QuadraticExtensions.mulp2, Fp6.fp2_inv, QuadraticExtensions.onep2.
      cbn -[F.inv F.mul F.add F.sub F.opp F.zero F.one F.div PrimeField.M_pos].
      apply injective_projections;
        cbn -[F.inv F.mul F.add F.sub F.opp F.zero F.one F.div PrimeField.M_pos];
        field; assumption. }
    pose proof (Finv_l FFp2 (a0,a1) Hx) as Hinv_l.
    assert (Hy2 : Fp6.fp2_inv PrimeField.M_pos bn254_beta (a0, a1) =
                  QuadraticExtensions.invp2 PrimeField.M_pos bn254_beta (a0, a1)).
    { transitivity (QuadraticExtensions.mulp2 PrimeField.M_pos bn254_beta
        (QuadraticExtensions.onep2 PrimeField.M_pos)
        (Fp6.fp2_inv PrimeField.M_pos bn254_beta (a0, a1))). { ring. }
      rewrite <- Hinv_l.
      transitivity (QuadraticExtensions.mulp2 PrimeField.M_pos bn254_beta
        (QuadraticExtensions.invp2 PrimeField.M_pos bn254_beta (a0, a1))
        (QuadraticExtensions.mulp2 PrimeField.M_pos bn254_beta (a0, a1)
          (Fp6.fp2_inv PrimeField.M_pos bn254_beta (a0, a1)))). { ring. }
      rewrite Hfpinv. ring. }
    symmetry. exact Hy2.
  Qed.

  (* ================================================================ *)
  (* Fp6/Fp12 instances via generic tower                              *)
  (* ================================================================ *)

  Let fp6_prefix := "bn254_Fp6_".
  Let fp12_prefix := "bn254_Fp12_".

  Instance bn254_Fp6_params : AbstractField.FieldParameters
    ((F PrimeField.M_pos * F PrimeField.M_pos) *
     (F PrimeField.M_pos * F PrimeField.M_pos) *
     (F PrimeField.M_pos * F PrimeField.M_pos)) :=
    Fp6_field_parameters bn254_beta bn254_xi_re bn254_xi_im (fp6_prefix:=fp6_prefix).

  Instance bn254_Fp6_rep : AbstractField.FieldRepresentation (F:=
    (F PrimeField.M_pos * F PrimeField.M_pos) *
    (F PrimeField.M_pos * F PrimeField.M_pos) *
    (F PrimeField.M_pos * F PrimeField.M_pos)) :=
    Fp6_field_representation bn254_beta bn254_xi_re bn254_xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

End BN254.
