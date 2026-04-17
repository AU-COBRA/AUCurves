(** * BLS12-377 field tower instances (Fp2 → Fp6 → Fp12).

    Provides FieldParameters, FieldRepresentation, and spec_of instances
    for BLS12-377 with β=-5, ξ=(0,1).

    Generic WP proofs (add, sub, copy, zero, one) are reused from
    QuadraticFieldExtensions.v. β-dependent proofs (mul, sqr, inv)
    use the BLS12-377-specific bodies from bls12_377_Fp2.v.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_Fp2.
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

Section BLS377.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls377_prime_parameters bls377_prime_parameters_ok
    bls377_field_representation bls377_field_representation_ok.
  Existing Instance prime_field_parameters.

  (* ================================================================ *)
  (* BLS12-377 curve parameters                                        *)
  (* ================================================================ *)

  Definition bls377_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-5).
  Definition bls377_xi_re : F PrimeField.M_pos := @F.zero PrimeField.M_pos.
  Definition bls377_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

  Lemma bls377_beta_nz : bls377_beta <> @F.zero PrimeField.M_pos.
  Proof.
    unfold bls377_beta. intro H. apply (f_equal F.to_Z) in H.
    rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
  Qed.

  Lemma bls377_M_big : 2 < Z.pos PrimeField.M_pos.
  Proof. vm_compute. reflexivity. Qed.

  Lemma bls377_M_mod_4_3 : (Z.pos PrimeField.M_pos mod 4 =? 3) = false.
  Proof. vm_compute. reflexivity. Qed.

  (* For β=-5 QNR proof, we use the Euler criterion.
     p ≡ 1 (mod 4) for BLS12-377, but -5 is still a QNR.
     This requires a different proof strategy than BLS12-381. *)
  Lemma bls377_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bls377_beta).
  Proof.
    (* Use Euler criterion: (∃ b, b*b = a) ↔ a^(p/2) = 1.
       We show β^(p/2) ≠ 1 by computation. *)
    intro H.
    assert (Hprime : Znumtheory.prime (Z.pos PrimeField.M_pos))
      by exact prime_bls12_377.
    assert (Hbig : 2 < Z.pos PrimeField.M_pos) by exact bls377_M_big.
    apply (proj2 (@F.euler_criterion _ Hprime Hbig bls377_beta bls377_beta_nz)) in H.
    (* H : bls377_beta ^ (p/2) = 1 — false by Euler criterion.
       vm_compute handles the 377-bit modular exponentiation in ~4 seconds. *)
    assert (Hcheck : (F.to_Z (@F.pow PrimeField.M_pos bls377_beta
      (Z.to_N (Z.pos PrimeField.M_pos / 2))) =? F.to_Z (@F.one PrimeField.M_pos))%Z = false).
    { vm_cast_no_check (eq_refl false). }
    apply (f_equal F.to_Z) in H. rewrite H in Hcheck.
    rewrite Z.eqb_refl in Hcheck. discriminate.
  Qed.

  Let fp2_prefix := "bls377_Fp2_".

  (* ================================================================ *)
  (* Fp2 instances                                                      *)
  (* ================================================================ *)

  Instance bls377_Fp2_params : AbstractField.FieldParameters (F PrimeField.M_pos * F PrimeField.M_pos) :=
    Fp2_field_parameters bls377_beta fp2_prefix.

  Instance bls377_Fp2_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos * F PrimeField.M_pos) :=
    Fp2_field_representation bls377_beta fp2_prefix.

  Instance bls377_Fp2_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos * F PrimeField.M_pos) :=
    Fp2_field_representation_ok bls377_beta fp2_prefix.

  Instance bls377_Fp2_names : FieldNames (F:=F PrimeField.M_pos * F PrimeField.M_pos) :=
    field_names_prefixed fp2_prefix.

  (* spec_of instances for Fp-level operations *)
  Instance spec_of_bls377_add : spec_of PrimeField.add :=
    AbstractField.binop_spec AbstractField.bin_add (F:=F PrimeField.M_pos).
  Instance spec_of_bls377_sub : spec_of PrimeField.sub :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=F PrimeField.M_pos).
  Instance spec_of_bls377_mul : spec_of PrimeField.mul :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=F PrimeField.M_pos).
  Instance spec_of_bls377_sqr : spec_of PrimeField.square :=
    AbstractField.unop_spec AbstractField.un_square (F:=F PrimeField.M_pos).
  Instance spec_of_bls377_inv : spec_of PrimeField.inv :=
    AbstractField.unop_spec AbstractField.un_inv (F:=F PrimeField.M_pos).
  Instance spec_of_bls377_copy : spec_of PrimeField.felem_copy :=
    AbstractField.spec_of_felem_copy (F:=F PrimeField.M_pos).
  (* from_word spec — may not exist in AbstractField *)

  (* spec_of instances for Fp2 operations — using generic proofs where possible *)
  Instance spec_of_bls377_Fp2_add : spec_of (AbstractField.add (F:=F PrimeField.M_pos * F PrimeField.M_pos)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=F PrimeField.M_pos * F PrimeField.M_pos).
  Instance spec_of_bls377_Fp2_sub : spec_of (AbstractField.sub (F:=F PrimeField.M_pos * F PrimeField.M_pos)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=F PrimeField.M_pos * F PrimeField.M_pos).
  Instance spec_of_bls377_Fp2_mul : spec_of (AbstractField.mul (F:=F PrimeField.M_pos * F PrimeField.M_pos)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=F PrimeField.M_pos * F PrimeField.M_pos).
  Instance spec_of_bls377_Fp2_copy : spec_of (AbstractField.felem_copy (F:=F PrimeField.M_pos * F PrimeField.M_pos)) :=
    AbstractField.spec_of_felem_copy (F:=F PrimeField.M_pos * F PrimeField.M_pos).

  (* ================================================================ *)
  (* Bridge hypotheses for β=-5                                        *)
  (* After spec generalization, mulp2 and fp2_mul use the same formula *)
  (* ================================================================ *)

  Lemma bls377_mulp2_eq_fp2_mul : forall a b,
    QuadraticExtensions.mulp2 PrimeField.M_pos bls377_beta a b =
    Fp6.fp2_mul PrimeField.M_pos bls377_beta a b.
  Proof. intros [a0 a1] [b0 b1]. reflexivity. Qed.

  Let ftfst := @Field.field_theory_for_stdlib_tactic
    (F PrimeField.M_pos) (@eq (F PrimeField.M_pos))
    (@F.zero PrimeField.M_pos) (@F.one PrimeField.M_pos)
    (@F.opp PrimeField.M_pos) (@F.add PrimeField.M_pos)
    (@F.mul PrimeField.M_pos) (@F.sub PrimeField.M_pos)
    (@F.inv PrimeField.M_pos) (@F.div PrimeField.M_pos)
    (@F.field_modulo PrimeField.M_pos prime_bls12_377).
  Add Field Fp_field : ftfst.

  (* Fp2 field theory for cancellation *)
  Let FFp2 := QuadraticExtensions.FFp2 PrimeField.M_pos prime_bls12_377
    bls377_M_big bls377_beta bls377_beta_nz bls377_beta_qnr.
  Add Field Fp2field : FFp2.

  (* a² = 0 => a = 0 in Fp *)
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

  (* β being QNR + (a0,a1) ≠ 0 implies a0²-β·a1² ≠ 0 *)
  Local Lemma bls377_norm_nonzero : forall a0 a1 : F PrimeField.M_pos,
    (a0, a1) <> QuadraticExtensions.zerop2 PrimeField.M_pos ->
    @F.sub PrimeField.M_pos
      (@F.mul PrimeField.M_pos a0 a0)
      (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bls377_beta a1) a1)
      <> @F.zero PrimeField.M_pos.
  Proof.
    intros a0 a1 Hx Habs.
    apply bls377_beta_qnr.
    destruct (F.eq_dec a1 (@F.zero PrimeField.M_pos)) as [Ha1|Ha1].
    - (* a1 = 0 => a0² = 0 => a0 = 0, contradicting Hx *)
      subst a1.
      assert (Ha0sq : @F.mul PrimeField.M_pos a0 a0 = @F.zero PrimeField.M_pos).
      { replace (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bls377_beta (@F.zero PrimeField.M_pos)) (@F.zero PrimeField.M_pos))
          with (@F.zero PrimeField.M_pos) in Habs by ring.
        replace (@F.sub PrimeField.M_pos (@F.mul PrimeField.M_pos a0 a0) (@F.zero PrimeField.M_pos))
          with (@F.mul PrimeField.M_pos a0 a0) in Habs by ring.
        exact Habs. }
      apply Fp_sq_zero in Ha0sq. subst a0. exfalso. apply Hx. reflexivity.
    - (* a1 ≠ 0 => β = (a0·inv(a1))² *)
      exists (@F.mul PrimeField.M_pos a0 (@F.inv PrimeField.M_pos a1)).
      assert (Heq : @F.mul PrimeField.M_pos a0 a0 =
                     @F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bls377_beta a1) a1).
      { assert (@F.sub PrimeField.M_pos (@F.mul PrimeField.M_pos a0 a0)
                  (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bls377_beta a1) a1) =
                @F.zero PrimeField.M_pos) by exact Habs.
        assert (@F.mul PrimeField.M_pos a0 a0 =
                @F.sub PrimeField.M_pos (@F.zero PrimeField.M_pos)
                  (@F.opp PrimeField.M_pos (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos bls377_beta a1) a1))).
        { rewrite <- H. ring. }
        rewrite H0. ring. }
      transitivity (@F.mul PrimeField.M_pos (@F.mul PrimeField.M_pos a0 a0)
                     (@F.mul PrimeField.M_pos (@F.inv PrimeField.M_pos a1) (@F.inv PrimeField.M_pos a1))).
      + ring.
      + rewrite Heq. field. exact Ha1.
  Qed.

  (* Both invp2 and fp2_inv are right-inverses under mulp2.
     Since the Fp2 field has unique inverses, they must be equal. *)
  Lemma bls377_invp2_eq_fp2_inv : forall x,
    x <> QuadraticExtensions.zerop2 PrimeField.M_pos ->
    QuadraticExtensions.invp2 PrimeField.M_pos bls377_beta x =
    Fp6.fp2_inv PrimeField.M_pos bls377_beta x.
  Proof.
    intros [a0 a1] Hx.
    pose proof (bls377_norm_nonzero a0 a1 Hx) as Hnorm.
    (* invp2 is correct inverse: mulp2 x (invp2 x) = 1 *)
    assert (Hinvp2 : QuadraticExtensions.mulp2 PrimeField.M_pos bls377_beta (a0,a1)
      (QuadraticExtensions.invp2 PrimeField.M_pos bls377_beta (a0,a1)) =
      QuadraticExtensions.onep2 PrimeField.M_pos).
    { pose proof (Finv_l FFp2 (a0,a1) Hx). rewrite <- H. ring. }
    (* fp2_inv is also correct: mulp2 x (fp2_inv x) = 1 *)
    assert (Hfpinv : QuadraticExtensions.mulp2 PrimeField.M_pos bls377_beta (a0,a1)
      (Fp6.fp2_inv PrimeField.M_pos bls377_beta (a0,a1)) =
      QuadraticExtensions.onep2 PrimeField.M_pos).
    { unfold QuadraticExtensions.mulp2, Fp6.fp2_inv, QuadraticExtensions.onep2.
      cbn -[F.inv F.mul F.add F.sub F.opp F.zero F.one F.div PrimeField.M_pos].
      apply injective_projections;
        cbn -[F.inv F.mul F.add F.sub F.opp F.zero F.one F.div PrimeField.M_pos];
        field; assumption. }
    (* Both are right-inverses => both equal invp2 x => equal to each other *)
    pose proof (Finv_l FFp2 (a0,a1) Hx) as Hinv_l.
    (* Hinv_l : mulp2 (invp2 x) x = onep2 *)
    (* Show: invp2 x = y iff x * y = 1, by cancellation *)
    assert (Hy1 : QuadraticExtensions.invp2 PrimeField.M_pos bls377_beta (a0, a1) =
                  QuadraticExtensions.invp2 PrimeField.M_pos bls377_beta (a0, a1)) by reflexivity.
    assert (Hy2 : Fp6.fp2_inv PrimeField.M_pos bls377_beta (a0, a1) =
                  QuadraticExtensions.invp2 PrimeField.M_pos bls377_beta (a0, a1)).
    { transitivity (QuadraticExtensions.mulp2 PrimeField.M_pos bls377_beta
        (QuadraticExtensions.onep2 PrimeField.M_pos)
        (Fp6.fp2_inv PrimeField.M_pos bls377_beta (a0, a1))). { ring. }
      rewrite <- Hinv_l.
      transitivity (QuadraticExtensions.mulp2 PrimeField.M_pos bls377_beta
        (QuadraticExtensions.invp2 PrimeField.M_pos bls377_beta (a0, a1))
        (QuadraticExtensions.mulp2 PrimeField.M_pos bls377_beta (a0, a1)
          (Fp6.fp2_inv PrimeField.M_pos bls377_beta (a0, a1)))). { ring. }
      rewrite Hfpinv. ring. }
    symmetry. exact Hy2.
  Qed.

  (* ================================================================ *)
  (* Fp6/Fp12 instances via generic tower                              *)
  (* ================================================================ *)

  Let fp6_prefix := "bls377_Fp6_".
  Let fp12_prefix := "bls377_Fp12_".

  Instance bls377_Fp6_params : AbstractField.FieldParameters
    ((F PrimeField.M_pos * F PrimeField.M_pos) *
     (F PrimeField.M_pos * F PrimeField.M_pos) *
     (F PrimeField.M_pos * F PrimeField.M_pos)) :=
    Fp6_field_parameters bls377_beta bls377_xi_re bls377_xi_im (fp6_prefix:=fp6_prefix).

  Instance bls377_Fp6_rep : AbstractField.FieldRepresentation (F:=
    (F PrimeField.M_pos * F PrimeField.M_pos) *
    (F PrimeField.M_pos * F PrimeField.M_pos) *
    (F PrimeField.M_pos * F PrimeField.M_pos)) :=
    Fp6_field_representation bls377_beta bls377_xi_re bls377_xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

End BLS377.
