(** * P-384 instantiation of the Rupicola general-a RCB doubling.

    Parallel to [CurveDoubleGeneralA_P256.v] at the P-384 field
    representation [p384_frep] (6 limbs of 64 bits).  All per-curve
    ingredients (constants, loader bodies, loader-spec proofs, §5a
    bridge lemmas) are imported from [CurveAddGeneralA_P384.v], which
    is self-contained (its loader proofs are in the same file).

    Compile status: deferred together with CurveAddGeneralA_P384.v
    (this file depends on it).

    Honesty ledger (this file): 0 Admitted.  The unconditional bridge
    shape is not stated (comment block at the end of §4). *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SeparationLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require Import bedrock2.BasicC64Semantics.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Bedrock.Group.CurveAdd.CurveDoubleGeneralA.
Require Import Bedrock.Group.CurveAdd.CurveDoubleGeneralA_GallinaToZ.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P384.
Require Import Bedrock.Field.Synthesis.Examples.p384_field.
Require Import Bedrock.Curve.P384Curve_G1.

Import Syntax ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section P384_DoubleGeneralA.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p384_field_parameters
    p384_field_parameters_ok
    p384_frep
    p384_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  (* ============================================================== *)
  (* §1. Loader specs of the doubling derivation                     *)
  (* ============================================================== *)

  (* PORT-CHECK (L): conversion between the two spec copies, as in
     CurveDoubleGeneralA_P256.v §1. *)
  Lemma p384_three_b_loader_ok_dbl :
    forall functions,
      map.get functions "p384_three_b" = Some p384_three_b_func ->
      CurveDoubleGeneralA.spec_of_three_b_loader
        p384_three_b_felem "p384_three_b" functions.
  Proof.
    intros functions Henv.
    Timeout 300 exact (p384_three_b_loader_ok functions Henv).
  Qed.

  Lemma p384_a_loader_ok_dbl :
    forall functions,
      map.get functions "p384_a_const" = Some p384_a_const_func ->
      CurveDoubleGeneralA.spec_of_a_loader
        p384_a_felem "p384_a_const" functions.
  Proof.
    intros functions Henv.
    Timeout 300 exact (p384_a_loader_ok functions Henv).
  Qed.

  (* ============================================================== *)
  (* §2. The derived body at P-384, and its spec                     *)
  (* ============================================================== *)

  Definition p384_curve_double_general_func : Syntax.func :=
    rcb_double_general_body "p384_three_b" "p384_a_const".

  Lemma p384_curve_double_general_ok :
    forall functions,
      map.get functions "curve_double_general"
      = Some p384_curve_double_general_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      CurveDoubleGeneralA.spec_of_three_b_loader
        p384_three_b_felem "p384_three_b" functions ->
      CurveDoubleGeneralA.spec_of_a_loader
        p384_a_felem "p384_a_const" functions ->
      spec_of_rcb_double_general p384_three_b_felem p384_a_felem functions.
  Proof.
    intros functions Henv Hmul Hadd Hsub Htb Ha.
    unfold p384_curve_double_general_func in Henv.
    Timeout 300 refine
      (rcb_double_general_correct p384_bounds_eq
         p384_three_b_felem "p384_three_b" p384_a_felem "p384_a_const"
         I functions _ Hmul Hadd Hsub Htb Ha).
    Timeout 120 exact Henv.
  Qed.

  Lemma p384_curve_double_general_full :
    forall functions,
      map.get functions "curve_double_general"
        = Some p384_curve_double_general_func ->
      map.get functions "p384_three_b" = Some p384_three_b_func ->
      map.get functions "p384_a_const" = Some p384_a_const_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_rcb_double_general p384_three_b_felem p384_a_felem functions.
  Proof.
    intros functions Hdbl_env Htb_env Ha_env Hmul Hadd Hsub.
    eapply p384_curve_double_general_ok; eauto using
      p384_three_b_loader_ok_dbl, p384_a_loader_ok_dbl.
  Qed.

  (* ============================================================== *)
  (* §3. Z-level and Bignum-level specifications                    *)
  (* ============================================================== *)

  Local Notation toZ ws := (List.map word.unsigned ws).
  Local Notation p384_valid := (WordByWordMontgomery.valid 64 6%nat p384_m).

  Definition P384_double_Gallina_spec :=
    rcb_double_general_Z_spec
      P384Curve_G1.m P384Curve_G1.bw P384Curve_G1.n P384Curve_G1.m'
      P384Curve_G1.a P384Curve_G1.three_b.

  Definition spec_of_p384_curve_double_general_bignum
    : spec_of "curve_double_general" :=
    fun functions =>
      forall (wX wY wZ wold_outx wold_outy wold_outz : list word)
             (pX pY pZ poutx pouty poutz : word)
             (tr : Semantics.trace) (m0 : BasicC64Semantics.mem)
             (Rout : BasicC64Semantics.mem -> Prop),
        p384_valid (toZ wX) /\ p384_valid (toZ wY) /\ p384_valid (toZ wZ) ->
        (Bignum 6 pX wX * Bignum 6 pY wY * Bignum 6 pZ wZ *
         Bignum 6 poutx wold_outx * Bignum 6 pouty wold_outy *
         Bignum 6 poutz wold_outz * Rout)%sep m0 ->
        WeakestPrecondition.call functions "curve_double_general" tr m0
          [poutx; pouty; poutz; pX; pY; pZ]
          (fun tr' m' rets =>
             tr = tr' /\ rets = nil /\
             exists woutx wouty woutz : list word,
               (P384_double_Gallina_spec
                  (toZ wX) (toZ wY) (toZ wZ)
                  (toZ woutx) (toZ wouty) (toZ woutz)
                /\ p384_valid (toZ woutx)
                /\ p384_valid (toZ wouty)
                /\ p384_valid (toZ woutz)) /\
               (Bignum 6 pX wX * Bignum 6 pY wY * Bignum 6 pZ wZ *
                Bignum 6 poutx woutx * Bignum 6 pouty wouty *
                Bignum 6 poutz woutz * Rout)%sep m').

  Definition spec_of_p384_curve_double_general_bignum_valid_out
    : spec_of "curve_double_general" :=
    fun functions =>
      forall (wX wY wZ wold_outx wold_outy wold_outz : list word)
             (pX pY pZ poutx pouty poutz : word)
             (tr : Semantics.trace) (m0 : BasicC64Semantics.mem)
             (Rout : BasicC64Semantics.mem -> Prop),
        p384_valid (toZ wX) /\ p384_valid (toZ wY) /\ p384_valid (toZ wZ) /\
        p384_valid (toZ wold_outx) /\ p384_valid (toZ wold_outy) /\
        p384_valid (toZ wold_outz) ->
        (Bignum 6 pX wX * Bignum 6 pY wY * Bignum 6 pZ wZ *
         Bignum 6 poutx wold_outx * Bignum 6 pouty wold_outy *
         Bignum 6 poutz wold_outz * Rout)%sep m0 ->
        WeakestPrecondition.call functions "curve_double_general" tr m0
          [poutx; pouty; poutz; pX; pY; pZ]
          (fun tr' m' rets =>
             tr = tr' /\ rets = nil /\
             exists woutx wouty woutz : list word,
               (P384_double_Gallina_spec
                  (toZ wX) (toZ wY) (toZ wZ)
                  (toZ woutx) (toZ wouty) (toZ woutz)
                /\ p384_valid (toZ woutx)
                /\ p384_valid (toZ wouty)
                /\ p384_valid (toZ woutz)) /\
               (Bignum 6 pX wX * Bignum 6 pY wY * Bignum 6 pZ wZ *
                Bignum 6 poutx woutx * Bignum 6 pouty wouty *
                Bignum 6 poutz woutz * Rout)%sep m').

  (* ============================================================== *)
  (* §4. The bridge                                                  *)
  (* ============================================================== *)

  Local Notation G_evfrom x :=
    (@WordByWordMontgomery.eval P384Curve_G1.bw P384Curve_G1.n
       (@WordByWordMontgomery.from_montgomerymod
          P384Curve_G1.bw P384Curve_G1.n P384Curve_G1.m P384Curve_G1.m' x)).

  Lemma p384_pre_bridge_dbl
        (pX pY pZ poutx pouty poutz : word)
        (wX wY wZ wox woy woz : list word)
        (R : BasicC64Semantics.mem -> Prop) :
    p384_valid (toZ wX) -> p384_valid (toZ wY) -> p384_valid (toZ wZ) ->
    p384_valid (toZ wox) -> p384_valid (toZ woy) -> p384_valid (toZ woz) ->
    Lift1Prop.impl1
      (Bignum 6 pX wX * Bignum 6 pY wY * Bignum 6 pZ wZ *
       Bignum 6 poutx wox * Bignum 6 pouty woy * Bignum 6 poutz woz * R)%sep
      (Compilation2.FElem (Some tight_bounds) pX (feval wX)
       * Compilation2.FElem (Some tight_bounds) pY (feval wY)
       * Compilation2.FElem (Some tight_bounds) pZ (feval wZ)
       * Compilation2.FElem (Some tight_bounds) poutx (feval wox)
       * Compilation2.FElem (Some tight_bounds) pouty (feval woy)
       * Compilation2.FElem (Some tight_bounds) poutz (feval woz) * R)%sep.
  Proof.
    intros.
    repeat apply sep_impl1_both;
      first [ apply p384_Bignum_to_FElem2; assumption | reflexivity ].
  Qed.

  Local Ltac rebuild_sep :=
    lazymatch goal with
    | |- sep _ _ _ => eapply sep_intro'; [eassumption | rebuild_sep | rebuild_sep]
    | |- _ => assumption
    end.

  Theorem p384_curve_double_general_bignum_bridge_valid_out :
    forall functions,
      spec_of_rcb_double_general p384_three_b_felem p384_a_felem functions ->
      spec_of_p384_curve_double_general_bignum_valid_out functions.
  Proof.
    intros functions Hspec.
    unfold spec_of_p384_curve_double_general_bignum_valid_out.
    intros wX wY wZ wold_outx wold_outy wold_outz
           pX pY pZ poutx pouty poutz tr m0 Rout
           Hvalid Hsep.
    destruct Hvalid as (HvX & HvY & HvZ & Hvox & Hvoy & Hvoz).
    cbv [spec_of_rcb_double_general] in Hspec.
    specialize (Hspec poutx pouty poutz pX pY pZ
                  (feval wX) (feval wY) (feval wZ)
                  (feval wold_outx) (feval wold_outy) (feval wold_outz)
                  Rout tr m0).
    specialize (Hspec
                  (p384_pre_bridge_dbl pX pY pZ poutx pouty poutz
                     wX wY wZ wold_outx wold_outy wold_outz Rout
                     HvX HvY HvZ Hvox Hvoy Hvoz m0 Hsep)).
    eapply WeakestPreconditionProperties.Proper_call; [ | exact Hspec ].
    intros tr' m' rets Hpost.
    cbv beta in Hpost.
    destruct Hpost as (Hrets & Htr & outx & outy & outz & Hgal & Hsep').
    clear Hspec Hsep.
    cbv beta.
    split; [exact Htr|]. split; [exact Hrets|].
    repeat match goal with
           | H : sep _ _ _ |- _ => destruct H as (? & ? & ? & ? & ?)
           end.
    repeat match goal with
           | H : _ |- _ =>
               apply p384_FElem2_to_Bignum in H; destruct H as (? & ? & ? & ?)
           end.
    repeat match goal with
           | Hfe : feval ?ws = feval ?w,
             Hv1 : p384_valid (toZ ?ws), Hv2 : p384_valid (toZ ?w) |- _ =>
               assert (ws = w) by (apply p384_feval_inj; assumption);
               subst ws; clear Hfe
           end.
    lazymatch goal with
    | Hx : feval ?wx = outx, Hy : feval ?wy = outy, Hz : feval ?wz = outz |- _ =>
        exists wx, wy, wz
    end.
    split; [ | rebuild_sep ].
    split; [ | split; [assumption | split; assumption] ].
    try unfold P384_double_Gallina_spec.
    Timeout 600 refine
      (rcb_double_general_gallina_to_Z (field_parameters := p384_field_parameters)
         P384Curve_G1.m P384Curve_G1.bw P384Curve_G1.n P384Curve_G1.m'
         P384Curve_G1.a P384Curve_G1.three_b p384_M_eq
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hgal).
    Show.
    (* Per-goal dispatch to a single term; see CurveDoubleGeneralA_P256.v. *)
    all: timeout 60
      (lazymatch goal with
       | |- G_evfrom (toZ ?w) = F.to_Z (feval ?w) =>
           exact (p384_feval_evfrom_valid w ltac:(assumption))
       | |- G_evfrom (toZ ?w) = F.to_Z ?o =>
           lazymatch goal with
           | H : feval w = o |- _ =>
               exact (eq_trans (p384_feval_evfrom_valid w ltac:(assumption))
                               (f_equal F.to_Z H))
           end
       | |- @WordByWordMontgomery.eval _ _ (MontgomeryCurveSpecs.a_list _ _ _) = _ =>
           exact p384_a_toZ
       | |- @WordByWordMontgomery.eval _ _ (MontgomeryCurveSpecs.three_b_list _ _ _) = _ =>
           exact p384_three_b_toZ
       | |- ?G => fail 99 "BRIDGE-RESIDUAL" G
       end).
  Qed.

  (** The unconditional shape, NOT stated as a theorem.

      <<
      Theorem p384_curve_double_general_bignum_bridge :
        forall functions,
          spec_of_rcb_double_general p384_three_b_felem p384_a_felem functions ->
          spec_of_p384_curve_double_general_bignum functions.
      >>

      is not derivable from [spec_of_rcb_double_general] (canonical
      output buffers are required on entry by the FElem-level spec);
      see the note in CurveDoubleGeneralA_P256.v.  Downstream users
      take [p384_curve_double_general_bignum_bridge_valid_out]. *)

End P384_DoubleGeneralA.
