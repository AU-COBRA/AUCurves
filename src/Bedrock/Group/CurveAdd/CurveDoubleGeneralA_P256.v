(** * P-256 instantiation of the Rupicola general-a RCB doubling.

    Sibling of [CurveAddGeneralA_P256.v] for the derived doubling
    [CurveDoubleGeneralA.rcb_double_general_body].  Everything
    per-curve that the addition instantiation already provides —
    the Montgomery-encoded constants a = -3 and 3b
    ([p256_three_b_felem] / [p256_a_felem]), [p256_bounds_eq], the
    two loader bodies ([p256_three_b_func] / [p256_a_const_func]),
    their loader-spec proofs ([CurveAddGeneralA_P256_Loaders]) and
    the §5a bridge ingredients (feval/Montgomery-decoding
    correspondence, canonicity, Bignum/FElem transport) — is imported
    from those files, not duplicated.

    Contents:
      §1  Loader specs of the doubling derivation discharged from the
          addition loader proofs (the two spec copies are
          definitionally equal).
      §2  [p256_curve_double_general_func] := the derived body at
          P-256, and [p256_curve_double_general_ok] discharging
          [spec_of_rcb_double_general] from
          [rcb_double_general_correct].
      §3  The Z-level doubling spec at P-256
          ([P256_double_Gallina_spec]) and the Bignum-level
          specification shape of "curve_double_general" (ABI
          [poutx; pouty; poutz; pX; pY; pZ]), in the unconditional
          and the [_valid_out] shapes.
      §4  Bridge from the FElem-level [spec_of_rcb_double_general] to
          the [_valid_out] shape (intended Qed; the script is the
          six-buffer replay of the addition bridge), and the
          unconditional shape (Admitted, same obstruction as for the
          addition).

    Honesty ledger (this file): 1 Admitted —
    [p256_curve_double_general_bignum_bridge] (§4, unconditional
    shape; not derivable from the FElem-level spec, see the note at
    §4).  Every other proof is intended Qed and untested. *)

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
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P256.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P256_Loaders.
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Bedrock.Curve.P256Curve_G1.

Import Syntax ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section P256_DoubleGeneralA.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p256_field_parameters
    p256_field_parameters_ok
    p256_frep
    p256_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  (* ============================================================== *)
  (* §1. Loader specs of the doubling derivation                     *)
  (* ============================================================== *)

  (** [CurveDoubleGeneralA.spec_of_three_b_loader] is a verbatim
      copy of [CurveAddGeneralA.spec_of_three_b_loader]; applied to
      the same felem and name, the two unfold to the same fnspec
      (their [three_b_val] copies both reduce to
      [feval (proj1_sig p256_three_b_felem)]), so the addition loader
      proof is a proof of the doubling copy by conversion.
      PORT-CHECK (L): if [exact] does not see the two spec copies as
      convertible (e.g. an opaque [Local Definition] boundary), replay
      the loader script of CurveAddGeneralA_P256_Loaders.v against
      the doubling spec — it only uses the fnspec shape. *)
  Lemma p256_three_b_loader_ok_dbl :
    forall functions,
      map.get functions "p256_three_b" = Some p256_three_b_func ->
      CurveDoubleGeneralA.spec_of_three_b_loader
        p256_three_b_felem "p256_three_b" functions.
  Proof.
    intros functions Henv.
    Timeout 300 exact (p256_three_b_loader_ok functions Henv).
  Qed.

  Lemma p256_a_loader_ok_dbl :
    forall functions,
      map.get functions "p256_a_const" = Some p256_a_const_func ->
      CurveDoubleGeneralA.spec_of_a_loader
        p256_a_felem "p256_a_const" functions.
  Proof.
    intros functions Henv.
    Timeout 300 exact (p256_a_loader_ok functions Henv).
  Qed.

  (* ============================================================== *)
  (* §2. The derived body at P-256, and its spec                     *)
  (* ============================================================== *)

  Definition p256_curve_double_general_func : Syntax.func :=
    rcb_double_general_body "p256_three_b" "p256_a_const".

  (** [spec_of_rcb_double_general] for the instantiated body, from
      the generic derivation correctness [rcb_double_general_correct].
      Argument order as for [rcb_add_general_correct] (PORT-CHECK (C)
      of CurveDoubleGeneralA.v). *)
  Lemma p256_curve_double_general_ok :
    forall functions,
      map.get functions "curve_double_general"
      = Some p256_curve_double_general_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      CurveDoubleGeneralA.spec_of_three_b_loader
        p256_three_b_felem "p256_three_b" functions ->
      CurveDoubleGeneralA.spec_of_a_loader
        p256_a_felem "p256_a_const" functions ->
      spec_of_rcb_double_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions Henv Hmul Hadd Hsub Htb Ha.
    unfold p256_curve_double_general_func in Henv.
    Timeout 300 refine
      (rcb_double_general_correct p256_bounds_eq
         p256_three_b_felem "p256_three_b" p256_a_felem "p256_a_const"
         I functions _ Hmul Hadd Hsub Htb Ha).
    Timeout 120 exact Henv.
  Qed.

  (** End-to-end: with the two loader functions and the three field
      ops in the table, the derived body meets its FElem-level spec. *)
  Lemma p256_curve_double_general_full :
    forall functions,
      map.get functions "curve_double_general"
        = Some p256_curve_double_general_func ->
      map.get functions "p256_three_b" = Some p256_three_b_func ->
      map.get functions "p256_a_const" = Some p256_a_const_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_rcb_double_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions Hdbl_env Htb_env Ha_env Hmul Hadd Hsub.
    eapply p256_curve_double_general_ok; eauto using
      p256_three_b_loader_ok_dbl, p256_a_loader_ok_dbl.
  Qed.

  (* ============================================================== *)
  (* §3. Z-level and Bignum-level specifications                    *)
  (* ============================================================== *)

  Local Notation toZ ws := (List.map word.unsigned ws).
  Local Notation p256_valid := (WordByWordMontgomery.valid 64 4%nat p256_m).

  (** The Z-level doubling spec at the P-256 parameters, parallel to
      [P256Curve_G1.P256_add_Gallina_spec]
      (= BLS12_add_Gallina_spec m bw n m' a three_b). *)
  Definition P256_double_Gallina_spec :=
    rcb_double_general_Z_spec
      P256Curve_G1.m P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.m'
      P256Curve_G1.a P256Curve_G1.three_b.

  (** Bignum-level specification of "curve_double_general", ABI
      [poutx; pouty; poutz; pX; pY; pZ]; the doubling shape of
      [spec_of_p256_curve_add_general_bignum]. *)
  Definition spec_of_p256_curve_double_general_bignum
    : spec_of "curve_double_general" :=
    fun functions =>
      forall (wX wY wZ wold_outx wold_outy wold_outz : list word)
             (pX pY pZ poutx pouty poutz : word)
             (tr : Semantics.trace) (m0 : BasicC64Semantics.mem)
             (Rout : BasicC64Semantics.mem -> Prop),
        p256_valid (toZ wX) /\ p256_valid (toZ wY) /\ p256_valid (toZ wZ) ->
        (Bignum 4 pX wX * Bignum 4 pY wY * Bignum 4 pZ wZ *
         Bignum 4 poutx wold_outx * Bignum 4 pouty wold_outy *
         Bignum 4 poutz wold_outz * Rout)%sep m0 ->
        WeakestPrecondition.call functions "curve_double_general" tr m0
          [poutx; pouty; poutz; pX; pY; pZ]
          (fun tr' m' rets =>
             tr = tr' /\ rets = nil /\
             exists woutx wouty woutz : list word,
               (P256_double_Gallina_spec
                  (toZ wX) (toZ wY) (toZ wZ)
                  (toZ woutx) (toZ wouty) (toZ woutz)
                /\ p256_valid (toZ woutx)
                /\ p256_valid (toZ wouty)
                /\ p256_valid (toZ woutz)) /\
               (Bignum 4 pX wX * Bignum 4 pY wY * Bignum 4 pZ wZ *
                Bignum 4 poutx woutx * Bignum 4 pouty wouty *
                Bignum 4 poutz woutz * Rout)%sep m').

  (** The shape with the three output buffers required to hold valid
      (canonical) encodings on entry — what [spec_of_rcb_double_general]
      (FElem (Some tight_bounds) on the outputs) supports; see the
      note at [spec_of_p256_curve_add_general_bignum_valid_out]. *)
  Definition spec_of_p256_curve_double_general_bignum_valid_out
    : spec_of "curve_double_general" :=
    fun functions =>
      forall (wX wY wZ wold_outx wold_outy wold_outz : list word)
             (pX pY pZ poutx pouty poutz : word)
             (tr : Semantics.trace) (m0 : BasicC64Semantics.mem)
             (Rout : BasicC64Semantics.mem -> Prop),
        p256_valid (toZ wX) /\ p256_valid (toZ wY) /\ p256_valid (toZ wZ) /\
        p256_valid (toZ wold_outx) /\ p256_valid (toZ wold_outy) /\
        p256_valid (toZ wold_outz) ->
        (Bignum 4 pX wX * Bignum 4 pY wY * Bignum 4 pZ wZ *
         Bignum 4 poutx wold_outx * Bignum 4 pouty wold_outy *
         Bignum 4 poutz wold_outz * Rout)%sep m0 ->
        WeakestPrecondition.call functions "curve_double_general" tr m0
          [poutx; pouty; poutz; pX; pY; pZ]
          (fun tr' m' rets =>
             tr = tr' /\ rets = nil /\
             exists woutx wouty woutz : list word,
               (P256_double_Gallina_spec
                  (toZ wX) (toZ wY) (toZ wZ)
                  (toZ woutx) (toZ wouty) (toZ woutz)
                /\ p256_valid (toZ woutx)
                /\ p256_valid (toZ wouty)
                /\ p256_valid (toZ woutz)) /\
               (Bignum 4 pX wX * Bignum 4 pY wY * Bignum 4 pZ wZ *
                Bignum 4 poutx woutx * Bignum 4 pouty wouty *
                Bignum 4 poutz woutz * Rout)%sep m').

  (* ============================================================== *)
  (* §4. The bridge                                                  *)
  (* ============================================================== *)

  (** The Montgomery decoding as it occurs in [P256_double_Gallina_spec]
      (the [P256Curve_G1] constants), as in CurveAddGeneralA_P256.v §5a. *)
  Local Notation G_evfrom x :=
    (@WordByWordMontgomery.eval P256Curve_G1.bw P256Curve_G1.n
       (@WordByWordMontgomery.from_montgomerymod
          P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.m P256Curve_G1.m' x)).

  (** Pre-transport of the six Bignums (all valid) to the
      [Compilation2.FElem (Some tight_bounds)] chain of
      [spec_of_rcb_double_general]. *)
  Lemma p256_pre_bridge_dbl
        (pX pY pZ poutx pouty poutz : word)
        (wX wY wZ wox woy woz : list word)
        (R : BasicC64Semantics.mem -> Prop) :
    p256_valid (toZ wX) -> p256_valid (toZ wY) -> p256_valid (toZ wZ) ->
    p256_valid (toZ wox) -> p256_valid (toZ woy) -> p256_valid (toZ woz) ->
    Lift1Prop.impl1
      (Bignum 4 pX wX * Bignum 4 pY wY * Bignum 4 pZ wZ *
       Bignum 4 poutx wox * Bignum 4 pouty woy * Bignum 4 poutz woz * R)%sep
      (Compilation2.FElem (Some tight_bounds) pX (feval wX)
       * Compilation2.FElem (Some tight_bounds) pY (feval wY)
       * Compilation2.FElem (Some tight_bounds) pZ (feval wZ)
       * Compilation2.FElem (Some tight_bounds) poutx (feval wox)
       * Compilation2.FElem (Some tight_bounds) pouty (feval woy)
       * Compilation2.FElem (Some tight_bounds) poutz (feval woz) * R)%sep.
  Proof.
    intros.
    repeat apply sep_impl1_both;
      first [ apply p256_Bignum_to_FElem2; assumption | reflexivity ].
  Qed.

  (** Rebuild a left-nested sep chain from its destructed pieces. *)
  Local Ltac rebuild_sep :=
    lazymatch goal with
    | |- sep _ _ _ => eapply sep_intro'; [eassumption | rebuild_sep | rebuild_sep]
    | |- _ => assumption
    end.

  (** Bridge from the FElem-level derived spec to the Bignum shape:
      the six-buffer replay of
      [p256_curve_add_general_bignum_bridge_valid_out].
      1. pre-transport ([p256_pre_bridge_dbl]); 2. the FElem-level
      spec at [X := feval wX] etc.; 3. post-transport by destructing
      the sep chain, [p256_FElem2_to_Bignum] on each clause,
      canonicity ([p256_feval_inj]) for the three preserved inputs,
      and [rebuild_sep]; 4. algebra by the generic
      [rcb_double_general_gallina_to_Z], whose premises are the
      Montgomery-decoding identities ([p256_feval_evfrom_valid]) and
      the constant identifications ([p256_a_toZ] / [p256_three_b_toZ]).
      PORT-CHECK (B): the destruct/canonicity/exists steps are
      pattern-driven and independent of the buffer count; the only
      count-dependent line is the 22-underscore [refine]. *)
  Theorem p256_curve_double_general_bignum_bridge_valid_out :
    forall functions,
      spec_of_rcb_double_general p256_three_b_felem p256_a_felem functions ->
      spec_of_p256_curve_double_general_bignum_valid_out functions.
  Proof.
    intros functions Hspec.
    unfold spec_of_p256_curve_double_general_bignum_valid_out.
    intros wX wY wZ wold_outx wold_outy wold_outz
           pX pY pZ poutx pouty poutz tr m0 Rout
           Hvalid Hsep.
    destruct Hvalid as (HvX & HvY & HvZ & Hvox & Hvoy & Hvoz).
    (* 1+2: pre-transport and the FElem-level call *)
    cbv [spec_of_rcb_double_general] in Hspec.
    specialize (Hspec poutx pouty poutz pX pY pZ
                  (feval wX) (feval wY) (feval wZ)
                  (feval wold_outx) (feval wold_outy) (feval wold_outz)
                  Rout tr m0).
    specialize (Hspec
                  (p256_pre_bridge_dbl pX pY pZ poutx pouty poutz
                     wX wY wZ wold_outx wold_outy wold_outz Rout
                     HvX HvY HvZ Hvox Hvoy Hvoz m0 Hsep)).
    eapply WeakestPreconditionProperties.Proper_call; [ | exact Hspec ].
    intros tr' m' rets Hpost.
    cbv beta in Hpost.
    destruct Hpost as (Hrets & Htr & outx & outy & outz & Hgal & Hsep').
    clear Hspec Hsep.
    cbv beta.
    split; [exact Htr|]. split; [exact Hrets|].
    (* 3: post-transport *)
    repeat match goal with
           | H : sep _ _ _ |- _ => destruct H as (? & ? & ? & ? & ?)
           end.
    repeat match goal with
           | H : _ |- _ =>
               apply p256_FElem2_to_Bignum in H; destruct H as (? & ? & ? & ?)
           end.
    (* the three inputs are preserved: canonicity *)
    repeat match goal with
           | Hfe : feval ?ws = feval ?w,
             Hv1 : p256_valid (toZ ?ws), Hv2 : p256_valid (toZ ?w) |- _ =>
               assert (ws = w) by (apply p256_feval_inj; assumption);
               subst ws; clear Hfe
           end.
    lazymatch goal with
    | Hx : feval ?wx = outx, Hy : feval ?wy = outy, Hz : feval ?wz = outz |- _ =>
        exists wx, wy, wz
    end.
    split; [ | rebuild_sep ].
    split; [ | split; [assumption | split; assumption] ].
    (* 4: algebra, by the generic F-level lemma *)
    try unfold P256_double_Gallina_spec.
    Timeout 600 refine
      (rcb_double_general_gallina_to_Z (field_parameters := p256_field_parameters)
         P256Curve_G1.m P256Curve_G1.bw P256Curve_G1.n P256Curve_G1.m'
         P256Curve_G1.a P256Curve_G1.three_b p256_M_eq
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hgal).
    Show.
    (* Each premise is closed by the one intended term, chosen by the
       goal's shape; no tactic may fall through to a unification that
       unfolds the Montgomery code (the addition's [first [...]]
       closer timed out at 600 s for that reason). *)
    all: timeout 60
      (lazymatch goal with
       | |- G_evfrom (toZ ?w) = F.to_Z (feval ?w) =>
           exact (p256_feval_evfrom_valid w ltac:(assumption))
       | |- G_evfrom (toZ ?w) = F.to_Z ?o =>
           lazymatch goal with
           | H : feval w = o |- _ =>
               exact (eq_trans (p256_feval_evfrom_valid w ltac:(assumption))
                               (f_equal F.to_Z H))
           end
       | |- @WordByWordMontgomery.eval _ _ (MontgomeryCurveSpecs.a_list _ _ _) = _ =>
           exact p256_a_toZ
       | |- @WordByWordMontgomery.eval _ _ (MontgomeryCurveSpecs.three_b_list _ _ _) = _ =>
           exact p256_three_b_toZ
       | |- ?G => fail 99 "BRIDGE-RESIDUAL" G
       end).
  Qed.

  (** The unconditional shape, NOT stated as a theorem.

      <<
      Theorem p256_curve_double_general_bignum_bridge :
        forall functions,
          spec_of_rcb_double_general p256_three_b_felem p256_a_felem functions ->
          spec_of_p256_curve_double_general_bignum functions.
      >>

      is not derivable from [spec_of_rcb_double_general]: that spec
      requires [FElem (Some tight_bounds) poutx outxold] for the three
      output buffers, i.e. canonical ([p256_valid]) old contents, and
      says nothing about a call on non-canonical output buffers, while
      [spec_of_p256_curve_double_general_bignum] assumes nothing about
      [wold_outx]/[wold_outy]/[wold_outz].  A function satisfying the
      FElem-level spec and misbehaving on non-canonical output buffers
      is a model of the hypothesis and a counter-model of the
      conclusion.  Downstream users take
      [p256_curve_double_general_bignum_bridge_valid_out] above; the
      unconditional shape would need the derivation in
      CurveDoubleGeneralA.v to require only [FElem None] for the
      outputs.  Same status as the addition
      (CurveAddGeneralA_P256.v). *)

End P256_DoubleGeneralA.
