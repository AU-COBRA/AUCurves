(** Generic transport lemmas for WBW Montgomery G1 coordinate operations.

    Each lemma proves that a fiat-crypto [spec_of_BinOp] / [spec_of_UnOp]
    (in the New-pipeline form, taking a [FieldRepresentation]) implies
    the corresponding Bignum-style body from
    [WbwMontgomeryG1_BignumSpecBodies].

    Adoption collapses each curve's 5 [*_bignum_correct] lemmas (each
    ~55 LoC, ~275 LoC/curve) into 5 one-liners:

    {[
      Lemma pallas_mul_bignum_correct functions
        : spec_of_BinOp bin_mul (field_representation:=pallas_frep) functions
          -> spec_of_pallas_mul_bignum functions
        := mul_bignum_transport pallas_feval_def functions.
    ]}

    7 curves × ~255 LoC saved per curve = ~1800 LoC cleanup. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Memory.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.ArrayCasts.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Map.Interface.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecBodies.
Require Import Bedrock.Curve.WbwMontgomeryG1_WiredBridges.

Import ListNotations.
Local Open Scope Z_scope.

Section Transports.
  Context {field_parameters : FieldParameters}.
  Context {field_representation : FieldRepresentation}.
  Context {field_representation_ok : FieldRepresentation_ok}.

  Local Notation bw := 64%Z.
  Local Notation n  := (felem_size_in_words (FieldRepresentation := field_representation)).
  Local Notation m  := (Z.pos M_pos).
  Local Notation m' := (@Field.m' bw field_parameters).
  Local Notation eval     := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
  Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation toZ       := (List.map Interface.word.unsigned).

  (** As in [WbwMontgomeryG1_WiredBridges]: downstream curves supply this
      via a one-line [reflexivity] proof. *)
  Variable feval_wbw_def :
    forall (ws : list word.rep),
      feval ws = F.of_Z M_pos (eval (from_mont (toZ ws))).

  (** Curve-specific definitional equality: for a WBW field_representation,
      [bounded_by tight_bounds ws] unfolds to [WBW.valid bw n m (toZ ws)].
      Each curve supplies both directions via [reflexivity]. *)
  Variable tight_of_valid :
    forall (ws : list word.rep),
      WordByWordMontgomery.valid bw n m (toZ ws) ->
      bounded_by tight_bounds ws.
  Variable valid_of_tight :
    forall (ws : list word.rep),
      bounded_by tight_bounds ws ->
      WordByWordMontgomery.valid bw n m (toZ ws).
  Variable valid_of_loose :
    forall (ws : list word.rep),
      bounded_by loose_bounds ws ->
      WordByWordMontgomery.valid bw n m (toZ ws).
  Variable loose_of_valid :
    forall (ws : list word.rep),
      WordByWordMontgomery.valid bw n m (toZ ws) ->
      bounded_by loose_bounds ws.

  (** Specialized bridges for use in the transport proofs. *)
  Let feval_toZ         := feval_toZ         feval_wbw_def.
  Let feval_mul_bridge  := feval_mul_bridge  feval_wbw_def.
  Let feval_add_bridge  := feval_add_bridge  feval_wbw_def.
  Let feval_sub_bridge  := feval_sub_bridge  feval_wbw_def.
  Let feval_square_bridge := feval_square_bridge feval_wbw_def.
  Let feval_opp_bridge  := feval_opp_bridge  feval_wbw_def.

  (** ** mul *)

  Lemma mul_bignum_transport functions :
    spec_of_BinOp bin_mul (field_representation:=field_representation) functions ->
    binop_mul_body functions.
  Proof.
    intros Hfelem.
    intros wsx wsy old_out px py pout tr m0 Rx Ry Rout.
    intros Hvalx Hvaly Hlenout Hsepx Hsepy Hsepout.
    pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
    pose proof (Bignum_length _ _ _ _ _ Hsepy) as Hleny.
    set (fx := exist _ wsx Hlenx : felem).
    set (fy := exist _ wsy Hleny : felem).
    set (fout := exist _ old_out Hlenout : felem).
    seprewrite_in (Bignum_to_FElem px wsx Hlenx) Hsepx.
    seprewrite_in (Bignum_to_FElem py wsy Hleny) Hsepy.
    seprewrite_in (Bignum_to_FElem pout old_out Hlenout) Hsepout.
    seprewrite_in (felem_to_bytes pout fout) Hsepout.
    unfold spec_of_BinOp in Hfelem.
    set (out_bs := ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list fout)).
    specialize (Hfelem pout px py fx fy out_bs Rout tr m0).
    cbv [bin_mul bin_xbounds bin_ybounds bin_outbounds bin_model] in Hfelem.
    assert (Hbdx : bounded_by loose_bounds (felem_to_list fx))
      by (apply relax_bounds; apply tight_of_valid; exact Hvalx).
    assert (Hbdy : bounded_by loose_bounds (felem_to_list fy))
      by (apply relax_bounds; apply tight_of_valid; exact Hvaly).
    assert (Hcall : call functions mul tr m0 [pout; px; py]
      (fun (tr' : trace) (mem' : map.rep) (rets : list word.rep) =>
         rets = [] /\ tr = tr' /\
         (exists out0 : felem,
            feval (felem_to_list out0) =
            (feval (felem_to_list fx) * feval (felem_to_list fy))%F /\
            bounded_by tight_bounds (felem_to_list out0) /\
            (FElem pout out0 * Rout)%sep mem'))).
    { apply Hfelem.
      refine (conj Hbdx (conj Hbdy (conj _ (conj _ (conj _ _))))).
      - exact (ws2bs_felem_length fout).
      - exists Rx. exact Hsepx.
      - exists Ry. exact Hsepy.
      - exact Hsepout. }
    eapply Proper_call; [ | exact Hcall].
    clear Hcall Hfelem Hsepx Hsepy Hsepout Hbdx Hbdy.
    intros tr' m' rets (Hrets & Htr & out0 & Hfeval_out & Hbd_out & Hsep_out).
    split; [exact Htr|]. split; [exact Hrets|].
    exists (felem_to_list out0).
    split; [exact (proj2_sig out0)|].
    split; [exact (valid_of_tight _ Hbd_out)|].
    split.
    - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
      change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
      exact Hsep_out.
    - change (felem_to_list fx) with wsx in Hfeval_out.
      change (felem_to_list fy) with wsy in Hfeval_out.
      apply (feval_mul_bridge _ _ _ Hfeval_out).
  Qed.

  (** ** add *)

  Lemma add_bignum_transport functions :
    spec_of_BinOp bin_add (field_representation:=field_representation) functions ->
    binop_add_body functions.
  Proof.
    intros Hfelem.
    intros wsx wsy old_out px py pout tr m0 Rx Ry Rout.
    intros Hvalx Hvaly Hlenout Hsepx Hsepy Hsepout.
    pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
    pose proof (Bignum_length _ _ _ _ _ Hsepy) as Hleny.
    set (fx := exist _ wsx Hlenx : felem).
    set (fy := exist _ wsy Hleny : felem).
    set (fout := exist _ old_out Hlenout : felem).
    seprewrite_in (Bignum_to_FElem px wsx Hlenx) Hsepx.
    seprewrite_in (Bignum_to_FElem py wsy Hleny) Hsepy.
    seprewrite_in (Bignum_to_FElem pout old_out Hlenout) Hsepout.
    seprewrite_in (felem_to_bytes pout fout) Hsepout.
    unfold spec_of_BinOp in Hfelem.
    set (out_bs := ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list fout)).
    specialize (Hfelem pout px py fx fy out_bs Rout tr m0).
    cbv [bin_add bin_xbounds bin_ybounds bin_outbounds bin_model] in Hfelem.
    assert (Hcall : call functions add tr m0 [pout; px; py]
      (fun (tr' : trace) (mem' : map.rep) (rets : list word.rep) =>
         rets = [] /\ tr = tr' /\
         (exists out0 : felem,
            feval (felem_to_list out0) =
            (feval (felem_to_list fx) + feval (felem_to_list fy))%F /\
            bounded_by loose_bounds (felem_to_list out0) /\
            (FElem pout out0 * Rout)%sep mem'))).
    { apply Hfelem.
      refine (conj (tight_of_valid _ Hvalx) (conj (tight_of_valid _ Hvaly) (conj _ (conj _ (conj _ _))))).
      - exact (ws2bs_felem_length fout).
      - exists Rx. exact Hsepx.
      - exists Ry. exact Hsepy.
      - exact Hsepout. }
    eapply Proper_call; [ | exact Hcall].
    clear Hcall Hfelem Hsepx Hsepy Hsepout.
    intros tr' m' rets (Hrets & Htr & out0 & Hfeval_out & Hbd_out & Hsep_out).
    split; [exact Htr|]. split; [exact Hrets|].
    exists (felem_to_list out0).
    split; [exact (proj2_sig out0)|].
    split; [exact (valid_of_loose _ Hbd_out)|].
    split.
    - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
      change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
      exact Hsep_out.
    - change (felem_to_list fx) with wsx in Hfeval_out.
      change (felem_to_list fy) with wsy in Hfeval_out.
      apply (feval_add_bridge _ _ _ Hfeval_out).
  Qed.

  (** ** sub *)

  Lemma sub_bignum_transport functions :
    spec_of_BinOp bin_sub (field_representation:=field_representation) functions ->
    binop_sub_body functions.
  Proof.
    intros Hfelem.
    intros wsx wsy old_out px py pout tr m0 Rx Ry Rout.
    intros Hvalx Hvaly Hlenout Hsepx Hsepy Hsepout.
    pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
    pose proof (Bignum_length _ _ _ _ _ Hsepy) as Hleny.
    set (fx := exist _ wsx Hlenx : felem).
    set (fy := exist _ wsy Hleny : felem).
    set (fout := exist _ old_out Hlenout : felem).
    seprewrite_in (Bignum_to_FElem px wsx Hlenx) Hsepx.
    seprewrite_in (Bignum_to_FElem py wsy Hleny) Hsepy.
    seprewrite_in (Bignum_to_FElem pout old_out Hlenout) Hsepout.
    seprewrite_in (felem_to_bytes pout fout) Hsepout.
    unfold spec_of_BinOp in Hfelem.
    set (out_bs := ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list fout)).
    specialize (Hfelem pout px py fx fy out_bs Rout tr m0).
    cbv [bin_sub bin_xbounds bin_ybounds bin_outbounds bin_model] in Hfelem.
    assert (Hcall : call functions sub tr m0 [pout; px; py]
      (fun (tr' : trace) (mem' : map.rep) (rets : list word.rep) =>
         rets = [] /\ tr = tr' /\
         (exists out0 : felem,
            feval (felem_to_list out0) =
            (feval (felem_to_list fx) - feval (felem_to_list fy))%F /\
            bounded_by loose_bounds (felem_to_list out0) /\
            (FElem pout out0 * Rout)%sep mem'))).
    { apply Hfelem.
      refine (conj (tight_of_valid _ Hvalx) (conj (tight_of_valid _ Hvaly) (conj _ (conj _ (conj _ _))))).
      - exact (ws2bs_felem_length fout).
      - exists Rx. exact Hsepx.
      - exists Ry. exact Hsepy.
      - exact Hsepout. }
    eapply Proper_call; [ | exact Hcall].
    clear Hcall Hfelem Hsepx Hsepy Hsepout.
    intros tr' m' rets (Hrets & Htr & out0 & Hfeval_out & Hbd_out & Hsep_out).
    split; [exact Htr|]. split; [exact Hrets|].
    exists (felem_to_list out0).
    split; [exact (proj2_sig out0)|].
    split; [exact (valid_of_loose _ Hbd_out)|].
    split.
    - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
      change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
      exact Hsep_out.
    - change (felem_to_list fx) with wsx in Hfeval_out.
      change (felem_to_list fy) with wsy in Hfeval_out.
      apply (feval_sub_bridge _ _ _ Hfeval_out).
  Qed.

  (** ** square *)

  Lemma square_bignum_transport functions :
    spec_of_UnOp un_square (field_representation:=field_representation) functions ->
    unop_square_body functions.
  Proof.
    intros Hfelem.
    intros wsx old_out px pout tr m0 Rx Rout.
    intros Hvalx Hlenout Hsepx Hsepout.
    pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
    set (fx := exist _ wsx Hlenx : felem).
    set (fout := exist _ old_out Hlenout : felem).
    seprewrite_in (Bignum_to_FElem px wsx Hlenx) Hsepx.
    seprewrite_in (Bignum_to_FElem pout old_out Hlenout) Hsepout.
    seprewrite_in (felem_to_bytes pout fout) Hsepout.
    unfold spec_of_UnOp in Hfelem.
    set (out_bs := ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list fout)).
    specialize (Hfelem pout px fx out_bs Rout tr m0).
    cbv [un_square un_xbounds un_outbounds un_model] in Hfelem.
    assert (Hcall : call functions square tr m0 [pout; px]
      (fun (tr' : trace) (mem' : map.rep) (rets : list word.rep) =>
         rets = [] /\ tr = tr' /\
         (exists out0 : felem,
            feval (felem_to_list out0) =
            F.pow (feval (felem_to_list fx)) 2 /\
            bounded_by tight_bounds (felem_to_list out0) /\
            (FElem pout out0 * Rout)%sep mem'))).
    { apply Hfelem.
      refine (conj (loose_of_valid _ Hvalx) (conj _ (conj _ _))).
      - exact (ws2bs_felem_length fout).
      - exists Rx. exact Hsepx.
      - exact Hsepout. }
    eapply Proper_call; [ | exact Hcall].
    clear Hcall Hfelem Hsepx Hsepout.
    intros tr' m' rets (Hrets & Htr & out0 & Hfeval_out & Hbd_out & Hsep_out).
    split; [exact Htr|]. split; [exact Hrets|].
    exists (felem_to_list out0).
    split; [exact (proj2_sig out0)|].
    split; [exact (valid_of_tight _ Hbd_out)|].
    split.
    - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
      change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
      exact Hsep_out.
    - change (felem_to_list fx) with wsx in Hfeval_out.
      apply (feval_square_bridge _ _ Hfeval_out).
  Qed.

  (** ** opp *)

  Lemma opp_bignum_transport functions :
    spec_of_UnOp un_opp (field_representation:=field_representation) functions ->
    unop_opp_body functions.
  Proof.
    intros Hfelem.
    intros wsx old_out px pout tr m0 Rx Rout.
    intros Hvalx Hlenout Hsepx Hsepout.
    pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
    set (fx := exist _ wsx Hlenx : felem).
    set (fout := exist _ old_out Hlenout : felem).
    seprewrite_in (Bignum_to_FElem px wsx Hlenx) Hsepx.
    seprewrite_in (Bignum_to_FElem pout old_out Hlenout) Hsepout.
    seprewrite_in (felem_to_bytes pout fout) Hsepout.
    unfold spec_of_UnOp in Hfelem.
    set (out_bs := ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list fout)).
    specialize (Hfelem pout px fx out_bs Rout tr m0).
    cbv [un_opp un_xbounds un_outbounds un_model] in Hfelem.
    assert (Hcall : call functions opp tr m0 [pout; px]
      (fun (tr' : trace) (mem' : map.rep) (rets : list word.rep) =>
         rets = [] /\ tr = tr' /\
         (exists out0 : felem,
            feval (felem_to_list out0) =
            F.opp (feval (felem_to_list fx)) /\
            bounded_by loose_bounds (felem_to_list out0) /\
            (FElem pout out0 * Rout)%sep mem'))).
    { apply Hfelem.
      refine (conj (tight_of_valid _ Hvalx) (conj _ (conj _ _))).
      - exact (ws2bs_felem_length fout).
      - exists Rx. exact Hsepx.
      - exact Hsepout. }
    eapply Proper_call; [ | exact Hcall].
    clear Hcall Hfelem Hsepx Hsepout.
    intros tr' m' rets (Hrets & Htr & out0 & Hfeval_out & Hbd_out & Hsep_out).
    split; [exact Htr|]. split; [exact Hrets|].
    exists (felem_to_list out0).
    split; [exact (proj2_sig out0)|].
    split; [exact (valid_of_loose _ Hbd_out)|].
    split.
    - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
      change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
      exact Hsep_out.
    - change (felem_to_list fx) with wsx in Hfeval_out.
      apply (feval_opp_bridge _ _ Hfeval_out).
  Qed.

End Transports.
