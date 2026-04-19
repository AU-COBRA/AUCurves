(** Wired Bignum-style spec instances for Vesta field operations.

    Vesta analogue of [Secp256k1_Wired_Specs.v]. Uses the
    [vesta_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.vesta_prime] and exposes
    the synthesized [vesta_mul], [vesta_add], etc. as Bignum-style
    [spec_of] instances for AUCurves callers. *)

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
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.vesta_prime.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.
Require Import Bedrock.Curve.VestaCurve_G1_BignumSpecs.

Import ListNotations.
Local Open Scope Z_scope.

Existing Instance vesta_prime.vesta_field_parameters.
Existing Instance vesta_prime.vesta_frep.
Existing Instance vesta_prime.vesta_frep_ok.

Local Notation m := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001%Z.
Local Notation n := 4%nat.
Local Notation bw := 64%Z.
Local Notation vesta_m' := (@Field.m' bw vesta_field_parameters).
Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m vesta_m').
Local Notation toZ := (List.map Interface.word.unsigned).

(** ** Concrete spec_of instances — use shared predicate bodies from
    [WbwMontgomeryG1_BignumSpecBodies]. *)

Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecBodies.

Instance spec_of_vesta_mul_bignum    : spec_of "vesta_coord_mul"    := binop_mul_body.
Instance spec_of_vesta_add_bignum    : spec_of "vesta_coord_add"    := binop_add_body.
Instance spec_of_vesta_sub_bignum    : spec_of "vesta_coord_sub"    := binop_sub_body.
Instance spec_of_vesta_square_bignum : spec_of "vesta_coord_square" := unop_square_body.
Instance spec_of_vesta_opp_bignum    : spec_of "vesta_coord_opp"    := unop_opp_body.

(** ** Bridge lemmas — use shared WbwMontgomeryG1_WiredBridges functor.
    Replaces ~80 LoC of identical-per-curve bridge lemmas with a functor
    application. *)

Require Import Bedrock.Curve.WbwMontgomeryG1_WiredBridges.

Local Lemma feval_wbw_def :
  forall ws, feval ws = F.of_Z M_pos (eval (from_mont (toZ ws))).
Proof. reflexivity. Qed.

Local Definition feval_toZ         := feval_toZ         feval_wbw_def.
Local Definition feval_mul_bridge  := feval_mul_bridge  feval_wbw_def.
Local Definition feval_add_bridge  := feval_add_bridge  feval_wbw_def.
Local Definition feval_sub_bridge  := feval_sub_bridge  feval_wbw_def.
Local Definition feval_square_bridge := feval_square_bridge feval_wbw_def.
Local Definition feval_opp_bridge  := feval_opp_bridge  feval_wbw_def.
(* [Z_opp_mod] is now available unqualified from the functor import. *)

(** ** Transport lemmas -- proved via FElem bridge *)

Lemma vesta_mul_bignum_correct :
  forall functions,
    spec_of_BinOp bin_mul (field_representation:=vesta_frep) functions ->
    spec_of_vesta_mul_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx wsy old_out px py pout tr m0 Rx Ry Rout.
  intros Hvalx Hvaly Hlenout Hsepx Hsepy Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  pose proof (Bignum_length _ _ _ _ _ Hsepy) as Hleny.
  change 4%nat with felem_size_in_words in Hlenout, Hlenx, Hleny, Hsepx, Hsepy, Hsepout.
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
    by (apply relax_bounds; exact Hvalx).
  assert (Hbdy : bounded_by loose_bounds (felem_to_list fy))
    by (apply relax_bounds; exact Hvaly).
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
  split; [exact Hbd_out|].
  split.
  - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
    change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
    exact Hsep_out.
  - apply (f_equal F.to_Z) in Hfeval_out.
    rewrite F.to_Z_mul in Hfeval_out.
    change (felem_to_list fx) with wsx in Hfeval_out.
    change (felem_to_list fy) with wsy in Hfeval_out.
    rewrite !feval_toZ in Hfeval_out.
    change (Z.pos M_pos) with m in Hfeval_out.
    rewrite Z.mul_mod_idemp_r in Hfeval_out by discriminate.
    rewrite Zmod_mod.
    exact Hfeval_out.
Qed.

Lemma vesta_add_bignum_correct :
  forall functions,
    spec_of_BinOp bin_add (field_representation:=vesta_frep) functions ->
    spec_of_vesta_add_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx wsy old_out px py pout tr m0 Rx Ry Rout.
  intros Hvalx Hvaly Hlenout Hsepx Hsepy Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  pose proof (Bignum_length _ _ _ _ _ Hsepy) as Hleny.
  change 4%nat with felem_size_in_words in Hlenout, Hlenx, Hleny, Hsepx, Hsepy, Hsepout.
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
    refine (conj Hvalx (conj Hvaly (conj _ (conj _ (conj _ _))))).
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
  split; [exact Hbd_out|].
  split.
  - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
    change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
    exact Hsep_out.
  - apply (f_equal F.to_Z) in Hfeval_out.
    rewrite F.to_Z_add in Hfeval_out.
    change (felem_to_list fx) with wsx in Hfeval_out.
    change (felem_to_list fy) with wsy in Hfeval_out.
    rewrite !feval_toZ in Hfeval_out.
    change (Z.pos M_pos) with m in Hfeval_out.
    exact Hfeval_out.
Qed.

Lemma vesta_sub_bignum_correct :
  forall functions,
    spec_of_BinOp bin_sub (field_representation:=vesta_frep) functions ->
    spec_of_vesta_sub_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx wsy old_out px py pout tr m0 Rx Ry Rout.
  intros Hvalx Hvaly Hlenout Hsepx Hsepy Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  pose proof (Bignum_length _ _ _ _ _ Hsepy) as Hleny.
  change 4%nat with felem_size_in_words in Hlenout, Hlenx, Hleny, Hsepx, Hsepy, Hsepout.
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
    refine (conj Hvalx (conj Hvaly (conj _ (conj _ (conj _ _))))).
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
  split; [exact Hbd_out|].
  split.
  - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
    change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
    exact Hsep_out.
  - change (felem_to_list fx) with wsx in Hfeval_out.
    change (felem_to_list fy) with wsy in Hfeval_out.
    apply (feval_sub_bridge _ _ _ Hfeval_out).
Qed.

Lemma vesta_square_bignum_correct :
  forall functions,
    spec_of_UnOp un_square (field_representation:=vesta_frep) functions ->
    spec_of_vesta_square_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx old_out px pout tr m0 Rx Rout.
  intros Hvalx Hlenout Hsepx Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  change 4%nat with felem_size_in_words in Hlenout, Hlenx, Hsepx, Hsepout.
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
    refine (conj Hvalx (conj _ (conj _ _))).
    - exact (ws2bs_felem_length fout).
    - exists Rx. exact Hsepx.
    - exact Hsepout. }
  eapply Proper_call; [ | exact Hcall].
  clear Hcall Hfelem Hsepx Hsepout.
  intros tr' m' rets (Hrets & Htr & out0 & Hfeval_out & Hbd_out & Hsep_out).
  split; [exact Htr|]. split; [exact Hrets|].
  exists (felem_to_list out0).
  split; [exact (proj2_sig out0)|].
  split; [exact Hbd_out|].
  split.
  - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
    change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
    exact Hsep_out.
  - apply (f_equal F.to_Z) in Hfeval_out.
    rewrite F.to_Z_pow in Hfeval_out.
    change (felem_to_list fx) with wsx in Hfeval_out.
    rewrite !feval_toZ in Hfeval_out.
    simpl Z.of_N in Hfeval_out.
    rewrite Z.pow_2_r in Hfeval_out.
    change (Z.pos M_pos) with m in Hfeval_out.
    exact Hfeval_out.
Qed.

Lemma vesta_opp_bignum_correct :
  forall functions,
    spec_of_UnOp un_opp (field_representation:=vesta_frep) functions ->
    spec_of_vesta_opp_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx old_out px pout tr m0 Rx Rout.
  intros Hvalx Hlenout Hsepx Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  change 4%nat with felem_size_in_words in Hlenout, Hlenx, Hsepx, Hsepout.
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
    refine (conj Hvalx (conj _ (conj _ _))).
    - exact (ws2bs_felem_length fout).
    - exists Rx. exact Hsepx.
    - exact Hsepout. }
  eapply Proper_call; [ | exact Hcall].
  clear Hcall Hfelem Hsepx Hsepout.
  intros tr' m' rets (Hrets & Htr & out0 & Hfeval_out & Hbd_out & Hsep_out).
  split; [exact Htr|]. split; [exact Hrets|].
  exists (felem_to_list out0).
  split; [exact (proj2_sig out0)|].
  split; [exact Hbd_out|].
  split.
  - seprewrite_in (FElem_iff_Bignum pout out0) Hsep_out.
    change (proj1_sig out0) with (felem_to_list out0) in Hsep_out.
    exact Hsep_out.
  - apply (f_equal F.to_Z) in Hfeval_out.
    rewrite F.to_Z_opp in Hfeval_out.
    change (felem_to_list fx) with wsx in Hfeval_out.
    rewrite !feval_toZ in Hfeval_out.
    change (Z.pos M_pos) with m in Hfeval_out.
    (* H: -(a mod m) mod m; goal: (-a) mod m mod m *)
    rewrite Z_opp_mod in Hfeval_out. rewrite Zmod_mod. exact Hfeval_out.
Qed.
