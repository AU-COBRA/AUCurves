(** Wired Bignum-style spec instances for BN254 field operations.

    BN254 analogue of [Secbn254k1_Wired_Specs.v]. Uses the
    [bn254_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.bn254_prime] and exposes
    the synthesized [bn254_mul], [bn254_add], etc. as Bignum-style
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
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.
Require Import Bedrock.Curve.BN254Curve_G1_BignumSpecs.

Import ListNotations.
Local Open Scope Z_scope.

Existing Instance bn254_prime.bn254_field_parameters.
Existing Instance bn254_prime.bn254_frep.
Existing Instance bn254_prime.bn254_frep_ok.

Local Notation m := 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47%Z.
Local Notation n := 4%nat.
Local Notation bw := 64%Z.
Local Notation bn254_m' := (@Field.m' bw bn254_field_parameters).
Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m bn254_m').
Local Notation toZ := (List.map Interface.word.unsigned).

(** ** Concrete spec_of instances *)

Instance spec_of_bn254_mul_bignum : spec_of "bn254_coord_mul" :=
  fun functions =>
    forall (wsx wsy old_out : list word.rep)
           (px py pout : word.rep)
           (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
           (Rx Ry Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
      WordByWordMontgomery.valid bw n m (toZ wsx) ->
      WordByWordMontgomery.valid bw n m (toZ wsy) ->
      Datatypes.length old_out = n ->
      (Bignum n px wsx * Rx)%sep mem0 ->
      (Bignum n py wsy * Ry)%sep mem0 ->
      (Bignum n pout old_out * Rout)%sep mem0 ->
      call functions Field.mul tr mem0
        [pout; px; py]
        (fun tr' mem' rets =>
           tr = tr' /\ rets = nil /\
           exists wsout : list word.rep,
             Datatypes.length wsout = n /\
             WordByWordMontgomery.valid bw n m (toZ wsout) /\
             (Bignum n pout wsout * Rout)%sep mem' /\
             (eval (from_mont (toZ wsout))) mod m =
             ((eval (from_mont (toZ wsx))) mod m *
              (eval (from_mont (toZ wsy))) mod m) mod m).

Instance spec_of_bn254_add_bignum : spec_of "bn254_coord_add" :=
  fun functions =>
    forall (wsx wsy old_out : list word.rep)
           (px py pout : word.rep)
           (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
           (Rx Ry Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
      WordByWordMontgomery.valid bw n m (toZ wsx) ->
      WordByWordMontgomery.valid bw n m (toZ wsy) ->
      Datatypes.length old_out = n ->
      (Bignum n px wsx * Rx)%sep mem0 ->
      (Bignum n py wsy * Ry)%sep mem0 ->
      (Bignum n pout old_out * Rout)%sep mem0 ->
      call functions Field.add tr mem0
        [pout; px; py]
        (fun tr' mem' rets =>
           tr = tr' /\ rets = nil /\
           exists wsout : list word.rep,
             Datatypes.length wsout = n /\
             WordByWordMontgomery.valid bw n m (toZ wsout) /\
             (Bignum n pout wsout * Rout)%sep mem' /\
             (eval (from_mont (toZ wsout))) mod m =
             ((eval (from_mont (toZ wsx))) mod m +
              (eval (from_mont (toZ wsy))) mod m) mod m).

Instance spec_of_bn254_sub_bignum : spec_of "bn254_coord_sub" :=
  fun functions =>
    forall (wsx wsy old_out : list word.rep)
           (px py pout : word.rep)
           (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
           (Rx Ry Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
      WordByWordMontgomery.valid bw n m (toZ wsx) ->
      WordByWordMontgomery.valid bw n m (toZ wsy) ->
      Datatypes.length old_out = n ->
      (Bignum n px wsx * Rx)%sep mem0 ->
      (Bignum n py wsy * Ry)%sep mem0 ->
      (Bignum n pout old_out * Rout)%sep mem0 ->
      call functions Field.sub tr mem0
        [pout; px; py]
        (fun tr' mem' rets =>
           tr = tr' /\ rets = nil /\
           exists wsout : list word.rep,
             Datatypes.length wsout = n /\
             WordByWordMontgomery.valid bw n m (toZ wsout) /\
             (Bignum n pout wsout * Rout)%sep mem' /\
             (eval (from_mont (toZ wsout))) mod m =
             ((eval (from_mont (toZ wsx))) mod m -
              (eval (from_mont (toZ wsy))) mod m) mod m).

Instance spec_of_bn254_square_bignum : spec_of "bn254_coord_square" :=
  fun functions =>
    forall (wsx old_out : list word.rep)
           (px pout : word.rep)
           (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
           (Rx Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
      WordByWordMontgomery.valid bw n m (toZ wsx) ->
      Datatypes.length old_out = n ->
      (Bignum n px wsx * Rx)%sep mem0 ->
      (Bignum n pout old_out * Rout)%sep mem0 ->
      call functions Field.square tr mem0
        [pout; px]
        (fun tr' mem' rets =>
           tr = tr' /\ rets = nil /\
           exists wsout : list word.rep,
             Datatypes.length wsout = n /\
             WordByWordMontgomery.valid bw n m (toZ wsout) /\
             (Bignum n pout wsout * Rout)%sep mem' /\
             (eval (from_mont (toZ wsout))) mod m =
             (((eval (from_mont (toZ wsx))) mod m) *
              ((eval (from_mont (toZ wsx))) mod m)) mod m).

Instance spec_of_bn254_opp_bignum : spec_of "bn254_coord_opp" :=
  fun functions =>
    forall (wsx old_out : list word.rep)
           (px pout : word.rep)
           (tr : trace) (mem0 : @map.rep _ _ BasicC64Semantics.mem)
           (Rx Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
      WordByWordMontgomery.valid bw n m (toZ wsx) ->
      Datatypes.length old_out = n ->
      (Bignum n px wsx * Rx)%sep mem0 ->
      (Bignum n pout old_out * Rout)%sep mem0 ->
      call functions Field.opp tr mem0
        [pout; px]
        (fun tr' mem' rets =>
           tr = tr' /\ rets = nil /\
           exists wsout : list word.rep,
             Datatypes.length wsout = n /\
             WordByWordMontgomery.valid bw n m (toZ wsout) /\
             (Bignum n pout wsout * Rout)%sep mem' /\
             (eval (from_mont (toZ wsout))) mod m =
             (- (eval (from_mont (toZ wsx))) mod m) mod m).

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

Lemma bn254_mul_bignum_correct :
  forall functions,
    spec_of_BinOp bin_mul (field_representation:=bn254_frep) functions ->
    spec_of_bn254_mul_bignum functions.
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

Lemma bn254_add_bignum_correct :
  forall functions,
    spec_of_BinOp bin_add (field_representation:=bn254_frep) functions ->
    spec_of_bn254_add_bignum functions.
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

Lemma bn254_sub_bignum_correct :
  forall functions,
    spec_of_BinOp bin_sub (field_representation:=bn254_frep) functions ->
    spec_of_bn254_sub_bignum functions.
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

Lemma bn254_square_bignum_correct :
  forall functions,
    spec_of_UnOp un_square (field_representation:=bn254_frep) functions ->
    spec_of_bn254_square_bignum functions.
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

Lemma bn254_opp_bignum_correct :
  forall functions,
    spec_of_UnOp un_opp (field_representation:=bn254_frep) functions ->
    spec_of_bn254_opp_bignum functions.
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
