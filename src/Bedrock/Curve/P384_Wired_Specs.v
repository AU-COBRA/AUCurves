(** Wired Bignum-style spec instances for P-384 field operations.

    P-384 analogue of [P256_Wired_Specs.v]. Uses the
    [p384_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.p384_field] and exposes
    the synthesized [p384_coord_mul], [p384_coord_add], etc. as
    Bignum-style [spec_of] instances for AUCurves callers. *)

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
Require Import Bedrock.Field.Synthesis.Examples.p384_field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.
Require Import Bedrock.Curve.P384_Bignum_Specs.

Import ListNotations.
Local Open Scope Z_scope.

Existing Instance p384_field.p384_field_parameters.
Existing Instance p384_field.p384_frep.
Existing Instance p384_field.p384_frep_ok.

Local Notation m := (2^384 - 2^128 - 2^96 + 2^32 - 1)%Z.
Local Notation n := 6%nat.
Local Notation bw := 64%Z.
Local Notation p384_m' := (@Field.m' bw p384_field_parameters).
Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m p384_m').
Local Notation toZ := (List.map Interface.word.unsigned).

(** Sanity checks: the Montgomery constants used downstream.
    m' = -m^-1 mod 2^64 = 2^32 + 1; r' = (2^64)^-1 mod m. *)
Lemma p384_m'_sanity : (m * 4294967297) mod 2^64 = (-1) mod 2^64.
Proof. vm_compute. reflexivity. Qed.

Lemma p384_r'_sanity :
  (2^64 * 9173994466096273082364193663603369469355812071275829017307008127494733112176079729898163604637719575134209) mod m = 1.
Proof. vm_compute. reflexivity. Qed.

(** ** Concrete spec_of instances *)

Instance spec_of_p384_mul_bignum : spec_of "p384_coord_mul" :=
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

Instance spec_of_p384_add_bignum : spec_of "p384_coord_add" :=
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

Instance spec_of_p384_sub_bignum : spec_of "p384_coord_sub" :=
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

Instance spec_of_p384_square_bignum : spec_of "p384_coord_square" :=
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

Instance spec_of_p384_opp_bignum : spec_of "p384_coord_opp" :=
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

(** ** Helper: feval -> eval/from_mont/mod m bridge *)

(** For the WBW Montgomery representation, [feval ws] is definitionally
    [F.of_Z M_pos (eval (from_mont (toZ ws)))]. Therefore
    [F.to_Z (feval ws) = eval (from_mont (toZ ws)) mod m]. *)
Local Lemma feval_toZ (ws : list word.rep) :
  F.to_Z (feval ws) = eval (from_mont (toZ ws)) mod m.
Proof.
  change (feval ws) with (F.of_Z M_pos (eval (from_mont (toZ ws)))).
  rewrite F.to_Z_of_Z. unfold M. reflexivity.
Qed.

(** Bridge lemmas: from [feval out = F.op ...] to the [eval/from_mont mod m]
    form used in the Bignum-style specs. *)

Local Lemma feval_mul_bridge (wout wx wy : list word.rep) :
  feval wout = F.mul (feval wx) (feval wy) ->
  eval (from_mont (toZ wout)) mod m =
  ((eval (from_mont (toZ wx))) mod m *
   (eval (from_mont (toZ wy))) mod m) mod m.
Proof.
  intros H. apply (f_equal F.to_Z) in H.
  rewrite F.to_Z_mul in H. rewrite !feval_toZ in H.
  change (Z.pos M_pos) with m in H.
  rewrite Z.mul_mod_idemp_r in H by discriminate.
  rewrite Zmod_mod. exact H.
Qed.

Local Lemma feval_add_bridge (wout wx wy : list word.rep) :
  feval wout = F.add (feval wx) (feval wy) ->
  eval (from_mont (toZ wout)) mod m =
  ((eval (from_mont (toZ wx))) mod m +
   (eval (from_mont (toZ wy))) mod m) mod m.
Proof.
  intros H. apply (f_equal F.to_Z) in H.
  rewrite F.to_Z_add in H. rewrite !feval_toZ in H.
  change (Z.pos M_pos) with m in H. exact H.
Qed.

Local Lemma feval_sub_bridge (wout wx wy : list word.rep) :
  feval wout = F.sub (feval wx) (feval wy) ->
  eval (from_mont (toZ wout)) mod m =
  ((eval (from_mont (toZ wx))) mod m -
   (eval (from_mont (toZ wy))) mod m) mod m.
Proof.
  intros H. apply (f_equal F.to_Z) in H.
  cbv [F.sub] in H.
  rewrite F.to_Z_add, F.to_Z_opp in H. rewrite !feval_toZ in H.
  change (Z.pos M_pos) with m in H.
  rewrite Zdiv.Zplus_mod_idemp_r in H. exact H.
Qed.

Local Lemma feval_square_bridge (wout wx : list word.rep) :
  feval wout = F.pow (feval wx) 2 ->
  eval (from_mont (toZ wout)) mod m =
  ((eval (from_mont (toZ wx))) mod m *
   (eval (from_mont (toZ wx))) mod m) mod m.
Proof.
  intros H. apply (f_equal F.to_Z) in H.
  rewrite F.to_Z_pow in H. simpl Z.of_N in H.
  rewrite Z.pow_2_r in H. rewrite !feval_toZ in H.
  change (Z.pos M_pos) with m in H.
  rewrite Z.mul_mod_idemp_r in H by discriminate.
  rewrite Zmod_mod. exact H.
Qed.

Local Lemma Z_opp_mod (a n : Z) : (- (a mod n)) mod n = (- a) mod n.
Proof.
  replace (- (a mod n)) with (0 - (a mod n)) by lia.
  replace (- a) with (0 - a) by lia.
  apply Zminus_mod_idemp_r.
Qed.

Local Lemma feval_opp_bridge (wout wx : list word.rep) :
  feval wout = F.opp (feval wx) ->
  eval (from_mont (toZ wout)) mod m =
  (- (eval (from_mont (toZ wx))) mod m) mod m.
Proof.
  intros H. apply (f_equal F.to_Z) in H.
  rewrite F.to_Z_opp in H. rewrite !feval_toZ in H.
  change (Z.pos M_pos) with m in H.
  rewrite Z_opp_mod in H. rewrite Zmod_mod. exact H.
Qed.

(** ** Transport lemmas -- proved via FElem bridge *)

Lemma p384_mul_bignum_correct :
  forall functions,
    spec_of_BinOp bin_mul (field_representation:=p384_frep) functions ->
    spec_of_p384_mul_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx wsy old_out px py pout tr m0 Rx Ry Rout.
  intros Hvalx Hvaly Hlenout Hsepx Hsepy Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  pose proof (Bignum_length _ _ _ _ _ Hsepy) as Hleny.
  change 6%nat with felem_size_in_words in Hlenout, Hlenx, Hleny, Hsepx, Hsepy, Hsepout.
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

Lemma p384_add_bignum_correct :
  forall functions,
    spec_of_BinOp bin_add (field_representation:=p384_frep) functions ->
    spec_of_p384_add_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx wsy old_out px py pout tr m0 Rx Ry Rout.
  intros Hvalx Hvaly Hlenout Hsepx Hsepy Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  pose proof (Bignum_length _ _ _ _ _ Hsepy) as Hleny.
  change 6%nat with felem_size_in_words in Hlenout, Hlenx, Hleny, Hsepx, Hsepy, Hsepout.
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

Lemma p384_sub_bignum_correct :
  forall functions,
    spec_of_BinOp bin_sub (field_representation:=p384_frep) functions ->
    spec_of_p384_sub_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx wsy old_out px py pout tr m0 Rx Ry Rout.
  intros Hvalx Hvaly Hlenout Hsepx Hsepy Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  pose proof (Bignum_length _ _ _ _ _ Hsepy) as Hleny.
  change 6%nat with felem_size_in_words in Hlenout, Hlenx, Hleny, Hsepx, Hsepy, Hsepout.
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

Lemma p384_square_bignum_correct :
  forall functions,
    spec_of_UnOp un_square (field_representation:=p384_frep) functions ->
    spec_of_p384_square_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx old_out px pout tr m0 Rx Rout.
  intros Hvalx Hlenout Hsepx Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  change 6%nat with felem_size_in_words in Hlenout, Hlenx, Hsepx, Hsepout.
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

Lemma p384_opp_bignum_correct :
  forall functions,
    spec_of_UnOp un_opp (field_representation:=p384_frep) functions ->
    spec_of_p384_opp_bignum functions.
Proof.
  intros functions Hfelem.
  intros wsx old_out px pout tr m0 Rx Rout.
  intros Hvalx Hlenout Hsepx Hsepout.
  pose proof (Bignum_length _ _ _ _ _ Hsepx) as Hlenx.
  change 6%nat with felem_size_in_words in Hlenout, Hlenx, Hsepx, Hsepout.
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
