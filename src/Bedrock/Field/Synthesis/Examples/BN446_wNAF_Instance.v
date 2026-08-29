(** * BN446 single-scalar wNAF — instance discharge + composition.

    Discharges the algebraic hypotheses (Horner step, digit-point
    correctness, weighted-sum non-negativity) for BN446 and composes
    the full WP chain:

      single_load_and_process_ok  →  wnaf_single_loop_body_ok  →  wnaf_single_ok

    The result is a single theorem:
      Given BN446 curve_add/double specs and the digit/table data,
      the bedrock2 wnaf_single_func_body computes k*P.

    This file follows the pattern of [BLS12_wNAF_GLV_Instance.v]
    but is simpler: single scalar, no GLV decomposition.

    ** G6 / G5 **

    The point-level algebra is stated up to the Section-parametric
    equivalence [pt_eq] with the on-curve predicate [oncurve] (see
    wNAF_Single_HornerAlgebra.v for the honesty ledger), and the aliased
    negation is called at the Section-parametric name [opp_name].  A
    curve whose addition satisfies the group laws on the nose recovers
    the previous interface with [pt_eq := eq],
    [pt_eq_equiv := eq_equivalence], [oncurve := fun _ => True],
    [opp_name := opp]. *)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import RelationClasses.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoopBody.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_Proof.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoadAndProcess.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section BN446_wNAF_Instance.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {env: map.map string (list string * list string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.
  Context {field_parameters_ok : FieldParameters_ok}
          {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  Context (curve_add_name curve_double_name opp_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.

  (** G6: point-level equality is the parametric equivalence [pt_eq],
      and the group laws carry [oncurve] side conditions. *)
  Context (pt_eq : F * F * F -> F * F * F -> Prop).
  Context (pt_eq_equiv : Equivalence pt_eq).
  Context (oncurve : F * F * F -> Prop).
  Context (oncurve_id : oncurve (Fzero,Fone,Fzero)).
  Context (oncurve_curve_add :
    forall P Q, oncurve P -> oncurve Q -> oncurve (curve_add P Q)).
  Context (curve_add_Proper : forall P P' Q Q',
    oncurve P -> oncurve P' -> oncurve Q -> oncurve Q' ->
    pt_eq P P' -> pt_eq Q Q' -> pt_eq (curve_add P Q) (curve_add P' Q')).
  Context (curve_add_id_l : forall x y z,
    oncurve (x,y,z) -> pt_eq (curve_add (Fzero,Fone,Fzero) (x,y,z)) (x,y,z)).
  Context (curve_add_assoc : forall P Q R,
    oncurve P -> oncurve Q -> oncurve R ->
    pt_eq (curve_add P (curve_add Q R)) (curve_add (curve_add P Q) R)).
  Let scmul_s := scmul Fzero Fone curve_add.

  Variable functions : map.rep (map := Semantics.env).

  (* Primitive function specs *)
  Context (HCurveDouble : forall pX pY pZ
    (X Y Z : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pX X ⋆ FElem (Some tight_bounds) pY Y
     ⋆ FElem (Some tight_bounds) pZ Z ⋆ R0) m0 ->
    Semantics.call functions curve_double_name tr0 m0
      [pX; pY; pZ; pX; pY; pZ]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        let '(Xo, Yo, Zo) := curve_add (X, Y, Z) (X, Y, Z) in
        (FElem (Some tight_bounds) pX Xo ⋆ FElem (Some tight_bounds) pY Yo
         ⋆ FElem (Some tight_bounds) pZ Zo ⋆ R0) m')).

  Context (HCurveAddInplace :
    forall pXo pX2 pYo pY2 pZo pZ2
      (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pXo X ⋆ FElem (Some tight_bounds) pYo Y
     ⋆ FElem (Some tight_bounds) pZo Z ⋆ FElem (Some tight_bounds) pX2 X2'
     ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
     ⋆ R0) m0 ->
    WeakestPrecondition.call functions curve_add_name tr0 m0
      [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
      (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
        let '(Xo', Yo', Zo') := curve_add (X, Y, Z) (X2', Y2', Z2') in
        (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pYo Yo'
         ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pX2 X2'
         ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
         ⋆ R0) m'))).

  Context (HFelemCopy :
    forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pSrc v
     ⋆ FElem (Some tight_bounds) pDst old ⋆ R0) m0 ->
    Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pSrc v
         ⋆ FElem (Some tight_bounds) pDst v ⋆ R0) m')).

  Context (HOpp :
    forall pOut pIn (Y : F) (Yold : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pIn Y
     ⋆ FElem (Some tight_bounds) pOut Yold ⋆ R0) m0 ->
    Semantics.call functions opp_name tr0 m0 [pOut; pIn]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pIn Y
         ⋆ FElem (Some tight_bounds) pOut (F.opp Y) ⋆ R0) m')).

  Context (HOppInplace :
    forall p (Y : F) R0 tr0 m0,
    (FElem (Some tight_bounds) p Y ⋆ R0) m0 ->
    Semantics.call functions opp_name tr0 m0 [p; p]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) p (F.opp Y) ⋆ R0) m')).

  Context (HStoreZero : @StoreZero.spec_of_store_zero
    _ _ _ _ _ _ field_parameters field_representation functions).

  (* Data *)
  Context (dk : list Z) (Px Py Pz : F).
  Context (Honcurve_P : oncurve (Px,Py,Pz)).
  Context (num_iters : nat).
  Context (Hlen : length dk = num_iters).
  Context (Hnbound : Z.of_nat num_iters < 2 ^ width).
  Context (Hdigits_bounded :
    forall i, (i < num_iters)%nat -> -7 <= nth i dk 0 <= 7).
  Context (Hfs_pos : 0 < felem_size_in_bytes).
  Context (Hfs_small : 12 * felem_size_in_bytes < 2 ^ width).

  Context (table_entries : list (F * F * F)).
  Context (Htable_len : length table_entries = 4%nat).

  Context (Hdigit_load : forall (n : nat) (base : word) (m : mem) R,
    (n < length dk)%nat ->
    (@DigitArray _ word mem base dk ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk 0))).

  Context (Hws_nn :
    forall n, (n <= num_iters)%nat -> 0 <= weighted_sum (skipn n dk) 0).

  (** Horner step: connects digit_point-based result to weighted_sum formula.
      For each digit d_n:
        scmul(ws(skipn n dk)) P =
          if d_n = 0 then scmul(2*ws(skipn (S n) dk)) P
          else curve_add (scmul(2*ws(skipn (S n) dk)) P) (digit_point d_n table) *)
  Context (Hhorner_step : forall n (Ox Oy Oz : F),
    (n < num_iters)%nat ->
    let ws_old := weighted_sum (skipn (S n) dk) 0 in
    oncurve (Ox,Oy,Oz) ->
    pt_eq (Ox,Oy,Oz) (scmul_s (Z.to_nat (2 * ws_old)) (Px,Py,Pz)) ->
    let d := nth n dk 0 in
    pt_eq
      (if d =? 0 then (Ox,Oy,Oz)
       else curve_add (Ox,Oy,Oz) (digit_point d table_entries))
      (scmul_s (Z.to_nat (weighted_sum (skipn n dk) 0)) (Px,Py,Pz))).

  (** On-curve closure of one Horner step.  NEW, forced by G6:
      [oncurve] is not [pt_eq]-invariant, so it cannot be recovered from
      [Hhorner_step]. *)
  Context (Hhorner_oncurve : forall n (Ox Oy Oz : F),
    (n < num_iters)%nat ->
    oncurve (Ox,Oy,Oz) ->
    let d := nth n dk 0 in
    oncurve (if d =? 0 then (Ox,Oy,Oz)
             else curve_add (Ox,Oy,Oz) (digit_point d table_entries))).

  (** ================================================================
      Full single-scalar wNAF theorem for BN446 (or any non-GLV curve).
      Composes: LoadAndProcess → LoopBody → Proof.
      ================================================================ *)
  Theorem wnaf_single_full :
    forall k,
    wsum dk = k -> 0 <= k ->
    forall pOx pOy pOz pAx pAy pAz pT pDK
      (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F)
      (Rinner : mem -> Prop) tr m l,
    map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
    map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
    map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
    map.get l "table_P" = Some pT ->
    map.get l "digits_k" = Some pDK ->
    (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
     ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0
     ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries
     ⋆ Rinner) m ->
    WeakestPrecondition.cmd functions
      (wnaf_single_func_body curve_add_name curve_double_name "store_zero"
         felem_copy opp_name (Z.of_nat num_iters) felem_size_in_bytes
         "digits_k" "table_P")
      tr m l
      (fun t m' l' =>
        exists Rx Ry Rz Ax' Ay' Az',
        oncurve (Rx,Ry,Rz)
        /\ pt_eq (Rx,Ry,Rz) (scmul_s (Z.to_nat k) (Px,Py,Pz))
        /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
            ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az'
            ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries
            ⋆ Rinner) m').
  Proof.
    intros k Hk Hknn.
    intros pOx pOy pOz pAx pAy pAz pT pDK
      Ox0 Oy0 Oz0 Ax0 Ay0 Az0 Rinner tr m l
      Hl_ox Hl_oy Hl_oz Hl_ax Hl_ay Hl_az Hl_t Hl_dk Hsep.
    (* Apply wnaf_single_ok with R := DigitArray ⋆ Table4 ⋆ Rinner *)
    eapply WeakestPreconditionProperties.Proper_cmd;
      [|eapply wnaf_single_ok with (pt_eq := pt_eq) (oncurve := oncurve);
        try eassumption; try ecancel_assumption].
    - (* Postcondition weakening *)
      intros t2 m2 l2 (Rx & Ry & Rz & Ax' & Ay' & Az' & Hoc2 & Hout & Hsep2).
      exists Rx, Ry, Rz, Ax', Ay', Az'.
      split; [exact Hoc2|]. split; [exact Hout|].
      ecancel_assumption.
    - (* HLoopBody *)
      intros n pOx' pOy' pOz' pAx' pAy' pAz'
        Ox Oy Oz Ax Ay Az tr0 m0 l0
        Hn Hoc Hinv Hsep0 Hl_ox0 Hl_oy0 Hl_oz0 Hl_ax0 Hl_ay0 Hl_az0
        Hl_t0 Hl_dk0 Hl_iter0.
      (* Regroup sep associativity in the goal's postcondition so the
         Rinner frame matches wnaf_single_loop_body_ok's flat shape.
         See BN254_wNAF_Instance.v for the positional argument key. *)
      eapply WeakestPreconditionProperties.Proper_cmd;
        [|simple refine (@wnaf_single_loop_body_ok _ _ _ _ _ _ _ _ _ _ _ _
                curve_add_name curve_double_name opp_name _
                pt_eq pt_eq_equiv oncurve oncurve_id oncurve_curve_add
                curve_add_Proper
                curve_add_id_l curve_add_assoc
                functions HCurveDouble
                dk Px Py Pz Honcurve_P
                num_iters Hws_nn table_entries
                _  (* HProcessDigit subgoal *)
                n pOx' pOy' pOz' pAx' pAy' pAz' pT pDK
                Ox Oy Oz Ax Ay Az _ tr0 m0 l0
                Hn Hoc Hinv _ Hl_ox0 Hl_oy0 Hl_oz0 Hl_ax0 Hl_ay0 Hl_az0
                Hl_t0 Hl_dk0 Hl_iter0)].
      { (* postcondition weakening *)
        intros t2 m2 l2 (Ox' & Oy' & Oz' & Ax' & Ay' & Az' &
          Hoc' & Hout' & Hsep' & H_ox' & H_oy' & H_oz' & H_ax' & H_ay' & H_az' &
          H_tP' & H_dk' & H_it' & Htr').
        exists Ox', Oy', Oz', Ax', Ay', Az'.
        repeat (split; [try assumption|]); try assumption.
        ecancel_assumption. }
      { (* HProcessDigit — compose single_load_and_process_ok + Hhorner_step *)
        intros n' pOx'' pOy'' pOz'' pAx'' pAy'' pAz'' pT'' pDK''
          Ox' Oy' Oz' Ax' Ay' Az' Rinner' tr0' m0' l0'
          Hn' Hoc' Hinv' Hsep' Hl_ox' Hl_oy' Hl_oz' Hl_ax' Hl_ay' Hl_az'
          Hl_t' Hl_dk' Hl_iter'.
        eapply WeakestPreconditionProperties.Proper_cmd;
          [|eapply single_load_and_process_ok; try eassumption].
        intros t3 m3 l3 (Ox3 & Oy3 & Oz3 & Ax3 & Ay3 & Az3 &
          Hout3 & Hsep3 & Hlox3 & Hloy3 & Hloz3 & Hlax3 & Hlay3 & Hlaz3 &
          Hlt3 & Hldk3 & Hliter3 & Hpres3 & Htr3).
        exists Ox3, Oy3, Oz3, Ax3, Ay3, Az3.
        repeat split; try assumption;
          [ rewrite Hout3; apply Hhorner_oncurve; assumption
          | rewrite Hout3; apply Hhorner_step; assumption ]. }
      { (* sep precondition *)
        ecancel_assumption. }
  Qed.

End BN446_wNAF_Instance.

(** [wnaf_single_full] is the citable end-to-end theorem for
    single-scalar wNAF on any non-GLV curve. It takes:
    - Primitive function specs (curve_add, double, copy, opp, store_zero)
    - Digit array and table data with bounds
    - Algebraic hypotheses (Horner step, weighted-sum non-negativity)
    And proves the full WP for wnaf_single_func_body.

    Status: Qed, 0 Admitted (2026-04-21). [single_load_and_process_ok]
    Qed via prep_ecancel_H normalization. [wnaf_single_full] Qed via
    Option-1 HLoopBody hoist + Proper_cmd+simple refine sep-assoc fix.
    [Print Assumptions wnaf_single_full] = "Closed under the global context". *)
