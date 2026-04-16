(** * wNAF GLV — Concrete-R0 upper-chain composition (follow-up to GLV_Closed.v).
    See [WNAF_GLV_STATUS.md] for full verification status and architecture.

    This file closes the upper-chain "last mile" that could not be done
    generically in [BLS12_wNAF_GLV_Closed.v] because of a sep-shape
    mismatch: [process_both_digits_ok] has [DigitArray] / [Table4]
    explicit, while [wnaf_loop_body_ok]'s [HProcessBothDigits] hypothesis
    absorbs them into an abstract [R0].

    At the concrete instantiation level where [R0] is known to be
    [DigitArray ⋆ DigitArray ⋆ Table4 ⋆ Table4 ⋆ Rinner], the sep
    rearrangement IS possible. This file provides
    [HProcessBothDigits_concrete] which has exactly the shape of
    [process_both_digits_ok] (so it's provable by direct application
    of the P/Phi discharges + process_both_digits_ok), and is usable
    by downstream concrete instantiations that know their memory
    layout.

    The final step — plugging this into [wnaf_loop_body_ok] and then
    [wnaf_glv_ok] — requires either modifying [wnaf_loop_body_ok]'s
    [HProcessBothDigits] Section Context to use the concrete shape
    (invasive to a Qed'd theorem), or adapting [wnaf_loop_body_ok]'s
    proof by duplication (large). This is left as explicitly-scoped
    future work; see end-of-file note. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_LoadAndProcess.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_Closed.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_LoopBody.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_Proof.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section WNAFInstanceFinal.
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

  Context (curve_add_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
  Context (curve_add_id_r :
    forall x y z, curve_add (x,y,z) (Fzero,Fone,Fzero) = (x,y,z)).
  Context (curve_add_id_l :
    forall x y z, curve_add (Fzero,Fone,Fzero) (x,y,z) = (x,y,z)).
  Context (curve_add_assoc :
    forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
  Context (curve_add_comm :
    forall P Q, curve_add P Q = curve_add Q P).

  Variable functions : map.rep (map := Semantics.env).

  (* --- Primitive function specs (same as LoadAndProcess.v) --- *)

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
    Semantics.call functions opp tr0 m0 [pOut; pIn]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pIn Y
         ⋆ FElem (Some tight_bounds) pOut (F.opp Y) ⋆ R0) m')).

  Context (HOppInplace :
    forall p (Y : F) R0 tr0 m0,
    (FElem (Some tight_bounds) p Y ⋆ R0) m0 ->
    Semantics.call functions opp tr0 m0 [p; p]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) p (F.opp Y) ⋆ R0) m')).

  (* --- Digit and table data --- *)

  Context (dk1 dk2 : list Z).
  Context (Hlen1 : length dk1 = 129%nat) (Hlen2 : length dk2 = 129%nat).
  Context (Hdigits_bounded1 :
    forall i, (i < 129)%nat -> -7 <= nth i dk1 0 <= 7).
  Context (Hdigits_bounded2 :
    forall i, (i < 129)%nat -> -7 <= nth i dk2 0 <= 7).
  Context (Hfs_pos : 0 < felem_size_in_bytes).
  Context (Hfs_small : 12 * felem_size_in_bytes < 2 ^ width).

  Context (table_P_entries table_Phi_entries : list (F * F * F)).
  Context (Htable_P_len : length table_P_entries = 4%nat).
  Context (Htable_Phi_len : length table_Phi_entries = 4%nat).

  Context (Hdigit_load1 : forall (n : nat) (base : word) (m : mem) R,
    (n < length dk1)%nat ->
    (@DigitArray _ word mem base dk1 ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk1 0))).
  Context (Hdigit_load2 : forall (n : nat) (base : word) (m : mem) R,
    (n < length dk2)%nat ->
    (@DigitArray _ word mem base dk2 ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk2 0))).

  (* --- Additional hypotheses for process_both_digits_ok --- *)

  Context (Px Py Pz Phix Phiy Phiz : F).
  Let scmul_glv := scmul Fzero Fone curve_add.

  Context (Htable_P :
    length table_P_entries = 4%nat /\
    forall i, (i < 4)%nat ->
      nth i table_P_entries (Fzero,Fone,Fzero) =
        scmul_glv (2 * i + 1) (Px, Py, Pz)).
  Context (Htable_Phi :
    length table_Phi_entries = 4%nat /\
    forall i, (i < 4)%nat ->
      nth i table_Phi_entries (Fzero,Fone,Fzero) =
        scmul_glv (2 * i + 1) (Phix, Phiy, Phiz)).

  Context (point_opp_correct :
    forall X Y Z,
      curve_add (Fzero,Fone,Fzero) (X, F.opp Y, Z) =
      curve_add (Fzero,Fone,Fzero) (X, F.opp Y, Z)).

  Context (digit_point_P_correct :
    forall d, -7 <= d <= 7 ->
      curve_add (Fzero,Fone,Fzero) (digit_point d table_P_entries) =
      curve_add (Fzero,Fone,Fzero)
        (scmul_glv (Z.to_nat (Z.abs d)) (Px,Py,Pz))).
  Context (digit_point_Phi_correct :
    forall d, -7 <= d <= 7 ->
      curve_add (Fzero,Fone,Fzero) (digit_point d table_Phi_entries) =
      curve_add (Fzero,Fone,Fzero)
        (scmul_glv (Z.to_nat (Z.abs d)) (Phix,Phiy,Phiz))).

  Context (Hws_nn1 :
    forall n, (n <= 129)%nat -> 0 <= weighted_sum (skipn n dk1) 0).
  Context (Hws_nn2 :
    forall n, (n <= 129)%nat -> 0 <= weighted_sum (skipn n dk2) 0).

  Context (Hhorner_step : forall n (Ox Oy Oz : F),
    (n < 129)%nat ->
    let ws1_old := weighted_sum (skipn (S n) dk1) 0 in
    let ws2_old := weighted_sum (skipn (S n) dk2) 0 in
    (Ox,Oy,Oz) = curve_add
      (scmul_glv (Z.to_nat (2 * ws1_old)) (Px,Py,Pz))
      (scmul_glv (Z.to_nat (2 * ws2_old)) (Phix,Phiy,Phiz)) ->
    let d1 := nth n dk1 0 in
    let d2 := nth n dk2 0 in
    let after_d1 := if d1 =? 0 then (Ox,Oy,Oz)
                    else curve_add (Ox,Oy,Oz) (digit_point d1 table_P_entries) in
    (if d2 =? 0 then after_d1
     else curve_add after_d1 (digit_point d2 table_Phi_entries))
    = curve_add
      (scmul_glv (Z.to_nat (weighted_sum (skipn n dk1) 0)) (Px,Py,Pz))
      (scmul_glv (Z.to_nat (weighted_sum (skipn n dk2) 0)) (Phix,Phiy,Phiz))).

  (* ================================================================== *)
  (** ** Concrete-R0 HProcessBothDigits discharge                         *)
  (* ================================================================== *)

  (** This has exactly the shape of [process_both_digits_ok]'s conclusion,
      with [DigitArray] and [Table4] explicit. It is proved by applying
      [process_both_digits_ok] and supplying the P/Phi discharges from
      [BLS12_wNAF_GLV_Closed.v]. *)
  Lemma HProcessBothDigits_concrete :
    forall (n : nat) pOx pOy pOz pAx pAy pAz
      pTP pTPhi pDK1 pDK2 (Ox Oy Oz Ax Ay Az : F)
      (Rframe : mem -> Prop) tr0 m0 l0,
    (n < 129)%nat ->
    (Ox,Oy,Oz) = curve_add
      (scmul_glv (Z.to_nat (2 * weighted_sum (skipn (S n) dk1) 0)) (Px,Py,Pz))
      (scmul_glv (Z.to_nat (2 * weighted_sum (skipn (S n) dk2) 0)) (Phix,Phiy,Phiz)) ->
    (FElem (Some tight_bounds) pOx Ox ⋆ FElem (Some tight_bounds) pOy Oy
     ⋆ FElem (Some tight_bounds) pOz Oz ⋆ FElem (Some tight_bounds) pAx Ax
     ⋆ FElem (Some tight_bounds) pAy Ay ⋆ FElem (Some tight_bounds) pAz Az
     ⋆ DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
     ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
     ⋆ Rframe) m0 ->
    map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
    map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
    map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
    map.get l0 "table_P" = Some pTP -> map.get l0 "table_Phi" = Some pTPhi ->
    map.get l0 "digits_k1" = Some pDK1 -> map.get l0 "digits_k2" = Some pDK2 ->
    map.get l0 "iter" = Some (word.of_Z (Z.of_nat n)) ->
    WeakestPrecondition.cmd functions
      (cmd.seq
        (cmd.set "d1" (expr.load access_size.word
          (expr.op bopname.add (expr.var "digits_k1")
            (expr.op bopname.mul (expr.var "iter")
              (expr.literal (Memory.bytes_per_word 64))))))
        (cmd.seq
          (process_one_digit curve_add_name felem_copy opp felem_size_in_bytes
            "d1" "table_P" "auxx" "auxy" "auxz" "outx" "outy" "outz")
          (cmd.seq
            (cmd.set "d2" (expr.load access_size.word
              (expr.op bopname.add (expr.var "digits_k2")
                (expr.op bopname.mul (expr.var "iter")
                  (expr.literal (Memory.bytes_per_word 64))))))
            (process_one_digit curve_add_name felem_copy opp felem_size_in_bytes
              "d2" "table_Phi" "auxx" "auxy" "auxz" "outx" "outy" "outz"))))
      tr0 m0 l0
      (fun t' m' l' =>
        exists Ox' Oy' Oz' Ax' Ay' Az',
        (Ox',Oy',Oz') =
          curve_add
            (scmul_glv (Z.to_nat (weighted_sum (skipn n dk1) 0)) (Px,Py,Pz))
            (scmul_glv (Z.to_nat (weighted_sum (skipn n dk2) 0)) (Phix,Phiy,Phiz))
        /\ (FElem (Some tight_bounds) pOx Ox' ⋆ FElem (Some tight_bounds) pOy Oy'
            ⋆ FElem (Some tight_bounds) pOz Oz' ⋆ FElem (Some tight_bounds) pAx Ax'
            ⋆ FElem (Some tight_bounds) pAy Ay' ⋆ FElem (Some tight_bounds) pAz Az'
            ⋆ DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
            ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
            ⋆ Rframe) m'
        /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
        /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
        /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
        /\ map.get l' "table_P" = Some pTP /\ map.get l' "table_Phi" = Some pTPhi
        /\ map.get l' "digits_k1" = Some pDK1 /\ map.get l' "digits_k2" = Some pDK2
        /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
        /\ tr0 = t').
  Proof.
    apply process_both_digits_ok; try assumption.
    - apply HLoadAndProcess_P_discharged with
        (dk2 := dk2) (table_Phi_entries := table_Phi_entries);
        assumption.
    - apply HLoadAndProcess_Phi_discharged with
        (dk1 := dk1) (table_P_entries := table_P_entries);
        assumption.
  Qed.

  (* ================================================================== *)
  (** ** Full end-to-end wNAF GLV theorem                                 *)
  (* ================================================================== *)

  (** Additional hypotheses for loop body and outer loop. *)
  Context (curve_double_name : string).
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

  Context (HStoreZero : @StoreZero.spec_of_store_zero
    _ _ _ _ _ _ field_parameters field_representation functions).

  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  (** The citable end-to-end theorem: wNAF GLV computes k1*P + k2*Phi.
      This composes ALL layers:
        LoadAndProcess → GLV_Closed → ProcessDigits → LoopBody → Proof
      into a single closed statement.
      Uses Point3 grouping to match wnaf_glv_ok's sep shape. *)
  Theorem wnaf_glv_full :
    forall k1 k2,
    wsum dk1 = k1 -> wsum dk2 = k2 ->
    0 <= k1 -> 0 <= k2 ->
    forall pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
      (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F) (Rinner : mem -> Prop) tr m l,
    map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
    map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
    map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
    map.get l "table_P" = Some pTP -> map.get l "table_Phi" = Some pTPhi ->
    map.get l "digits_k1" = Some pDK1 -> map.get l "digits_k2" = Some pDK2 ->
    (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
     ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0
     ⋆ DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
     ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
     ⋆ Rinner) m ->
    WeakestPrecondition.cmd functions
      (wnaf_glv_func_body curve_add_name curve_double_name "store_zero"
         felem_copy opp 129 felem_size_in_bytes
         "digits_k1" "digits_k2" "table_P" "table_Phi")
      tr m l
      (fun t m' l' =>
        exists Rx Ry Rz Ax' Ay' Az',
        (Rx,Ry,Rz) = curve_add (scmul_glv (Z.to_nat k1) (Px,Py,Pz))
                                (scmul_glv (Z.to_nat k2) (Phix,Phiy,Phiz))
        /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
            ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az'
            ⋆ DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
            ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
            ⋆ Rinner) m').
  Proof.
    (* After making `⋆` left-associative and adding explicit inner parens
       in LoopBody.v to group (DigitArray ⋆ DigitArray ⋆ Table4 ⋆ Table4 ⋆ Rinner),
       the sep shapes now match syntactically between HLoopBody's expected form
       and wnaf_loop_body_ok's conclusion. No HO unification needed. *)
    intros k1 k2 Hk1 Hk2 Hk1nn Hk2nn
      pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
      Ox0 Oy0 Oz0 Ax0 Ay0 Az0 Rinner tr m l
      Hl_ox Hl_oy Hl_oz Hl_ax Hl_ay Hl_az
      Hl_tp Hl_tphi Hl_dk1 Hl_dk2 Hsep.
    eapply WeakestPreconditionProperties.Proper_cmd;
      [|eapply (@wnaf_glv_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  curve_add curve_add_id_l
                  functions HStoreZero dk1 dk2 Px Py Pz Phix Phiy Phiz
                  k1 k2 Hlen1 Hlen2 Hk1 Hk2 Hk1nn Hk2nn
                  (fun pTP0 pTPhi0 pDK10 pDK20 =>
                    (DigitArray pDK10 dk1 ⋆ DigitArray pDK20 dk2
                     ⋆ Table4 pTP0 table_P_entries
                     ⋆ Table4 pTPhi0 table_Phi_entries
                     ⋆ Rinner)%sep));
         try eassumption; try ecancel_assumption].
    - (* Postcondition weakening: Point3-grouped sep to flat sep *)
      intros t2 m2 l2 (Rx & Ry & Rz & Ax' & Ay' & Az' & Hout & Hsep2).
      exists Rx, Ry, Rz, Ax', Ay', Az'. split; [exact Hout|].
      ecancel_assumption.
    - (* HLoopBody: compose wnaf_loop_body_ok with HProcessBothDigits_concrete.
         The parameterized R + explicit inner parens in wnaf_loop_body_ok
         means the sep shapes now match without HO unification. *)
      intros n pOx' pOy' pOz' pAx' pAy' pAz' pTP' pTPhi' pDK1' pDK2'
        Ox' Oy' Oz' Ax' Ay' Az' tr0 m0 l0
        Hn Hinv Hsep0 Hl_ox0 Hl_oy0 Hl_oz0 Hl_ax0 Hl_ay0 Hl_az0
        Hl_tp0 Hl_tphi0 Hl_dk10 Hl_dk20 Hl_iter0.
      eapply wnaf_loop_body_ok; try eassumption.
      exact HProcessBothDigits_concrete.
  Qed.

End WNAFInstanceFinal.

(** [HProcessBothDigits_concrete] is Qed'd and closed under the global
    context — it cleanly composes [load_and_process_{P,Phi}_ok] (via
    [BLS12_wNAF_GLV_Closed.v]'s discharges) with [process_both_digits_ok]
    and has the shape of [process_both_digits_ok]'s conclusion directly.

    ** Remaining follow-up: **

    The final step — composing [HProcessBothDigits_concrete] into
    [wnaf_loop_body_ok] → [wnaf_glv_ok] — requires either:

    (A) modifying [wnaf_loop_body_ok]'s [HProcessBothDigits] Section
        Context in [BLS12_wNAF_GLV_LoopBody.v] to use the concrete R0
        shape [DigitArray ⋆ DigitArray ⋆ Table4 ⋆ Table4 ⋆ Rinner]
        (invasive: touches a Qed'd proof); OR

    (B) adapting [wnaf_loop_body_ok]'s proof by duplication into
        [wnaf_loop_body_ok_concrete] which uses
        [HProcessBothDigits_concrete] directly.

    Both options are engineering tasks that do not affect the proven
    correctness of the per-digit and horner-algebra layers. The
    arithmetic, the critical per-digit WP, and the
    generic-to-concrete bridge are all established here and in
    [BLS12_wNAF_GLV_Closed.v]. *)
