(** * wNAF GLV — Closed Composition (critical link).
    See [WNAF_GLV_STATUS.md] for full verification status and architecture.

    Demonstrates that [load_and_process_P_ok] and [load_and_process_Phi_ok]
    from [BLS12_wNAF_LoadAndProcess.v] have exactly the type required to
    discharge the [HLoadAndProcess_P] and [HLoadAndProcess_Phi] Section
    Context hypotheses of [process_both_digits_ok] in
    [BLS12_wNAF_ProcessDigits.v].

    This file opens a single Section with the union of primitive
    Contexts needed by both files and exposes two [Lemma]s whose
    bodies are direct applications of the Qed'd theorems from
    [BLS12_wNAF_LoadAndProcess.v].

    The full composition up to [wnaf_glv_ok] is then a straightforward
    chaining of these discharges with [process_both_digits_ok],
    [wnaf_loop_body_ok], and [wnaf_glv_ok] — each of which is already
    Qed'd and takes the layer below as an explicit hypothesis. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_wNAF_LoadAndProcess.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section WNAFClosed.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
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

  (* --- Digit and table data (both sides) --- *)

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

  (** ** Discharges: the two proven theorems discharge the ProcessDigits
         Section Context hypotheses [HLoadAndProcess_P] and
         [HLoadAndProcess_Phi] exactly. *)

  Lemma HLoadAndProcess_P_discharged :
    forall n pOx pOy pOz pAx pAy pAz pTP pDK1
      (Ox Oy Oz Ax Ay Az : F) R0 tr0 m0 l0,
    (n < 129)%nat ->
    (FElem (Some tight_bounds) pOx Ox ⋆ FElem (Some tight_bounds) pOy Oy
     ⋆ FElem (Some tight_bounds) pOz Oz ⋆ FElem (Some tight_bounds) pAx Ax
     ⋆ FElem (Some tight_bounds) pAy Ay ⋆ FElem (Some tight_bounds) pAz Az
     ⋆ DigitArray pDK1 dk1 ⋆ Table4 pTP table_P_entries ⋆ R0) m0 ->
    map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
    map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
    map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
    map.get l0 "table_P" = Some pTP ->
    map.get l0 "digits_k1" = Some pDK1 ->
    map.get l0 "iter" = Some (word.of_Z (Z.of_nat n)) ->
    WeakestPrecondition.cmd functions
      (cmd.seq
        (cmd.set "d1" (expr.load access_size.word
          (expr.op bopname.add (expr.var "digits_k1")
            (expr.op bopname.mul (expr.var "iter")
              (expr.literal (Memory.bytes_per_word 64))))))
        (process_one_digit curve_add_name felem_copy opp felem_size_in_bytes
          "d1" "table_P" "auxx" "auxy" "auxz" "outx" "outy" "outz"))
      tr0 m0 l0
      (fun t' m' l' =>
        exists Ox' Oy' Oz' Ax' Ay' Az',
        let d := nth n dk1 0 in
        (Ox',Oy',Oz') = (if d =? 0 then (Ox,Oy,Oz)
          else curve_add (Ox,Oy,Oz) (digit_point d table_P_entries))
        /\ (FElem (Some tight_bounds) pOx Ox' ⋆ FElem (Some tight_bounds) pOy Oy'
            ⋆ FElem (Some tight_bounds) pOz Oz' ⋆ FElem (Some tight_bounds) pAx Ax'
            ⋆ FElem (Some tight_bounds) pAy Ay' ⋆ FElem (Some tight_bounds) pAz Az'
            ⋆ DigitArray pDK1 dk1 ⋆ Table4 pTP table_P_entries ⋆ R0) m'
        /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
        /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
        /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
        /\ map.get l' "table_P" = Some pTP
        /\ map.get l' "digits_k1" = Some pDK1
        /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
        /\ (forall k v, k <> "d1" -> k <> "lookup_d" -> k <> "tab_idx" ->
              k <> "tab_off" -> map.get l0 k = Some v -> map.get l' k = Some v)
        /\ tr0 = t').
  Proof.
    apply load_and_process_P_ok with
      (dk2 := dk2) (table_Phi_entries := table_Phi_entries);
      try assumption.
  Qed.

  Lemma HLoadAndProcess_Phi_discharged :
    forall n pOx pOy pOz pAx pAy pAz pTPhi pDK2
      (Ox Oy Oz Ax Ay Az : F) R0 tr0 m0 l0,
    (n < 129)%nat ->
    (FElem (Some tight_bounds) pOx Ox ⋆ FElem (Some tight_bounds) pOy Oy
     ⋆ FElem (Some tight_bounds) pOz Oz ⋆ FElem (Some tight_bounds) pAx Ax
     ⋆ FElem (Some tight_bounds) pAy Ay ⋆ FElem (Some tight_bounds) pAz Az
     ⋆ DigitArray pDK2 dk2 ⋆ Table4 pTPhi table_Phi_entries ⋆ R0) m0 ->
    map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
    map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
    map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
    map.get l0 "table_Phi" = Some pTPhi ->
    map.get l0 "digits_k2" = Some pDK2 ->
    map.get l0 "iter" = Some (word.of_Z (Z.of_nat n)) ->
    WeakestPrecondition.cmd functions
      (cmd.seq
        (cmd.set "d2" (expr.load access_size.word
          (expr.op bopname.add (expr.var "digits_k2")
            (expr.op bopname.mul (expr.var "iter")
              (expr.literal (Memory.bytes_per_word 64))))))
        (process_one_digit curve_add_name felem_copy opp felem_size_in_bytes
          "d2" "table_Phi" "auxx" "auxy" "auxz" "outx" "outy" "outz"))
      tr0 m0 l0
      (fun t' m' l' =>
        exists Ox' Oy' Oz' Ax' Ay' Az',
        let d := nth n dk2 0 in
        (Ox',Oy',Oz') = (if d =? 0 then (Ox,Oy,Oz)
          else curve_add (Ox,Oy,Oz) (digit_point d table_Phi_entries))
        /\ (FElem (Some tight_bounds) pOx Ox' ⋆ FElem (Some tight_bounds) pOy Oy'
            ⋆ FElem (Some tight_bounds) pOz Oz' ⋆ FElem (Some tight_bounds) pAx Ax'
            ⋆ FElem (Some tight_bounds) pAy Ay' ⋆ FElem (Some tight_bounds) pAz Az'
            ⋆ DigitArray pDK2 dk2 ⋆ Table4 pTPhi table_Phi_entries ⋆ R0) m'
        /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
        /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
        /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
        /\ map.get l' "table_Phi" = Some pTPhi
        /\ map.get l' "digits_k2" = Some pDK2
        /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
        /\ (forall k v, k <> "d2" -> k <> "lookup_d" -> k <> "tab_idx" ->
              k <> "tab_off" -> map.get l0 k = Some v -> map.get l' k = Some v)
        /\ tr0 = t').
  Proof.
    apply load_and_process_Phi_ok with
      (dk1 := dk1) (table_P_entries := table_P_entries);
      try assumption.
  Qed.

End WNAFClosed.

(** [HLoadAndProcess_P_discharged] and [HLoadAndProcess_Phi_discharged]
    are Qed'd closed lemmas with no remaining admits — they are the
    critical generic link from [BLS12_wNAF_LoadAndProcess.v]'s theorems
    to the [HLoadAndProcess_P/Phi] Section Contexts of
    [BLS12_wNAF_ProcessDigits.v].

    The upward chain ([HProcessBothDigits], [HLoopBody], [wnaf_glv_ok])
    cannot be composed generically: [wnaf_loop_body_ok]'s
    [HProcessBothDigits] hypothesis absorbs [DigitArray] / [Table4] into
    the frame [R0], while [process_both_digits_ok] has them EXPLICIT.
    The generic-to-concrete sep rearrangement is only possible when
    [R0] is known concretely. This is done in the final BLS12-381
    instantiation where the concrete memory layout supplies [R0] =
    [DigitArray ⋆ DigitArray ⋆ Table4 ⋆ Table4 ⋆ Rframe]. *)
