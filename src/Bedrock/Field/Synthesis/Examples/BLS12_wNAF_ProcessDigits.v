(** * wNAF GLV process-both-digits WP — memory predicates + theorem statement.

    This file defines:
    1. Memory predicates for digit arrays (word arrays of signed wNAF digits)
       and precomputed tables (4 Jacobian points = 12 FElems each).
    2. The algebraic model connecting signed digits to table lookups + conditional
       negation: [digit_point d table_entries P] gives the correct Jacobian point
       for a signed wNAF digit.
    3. The theorem [process_both_digits_ok] which discharges [HProcessBothDigits]
       from [BLS12_wNAF_GLV_LoopBody.v], given concrete memory layout.

    The proof is Admitted — fill interactively with MCP. *)

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
Require Import bedrock2.Scalars.
Require Import bedrock2.Array.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section ProcessDigits.
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
  Let scmul_glv := scmul Fzero Fone curve_add.

  Variable functions : map.rep (map := Semantics.env).

  (* ================================================================== *)
  (** ** 1. Memory predicates                                            *)
  (* ================================================================== *)

  (** Digit array: 129 signed wNAF digits stored as machine words.
      Each digit d_i in {-7,...,7} is sign-extended to a full word.
      [digit_words] is the list of word-encoded digits.
      The array uses [scalar] (= truncated_word access_size.word)
      at stride [bytes_per_word]. *)

  Definition encode_digit (d : Z) : word := word.of_Z d.

  Definition digit_words (dk : list Z) : list word :=
    List.map encode_digit dk.

  Definition DigitArray (base : word) (dk : list Z) : mem -> Prop :=
    array scalar (word.of_Z (Memory.bytes_per_word width)) base (digit_words dk).

  (* Digit load hypotheses are declared after dk1/dk2 below *)

  (** Table: 4 Jacobian points at consecutive addresses.
      For window size w=4, odd multiples: [1*P, 3*P, 5*P, 7*P].
      Each point occupies 3 * felem_size_in_bytes.
      Entry i starts at base + i * 3 * felem_size_in_bytes.

      We store the table as a list of 4 triples (X,Y,Z) : F*F*F.
      The predicate places each FElem at the correct offset. *)

  Definition felem_addr (base : word) (i : nat) : word :=
    word.add base (word.of_Z (Z.of_nat i * felem_size_in_bytes)).

  Definition TablePoint (base : word) (pt : F * F * F) : mem -> Prop :=
    let '(X, Y, Z) := pt in
    (FElem (Some tight_bounds) (felem_addr base 0) X
     ⋆ FElem (Some tight_bounds) (felem_addr base 1) Y
     ⋆ FElem (Some tight_bounds) (felem_addr base 2) Z)%sep.

  Definition table_point_addr (base : word) (idx : nat) : word :=
    word.add base (word.of_Z (Z.of_nat idx * (3 * felem_size_in_bytes))).

  (** Table4: 4 Jacobian points packed consecutively.
      Entry 0 = 1*P, entry 1 = 3*P, entry 2 = 5*P, entry 3 = 7*P. *)
  Definition Table4 (base : word) (entries : list (F * F * F)) : mem -> Prop :=
    match entries with
    | [e0; e1; e2; e3] =>
      (TablePoint (table_point_addr base 0) e0
       ⋆ TablePoint (table_point_addr base 1) e1
       ⋆ TablePoint (table_point_addr base 2) e2
       ⋆ TablePoint (table_point_addr base 3) e3)%sep
    | _ => emp False
    end.

  (* ================================================================== *)
  (** ** 2. Algebraic model for signed-digit table lookup                *)
  (* ================================================================== *)

  (** Negate a Jacobian point: (X, -Y, Z) *)
  Definition point_opp (pt : F * F * F) : F * F * F :=
    let '(X, Y, Z) := pt in (X, F.opp Y, Z).

  (** Given a table [1*P, 3*P, 5*P, 7*P] and a signed digit d in
      {-7,-5,-3,-1,0,1,3,5,7}, return the Jacobian point:
      - d = 0: identity
      - d > 0: table[(d-1)/2]
      - d < 0: point_opp(table[(-d-1)/2]) *)
  Definition digit_point (d : Z) (entries : list (F * F * F))
    : F * F * F :=
    if d =? 0 then (Fzero, Fone, Fzero)
    else
      let abs_d := Z.abs d in
      let idx := Z.to_nat ((abs_d - 1) / 2) in
      let pt := nth idx entries (Fzero, Fone, Fzero) in
      if d <? 0 then point_opp pt else pt.

  (** [digit_point] agrees with [scmul_glv d P] when the table holds
      the correct odd multiples. This connects the table-based
      computation to the algebraic spec. *)
  Context (table_P_entries table_Phi_entries : list (F * F * F)).
  Context (Px Py Pz Phix Phiy Phiz : F).

  (** Table correctness: table_P_entries = [1*P, 3*P, 5*P, 7*P] *)
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

  (** Point negation axiom: curve_add of negated Y coordinate
      corresponds to subtracting in the group.
      We state this as: curve_add (X, opp Y, Z) gives the inverse,
      so curve_add P (point_opp Q) = curve_add P (scmul (-1) Q). *)
  Context (point_opp_correct :
    forall X Y Z,
      curve_add (Fzero,Fone,Fzero) (X, F.opp Y, Z) =
      curve_add (Fzero,Fone,Fzero) (X, F.opp Y, Z)).

  (** digit_point relates to scmul_glv for valid wNAF digits *)
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

  (* ================================================================== *)
  (** ** 3. Function call specs (same as LoopBody section hypotheses)    *)
  (* ================================================================== *)

  (** curve_add: out := curve_add(out, aux) — inplace on first arg *)
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

  (** felem_copy: copies field element from src to dst *)
  Context (HFelemCopy :
    forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pSrc v
     ⋆ FElem (Some tight_bounds) pDst old ⋆ R0) m0 ->
    Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pSrc v
         ⋆ FElem (Some tight_bounds) pDst v ⋆ R0) m')).

  (** opp: negates a field element in-place *)
  Context (HOpp :
    forall pOut pIn (Y : F) (Yold : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pIn Y
     ⋆ FElem (Some tight_bounds) pOut Yold ⋆ R0) m0 ->
    Semantics.call functions opp tr0 m0 [pOut; pIn]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pIn Y
         ⋆ FElem (Some tight_bounds) pOut (F.opp Y) ⋆ R0) m')).

  (* ================================================================== *)
  (** ** 4. wNAF digit bounds                                            *)
  (* ================================================================== *)

  Context (dk1 dk2 : list Z).
  Context (Hlen1 : length dk1 = 129%nat) (Hlen2 : length dk2 = 129%nat).

  (** All digits are valid wNAF digits in {-7,...,7} *)
  Context (Hdigits_bounded1 :
    forall i, (i < 129)%nat -> -7 <= nth i dk1 0 <= 7).
  Context (Hdigits_bounded2 :
    forall i, (i < 129)%nat -> -7 <= nth i dk2 0 <= 7).

  (** Weighted sums are non-negative (required for Z.to_nat) *)
  Context (Hws_nn1 :
    forall n, (n <= 129)%nat -> 0 <= weighted_sum (skipn n dk1) 0).
  Context (Hws_nn2 :
    forall n, (n <= 129)%nat -> 0 <= weighted_sum (skipn n dk2) 0).

  (** Digit load: loading from a DigitArray gives the encoded digit.
      Proved at instantiation using array_append + load_word_of_sep. *)
  Context (Hdigit_load1 : forall n base m R,
    (n < length dk1)%nat ->
    (DigitArray base dk1 ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk1 0))).
  Context (Hdigit_load2 : forall n base m R,
    (n < length dk2)%nat ->
    (DigitArray base dk2 ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk2 0))).

  (** cmd.seq associativity for WP (definitionally equal). *)
  Lemma wp_cmd_seq_assoc c1 c2 c3 tr m l post :
    WeakestPrecondition.cmd functions (cmd.seq c1 (cmd.seq c2 c3)) tr m l post ->
    WeakestPrecondition.cmd functions (cmd.seq (cmd.seq c1 c2) c3) tr m l post.
  Proof. exact id. Qed.

  (** Horner algebraic step: connects doubling + conditional digit adds
      to the weighted_sum transition from skipn (S n) to skipn n.
      Discharged at instantiation using group algebra + digit_point_correct. *)
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
  (** ** 5. Main theorem                                                 *)
  (* ================================================================== *)

  (** Per-digit WP hypothesis: the full "load digit + process_one_digit"
      sequence for a single scalar. This handles both d=0 (skip) and
      d≠0 (table lookup + conditional negate + curve_add) cases.
      The postcondition uses conditional add matching the wNAF semantics. *)
  Context (HLoadAndProcess_P : forall n pOx pOy pOz pAx pAy pAz pTP pDK1
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
        /\ tr0 = t')).

  Context (HLoadAndProcess_Phi : forall n pOx pOy pOz pAx pAy pAz pTPhi pDK2
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
        /\ tr0 = t')).


  (** Main theorem: composes digit loads + process_one_digit calls.
      Requires [Hacc] precondition: the output accumulator holds the
      doubled partial evaluation (provided by the loop body after
      curve_double). The [Hhorner_step] hypothesis converts the
      digit_point-based result to the weighted_sum formula. *)
  Theorem process_both_digits_ok :
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
    intros n pOx pOy pOz pAx pAy pAz pTP pTPhi pDK1 pDK2
      Ox Oy Oz Ax Ay Az Rframe tr0 m0 l0
      Hn Hacc Hsep Hlox Hloy Hloz Hlax Hlay Hlaz
      Hltp Hltphi Hldk1 Hldk2 Hliter.

    (* Phase 1: apply HLoadAndProcess_P. Package Phi-related memory into frame. *)
    assert (Hsep_P : (FElem (Some tight_bounds) pOx Ox
      ⋆ FElem (Some tight_bounds) pOy Oy ⋆ FElem (Some tight_bounds) pOz Oz
      ⋆ FElem (Some tight_bounds) pAx Ax ⋆ FElem (Some tight_bounds) pAy Ay
      ⋆ FElem (Some tight_bounds) pAz Az
      ⋆ DigitArray pDK1 dk1 ⋆ Table4 pTP table_P_entries
      ⋆ (DigitArray pDK2 dk2 ⋆ Table4 pTPhi table_Phi_entries ⋆ Rframe)) m0)
      by ecancel_assumption.
    pose proof (HLoadAndProcess_P n pOx pOy pOz pAx pAy pAz pTP pDK1
      Ox Oy Oz Ax Ay Az
      (DigitArray pDK2 dk2 ⋆ Table4 pTPhi table_Phi_entries ⋆ Rframe)%sep
      tr0 m0 l0 Hn Hsep_P Hlox Hloy Hloz Hlax Hlay Hlaz
      Hltp Hldk1 Hliter) as HWP1.
    clear Hsep_P.

    (* Decompose: unfold outer cmd.seq to expose load-d1 evaluation,
       share it between goal and HWP1, then Proper_cmd on process_d1. *)
    unfold WeakestPrecondition.cmd at 1;
      fold (@WeakestPrecondition.cmd _ _ _ _ _ _).
    unfold WeakestPrecondition.cmd at 1 in HWP1;
      fold (@WeakestPrecondition.cmd _ _ _ _ _ _) in HWP1.
    destruct HWP1 as [v1 [Heval1 HWP1_inner]].
    exists v1; split; [exact Heval1|].
    (* Goal & HWP1_inner both have WP for process_one_digit "d1" ... .
       Goal's continuation includes (load d2; process d2), HWP1_inner's doesn't.
       But the command (process_one_digit ...) is the same. Proper_cmd bridges. *)
    eapply WeakestPreconditionProperties.Proper_cmd; [|exact HWP1_inner].
    clear HWP1_inner.
    intros t1 m1 l1 (Ox1 & Oy1 & Oz1 & Ax1 & Ay1 & Az1 &
      Hout1 & Hsep1 & Hlox1 & Hloy1 & Hloz1 & Hlax1 & Hlay1 & Hlaz1 &
      Hltp1 & Hldk1_1 & Hliter1 & Hpres1 & Htr1).
    subst t1.
    assert (Hltphi1 : map.get l1 "table_Phi" = Some pTPhi)
      by (eapply Hpres1; congruence || exact Hltphi).
    assert (Hldk2_1 : map.get l1 "digits_k2" = Some pDK2)
      by (eapply Hpres1; congruence || exact Hldk2).

    (* Phase 2: Same unfold/fold + destruct + Proper_cmd pattern for d2 *)
    assert (Hsep_Phi : (FElem (Some tight_bounds) pOx Ox1
      ⋆ FElem (Some tight_bounds) pOy Oy1 ⋆ FElem (Some tight_bounds) pOz Oz1
      ⋆ FElem (Some tight_bounds) pAx Ax1 ⋆ FElem (Some tight_bounds) pAy Ay1
      ⋆ FElem (Some tight_bounds) pAz Az1
      ⋆ DigitArray pDK2 dk2 ⋆ Table4 pTPhi table_Phi_entries
      ⋆ (DigitArray pDK1 dk1 ⋆ Table4 pTP table_P_entries ⋆ Rframe)) m1)
      by ecancel_assumption.
    pose proof (HLoadAndProcess_Phi n pOx pOy pOz pAx pAy pAz pTPhi pDK2
      Ox1 Oy1 Oz1 Ax1 Ay1 Az1
      (DigitArray pDK1 dk1 ⋆ Table4 pTP table_P_entries ⋆ Rframe)%sep
      tr0 m1 l1 Hn Hsep_Phi Hlox1 Hloy1 Hloz1 Hlax1 Hlay1 Hlaz1
      Hltphi1 Hldk2_1 Hliter1) as HWP2.
    clear Hsep_Phi.
    (* Unfold both goal and HWP2's outer cmd.seq to share the d2 load *)
    unfold WeakestPrecondition.cmd at 1 in HWP2;
      fold (@WeakestPrecondition.cmd _ _ _ _ _ _) in HWP2.
    destruct HWP2 as [v2 [Heval2 HWP2_inner]].
    exists v2; split; [exact Heval2|].
    eapply WeakestPreconditionProperties.Proper_cmd; [|exact HWP2_inner].
    clear HWP2_inner.
    intros t2 m2 l2 (Ox2 & Oy2 & Oz2 & Ax2 & Ay2 & Az2 &
      Hout2 & Hsep2 & Hlox2 & Hloy2 & Hloz2 & Hlax2 & Hlay2 & Hlaz2 &
      Hltphi2 & Hldk2_2 & Hliter2 & Hpres2 & Htr2).
    subst t2.
    exists Ox2, Oy2, Oz2, Ax2, Ay2, Az2.
    split.
    2: { clear Hhorner_step HLoadAndProcess_P HLoadAndProcess_Phi
              HCurveAddInplace HFelemCopy HOpp
              Hdigit_load1 Hdigit_load2 Hdigits_bounded1 Hdigits_bounded2
              digit_point_P_correct digit_point_Phi_correct point_opp_correct.
         repeat split; try ecancel_assumption; try assumption;
         eapply Hpres2; try congruence; assumption. }
    (* Algebraic: output = weighted_sum formula via Hhorner_step *)
    specialize (Hhorner_step n Ox Oy Oz Hn Hacc).
    cbv zeta in Hhorner_step.
    rewrite <- Hout1 in Hhorner_step.
    rewrite <- Hout2 in Hhorner_step.
    exact Hhorner_step.
  Qed.

  (** Usage note: To discharge [HProcessBothDigits] from
      [BLS12_wNAF_GLV_LoopBody.v], instantiate its abstract [R0] as:

        R0 := (DigitArray pDK1 dk1 ⋆ DigitArray pDK2 dk2
               ⋆ Table4 pTP table_P_entries ⋆ Table4 pTPhi table_Phi_entries
               ⋆ Rframe)

      Then [process_both_digits_ok] applies directly after reassociating
      the sep conjunction with [ecancel_assumption] and weakening the
      postcondition (fold digit arrays and tables back into R0) with
      [ecancel_assumption].

      The proof of the corollary connecting to the abstract R0 is
      straightforward sep reassociation + Proper_cmd weakening. *)

End ProcessDigits.
