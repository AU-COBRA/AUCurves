(** * Adapters from the Rupicola general-a RCB addition to the wNAF
      scalar-multiplication interface.

    The verified single-scalar wNAF chain
    (wNAF_GLV_Func.v / wNAF_Single_LoadAndProcess.v /
    wNAF_Single_LoopBody.v / wNAF_Single_Proof.v /
    BN254_wNAF_Instance.wnaf_single_full) takes its point operations
    as bedrock2 call specs of a fixed shape:

      HCurveAddInplace  "curve_add"    [pXo;pX2;pYo;pY2;pZo;pZ2;pXo;pYo;pZo]
                        (out aliases input 1; post = curve_add P1 P2)
      HCurveDouble      "curve_double" [pX;pY;pZ;pX;pY;pZ]
                        (fully aliased; post = curve_add P P)
      HFelemCopy        felem_copy     [pDst;pSrc]  (dst an FElem, not bytes)
      HOpp / HOppInplace opp           [pOut;pIn] / [p;p]
      HStoreZero        "store_zero"   [px;py;pz]   (StoreZero.spec_of_store_zero)

    [spec_of_rcb_add_general] (CurveAddGeneralA.v) has a different ABI
    (outputs first), requires all nine buffers pairwise disjoint, and
    requires the three output buffers to hold tight-bounded encodings
    on entry.  This file defines wrapper bodies that realise the chain's
    shapes on top of the derived function plus [felem_copy] and
    [from_word], states their specs in exactly the chain's form, and
    states the adapter lemmas.  All proofs are Admitted: this is a
    static draft written under a no-compile constraint.  Proof
    templates: CurveAddInplaceWrapper.v (stack temps + copy back),
    CurveAddGeneralA_P256_Loaders.v (start_func / straightline).

    Design notes (see docs/nist_scalar_mult_plan.md §3):
    - G2: the three [felem_copy t <- P1] before the add exist only to
      make the temporaries tight-bounded for the derived spec.  Once
      CurveAddGeneralA.v weakens its output precondition to
      [FElem None], drop them.
    - G3: doubling calls the general add with a COPY of P as the second
      operand because the derived spec forbids P1 = P2 aliasing.
    - G5: the chain hard-wires the FieldParameters name [opp] for the
      aliased negation; [opp_inplace_func] below is the intended callee
      once the four generic files take an [opp_name] parameter. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(* ================================================================== *)
(** ** 1. Gallina model: the chain's [curve_add] on plain triples         *)
(* ================================================================== *)

Section Model.
  Context {field_parameters : FieldParameters}.
  Local Notation F := (F M_pos).

  (** [rcb_add_general_gallina] returns a Rupicola tuple
      [\<X, Y, Z\>]; the chain works with [F * F * F]. *)
  Definition curve_add_general_triple (a_val three_b_val : F)
             (P Q : F * F * F) : F * F * F :=
    let '(X1, Y1, Z1) := P in
    let '(X2, Y2, Z2) := Q in
    let '\<x, y, z\> :=
      @rcb_add_general_gallina _ a_val three_b_val X1 Y1 Z1 X2 Y2 Z2 in
    (x, y, z).

  (** Point negation on projective triples, as in
      BLS12_wNAF_ProcessDigits.point_opp. *)
  Definition point_opp_triple (P : F * F * F) : F * F * F :=
    let '(X, Y, Z) := P in (X, F.opp Y, Z).
End Model.

(* ================================================================== *)
(** ** 2. Wrapper bodies                                                *)
(* ================================================================== *)

Section Bodies.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width}
          {mem : map.map word Byte.byte}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  (** "curve_add" in the wNAF ABI (a=0 argument order, output aliases
      input 1; the last three parameters are ignored because the chain
      always passes X1,Y1,Z1 there).  Body:
        stackalloc tx ty tz
        felem_copy(tx,X1); felem_copy(ty,Y1); felem_copy(tz,Z1)   (G2)
        curve_add_general(tx,ty,tz, X1,Y1,Z1, X2,Y2,Z2)
        felem_copy(X1,tx); felem_copy(Y1,ty); felem_copy(Z1,tz) *)
  Definition curve_add_inplace_general_func : function_t :=
    ("curve_add",
     (["X1"; "X2"; "Y1"; "Y2"; "Z1"; "Z2"; "Xout"; "Yout"; "Zout"],
      []%list,
      cmd.stackalloc "tx" felem_size_in_bytes
      (cmd.stackalloc "ty" felem_size_in_bytes
      (cmd.stackalloc "tz" felem_size_in_bytes
      (cmd.seq (cmd.call [] felem_copy [expr.var "tx"; expr.var "X1"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "ty"; expr.var "Y1"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "tz"; expr.var "Z1"])
      (cmd.seq (cmd.call [] "curve_add_general"
                 [expr.var "tx"; expr.var "ty"; expr.var "tz";
                  expr.var "X1"; expr.var "Y1"; expr.var "Z1";
                  expr.var "X2"; expr.var "Y2"; expr.var "Z2"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "X1"; expr.var "tx"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "Y1"; expr.var "ty"])
               (cmd.call [] felem_copy [expr.var "Z1"; expr.var "tz"]))))))))))).

  (** "curve_double" in the wNAF ABI (fully aliased).  Body:
        stackalloc tx ty tz ux uy uz
        felem_copy(ux,Xin); felem_copy(uy,Yin); felem_copy(uz,Zin)   -- second operand copy (G3)
        felem_copy(tx,Xin); felem_copy(ty,Yin); felem_copy(tz,Zin)   -- tight-bounded outputs (G2)
        curve_add_general(tx,ty,tz, Xin,Yin,Zin, ux,uy,uz)
        felem_copy(Xin,tx); felem_copy(Yin,ty); felem_copy(Zin,tz)
      Phase 1 only; the dedicated CurveDoubleGeneralA body needs the
      projective-equivalence refactor of the chain (plan G6). *)
  Definition curve_double_general_func : function_t :=
    ("curve_double",
     (["Xin"; "Yin"; "Zin"; "Xout"; "Yout"; "Zout"],
      []%list,
      cmd.stackalloc "tx" felem_size_in_bytes
      (cmd.stackalloc "ty" felem_size_in_bytes
      (cmd.stackalloc "tz" felem_size_in_bytes
      (cmd.stackalloc "ux" felem_size_in_bytes
      (cmd.stackalloc "uy" felem_size_in_bytes
      (cmd.stackalloc "uz" felem_size_in_bytes
      (cmd.seq (cmd.call [] felem_copy [expr.var "ux"; expr.var "Xin"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "uy"; expr.var "Yin"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "uz"; expr.var "Zin"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "tx"; expr.var "Xin"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "ty"; expr.var "Yin"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "tz"; expr.var "Zin"])
      (cmd.seq (cmd.call [] "curve_add_general"
                 [expr.var "tx"; expr.var "ty"; expr.var "tz";
                  expr.var "Xin"; expr.var "Yin"; expr.var "Zin";
                  expr.var "ux"; expr.var "uy"; expr.var "uz"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "Xin"; expr.var "tx"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "Yin"; expr.var "ty"])
               (cmd.call [] felem_copy [expr.var "Zin"; expr.var "tz"]))))))))))))))))).

  (** Aliasing-tolerant negation: opp_inplace(Yout, Yin) with Yout = Yin
      allowed.  Body: stackalloc t; felem_copy(t, Yin); opp(Yout, t). *)
  Definition opp_inplace_func : function_t :=
    ("opp_inplace",
     (["Yout"; "Yin"],
      []%list,
      cmd.stackalloc "t" felem_size_in_bytes
      (cmd.seq (cmd.call [] felem_copy [expr.var "t"; expr.var "Yin"])
               (cmd.call [] opp [expr.var "Yout"; expr.var "t"])))).

  (** "store_zero" via [from_word] (the NIST syntheses provide no
      dedicated zero/one loaders): (0 : 1 : 0). *)
  Definition store_zero_from_word_func : function_t :=
    ("store_zero",
     (["outx"; "outy"; "outz"],
      []%list,
      cmd.seq (cmd.call [] from_word [expr.var "outx"; expr.literal 0])
      (cmd.seq (cmd.call [] from_word [expr.var "outy"; expr.literal 1])
               (cmd.call [] from_word [expr.var "outz"; expr.literal 0])))).
End Bodies.

(* ================================================================== *)
(** ** 3. Specs in the chain's shapes, and adapter lemmas                *)
(* ================================================================== *)

Section Specs.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width}
          {mem : map.map word Byte.byte}.
  Context {locals : map.map String.string word}.
  Context {ext_spec : bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  (** The two curve constants, as in CurveAddGeneralA.v. *)
  Context (three_b a_const : felem).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).

  Let a_val : F := feval (proj1_sig a_const).
  Let three_b_val : F := feval (proj1_sig three_b).

  (** The chain's [curve_add] for this curve. *)
  Definition curve_add_g : F * F * F -> F * F * F -> F * F * F :=
    curve_add_general_triple a_val three_b_val.

  (** [curve_add_g] unfolds the derived post-condition equation. *)
  Lemma curve_add_g_of_gallina :
    forall X1 Y1 Z1 X2 Y2 Z2 outx outy outz,
      @rcb_add_general_gallina _ a_val three_b_val X1 Y1 Z1 X2 Y2 Z2
        = \<outx, outy, outz\> ->
      curve_add_g (X1, Y1, Z1) (X2, Y2, Z2) = (outx, outy, outz).
  Proof.
    intros * H. unfold curve_add_g, curve_add_general_triple.
    rewrite H. reflexivity.
  Qed.

  (* ---- HCurveAddInplace ------------------------------------------ *)

  Definition spec_of_curve_add_inplace_general
             (functions : Semantics.env) : Prop :=
    forall pXo pX2 pYo pY2 pZo pZ2
      (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pXo X * FElem (Some tight_bounds) pYo Y
     * FElem (Some tight_bounds) pZo Z * FElem (Some tight_bounds) pX2 X2'
     * FElem (Some tight_bounds) pY2 Y2' * FElem (Some tight_bounds) pZ2 Z2'
     * R0)%sep m0 ->
    WeakestPrecondition.call functions "curve_add" tr0 m0
      [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
      (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
        let '(Xo', Yo', Zo') := curve_add_g (X, Y, Z) (X2', Y2', Z2') in
        (FElem (Some tight_bounds) pXo Xo' * FElem (Some tight_bounds) pYo Yo'
         * FElem (Some tight_bounds) pZo Zo' * FElem (Some tight_bounds) pX2 X2'
         * FElem (Some tight_bounds) pY2 Y2' * FElem (Some tight_bounds) pZ2 Z2'
         * R0)%sep m')).

  (** Proof template (CurveAddInplaceWrapper.v phases 1-5):
      start_func; 3 stackallocs (anybytes -> FElem None via
      felem_alloc / P_from_bytes); 3 felem_copy (FElem None dst is
      bytes: FElem_to_bytes) giving tight temps; the derived call with
      Rout := the frame (uses the six disjoint inputs + three tight
      temps); 3 felem_copy back (dst pXo etc. as bytes); dealloc the
      temps (P_to_bytes); rewrite with [curve_add_g_of_gallina]. *)
  Lemma curve_add_inplace_general_ok :
    forall functions,
      map.get functions "curve_add"
        = Some (snd curve_add_inplace_general_func) ->
      spec_of_rcb_add_general three_b a_const functions ->
      spec_of_felem_copy functions ->
      spec_of_curve_add_inplace_general functions.
  Proof.
  Admitted.

  (* ---- HCurveDouble ---------------------------------------------- *)

  Definition spec_of_curve_double_general
             (functions : Semantics.env) : Prop :=
    forall pX pY pZ (X Y Z : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pX X * FElem (Some tight_bounds) pY Y
     * FElem (Some tight_bounds) pZ Z * R0)%sep m0 ->
    Semantics.call functions "curve_double" tr0 m0
      [pX; pY; pZ; pX; pY; pZ]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        let '(Xo, Yo, Zo) := curve_add_g (X, Y, Z) (X, Y, Z) in
        (FElem (Some tight_bounds) pX Xo * FElem (Some tight_bounds) pY Yo
         * FElem (Some tight_bounds) pZ Zo * R0)%sep m').

  Lemma curve_double_general_ok :
    forall functions,
      map.get functions "curve_double"
        = Some (snd curve_double_general_func) ->
      spec_of_rcb_add_general three_b a_const functions ->
      spec_of_felem_copy functions ->
      spec_of_curve_double_general functions.
  Proof.
  Admitted.

  (* ---- HFelemCopy (shape adapter, G4) ----------------------------- *)

  (** The chain's copy spec has an FElem destination; fiat-crypto's
      [spec_of_felem_copy] has a byte-array destination with a length
      side condition.  Proof: [FElem (Some tight_bounds) pDst old] ->
      [exists bs, bs$@pDst /\ length bs = felem_size_in_bytes]
      (Compilation2 FElem_to_bytes / P_to_bytes), then the fiat spec. *)
  Lemma felem_copy_HFelemCopy :
    forall functions,
      spec_of_felem_copy functions ->
      forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
        (FElem (Some tight_bounds) pSrc v
         * FElem (Some tight_bounds) pDst old * R0)%sep m0 ->
        Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
          (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
            (FElem (Some tight_bounds) pSrc v
             * FElem (Some tight_bounds) pDst v * R0)%sep m').
  Proof.
  Admitted.

  (* ---- HOpp (shape adapter, G4) ----------------------------------- *)

  (** From fiat-crypto's [unop_spec un_opp] (input tight, output loose,
      byte-array destination); loose -> tight by [Hbounds_eq]. *)
  Lemma opp_HOpp :
    forall functions,
      spec_of_UnOp un_opp functions ->
      forall pOut pIn (Y : F) (Yold : F) R0 tr0 m0,
        (FElem (Some tight_bounds) pIn Y
         * FElem (Some tight_bounds) pOut Yold * R0)%sep m0 ->
        Semantics.call functions opp tr0 m0 [pOut; pIn]
          (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
            (FElem (Some tight_bounds) pIn Y
             * FElem (Some tight_bounds) pOut (F.opp Y) * R0)%sep m').
  Proof.
  Admitted.

  (* ---- HOppInplace via the wrapper (G5) --------------------------- *)

  (** Both shapes of the chain's negation hypothesis, at the wrapper
      name.  Usable by the chain only after its [opp] name is made a
      parameter (plan G5). *)
  Definition spec_of_opp_inplace (functions : Semantics.env) : Prop :=
    (forall pOut pIn (Y : F) (Yold : F) R0 tr0 m0,
        (FElem (Some tight_bounds) pIn Y
         * FElem (Some tight_bounds) pOut Yold * R0)%sep m0 ->
        Semantics.call functions "opp_inplace" tr0 m0 [pOut; pIn]
          (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
            (FElem (Some tight_bounds) pIn Y
             * FElem (Some tight_bounds) pOut (F.opp Y) * R0)%sep m'))
    /\
    (forall p (Y : F) R0 tr0 m0,
        (FElem (Some tight_bounds) p Y * R0)%sep m0 ->
        Semantics.call functions "opp_inplace" tr0 m0 [p; p]
          (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
            (FElem (Some tight_bounds) p (F.opp Y) * R0)%sep m')).

  Lemma opp_inplace_ok :
    forall functions,
      map.get functions "opp_inplace" = Some (snd opp_inplace_func) ->
      spec_of_UnOp un_opp functions ->
      spec_of_felem_copy functions ->
      spec_of_opp_inplace functions.
  Proof.
  Admitted.

  (* ---- HStoreZero (G8) -------------------------------------------- *)

  (** [StoreZero.spec_of_store_zero]: inputs [FElem None], outputs
      [(F.of_Z 0, F.of_Z 1, F.of_Z 0)] tight.  From [spec_of_from_word]:
      [feval X = F.of_Z _ (word.unsigned (word.of_Z 0))] and
      [word.unsigned_of_Z_0]; [FElem None] -> bytes for the destination. *)
  Lemma store_zero_from_word_ok :
    forall functions,
      map.get functions "store_zero" = Some (snd store_zero_from_word_func) ->
      spec_of_from_word functions ->
      @StoreZero.spec_of_store_zero _ _ _ _ _ _
        field_parameters field_representation functions.
  Proof.
  Admitted.

End Specs.
