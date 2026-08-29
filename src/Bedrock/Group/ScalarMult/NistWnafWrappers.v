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
    states the adapter lemmas.

    Honesty ledger (this file): proved — [FElem2_elim_frame],
    [FElem2_intro_frame], [FElem2_intro3], [FElem2_intro3R],
    [symmetry_iff1], [curve_add_g_of_gallina],
    [felem_copy_HFelemCopy], [opp_HOpp], [store_zero_from_word_ok].
    Admitted — the three wrapper-body lemmas
    ([curve_add_inplace_general_ok], [curve_double_general_ok],
    [opp_inplace_ok]): each needs the stackalloc/dealloc cascade on top
    of the function entry, which no wrapper proof in this repository has
    carried out yet — [CurveAddInplaceWrapper.v] gives its template in
    comments only.  Proof templates:
    CurveAddInplaceWrapper.v (stack temps + copy back),
    CurveAddGeneralA_P256_Loaders.v (start_func / straightline),
    wNAF_Single_Proof.v (per-call letexists / weaken_call pattern).

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

  (* ---- Transport between the two FElem layers --------------------- *)

  (** [Compilation2.FElem] hides a [felem] witness behind an [ex1];
      fiat-crypto's specs speak about that witness (or about its bytes)
      directly.  The two lemmas below move one leaf of a separation
      chain across the layer, with the rest of the chain as an explicit
      frame, so that reassociation is left to [ecancel_assumption].
      Shapes follow [p256_Bignum_to_FElem2] / [p256_FElem2_to_Bignum]
      (CurveAddGeneralA_P256.v, Qed). *)

  Lemma FElem2_elim_frame (b : option bounds) (p : word) (v : F)
        (R : mem -> Prop) (m : mem) :
    (FElem b p v * R)%sep m ->
    exists x : felem,
      feval x = v /\ Compilation2.maybe_bounded b x
      /\ (Field.FElem p x * R)%sep m.
  Proof.
    intros H. destruct H as (m1 & m2 & Hsplit & H1 & H2).
    cbv [Compilation2.FElem Lift1Prop.ex1] in H1.
    destruct H1 as [x H1].
    apply sep_emp_l in H1. destruct H1 as [[Hfe Hbd] H1].
    exists x. split; [exact Hfe|]. split; [exact Hbd|].
    exists m1, m2. split; [exact Hsplit|]. split; [exact H1 | exact H2].
  Qed.

  Lemma FElem2_intro_frame (b : bounds) (p : word) (x : felem) (v : F)
        (R : mem -> Prop) (m : mem) :
    feval x = v -> bounded_by b x ->
    (Field.FElem p x * R)%sep m ->
    (FElem (Some b) p v * R)%sep m.
  Proof.
    intros Hfe Hbd H. destruct H as (m1 & m2 & Hsplit & H1 & H2).
    exists m1, m2. split; [exact Hsplit|]. split; [|exact H2].
    cbv [Compilation2.FElem Lift1Prop.ex1].
    exists x. apply sep_emp_l.
    split; [split; [exact Hfe | exact Hbd] | exact H1].
  Qed.

  (** Three leaves at once, with the separation hypothesis FIRST so that
      [eapply ...; [ecancel_assumption | ..]] fixes the three witnesses
      before the value/bounds side conditions are seen. *)
  Lemma FElem2_intro3 (b : bounds) (p1 p2 p3 : word) (x1 x2 x3 : felem)
        (v1 v2 v3 : F) (R : mem -> Prop) (m : mem) :
    (Field.FElem p1 x1 * Field.FElem p2 x2 * Field.FElem p3 x3 * R)%sep m ->
    feval x1 = v1 -> bounded_by b x1 ->
    feval x2 = v2 -> bounded_by b x2 ->
    feval x3 = v3 -> bounded_by b x3 ->
    (FElem (Some b) p1 v1 * FElem (Some b) p2 v2 * FElem (Some b) p3 v3
     * R)%sep m.
  Proof.
    intros Hsep Hf1 Hb1 Hf2 Hb2 Hf3 Hb3.
    assert (H1 : (FElem (Some b) p1 v1
                  * (Field.FElem p2 x2 * (Field.FElem p3 x3 * R)))%sep m)
      by (apply (FElem2_intro_frame b p1 x1 v1 _ _ Hf1 Hb1); ecancel_assumption).
    assert (H2 : (FElem (Some b) p2 v2
                  * (FElem (Some b) p1 v1 * (Field.FElem p3 x3 * R)))%sep m)
      by (apply (FElem2_intro_frame b p2 x2 v2 _ _ Hf2 Hb2); ecancel_assumption).
    assert (H3 : (FElem (Some b) p3 v3
                  * (FElem (Some b) p1 v1 * (FElem (Some b) p2 v2 * R)))%sep m)
      by (apply (FElem2_intro_frame b p3 x3 v3 _ _ Hf3 Hb3); ecancel_assumption).
    ecancel_assumption.
  Qed.

  (** The same conclusion, right-associated.  [sep] is not
      definitionally associative, so an [eapply] of [FElem2_intro3]
      against a right-associated goal fails in unification (measured:
      the [store_zero] rebuild's only failure).  Which association the
      goal carries after the call plumbing is not predictable, so both
      shapes are available and the caller tries them in turn. *)
  Lemma FElem2_intro3R (b : bounds) (p1 p2 p3 : word) (x1 x2 x3 : felem)
        (v1 v2 v3 : F) (R : mem -> Prop) (m : mem) :
    (Field.FElem p1 x1 * Field.FElem p2 x2 * Field.FElem p3 x3 * R)%sep m ->
    feval x1 = v1 -> bounded_by b x1 ->
    feval x2 = v2 -> bounded_by b x2 ->
    feval x3 = v3 -> bounded_by b x3 ->
    (FElem (Some b) p1 v1
     * (FElem (Some b) p2 v2 * (FElem (Some b) p3 v3 * R)))%sep m.
  Proof.
    intros Hsep Hf1 Hb1 Hf2 Hb2 Hf3 Hb3.
    assert (H : (FElem (Some b) p1 v1 * FElem (Some b) p2 v2
                 * FElem (Some b) p3 v3 * R)%sep m)
      by (eapply FElem2_intro3; eassumption).
    ecancel_assumption.
  Qed.

  (* ---- HFelemCopy (shape adapter, G4) ----------------------------- *)

  (** The chain's copy spec has an FElem destination; fiat-crypto's
      [spec_of_felem_copy] has a byte-array destination with a length
      side condition.  Proof: peel both leaves with
      [FElem2_elim_frame], turn the destination felem into bytes with
      [felem_to_bytes] (an [iff1]), call the fiat spec (its ghost
      [out] is fixed by [ecancel_assumption], so the length obligation
      is closed afterwards by [ws2bs_felem_length]), then rebuild both
      leaves at the source witness — which is what the copy leaves in
      both buffers. *)
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
    intros functions Hcopy pDst pSrc v old R0 tr0 m0 Hsep.
    (* peel the source leaf *)
    assert (Hs : (FElem (Some tight_bounds) pSrc v
                  * (FElem (Some tight_bounds) pDst old * R0))%sep m0)
      by ecancel_assumption.
    destruct (FElem2_elim_frame _ _ _ _ _ Hs) as (xs & Hfe_s & Hbd_s & Hs').
    (* peel the destination leaf *)
    assert (Hd : (FElem (Some tight_bounds) pDst old
                  * (Field.FElem pSrc xs * R0))%sep m0)
      by ecancel_assumption.
    destruct (FElem2_elim_frame _ _ _ _ _ Hd) as (xd & Hfe_d & Hbd_d & Hd').
    cbv [Compilation2.maybe_bounded] in Hbd_s, Hbd_d.
    (* the destination buffer as bytes, as the fiat spec wants it *)
    seprewrite_in (felem_to_bytes pDst xd) Hd'.
    eapply Semantics.weaken_call.
    1: { eapply Hcopy.
         split; [ ecancel_assumption | apply ws2bs_felem_length ]. }
    intros tr' m' rets Hpost. cbv beta in Hpost.
    destruct Hpost as (Hrets & Htr & Hpost).
    split; [exact Hrets|]. split; [exact Htr|].
    (* both buffers now hold the source witness *)
    assert (H1 : (FElem (Some tight_bounds) pSrc v
                  * (Field.FElem pDst xs * R0))%sep m')
      by (apply (FElem2_intro_frame tight_bounds pSrc xs v _ _ Hfe_s Hbd_s);
          ecancel_assumption).
    assert (H2 : (FElem (Some tight_bounds) pDst v
                  * (FElem (Some tight_bounds) pSrc v * R0))%sep m')
      by (apply (FElem2_intro_frame tight_bounds pDst xs v _ _ Hfe_s Hbd_s);
          ecancel_assumption).
    ecancel_assumption.
  Qed.

  (* ---- HOpp (shape adapter, G4) ----------------------------------- *)

  (** From fiat-crypto's [unop_spec un_opp] (input tight, output loose,
      byte-array destination); loose -> tight by [Hbounds_eq].

      The unop precondition is a four-way conjunction whose second
      conjunct constrains the length of the ghost byte list [out];
      [out] is only fixed by the fourth conjunct, so the length goal is
      deferred (empty branch) and closed after the sep goals have run.
      The unop postcondition keeps only [FElem pout * Rr], so the input
      leaf is carried inside [Rr]. *)
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
    intros functions Hopp pOut pIn Y Yold R0 tr0 m0 Hsep.
    assert (Hi : (FElem (Some tight_bounds) pIn Y
                  * (FElem (Some tight_bounds) pOut Yold * R0))%sep m0)
      by ecancel_assumption.
    destruct (FElem2_elim_frame _ _ _ _ _ Hi) as (xi & Hfe_i & Hbd_i & Hi').
    assert (Ho : (FElem (Some tight_bounds) pOut Yold
                  * (Field.FElem pIn xi * R0))%sep m0)
      by ecancel_assumption.
    destruct (FElem2_elim_frame _ _ _ _ _ Ho) as (xo & Hfe_o & Hbd_o & Ho').
    cbv [Compilation2.maybe_bounded] in Hbd_i, Hbd_o.
    seprewrite_in (felem_to_bytes pOut xo) Ho'.
    eapply Semantics.weaken_call.
    1: { eapply Hopp.
         ssplit;
           [ exact Hbd_i
           | (* length of the ghost byte list: deferred *)
           | eexists; ecancel_assumption
           | ecancel_assumption ].
         apply ws2bs_felem_length. }
    intros tr' m' rets Hpost. cbv beta in Hpost.
    destruct Hpost as (Hrets & Htr & xres & Hfe_res & Hbd_res & Hpost).
    split; [exact Hrets|]. split; [exact Htr|].
    (* The postcondition states the result bound as [un_outbounds],
       the record projection of [un_opp], not as the literal
       [loose_bounds] — so rewrite on the goal (where [tight_bounds] is
       literal) and let [exact] do the delta on the hypothesis. *)
    assert (Hbd_res' : bounded_by tight_bounds xres)
      by (first
            [ exact Hbd_res
            | (rewrite <- Hbounds_eq; exact Hbd_res)
            | (cbn [un_outbounds un_opp] in Hbd_res;
               rewrite Hbounds_eq in Hbd_res; exact Hbd_res)
            | (cbv [un_outbounds un_opp] in Hbd_res;
               rewrite Hbounds_eq in Hbd_res; exact Hbd_res) ]).
    assert (Hfe_res' : feval xres = F.opp Y)
      by (first
            [ (rewrite Hfe_res, Hfe_i; reflexivity)
            | (cbn [un_model un_opp] in Hfe_res;
               rewrite Hfe_res, Hfe_i; reflexivity)
            | (cbv [un_model un_opp] in Hfe_res;
               rewrite Hfe_res, Hfe_i; reflexivity) ]).
    assert (H1 : (FElem (Some tight_bounds) pOut (F.opp Y)
                  * (Field.FElem pIn xi * R0))%sep m')
      by (apply (FElem2_intro_frame tight_bounds pOut xres (F.opp Y) _ _
                   Hfe_res' Hbd_res');
          ecancel_assumption).
    assert (H2 : (FElem (Some tight_bounds) pIn Y
                  * (FElem (Some tight_bounds) pOut (F.opp Y) * R0))%sep m')
      by (apply (FElem2_intro_frame tight_bounds pIn xi Y _ _ Hfe_i Hbd_i);
          ecancel_assumption).
    ecancel_assumption.
  Qed.

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

  (** [iff1] symmetry: coqutil defines [Lift1Prop.iff1] but this
      bedrock2 exports no named symmetry lemma, and [seprewrite_in <- H]
      is not accepted here — so state it locally and pass it explicitly. *)
  Lemma symmetry_iff1 {T} (P Q : T -> Prop) :
    Lift1Prop.iff1 P Q -> Lift1Prop.iff1 Q P.
  Proof. intros H x; split; apply H. Qed.

  (** Locals lookups in a [map.put] chain, and the argument-list
      evaluation of a call whose arguments mix variables and literals —
      which [straightline] does not consume, leaving the goal as the
      existential [exists args, dexprs .. args /\ Semantics.call ..]. *)
  Local Ltac solve_mapget :=
    first [ apply map.get_put_same
          | (rewrite !map.get_put_diff by congruence;
             first [ apply map.get_put_same | eassumption | reflexivity ])
          | eassumption
          | reflexivity ].

  Local Ltac eval_call_args :=
    (* The locals map after a call is a LET-BOUND variable
       ([l' := #{ ... }#]); [map.get] cannot see the put-chain through
       the binder, so unfold every locals let before looking up. *)
    repeat match goal with
           | x := _ : @Interface.map.rep _ _ _ |- _ => subst x
           end;
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.dexpr
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | (eexists; split; [ solve [ solve_mapget ] | ])
      | (eexists; split; [ exact eq_refl | ]) ]).

  (** One [from_word] call: re-expose the command head (the entry [cbv]
      leaves [cmd.seq] folded), let [straightline] resolve what it can,
      discharge the argument existential, then apply the callee spec.
      The callee-goal head is matched both as [WeakestPrecondition.call]
      and as [Semantics.call], and the fallback FAILS rather than
      skipping: a silent skip here looks like a successful body and only
      shows up much later, at the postcondition, as untouched buffers. *)
  Local Ltac wp_from_word_call Hspec :=
    try (unfold1_cmd_goal;
         cbv beta match delta [WeakestPrecondition.cmd_body]);
    repeat straightline;
    try (lazymatch goal with
         | |- exists _, _ /\ _ =>
             eexists; split; [ solve [ eval_call_args ] | ]
         end);
    lazymatch goal with
    | |- WeakestPrecondition.call _ _ _ _ _ _ =>
        first
          [ (straightline_call;
             try (solve [ split;
                          [ ecancel_assumption | apply ws2bs_felem_length ] ]))
          | (eapply Semantics.weaken_call;
             [ eapply Hspec;
               split; [ ecancel_assumption | apply ws2bs_felem_length ]
             | intros ? ? ? ? ]) ]
    | |- Semantics.call _ _ _ _ _ _ =>
        eapply Semantics.weaken_call;
        [ eapply Hspec;
          split; [ ecancel_assumption | apply ws2bs_felem_length ]
        | intros ? ? ? ? ]
    | |- ?G => fail 1 "wp_from_word_call: no call goal exposed, got:" G
    end;
    (* The callee returns nothing, so its postcondition carries
       [rets = []].  Flatten the postcondition and substitute that
       equation SPECIFICALLY: a bare [subst] aborts (and, under [try],
       silently does nothing) if any other equation in context is not
       substitutable.  Once [rets] is [[]], [map.putmany_of_list_zip []
       [] l] computes to [Some l], so the locals stay the concrete
       [map.put] chain for the next call. *)
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : ?x = nil |- _ => is_var x; subst x
           | H : nil = ?x |- _ => is_var x; subst x
           end;
    repeat match goal with
           | H : map.putmany_of_list_zip [] [] ?l = Some ?l2 |- _ =>
               cbn [map.putmany_of_list_zip] in H;
               first [ (injection H as H; subst)
                     | (inversion H; subst; clear H) ]
           end;
    repeat straightline.

  (** Side conditions of the final rebuild, split out so a failure names
      which one failed rather than reporting the whole [eapply].
      [from_word] states its result as
      [feval X = F.of_Z _ (word.unsigned (word.of_Z c))]; the
      [etransitivity] branch normalises that to [F.of_Z _ c] on the fly,
      so it does not depend on the earlier rewrite pass having fired. *)
  Local Ltac solve_feval :=
    first [ eassumption
          | (etransitivity; [ eassumption | ];
             rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1;
             reflexivity)
          | (rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1;
             eassumption)
          | reflexivity ].

  Local Ltac solve_bounded := first [ eassumption | assumption ].

  Lemma store_zero_from_word_ok :
    forall functions,
      map.get functions "store_zero" = Some (snd store_zero_from_word_func) ->
      spec_of_from_word functions ->
      @StoreZero.spec_of_store_zero _ _ _ _ _ _
        field_parameters field_representation functions.
  Proof.
    intros functions Henv Hfw.
    cbv [StoreZero.spec_of_store_zero].
    intros pX pY pZ X Y Z R tr m0 Hpre.
    change CompilationAbstract.FElem with Compilation2.FElem in Hpre.
    (* Peel the three output buffers down to byte arrays, which is what
       [spec_of_from_word] writes into.  [maybe_bounded None] carries no
       information, so the witnesses' side conditions are dropped. *)
    assert (HX : (FElem None pX X
                  * (FElem None pY Y * (FElem None pZ Z * R)))%sep m0)
      by ecancel_assumption.
    destruct (FElem2_elim_frame _ _ _ _ _ HX) as (xX & _ & _ & HX').
    assert (HY : (FElem None pY Y
                  * (Field.FElem pX xX * (FElem None pZ Z * R)))%sep m0)
      by ecancel_assumption.
    destruct (FElem2_elim_frame _ _ _ _ _ HY) as (xY & _ & _ & HY').
    assert (HZ : (FElem None pZ Z
                  * (Field.FElem pX xX * (Field.FElem pY xY * R)))%sep m0)
      by ecancel_assumption.
    destruct (FElem2_elim_frame _ _ _ _ _ HZ) as (xZ & _ & _ & HZ').
    seprewrite_in (felem_to_bytes pX xX) HZ'.
    seprewrite_in (felem_to_bytes pY xY) HZ'.
    seprewrite_in (felem_to_bytes pZ xZ) HZ'.
    clear HX HY HZ HX' HY'.
    (* Function entry, then the three [from_word] calls. *)
    eapply WeakestPreconditionProperties.start_func;
      [ exact Henv | clear Henv ].
    cbv match beta delta
      [WeakestPrecondition.func store_zero_from_word_func snd].
    eexists. split. { reflexivity. }
    wp_from_word_call Hfw.
    wp_from_word_call Hfw.
    wp_from_word_call Hfw.
    (* [from_word] returns [F.of_Z _ (word.unsigned (word.of_Z c))];
       normalise to the [F.of_Z _ 0] / [F.of_Z _ 1] of the store_zero
       postcondition. *)
    repeat match goal with
           | H : context [word.unsigned (word.of_Z 0)] |- _ =>
               rewrite word.unsigned_of_Z_0 in H
           | H : context [word.unsigned (word.of_Z 1)] |- _ =>
               rewrite word.unsigned_of_Z_1 in H
           end.
    (* Drop the pre-call facts.  They speak about the same three
       pointers at the OLD memory with the original witnesses, so they
       are matched FIRST both by the reverse transport below and by
       [ecancel_assumption]. *)
    try clear HZ'.
    try clear Hpre.
    (* Safety net, now that only post-call hypotheses remain: fold any
       buffer still held as a byte array back into a [Field.FElem]
       leaf.  A no-op once the three calls have written their results. *)
    repeat match goal with
           | H : sep _ _ _ |- _ =>
               progress (first [ seprewrite_in (symmetry_iff1 (felem_to_bytes pX xX)) H
                               | seprewrite_in (symmetry_iff1 (felem_to_bytes pY xY)) H
                               | seprewrite_in (symmetry_iff1 (felem_to_bytes pZ xZ)) H ])
           end.
    change CompilationAbstract.FElem with Compilation2.FElem.
    ssplit; try reflexivity.
    (* Rebuild the three [FElem] leaves at the post-call witnesses.  Try
       both associations of the goal's sep tree; [eapply] cannot
       reassociate [sep], and which shape the call plumbing leaves is
       not predictable. *)
    first
      [ eapply FElem2_intro3R;
          [ ecancel_assumption
          | solve_feval | solve_bounded
          | solve_feval | solve_bounded
          | solve_feval | solve_bounded ]
      | eapply FElem2_intro3;
          [ ecancel_assumption
          | solve_feval | solve_bounded
          | solve_feval | solve_bounded
          | solve_feval | solve_bounded ]
      | lazymatch goal with
        | |- ?G => fail 99 "store_zero: final FElem rebuild failed on:" G
        end ].
  Qed.

End Specs.
