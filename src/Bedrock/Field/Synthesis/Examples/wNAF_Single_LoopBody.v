(** * Single-scalar wNAF loop body ��� algebraic lemmas + WP proof skeleton.

    Mirrors [BLS12_wNAF_GLV_LoopBody.v] but for single-scalar wNAF
    (one digit stream, one table, no GLV). Simpler invariant:
      acc = scmul(weighted_sum(skipn n dk)) P

    This file is GENERIC — parameterized by field_parameters.
    Works for BN254, BN256, P-256, or any curve without GLV.

    ** G6 (projective equivalence) **

    The loop invariant is stated up to the Section-parametric
    equivalence [pt_eq], not Leibniz equality on raw triples, and it
    carries an [oncurve] conjunct.  Both are forced: the
    Renes-Costello-Batina addition satisfies the group laws only up to
    projective equivalence, and [oncurve] is not [pt_eq]-invariant, so
    it cannot be recovered from the equation.  The sep-logic (memory)
    part of every statement stays Leibniz — only the point-level algebra
    is quotiented.

    Instantiating [pt_eq := eq], [oncurve := fun _ => True] recovers the
    previous interface.

    ** G5 (negation name) **

    The name of the aliasing-tolerant in-place negation is the Section
    parameter [opp_name], no longer the [FieldParameters] field [opp]:
    the fiat-crypto synthesis of [opp] has no aliasing spec, so the NIST
    chain must call [NistWnafWrappers.opp_inplace_func] instead. *)

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
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

(** ** Horner step for single scalar *)

Lemma single_weighted_sum_cons d rest :
  weighted_sum (d :: rest) 0 = d + 2 * weighted_sum rest 0.
Proof.
  unfold weighted_sum at 1. fold weighted_sum.
  rewrite weighted_sum_succ. lia.
Qed.

Lemma single_skipn_cons_nth {A} (n : nat) (l : list A) (d : A) :
  (n < length l)%nat ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  revert l. induction n as [|n' IH]; intros l Hlt.
  - destruct l; simpl in *; [lia|reflexivity].
  - destruct l as [|x rest]; simpl in *; [lia|].
    apply IH. lia.
Qed.

Theorem single_wnaf_horner_step dk n :
  (n < length dk)%nat ->
  weighted_sum (skipn n dk) 0 =
    nth n dk 0 + 2 * weighted_sum (skipn (S n) dk) 0.
Proof.
  intros Hlt.
  rewrite (single_skipn_cons_nth n dk 0 Hlt).
  apply single_weighted_sum_cons.
Qed.

(** ** Loop body WP proof *)

Section SingleLoopBodyProof.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters} {field_representation : FieldRepresentation}.
  Context {field_parameters_ok : FieldParameters_ok} {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z := (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  Context (curve_add_name curve_double_name opp_name : string).
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.

  (** *** G6: the point-level equivalence and the on-curve predicate.

      [curve_add_id_r] and [curve_add_comm] were declared here but never
      used by [wnaf_single_loop_body_ok]; they are dropped so that the
      Section-discharged argument list is unambiguous. *)
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

  (** Explicit projections of [pt_eq_equiv]: [curve_add_Proper] carries
      [oncurve] side conditions and so is not a [Proper] instance, hence
      no setoid tactics. *)
  Local Lemma pt_refl : forall P, pt_eq P P.
  Proof. destruct pt_eq_equiv as [Hr _ _]. exact Hr. Qed.
  Local Lemma pt_sym : forall P Q, pt_eq P Q -> pt_eq Q P.
  Proof. destruct pt_eq_equiv as [_ Hs _]. exact Hs. Qed.
  Local Lemma pt_trans : forall P Q R, pt_eq P Q -> pt_eq Q R -> pt_eq P R.
  Proof. destruct pt_eq_equiv as [_ _ Ht]. exact Ht. Qed.

  Local Lemma add_id_l' : forall P,
    oncurve P -> pt_eq (curve_add (Fzero,Fone,Fzero) P) P.
  Proof. intros [[x y] z] H. apply curve_add_id_l. exact H. Qed.

  (** The two computation rules of [scmul_s], as rewrite lemmas: the
      unifier is not asked to delta-unfold [scmul] under [oncurve]. *)
  Local Lemma scmul_s_O : forall P, scmul_s 0%nat P = (Fzero,Fone,Fzero).
  Proof. intros. reflexivity. Qed.
  Local Lemma scmul_s_S : forall n P,
    scmul_s (S n) P = curve_add P (scmul_s n P).
  Proof. intros. reflexivity. Qed.

  Local Lemma oncurve_scmul : forall n P, oncurve P -> oncurve (scmul_s n P).
  Proof.
    induction n as [|n' IH]; intros P HP.
    - rewrite scmul_s_O. exact oncurve_id.
    - rewrite scmul_s_S.
      apply oncurve_curve_add; [exact HP | apply IH; exact HP].
  Qed.

  (** [scmul_add] of BLS12_GLV_LoopInvariant.v, up to [pt_eq]. *)
  Local Lemma scmul_add_pt : forall a b P, oncurve P ->
    pt_eq (scmul_s (a + b)%nat P) (curve_add (scmul_s a P) (scmul_s b P)).
  Proof.
    induction a as [|a' IH]; intros b P HP.
    - rewrite scmul_s_O. simpl (0 + b)%nat.
      apply pt_sym. apply add_id_l'. apply oncurve_scmul. exact HP.
    - replace (S a' + b)%nat with (S (a' + b)%nat) by lia.
      rewrite !scmul_s_S.
      apply (pt_trans
               (curve_add P (scmul_s (a' + b)%nat P))
               (curve_add P (curve_add (scmul_s a' P) (scmul_s b P)))
               (curve_add (curve_add P (scmul_s a' P)) (scmul_s b P))).
      + apply curve_add_Proper;
          [ exact HP | exact HP
          | apply oncurve_scmul; exact HP
          | apply oncurve_curve_add; apply oncurve_scmul; exact HP
          | apply pt_refl
          | apply IH; exact HP ].
      + apply curve_add_assoc;
          [ exact HP | apply oncurve_scmul; exact HP
          | apply oncurve_scmul; exact HP ].
  Qed.

  Variable functions : map.rep (map := Semantics.env).

  (** In-place doubling *)
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

  (** Aliased curve_add *)
  Context (HCurveAddInplace : forall pXo pX2 pYo pY2 pZo pZ2
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

  Context (HFelemCopy : forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pSrc v ⋆ FElem (Some tight_bounds) pDst old ⋆ R0) m0 ->
    Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pSrc v ⋆ FElem (Some tight_bounds) pDst v ⋆ R0) m')).

  Context (HOpp : forall pOut pIn (Y : F) (Yold : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pIn Y ⋆ FElem (Some tight_bounds) pOut Yold ⋆ R0) m0 ->
    Semantics.call functions opp_name tr0 m0 [pOut; pIn]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pIn Y ⋆ FElem (Some tight_bounds) pOut (F.opp Y) ⋆ R0) m')).

  (** Single digit stream and point.

      [Hlen : length dk = num_iters] used to be declared here.  It is
      not needed by [wnaf_single_loop_body_ok] (only [num_iters] bounds
      the iteration), and being a ground nat equation it was silently
      collected by [lia]/[zify] into the discharged argument list.  It
      is removed so that list is determined by genuine use. *)
  Context (dk : list Z).
  Context (Px Py Pz : F).
  Context (Honcurve_P : oncurve (Px,Py,Pz)).
  Context (num_iters : nat).

  Context (Hws_nn :
    forall n, (n <= num_iters)%nat -> 0 <= weighted_sum (skipn n dk) 0).

  Context (table_entries : list (F * F * F)).

  (** Abstract hypothesis for processing one digit.
      After iter-- and curve_double, the remaining loop body is:
        load d, process_one_digit d.
      This hypothesis abstracts the load + process into one WP statement. *)
  Context (HProcessDigit : forall (n : nat) pOx pOy pOz pAx pAy pAz
    pT pDK (Ox Oy Oz Ax Ay Az : F) Rinner tr0 m0 l0,
    (n < num_iters)%nat ->
    oncurve (Ox,Oy,Oz) ->
    pt_eq (Ox,Oy,Oz) (scmul_s (Z.to_nat (2 * weighted_sum (skipn (S n) dk) 0)) (Px,Py,Pz)) ->
    (FElem (Some tight_bounds) pOx Ox ⋆ FElem (Some tight_bounds) pOy Oy
     ⋆ FElem (Some tight_bounds) pOz Oz ⋆ FElem (Some tight_bounds) pAx Ax
     ⋆ FElem (Some tight_bounds) pAy Ay ⋆ FElem (Some tight_bounds) pAz Az
     ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries
     ⋆ Rinner) m0 ->
    map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
    map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
    map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
    map.get l0 "table_P" = Some pT ->
    map.get l0 "digits_k" = Some pDK ->
    map.get l0 "iter" = Some (word.of_Z (Z.of_nat n)) ->
    WeakestPrecondition.cmd functions
      (cmd.seq
        (cmd.set "d" (expr.load access_size.word
          (expr.op bopname.add (expr.var "digits_k")
            (expr.op bopname.mul (expr.var "iter")
              (expr.literal (Memory.bytes_per_word 64))))))
        (process_one_digit curve_add_name felem_copy opp_name felem_size_in_bytes
          "d" "table_P" "auxx" "auxy" "auxz" "outx" "outy" "outz"))
      tr0 m0 l0
      (fun t' m' l' =>
        exists Ox' Oy' Oz' Ax' Ay' Az',
        oncurve (Ox',Oy',Oz')
        /\ pt_eq (Ox',Oy',Oz') (scmul_s (Z.to_nat (weighted_sum (skipn n dk) 0)) (Px,Py,Pz))
        /\ (FElem (Some tight_bounds) pOx Ox' ⋆ FElem (Some tight_bounds) pOy Oy'
            ⋆ FElem (Some tight_bounds) pOz Oz' ⋆ FElem (Some tight_bounds) pAx Ax'
            ⋆ FElem (Some tight_bounds) pAy Ay' ⋆ FElem (Some tight_bounds) pAz Az'
            ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries
            ⋆ Rinner) m'
        /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
        /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
        /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
        /\ map.get l' "table_P" = Some pT
        /\ map.get l' "digits_k" = Some pDK
        /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
        /\ tr0 = t')).

  (** The main theorem: single-scalar wnaf_single_loop_body satisfies HLoopBody.
      Composes iter--, curve_double, HProcessDigit,
      and the single-scalar Horner step. *)
  Theorem wnaf_single_loop_body_ok :
    forall (n : nat) pOx pOy pOz pAx pAy pAz pT pDK
      (Ox Oy Oz Ax Ay Az : F) Rinner tr0 m0 l0,
      (n < num_iters)%nat ->
      oncurve (Ox,Oy,Oz) ->
      pt_eq (Ox,Oy,Oz) (scmul_s (Z.to_nat (weighted_sum (skipn (S n) dk) 0)) (Px,Py,Pz)) ->
      (Point3 (Some tight_bounds) pOx pOy pOz Ox Oy Oz
       ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax Ay Az
       ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries
       ⋆ Rinner) m0 ->
      map.get l0 "outx" = Some pOx -> map.get l0 "outy" = Some pOy ->
      map.get l0 "outz" = Some pOz -> map.get l0 "auxx" = Some pAx ->
      map.get l0 "auxy" = Some pAy -> map.get l0 "auxz" = Some pAz ->
      map.get l0 "table_P" = Some pT ->
      map.get l0 "digits_k" = Some pDK ->
      map.get l0 "iter" = Some (word.of_Z (Z.of_nat (S n))) ->
      WeakestPrecondition.cmd functions
        (wnaf_single_loop_body curve_add_name curve_double_name
           felem_copy opp_name felem_size_in_bytes
           "digits_k" "table_P")
        tr0 m0 l0
        (fun t' m' l' =>
          exists Ox' Oy' Oz' Ax' Ay' Az',
          oncurve (Ox',Oy',Oz')
          /\ pt_eq (Ox',Oy',Oz') (scmul_s (Z.to_nat (weighted_sum (skipn n dk) 0)) (Px,Py,Pz))
          /\ (Point3 (Some tight_bounds) pOx pOy pOz Ox' Oy' Oz'
              ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az'
              ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries
              ⋆ Rinner) m'
          /\ map.get l' "outx" = Some pOx /\ map.get l' "outy" = Some pOy
          /\ map.get l' "outz" = Some pOz /\ map.get l' "auxx" = Some pAx
          /\ map.get l' "auxy" = Some pAy /\ map.get l' "auxz" = Some pAz
          /\ map.get l' "table_P" = Some pT
          /\ map.get l' "digits_k" = Some pDK
          /\ map.get l' "iter" = Some (word.of_Z (Z.of_nat n))
          /\ tr0 = t').
  Proof.
    intros n pOx pOy pOz pAx pAy pAz pT pDK
      Ox Oy Oz Ax Ay Az Rinner tr0 m0 l0
      Hn Hoc Hinv Hsep Hl_ox Hl_oy Hl_oz Hl_ax Hl_ay Hl_az
      Hl_t Hl_dk Hl_iter.
    unfold wnaf_single_loop_body.
    (* Step 1: iter-- *)
    repeat straightline.
    eexists; split;
      [cbv [DEXPR WeakestPrecondition.dexpr
            WeakestPrecondition.expr WeakestPrecondition.expr_body
            WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
       eexists; split; [exact Hl_iter|]; exact eq_refl|].
    cbv [dlet.dlet].
    (* Step 2: curve_double(out, out) *)
    repeat straightline.
    eexists; split;
      [cbv [dexprs list_map list_map_body
            WeakestPrecondition.expr WeakestPrecondition.expr_body
            WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_ox|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_oy|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_oz|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_ox|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_oy|];
       eexists; split; [rewrite map.get_put_diff by congruence; exact Hl_oz|];
       exact eq_refl|].
    eapply Semantics.weaken_call;
      [eapply HCurveDouble; ecancel_assumption_impl|].
    intros t1 m1 rets1 [Hrets1 [Htr1 Hsep1]].
    subst rets1. symmetry in Htr1. subst t1.
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl|].
    (* After doubling: out = curve_add(Ox,Oy,Oz)(Ox,Oy,Oz). *)
    set (doubled := curve_add (Ox, Oy, Oz) (Ox, Oy, Oz)) in Hsep1.
    destruct doubled as [[Dx Dy] Dz] eqn:Hdoubled.
    set (iter_word := word.sub (word.of_Z (Z.of_nat (S n))) (word.of_Z 1)).
    assert (Hiter_n : iter_word = word.of_Z (Z.of_nat n))
      by (unfold iter_word; rewrite <- word.ring_morph_sub; f_equal; lia).
    (* Prove doubling precondition for HProcessDigit:
       (Dx,Dy,Dz) is on-curve and pt_eq to scmul_s(2 * ws) P. *)
    assert (Hdbl_eq : curve_add (Ox, Oy, Oz) (Ox, Oy, Oz) = (Dx, Dy, Dz)).
    { unfold doubled in Hdoubled. exact Hdoubled. }
    assert (Hdbl_oc : oncurve (Dx, Dy, Dz)).
    { rewrite <- Hdbl_eq. apply oncurve_curve_add; exact Hoc. }
    assert (Hdbl_acc : pt_eq (Dx, Dy, Dz)
             (scmul_s (Z.to_nat (2 * weighted_sum (skipn (S n) dk) 0)) (Px,Py,Pz))).
    { assert (Hdouble_nat :
        Z.to_nat (2 * weighted_sum (skipn (S n) dk) 0)
        = (Z.to_nat (weighted_sum (skipn (S n) dk) 0)
           + Z.to_nat (weighted_sum (skipn (S n) dk) 0))%nat).
      { rewrite Z2Nat.inj_mul; [simpl Z.to_nat; lia | lia |].
        apply Hws_nn. lia. }
      rewrite Hdouble_nat, <- Hdbl_eq.
      apply (pt_trans
               (curve_add (Ox,Oy,Oz) (Ox,Oy,Oz))
               (curve_add
                  (scmul_s (Z.to_nat (weighted_sum (skipn (S n) dk) 0)) (Px,Py,Pz))
                  (scmul_s (Z.to_nat (weighted_sum (skipn (S n) dk) 0)) (Px,Py,Pz)))
               (scmul_s (Z.to_nat (weighted_sum (skipn (S n) dk) 0)
                         + Z.to_nat (weighted_sum (skipn (S n) dk) 0))%nat
                        (Px,Py,Pz))).
      - apply curve_add_Proper;
          [ exact Hoc | apply oncurve_scmul; exact Honcurve_P
          | exact Hoc | apply oncurve_scmul; exact Honcurve_P
          | exact Hinv | exact Hinv ].
      - apply pt_sym. apply scmul_add_pt. exact Honcurve_P. }
    (* Reassociate sep for HProcessDigit *)
    assert (Hsep1' : (FElem (Some tight_bounds) pOx Dx
      ⋆ FElem (Some tight_bounds) pOy Dy ⋆ FElem (Some tight_bounds) pOz Dz
      ⋆ FElem (Some tight_bounds) pAx Ax ⋆ FElem (Some tight_bounds) pAy Ay
      ⋆ FElem (Some tight_bounds) pAz Az
      ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries
      ⋆ Rinner) m1) by ecancel_assumption.
    (* Step 3: Apply HProcessDigit *)
    eapply WeakestPreconditionProperties.Proper_cmd;
      [|exact (HProcessDigit n pOx pOy pOz pAx pAy pAz pT pDK
                Dx Dy Dz Ax Ay Az Rinner tr0 m1 (map.put l0 "iter" iter_word)
                Hn Hdbl_oc Hdbl_acc Hsep1'
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_ox)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_oy)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_oz)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_ax)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_ay)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_az)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_t)
                ltac:(rewrite map.get_put_diff by congruence; exact Hl_dk)
                ltac:(rewrite map.get_put_same; f_equal; exact Hiter_n))].
    (* Weaken postcondition: convert flat FElem sep to Point3 notation *)
    intros t2 m2 l2 (Ox2 & Oy2 & Oz2 & Ax2 & Ay2 & Az2 &
      Hoc2 & Hout2 & Hsep2 & Hlox2 & Hloy2 & Hloz2 &
      Hlax2 & Hlay2 & Hlaz2 & Hlt2 &
      Hldk2 & Hliter2 & Htr2).
    subst t2.
    exists Ox2, Oy2, Oz2, Ax2, Ay2, Az2.
    repeat split; try assumption.
    ecancel_assumption.
  Qed.

End SingleLoopBodyProof.
