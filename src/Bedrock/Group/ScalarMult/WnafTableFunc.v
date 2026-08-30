(** * The memory half of gap G7: a bedrock2 body that POPULATES the
      wNAF precomputation table.

    [WnafTableBuild.rcb_table4_ok] (Qed) closes the ALGEBRAIC half of
    the chain's table obligation: the four-entry list
    [rcb_build_table4 P] has length 4 and its entries are on the curve
    and [pt_eq] to [1P;3P;5P;7P].  It says nothing about memory.

    This file closes the memory half.  [precompute_table4_body] is a
    straight-line bedrock2 command over the two wrappers of
    NistWnafWrappers.v ([felem_copy] at the [FElem] layer, and the
    aliasing "curve_add" whose output is its first operand), and
    [precompute_table4_body_ok] says: run it on a caller-supplied
    table buffer described by [BLS12_wNAF_ProcessDigits.Table4], a
    three-word scratch point, and the base point [P], and the buffer
    afterwards holds [table4_of P], which is [rcb_build_table4] at the
    same curve constants ([table4_of_is_rcb], by conversion).

    Route.  A Rupicola [Derive] (the PointDoubleA0.v style) is not
    usable here: Rupicola's output discipline binds each [let/n] output
    to a bedrock2 LOCAL variable, whereas the twelve outputs of this
    function are field elements at COMPUTED OFFSETS inside one
    caller-supplied buffer; there is no compilation lemma for the
    nine-argument aliasing "curve_add" ABI; and the postcondition is
    [Table4], a hand-written separation predicate outside Rupicola's
    [predicate] shape.  The direct weakest-precondition proof reuses
    [NistWnafWrappers.felem_copy_HFelemCopy] and
    [spec_of_curve_add_inplace_general], both already Qed, so every one
    of the nineteen calls is one [ecancel_assumption].

    Layout:
      §1  Addresses and the body.
      §2  The Gallina table [table4_of] and its two conversions.
      §3a [curve_add_triple], the addition wrapper without the tuple let.
      §3b Per-call plumbing (copied from NistWnafWrappers.v §3).
      §3c [wp_seq] / [wp_cp_step] / [wp_add_step]: one lemma per
          statement shape, so §4 is nineteen uniform lines and never
          reasons about [tcoord] or about [cmd_body] by hand.
      §4  [precompute_table4_body_ok].

    The P-256 instantiation, and the composition that turns
    [P256_wNAF_Instance.p256_table_ok] from a hypothesis into a
    theorem, are in P256_wNAF_TableFunc.v.

    Honesty ledger: no [Admitted] and no [Axiom]. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Require Import Bedrock.Group.ScalarMult.WnafTableBuild.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ==================================================================== *)
(** ** 1. Addresses and the body                                         *)
(* ==================================================================== *)

Section Body.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width}
          {mem : map.map word Byte.byte}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  (** The address of coordinate [j] of table entry [i], as a bedrock2
      expression.  The two nested additions and the two literals are
      written so that the value is SYNTACTICALLY
      [felem_addr (table_point_addr base i) j] — the address
      [BLS12_wNAF_ProcessDigits.Table4] puts that field element at — so
      no word-arithmetic rewriting is needed anywhere in §4. *)
  Definition tcoord (base : String.string) (i j : nat) : Syntax.expr :=
    expr.op bopname.add
      (expr.op bopname.add (expr.var base)
         (expr.literal (Z.of_nat i * (3 * felem_size_in_bytes))))
      (expr.literal (Z.of_nat j * felem_size_in_bytes)).

  Local Notation E i j := (tcoord "table_P" i j).
  Local Notation cp d s := (cmd.call []%list felem_copy [d; s]).
  Local Notation cadd3 ox oy oz ax ay az :=
    (cmd.call []%list "curve_add" [ox; ax; oy; ay; oz; az; ox; oy; oz]).

  (** Locals read: "table_P" (the buffer), "tmpx"/"tmpy"/"tmpz" (a
      scratch point, which a caller may take to be the wNAF driver's
      own aux point), "px"/"py"/"pz" (the base point).

      Schedule (19 calls, 4 additions — the cost [WNAFTable.precompute_w4]
      advertises):
        e0   := P
        tmp  := P ; tmp += P            (* tmp = 2P *)
        e1   := e0 ; e1  += tmp         (* 3P *)
        e2   := e1 ; e2  += tmp         (* 5P *)
        e3   := e2 ; e3  += tmp         (* 7P *) *)
  Definition precompute_table4_body : Syntax.cmd.cmd :=
    cmd.seq (cp (E 0 0) (expr.var "px"))
   (cmd.seq (cp (E 0 1) (expr.var "py"))
   (cmd.seq (cp (E 0 2) (expr.var "pz"))
   (cmd.seq (cp (expr.var "tmpx") (expr.var "px"))
   (cmd.seq (cp (expr.var "tmpy") (expr.var "py"))
   (cmd.seq (cp (expr.var "tmpz") (expr.var "pz"))
   (cmd.seq (cadd3 (expr.var "tmpx") (expr.var "tmpy") (expr.var "tmpz")
                   (expr.var "px") (expr.var "py") (expr.var "pz"))
   (cmd.seq (cp (E 1 0) (E 0 0))
   (cmd.seq (cp (E 1 1) (E 0 1))
   (cmd.seq (cp (E 1 2) (E 0 2))
   (cmd.seq (cadd3 (E 1 0) (E 1 1) (E 1 2)
                   (expr.var "tmpx") (expr.var "tmpy") (expr.var "tmpz"))
   (cmd.seq (cp (E 2 0) (E 1 0))
   (cmd.seq (cp (E 2 1) (E 1 1))
   (cmd.seq (cp (E 2 2) (E 1 2))
   (cmd.seq (cadd3 (E 2 0) (E 2 1) (E 2 2)
                   (expr.var "tmpx") (expr.var "tmpy") (expr.var "tmpz"))
   (cmd.seq (cp (E 3 0) (E 2 0))
   (cmd.seq (cp (E 3 1) (E 2 1))
   (cmd.seq (cp (E 3 2) (E 2 2))
            (cadd3 (E 3 0) (E 3 1) (E 3 2)
                   (expr.var "tmpx") (expr.var "tmpy") (expr.var "tmpz"))
   ))))))))))))))))).

  (** The same body as a bedrock2 function, for callers that want a
      separate compilation unit rather than an inlined command. *)
  Definition precompute_table4_func
    : String.string * (list String.string * list String.string * Syntax.cmd.cmd) :=
    ("precompute_table4",
     (["table_P"; "tmpx"; "tmpy"; "tmpz"; "px"; "py"; "pz"],
      []%list, precompute_table4_body)).

End Body.

(* ==================================================================== *)
(** ** 2. The Gallina table                                              *)
(* ==================================================================== *)

Section Table.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width}
          {mem : map.map word Byte.byte}
          {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.
  Context (three_b a_const : felem).

  Local Notation F := (F M_pos).
  Local Notation Add := (@curve_add_g _ _ _ _ _ _ three_b a_const).

  Definition table4_of (P : F * F * F) : list (F * F * F) :=
    build_odd_table_gen Add 4%nat P.

  (** The four entries, unfolded.  [reflexivity] because
      [build_odd_table_gen] / [build_aux] are structural on the literal
      [4%nat]. *)
  Lemma table4_of_eq (P : F * F * F) :
    table4_of P
    = [ P;
        Add P (Add P P);
        Add (Add P (Add P P)) (Add P P);
        Add (Add (Add P (Add P P)) (Add P P)) (Add P P) ].
  Proof. reflexivity. Qed.

  Lemma table4_of_length (P : F * F * F) : length (table4_of P) = 4%nat.
  Proof. reflexivity. Qed.

  (** [WnafTableBuild.rcb_build_table4] is built over
      [RcbProjectiveLaws.cadd], whose body is that of
      [NistWnafWrappers.curve_add_general_triple]; [curve_add_g] is the
      latter at the [feval]s of the two stored constants.  So the two
      tables are the same term up to delta. *)
  Lemma table4_of_is_rcb (P : F * F * F) :
    table4_of P
    = rcb_build_table4 (feval (proj1_sig a_const))
                       (feval (proj1_sig three_b)) P.
  Proof. reflexivity. Qed.

End Table.

(* ==================================================================== *)
(** ** 3./4. The weakest-precondition proof                              *)
(* ==================================================================== *)

Section Proof.
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
  Context (three_b a_const : felem).

  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Pt3 px py pz X Y Z :=
    (FElem (Some tight_bounds) px X ⋆ FElem (Some tight_bounds) py Y
     ⋆ FElem (Some tight_bounds) pz Z)%sep.
  Local Notation Add := (@curve_add_g _ _ _ _ _ _ three_b a_const).

  (* ---- 3a. The addition wrapper without the [let '(_,_,_)] --------- *)

  (** [spec_of_curve_add_inplace_general] states its result through a
      [let '(Xo,Yo,Zo) := curve_add_g .. in ..], which does not reduce
      until the tuple is in constructor form.  This restatement takes
      the constructor form as a hypothesis instead, so §4 never has to
      destruct a [curve_add_g] application under a binder. *)
  Lemma curve_add_triple :
    forall functions,
      spec_of_curve_add_inplace_general three_b a_const functions ->
      forall pXo pYo pZo pX2 pY2 pZ2
             (X Y Z X2 Y2 Z2 Xo Yo Zo : F) R0 tr0 m0,
        Add (X, Y, Z) (X2, Y2, Z2) = (Xo, Yo, Zo) ->
        (Pt3 pXo pYo pZo X Y Z ⋆ Pt3 pX2 pY2 pZ2 X2 Y2 Z2 ⋆ R0)%sep m0 ->
        Semantics.call functions "curve_add" tr0 m0
          [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
          (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
            (Pt3 pXo pYo pZo Xo Yo Zo ⋆ Pt3 pX2 pY2 pZ2 X2 Y2 Z2
             ⋆ R0)%sep m').
  Proof.
    intros functions Hadd pXo pYo pZo pX2 pY2 pZ2 X Y Z X2 Y2 Z2 Xo Yo Zo
           R0 tr0 m0 Heq Hsep.
    eapply Semantics.weaken_call.
    1: { eapply Hadd. ecancel_assumption. }
    intros tr' m' rets Hp. cbv beta in Hp.
    rewrite Heq in Hp.
    destruct Hp as (Hr & Ht & Hm).
    split; [exact Hr|]. split; [exact Ht|].
    ecancel_assumption.
  Qed.

  (* ---- 3b. Call plumbing (NistWnafWrappers.v §3, verbatim) --------- *)

  Local Ltac solve_mapget :=
    first [ apply map.get_put_same
          | (rewrite !map.get_put_diff by congruence;
             first [ apply map.get_put_same | eassumption | reflexivity ])
          | eassumption
          | reflexivity ].

  Local Ltac eval_call_args :=
    repeat match goal with
           | x := _ : @Interface.map.rep _ _ _ |- _ => subst x
           end;
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.dexpr
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet
         Semantics.interp_binop tcoord];
    repeat (first
      [ exact eq_refl
      | (eexists; split; [ solve [ solve_mapget ] | ])
      | (eexists; split; [ exact eq_refl | ]) ]).

  Local Ltac wp_expose_call :=
    repeat (lazymatch goal with
            | |- WeakestPrecondition.cmd _ _ _ _ _ _ =>
                unfold1_cmd_goal;
                cbv beta match delta [WeakestPrecondition.cmd_body]
            end).

  (** One call: expose it, evaluate its argument expressions, discharge
      it with [lem], consume the three-way postcondition, drop the stale
      separation hypothesis [Hold], and re-enter the continuation. *)
  Local Ltac wp_call lem Hold Hnew :=
    wp_expose_call;
    (eexists; split; [ solve [ eval_call_args ] | ]);
    eapply Semantics.weaken_call; [ lem | ];
    let t' := fresh "t" in
    let m' := fresh "mm" in
    let r' := fresh "rr" in
    let Hr := fresh "Hr" in
    let Ht := fresh "Ht" in
    intros t' m' r' Hnew; cbv beta in Hnew;
    destruct Hnew as (Hr & Ht & Hnew);
    subst r'; subst t'; clear Hold;
    (eexists; split; [ exact eq_refl | ]).

  (* ---- 3c. Three one-step weakest-precondition lemmas -------------- *)

  (** [cmd.seq] is definitionally the continuation-passing composition,
      so this is [exact].  Stating it as a lemma keeps §4 free of
      [unfold1_cmd_goal], whose [repeat] would also unfold the call
      that the two step lemmas below are supposed to consume. *)
  Lemma wp_seq :
    forall functions c1 c2 tr m l post,
      WeakestPrecondition.cmd functions c1 tr m l
        (fun tr' m' l' => WeakestPrecondition.cmd functions c2 tr' m' l' post) ->
      WeakestPrecondition.cmd functions (cmd.seq c1 c2) tr m l post.
  Proof. intros functions c1 c2 tr m l post H. exact H. Qed.

  (** One [felem_copy] call.  The argument-address hypothesis is stated
      as a [dexprs] so that §4 discharges it with [eval_call_args] and
      never has to reason about [tcoord] by hand. *)
  Lemma wp_cp_step :
    forall functions,
      spec_of_felem_copy functions ->
      forall (ed es : Syntax.expr) (pd ps : word.rep) (v old : F)
             (Rest : mem -> Prop) tr m l post,
        WeakestPrecondition.dexprs m l [ed; es] [pd; ps] ->
        (FElem (Some tight_bounds) ps v ⋆ FElem (Some tight_bounds) pd old
         ⋆ Rest)%sep m ->
        (forall m',
            (FElem (Some tight_bounds) ps v ⋆ FElem (Some tight_bounds) pd v
             ⋆ Rest)%sep m' -> post tr m' l) ->
        WeakestPrecondition.cmd functions
          (cmd.call []%list felem_copy [ed; es]) tr m l post.
  Proof.
    intros functions Hcopy ed es pd ps v old Rest tr m l post
           Hargs Hsep Hpost.
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    exists [pd; ps]. split; [ exact Hargs | ].
    eapply Semantics.weaken_call.
    1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
    intros tr' m' rets Hp. cbv beta in Hp.
    destruct Hp as (Hr & Ht & Hm').
    subst rets. subst tr'.
    eexists. split; [ exact eq_refl | ].
    apply Hpost. ecancel_assumption.
  Qed.

  (** One aliasing "curve_add" call, through §3a. *)
  Lemma wp_add_step :
    forall functions,
      spec_of_curve_add_inplace_general three_b a_const functions ->
      forall (eox eoy eoz eax eay eaz : Syntax.expr)
             (pXo pYo pZo pX2 pY2 pZ2 : word.rep)
             (X Y Z X2 Y2 Z2 Xo Yo Zo : F)
             (Rest : mem -> Prop) tr m l post,
        WeakestPrecondition.dexprs m l
          [eox; eax; eoy; eay; eoz; eaz; eox; eoy; eoz]
          [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo] ->
        Add (X, Y, Z) (X2, Y2, Z2) = (Xo, Yo, Zo) ->
        (Pt3 pXo pYo pZo X Y Z ⋆ Pt3 pX2 pY2 pZ2 X2 Y2 Z2 ⋆ Rest)%sep m ->
        (forall m',
            (Pt3 pXo pYo pZo Xo Yo Zo ⋆ Pt3 pX2 pY2 pZ2 X2 Y2 Z2 ⋆ Rest)%sep m'
            -> post tr m' l) ->
        WeakestPrecondition.cmd functions
          (cmd.call []%list "curve_add"
             [eox; eax; eoy; eay; eoz; eaz; eox; eoy; eoz]) tr m l post.
  Proof.
    intros functions Hadd eox eoy eoz eax eay eaz pXo pYo pZo pX2 pY2 pZ2
           X Y Z X2 Y2 Z2 Xo Yo Zo Rest tr m l post Hargs Heq Hsep Hpost.
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    exists [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo].
    split; [ exact Hargs | ].
    eapply Semantics.weaken_call.
    1: { eapply curve_add_triple;
         [ exact Hadd | exact Heq | ecancel_assumption ]. }
    intros tr' m' rets Hp. cbv beta in Hp.
    destruct Hp as (Hr & Ht & Hm').
    subst rets. subst tr'.
    eexists. split; [ exact eq_refl | ].
    apply Hpost. ecancel_assumption.
  Qed.

  (** The two per-statement tactics used in §4.  [Hold] is the stale
      separation hypothesis; [Hnew] names the one the call produces. *)
  Local Ltac cpstep Hold Hnew :=
    apply wp_seq;
    eapply wp_cp_step;
    [ eassumption
    | solve [ eval_call_args ]
    | ecancel_assumption
    | intros ? Hnew; clear Hold ].

  Local Ltac addstep Heq Hold Hnew :=
    apply wp_seq;
    eapply wp_add_step;
    [ eassumption
    | solve [ eval_call_args ]
    | exact Heq
    | ecancel_assumption
    | intros ? Hnew; clear Hold ].

  (* ---- 4. The theorem --------------------------------------------- *)

  (** After [precompute_table4_body], the caller's table buffer holds
      [table4_of (Px,Py,Pz)] — which is [rcb_build_table4] at the same
      constants ([table4_of_is_rcb]), so
      [WnafTableBuild.rcb_table4_ok] applies to it verbatim.  The base
      point is unchanged; the scratch point is clobbered (it ends at
      [2P], but the statement only exposes that it still is a point). *)
  Theorem precompute_table4_body_ok :
    forall functions,
      spec_of_felem_copy functions ->
      spec_of_curve_add_inplace_general three_b a_const functions ->
    forall pT pQx pQy pQz pPx pPy pPz
      (Px Py Pz Qx0 Qy0 Qz0 : F)
      (x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 : F)
      (R : mem -> Prop) tr m l,
      map.get l "table_P" = Some pT ->
      map.get l "tmpx" = Some pQx ->
      map.get l "tmpy" = Some pQy ->
      map.get l "tmpz" = Some pQz ->
      map.get l "px" = Some pPx ->
      map.get l "py" = Some pPy ->
      map.get l "pz" = Some pPz ->
      (Table4 pT [(x0,y0,z0); (x1,y1,z1); (x2,y2,z2); (x3,y3,z3)]
       ⋆ Pt3 pQx pQy pQz Qx0 Qy0 Qz0
       ⋆ Pt3 pPx pPy pPz Px Py Pz ⋆ R)%sep m ->
      WeakestPrecondition.cmd functions precompute_table4_body tr m l
        (fun tr' m' l' =>
           tr' = tr /\ l' = l /\
           exists Qx Qy Qz,
             (Table4 pT (table4_of three_b a_const (Px,Py,Pz))
              ⋆ Pt3 pQx pQy pQz Qx Qy Qz
              ⋆ Pt3 pPx pPy pPz Px Py Pz ⋆ R)%sep m').
  Proof.
    intros functions Hcopy Hadd pT pQx pQy pQz pPx pPy pPz Px Py Pz
           Qx0 Qy0 Qz0 x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 R tr m l
           HlT HlQx HlQy HlQz HlPx HlPy HlPz Hm.
    (* The four entries of [table4_of], and the three-address form of
       [Table4], as explicit coordinates.  [E2]/[E3]/[E5]/[E7] are the
       four additions the body performs, in program order. *)
    rewrite (table4_of_eq three_b a_const (Px, Py, Pz)).
    destruct (Add (Px, Py, Pz) (Px, Py, Pz)) as [[T2x T2y] T2z] eqn:E2.
    destruct (Add (Px, Py, Pz) (T2x, T2y, T2z)) as [[X1 Y1] Z1] eqn:E3.
    destruct (Add (X1, Y1, Z1) (T2x, T2y, T2z)) as [[X2 Y2] Z2] eqn:E5.
    destruct (Add (X2, Y2, Z2) (T2x, T2y, T2z)) as [[X3 Y3] Z3] eqn:E7.
    (* [Table4]'s twelve addresses are literally what [tcoord] evaluates
       to, so no word arithmetic is needed below. *)
    cbv [Table4 TablePoint table_point_addr felem_addr] in Hm |- *.
    unfold precompute_table4_body.
    (* e0 := P *)
    cpstep Hm  H1.
    cpstep H1  H2.
    cpstep H2  H3.
    (* tmp := P; tmp += P, so tmp = 2P *)
    cpstep H3  H4.
    cpstep H4  H5.
    cpstep H5  H6.
    addstep E2 H6  H7.
    (* e1 := e0; e1 += tmp, so e1 = 3P *)
    cpstep H7  H8.
    cpstep H8  H9.
    cpstep H9  H10.
    addstep E3 H10 H11.
    (* e2 := e1; e2 += tmp, so e2 = 5P *)
    cpstep H11 H12.
    cpstep H12 H13.
    cpstep H13 H14.
    addstep E5 H14 H15.
    (* e3 := e2; e3 += tmp, so e3 = 7P.  The last statement carries no
       [cmd.seq] wrapper, so [addstep] is inlined without [wp_seq]. *)
    cpstep H15 H16.
    cpstep H16 H17.
    cpstep H17 H18.
    eapply wp_add_step;
      [ eassumption
      | solve [ eval_call_args ]
      | exact E7
      | ecancel_assumption
      | intros mfin Hfin ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    exists T2x, T2y, T2z. ecancel_assumption.
  Qed.

End Proof.
