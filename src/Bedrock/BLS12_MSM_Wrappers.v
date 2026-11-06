(** * The callee contracts of [BLS12_MSM.msm_bls12], discharged.

    [BLS12_MSM.msm_bls12_prog_ok] takes three contracts on its callees:
    [CurveAddAliasedOK] (addition with output = first input),
    [CurveDoubleInplaceOK] (doubling in place) and [StoreZero3OK]
    (write the identity).  The shipped program
    ([BLS12_G1ArenaRust.bls12_g1_funcs]) calls the copy-out wrappers
    ["msm_curve_add"] / ["msm_curve_double"] and [StoreZero.store_zero_func].

    This file proves, generically in the field representation (with
    [loose_bounds = tight_bounds], as for the saturated Montgomery
    representation of BLS12-381):

    - [copy_out_add_ok]: the wrapper body
      [stackalloc tx ty tz; curve_add(ins, tx, ty, tz); copy(outs, t)]
      satisfies [CurveAddAliasedOK] for [g1_add_spec = ladderstep_triple],
      from [RcbAnyOut.spec_of_ladderstep_anyout] (the shipped
      [ladderstep_body] with unconstrained output buffers) and
      fiat-crypto's [spec_of_felem_copy];
    - [copy_out_double_ok]: the same for doubling,
      [g1_double_spec = rcb_double_a0_triple], from
      [RcbAnyOut.spec_of_rcb_double_a0_anyout];
    - [store_zero_ok3]: [store_zero_func] satisfies [StoreZero3OK] for
      [g1_identity = (0, 1, 0)], from contracts of its two leaves
      [zero_name] / [one_name] ([spec_of_store_const]: write the
      constant, tight, into an allocated field element).

    The transport lemmas between the two [FElem] layers and the stack
    plumbing come from [NistWnafWrappers] (Qed there). *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith Lia List.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.RcbAnyOut.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Require Import Bedrock.BLS12_MSM.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section Bodies.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width}
          {mem : map.map word Byte.byte}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  (** The body of [BLS12_G1ArenaRust.copy_out_wrapper], with the copy
      function named by the field parameters ([felem_copy]); at BLS12
      it is literally the shipped body ([BLS12_MSM_Closed]). *)
  Definition copy_out_body (callee : string) (ins outs : list string)
    : Syntax.cmd :=
    cmd.stackalloc "tx" felem_size_in_bytes
    (cmd.stackalloc "ty" felem_size_in_bytes
    (cmd.stackalloc "tz" felem_size_in_bytes
      (cmd.seq
        (cmd.call [] callee
           (List.map expr.var (ins ++ ["tx"; "ty"; "tz"])))
      (cmd.seq
        (cmd.call [] felem_copy [expr.var (nth 0 outs ""); expr.var "tx"])
      (cmd.seq
        (cmd.call [] felem_copy [expr.var (nth 1 outs ""); expr.var "ty"])
        (cmd.call [] felem_copy [expr.var (nth 2 outs ""); expr.var "tz"]))))))%list.

  Definition add_ins : list string := ["X1"; "X2"; "Y1"; "Y2"; "Z1"; "Z2"].
  Definition dbl_ins : list string := ["Xin"; "Yin"; "Zin"].
  Definition outs3 : list string := ["Xout"; "Yout"; "Zout"].

  Definition msm_curve_add_func : string * Syntax.func :=
    ("msm_curve_add", ((add_ins ++ outs3)%list, @nil string, copy_out_body "curve_add" add_ins outs3)).
  Definition msm_curve_double_func : string * Syntax.func :=
    ("msm_curve_double", ((dbl_ins ++ outs3)%list, @nil string, copy_out_body "curve_double_a0" dbl_ins outs3)).
End Bodies.

Section Proofs.
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
  Context (three_b : felem) (three_b_name : string).

  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Let three_b_val : F := feval (proj1_sig three_b).

  Lemma FElem_none_intro_frame (p : word) (x : felem) (R : mem -> Prop) (m : mem) :
    (Field.FElem p x * R)%sep m -> (FElem None p (feval x) * R)%sep m.
  Proof.
    intros H. destruct H as (m1 & m2 & Hsplit & H1 & H2).
    exists m1, m2. split; [exact Hsplit|]. split; [|exact H2].
    cbv [Compilation2.FElem Lift1Prop.ex1].
    exists x. apply sep_emp_l.
    split; [split; [reflexivity | exact I] | exact H1].
  Qed.

  Lemma FElem_none_impl1 (p : word) (x : felem) :
    Lift1Prop.impl1 (Field.FElem p x) (FElem None p (feval x)).
  Proof.
    intros m H. cbv [Compilation2.FElem Lift1Prop.ex1].
    exists x. apply sep_emp_l.
    split; [split; [reflexivity | exact I] | exact H].
  Qed.

  Lemma FElem_none_intro3 (p1 p2 p3 : word) (x1 x2 x3 : felem) (R : mem -> Prop) (m : mem) :
    (Field.FElem p1 x1 * Field.FElem p2 x2 * Field.FElem p3 x3 * R)%sep m ->
    (FElem None p1 (feval x1) * FElem None p2 (feval x2) * FElem None p3 (feval x3) * R)%sep m.
  Proof.
    revert m.
    refine (SeparationLogic.Proper_sep_impl1 _ _ _ _ _ (reflexivity R)).
    refine (SeparationLogic.Proper_sep_impl1 _ _ _ _ _ (FElem_none_impl1 p3 x3)).
    exact (SeparationLogic.Proper_sep_impl1 _ _ (FElem_none_impl1 p1 x1) _ _ (FElem_none_impl1 p2 x2)).
  Qed.

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
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
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

  Local Ltac stackalloc3 Hsep :=
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body];
    split; [ apply felem_size_in_bytes_mod | ];
    let atx := fresh "atx" in let mSx := fresh "mSx" in let mCx := fresh "mCx" in
    let Hanyx := fresh "Hanyx" in let Hsplitx := fresh "Hsplitx" in
    let xtx := fresh "xtx" in let Hax := fresh "Hax" in
    intros atx mSx mCx Hanyx Hsplitx;
    cbv beta zeta delta [dlet.dlet];
    destruct (stackalloc_FElem _ _ _ _ _ Hanyx Hsplitx Hsep) as (xtx & Hax);
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body];
    split; [ apply felem_size_in_bytes_mod | ];
    let aty := fresh "aty" in let mSy := fresh "mSy" in let mCy := fresh "mCy" in
    let Hanyy := fresh "Hanyy" in let Hsplity := fresh "Hsplity" in
    let xty := fresh "xty" in let Hay := fresh "Hay" in
    intros aty mSy mCy Hanyy Hsplity;
    cbv beta zeta delta [dlet.dlet];
    destruct (stackalloc_FElem _ _ _ _ _ Hanyy Hsplity Hax) as (xty & Hay);
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body];
    split; [ apply felem_size_in_bytes_mod | ];
    let atz := fresh "atz" in let mSz := fresh "mSz" in let mCz := fresh "mCz" in
    let Hanyz := fresh "Hanyz" in let Hsplitz := fresh "Hsplitz" in
    let xtz := fresh "xtz" in let Haz := fresh "Haz" in
    intros atz mSz mCz Hanyz Hsplitz;
    cbv beta zeta delta [dlet.dlet];
    destruct (stackalloc_FElem _ _ _ _ _ Hanyz Hsplitz Hay) as (xtz & Haz);
    clear Hsep Hax Hay.

  Lemma ladderstep_triple_of_gallina X1 Y1 Z1 X2 Y2 Z2 outx outy outz :
    @ladderstep_gallina _ three_b_val X1 X2 Y1 Y2 Z1 Z2 = \<outx, outy, outz\> ->
    ladderstep_triple three_b_val (X1, Y1, Z1) (X2, Y2, Z2) = (outx, outy, outz).
  Proof. intros H. unfold ladderstep_triple. rewrite H. reflexivity. Qed.

  Lemma rcb_double_a0_triple_of_gallina X Y Z outx outy outz :
    @rcb_double_a0_gallina _ three_b_val X Y Z = \<outx, outy, outz\> ->
    rcb_double_a0_triple three_b_val (X, Y, Z) = (outx, outy, outz).
  Proof. intros H. unfold rcb_double_a0_triple. rewrite H. reflexivity. Qed.

  Lemma copy_out_add_ok :
    forall functions,
      map.get functions "msm_curve_add" = Some (snd msm_curve_add_func) ->
      spec_of_ladderstep_anyout three_b functions ->
      spec_of_felem_copy functions ->
      CurveAddAliasedOK "msm_curve_add" (ladderstep_triple three_b_val) functions.
  Proof.
    intros functions Henv Hadd Hcopy.
    cbv [spec_of_ladderstep_anyout] in Hadd.
    change CompilationAbstract.FElem with Compilation2.FElem in Hadd.
    cbv [CurveAddAliasedOK].
    change CompilationAbstract.FElem with Compilation2.FElem.
    intros pb1 pp1 pb2 pp2 pb3 pp3 B1 P1 B2 P2 B3 P3 R0 tr0 m0 Hsep.
    eapply WeakestPreconditionProperties.start_func; [ exact Henv | ].
    cbv match beta delta [WeakestPrecondition.func msm_curve_add_func snd
                          copy_out_body add_ins outs3 List.app List.map nth].
    eexists. split. { reflexivity. }
    stackalloc3 Hsep.
    (* --- curve_add(X1..Z2, tx, ty, tz) --- *)
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    assert (Hpre : (FElem None atx (feval xtx) * FElem None aty (feval xty)
                    * FElem None atz (feval xtz)
                    * (FElem (Some tight_bounds) pb1 B1 * FElem (Some tight_bounds) pp1 P1
                       * FElem (Some tight_bounds) pb2 B2 * FElem (Some tight_bounds) pp2 P2
                       * FElem (Some tight_bounds) pb3 B3 * FElem (Some tight_bounds) pp3 P3
                       * R0))%sep mCz).
    { apply FElem_none_intro3. ecancel_assumption. }
    specialize (Hadd pb1 pp1 pb2 pp2 pb3 pp3 atx aty atz
                  B1 P1 B2 P2 B3 P3 (feval xtx) (feval xty) (feval xtz) R0 tr0 mCz).
    eapply Semantics.weaken_call.
    1: { apply Hadd; ecancel_assumption. }
    intros tr4 m4 rets4 Hp4. cbv beta in Hp4.
    destruct Hp4 as (Hr4 & Ht4 & outx & outy & outz & Hgal & Hm4).
    subst rets4. subst tr4. clear Haz Hpre.
    eexists. split. { exact eq_refl. }
    (* --- three copies back --- *)
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
    intros tr5 m5 rets5 Hp5. cbv beta in Hp5.
    destruct Hp5 as (Hr5 & Ht5 & Hm5). subst rets5. subst tr5. clear Hm4.
    eexists. split. { exact eq_refl. }
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
    intros tr6 m6 rets6 Hp6. cbv beta in Hp6.
    destruct Hp6 as (Hr6 & Ht6 & Hm6). subst rets6. subst tr6. clear Hm5.
    eexists. split. { exact eq_refl. }
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
    intros tr7 m7 rets7 Hp7. cbv beta in Hp7.
    destruct Hp7 as (Hr7 & Ht7 & Hm7). subst rets7. subst tr7. clear Hm6.
    eexists. split. { exact eq_refl. }
    cbv beta.
    (* --- give the temporaries back (tz, ty, tx) --- *)
    assert (Hdz : (FElem (Some tight_bounds) atz outz
                   * (FElem (Some tight_bounds) aty outy
                      * (FElem (Some tight_bounds) atx outx
                         * (FElem (Some tight_bounds) pb1 outx
                            * FElem (Some tight_bounds) pp1 P1
                            * FElem (Some tight_bounds) pb2 outy
                            * FElem (Some tight_bounds) pp2 P2
                            * FElem (Some tight_bounds) pb3 outz
                            * FElem (Some tight_bounds) pp3 P3
                            * R0))))%sep m7)
      by ecancel_assumption.
    clear Hm7.
    destruct (FElem2_dealloc _ _ _ _ _ Hdz) as (mz & mSz2 & Habz & Hspz & Hpz).
    exists mz, mSz2. split; [ exact Habz | ]. split; [ exact Hspz | ]. cbv beta.
    destruct (FElem2_dealloc _ _ _ _ _ Hpz) as (my & mSy2 & Haby & Hspy & Hpy).
    exists my, mSy2. split; [ exact Haby | ]. split; [ exact Hspy | ]. cbv beta.
    destruct (FElem2_dealloc _ _ _ _ _ Hpy) as (mx & mSx2 & Habx & Hspx & Hpx).
    exists mx, mSx2. split; [ exact Habx | ]. split; [ exact Hspx | ].
    cbv beta match fix delta [list_map list_map_body].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    rewrite (ladderstep_triple_of_gallina _ _ _ _ _ _ _ _ _ Hgal). cbv beta iota.
    exact Hpx.
  Qed.

  Lemma copy_out_double_ok :
    forall functions,
      map.get functions "msm_curve_double" = Some (snd msm_curve_double_func) ->
      spec_of_rcb_double_a0_anyout three_b functions ->
      spec_of_felem_copy functions ->
      CurveDoubleInplaceOK "msm_curve_double" (rcb_double_a0_triple three_b_val) functions.
  Proof.
    intros functions Henv Hdbl Hcopy.
    cbv [spec_of_rcb_double_a0_anyout] in Hdbl.
    change CompilationAbstract.FElem with Compilation2.FElem in Hdbl.
    cbv [CurveDoubleInplaceOK].
    change CompilationAbstract.FElem with Compilation2.FElem.
    intros pX pY pZ X Y Z R0 tr0 m0 Hsep.
    eapply WeakestPreconditionProperties.start_func; [ exact Henv | ].
    cbv match beta delta [WeakestPrecondition.func msm_curve_double_func snd
                          copy_out_body dbl_ins outs3 List.app List.map nth].
    eexists. split. { reflexivity. }
    stackalloc3 Hsep.
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    assert (Hpre : (FElem None atx (feval xtx) * FElem None aty (feval xty)
                    * FElem None atz (feval xtz)
                    * (FElem (Some tight_bounds) pX X * FElem (Some tight_bounds) pY Y
                       * FElem (Some tight_bounds) pZ Z * R0))%sep mCz).
    { apply FElem_none_intro3. ecancel_assumption. }
    specialize (Hdbl pX pY pZ atx aty atz X Y Z
                  (feval xtx) (feval xty) (feval xtz) R0 tr0 mCz).
    eapply Semantics.weaken_call.
    1: { apply Hdbl; ecancel_assumption. }
    intros tr4 m4 rets4 Hp4. cbv beta in Hp4.
    destruct Hp4 as (Hr4 & Ht4 & outx & outy & outz & Hgal & Hm4).
    subst rets4. subst tr4. clear Haz Hpre.
    eexists. split. { exact eq_refl. }
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
    intros tr5 m5 rets5 Hp5. cbv beta in Hp5.
    destruct Hp5 as (Hr5 & Ht5 & Hm5). subst rets5. subst tr5. clear Hm4.
    eexists. split. { exact eq_refl. }
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
    intros tr6 m6 rets6 Hp6. cbv beta in Hp6.
    destruct Hp6 as (Hr6 & Ht6 & Hm6). subst rets6. subst tr6. clear Hm5.
    eexists. split. { exact eq_refl. }
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
    intros tr7 m7 rets7 Hp7. cbv beta in Hp7.
    destruct Hp7 as (Hr7 & Ht7 & Hm7). subst rets7. subst tr7. clear Hm6.
    eexists. split. { exact eq_refl. }
    cbv beta.
    assert (Hdz : (FElem (Some tight_bounds) atz outz
                   * (FElem (Some tight_bounds) aty outy
                      * (FElem (Some tight_bounds) atx outx
                         * (FElem (Some tight_bounds) pX outx
                            * FElem (Some tight_bounds) pY outy
                            * FElem (Some tight_bounds) pZ outz
                            * R0))))%sep m7)
      by ecancel_assumption.
    clear Hm7.
    destruct (FElem2_dealloc _ _ _ _ _ Hdz) as (mz & mSz2 & Habz & Hspz & Hpz).
    exists mz, mSz2. split; [ exact Habz | ]. split; [ exact Hspz | ]. cbv beta.
    destruct (FElem2_dealloc _ _ _ _ _ Hpz) as (my & mSy2 & Haby & Hspy & Hpy).
    exists my, mSy2. split; [ exact Haby | ]. split; [ exact Hspy | ]. cbv beta.
    destruct (FElem2_dealloc _ _ _ _ _ Hpy) as (mx & mSx2 & Habx & Hspx & Hpx).
    exists mx, mSx2. split; [ exact Habx | ]. split; [ exact Hspx | ].
    cbv beta match fix delta [list_map list_map_body].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    rewrite (rcb_double_a0_triple_of_gallina _ _ _ _ _ _ Hgal). cbv beta iota.
    exact Hpx.
  Qed.

  (** Contract of a leaf that writes the field constant [c], tight, into
      an allocated field element (for BLS12: ["bls12_zero"] /
      ["bls12_one"], routed by the Rust runtime to the crate's leaves). *)
  Definition spec_of_store_const (name : string) (c : F)
             (functions : Semantics.env) : Prop :=
    forall p (x : F) R tr m,
      (FElem None p x * R)%sep m ->
      Semantics.call functions name tr m [p]
        (fun tr' m' rets => rets = [] /\ tr = tr' /\
           (FElem (Some tight_bounds) p c * R)%sep m').

  Lemma store_zero_ok3 (zero_name one_name : string) :
    forall functions,
      map.get functions "store_zero"
        = Some (snd (store_zero_func (zero_name := zero_name) (one_name := one_name))) ->
      spec_of_store_const zero_name (F.of_Z M_pos 0) functions ->
      spec_of_store_const one_name (F.of_Z M_pos 1) functions ->
      StoreZero3OK "store_zero" (F.of_Z M_pos 0, F.of_Z M_pos 1, F.of_Z M_pos 0) functions.
  Proof.
    intros functions Henv Hz Ho.
    cbv [StoreZero3OK].
    change CompilationAbstract.FElem with Compilation2.FElem.
    intros pX pY pZ Xv Yv Zv R0 tr0 m0 Hsep.
    eapply WeakestPreconditionProperties.start_func; [ exact Henv | ].
    cbv match beta delta [WeakestPrecondition.func store_zero_func snd].
    eexists. split. { reflexivity. }
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply Hz. ecancel_assumption. }
    intros tr1 m1 rets1 (Hr1 & Ht1 & Hm1). subst rets1 tr1.
    eexists. split. { exact eq_refl. }
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply Ho. ecancel_assumption. }
    intros tr2 m2 rets2 (Hr2 & Ht2 & Hm2). subst rets2 tr2.
    eexists. split. { exact eq_refl. }
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply Hz. ecancel_assumption. }
    intros tr3 m3 rets3 (Hr3 & Ht3 & Hm3). subst rets3 tr3.
    eexists. split. { exact eq_refl. }
    cbv beta match fix delta [list_map list_map_body].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    ecancel_assumption.
  Qed.
End Proofs.
