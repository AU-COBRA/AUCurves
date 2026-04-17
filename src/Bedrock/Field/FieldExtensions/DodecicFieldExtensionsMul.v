(** * Standalone compilation unit for the Fp12_mul_ok proof.
    Split from DodecicFieldExtensions.v to reduce per-file compilation time.
*)

Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Export Crypto.Spec.ModularArithmetic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Ltac2.Ltac2.
From Hammer Require Import Tactics.
Set Default Proof Mode "Classic".

Section Fp12.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {prime_parameters : PrimeFieldParameters}
          {prime_parameters_ok : PrimeFieldParameters_ok}.

  Local Notation Fp := (F M_pos).
  Local Notation Fp2 := ((Fp * Fp)%type).
  Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
  Local Notation Fp12 := ((Fp6 * Fp6)%type).

  Existing Instance prime_field_parameters.

  Context {F_representation : AbstractField.FieldRepresentation (F:=Fp)}
          {F_representation_ok : AbstractField.FieldRepresentation_ok (F:=Fp)}.

  (* note that this excludes non-saturated representations *)
  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  (* Quadratic non-residue β for Fp2 = Fp[u]/(u² - β) *)
  Variable beta : F M_pos.
  Hypothesis beta_nz : beta <> @F.zero M_pos.
  Hypothesis beta_qnr : ~(exists x, @F.mul M_pos x x = beta).
  Hypothesis M_big : 2 < Z.pos M_pos.

  (* ξ = (xi_re, xi_im) in Fp2 — the cubic non-residue for Fp6 = Fp2[v]/(v³ - ξ) *)
  Variable xi_re : F M_pos.
  Variable xi_im : F M_pos.

  (* Prefixes for function names *)
  Variable fp12_prefix : string.
  Variable fp6_prefix : string.
  Variable fp2_prefix : string.

  (* ================================================================ *)
  (* Lower-layer instances                                             *)
  (* ================================================================ *)

  Local Instance Fp2_fp_inst : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters beta fp2_prefix.
  Local Instance Fp2_fp_ok_inst : @AbstractField.FieldParameters_ok _ Fp2_fp_inst :=
    Fp2_field_parameters_ok beta beta_nz beta_qnr M_big fp2_prefix.
  Local Instance Fp2_repr_inst : @AbstractField.FieldRepresentation Fp2 Fp2_fp_inst width BW word mem :=
    @Fp2_field_representation width BW word mem prime_parameters F_representation beta fp2_prefix.
  Local Instance Fp2_repr_ok_inst : @AbstractField.FieldRepresentation_ok Fp2 Fp2_fp_inst _ _ _ _ Fp2_repr_inst :=
    @Fp2_field_representation_ok width BW word mem prime_parameters F_representation F_representation_ok beta fp2_prefix.

  Local Instance Fp6_fp_inst : AbstractField.FieldParameters Fp6 :=
    Fp6_field_parameters beta xi_re xi_im (fp6_prefix:=fp6_prefix).
  Local Instance Fp6_repr_inst : @AbstractField.FieldRepresentation Fp6 Fp6_fp_inst width BW word mem :=
    Fp6_field_representation beta xi_re xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
  Local Instance Fp6_repr_ok_inst : @AbstractField.FieldRepresentation_ok Fp6 Fp6_fp_inst _ _ _ _ Fp6_repr_inst :=
    Fp6_field_representation_ok beta xi_re xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  Local Instance Fp12_fp_inst : AbstractField.FieldParameters Fp12 :=
    Fp12_field_parameters beta xi_re xi_im (fp12_prefix:=fp12_prefix).
  Local Instance Fp12_repr_inst : @AbstractField.FieldRepresentation Fp12 Fp12_fp_inst width BW word mem :=
    Fp12_field_representation beta xi_re xi_im (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
  Local Instance Fp12_repr_ok_inst : @AbstractField.FieldRepresentation_ok Fp12 Fp12_fp_inst _ _ _ _ Fp12_repr_inst :=
    Fp12_field_representation_ok beta xi_re xi_im (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

  (* ================================================================ *)
  (* Helper function names                                             *)
  (* ================================================================ *)

  Local Definition fp6_mul_by_v_name := (fp6_prefix ++ "mul_by_v")%string.

  (* ================================================================ *)
  (* Offset helpers                                                    *)
  (* ================================================================ *)

  Local Notation fp2_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).

  Local Notation fp6_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp6))).
  Local Definition expr_fp12_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp12_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp6_felem_offset).

  (* ================================================================ *)
  (* spec_of instances for underlying operations                       *)
  (* ================================================================ *)

  Instance spec_of_Fp6_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp6)) :=
    AbstractField.spec_of_felem_copy (F:=Fp6).
  Instance spec_of_Fp6_add : spec_of (AbstractField.add (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp6).
  Instance spec_of_Fp6_mul : spec_of (AbstractField.mul (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp6).
  Instance spec_of_Fp6_sub : spec_of (AbstractField.sub (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp6).

  (* ================================================================ *)
  (* Fp12 decomposition infrastructure                                 *)
  (* ================================================================ *)

  Local Notation FElem_Fp6 := (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
  Local Notation Fp6_felem_size := (@AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).

  Lemma Fp12_list_decomp : forall l, d0_felem l ++ d1_felem l = l.
  Proof.
    intros. unfold d0_felem, d1_felem.
    apply QuadraticFieldExtensions.firstn_skipn.
  Qed.

  Lemma Fp6_FElem_length pout
    (out : @AbstractField.felem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) m :
    FElem_Fp6 pout out m ->
    length out = Fp6_felem_size.
  Proof.
    unfold AbstractField.FElem, Bignum.Bignum.
    intros [me [ma [_ [[_ H] _]]]]. exact H.
  Qed.

  Lemma d0_felem_length (l : list word) :
    length l = (2 * Fp6_felem_size)%nat ->
    length (d0_felem l) = Fp6_felem_size.
  Proof.
    intros. unfold d0_felem.
    apply QuadraticFieldExtensions.length_firstn. lia.
  Qed.

  Lemma d1_felem_length (l : list word) :
    length l = (2 * Fp6_felem_size)%nat ->
    length (d1_felem l) = Fp6_felem_size.
  Proof.
    intros. unfold d1_felem.
    apply QuadraticFieldExtensions.length_skipn. lia.
  Qed.

  Lemma Fp12_raw_FElem_split pout
    (out : @AbstractField.felem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) m :
    @AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst pout out m ->
    (FElem_Fp6 pout (d0_felem out) *
     FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem out))%sep m.
  Proof.
    intros H.
    unfold AbstractField.FElem, Bignum.Bignum in *.
    destruct H as [me [ma [Hms [[Hme Hlen] Ha]]]].
    subst me.
    assert (m = ma) by (apply Properties.map.split_empty_l in Hms; exact Hms). subst.
    set (n := Fp6_felem_size) in *.
    change (@AbstractField.felem_size_in_words _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst)
      with (2 * n)%nat in Hlen.
    assert (Hdecomp : out = d0_felem out ++ d1_felem out)
      by (symmetry; apply Fp12_list_decomp).
    rewrite Hdecomp in Ha.
    apply array_append' in Ha.
    destruct Ha as [m0 [m1 [Hms01 [Ha0 Ha1]]]].
    assert (Hlen0 : length (d0_felem out) = n) by (apply d0_felem_length; lia).
    rewrite Hlen0 in Ha1.
    rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha1.
    exists m0, m1.
    destruct Hms01 as [Heq01 Hd01]. subst.
    split; [split; [reflexivity | exact Hd01] |]. split.
    - exists map.empty, m0. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [split; [exact eq_refl | exact Hlen0] | exact Ha0].
    - exists map.empty, m1. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [split; [exact eq_refl |] | exact Ha1].
      apply d1_felem_length. lia.
  Qed.

  Lemma Fp12_raw_FElem_join pout c0 c1 m :
    length c0 = Fp6_felem_size ->
    length c1 = Fp6_felem_size ->
    (FElem_Fp6 pout c0 *
     FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) c1)%sep m ->
    @AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst pout (c0 ++ c1) m.
  Proof.
    intros Hlen0 Hlen1 H.
    unfold AbstractField.FElem, Bignum.Bignum in *.
    destruct H as [m0 [m1 [Hms01 [H0 H1]]]].
    destruct H0 as [me0 [ma0 [Hms0 [[Hme0 Hlen0'] Ha0]]]].
    subst me0. assert (m0 = ma0) by (apply Properties.map.split_empty_l in Hms0; exact Hms0). subst.
    destruct H1 as [me1 [ma1 [Hms1 [[Hme1 Hlen1'] Ha1]]]].
    subst me1. assert (m1 = ma1) by (apply Properties.map.split_empty_l in Hms1; exact Hms1). subst.
    set (n := Fp6_felem_size) in *.
    exists map.empty, m. split. { apply Properties.map.split_empty_l. reflexivity. }
    split.
    - split; [exact eq_refl |].
      rewrite length_app.
      change (@AbstractField.felem_size_in_words _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst)
        with (2 * n)%nat. lia.
    - pose proof (proj2 (array_append'
        scalar (word.of_Z (Memory.bytes_per_word width))
        c0 c1 pout m)) as Hback.
      apply Hback. clear Hback.
      exists ma0, ma1.
      destruct Hms01 as [Heq01 Hd01]. subst.
      split; [split; [reflexivity | exact Hd01] |]. split.
      { exact Ha0. }
      { rewrite Hlen0'. rewrite <- (@word.ring_morph_mul _ _ word_ok).
        exact Ha1. }
  Qed.

  Lemma d0_felem_app (a b : list word) :
    length a = Fp6_felem_size ->
    d0_felem (a ++ b) = a.
  Proof.
    intro H. unfold d0_felem.
    apply firstn_app'. exact H.
  Qed.

  Lemma d1_felem_app (a b : list word) :
    length a = Fp6_felem_size ->
    d1_felem (a ++ b) = b.
  Proof.
    intro H. unfold d1_felem.
    apply QuadraticFieldExtensions.skipn_app. exact H.
  Qed.

  (* Fp6 bounds equivalence *)
  Lemma Fp6_bounds_tight_of_loose : forall x,
    @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
      (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x ->
    @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
      (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x.
  Proof.
    intros fe H.
    unfold bounded_by, Fp6_field_representation, Fp6_repr_inst in *.
    unfold Fp6_field_representation in *. simpl in *.
    destruct H as [[H0a H0b] [[H1a H1b] [H2a H2b]]].
    repeat split; apply bounds_equiv; assumption.
  Qed.

  (* ================================================================ *)
  (* FieldNames for each layer                                         *)
  (* ================================================================ *)

  Context {Fp12_names : FieldNames (F:=Fp12)}.
  Context {Fp6_names : FieldNames (F:=Fp6)}.
  Context {Fp2_names : FieldNames (F:=Fp2)}.
  Context {Fp_names : FieldNames (F:=Fp)}.

  (* ================================================================ *)
  (* Function bodies                                                   *)
  (* ================================================================ *)

  Import Syntax BinInt String List.ListNotations.

  (* Generate real WP goals for (string * func) definitions *)
  Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

  Local Ltac2 Notation "instance_of" type(constr) :=
    lazy_match! Ltac2.Constr.pretype (preterm:(_ : $type)) with ?instance => instance end.

  Local Ltac2 rec callee_specs_ft (cmd : constr) : constr list :=
    multi_match! cmd with
      | cmd.cond _ ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.seq ?c1 ?c2 => List.append (callee_specs_ft c1) (callee_specs_ft c2)
      | cmd.while _ ?c => callee_specs_ft c
      | cmd.stackalloc _ _ ?c => callee_specs_ft c
      | cmd.call _ ?f _ => [instance_of (spec_of $f)]
      | _ => []
    end.

  Local Ltac2 program_logic_goal_for_ft (proc : constr) : unit :=
    let unfolded := eval hnf in $proc in
    lazy_match! unfolded with
    | (?fname, (?params, ?rets, ?body)) =>
      let fname_spec := instance_of (spec_of $fname) in
      let specs := callee_specs_ft body in
      let goal := (fun (functions : constr) =>
        List.fold_right (fun ps c => '(($ps $functions) -> $c)) specs '($fname_spec $functions)) in
      exact (forall functions (EnvContains : map.get functions $fname = Some ($params, $rets, $body)),
        ltac2:(let g := goal &functions in exact $g))
    end.

  Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
  Local Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac2:(
     Control.plus (fun () => program_logic_goal_for_ft (Ltac2.Constr.pretype proc)) (fun _ => exact True)))
    (at level 10, only parsing).

  (* ================================================================ *)
  (* Fp6_mul_by_v model and spec                                       *)
  (* ================================================================ *)

  Local Definition fp6_mul_by_v_model (x : Fp6) : Fp6 :=
    ((BLS12Fp6Spec.fp2_mul_xi M_pos beta xi_re xi_im (snd x), fst (fst x)), snd (fst x)).

  Local Instance un_Fp6_mul_by_v
    : @AbstractField.UnOp _ _ _ _ Fp6 Fp6_fp_inst Fp6_repr_inst fp6_mul_by_v_name :=
    {| AbstractField.un_model := fp6_mul_by_v_model;
       AbstractField.un_xbounds := @AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst;
       AbstractField.un_outbounds := @AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst |}.

  Instance spec_of_Fp6_mul_by_v : spec_of fp6_mul_by_v_name :=
    AbstractField.unop_spec un_Fp6_mul_by_v.

  (* ================================================================ *)
  (* Fp12 copy and mul definitions (needed for specs)                  *)
  (* ================================================================ *)

  Definition Fp12_felem_copy : function_t :=
    (AbstractField.felem_copy (F:=Fp12), (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "x")]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "x")])
    ))).

  Instance spec_of_Fp12_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
    AbstractField.spec_of_felem_copy (F:=Fp12).

  Local Definition expr_fp6_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp6_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp2_felem_offset).
  Local Definition expr_fp6_c2 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal (2 * fp2_felem_offset)).

  Definition Fp12_mul : function_t :=
    (AbstractField.mul (F:=Fp12), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as ax;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as ay;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "ax"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "ay"; expr.var "iny"]);
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as v0;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as v1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as u;
      (* v0 = a0*b0 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr.var "v0"; expr_fp12_c0 (expr.var "ax"); expr_fp12_c0 (expr.var "ay")]);
      (* v1 = a1*b1 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr.var "v1"; expr_fp12_c1 (expr.var "ax"); expr_fp12_c1 (expr.var "ay")]);
      (* t = a0+a1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr.var "t"; expr_fp12_c0 (expr.var "ax"); expr_fp12_c1 (expr.var "ax")]);
      (* u = b0+b1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr.var "u"; expr_fp12_c0 (expr.var "ay"); expr_fp12_c1 (expr.var "ay")]);
      (* t = (a0+a1)(b0+b1) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr.var "t"; expr.var "t"; expr.var "u"]);
      (* u = mul_by_v(v1) *)
      coq:(cmd.call [] fp6_mul_by_v_name [expr.var "u"; expr.var "v1"]);
      (* out.c0 = v0 + mul_by_v(v1) *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr.var "v0"; expr.var "u"]);
      (* t = t - v0 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp6)) [expr.var "t"; expr.var "t"; expr.var "v0"]);
      (* out.c1 = t - v1 *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr.var "t"; expr.var "v1"])
    ))).

  Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp12).

  (* ================================================================ *)
  (* WP proof automation tactics                                       *)
  (* ================================================================ *)

  Local Ltac map_disjoint_auto :=
    lazymatch goal with
    | |- map.disjoint (map.putmany _ _) _ =>
        apply map.disjoint_putmany_l; split; map_disjoint_auto
    | |- map.disjoint _ (map.putmany _ _) =>
        apply map.disjoint_putmany_r; split; map_disjoint_auto
    | |- map.disjoint ?a ?b =>
        first [ assumption
              | (unfold map.disjoint; intros ?k ?v1 ?v2 ?Hg1 ?Hg2;
                 match goal with H : map.disjoint _ _ |- _ => exact (H k v2 v1 Hg2 Hg1) end) ]
    end.

  Local Ltac solve_map_get :=
    repeat (first [ apply map.get_put_same
                  | rewrite map.get_put_diff by (cbv; congruence) ]).

  Local Ltac solve_dexprs :=
    repeat match goal with x := map.put _ _ _ |- _ => unfold x in *; clear x end;
    cbv [dexprs list_map list_map_body expr_fp6_c0 expr_fp6_c1 expr_fp6_c2
         expr_fp12_c0 expr_fp12_c1
         WeakestPrecondition.expr WeakestPrecondition.expr_body];
    repeat first
      [ exact eq_refl
      | eexists; split;
        [ solve_map_get; try exact eq_refl | ]
      | straightline ].

  Local Ltac split_all_disjointness :=
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
    | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
        let H1 := fresh "Hd" in let H2 := fresh "Hd" in
        destruct (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2]; clear H
    end.

  Local Ltac fp12_feval_eq :=
    change (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
      (fun ws => (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem ws),
                  @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem ws)));
    cbv beta.

  Local Ltac fp12_bounded_by_eq :=
    change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
      (fun b felem => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d0_felem felem)
                   /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d1_felem felem));
    cbv beta.

  Lemma Fp6_bounds_loose_of_tight : forall x,
    @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
      (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x ->
    @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
      (@AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) x.
  Proof.
    intros fe H.
    unfold bounded_by, Fp6_field_representation, Fp6_repr_inst in *.
    unfold Fp6_field_representation in *. simpl in *.
    destruct H as [[H0a H0b] [[H1a H1b] [H2a H2b]]].
    repeat split; apply relax_bounds; assumption.
  Qed.

  Local Ltac solve_bounds :=
    first [ assumption | apply bounds_equiv; assumption
          | apply Fp6_bounds_tight_of_loose; assumption
          | apply Fp6_bounds_loose_of_tight; assumption
          | apply relax_bounds; assumption ].

  Local Ltac solve_putmany_eq_aux n :=
    match n with
    | O => fail "solve_putmany_eq: out of fuel"
    | S ?n' =>
      first [
        reflexivity
      | match goal with
        | |- map.putmany ?a _ = map.putmany ?a _ =>
          apply (f_equal (map.putmany a)); solve_putmany_eq_aux n'
        end
      | match goal with
        | |- _ = map.putmany ?target _ =>
          match goal with
          | |- context [map.putmany ?a (map.putmany target ?rest)] =>
            rewrite (map.putmany_assoc a target rest);
            rewrite (map.putmany_comm a target) by map_disjoint_auto;
            rewrite <- (map.putmany_assoc target a rest);
            solve_putmany_eq_aux n'
          end
        end
      | (* Fallback: target is the rightmost element -- bubble it up *)
        match goal with
        | |- _ = map.putmany ?target _ =>
          match goal with
          | |- context [map.putmany ?a (map.putmany ?b target)] =>
            rewrite (map.putmany_assoc a b);
            rewrite (map.putmany_comm (map.putmany a b) target) by map_disjoint_auto;
            rewrite <- ?map.putmany_assoc;
            solve_putmany_eq_aux n'
          end
        end
      | match goal with
        | |- map.putmany ?a ?b = map.putmany ?b ?a =>
          apply map.putmany_comm; map_disjoint_auto
        end
      ]
    end.
  Local Ltac solve_putmany_eq :=
    rewrite <- ?map.putmany_assoc;
    solve_putmany_eq_aux 50%nat.

  (* ================================================================ *)
  (* The Fp12_mul_ok proof                                             *)
  (* ================================================================ *)

  Lemma Fp12_mul_ok : program_logic_goal_for_function! Fp12_mul.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2
      HFmul1 HFmul2 HFadd1 HFadd2 HFmul3 HFmulv HFadd3 HFsub1 HFsub2.
    unfold spec_of_Fp12_mul, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_mul].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc ax === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Stackalloc ay === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    pose proof (@AbstractField.FElem_from_bytes _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_xrx_sY Hd_sX_sY].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_x_sY Hd_rx_sY].
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === First Fp12 copy: x -> allocx === *)
    repeat straightline.
    exists [allocx; px]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 allocx px allocx_val x
        (fun m => (Rx ⋆ @AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst allocy allocy_val) m)
        (eq (map.putmany (map.putmany m_x m_rx) mStackY))
        tr).
      split.
      { exists (map.putmany m_x mStackX), (map.putmany m_rx mStackY).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split.
        { exists m_x, mStackX.
          split; [split; [reflexivity | exact Hd_x_sX] |].
          split; [exact Hfx | exact Hallocx]. }
        { exists m_rx, mStackY.
          split; [split; [reflexivity | exact Hd_rx_sY] |].
          split; [exact Hrx | exact Hallocy]. } }
      { exists mStackX, (map.putmany (map.putmany m_x m_rx) mStackY).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp12 copy: y -> allocy === *)
    destruct Hsep_copy1 as [m_new1 [m_frame1 [[Heq_m' Hd_n1_f1] [Hfelem_allocx Hframe1]]]].
    subst m_frame1 m'.
    destruct Hmemy as [m_y [m_ry [Hmemy_sp [Hfelem_y Hry]]]].
    destruct Hmemy_sp as [Heq_mem0_y Hd_yry].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_f1) as [Hd_n1_mem0 Hd_n1_sY].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_x Hd_n1_rx].
    rewrite Heq_mem0_y in Hd_n1_mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_y Hd_n1_ry].
    rewrite Heq_mem0_y in Hd_xrx_sY.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_xrx_sY) as [Hd_y_sY Hd_ry_sY'].
    exists [allocy; py]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 allocy py allocy_val y
        (fun m => (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst allocx x ⋆ Ry) m)
        (eq (map.putmany m_new1 (map.putmany m_y m_ry)))
        tr).
      split.
      { rewrite Heq_mem0_y.
        exists (map.putmany m_y mStackY), (map.putmany m_new1 m_ry).
        split; [split |].
        { transitivity (map.putmany m_new1 (map.putmany (map.putmany m_y mStackY) m_ry)).
          { f_equal. apply map.disjoint_putmany_commutes. exact Hd_ry_sY'. }
          transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y mStackY)) m_ry).
          { apply map.putmany_assoc. }
          transitivity (map.putmany (map.putmany m_new1 m_ry) (map.putmany m_y mStackY)).
          { apply map.disjoint_putmany_commutes.
            apply map.disjoint_putmany_l. split; [exact Hd_yry |].
            unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_ry_sY' k v2 v1 H2 H1). }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_n1_y | exact Hd_n1_sY]. }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_yry k v2 v1 H2 H1). }
            { exact Hd_ry_sY'. } } }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_y k v2 v1 H2 H1). }
            { exact Hd_yry. } }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_n1_sY k v2 v1 H2 H1). }
            { unfold map.disjoint in *; intros k v1 v2 H1 H2;
              exact (Hd_ry_sY' k v2 v1 H2 H1). } } }
        split.
        { exists m_y, mStackY.
          split; [split; [reflexivity | exact Hd_y_sY] |].
          split; [exact Hfelem_y | exact Hallocy]. }
        { exists m_new1, m_ry.
          split; [split; [reflexivity | exact Hd_n1_ry] |].
          split; [exact Hfelem_allocx | exact Hry]. } }
      { rewrite Heq_mem0_y.
        exists mStackY, (map.putmany m_new1 (map.putmany m_y m_ry)).
        split; [split |].
        { transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y m_ry)) mStackY).
          { apply map.putmany_assoc. }
          apply map.putmany_comm.
          apply map.disjoint_putmany_l. split; [exact Hd_n1_sY | exact Hd_xrx_sY]. }
        { apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_n1_sY k v2 v1 H2 H1). }
          { unfold map.disjoint in *; intros k v1 v2 H1 H2;
            exact (Hd_xrx_sY k v2 v1 H2 H1). } }
        split; [exact Hallocy | exact eq_refl]. } }
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Decompose for Fp6 mul calls === *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    pose proof (Fp12_raw_FElem_split allocx x m_new1 Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax1 [Hsp_ax [Hfe_ax0 Hfe_ax1]]]].
    destruct Hsp_ax as [Heq_new1_ax Hd_ax01].
    pose proof (Fp12_raw_FElem_split allocy y m_new2 Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay0 [m_ay1 [Hsp_ay [Hfe_ay0 Hfe_ay1]]]].
    destruct Hsp_ay as [Heq_new2_ay Hd_ay01].
    pose proof (Fp12_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o1 [Hsp_out [Hfe_o0 Hfe_o1]]]].
    destruct Hsp_out as [Heq_out_o Hd_o01].
    fp12_bounded_by_eq. destruct Hbx as [Hbx0 Hbx1]. destruct Hby as [Hby0 Hby1].
    assert (Heq_yr : map.putmany m_y m_ry = map.putmany m_out m_rr)
      by (rewrite <- Heq_mem0_y; exact Heq_m0_out).
    subst m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* === 4 Fp6 stackallocs: v0, v1, t, u === *)
    split. { apply Z_mod_mult. }
    intros pv0 mStack_v0 m3 Hstack_v0 Hm3.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros pv1 mStack_v1 m4 Hstack_v1 Hm4.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros pt mStack_t m5 Hstack_t Hm5.
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros pu mStack_u m6 Hstack_u Hm6.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok pv0) as Hfb_v0.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok pv1) as Hfb_v1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok pt) as Hfb_t.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok pu) as Hfb_u.
    unfold AbstractField.Placeholder in Hfb_v0, Hfb_v1, Hfb_t, Hfb_u.
    pose proof (proj1 (Hfb_v0 mStack_v0) Hstack_v0) as [v0_val Hv0]. clear Hfb_v0.
    pose proof (proj1 (Hfb_v1 mStack_v1) Hstack_v1) as [v1_val Hv1]. clear Hfb_v1.
    pose proof (proj1 (Hfb_t mStack_t) Hstack_t) as [t_val Hft]. clear Hfb_t.
    pose proof (proj1 (Hfb_u mStack_u) Hstack_u) as [u_val Hu]. clear Hfb_u.
    destruct Hm3 as [Heq_m3 Hd_m3]. subst m3.
    destruct Hm4 as [Heq_m4 Hd_m4]. subst m4.
    destruct Hm5 as [Heq_m5 Hd_m5]. subst m5.
    destruct Hm6 as [Heq_m6 Hd_m6]. subst m6.
    split_all_disjointness.
    rewrite <- ?map.putmany_assoc.
    (* Build master 10-way sep fact -- ay before ax to match actual memory layout *)
    assert (Hsep10 :
      (FElem_Fp6 allocy (d0_felem y) ⋆
       (FElem_Fp6 (word.add allocy (word.of_Z fp6_felem_offset)) (d1_felem y) ⋆
        (FElem_Fp6 allocx (d0_felem x) ⋆
         (FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
          (FElem_Fp6 pout (d0_felem old_out) ⋆
           (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆
            (Rr ⋆
             (FElem_Fp6 pv0 v0_val ⋆
              (FElem_Fp6 pv1 v1_val ⋆
               (FElem_Fp6 pt t_val ⋆ FElem_Fp6 pu u_val))))))))))
      (map.putmany m_ay0 (map.putmany m_ay1
        (map.putmany m_ax0 (map.putmany m_ax1
          (map.putmany m_o0 (map.putmany m_o1
            (map.putmany m_rr (map.putmany mStack_v0
              (map.putmany mStack_v1
                (map.putmany mStack_t mStack_u))))))))))).
    { exists m_ay0, (map.putmany m_ay1
        (map.putmany m_ax0 (map.putmany m_ax1
          (map.putmany m_o0 (map.putmany m_o1
            (map.putmany m_rr (map.putmany mStack_v0
              (map.putmany mStack_v1
                (map.putmany mStack_t mStack_u))))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ay0 |].
      exists m_ay1, (map.putmany m_ax0 (map.putmany m_ax1
          (map.putmany m_o0 (map.putmany m_o1
            (map.putmany m_rr (map.putmany mStack_v0
              (map.putmany mStack_v1
                (map.putmany mStack_t mStack_u)))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ay1 |].
      exists m_ax0, (map.putmany m_ax1
          (map.putmany m_o0 (map.putmany m_o1
            (map.putmany m_rr (map.putmany mStack_v0
              (map.putmany mStack_v1
                (map.putmany mStack_t mStack_u))))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax0 |].
      exists m_ax1, (map.putmany m_o0 (map.putmany m_o1
            (map.putmany m_rr (map.putmany mStack_v0
              (map.putmany mStack_v1
                (map.putmany mStack_t mStack_u)))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax1 |].
      exists m_o0, (map.putmany m_o1
            (map.putmany m_rr (map.putmany mStack_v0
              (map.putmany mStack_v1
                (map.putmany mStack_t mStack_u))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o0 |].
      exists m_o1, (map.putmany m_rr (map.putmany mStack_v0
              (map.putmany mStack_v1
                (map.putmany mStack_t mStack_u)))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o1 |].
      exists m_rr, (map.putmany mStack_v0
              (map.putmany mStack_v1
                (map.putmany mStack_t mStack_u))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hrr_out |].
      exists mStack_v0, (map.putmany mStack_v1 (map.putmany mStack_t mStack_u)).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hv0 |].
      exists mStack_v1, (map.putmany mStack_t mStack_u).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hv1 |].
      exists mStack_t, mStack_u.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hft | exact Hu]. }
    (* Locals after all stackallocs *)
    set (lall := (#{ "out" => pout; "inx" => px; "iny" => py;
                     "ax" => allocx; "ay" => allocy;
                     "v0" => pv0; "v1" => pv1; "t" => pt; "u" => pu }#)).
    (* === Call 1: v0 = mul(ax.c0, ay.c0) === *)
    exists [pv0; allocx; allocy]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul1 pv0 allocx allocy
           v0_val (d0_felem x) (d0_felem y) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_m1 m_m1 rets_m1 [Hrets_m1 [Htr_m1 [v0' [Hfeval_v0 [Hbound_v0 Hsep_m1]]]]].
    subst rets_m1. symmetry in Htr_m1. subst t_m1.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 2: v1 = mul(ax.c1, ay.c1) === *)
    exists [pv1; word.add allocx (word.of_Z fp6_felem_offset);
            word.add allocy (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul2 pv1
           (word.add allocx (word.of_Z fp6_felem_offset))
           (word.add allocy (word.of_Z fp6_felem_offset))
           v1_val (d1_felem x) (d1_felem y) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_m2 m_m2 rets_m2 [Hrets_m2 [Htr_m2 [v1' [Hfeval_v1 [Hbound_v1 Hsep_m2]]]]].
    subst rets_m2. symmetry in Htr_m2. subst t_m2.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: t = add(ax.c0, ax.c1) === *)
    exists [pt; allocx; word.add allocx (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 pt allocx
           (word.add allocx (word.of_Z fp6_felem_offset))
           t_val (d0_felem x) (d1_felem x) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_a1 m_a1 rets_a1 [Hrets_a1 [Htr_a1 [t' [Hfeval_t [Hbound_t Hsep_a1]]]]].
    subst rets_a1. symmetry in Htr_a1. subst t_a1.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 4: u = add(ay.c0, ay.c1) === *)
    exists [pu; allocy; word.add allocy (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 pu allocy
           (word.add allocy (word.of_Z fp6_felem_offset))
           u_val (d0_felem y) (d1_felem y) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_a2 m_a2 rets_a2 [Hrets_a2 [Htr_a2 [u' [Hfeval_u [Hbound_u Hsep_a2]]]]].
    subst rets_a2. symmetry in Htr_a2. subst t_a2.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 5: t = mul(t, u) === *)
    exists [pt; pt; pu]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul3 pt pt pu
           t' t' u' _ tr).
         wp_binop_precond solve_bounds. }
    intros t_m5 m_m5 rets_m5 [Hrets_m5 [Htr_m5 [t'' [Hfeval_t' [Hbound_t' Hsep_m5]]]]].
    subst rets_m5. symmetry in Htr_m5. subst t_m5.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 6: u = mul_by_v(v1) === *)
    exists [pu; pv1]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulv pu pv1
           u' v1' _ tr).
         wp_unop_precond solve_bounds. }
    intros t_mv m_mv rets_mv [Hrets_mv [Htr_mv [u'' [Hfeval_u' [Hbound_u' Hsep_mv]]]]].
    subst rets_mv. symmetry in Htr_mv. subst t_mv.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 7: out.c0 = add(v0, u) === *)
    exists [pout; pv0; pu]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd3 pout pv0 pu
           (d0_felem old_out) v0' u'' _ tr).
         wp_binop_precond solve_bounds. }
    intros t_a7 m_a7 rets_a7 [Hrets_a7 [Htr_a7 [out0' [Hfeval_out0 [Hbound_out0 Hsep_a7]]]]].
    subst rets_a7. symmetry in Htr_a7. subst t_a7.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 8: t = sub(t, v0) === *)
    exists [pt; pt; pv0]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 pt pt pv0
           t'' t'' v0' _ tr).
         wp_binop_precond solve_bounds. }
    intros t_s8 m_s8 rets_s8 [Hrets_s8 [Htr_s8 [t''' [Hfeval_t'' [Hbound_t'' Hsep_s8]]]]].
    subst rets_s8. symmetry in Htr_s8. subst t_s8.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 9: out.c1 = sub(t, v1) === *)
    exists [word.add pout (word.of_Z fp6_felem_offset); pt; pv1].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 (word.add pout (word.of_Z fp6_felem_offset)) pt pv1
           (d1_felem old_out) t''' v1' _ tr).
         wp_binop_precond solve_bounds. }
    intros t_s9 m_s9 rets_s9 [Hrets_s9 [Htr_s9 [out1' [Hfeval_out1 [Hbound_out1 Hsep_s9]]]]].
    subst rets_s9. symmetry in Htr_s9. subst t_s9.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure final sep (11 components) === *)
    (* After 9 calls, sep order is:
       A = out1' at out.c1, B = t''' at pt, C = out0' at pout,
       D = u'' at pu, E = v1' at pv1, F = v0' at pv0,
       G = d0 y at allocy, H = d1 y at allocy+off,
       I = d0 x at allocx, J = d1 x at allocx+off, K = Rr *)
    destruct Hsep_s9 as [m_A [m_rest1 [[Heq_s9 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_F [m_rest6 [[Heq_r5 Hd_F] [HF Hrest6]]]].
    destruct Hrest6 as [m_G [m_rest7 [[Heq_r6 Hd_G] [HG Hrest7]]]].
    destruct Hrest7 as [m_H [m_rest8 [[Heq_r7 Hd_H] [HH Hrest8]]]].
    destruct Hrest8 as [m_I [m_rest9 [[Heq_r8 Hd_I] [HI Hrest9]]]].
    destruct Hrest9 as [m_J [m_K [[Heq_r9 Hd_JK] [HJ HK]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m_rest7 m_rest8 m_rest9 m_s9.
    split_all_disjointness.
    pose proof (Fp6_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp6_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp6_FElem_length _ _ _ HG) as Hlen_G.
    pose proof (Fp6_FElem_length _ _ _ HH) as Hlen_H.
    pose proof (Fp6_FElem_length _ _ _ HI) as Hlen_I.
    pose proof (Fp6_FElem_length _ _ _ HJ) as Hlen_J.
    (* === Stack deallocation: u (m_D) === *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst pu _ m_D HD) as Hanybytes_u.
    unfold AbstractField.Placeholder in Hanybytes_u.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_E (map.putmany m_F (map.putmany m_G
        (map.putmany m_H (map.putmany m_I (map.putmany m_J m_K))))))))), m_D.
    split. { exact Hanybytes_u. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Stack deallocation: t (m_B) === *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst pt _ m_B HB) as Hanybytes_t.
    unfold AbstractField.Placeholder in Hanybytes_t.
    exists (map.putmany m_A (map.putmany m_C
      (map.putmany m_E (map.putmany m_F (map.putmany m_G
        (map.putmany m_H (map.putmany m_I (map.putmany m_J m_K)))))))), m_B.
    split. { exact Hanybytes_t. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Stack deallocation: v1 (m_E) === *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst pv1 _ m_E HE) as Hanybytes_v1.
    unfold AbstractField.Placeholder in Hanybytes_v1.
    exists (map.putmany m_A (map.putmany m_C
      (map.putmany m_F (map.putmany m_G
        (map.putmany m_H (map.putmany m_I (map.putmany m_J m_K))))))), m_E.
    split. { exact Hanybytes_v1. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Stack deallocation: v0 (m_F) === *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst pv0 _ m_F HF) as Hanybytes_v0.
    unfold AbstractField.Placeholder in Hanybytes_v0.
    exists (map.putmany m_A (map.putmany m_C
      (map.putmany m_G (map.putmany m_H (map.putmany m_I (map.putmany m_J m_K)))))), m_F.
    split. { exact Hanybytes_v0. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Stack deallocation: ay (m_G + m_H) === *)
    assert (Hjoin_ay : (FElem_Fp6 allocy (d0_felem y) ⋆
      FElem_Fp6 (word.add allocy (word.of_Z fp6_felem_offset)) (d1_felem y))
      (map.putmany m_G m_H)).
    { exists m_G, m_H.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HG | exact HH]. }
    pose proof (Fp12_raw_FElem_join allocy (d0_felem y) (d1_felem y)
      (map.putmany m_G m_H) Hlen_G Hlen_H Hjoin_ay) as Hfp12_ay.
    rewrite Fp12_list_decomp in Hfp12_ay.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocy y
      (map.putmany m_G m_H) Hfp12_ay) as Hanybytes_ay.
    unfold AbstractField.Placeholder in Hanybytes_ay.
    exists (map.putmany m_A (map.putmany m_C (map.putmany m_I (map.putmany m_J m_K)))),
      (map.putmany m_G m_H).
    split. { exact Hanybytes_ay. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Stack deallocation: ax (m_I + m_J) === *)
    assert (Hjoin_ax : (FElem_Fp6 allocx (d0_felem x) ⋆
      FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x))
      (map.putmany m_I m_J)).
    { exists m_I, m_J.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HI | exact HJ]. }
    pose proof (Fp12_raw_FElem_join allocx (d0_felem x) (d1_felem x)
      (map.putmany m_I m_J) Hlen_I Hlen_J Hjoin_ax) as Hfp12_ax.
    rewrite Fp12_list_decomp in Hfp12_ax.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocx x
      (map.putmany m_I m_J) Hfp12_ax) as Hanybytes_ax.
    unfold AbstractField.Placeholder in Hanybytes_ax.
    exists (map.putmany m_A (map.putmany m_C m_K)),
      (map.putmany m_I m_J).
    split. { exact Hanybytes_ax. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1').
    assert (Hd0_app : d0_felem (out0' ++ out1') = out0').
    { apply d0_felem_app. exact Hlen_C. }
    assert (Hd1_app : d1_felem (out0' ++ out1') = out1').
    { apply d1_felem_app. exact Hlen_C. }
    split.
    { (* feval -- rewrite in dependency order: outermost first, then expand *)
      fp12_feval_eq. rewrite Hd0_app, Hd1_app.
      rewrite Hfeval_out0, Hfeval_out1.
      rewrite Hfeval_t''.                     (* t''' -> sub t'' v0' *)
      rewrite Hfeval_u'.                      (* u'' -> mul_by_v v1' *)
      rewrite Hfeval_t'.                      (* t'' -> mul t' u' *)
      rewrite Hfeval_t, Hfeval_u.            (* t' -> add a0 a1, u' -> add b0 b1 *)
      rewrite Hfeval_v0, Hfeval_v1.          (* v0' -> mul a0 b0, v1' -> mul a1 b1 *)
      (* Fp12.v now imports Fp6.v, so operations are definitionally equal *)
      cbv [AbstractField.bin_model AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub
           AbstractField.Fmul AbstractField.Fadd AbstractField.Fsub
           Fp12_fp_inst Fp12_field_parameters
           DodecicFieldExtensionsSpecs.fp12_mul_fn
           BLS12Fp12Spec.fp12_mul BLS12Fp12Spec.fp12_c0 BLS12Fp12Spec.fp12_c1
           BLS12Fp12Spec.mk_fp12 fst snd
           Fp6_fp_inst Fp6_field_parameters
           CubicFieldExtensionsSpecs.fp6_add_fn CubicFieldExtensionsSpecs.fp6_sub_fn
           CubicFieldExtensionsSpecs.fp6_mul_fn
           AbstractField.un_model un_Fp6_mul_by_v fp6_mul_by_v_model
           BLS12Fp6Spec.fp6_mul_by_v BLS12Fp6Spec.fp6_c0 BLS12Fp6Spec.fp6_c1
           BLS12Fp6Spec.fp6_c2 BLS12Fp6Spec.fp6_build].
      (* Bridge module aliases: convert goal-only occurrences *)
      match goal with |- ?L = ?R =>
        let R' := eval cbv [Fp6.fp6_add Fp6.fp6_sub Fp6.fp6_mul Fp6.fp6_mul_by_v
                            Fp6.fp6_c0 Fp6.fp6_c1 Fp6.fp6_c2 Fp6.fp6_build] in R in
        change (L = R')
      end.
      cbv [BLS12Fp6Spec.fp6_add BLS12Fp6Spec.fp6_sub BLS12Fp6Spec.fp6_mul
           BLS12Fp6Spec.fp6_mul_by_v
           BLS12Fp6Spec.fp6_c0 BLS12Fp6Spec.fp6_c1 BLS12Fp6Spec.fp6_c2
           BLS12Fp6Spec.fp6_build].
      reflexivity. }
    split.
    { fp12_bounded_by_eq. rewrite Hd0_app, Hd1_app.
      split; solve_bounds. }
    { assert (Hjoin_out : (FElem_Fp6 pout out0' ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1')
        (map.putmany m_C m_A)).
      { exists m_C, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC | exact HA]. }
      pose proof (Fp12_raw_FElem_join pout out0' out1'
        (map.putmany m_C m_A) Hlen_C Hlen_A Hjoin_out) as Hfp12_out.
      exists (map.putmany m_C m_A), m_K.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out | exact HK]. }
  Qed.

End Fp12.
