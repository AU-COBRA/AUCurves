(** * Standalone compilation unit for the Fp12_sqr_ok proof.
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
  Instance spec_of_Fp6_square : spec_of (AbstractField.square (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_square (F:=Fp6).

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
  (* Fp12 copy and sqr definitions (needed for specs)                  *)
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

  Definition Fp12_sqr : function_t :=
    (AbstractField.square (F:=Fp12), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as allocx;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "allocx"; expr.var "x"]);
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t0;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t2;
      (* t0 = a0^2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp6)) [expr.var "t0"; expr_fp12_c0 (expr.var "allocx")]);
      (* t1 = a1^2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp6)) [expr.var "t1"; expr_fp12_c1 (expr.var "allocx")]);
      (* t2 = a0*a1 -- last read of allocx *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr.var "t2"; expr_fp12_c0 (expr.var "allocx"); expr_fp12_c1 (expr.var "allocx")]);
      (* t1 = mul_by_v(a1^2) *)
      coq:(cmd.call [] fp6_mul_by_v_name [expr.var "t1"; expr.var "t1"]);
      (* out.c0 = t0 + mul_by_v(a1^2) *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr.var "t0"; expr.var "t1"]);
      (* out.c1 = 2*a0*a1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr.var "t2"; expr.var "t2"])
    ))).

  Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
    AbstractField.unop_spec AbstractField.un_square (F:=Fp12).

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
  (* Fp ring instance for algebraic bridge lemma                       *)
  (* ================================================================ *)

  Add Ring Fp_ring : (ModularArithmeticTheorems.F.ring_theory M_pos).

  (* Bridge: 2*a*b = (a+b)^2 - a^2 - b^2 at Fp6 level *)
  Local Lemma fp6_double_eq_karatsuba (a0 a1 : Fp6) :
    @AbstractField.Fadd _ Fp6_fp_inst
      (@AbstractField.Fmul _ Fp6_fp_inst a0 a1)
      (@AbstractField.Fmul _ Fp6_fp_inst a0 a1) =
    @AbstractField.Fsub _ Fp6_fp_inst
      (@AbstractField.Fsub _ Fp6_fp_inst
        (@AbstractField.Fmul _ Fp6_fp_inst
          (@AbstractField.Fadd _ Fp6_fp_inst a0 a1)
          (@AbstractField.Fadd _ Fp6_fp_inst a0 a1))
        (@AbstractField.Fmul _ Fp6_fp_inst a0 a0))
      (@AbstractField.Fmul _ Fp6_fp_inst a1 a1).
  Proof.
    destruct a0 as [[a00 a01] a02]. destruct a1 as [[a10 a11] a12].
    destruct a00 as [a000 a001]. destruct a01 as [a010 a011].
    destruct a02 as [a020 a021]. destruct a10 as [a100 a101].
    destruct a11 as [a110 a111]. destruct a12 as [a120 a121].
    cbv [Fadd Fsub Fmul Fp6_fp_inst Fp6_field_parameters
         CubicFieldExtensionsSpecs.fp6_add_fn CubicFieldExtensionsSpecs.fp6_sub_fn
         CubicFieldExtensionsSpecs.fp6_mul_fn
         BLS12Fp6Spec.fp6_add BLS12Fp6Spec.fp6_sub BLS12Fp6Spec.fp6_mul
         BLS12Fp6Spec.fp6_build BLS12Fp6Spec.fp6_c0 BLS12Fp6Spec.fp6_c1 BLS12Fp6Spec.fp6_c2
         fst snd BLS12Fp6Spec.fp2_add BLS12Fp6Spec.fp2_sub BLS12Fp6Spec.fp2_mul
         BLS12Fp6Spec.fp2_mul_xi].
    repeat (apply pair_equal_spec; split); ring.
  Qed.

  (* Same lemma stated with BLS12Fp6Spec to match the goal after cbv *)
  Local Corollary fp6_double_eq_karatsuba_concrete (a0 a1 : Fp6) :
    BLS12Fp6Spec.fp6_add M_pos
      (BLS12Fp6Spec.fp6_mul M_pos beta xi_re xi_im a0 a1)
      (BLS12Fp6Spec.fp6_mul M_pos beta xi_re xi_im a0 a1) =
    BLS12Fp6Spec.fp6_sub M_pos
      (BLS12Fp6Spec.fp6_sub M_pos
        (BLS12Fp6Spec.fp6_mul M_pos beta xi_re xi_im
          (BLS12Fp6Spec.fp6_add M_pos a0 a1)
          (BLS12Fp6Spec.fp6_add M_pos a0 a1))
        (BLS12Fp6Spec.fp6_mul M_pos beta xi_re xi_im a0 a0))
      (BLS12Fp6Spec.fp6_mul M_pos beta xi_re xi_im a1 a1).
  Proof. exact (fp6_double_eq_karatsuba a0 a1). Qed.

  (* ================================================================ *)
  (* The Fp12_sqr_ok proof                                             *)
  (* ================================================================ *)

  Lemma Fp12_sqr_ok : program_logic_goal_for_function! Fp12_sqr.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy HFsqr1 HFsqr2 HFmul HFmulv HFadd1 HFadd2.
    unfold spec_of_Fp12_sqr, AbstractField.unop_spec.
    intros pout px old_out x Rr tr mem0
      [Hbx [[Rx Hmemx] Hmemout]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_sqr].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst word_ok mem_ok allocx) as Hfbx.
    unfold AbstractField.Placeholder in Hfbx.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === Fp12 copy: x -> allocx === *)
    repeat straightline.
    exists [allocx; px]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy allocx px allocx_val x
        Rx (eq (map.putmany m_x m_rx)) tr).
      split.
      { exists (map.putmany m_x mStackX), m_rx.
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split.
        { exists m_x, mStackX.
          split; [split; [reflexivity | exact Hd_x_sX] |].
          split; [exact Hfx | exact Hallocx]. }
        { exact Hrx. } }
      { exists mStackX, (map.putmany m_x m_rx).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split; [exact Hallocx | exact eq_refl]. } }
    intros t' m' rets [Hrets [Htr Hsep_copy]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    destruct Hsep_copy as [m_new [m_frame [[Heq_m' Hd_n_f] [Hfelem_allocx Hframe]]]].
    subst m_frame m'.
    pose proof (Fp12_raw_FElem_split allocx x m_new Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax1 [Hsp_ax [Hfe_ax0 Hfe_ax1]]]].
    destruct Hsp_ax as [Heq_new_ax Hd_ax01].
    pose proof (Fp12_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o1 [Hsp_out [Hfe_o0 Hfe_o1]]]].
    destruct Hsp_out as [Heq_out_o Hd_o01].
    fp12_bounded_by_eq. destruct Hbx as [Hbx0 Hbx1].
    assert (Heq_xr : map.putmany m_x m_rx = map.putmany m_out m_rr)
      by exact Heq_m0_out.
    subst m_out m_new.
    rewrite Heq_xr in Hd_n_f. rewrite Heq_xr.
    (* === Stackalloc t0 === *)
    split. { apply Z_mod_mult. }
    intros pt0 mStack0 m2 Hstack0 Hm2.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok pt0) as Hfb0.
    unfold AbstractField.Placeholder in Hfb0.
    pose proof (proj1 (Hfb0 mStack0) Hstack0) as [t0_val Ht0]. clear Hfb0.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    repeat straightline.
    (* === Stackalloc t1 === *)
    split. { apply Z_mod_mult. }
    intros pt1 mStack1 m3 Hstack1 Hm3.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok pt1) as Hfb1.
    unfold AbstractField.Placeholder in Hfb1.
    pose proof (proj1 (Hfb1 mStack1) Hstack1) as [t1_val Ht1]. clear Hfb1.
    destruct Hm3 as [Heq_m3 Hd_m3]. subst m3.
    repeat straightline.
    (* === Stackalloc t2 === *)
    split. { apply Z_mod_mult. }
    intros pt2 mStack2 m4 Hstack2 Hm4.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok pt2) as Hfb2.
    unfold AbstractField.Placeholder in Hfb2.
    pose proof (proj1 (Hfb2 mStack2) Hstack2) as [t2_val Ht2]. clear Hfb2.
    destruct Hm4 as [Heq_m4 Hd_m4]. subst m4.
    split_all_disjointness.
    rewrite <- ?map.putmany_assoc.
    (* Build master sep matching right-associated goal memory *)
    assert (Hsep8 :
      (FElem_Fp6 allocx (d0_felem x) ⋆
       (FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
        (FElem_Fp6 pout (d0_felem old_out) ⋆
         (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆
          (Rr ⋆
           (FElem_Fp6 pt0 t0_val ⋆
            (FElem_Fp6 pt1 t1_val ⋆ FElem_Fp6 pt2 t2_val)))))))
      (map.putmany m_ax0 (map.putmany m_ax1
        (map.putmany m_o0 (map.putmany m_o1
          (map.putmany m_rr (map.putmany mStack0
            (map.putmany mStack1 mStack2)))))))).
    { exists m_ax0, (map.putmany m_ax1
        (map.putmany m_o0 (map.putmany m_o1
          (map.putmany m_rr (map.putmany mStack0
            (map.putmany mStack1 mStack2)))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax0 |].
      exists m_ax1, (map.putmany m_o0 (map.putmany m_o1
          (map.putmany m_rr (map.putmany mStack0
            (map.putmany mStack1 mStack2))))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_ax1 |].
      exists m_o0, (map.putmany m_o1
          (map.putmany m_rr (map.putmany mStack0
            (map.putmany mStack1 mStack2)))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o0 |].
      exists m_o1, (map.putmany m_rr (map.putmany mStack0
            (map.putmany mStack1 mStack2))).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfe_o1 |].
      exists m_rr, (map.putmany mStack0 (map.putmany mStack1 mStack2)).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hrr_out |].
      exists mStack0, (map.putmany mStack1 mStack2).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ht0 |].
      exists mStack1, mStack2.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ht1 | exact Ht2]. }
    (* === Call 1: t0 = square(allocx.c0) === *)
    exists [pt0; allocx]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr1 pt0 allocx t0_val (d0_felem x) _ tr).
         wp_unop_precond solve_bounds. }
    intros t_sq1 m_sq1 rets_sq1 [Hrets_sq1 [Htr_sq1 [t0' [Hfeval_t0 [Hbound_t0 Hsep_sq1]]]]].
    subst rets_sq1. symmetry in Htr_sq1. subst t_sq1.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => pt0; "t1" => pt1; "t2" => pt2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 2: t1 = square(allocx.c1) === *)
    exists [pt1; word.add allocx (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr2 pt1 (word.add allocx (word.of_Z fp6_felem_offset))
           t1_val (d1_felem x) _ tr).
         wp_unop_precond solve_bounds. }
    intros t_sq2 m_sq2 rets_sq2 [Hrets_sq2 [Htr_sq2 [t1' [Hfeval_t1 [Hbound_t1 Hsep_sq2]]]]].
    subst rets_sq2. symmetry in Htr_sq2. subst t_sq2.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => pt0; "t1" => pt1; "t2" => pt2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: t2 = mul(allocx.c0, allocx.c1) === *)
    exists [pt2; allocx; word.add allocx (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul pt2 allocx (word.add allocx (word.of_Z fp6_felem_offset))
           t2_val (d0_felem x) (d1_felem x) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_mul m_mul rets_mul [Hrets_mul [Htr_mul [t2' [Hfeval_t2 [Hbound_t2 Hsep_mul]]]]].
    subst rets_mul. symmetry in Htr_mul. subst t_mul.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => pt0; "t1" => pt1; "t2" => pt2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 4: t1 = mul_by_v(t1) === *)
    exists [pt1; pt1]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulv pt1 pt1 t1' t1' _ tr).
         wp_unop_precond solve_bounds. }
    intros t_mbv m_mbv rets_mbv [Hrets_mbv [Htr_mbv [t1'' [Hfeval_t1' [Hbound_t1' Hsep_mbv]]]]].
    subst rets_mbv. symmetry in Htr_mbv. subst t_mbv.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => pt0; "t1" => pt1; "t2" => pt2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 5: out.c0 = add(t0, t1) === *)
    exists [pout; pt0; pt1]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 pout pt0 pt1 (d0_felem old_out) t0' t1'' _ tr).
         wp_binop_precond solve_bounds. }
    intros t_add1 m_add1 rets_add1 [Hrets_add1 [Htr_add1 [out0' [Hfeval_out0 [Hbound_out0 Hsep_add1]]]]].
    subst rets_add1. symmetry in Htr_add1. subst t_add1.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => pt0; "t1" => pt1; "t2" => pt2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 6: out.c1 = add(t2, t2) === *)
    exists [word.add pout (word.of_Z fp6_felem_offset); pt2; pt2].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 (word.add pout (word.of_Z fp6_felem_offset)) pt2 pt2
           (d1_felem old_out) t2' t2' _ tr).
         wp_binop_precond solve_bounds. }
    intros t_add2 m_add2 rets_add2 [Hrets_add2 [Htr_add2 [out1' [Hfeval_out1 [Hbound_out1 Hsep_add2]]]]].
    subst rets_add2. symmetry in Htr_add2. subst t_add2.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => pt0; "t1" => pt1; "t2" => pt2 }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure final sep === *)
    (* Sep star order after 6 calls (determined by ecancel):
       A = out1' (at out.c1), B = out0' (at out.c0),
       C = t1'' (at pt1), D = t2' (at pt2), E = t0' (at pt0),
       F = d0_felem x (at allocx), G = d1_felem x (at allocx+off),
       H = Rr *)
    destruct Hsep_add2 as [m_A [m_rest1 [[Heq_add2 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_F [m_rest6 [[Heq_r5 Hd_F] [HF Hrest6]]]].
    destruct Hrest6 as [m_G [m_H [[Heq_r6 Hd_GH] [HG HH]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_rest6 m_add2.
    split_all_disjointness.
    pose proof (Fp6_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp6_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp6_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp6_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp6_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp6_FElem_length _ _ _ HF) as Hlen_F.
    pose proof (Fp6_FElem_length _ _ _ HG) as Hlen_G.
    (* === Stack deallocation: t2 (m_D) === *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst pt2 _ m_D HD) as Hanybytes_t2.
    unfold AbstractField.Placeholder in Hanybytes_t2.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C
      (map.putmany m_E (map.putmany m_F (map.putmany m_G m_H)))))), m_D.
    split. { exact Hanybytes_t2. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Stack deallocation: t1 (m_C) === *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst pt1 _ m_C HC) as Hanybytes_t1.
    unfold AbstractField.Placeholder in Hanybytes_t1.
    exists (map.putmany m_A (map.putmany m_B
      (map.putmany m_E (map.putmany m_F (map.putmany m_G m_H))))), m_C.
    split. { exact Hanybytes_t1. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Stack deallocation: t0 (m_E) === *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst pt0 _ m_E HE) as Hanybytes_t0.
    unfold AbstractField.Placeholder in Hanybytes_t0.
    exists (map.putmany m_A (map.putmany m_B
      (map.putmany m_F (map.putmany m_G m_H)))), m_E.
    split. { exact Hanybytes_t0. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Stack deallocation: allocx (m_F + m_G) === *)
    assert (Hjoin_ax : (FElem_Fp6 allocx (d0_felem x) ⋆
      FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x))
      (map.putmany m_F m_G)).
    { exists m_F, m_G.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HF | exact HG]. }
    pose proof (Fp12_raw_FElem_join allocx (d0_felem x) (d1_felem x)
      (map.putmany m_F m_G) Hlen_F Hlen_G Hjoin_ax) as Hfp12_ax.
    rewrite Fp12_list_decomp in Hfp12_ax.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocx x
      (map.putmany m_F m_G) Hfp12_ax) as Hanybytes_ax.
    unfold AbstractField.Placeholder in Hanybytes_ax.
    exists (map.putmany m_A (map.putmany m_B m_H)), (map.putmany m_F m_G).
    split. { exact Hanybytes_ax. }
    split. { split. { solve_putmany_eq. } { map_disjoint_auto. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1').
    assert (Hd0_app : d0_felem (out0' ++ out1') = out0').
    { apply d0_felem_app. exact Hlen_B. }
    assert (Hd1_app : d1_felem (out0' ++ out1') = out1').
    { apply d1_felem_app. exact Hlen_B. }
    split.
    { fp12_feval_eq. rewrite Hd0_app, Hd1_app.
      rewrite Hfeval_out0, Hfeval_out1.
      rewrite Hfeval_t0, Hfeval_t1'.
      cbv [AbstractField.un_model AbstractField.un_square AbstractField.Fsquare].
      rewrite Hfeval_t1, Hfeval_t2.
      set (a0 := @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem x)).
      set (a1 := @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem x)).
      (* LHS has bin_model (Fp6 level). Unfold fully to BLS12Fp6Spec.fp6_* *)
      cbv [AbstractField.bin_model AbstractField.bin_mul AbstractField.bin_add
           AbstractField.Fadd AbstractField.Fmul
           Fp6_fp_inst Fp6_field_parameters
           CubicFieldExtensionsSpecs.fp6_mul_fn CubicFieldExtensionsSpecs.fp6_add_fn
           AbstractField.un_model un_Fp6_mul_by_v fp6_mul_by_v_model].
      (* RHS has Fp12 Fmul. Unfold to Fp6.fp6_* (from Fp12.v's Let bindings) *)
      cbv [AbstractField.Fmul Fp12_fp_inst Fp12_field_parameters
           DodecicFieldExtensionsSpecs.fp12_mul_fn
           BLS12Fp12Spec.fp12_mul BLS12Fp12Spec.fp12_c0 BLS12Fp12Spec.fp12_c1
           BLS12Fp12Spec.mk_fp12 fst snd].
      (* LHS has BLS12Fp6Spec.fp6_*, RHS has Fp6.fp6_*.
         These are the same module (Module BLS12Fp6Spec := Fp6),
         so we convert RHS to use BLS12Fp6Spec names. *)
      change (Fp6.fp6_add M_pos) with (BLS12Fp6Spec.fp6_add M_pos).
      change (Fp6.fp6_sub M_pos) with (BLS12Fp6Spec.fp6_sub M_pos).
      change (Fp6.fp6_mul M_pos) with (BLS12Fp6Spec.fp6_mul M_pos).
      change (Fp6.fp6_mul_by_v M_pos) with (BLS12Fp6Spec.fp6_mul_by_v M_pos).
      (* Now both sides use BLS12Fp6Spec.fp6_* *)
      (* Use Karatsuba identity to rewrite c1 component, then close *)
      subst a0 a1.
      rewrite (fp6_double_eq_karatsuba_concrete
        (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem x))
        (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem x))).
      reflexivity. }
    split.
    { fp12_bounded_by_eq. rewrite Hd0_app, Hd1_app.
      split; solve_bounds. }
    { assert (Hjoin_out : (FElem_Fp6 pout out0' ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1')
        (map.putmany m_B m_A)).
      { exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp12_raw_FElem_join pout out0' out1'
        (map.putmany m_B m_A) Hlen_B Hlen_A Hjoin_out) as Hfp12_out.
      exists (map.putmany m_B m_A), m_H.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out | exact HH]. }
  Qed.

End Fp12.
