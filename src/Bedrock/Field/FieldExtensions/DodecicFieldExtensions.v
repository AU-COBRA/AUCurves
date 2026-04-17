(** * Rupicola compilation layer for dodecic extensions (Fp12 = Fp6[w]/(w^2 - v)).

    Analogous to CubicFieldExtensions.v for Fp6.

    Defines bedrock2 function bodies for Fp12 operations.  Includes a
    fp6_mul_by_v helper (shift Fp6 components + mul_xi), Karatsuba Fp12
    multiplication, Fp12 squaring, conjugation, and full Fp12 inverse.
    WP proofs are currently stubs (exact I).
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

  Local Definition fp2_mul_xi_name := (fp2_prefix ++ "mul_xi")%string.
  Local Definition fp6_mul_by_v_name := (fp6_prefix ++ "mul_by_v")%string.

  (* ================================================================ *)
  (* Offset helpers                                                    *)
  (* ================================================================ *)

  (* Fp2-level offsets within an Fp6 element *)
  Local Notation fp2_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
  Local Definition expr_fp6_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp6_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp2_felem_offset).
  Local Definition expr_fp6_c2 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal (2 * fp2_felem_offset)).

  (* Fp6-level offsets within an Fp12 element *)
  Local Notation fp6_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp6))).
  Local Definition expr_fp12_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp12_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp6_felem_offset).

  (* ================================================================ *)
  (* spec_of instances for underlying operations                       *)
  (* ================================================================ *)

  (* Fp2-level (needed by fp6_mul_by_v) *)
  Instance spec_of_Fp2_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) :=
    AbstractField.spec_of_felem_copy.

  Local Instance un_Fp2_mul_xi_local
    : @AbstractField.UnOp _ _ _ _ Fp2 Fp2_fp_inst Fp2_repr_inst fp2_mul_xi_name :=
    @CubicFieldExtensions.un_Fp2_mul_xi _ _ _ _ prime_parameters beta xi_re xi_im F_representation fp2_prefix.

  Instance spec_of_Fp2_mul_xi_local : spec_of fp2_mul_xi_name :=
    AbstractField.unop_spec (field_representation:=Fp2_repr_inst) un_Fp2_mul_xi_local.

  (* Fp6-level (needed by Fp12 function bodies) *)
  Instance spec_of_Fp6_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp6)) :=
    AbstractField.spec_of_felem_copy (F:=Fp6).
  Instance spec_of_Fp6_add : spec_of (AbstractField.add (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp6).
  Instance spec_of_Fp6_mul : spec_of (AbstractField.mul (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp6).
  Instance spec_of_Fp6_sub : spec_of (AbstractField.sub (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp6).
  Instance spec_of_Fp6_opp : spec_of (AbstractField.opp (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=Fp6).
  Instance spec_of_Fp6_square : spec_of (AbstractField.square (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_square (F:=Fp6).
  Instance spec_of_Fp6_inv : spec_of (AbstractField.inv (F:=Fp6)) :=
    AbstractField.unop_spec AbstractField.un_inv (F:=Fp6).

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
  (* Fp ring instance for algebraic bridge lemmas                      *)
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

  (* Bridge: BLS12Fp6Spec.fp6_* = Fp6.fp6_* (both are module aliases for the same thing) *)
  Local Lemma fp6_add_bridge : BLS12Fp6Spec.fp6_add M_pos = Fp6.fp6_add M_pos.
  Proof. reflexivity. Qed.
  Local Lemma fp6_sub_bridge : BLS12Fp6Spec.fp6_sub M_pos = Fp6.fp6_sub M_pos.
  Proof. reflexivity. Qed.
  Local Lemma fp6_mul_bridge : BLS12Fp6Spec.fp6_mul M_pos = Fp6.fp6_mul M_pos.
  Proof. reflexivity. Qed.
  Local Lemma fp6_mul_by_v_bridge : BLS12Fp6Spec.fp6_mul_by_v M_pos = Fp6.fp6_mul_by_v M_pos.
  Proof. reflexivity. Qed.
  Local Lemma fp6_neg_bridge : BLS12Fp6Spec.fp6_neg M_pos = Fp6.fp6_neg M_pos.
  Proof. reflexivity. Qed.
  Local Lemma fp6_inv_bridge : BLS12Fp6Spec.fp6_inv M_pos = Fp6.fp6_inv M_pos.
  Proof. reflexivity. Qed.
  Local Lemma fp6_sqr_bridge : BLS12Fp6Spec.fp6_sqr M_pos = Fp6.fp6_sqr M_pos.
  Proof. reflexivity. Qed.

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

  Local Ltac map_swap a b :=
    rewrite (map.putmany_assoc a b);
    let D := fresh "D" in
    assert (D : map.disjoint a b) by map_disjoint_auto;
    rewrite (map.putmany_comm a b D);
    clear D;
    rewrite <- (map.putmany_assoc b a).

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
      | (* Fallback: target is the rightmost element — bubble it up *)
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

  (* -------------------------------------------------------------- *)
  (* fp6_mul_by_v: multiply Fp6 by v (shift + mul_xi)                 *)
  (*   v * (c0, c1, c2) = (xi*c2, c0, c1)                            *)
  (* -------------------------------------------------------------- *)

  Definition Fp6_mul_by_v : function_t :=
    (fp6_mul_by_v_name, (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as tmp;
      (* Copy x to tmp to handle aliasing *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr.var "tmp"; expr.var "x"]);
      (* out.c0 = mul_xi(tmp.c2) *)
      coq:(cmd.call [] fp2_mul_xi_name [expr_fp6_c0 (expr.var "out"); expr_fp6_c2 (expr.var "tmp")]);
      (* out.c1 = tmp.c0 *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c1 (expr.var "out"); expr_fp6_c0 (expr.var "tmp")]);
      (* out.c2 = tmp.c1 *)
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr_fp6_c2 (expr.var "out"); expr_fp6_c1 (expr.var "tmp")])
    ))).

  (* Gallina model for mul_by_v: shift Fp6 components, mul_xi on c2 *)
  Local Definition fp6_mul_by_v_model (x : Fp6) : Fp6 :=
    ((BLS12Fp6Spec.fp2_mul_xi M_pos beta xi_re xi_im (snd x), fst (fst x)), snd (fst x)).

  Local Instance un_Fp6_mul_by_v
    : @AbstractField.UnOp _ _ _ _ Fp6 Fp6_fp_inst Fp6_repr_inst fp6_mul_by_v_name :=
    {| AbstractField.un_model := fp6_mul_by_v_model;
       AbstractField.un_xbounds := @AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst;
       AbstractField.un_outbounds := @AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst |}.

  Instance spec_of_Fp6_mul_by_v : spec_of fp6_mul_by_v_name :=
    AbstractField.unop_spec un_Fp6_mul_by_v.

  Local Notation FElem_Fp2 := (@AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
  Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).

  Local Ltac fp6_feval_eq :=
    change (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
      (fun ws => ((@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c0_felem ws),
                   @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c1_felem ws)),
                  @AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (c2_felem ws)));
    cbv beta.

  Local Ltac fp6_bounded_by_eq :=
    change (@AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) with
      (fun b felem => @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c0_felem felem)
                   /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c1_felem felem)
                   /\ @AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst b (c2_felem felem));
    cbv beta.

  Lemma Fp6_mul_by_v_ok : program_logic_goal_for_function! Fp6_mul_by_v.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy6 HFmulxi HFcopy2a HFcopy2b.
    unfold spec_of_Fp6_mul_by_v, AbstractField.unop_spec.
    intros pout px old_out x Rr tr mem0
      [Hbx [[Rx Hmemx] Hmemout]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp6_mul_by_v].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc tmp === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    (* FElem_from_bytes *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok allocx) as Hfbx.
    unfold AbstractField.Placeholder in Hfbx.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    (* Decompose memory *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === Fp6 copy: x → tmp === *)
    repeat straightline.
    exists [allocx; px]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy6 allocx px allocx_val x
        Rx
        (eq (map.putmany m_x m_rx))
        tr).
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
    (* Post copy *)
    intros t' m' rets [Hrets [Htr Hsep_copy]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "tmp" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Decompose copy postcondition === *)
    destruct Hsep_copy as [m_new [m_frame [[Heq_m' Hd_n_f] [Hfelem_allocx Hframe]]]].
    subst m_frame m'.
    (* Split Fp6 FElems into 3 Fp2 components *)
    pose proof (@CubicFieldExtensions.Fp6_raw_FElem_split _ _ _ _ word_ok mem_ok
      prime_parameters beta xi_re xi_im F_representation fp6_prefix fp2_prefix
      allocx x m_new Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax12 [Hsp_ax [Hfe_ax0 Hax12]]]].
    destruct Hsp_ax as [Heq_new_ax Hd_ax0_12].
    destruct Hax12 as [m_ax1 [m_ax2 [Hsp_ax12 [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax12 as [Heq_ax12 Hd_ax12].
    (* Split output FElem *)
    pose proof (@CubicFieldExtensions.Fp6_raw_FElem_split _ _ _ _ word_ok mem_ok
      prime_parameters beta xi_re xi_im F_representation fp6_prefix fp2_prefix
      pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o12 [Hsp_out [Hfe_o0 Ho12]]]].
    destruct Hsp_out as [Heq_out_o Hd_o0_12].
    destruct Ho12 as [m_o1 [m_o2 [Hsp_o12 [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_o12 as [Heq_o12 Hd_o12].
    (* Decompose bounded_by at Fp2 level *)
    fp6_bounded_by_eq. destruct Hbx as [Hbx0 [Hbx1 Hbx2]].
    (* Relate memory *)
    assert (Heq_xr : map.putmany m_x m_rx = map.putmany m_out m_rr)
      by exact Heq_m0_out.
    subst m_ax12 m_o12 m_out m_new.
    rewrite Heq_xr in Hd_n_f.
    rewrite Heq_xr.
    (* Build master 7-way sep fact (before split_all_disjointness clears Hd_n_f) *)
    assert (Hsep7 :
      ((FElem_Fp2 allocx (c0_felem x) ⋆
        (FElem_Fp2 (word.add allocx (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆
         FElem_Fp2 (word.add allocx (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x))) ⋆
       ((FElem_Fp2 pout (c0_felem old_out) ⋆
         (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem old_out) ⋆
          FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem old_out))) ⋆ Rr))
      (map.putmany (map.putmany m_ax0 (map.putmany m_ax1 m_ax2))
        (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr))).
    { exists (map.putmany m_ax0 (map.putmany m_ax1 m_ax2)),
        (map.putmany (map.putmany m_o0 (map.putmany m_o1 m_o2)) m_rr).
      split; [split; [reflexivity | exact Hd_n_f] |].
      split.
      { exists m_ax0, (map.putmany m_ax1 m_ax2).
        split; [split; [reflexivity | exact Hd_ax0_12] |].
        split; [exact Hfe_ax0 |].
        exists m_ax1, m_ax2.
        split; [split; [reflexivity | exact Hd_ax12] |].
        split; [exact Hfe_ax1 | exact Hfe_ax2]. }
      exists (map.putmany m_o0 (map.putmany m_o1 m_o2)), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, (map.putmany m_o1 m_o2).
        split; [split; [reflexivity | exact Hd_o0_12] |].
        split; [exact Hfe_o0 |].
        exists m_o1, m_o2.
        split; [split; [reflexivity | exact Hd_o12] |].
        split; [exact Hfe_o1 | exact Hfe_o2]. }
      exact Hrr_out. }
    (* === mul_xi call: out.c0 = mul_xi(tmp.c2) === *)
    exists [pout; word.add allocx (word.of_Z (2 * fp2_felem_offset))].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmulxi pout
           (word.add allocx (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
           (c0_felem old_out) (c2_felem x) _ tr).
         wp_unop_precond solve_bounds. }
    (* Post mul_xi *)
    intros t_xi m_xi rets_xi [Hrets_xi [Htr_xi [out0' [Hfeval0 [Hbound0 Hsep_xi]]]]].
    subst rets_xi. symmetry in Htr_xi. subst t_xi.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "tmp" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Fp2 copy: out.c1 = tmp.c0 === *)
    exists [word.add pout (word.of_Z fp2_felem_offset); allocx].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy2a (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
               allocx
               (c1_felem old_out) (c0_felem x)
               _ _ tr).
      split.
      { pose proof Hsep_xi as H'. ecancel_assumption. }
      { pose proof Hsep_xi as H'. ecancel_assumption. } }
    (* Post Fp2 copy c1 *)
    intros t_c1 m_c1 rets_c1 [Hrets_c1 [Htr_c1 Hsep_c1]].
    subst rets_c1. symmetry in Htr_c1. subst t_c1.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "tmp" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Fp2 copy: out.c2 = tmp.c1 === *)
    exists [word.add pout (word.of_Z (2 * fp2_felem_offset));
            word.add allocx (word.of_Z fp2_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy2b (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix))
               (word.add allocx (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix))
               (c2_felem old_out) (c1_felem x)
               _ _ tr).
      split.
      { pose proof Hsep_c1 as H'. ecancel_assumption. }
      { pose proof Hsep_c1 as H'. ecancel_assumption. } }
    (* Post Fp2 copy c2 *)
    intros t_c2 m_c2 rets_c2 [Hrets_c2 [Htr_c2 Hsep_c2]].
    subst rets_c2. symmetry in Htr_c2. subst t_c2.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "tmp" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure Hsep_c2 into map components === *)
    destruct Hsep_c2 as [m_A [m_rest1 [[Heq_c2 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_F [m_G [[Heq_r5 Hd_FG] [HF HG]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_c2.
    split_all_disjointness.
    pose proof (@CubicFieldExtensions.Fp2_FElem_length _ _ _ _ prime_parameters beta F_representation fp2_prefix _ _ _ HA) as Hlen_A.
    pose proof (@CubicFieldExtensions.Fp2_FElem_length _ _ _ _ prime_parameters beta F_representation fp2_prefix _ _ _ HB) as Hlen_B.
    pose proof (@CubicFieldExtensions.Fp2_FElem_length _ _ _ _ prime_parameters beta F_representation fp2_prefix _ _ _ HC) as Hlen_C.
    pose proof (@CubicFieldExtensions.Fp2_FElem_length _ _ _ _ prime_parameters beta F_representation fp2_prefix _ _ _ HD) as Hlen_D.
    pose proof (@CubicFieldExtensions.Fp2_FElem_length _ _ _ _ prime_parameters beta F_representation fp2_prefix _ _ _ HE) as Hlen_E.
    pose proof (@CubicFieldExtensions.Fp2_FElem_length _ _ _ _ prime_parameters beta F_representation fp2_prefix _ _ _ HF) as Hlen_F.
    (* === Stack deallocation: join tmp (D,E,F) back into Fp6 and deallocate === *)
    (* D = allocx/c0, E = allocx+c1/c1, F = allocx+c2/c2 *)
    assert (Hjoin_x : (FElem_Fp2 allocx (c0_felem x) ⋆
      (FElem_Fp2 (word.add allocx (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c1_felem x) ⋆
       FElem_Fp2 (word.add allocx (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c2_felem x)))
      (map.putmany m_D (map.putmany m_E m_F))).
    { exists m_D, (map.putmany m_E m_F).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HD |].
      exists m_E, m_F.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HE | exact HF]. }
    pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _ word_ok mem_ok
      prime_parameters beta xi_re xi_im F_representation fp6_prefix fp2_prefix
      allocx (c0_felem x) (c1_felem x) (c2_felem x)
      (map.putmany m_D (map.putmany m_E m_F))
      Hlen_D Hlen_E Hlen_F Hjoin_x) as Hfp6_x.
    rewrite CubicFieldExtensions.Fp6_list_decomp in Hfp6_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst allocx x
      (map.putmany m_D (map.putmany m_E m_F)) Hfp6_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C m_G))),
      (map.putmany m_D (map.putmany m_E m_F)).
    split. { exact Hanybytes_x. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    (* Output FElem: C = pout/out0', B = pout+c1/(c0_felem x), A = pout+c2/(c1_felem x) *)
    exists (out0' ++ c0_felem x ++ c1_felem x).
    (* Prove c0/c1/c2 decomposition of output *)
    assert (Hc0_app : c0_felem (out0' ++ c0_felem x ++ c1_felem x) = out0').
    { unfold c0_felem.
      set (n := (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc1_app : c1_felem (out0' ++ c0_felem x ++ c1_felem x) = c0_felem x).
    { unfold c1_felem.
      set (n := (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat).
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length (c0_felem x)) by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. apply ListUtil.firstn_app_sharp. reflexivity. }
    assert (Hc2_app : c2_felem (out0' ++ c0_felem x ++ c1_felem x) = c1_felem x).
    { unfold c2_felem.
      set (n := (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat).
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite <- ListUtil.skipn_skipn.
      assert (Hn : n = length out0') by (symmetry; exact Hlen_C).
      rewrite Hn. rewrite ListUtil.skipn_app_sharp by reflexivity.
      assert (Hn' : length out0' = length (c0_felem x)) by (rewrite Hlen_C, Hlen_B; reflexivity).
      rewrite Hn'. rewrite ListUtil.skipn_app_sharp by reflexivity.
      reflexivity. }
    (* feval *)
    split.
    { fp6_feval_eq. rewrite Hc0_app, Hc1_app, Hc2_app.
      rewrite Hfeval0.
      unfold fp6_mul_by_v_model, un_Fp6_mul_by_v; simpl.
      fp6_feval_eq. reflexivity. }
    (* bounded_by *)
    split.
    { fp6_bounded_by_eq. rewrite Hc0_app, Hc1_app, Hc2_app.
      split; [|split].
      - (* out0': mul_xi output has loose bounds *)
        change (@AbstractField.un_outbounds _ _ _ _ _ Fp2_fp_inst Fp2_repr_inst _ un_Fp2_mul_xi_local)
          with (@AbstractField.loose_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst) in Hbound0.
        exact Hbound0.
      - apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst Fp2_repr_ok_inst); exact Hbx0.
      - apply (@relax_bounds _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst Fp2_repr_ok_inst); exact Hbx1. }
    (* sep *)
    { assert (Hjoin_out : (FElem_Fp2 pout out0' ⋆
        (FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c1_offset beta fp2_prefix)) (c0_felem x) ⋆
         FElem_Fp2 (word.add pout (CubicFieldExtensions.fp6_c2_offset beta fp2_prefix)) (c1_felem x)))
        (map.putmany m_C (map.putmany m_B m_A))).
      { exists m_C, (map.putmany m_B m_A).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC |].
        exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _ word_ok mem_ok
        prime_parameters beta xi_re xi_im F_representation fp6_prefix fp2_prefix
        pout out0' (c0_felem x) (c1_felem x)
        (map.putmany m_C (map.putmany m_B m_A))
        Hlen_C Hlen_B Hlen_A Hjoin_out) as Hfp6_out.
      exists (map.putmany m_C (map.putmany m_B m_A)), m_G.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp6_out | exact HG]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp12_copy: copy 2 Fp6 elements                                   *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_felem_copy : function_t :=
    (AbstractField.felem_copy (F:=Fp12), (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "x")]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "x")])
    ))).

  Instance spec_of_Fp12_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
    AbstractField.spec_of_felem_copy (F:=Fp12).

  Lemma Fp12_felem_copy_ok : program_logic_goal_for_function! Fp12_felem_copy.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2.
    unfold spec_of_Fp12_copy, AbstractField.spec_of_felem_copy.
    intros pout px out x R Rout tr mem0 [Hmem0_1 Hmem0_2].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_felem_copy].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for first call *)
    exists [pout; px]. split.
    { unfold dexprs, expr_fp12_c0. repeat straightline.
      eexists. split. { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      cbv [list_map]. eexists. split.
      { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body]. apply map.get_put_same. }
      exact eq_refl. }
    (* === Decompose preconditions === *)
    destruct Hmem0_1 as [m_x [m_or [Hsep1 [Hx Hor]]]].
    destruct Hor as [m_o [m_r [Hsep_or [Ho Hr]]]].
    pose proof (Fp12_raw_FElem_split _ _ _ Hx) as [m_x0 [m_x1 [Hsep_x [Hx0 Hx1]]]].
    pose proof (Fp12_raw_FElem_split _ _ _ Ho) as [m_o0 [m_o1 [Hsep_o [Ho0 Ho1]]]].
    destruct Hmem0_2 as [m_o' [m_rout [Hsep2 [Ho' Hrout]]]].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp12_fp_inst Fp12_repr_inst pout out m_o Ho) as Hph_o.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp12_fp_inst Fp12_repr_inst pout out m_o' Ho') as Hph_o'.
    unfold AbstractField.Placeholder in Hph_o, Hph_o'.
    pose proof (Memory.anybytes_unique_domain _ _ _ _ Hph_o Hph_o') as Hsd.
    destruct Hsep1 as [Heq1 Hd1]. destruct Hsep_or as [Heq_or Hd_or]. subst m_or mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_x_o Hd_x_r].
    assert (Hsplit_mem : map.split (map.putmany m_x (map.putmany m_o m_r)) m_o (map.putmany m_x m_r)).
    { split.
      { rewrite map.putmany_assoc.
        rewrite (map.putmany_comm m_x m_o Hd_x_o).
        symmetry. apply map.putmany_assoc. }
      { apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x_o k v2 v1 Hg2 Hg1). }
        { exact Hd_or. } } }
    pose proof (proj1 (map.split_comm _ _ _) Hsplit_mem) as Hsplit_mem'.
    pose proof (proj1 (map.split_comm _ _ _) Hsep2) as Hsep2'.
    pose proof (map.split_diff Hsd Hsplit_mem' Hsep2') as [Heq_rout Heq_o'].
    subst m_o'. rewrite <- Heq_rout in Hrout.
    clear Heq_rout Hsd Hsep2 Hsep2' Hsplit_mem Hsplit_mem' Hph_o Hph_o' Ho'.
    destruct Hsep_x as [Heq_x Hd_x01]. destruct Hsep_o as [Heq_o Hd_o01].
    subst m_x m_o.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_o) as [Hd_x0_o Hd_x1_o].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x0_o) as [Hd_x0_o0 Hd_x0_o1].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x1_o) as [Hd_x1_o0 Hd_x1_o1].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_r) as [Hd_x0_r Hd_x1_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_or) as [Hd_o0_r Hd_o1_r].
    clear Hd_x_o Hd_x_r Hd_or Hd1 Hd_x0_o Hd_x1_o.
    (* === First Fp6 copy call (c0) === *)
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 pout px (d0_felem out) (d0_felem x)
        (fun m => (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
                   (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem out) ⋆ R)) m)
        (fun m => m = map.putmany m_x0 (map.putmany m_x1 (map.putmany m_o1 m_r)))
        tr).
      split.
      { exists (map.putmany m_x0 m_o0),
               (map.putmany m_x1 (map.putmany m_o1 m_r)).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split.
        { exists m_x0, m_o0.
          split; [split; [reflexivity | assumption] |].
          split; [exact Hx0 | exact Ho0]. }
        { exists m_x1, (map.putmany m_o1 m_r).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hx1 |].
          exists m_o1, m_r.
          split; [split; [reflexivity | exact Hd_o1_r] |].
          split; [exact Ho1 | exact Hr]. } }
      { exists m_o0, (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_o1 m_r))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split; [exact Ho0 | exact eq_refl]. } }
    (* === Post first call === *)
    intros t' m' rets [Hrets [Htr1 Hsep_post1]].
    subst rets. symmetry in Htr1. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    repeat straightline.
    eexists. split.
    { unfold dexprs. repeat straightline.
      exists pout. split.
      { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body expr_fp12_c1].
      repeat straightline.
      unfold list_map. repeat straightline.
      exists px. split. { apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat straightline. exact eq_refl. }
    destruct Hsep_post1 as [m_new0 [m_frame1 [Hsp_post1 [Hnew0 Hframe1]]]].
    subst m_frame1.
    destruct Hsp_post1 as [Heq_p1 Hd_p1].
    split_all_disjointness.
    (* === Second Fp6 copy call (c1) === *)
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 (word.add pout (word.of_Z fp6_felem_offset))
                       (word.add px (word.of_Z fp6_felem_offset))
        (d1_felem out) (d1_felem x)
        (fun m => (FElem_Fp6 pout (d0_felem x) ⋆
                   (FElem_Fp6 px (d0_felem x) ⋆ R)) m)
        (fun m => m = map.putmany m_new0 (map.putmany m_x0 (map.putmany m_x1 m_r)))
        tr).
      split.
      { subst m'.
        exists (map.putmany m_x1 m_o1),
               (map.putmany m_new0 (map.putmany m_x0 m_r)).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split.
        { exists m_x1, m_o1.
          split; [split; [reflexivity | assumption] |].
          split; [exact Hx1 | exact Ho1]. }
        { exists m_new0, (map.putmany m_x0 m_r).
          split; [split; [reflexivity |] |].
          { map_disjoint_auto. }
          split; [exact Hnew0 |].
          exists m_x0, m_r.
          split; [split; [reflexivity | exact Hd_x0_r] |].
          split; [exact Hx0 | exact Hr]. } }
      { subst m'.
        exists m_o1, (map.putmany m_new0 (map.putmany m_x0 (map.putmany m_x1 m_r))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split; [exact Ho1 | exact eq_refl]. } }
    (* === Close proof === *)
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_post2]].
    subst rets2.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact Htr2. }
    destruct Hsep_post2 as [m_new1 [m_frame2 [Hsp_post2 [Hnew1 Hframe2]]]].
    subst m_frame2.
    destruct Hsp_post2 as [Heq_p2 Hd_p2].
    split_all_disjointness.
    assert (Hdecomp : x = d0_felem x ++ d1_felem x) by (symmetry; apply Fp12_list_decomp).
    rewrite Hdecomp.
    exists (map.putmany m_new0 m_new1), (map.putmany (map.putmany m_x0 m_x1) m_r).
    split; [split |].
    { subst m''. solve_putmany_eq. }
    { map_disjoint_auto. }
    split.
    { apply Fp12_raw_FElem_join.
      { exact (Fp6_FElem_length _ _ _ Hnew0). }
      { exact (Fp6_FElem_length _ _ _ Hnew1). }
      exists m_new0, m_new1.
      split; [split; [reflexivity |] |].
      { map_disjoint_auto. }
      split; [exact Hnew0 | exact Hnew1]. }
    { exact Hrout. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp12_add: componentwise addition of 2 Fp6 elements               *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_add : function_t :=
    (AbstractField.add (F:=Fp12), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as ax;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as ay;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "ax"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "ay"; expr.var "iny"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "ax"); expr_fp12_c0 (expr.var "ay")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "ax"); expr_fp12_c1 (expr.var "ay")])
    ))).

  Instance spec_of_Fp12_add : spec_of (AbstractField.add (F:=Fp12)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp12).

  Lemma Fp12_add_ok : program_logic_goal_for_function! Fp12_add.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2 HFadd1 HFadd2.
    unfold spec_of_Fp12_add, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_add].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc ax === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Stackalloc ay === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    (* FElem_from_bytes *)
    pose proof (@AbstractField.FElem_from_bytes _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    (* Decompose memory *)
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
    (* === First Fp12 copy: x → allocx === *)
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
    (* Post first copy *)
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp12 copy: y → allocy === *)
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
    (* Post second copy *)
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Decompose for Fp6 add calls === *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    (* Split Fp12 FElems into 2 Fp6 components *)
    pose proof (Fp12_raw_FElem_split allocx x m_new1 Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax0 [m_ax1 [Hsp_ax [Hfe_ax0 Hfe_ax1]]]].
    destruct Hsp_ax as [Heq_new1_ax Hd_ax01].
    pose proof (Fp12_raw_FElem_split allocy y m_new2 Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay0 [m_ay1 [Hsp_ay [Hfe_ay0 Hfe_ay1]]]].
    destruct Hsp_ay as [Heq_new2_ay Hd_ay01].
    pose proof (Fp12_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o1 [Hsp_out [Hfe_o0 Hfe_o1]]]].
    destruct Hsp_out as [Heq_out_o Hd_o01].
    (* Decompose Fp12-level bounded_by into Fp6-level *)
    fp12_bounded_by_eq. destruct Hbx as [Hbx0 Hbx1]. destruct Hby as [Hby0 Hby1].
    (* Relate mem0 decompositions *)
    assert (Heq_yr : map.putmany m_y m_ry = map.putmany m_out m_rr)
      by (rewrite <- Heq_mem0_y; exact Heq_m0_out).
    subst m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* Build master 6-way sep fact *)
    assert (Hsep6 :
      ((FElem_Fp6 allocy (d0_felem y) ⋆
        FElem_Fp6 (word.add allocy (word.of_Z fp6_felem_offset)) (d1_felem y)) ⋆
       ((FElem_Fp6 allocx (d0_felem x) ⋆
         FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x)) ⋆
        ((FElem_Fp6 pout (d0_felem old_out) ⋆
          FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out)) ⋆ Rr)))
      (map.putmany (map.putmany m_ay0 m_ay1)
        (map.putmany (map.putmany m_ax0 m_ax1)
          (map.putmany (map.putmany m_o0 m_o1) m_rr)))).
    { exists (map.putmany m_ay0 m_ay1),
        (map.putmany (map.putmany m_ax0 m_ax1)
          (map.putmany (map.putmany m_o0 m_o1) m_rr)).
      split; [split; [reflexivity | exact Hd_n2_f2] |].
      split.
      { exists m_ay0, m_ay1.
        split; [split; [reflexivity | exact Hd_ay01] |].
        split; [exact Hfe_ay0 | exact Hfe_ay1]. }
      exists (map.putmany m_ax0 m_ax1),
        (map.putmany (map.putmany m_o0 m_o1) m_rr).
      split; [split; [reflexivity | exact Hd_n1_mem0] |].
      split.
      { exists m_ax0, m_ax1.
        split; [split; [reflexivity | exact Hd_ax01] |].
        split; [exact Hfe_ax0 | exact Hfe_ax1]. }
      exists (map.putmany m_o0 m_o1), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, m_o1.
        split; [split; [reflexivity | exact Hd_o01] |].
        split; [exact Hfe_o0 | exact Hfe_o1]. }
      exact Hrr_out. }
    (* === First Fp6 add: c0 === *)
    exists [pout; allocx; allocy]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 pout allocx allocy
           (d0_felem old_out) (d0_felem x) (d0_felem y) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_add1 m_add1 rets_add1 [Hrets_add1 [Htr_add1 [out0' [Hfeval0 [Hbound0 Hsep_add1]]]]].
    subst rets_add1 t_add1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp6 add: c1 === *)
    exists [word.add pout (word.of_Z fp6_felem_offset);
            word.add allocx (word.of_Z fp6_felem_offset);
            word.add allocy (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 (word.add pout (word.of_Z fp6_felem_offset))
           (word.add allocx (word.of_Z fp6_felem_offset))
           (word.add allocy (word.of_Z fp6_felem_offset))
           (d1_felem old_out) (d1_felem x) (d1_felem y) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_add2 m_add2 rets_add2 [Hrets_add2 [Htr_add2 [out1' [Hfeval1 [Hbound1 Hsep_add2]]]]].
    subst rets_add2 t_add2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure Hsep_add2 into map components === *)
    (* After two adds, the sep has 7 components:
       m_A: out1' at pout+offset,  m_B: out0' at pout,
       m_C: d0 y at allocy,  m_D: d1 y at allocy+offset,
       m_E: d0 x at allocx,  m_F: d1 x at allocx+offset,  m_G: Rr *)
    destruct Hsep_add2 as [m_A [m_rest1 [[Heq_add2 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_F [m_G [[Heq_r5 Hd_FG] [HF HG]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_add2.
    split_all_disjointness.
    pose proof (Fp6_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp6_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp6_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp6_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp6_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp6_FElem_length _ _ _ HF) as Hlen_F.
    (* === Allocy stack deallocation === *)
    assert (Hjoin_y : (FElem_Fp6 allocy (d0_felem y) ⋆
      FElem_Fp6 (word.add allocy (word.of_Z fp6_felem_offset)) (d1_felem y))
      (map.putmany m_C m_D)).
    { exists m_C, m_D.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HC | exact HD]. }
    pose proof (Fp12_raw_FElem_join allocy (d0_felem y) (d1_felem y)
      (map.putmany m_C m_D) Hlen_C Hlen_D Hjoin_y) as Hfp12_y.
    rewrite Fp12_list_decomp in Hfp12_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocy y
      (map.putmany m_C m_D) Hfp12_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_E (map.putmany m_F m_G)))),
      (map.putmany m_C m_D).
    split. { exact Hanybytes_y. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
    (* === Allocx stack deallocation === *)
    assert (Hjoin_x : (FElem_Fp6 allocx (d0_felem x) ⋆
      FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x))
      (map.putmany m_E m_F)).
    { exists m_E, m_F.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HE | exact HF]. }
    pose proof (Fp12_raw_FElem_join allocx (d0_felem x) (d1_felem x)
      (map.putmany m_E m_F) Hlen_E Hlen_F Hjoin_x) as Hfp12_x.
    rewrite Fp12_list_decomp in Hfp12_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocx x
      (map.putmany m_E m_F) Hfp12_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_B m_G)), (map.putmany m_E m_F).
    split. { exact Hanybytes_x. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
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
    { fp12_feval_eq. rewrite Hd0_app, Hd1_app. rewrite Hfeval0, Hfeval1.
      reflexivity. }
    split.
    { fp12_bounded_by_eq. rewrite Hd0_app, Hd1_app. split; assumption. }
    { assert (Hjoin_out : (FElem_Fp6 pout out0' ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1')
        (map.putmany m_B m_A)).
      { exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp12_raw_FElem_join pout out0' out1'
        (map.putmany m_B m_A) Hlen_B Hlen_A Hjoin_out) as Hfp12_out.
      exists (map.putmany m_B m_A), m_G.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out | exact HG]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp12_sub: componentwise subtraction of 2 Fp6 elements            *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_sub : function_t :=
    (AbstractField.sub (F:=Fp12), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as ax;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as ay;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "ax"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "ay"; expr.var "iny"]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "ax"); expr_fp12_c0 (expr.var "ay")]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "ax"); expr_fp12_c1 (expr.var "ay")])
    ))).

  Instance spec_of_Fp12_sub : spec_of (AbstractField.sub (F:=Fp12)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp12).

  Lemma Fp12_sub_ok : program_logic_goal_for_function! Fp12_sub.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2 HFsub1 HFsub2.
    unfold spec_of_Fp12_sub, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_sub].
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
    (* === First Fp12 copy: x → allocx === *)
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
    (* === Second Fp12 copy: y → allocy === *)
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
    (* === Decompose for Fp6 sub calls === *)
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
    (* Build master 6-way sep fact *)
    assert (Hsep6 :
      ((FElem_Fp6 allocy (d0_felem y) ⋆
        FElem_Fp6 (word.add allocy (word.of_Z fp6_felem_offset)) (d1_felem y)) ⋆
       ((FElem_Fp6 allocx (d0_felem x) ⋆
         FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x)) ⋆
        ((FElem_Fp6 pout (d0_felem old_out) ⋆
          FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out)) ⋆ Rr)))
      (map.putmany (map.putmany m_ay0 m_ay1)
        (map.putmany (map.putmany m_ax0 m_ax1)
          (map.putmany (map.putmany m_o0 m_o1) m_rr)))).
    { exists (map.putmany m_ay0 m_ay1),
        (map.putmany (map.putmany m_ax0 m_ax1)
          (map.putmany (map.putmany m_o0 m_o1) m_rr)).
      split; [split; [reflexivity | exact Hd_n2_f2] |].
      split.
      { exists m_ay0, m_ay1.
        split; [split; [reflexivity | exact Hd_ay01] |].
        split; [exact Hfe_ay0 | exact Hfe_ay1]. }
      exists (map.putmany m_ax0 m_ax1),
        (map.putmany (map.putmany m_o0 m_o1) m_rr).
      split; [split; [reflexivity | exact Hd_n1_mem0] |].
      split.
      { exists m_ax0, m_ax1.
        split; [split; [reflexivity | exact Hd_ax01] |].
        split; [exact Hfe_ax0 | exact Hfe_ax1]. }
      exists (map.putmany m_o0 m_o1), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, m_o1.
        split; [split; [reflexivity | exact Hd_o01] |].
        split; [exact Hfe_o0 | exact Hfe_o1]. }
      exact Hrr_out. }
    (* === First Fp6 sub: c0 === *)
    exists [pout; allocx; allocy]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 pout allocx allocy
           (d0_felem old_out) (d0_felem x) (d0_felem y) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_sub1 m_sub1 rets_sub1 [Hrets_sub1 [Htr_sub1 [out0' [Hfeval0 [Hbound0 Hsep_sub1]]]]].
    subst rets_sub1 t_sub1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp6 sub: c1 === *)
    exists [word.add pout (word.of_Z fp6_felem_offset);
            word.add allocx (word.of_Z fp6_felem_offset);
            word.add allocy (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 (word.add pout (word.of_Z fp6_felem_offset))
           (word.add allocx (word.of_Z fp6_felem_offset))
           (word.add allocy (word.of_Z fp6_felem_offset))
           (d1_felem old_out) (d1_felem x) (d1_felem y) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_sub2 m_sub2 rets_sub2 [Hrets_sub2 [Htr_sub2 [out1' [Hfeval1 [Hbound1 Hsep_sub2]]]]].
    subst rets_sub2 t_sub2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure sep into 7 atomic maps === *)
    destruct Hsep_sub2 as [m_A [m_rest1 [[Heq_sub2 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_F [m_G [[Heq_r5 Hd_FG] [HF HG]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_sub2.
    split_all_disjointness.
    pose proof (Fp6_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp6_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp6_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp6_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp6_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp6_FElem_length _ _ _ HF) as Hlen_F.
    (* === Allocy stack deallocation === *)
    assert (Hjoin_y : (FElem_Fp6 allocy (d0_felem y) ⋆
      FElem_Fp6 (word.add allocy (word.of_Z fp6_felem_offset)) (d1_felem y))
      (map.putmany m_C m_D)).
    { exists m_C, m_D.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HC | exact HD]. }
    pose proof (Fp12_raw_FElem_join allocy (d0_felem y) (d1_felem y)
      (map.putmany m_C m_D) Hlen_C Hlen_D Hjoin_y) as Hfp12_y.
    rewrite Fp12_list_decomp in Hfp12_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocy y
      (map.putmany m_C m_D) Hfp12_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_E (map.putmany m_F m_G)))),
      (map.putmany m_C m_D).
    split. { exact Hanybytes_y. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
    (* === Allocx stack deallocation === *)
    assert (Hjoin_x : (FElem_Fp6 allocx (d0_felem x) ⋆
      FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x))
      (map.putmany m_E m_F)).
    { exists m_E, m_F.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HE | exact HF]. }
    pose proof (Fp12_raw_FElem_join allocx (d0_felem x) (d1_felem x)
      (map.putmany m_E m_F) Hlen_E Hlen_F Hjoin_x) as Hfp12_x.
    rewrite Fp12_list_decomp in Hfp12_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocx x
      (map.putmany m_E m_F) Hfp12_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_B m_G)), (map.putmany m_E m_F).
    split. { exact Hanybytes_x. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
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
    { fp12_feval_eq. rewrite Hd0_app, Hd1_app. rewrite Hfeval0, Hfeval1.
      reflexivity. }
    split.
    { fp12_bounded_by_eq. rewrite Hd0_app, Hd1_app. split; assumption. }
    { assert (Hjoin_out : (FElem_Fp6 pout out0' ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1')
        (map.putmany m_B m_A)).
      { exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp12_raw_FElem_join pout out0' out1'
        (map.putmany m_B m_A) Hlen_B Hlen_A Hjoin_out) as Hfp12_out.
      exists (map.putmany m_B m_A), m_G.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out | exact HG]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* Nocopy Fp12 add/sub: operate directly on inputs, no copies.    *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_add_nocopy : function_t :=
    ((AbstractField.add (F:=Fp12) ++ "_nocopy")%string,
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "inx"); expr_fp12_c0 (expr.var "iny")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "inx"); expr_fp12_c1 (expr.var "iny")])
    ))).

  Lemma Fp12_add_nocopy_ok :
    forall functions
      (EnvContains : map.get functions (fst Fp12_add_nocopy) = Some (snd Fp12_add_nocopy))
      (HFadd1 : spec_of_Fp6_add functions)
      (HFadd2 : spec_of_Fp6_add functions),
    forall pout px py old_out x y Rr tr mem0,
      @AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst
        (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) x ->
      @AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst
        (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) y ->
      (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst px x ⋆
       (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst py y ⋆
        (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst pout old_out ⋆ Rr))) mem0 ->
      WeakestPrecondition.call functions (fst Fp12_add_nocopy) tr mem0 [pout; px; py]
        (fun tr' mem' rets =>
           rets = [] /\ tr = tr' /\
           exists result,
             @AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst result =
             @AbstractField.Fadd _ Fp12_fp_inst
               (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst x)
               (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst y) /\
             @AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst
               (@AbstractField.loose_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) result /\
             (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst pout result ⋆
              (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst px x ⋆
               (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst py y ⋆ Rr))) mem').
  Proof.
    intros functions EnvContains HFadd1 HFadd2.
    intros pout px py old_out x y Rr tr mem0 Hbx Hby Hsep.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_add_nocopy].
    eexists. split. { exact eq_refl. }
    (* Decompose Fp12 FElems into Fp6 halves *)
    destruct Hsep as [m_x [m_yr [[Heq_m0 Hd_x_yr] [Hfx Hyr]]]].
    destruct Hyr as [m_y [m_or [[Heq_yr Hd_y_or] [Hfy Hor]]]].
    destruct Hor as [m_o [m_rr [[Heq_or Hd_o_rr] [Hfo Hrr]]]].
    subst m_yr m_or mem0.
    pose proof (Fp12_raw_FElem_split px x m_x Hfx) as Hx_sep.
    pose proof (Fp12_raw_FElem_split py y m_y Hfy) as Hy_sep.
    pose proof (Fp12_raw_FElem_split pout old_out m_o Hfo) as Ho_sep.
    destruct Hx_sep as [m_x0 [m_x1 [[Heq_x Hd_x01] [Hx0 Hx1]]]].
    destruct Hy_sep as [m_y0 [m_y1 [[Heq_y Hd_y01] [Hy0 Hy1]]]].
    destruct Ho_sep as [m_o0 [m_o1 [[Heq_o Hd_o01] [Ho0 Ho1]]]].
    subst m_x m_y m_o.
    (* Decompose bounds *)
    change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst
      (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst)) with
      (fun ws => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
                   (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) (d0_felem ws)
              /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
                   (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) (d1_felem ws)) in Hbx, Hby.
    cbv beta in Hbx, Hby.
    destruct Hbx as [Hbx0 Hbx1]. destruct Hby as [Hby0 Hby1].
    split_all_disjointness. rewrite <- !map.putmany_assoc.
    assert (Hsep_fp6 : (FElem_Fp6 px (d0_felem x) ⋆
      (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
        (FElem_Fp6 py (d0_felem y) ⋆
          (FElem_Fp6 (word.add py (word.of_Z fp6_felem_offset)) (d1_felem y) ⋆
            (FElem_Fp6 pout (d0_felem old_out) ⋆
              (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆ Rr))))))
      (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_y0 (map.putmany m_y1 (map.putmany m_o0 (map.putmany m_o1 m_rr))))))).
    { build_sep. }
    (* === Call 1: Fp6_add(out.c0, inx.c0, iny.c0) === *)
    exists [pout; px; py]. split.
    { cbv [dexprs list_map expr_fp12_c0 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 pout px py (d0_felem old_out) (d0_felem x) (d0_felem y) _ tr).
         split; [exact Hbx0 |]. split; [exact Hby0 |].
         split.
         { eexists. exact Hsep_fp6. }
         split.
         { eexists. pose proof Hsep_fp6 as H'. ecancel_assumption. }
         pose proof Hsep_fp6 as H'. ecancel_assumption. }
    intros t1 m1 rets1 [Hrets1 [Htr1 [out0 [Hfeval0 [Hbound0 Hsep1]]]]].
    subst rets1 t1. cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    (* === Call 2: Fp6_add(out.c1, inx.c1, iny.c1) === *)
    exists [word.add pout (word.of_Z fp6_felem_offset);
            word.add px (word.of_Z fp6_felem_offset);
            word.add py (word.of_Z fp6_felem_offset)]. split.
    { cbv [dexprs list_map expr_fp12_c1 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 (word.add pout (word.of_Z fp6_felem_offset))
                        (word.add px (word.of_Z fp6_felem_offset))
                        (word.add py (word.of_Z fp6_felem_offset))
                        (d1_felem old_out) (d1_felem x) (d1_felem y) _ tr).
         split; [exact Hbx1 |]. split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [out1 [Hfeval1 [Hbound1 Hsep2]]]]].
    subst rets2 t2.
    eexists. split. { exact eq_refl. }
    cbv beta.
    split. { exact eq_refl. } split. { exact eq_refl. }
    (* === Final postcondition === *)
    destruct Hsep2 as [m_R0 [m_S0 [[Heq_S0 Hd_S0] [HR0 HS0]]]].
    destruct HS0 as [m_R1 [m_S1 [[Heq_S1 Hd_S1] [HR1 HS1]]]].
    destruct HS1 as [m_px0 [m_T0 [[Heq_T0 Hd_T0] [Hpx0 HT0]]]].
    destruct HT0 as [m_px1 [m_T1 [[Heq_T1 Hd_T1] [Hpx1 HT1]]]].
    destruct HT1 as [m_py0 [m_T2 [[Heq_T2 Hd_T2] [Hpy0 HT2]]]].
    destruct HT2 as [m_py1 [m_rr' [[Heq_T3 Hd_T3] [Hpy1 Hrr']]]].
    subst m_S0 m_S1 m_T0 m_T1 m_T2.
    pose proof (Fp6_FElem_length _ _ _ HR0) as Hlen_out1.
    pose proof (Fp6_FElem_length _ _ _ HR1) as Hlen_out0.
    pose proof (Fp6_FElem_length _ _ _ Hpx0) as Hlen_px0.
    pose proof (Fp6_FElem_length _ _ _ Hpx1) as Hlen_px1.
    pose proof (Fp6_FElem_length _ _ _ Hpy0) as Hlen_py0.
    pose proof (Fp6_FElem_length _ _ _ Hpy1) as Hlen_py1.
    exists (out0 ++ out1).
    split.
    { change (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun ws => (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem ws),
                    @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem ws))).
      cbv beta. rewrite d0_felem_app, d1_felem_app by assumption.
      rewrite Hfeval0, Hfeval1. reflexivity. }
    split.
    { change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d1_felem felem)).
      cbv beta. rewrite d0_felem_app, d1_felem_app by assumption.
      split; [exact Hbound0 | exact Hbound1]. }
    { split_all_disjointness.
      assert (Hjoin_out : (FElem_Fp6 pout out0 ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1)
        (map.putmany m_R1 m_R0)).
      { exists m_R1, m_R0.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HR1 | exact HR0]. }
      pose proof (Fp12_raw_FElem_join pout out0 out1
        (map.putmany m_R1 m_R0) Hlen_out0 Hlen_out1 Hjoin_out) as Hfp12_out.
      assert (Hjoin_px : (FElem_Fp6 px (d0_felem x) ⋆
        FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x))
        (map.putmany m_px0 m_px1)).
      { exists m_px0, m_px1.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpx0 | exact Hpx1]. }
      pose proof (Fp12_raw_FElem_join px (d0_felem x) (d1_felem x)
        (map.putmany m_px0 m_px1) Hlen_px0 Hlen_px1 Hjoin_px) as Hfp12_x.
      rewrite Fp12_list_decomp in Hfp12_x.
      assert (Hjoin_py : (FElem_Fp6 py (d0_felem y) ⋆
        FElem_Fp6 (word.add py (word.of_Z fp6_felem_offset)) (d1_felem y))
        (map.putmany m_py0 m_py1)).
      { exists m_py0, m_py1.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpy0 | exact Hpy1]. }
      pose proof (Fp12_raw_FElem_join py (d0_felem y) (d1_felem y)
        (map.putmany m_py0 m_py1) Hlen_py0 Hlen_py1 Hjoin_py) as Hfp12_y.
      rewrite Fp12_list_decomp in Hfp12_y.
      exists (map.putmany m_R1 m_R0),
             (map.putmany (map.putmany m_px0 m_px1)
               (map.putmany (map.putmany m_py0 m_py1) m_rr')).
      split; [split |].
      { rewrite Heq_S0. rewrite <- !map.putmany_assoc.
        map_swap m_R0 m_R1. reflexivity. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out |].
      exists (map.putmany m_px0 m_px1),
             (map.putmany (map.putmany m_py0 m_py1) m_rr').
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp12_x |].
      exists (map.putmany m_py0 m_py1), m_rr'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp12_y | exact Hrr']. }
  Qed.

  Definition Fp12_sub_nocopy : function_t :=
    ((AbstractField.sub (F:=Fp12) ++ "_nocopy")%string,
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.sub (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "inx"); expr_fp12_c0 (expr.var "iny")]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "inx"); expr_fp12_c1 (expr.var "iny")])
    ))).

  Lemma Fp12_sub_nocopy_ok :
    forall functions
      (EnvContains : map.get functions (fst Fp12_sub_nocopy) = Some (snd Fp12_sub_nocopy))
      (HFsub1 : spec_of_Fp6_sub functions)
      (HFsub2 : spec_of_Fp6_sub functions),
    forall pout px py old_out x y Rr tr mem0,
      @AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst
        (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) x ->
      @AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst
        (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) y ->
      (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst px x ⋆
       (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst py y ⋆
        (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst pout old_out ⋆ Rr))) mem0 ->
      WeakestPrecondition.call functions (fst Fp12_sub_nocopy) tr mem0 [pout; px; py]
        (fun tr' mem' rets =>
           rets = [] /\ tr = tr' /\
           exists result,
             @AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst result =
             @AbstractField.Fsub _ Fp12_fp_inst
               (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst x)
               (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst y) /\
             @AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst
               (@AbstractField.loose_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) result /\
             (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst pout result ⋆
              (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst px x ⋆
               (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst py y ⋆ Rr))) mem').
  Proof.
    intros functions EnvContains HFsub1 HFsub2.
    intros pout px py old_out x y Rr tr mem0 Hbx Hby Hsep.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_sub_nocopy].
    eexists. split. { exact eq_refl. }
    destruct Hsep as [m_x [m_yr [[Heq_m0 Hd_x_yr] [Hfx Hyr]]]].
    destruct Hyr as [m_y [m_or [[Heq_yr Hd_y_or] [Hfy Hor]]]].
    destruct Hor as [m_o [m_rr [[Heq_or Hd_o_rr] [Hfo Hrr]]]].
    subst m_yr m_or mem0.
    pose proof (Fp12_raw_FElem_split px x m_x Hfx) as Hx_sep.
    pose proof (Fp12_raw_FElem_split py y m_y Hfy) as Hy_sep.
    pose proof (Fp12_raw_FElem_split pout old_out m_o Hfo) as Ho_sep.
    destruct Hx_sep as [m_x0 [m_x1 [[Heq_x Hd_x01] [Hx0 Hx1]]]].
    destruct Hy_sep as [m_y0 [m_y1 [[Heq_y Hd_y01] [Hy0 Hy1]]]].
    destruct Ho_sep as [m_o0 [m_o1 [[Heq_o Hd_o01] [Ho0 Ho1]]]].
    subst m_x m_y m_o.
    change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst
      (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst)) with
      (fun ws => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
                   (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) (d0_felem ws)
              /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst
                   (@AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst) (d1_felem ws)) in Hbx, Hby.
    cbv beta in Hbx, Hby.
    destruct Hbx as [Hbx0 Hbx1]. destruct Hby as [Hby0 Hby1].
    split_all_disjointness. rewrite <- !map.putmany_assoc.
    assert (Hsep_fp6 : (FElem_Fp6 px (d0_felem x) ⋆
      (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
        (FElem_Fp6 py (d0_felem y) ⋆
          (FElem_Fp6 (word.add py (word.of_Z fp6_felem_offset)) (d1_felem y) ⋆
            (FElem_Fp6 pout (d0_felem old_out) ⋆
              (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆ Rr))))))
      (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_y0 (map.putmany m_y1 (map.putmany m_o0 (map.putmany m_o1 m_rr))))))).
    { build_sep. }
    (* === Call 1: Fp6_sub(out.c0, inx.c0, iny.c0) === *)
    exists [pout; px; py]. split.
    { cbv [dexprs list_map expr_fp12_c0 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 pout px py (d0_felem old_out) (d0_felem x) (d0_felem y) _ tr).
         split; [exact Hbx0 |]. split; [exact Hby0 |].
         split.
         { eexists. exact Hsep_fp6. }
         split.
         { eexists. pose proof Hsep_fp6 as H'. ecancel_assumption. }
         pose proof Hsep_fp6 as H'. ecancel_assumption. }
    intros t1 m1 rets1 [Hrets1 [Htr1 [out0 [Hfeval0 [Hbound0 Hsep1]]]]].
    subst rets1 t1. cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }
    (* === Call 2: Fp6_sub(out.c1, inx.c1, iny.c1) === *)
    exists [word.add pout (word.of_Z fp6_felem_offset);
            word.add px (word.of_Z fp6_felem_offset);
            word.add py (word.of_Z fp6_felem_offset)]. split.
    { cbv [dexprs list_map expr_fp12_c1 WeakestPrecondition.expr WeakestPrecondition.expr_body].
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { rewrite map.get_put_diff by (cbv; congruence).
        apply map.get_put_same. }
      eexists. split.
      { apply map.get_put_same. }
      exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 (word.add pout (word.of_Z fp6_felem_offset))
                        (word.add px (word.of_Z fp6_felem_offset))
                        (word.add py (word.of_Z fp6_felem_offset))
                        (d1_felem old_out) (d1_felem x) (d1_felem y) _ tr).
         split; [exact Hbx1 |]. split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep1 as H'. ecancel_assumption. }
         pose proof Hsep1 as H'. ecancel_assumption. }
    intros t2 m2 rets2 [Hrets2 [Htr2 [out1 [Hfeval1 [Hbound1 Hsep2]]]]].
    subst rets2 t2.
    eexists. split. { exact eq_refl. }
    cbv beta.
    split. { exact eq_refl. } split. { exact eq_refl. }
    destruct Hsep2 as [m_R0 [m_S0 [[Heq_S0 Hd_S0] [HR0 HS0]]]].
    destruct HS0 as [m_R1 [m_S1 [[Heq_S1 Hd_S1] [HR1 HS1]]]].
    destruct HS1 as [m_px0 [m_T0 [[Heq_T0 Hd_T0] [Hpx0 HT0]]]].
    destruct HT0 as [m_px1 [m_T1 [[Heq_T1 Hd_T1] [Hpx1 HT1]]]].
    destruct HT1 as [m_py0 [m_T2 [[Heq_T2 Hd_T2] [Hpy0 HT2]]]].
    destruct HT2 as [m_py1 [m_rr' [[Heq_T3 Hd_T3] [Hpy1 Hrr']]]].
    subst m_S0 m_S1 m_T0 m_T1 m_T2.
    pose proof (Fp6_FElem_length _ _ _ HR0) as Hlen_out1.
    pose proof (Fp6_FElem_length _ _ _ HR1) as Hlen_out0.
    pose proof (Fp6_FElem_length _ _ _ Hpx0) as Hlen_px0.
    pose proof (Fp6_FElem_length _ _ _ Hpx1) as Hlen_px1.
    pose proof (Fp6_FElem_length _ _ _ Hpy0) as Hlen_py0.
    pose proof (Fp6_FElem_length _ _ _ Hpy1) as Hlen_py1.
    exists (out0 ++ out1).
    split.
    { change (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun ws => (@AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d0_felem ws),
                    @AbstractField.feval _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst (d1_felem ws))).
      cbv beta. rewrite d0_felem_app, d1_felem_app by assumption.
      rewrite Hfeval0, Hfeval1. reflexivity. }
    split.
    { change (@AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) with
        (fun b felem => @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d0_felem felem)
                     /\ @AbstractField.bounded_by _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst b (d1_felem felem)).
      cbv beta. rewrite d0_felem_app, d1_felem_app by assumption.
      split; [exact Hbound0 | exact Hbound1]. }
    { split_all_disjointness.
      assert (Hjoin_out : (FElem_Fp6 pout out0 ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1)
        (map.putmany m_R1 m_R0)).
      { exists m_R1, m_R0.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HR1 | exact HR0]. }
      pose proof (Fp12_raw_FElem_join pout out0 out1
        (map.putmany m_R1 m_R0) Hlen_out0 Hlen_out1 Hjoin_out) as Hfp12_out.
      assert (Hjoin_px : (FElem_Fp6 px (d0_felem x) ⋆
        FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x))
        (map.putmany m_px0 m_px1)).
      { exists m_px0, m_px1.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpx0 | exact Hpx1]. }
      pose proof (Fp12_raw_FElem_join px (d0_felem x) (d1_felem x)
        (map.putmany m_px0 m_px1) Hlen_px0 Hlen_px1 Hjoin_px) as Hfp12_x.
      rewrite Fp12_list_decomp in Hfp12_x.
      assert (Hjoin_py : (FElem_Fp6 py (d0_felem y) ⋆
        FElem_Fp6 (word.add py (word.of_Z fp6_felem_offset)) (d1_felem y))
        (map.putmany m_py0 m_py1)).
      { exists m_py0, m_py1.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hpy0 | exact Hpy1]. }
      pose proof (Fp12_raw_FElem_join py (d0_felem y) (d1_felem y)
        (map.putmany m_py0 m_py1) Hlen_py0 Hlen_py1 Hjoin_py) as Hfp12_y.
      rewrite Fp12_list_decomp in Hfp12_y.
      exists (map.putmany m_R1 m_R0),
             (map.putmany (map.putmany m_px0 m_px1)
               (map.putmany (map.putmany m_py0 m_py1) m_rr')).
      split; [split |].
      { rewrite Heq_S0. rewrite <- !map.putmany_assoc.
        map_swap m_R0 m_R1. reflexivity. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out |].
      exists (map.putmany m_px0 m_px1),
             (map.putmany (map.putmany m_py0 m_py1) m_rr').
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp12_x |].
      exists (map.putmany m_py0 m_py1), m_rr'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp12_y | exact Hrr']. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp12_opp: componentwise negation                                  *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_opp : function_t :=
    (AbstractField.opp (F:=Fp12), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as allocx;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "allocx"; expr.var "x"]);
      coq:(cmd.call [] (AbstractField.opp (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.opp (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "allocx")])
    ))).

  Instance spec_of_Fp12_opp : spec_of (AbstractField.opp (F:=Fp12)) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=Fp12).

  Lemma Fp12_opp_ok : program_logic_goal_for_function! Fp12_opp.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy HFopp1 HFopp2.
    unfold spec_of_Fp12_opp, AbstractField.unop_spec.
    intros pout px old_out x Rr tr mem0
      [Hbx [[Rx Hmemx] Hmemout]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_opp].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst word_ok mem_ok allocx) as Hfbx.
    unfold AbstractField.Placeholder in Hfbx.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    (* Decompose memory *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === Fp12 copy: x → allocx === *)
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
    (* Post copy *)
    intros t' m' rets [Hrets [Htr Hsep_copy]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Decompose for Fp6 opp calls === *)
    destruct Hsep_copy as [m_new [m_frame [[Heq_m' Hd_n_f] [Hfelem_allocx Hframe]]]].
    subst m_frame m'.
    (* Split Fp12 FElems into 2 Fp6 components *)
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
    rewrite Heq_xr in Hd_n_f.
    rewrite Heq_xr.
    (* Build master 4-way sep fact *)
    assert (Hsep4 :
      ((FElem_Fp6 allocx (d0_felem x) ⋆
        FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x)) ⋆
       ((FElem_Fp6 pout (d0_felem old_out) ⋆
         FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out)) ⋆ Rr))
      (map.putmany (map.putmany m_ax0 m_ax1)
        (map.putmany (map.putmany m_o0 m_o1) m_rr))).
    { exists (map.putmany m_ax0 m_ax1),
        (map.putmany (map.putmany m_o0 m_o1) m_rr).
      split; [split; [reflexivity | exact Hd_n_f] |].
      split.
      { exists m_ax0, m_ax1.
        split; [split; [reflexivity | exact Hd_ax01] |].
        split; [exact Hfe_ax0 | exact Hfe_ax1]. }
      exists (map.putmany m_o0 m_o1), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, m_o1.
        split; [split; [reflexivity | exact Hd_o01] |].
        split; [exact Hfe_o0 | exact Hfe_o1]. }
      exact Hrr_out. }
    (* === First Fp6 opp: c0 === *)
    exists [pout; allocx]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFopp1 pout allocx
           (d0_felem old_out) (d0_felem x) _ tr).
         wp_unop_precond solve_bounds. }
    intros t_opp1 m_opp1 rets_opp1 [Hrets_opp1 [Htr_opp1 [out0' [Hfeval0 [Hbound0 Hsep_opp1]]]]].
    subst rets_opp1 t_opp1.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Second Fp6 opp: c1 === *)
    exists [word.add pout (word.of_Z fp6_felem_offset);
            word.add allocx (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFopp2 (word.add pout (word.of_Z fp6_felem_offset))
           (word.add allocx (word.of_Z fp6_felem_offset))
           (d1_felem old_out) (d1_felem x) _ tr).
         wp_unop_precond solve_bounds. }
    intros t_opp2 m_opp2 rets_opp2 [Hrets_opp2 [Htr_opp2 [out1' [Hfeval1 [Hbound1 Hsep_opp2]]]]].
    subst rets_opp2 t_opp2.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure sep into 5 maps === *)
    destruct Hsep_opp2 as [m_A [m_rest1 [[Heq_opp2 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_E [[Heq_r3 Hd_DE] [HD HE]]]].
    subst m_rest1 m_rest2 m_rest3 m_opp2.
    split_all_disjointness.
    pose proof (Fp6_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp6_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp6_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp6_FElem_length _ _ _ HA) as Hlen_A.
    (* === Allocx stack deallocation === *)
    assert (Hjoin_x : (FElem_Fp6 allocx (d0_felem x) ⋆
      FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x))
      (map.putmany m_C m_D)).
    { exists m_C, m_D.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HC | exact HD]. }
    pose proof (Fp12_raw_FElem_join allocx (d0_felem x) (d1_felem x)
      (map.putmany m_C m_D) Hlen_C Hlen_D Hjoin_x) as Hfp12_x.
    rewrite Fp12_list_decomp in Hfp12_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocx x
      (map.putmany m_C m_D) Hfp12_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_B m_E)), (map.putmany m_C m_D).
    split. { exact Hanybytes_x. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
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
    { fp12_feval_eq. rewrite Hd0_app, Hd1_app. rewrite Hfeval0, Hfeval1.
      reflexivity. }
    split.
    { fp12_bounded_by_eq. rewrite Hd0_app, Hd1_app. split; assumption. }
    { assert (Hjoin_out : (FElem_Fp6 pout out0' ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1')
        (map.putmany m_B m_A)).
      { exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp12_raw_FElem_join pout out0' out1'
        (map.putmany m_B m_A) Hlen_B Hlen_A Hjoin_out) as Hfp12_out.
      exists (map.putmany m_B m_A), m_E.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out | exact HE]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp12_conjugate: (c0, c1) -> (c0, -c1)                            *)
  (*   Cheap inverse for elements in the cyclotomic subgroup           *)
  (* -------------------------------------------------------------- *)

  Local Definition fp12_conjugate_name := (fp12_prefix ++ "conjugate")%string.

  Definition Fp12_conjugate : function_t :=
    (fp12_conjugate_name, (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as allocx;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "allocx"; expr.var "x"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "allocx")]);
      coq:(cmd.call [] (AbstractField.opp (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "allocx")])
    ))).

  Local Instance un_Fp12_conjugate
    : @AbstractField.UnOp _ _ _ _ Fp12 Fp12_fp_inst Fp12_repr_inst fp12_conjugate_name :=
    {| AbstractField.un_model := fun x => (fst x, @AbstractField.Fopp _ Fp6_fp_inst (snd x));
       AbstractField.un_xbounds := @AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst;
       AbstractField.un_outbounds := @AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst |}.

  Instance spec_of_Fp12_conjugate : spec_of fp12_conjugate_name :=
    AbstractField.unop_spec un_Fp12_conjugate.

  Lemma Fp12_conjugate_ok : program_logic_goal_for_function! Fp12_conjugate.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy HFcopy1 HFopp.
    unfold spec_of_Fp12_conjugate, AbstractField.unop_spec.
    intros pout px old_out x Rr tr mem0
      [Hbx [[Rx Hmemx] Hmemout]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_conjugate].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst word_ok mem_ok allocx) as Hfbx.
    unfold AbstractField.Placeholder in Hfbx.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    (* Decompose memory *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfx Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_x_rx]. subst mem0.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_m0_out Hd_out_rr].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst pout old_out m_out Hfe_out) as Hph_o.
    unfold AbstractField.Placeholder in Hph_o.
    (* === Fp12 copy: x → allocx === *)
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
    (* Post copy *)
    intros t' m' rets [Hrets [Htr Hsep_copy]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Decompose for sub-calls === *)
    destruct Hsep_copy as [m_new [m_frame [[Heq_m' Hd_n_f] [Hfelem_allocx Hframe]]]].
    subst m_frame m'.
    (* Split Fp12 FElems into 2 Fp6 components *)
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
    rewrite Heq_xr in Hd_n_f.
    rewrite Heq_xr.
    (* Build master 4-way sep fact *)
    assert (Hsep4 :
      ((FElem_Fp6 allocx (d0_felem x) ⋆
        FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x)) ⋆
       ((FElem_Fp6 pout (d0_felem old_out) ⋆
         FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out)) ⋆ Rr))
      (map.putmany (map.putmany m_ax0 m_ax1)
        (map.putmany (map.putmany m_o0 m_o1) m_rr))).
    { exists (map.putmany m_ax0 m_ax1),
        (map.putmany (map.putmany m_o0 m_o1) m_rr).
      split; [split; [reflexivity | exact Hd_n_f] |].
      split.
      { exists m_ax0, m_ax1.
        split; [split; [reflexivity | exact Hd_ax01] |].
        split; [exact Hfe_ax0 | exact Hfe_ax1]. }
      exists (map.putmany m_o0 m_o1), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o0, m_o1.
        split; [split; [reflexivity | exact Hd_o01] |].
        split; [exact Hfe_o0 | exact Hfe_o1]. }
      exact Hrr_out. }
    split_all_disjointness.
    (* === First: Fp6 copy c0 (allocx.c0 → out.c0) === *)
    exists [pout; allocx]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 pout allocx (d0_felem old_out) (d0_felem x)
        (fun m => (FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
                   (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆ Rr)) m)
        (fun m => m = map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_o1 m_rr)))
        tr).
      split.
      { exists (map.putmany m_ax0 m_o0),
               (map.putmany m_ax1 (map.putmany m_o1 m_rr)).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split.
        { exists m_ax0, m_o0.
          split; [split; [reflexivity |] |]; [map_disjoint_auto |].
          split; [exact Hfe_ax0 | exact Hfe_o0]. }
        { exists m_ax1, (map.putmany m_o1 m_rr).
          split; [split; [reflexivity |] |]; [map_disjoint_auto |].
          split; [exact Hfe_ax1 |].
          exists m_o1, m_rr.
          split; [split; [reflexivity |] |]; [map_disjoint_auto |].
          split; [exact Hfe_o1 | exact Hrr_out]. } }
      { exists m_o0, (map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_o1 m_rr))).
        split; [split |].
        { solve_putmany_eq. }
        { map_disjoint_auto. }
        split; [exact Hfe_o0 | exact eq_refl]. } }
    intros t_c1 m_c1 rets_c1 [Hrets_c1 [Htr_c1 Hsep_copy1]].
    subst rets_c1. symmetry in Htr_c1. subst t_c1.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* Decompose copy1 postcondition *)
    destruct Hsep_copy1 as [m_new0 [m_frame1 [Hsp_post1 [Hnew0 Hframe1]]]].
    subst m_frame1.
    destruct Hsp_post1 as [Heq_c1 Hd_c1].
    split_all_disjointness.
    (* Build sep fact for the opp call *)
    assert (Hsep5 :
      (FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
       (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆
        (FElem_Fp6 pout (d0_felem x) ⋆
         (FElem_Fp6 allocx (d0_felem x) ⋆ Rr))))
      m_c1).
    { subst m_c1.
      exists m_ax1, (map.putmany m_o1 (map.putmany m_new0 (map.putmany m_ax0 m_rr))).
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfe_ax1 |].
      exists m_o1, (map.putmany m_new0 (map.putmany m_ax0 m_rr)).
      split; [split; [reflexivity |] |]; [map_disjoint_auto |].
      split; [exact Hfe_o1 |].
      exists m_new0, (map.putmany m_ax0 m_rr).
      split; [split; [reflexivity |] |]; [map_disjoint_auto |].
      split; [exact Hnew0 |].
      exists m_ax0, m_rr.
      split; [split; [reflexivity |] |]; [map_disjoint_auto |].
      split; [exact Hfe_ax0 | exact Hrr_out]. }
    (* === Second: Fp6 opp c1 (allocx.c1 → out.c1) === *)
    exists [word.add pout (word.of_Z fp6_felem_offset);
            word.add allocx (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFopp (word.add pout (word.of_Z fp6_felem_offset))
           (word.add allocx (word.of_Z fp6_felem_offset))
           (d1_felem old_out) (d1_felem x) _ tr).
         wp_unop_precond solve_bounds. }
    intros t_opp m_opp rets_opp [Hrets_opp [Htr_opp [out1' [Hfeval1 [Hbound1 Hsep_opp]]]]].
    subst rets_opp. symmetry in Htr_opp. subst t_opp.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure sep into individual maps === *)
    destruct Hsep_opp as [m_A [m_rest1 [[Heq_opp Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_E [[Heq_r3 Hd_DE] [HD HE]]]].
    subst m_rest1 m_rest2 m_rest3 m_opp.
    split_all_disjointness.
    pose proof (Fp6_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp6_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp6_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp6_FElem_length _ _ _ HA) as Hlen_A.
    (* === Allocx stack deallocation === *)
    assert (Hjoin_x : (FElem_Fp6 allocx (d0_felem x) ⋆
      FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x))
      (map.putmany m_D m_B)).
    { exists m_D, m_B.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HD | exact HB]. }
    pose proof (Fp12_raw_FElem_join allocx (d0_felem x) (d1_felem x)
      (map.putmany m_D m_B) Hlen_D Hlen_B Hjoin_x) as Hfp12_x.
    rewrite Fp12_list_decomp in Hfp12_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocx x
      (map.putmany m_D m_B) Hfp12_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_C m_E)), (map.putmany m_D m_B).
    split. { exact Hanybytes_x. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (d0_felem x ++ out1').
    assert (Hd0_app : d0_felem (d0_felem x ++ out1') = d0_felem x).
    { apply d0_felem_app. exact Hlen_C. }
    assert (Hd1_app : d1_felem (d0_felem x ++ out1') = out1').
    { apply d1_felem_app. exact Hlen_C. }
    split.
    { fp12_feval_eq. rewrite Hd0_app, Hd1_app. rewrite Hfeval1.
      reflexivity. }
    split.
    { fp12_bounded_by_eq. rewrite Hd0_app, Hd1_app.
      split; [solve_bounds | exact Hbound1]. }
    { assert (Hjoin_out : (FElem_Fp6 pout (d0_felem x) ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1')
        (map.putmany m_C m_A)).
      { exists m_C, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC | exact HA]. }
      pose proof (Fp12_raw_FElem_join pout (d0_felem x) out1'
        (map.putmany m_C m_A) Hlen_C Hlen_A Hjoin_out) as Hfp12_out.
      exists (map.putmany m_C m_A), m_E.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out | exact HE]. }
  Qed.

  (* -------------------------------------------------------------- *)
  (* fp12_mul: Karatsuba multiplication                                *)
  (*                                                                   *)
  (* v0 = a0*b0                  (Fp6 mul)                             *)
  (* v1 = a1*b1                  (Fp6 mul)                             *)
  (* t  = a0+a1                  (Fp6 add)                             *)
  (* u  = b0+b1                  (Fp6 add)                             *)
  (* t  = t*u = (a0+a1)(b0+b1)  (Fp6 mul)                             *)
  (* out.c0 = v0 + mul_by_v(v1)                                       *)
  (* out.c1 = t - v0 - v1                                              *)
  (* -------------------------------------------------------------- *)

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

  (* No-alias Fp12_mul: skips input copies, requires out != inx /\ out != iny.
     The Karatsuba algorithm reads all inputs before writing to out,
     so non-aliasing is sufficient for correctness. Saves 2 Fp12 copies. *)
  Definition Fp12_mul_nocopy : function_t :=
    ((AbstractField.mul (F:=Fp12) ++ "_nocopy")%string,
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as v0;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as v1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as u;
      (* v0 = a0*b0 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr.var "v0"; expr_fp12_c0 (expr.var "inx"); expr_fp12_c0 (expr.var "iny")]);
      (* v1 = a1*b1 *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr.var "v1"; expr_fp12_c1 (expr.var "inx"); expr_fp12_c1 (expr.var "iny")]);
      (* t = a0+a1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr.var "t"; expr_fp12_c0 (expr.var "inx"); expr_fp12_c1 (expr.var "inx")]);
      (* u = b0+b1 *)
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr.var "u"; expr_fp12_c0 (expr.var "iny"); expr_fp12_c1 (expr.var "iny")]);
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

  (* Fp12_mul_ok is proved in DodecicFieldExtensionsMul.v *)
  (* Proof:
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
    (* === First Fp12 copy: x → allocx === *)
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
    (* === Second Fp12 copy: y → allocy === *)
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
    (* Build master 10-way sep fact — ay before ax to match actual memory layout *)
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
    { (* feval — rewrite in dependency order: outermost first, then expand *)
      fp12_feval_eq. rewrite Hd0_app, Hd1_app.
      rewrite Hfeval_out0, Hfeval_out1.
      rewrite Hfeval_t''.                     (* t''' → sub t'' v0' *)
      rewrite Hfeval_u'.                      (* u'' → mul_by_v v1' *)
      rewrite Hfeval_t'.                      (* t'' → mul t' u' *)
      rewrite Hfeval_t, Hfeval_u.            (* t' → add a0 a1, u' → add b0 b1 *)
      rewrite Hfeval_v0, Hfeval_v1.          (* v0' → mul a0 b0, v1' → mul a1 b1 *)
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
  Qed. *)

  (* -------------------------------------------------------------- *)
  (* fp12_sqr: squaring                                                *)
  (*                                                                   *)
  (* t0 = a0^2                   (Fp6 square)                         *)
  (* t1 = a1^2                   (Fp6 square)                         *)
  (* t2 = a0*a1                  (Fp6 mul)                             *)
  (* out.c0 = t0 + mul_by_v(t1)                                       *)
  (* out.c1 = t2 + t2 = 2*a0*a1                                       *)
  (* -------------------------------------------------------------- *)

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

  (* Fp12_sqr_ok is proved in DodecicFieldExtensionsSqr.v *)
  (* Proof:
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
      (* Unfold LHS to BLS12Fp6Spec level *)
      cbv [AbstractField.bin_model AbstractField.bin_mul AbstractField.bin_add
           AbstractField.Fmul AbstractField.Fadd
           Fp6_fp_inst Fp6_field_parameters
           CubicFieldExtensionsSpecs.fp6_mul_fn CubicFieldExtensionsSpecs.fp6_add_fn
           AbstractField.un_model un_Fp6_mul_by_v fp6_mul_by_v_model].
      (* Unfold RHS Fp12 sqr spec *)
      cbv [AbstractField.Fmul Fp12_fp_inst Fp12_field_parameters
           DodecicFieldExtensionsSpecs.fp12_mul_fn
           BLS12Fp12Spec.fp12_mul BLS12Fp12Spec.fp12_c0 BLS12Fp12Spec.fp12_c1
           BLS12Fp12Spec.mk_fp12 fst snd].
      (* Bridge module aliases: unfold both sides to raw Fp6 bodies *)
      (* Unfold both Fp6.* and BLS12Fp6Spec.* to Fp2-level bodies (keep Fp2 ops opaque) *)
      cbv [Fp6.fp6_add Fp6.fp6_sub Fp6.fp6_mul Fp6.fp6_mul_by_v
           Fp6.fp6_c0 Fp6.fp6_c1 Fp6.fp6_c2 Fp6.fp6_build
           BLS12Fp6Spec.fp6_add BLS12Fp6Spec.fp6_sub BLS12Fp6Spec.fp6_mul
           BLS12Fp6Spec.fp6_mul_by_v
           BLS12Fp6Spec.fp6_c0 BLS12Fp6Spec.fp6_c1 BLS12Fp6Spec.fp6_c2
           BLS12Fp6Spec.fp6_build
           BLS12Fp6Spec.fp2_add BLS12Fp6Spec.fp2_sub BLS12Fp6Spec.fp2_mul
           BLS12Fp6Spec.fp2_mul_xi
           Fp6.fp2_add Fp6.fp2_sub Fp6.fp2_mul Fp6.fp2_mul_xi
           fst snd].
      (* c1 needs the Karatsuba identity; unfold everything to F level in both *)
      pose proof (fp6_double_eq_karatsuba a0 a1) as Hk.
      cbv [AbstractField.Fadd AbstractField.Fmul AbstractField.Fsub
           Fp6_fp_inst Fp6_field_parameters
           CubicFieldExtensionsSpecs.fp6_add_fn CubicFieldExtensionsSpecs.fp6_mul_fn
           CubicFieldExtensionsSpecs.fp6_sub_fn
           BLS12Fp6Spec.fp6_add BLS12Fp6Spec.fp6_sub BLS12Fp6Spec.fp6_mul
           BLS12Fp6Spec.fp6_c0 BLS12Fp6Spec.fp6_c1 BLS12Fp6Spec.fp6_c2
           BLS12Fp6Spec.fp6_build
           BLS12Fp6Spec.fp2_add BLS12Fp6Spec.fp2_sub BLS12Fp6Spec.fp2_mul
           BLS12Fp6Spec.fp2_mul_xi
           QuadraticExtensions.mulp2 QuadraticExtensions.addp2 QuadraticExtensions.subp2
           fst snd] in Hk.
      rewrite Hk. reflexivity. }
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
  Qed. *)

  (* -------------------------------------------------------------- *)
  (* fp12_inv: full inverse using quadratic norm                       *)
  (*                                                                   *)
  (* norm = a0^2 - mul_by_v(a1^2)  (quadratic extension norm)         *)
  (* norm_inv = Fp6_inv(norm)                                          *)
  (* out.c0 = a0 * norm_inv                                           *)
  (* out.c1 = -(a1 * norm_inv)                                        *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_inv : function_t :=
    (AbstractField.inv (F:=Fp12), (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp12)) as allocx;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp12)) [expr.var "allocx"; expr.var "x"]);
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t0;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t1;
      (* t0 = a0^2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp6)) [expr.var "t0"; expr_fp12_c0 (expr.var "allocx")]);
      (* t1 = a1^2 *)
      coq:(cmd.call [] (AbstractField.square (F:=Fp6)) [expr.var "t1"; expr_fp12_c1 (expr.var "allocx")]);
      (* t1 = mul_by_v(a1^2) *)
      coq:(cmd.call [] fp6_mul_by_v_name [expr.var "t1"; expr.var "t1"]);
      (* t0 = a0^2 - mul_by_v(a1^2) = norm *)
      coq:(cmd.call [] (AbstractField.sub (F:=Fp6)) [expr.var "t0"; expr.var "t0"; expr.var "t1"]);
      (* t0 = inv(norm) *)
      coq:(cmd.call [] (AbstractField.inv (F:=Fp6)) [expr.var "t0"; expr.var "t0"]);
      (* out.c0 = a0 * inv(norm) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr_fp12_c0 (expr.var "allocx"); expr.var "t0"]);
      (* out.c1 = a1 * inv(norm) *)
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "allocx"); expr.var "t0"]);
      (* out.c1 = -(a1 * inv(norm)) *)
      coq:(cmd.call [] (AbstractField.opp (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr_fp12_c1 (expr.var "out")])
    ))).

  Instance spec_of_Fp12_inv : spec_of (AbstractField.inv (F:=Fp12)) :=
    AbstractField.unop_spec AbstractField.un_inv (F:=Fp12).

  (* Fp12_inv_ok is proved in DodecicFieldExtensionsInv.v *)
  (* Proof:
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy HFsqr1 HFsqr2 HFmbv HFsub HFinv6 HFmul1 HFmul2 HFopp.
    unfold spec_of_Fp12_inv, AbstractField.unop_spec.
    intros pout px old_out x Rr tr mem0
      [Hbx [[Rx Hmemx] Hmemout]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_inv].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst word_ok mem_ok allocx) as Hfbx.
    unfold AbstractField.Placeholder in Hfbx.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    (* Decompose memory *)
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
    (* Post copy *)
    intros t' m' rets [Hrets [Htr Hsep_copy]].
    subst rets. symmetry in Htr. subst t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc t0 === *)
    split. { apply Z_mod_mult. }
    intros t0_ptr mStack_t0 m_t0c Hstack_t0 Hm_t0.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok t0_ptr) as Hfb_t0.
    unfold AbstractField.Placeholder in Hfb_t0.
    pose proof (proj1 (Hfb_t0 mStack_t0) Hstack_t0) as [t0_val Ht0_felem]. clear Hfb_t0.
    repeat straightline.
    (* === Stackalloc t1 === *)
    split. { apply Z_mod_mult. }
    intros t1_ptr mStack_t1 m_t1c Hstack_t1 Hm_t1.
    pose proof (@AbstractField.FElem_from_bytes _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst word_ok mem_ok t1_ptr) as Hfb_t1.
    unfold AbstractField.Placeholder in Hfb_t1.
    pose proof (proj1 (Hfb_t1 mStack_t1) Hstack_t1) as [t1_val Ht1_felem]. clear Hfb_t1.
    repeat straightline.
    (* === Decompose for Fp6 sub-calls === *)
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
    rewrite Heq_xr in Hd_n_f.
    destruct Hm_t0 as [Heq_t0c Hd_t0c]. subst m_t0c.
    destruct Hm_t1 as [Heq_t1c Hd_t1c]. subst m_t1c.
    rewrite Heq_xr in Hd_t0c. rewrite Heq_xr in Hd_t1c.
    rewrite Heq_xr.
    split_all_disjointness.
    (* Derive missing disjointness for m_o0, m_o1, m_rr vs mStack_t1 *)
    (* Derive disjointness for m_o0, m_o1, m_rr vs mStack_t1 *)
    assert (Hd_o0_t1 : map.disjoint m_o0 mStack_t1) by map_disjoint_auto.
    assert (Hd_o1_t1 : map.disjoint m_o1 mStack_t1) by map_disjoint_auto.
    assert (Hd_rr_t1 : map.disjoint m_rr mStack_t1) by map_disjoint_auto.
    (* Build master sep fact *)
    assert (Hsep :
      (FElem_Fp6 t0_ptr t0_val ⋆
       (FElem_Fp6 t1_ptr t1_val ⋆
        (FElem_Fp6 allocx (d0_felem x) ⋆
         (FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
          (FElem_Fp6 pout (d0_felem old_out) ⋆
           (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆ Rr))))))
      (map.putmany
        (map.putmany
          (map.putmany (map.putmany m_ax0 m_ax1)
            (map.putmany (map.putmany m_o0 m_o1) m_rr))
          mStack_t0)
        mStack_t1)).
    { exists mStack_t0, (map.putmany mStack_t1 (map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_o0 (map.putmany m_o1 m_rr))))).
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Ht0_felem |].
      exists mStack_t1, (map.putmany m_ax0 (map.putmany m_ax1 (map.putmany m_o0 (map.putmany m_o1 m_rr)))).
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Ht1_felem |].
      exists m_ax0, (map.putmany m_ax1 (map.putmany m_o0 (map.putmany m_o1 m_rr))).
      split; [split; [reflexivity |] |]; [map_disjoint_auto |].
      split; [exact Hfe_ax0 |].
      exists m_ax1, (map.putmany m_o0 (map.putmany m_o1 m_rr)).
      split; [split; [reflexivity |] |]; [map_disjoint_auto |].
      split; [exact Hfe_ax1 |].
      exists m_o0, (map.putmany m_o1 m_rr).
      split; [split; [reflexivity |] |]; [map_disjoint_auto |].
      split; [exact Hfe_o0 |].
      exists m_o1, m_rr.
      split; [split; [reflexivity |] |]; [map_disjoint_auto |].
      split; [exact Hfe_o1 | exact Hrr_out]. }
    (* === Call 1: t0 = Fp6_square(allocx.c0) === *)
    exists [t0_ptr; allocx]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr1 t0_ptr allocx
           t0_val (d0_felem x) _ tr).
         wp_unop_precond solve_bounds. }
    intros t_s1 m_s1 rets_s1 [Hrets_s1 [Htr_s1 [t0' [Hfeval_t0 [Hbound_t0 Hsep_s1]]]]].
    subst rets_s1. symmetry in Htr_s1. subst t_s1.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => t0_ptr; "t1" => t1_ptr }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 2: t1 = Fp6_square(allocx.c1) === *)
    exists [t1_ptr; word.add allocx (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsqr2 t1_ptr (word.add allocx (word.of_Z fp6_felem_offset))
           t1_val (d1_felem x) _ tr).
         wp_unop_precond solve_bounds. }
    intros t_s2 m_s2 rets_s2 [Hrets_s2 [Htr_s2 [t1' [Hfeval_t1 [Hbound_t1 Hsep_s2]]]]].
    subst rets_s2. symmetry in Htr_s2. subst t_s2.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => t0_ptr; "t1" => t1_ptr }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: t1 = mul_by_v(t1) === *)
    exists [t1_ptr; t1_ptr].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmbv t1_ptr t1_ptr
           t1' t1' _ tr).
         wp_unop_precond solve_bounds. }
    intros t_m3 m_m3 rets_m3 [Hrets_m3 [Htr_m3 [t1'' [Hfeval_t1' [Hbound_t1' Hsep_m3]]]]].
    subst rets_m3. symmetry in Htr_m3. subst t_m3.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => t0_ptr; "t1" => t1_ptr }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 4: t0 = Fp6_sub(t0, t1) === *)
    exists [t0_ptr; t0_ptr; t1_ptr].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub t0_ptr t0_ptr t1_ptr
           t0' t0' t1'' _ tr).
         wp_binop_precond solve_bounds. }
    intros t_s4 m_s4 rets_s4 [Hrets_s4 [Htr_s4 [t0'' [Hfeval_t0' [Hbound_t0' Hsep_s4]]]]].
    subst rets_s4. symmetry in Htr_s4. subst t_s4.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => t0_ptr; "t1" => t1_ptr }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 5: t0 = Fp6_inv(t0) === *)
    exists [t0_ptr; t0_ptr].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFinv6 t0_ptr t0_ptr
           t0'' t0'' _ tr).
         wp_unop_precond solve_bounds. }
    intros t_i5 m_i5 rets_i5 [Hrets_i5 [Htr_i5 [t0''' [Hfeval_t0'' [Hbound_t0'' Hsep_i5]]]]].
    subst rets_i5. symmetry in Htr_i5. subst t_i5.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => t0_ptr; "t1" => t1_ptr }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 6: out.c0 = Fp6_mul(allocx.c0, t0) === *)
    exists [pout; allocx; t0_ptr].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul1 pout allocx t0_ptr
           (d0_felem old_out) (d0_felem x) t0''' _ tr).
         wp_binop_precond solve_bounds. }
    intros t_m6 m_m6 rets_m6 [Hrets_m6 [Htr_m6 [out0' [Hfeval_c0 [Hbound_c0 Hsep_m6]]]]].
    subst rets_m6. symmetry in Htr_m6. subst t_m6.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => t0_ptr; "t1" => t1_ptr }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 7: out.c1 = Fp6_mul(allocx.c1, t0) === *)
    exists [word.add pout (word.of_Z fp6_felem_offset);
            word.add allocx (word.of_Z fp6_felem_offset);
            t0_ptr].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul2 (word.add pout (word.of_Z fp6_felem_offset))
           (word.add allocx (word.of_Z fp6_felem_offset))
           t0_ptr
           (d1_felem old_out) (d1_felem x) t0''' _ tr).
         wp_binop_precond solve_bounds. }
    intros t_m7 m_m7 rets_m7 [Hrets_m7 [Htr_m7 [out1' [Hfeval_c1 [Hbound_c1 Hsep_m7]]]]].
    subst rets_m7. symmetry in Htr_m7. subst t_m7.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => t0_ptr; "t1" => t1_ptr }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Call 8: out.c1 = Fp6_opp(out.c1) === *)
    exists [word.add pout (word.of_Z fp6_felem_offset);
            word.add pout (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFopp (word.add pout (word.of_Z fp6_felem_offset))
           (word.add pout (word.of_Z fp6_felem_offset))
           out1' out1' _ tr).
         wp_unop_precond solve_bounds. }
    intros t_o8 m_o8 rets_o8 [Hrets_o8 [Htr_o8 [out1'' [Hfeval_c1' [Hbound_c1' Hsep_o8]]]]].
    subst rets_o8. symmetry in Htr_o8. subst t_o8.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px; "allocx" => allocx; "t0" => t0_ptr; "t1" => t1_ptr }#).
    split. { exact eq_refl. }
    repeat straightline.
    (* === Destructure final sep === *)
    destruct Hsep_o8 as [m_A [m_rest1 [[Heq_o8 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_F [m_G [[Heq_r5 Hd_FG] [HF HG]]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_o8.
    split_all_disjointness.
    pose proof (Fp6_FElem_length _ _ _ HA) as Hlen_A.
    pose proof (Fp6_FElem_length _ _ _ HB) as Hlen_B.
    pose proof (Fp6_FElem_length _ _ _ HC) as Hlen_C.
    pose proof (Fp6_FElem_length _ _ _ HD) as Hlen_D.
    pose proof (Fp6_FElem_length _ _ _ HE) as Hlen_E.
    pose proof (Fp6_FElem_length _ _ _ HF) as Hlen_F.
    (* Sep order after 8 calls (from ecancel):
       A = out1'' at out.c1,  B = out0' at out.c0,
       C = t0''' at t0_ptr,   D = allocx.c1 (d1_felem x),
       E = allocx.c0 (d0_felem x), F = t1'' at t1_ptr,  G = Rr *)
    (* Sep order: A=out1'', B=out0', C=t0''' at t0_ptr, D=t1'' at t1_ptr,
       E=allocx.c0, F=allocx.c1, G=Rr *)
    (* === Deallocate t1 stack (m_D) === *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst t1_ptr _ m_D HD) as Hab_t1.
    unfold AbstractField.Placeholder in Hab_t1.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_C (map.putmany m_E (map.putmany m_F m_G))))), m_D.
    split. { exact Hab_t1. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
    (* === Deallocate t0 stack (m_C) === *)
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp6_fp_inst Fp6_repr_inst t0_ptr _ m_C HC) as Hab_t0.
    unfold AbstractField.Placeholder in Hab_t0.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_E (map.putmany m_F m_G)))), m_C.
    split. { exact Hab_t0. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
    (* === Deallocate allocx stack (m_E + m_F) === *)
    assert (Hjoin_ax : (FElem_Fp6 allocx (d0_felem x) ⋆
      FElem_Fp6 (word.add allocx (word.of_Z fp6_felem_offset)) (d1_felem x))
      (map.putmany m_E m_F)).
    { exists m_E, m_F.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact HE | exact HF]. }
    pose proof (Fp12_raw_FElem_join allocx (d0_felem x) (d1_felem x)
      (map.putmany m_E m_F) Hlen_E Hlen_F Hjoin_ax) as Hfp12_ax.
    rewrite Fp12_list_decomp in Hfp12_ax.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp12_fp_inst Fp12_repr_inst allocx x
      (map.putmany m_E m_F) Hfp12_ax) as Hab_ax.
    unfold AbstractField.Placeholder in Hab_ax.
    exists (map.putmany m_A (map.putmany m_B m_G)), (map.putmany m_E m_F).
    split. { exact Hab_ax. }
    split. { split.
      { solve_putmany_eq. }
      { map_disjoint_auto. } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1'').
    assert (Hd0_app : d0_felem (out0' ++ out1'') = out0').
    { apply d0_felem_app. exact Hlen_B. }
    assert (Hd1_app : d1_felem (out0' ++ out1'') = out1'').
    { apply d1_felem_app. exact Hlen_B. }
    split.
    { (* feval *)
      fp12_feval_eq. rewrite Hd0_app, Hd1_app.
      rewrite Hfeval_c0, Hfeval_c1'.
      rewrite Hfeval_c1.
      rewrite Hfeval_t0'', Hfeval_t0', Hfeval_t0.
      rewrite Hfeval_t1', Hfeval_t1.
      unfold un_model, AbstractField.un_inv, Fp12_fp_inst, Fp12_field_parameters.
      cbv [Finv DodecicFieldExtensionsSpecs.fp12_inv_fn
           BLS12Fp12Spec.fp12_inv BLS12Fp12Spec.fp12_c0 BLS12Fp12Spec.fp12_c1 BLS12Fp12Spec.mk_fp12
           fst snd].
      cbv [Fopp Fp6_fp_inst Fp6_field_parameters
           CubicFieldExtensionsSpecs.fp6_neg_fn BLS12Fp6Spec.fp6_neg].
      cbv [Fmul Fp6_fp_inst Fp6_field_parameters
           CubicFieldExtensionsSpecs.fp6_mul_fn BLS12Fp6Spec.fp6_mul].
      cbv [Finv Fp6_fp_inst Fp6_field_parameters
           CubicFieldExtensionsSpecs.fp6_inv_fn BLS12Fp6Spec.fp6_inv].
      cbv [Fsub Fp6_fp_inst Fp6_field_parameters
           CubicFieldExtensionsSpecs.fp6_sub_fn BLS12Fp6Spec.fp6_sub].
      cbv [AbstractField.Fsquare].
      cbv [un_model un_Fp6_mul_by_v fp6_mul_by_v_model].
      cbv [BLS12Fp6Spec.fp6_sqr BLS12Fp6Spec.fp6_mul_by_v
           BLS12Fp6Spec.fp6_c0 BLS12Fp6Spec.fp6_c1 BLS12Fp6Spec.fp6_c2
           BLS12Fp6Spec.fp6_build fst snd].
      (* Bridge module aliases *)
      match goal with |- ?L = ?R =>
        let R' := eval cbv [Fp6.fp6_mul Fp6.fp6_sub Fp6.fp6_neg Fp6.fp6_inv
                            Fp6.fp6_sqr Fp6.fp6_mul_by_v
                            Fp6.fp6_c0 Fp6.fp6_c1 Fp6.fp6_c2 Fp6.fp6_build] in R in
        change (L = R')
      end.
      cbv [BLS12Fp6Spec.fp6_mul BLS12Fp6Spec.fp6_sub BLS12Fp6Spec.fp6_neg
           BLS12Fp6Spec.fp6_inv BLS12Fp6Spec.fp6_sqr BLS12Fp6Spec.fp6_mul_by_v
           BLS12Fp6Spec.fp6_c0 BLS12Fp6Spec.fp6_c1 BLS12Fp6Spec.fp6_c2
           BLS12Fp6Spec.fp6_build fst snd].
      reflexivity. }
    split.
    { (* bounded *)
      fp12_bounded_by_eq. rewrite Hd0_app, Hd1_app.
      split; solve_bounds. }
    { (* sep *)
      assert (Hjoin_out : (FElem_Fp6 pout out0' ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1'')
        (map.putmany m_B m_A)).
      { exists m_B, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HB | exact HA]. }
      pose proof (Fp12_raw_FElem_join pout out0' out1''
        (map.putmany m_B m_A) Hlen_B Hlen_A Hjoin_out) as Hfp12_out.
      exists (map.putmany m_B m_A), m_G.
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out | exact HG]. }
  Qed. *)

  (* -------------------------------------------------------------- *)
  (* Collected function list for downstream linking                    *)
  (* -------------------------------------------------------------- *)

  Definition Fp12_funcs : list function_t :=
    [ Fp6_mul_by_v;
      Fp12_felem_copy;
      Fp12_add;
      Fp12_sub;
      Fp12_opp;
      Fp12_conjugate;
      Fp12_mul;
      Fp12_sqr;
      Fp12_inv;
      Fp12_add_nocopy;
      Fp12_sub_nocopy;
      Fp12_mul_nocopy ].

End Fp12.
