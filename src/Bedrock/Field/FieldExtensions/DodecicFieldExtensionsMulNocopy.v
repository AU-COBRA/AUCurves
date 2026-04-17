(** * Standalone compilation unit for the Fp12_mul_nocopy_ok proof.
    The nocopy version skips input copies, saving 2 Fp12-sized stackalloc+copy.
    Requires non-aliasing: out != inx /\ out != iny (guaranteed by sep).
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

  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  Variable beta : F M_pos.
  Hypothesis beta_nz : beta <> @F.zero M_pos.
  Hypothesis beta_qnr : ~(exists x, @F.mul M_pos x x = beta).
  Context {M_big : 2 < Z.pos M_pos}.

  Variable xi_re : F M_pos.
  Variable xi_im : F M_pos.
  Variable fp6_prefix fp2_prefix : String.string.
  Variable fp6_mul_by_v_name : String.string.

  Local Notation Fp2_fp_inst := (@QuadraticFieldExtensionsSpecs.Fp2_field_parameters
    M_pos prime_parameters beta).
  Local Notation Fp2_repr_inst := (@QuadraticFieldExtensionsSpecs.Fp2_field_representation
    _ _ _ _ prime_parameters F_representation beta fp2_prefix).
  Local Notation Fp6_fp_inst := (@CubicFieldExtensionsSpecs.Fp6_field_parameters
    M_pos prime_parameters beta xi_re xi_im).
  Local Notation Fp6_repr_inst := (@CubicFieldExtensionsSpecs.Fp6_field_representation
    _ _ _ _ prime_parameters F_representation beta xi_re xi_im fp6_prefix fp2_prefix).
  Local Notation Fp12_fp_inst := (@DodecicFieldExtensionsSpecs.Fp12_field_parameters
    M_pos prime_parameters beta xi_re xi_im).
  Local Notation Fp12_repr_inst := (@DodecicFieldExtensionsSpecs.Fp12_field_representation
    _ _ _ _ prime_parameters F_representation beta xi_re xi_im fp6_prefix fp2_prefix).

  Local Notation FElem_Fp6 := (@AbstractField.FElem _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).
  Local Notation Fp6_felem_size := (@AbstractField.felem_size_in_words _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst).

  Local Notation fp2_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp2))).
  Local Notation fp6_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp6))).
  Local Definition expr_fp12_c0 (x : Syntax.expr) := x.
  Local Definition expr_fp12_c1 (x : Syntax.expr) :=
    expr.op bopname.add x (expr.literal fp6_felem_offset).

  Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
  Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.

  Import DodecicFieldExtensionsSpecs.

  (* Specs for callees *)
  Instance spec_of_Fp6_mul : spec_of (AbstractField.mul (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp6).
  Instance spec_of_Fp6_add : spec_of (AbstractField.add (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=Fp6).
  Instance spec_of_Fp6_sub : spec_of (AbstractField.sub (F:=Fp6)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=Fp6).

  Local Definition fp6_mul_by_v_model (x : Fp6) : Fp6 :=
    ((BLS12Fp6Spec.fp2_mul_xi M_pos beta xi_re xi_im (snd x), fst (fst x)), snd (fst x)).

  Local Instance un_Fp6_mul_by_v
    : @AbstractField.UnOp _ _ _ _ Fp6 Fp6_fp_inst Fp6_repr_inst fp6_mul_by_v_name :=
    {| AbstractField.un_model := fp6_mul_by_v_model;
       AbstractField.un_xbounds := @AbstractField.tight_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst;
       AbstractField.un_outbounds := @AbstractField.loose_bounds _ Fp6_fp_inst _ _ _ _ Fp6_repr_inst |}.

  Instance spec_of_Fp6_mul_by_v : spec_of fp6_mul_by_v_name :=
    AbstractField.unop_spec un_Fp6_mul_by_v.

  Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=Fp12).

  (* Fp12_mul_nocopy definition *)
  Definition Fp12_mul_nocopy : function_t :=
    ((AbstractField.mul (F:=Fp12) ++ "_nocopy")%string,
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as v0;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as v1;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as t;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as u;
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr.var "v0"; expr_fp12_c0 (expr.var "inx"); expr_fp12_c0 (expr.var "iny")]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr.var "v1"; expr_fp12_c1 (expr.var "inx"); expr_fp12_c1 (expr.var "iny")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr.var "t"; expr_fp12_c0 (expr.var "inx"); expr_fp12_c1 (expr.var "inx")]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr.var "u"; expr_fp12_c0 (expr.var "iny"); expr_fp12_c1 (expr.var "iny")]);
      coq:(cmd.call [] (AbstractField.mul (F:=Fp6)) [expr.var "t"; expr.var "t"; expr.var "u"]);
      coq:(cmd.call [] fp6_mul_by_v_name [expr.var "u"; expr.var "v1"]);
      coq:(cmd.call [] (AbstractField.add (F:=Fp6)) [expr_fp12_c0 (expr.var "out"); expr.var "v0"; expr.var "u"]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp6)) [expr.var "t"; expr.var "t"; expr.var "v0"]);
      coq:(cmd.call [] (AbstractField.sub (F:=Fp6)) [expr_fp12_c1 (expr.var "out"); expr.var "t"; expr.var "v1"])
    ))).

  (* Tactics from DodecicFieldExtensionsMul.v *)
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
    cbv [dexprs list_map list_map_body expr_fp12_c0 expr_fp12_c1
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
      | match goal with
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

  (* Need Fp6_bounds_tight_of_loose from DodecicFieldExtensions *)
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

  Lemma Fp12_mul_nocopy_ok :
    forall functions
      (EnvContains : map.get functions (fst Fp12_mul_nocopy) = Some (snd Fp12_mul_nocopy))
      (HFmul1 : spec_of_Fp6_mul functions)
      (HFmul2 : spec_of_Fp6_mul functions)
      (HFadd1 : spec_of_Fp6_add functions)
      (HFadd2 : spec_of_Fp6_add functions)
      (HFmul3 : spec_of_Fp6_mul functions)
      (HFmulv : spec_of_Fp6_mul_by_v functions)
      (HFadd3 : spec_of_Fp6_add functions)
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
      WeakestPrecondition.call functions (fst Fp12_mul_nocopy) tr mem0 [pout; px; py]
        (fun tr' mem' rets =>
           rets = [] /\ tr = tr' /\
           exists result,
             @AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst result =
             @AbstractField.Fmul _ Fp12_fp_inst
               (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst x)
               (@AbstractField.feval _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst y) /\
             @AbstractField.bounded_by _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst
               (@AbstractField.tight_bounds _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst) result /\
             (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst pout result ⋆
              (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst px x ⋆
               (@AbstractField.FElem _ Fp12_fp_inst _ _ _ _ Fp12_repr_inst py y ⋆ Rr))) mem').
  Proof.
    intros functions EnvContains HFmul1 HFmul2 HFadd1 HFadd2 HFmul3 HFmulv HFadd3 HFsub1 HFsub2.
    intros pout px py old_out x y Rr tr mem0 Hbx Hby Hsep.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp12_mul_nocopy].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Decompose Fp12 FElems into Fp6 halves === *)
    destruct Hsep as [m_x [m_yr [[Heq_m0 Hd_x_yr] [Hfx Hyr]]]].
    destruct Hyr as [m_y [m_or [[Heq_yr Hd_y_or] [Hfy Hor]]]].
    destruct Hor as [m_out [m_rr [[Heq_or Hd_out_rr] [Hfe_out Hrr_out]]]].
    subst m_yr m_or mem0.
    pose proof (Fp12_raw_FElem_split px x m_x Hfx) as Hsplit_x.
    destruct Hsplit_x as [m_x0 [m_x1 [Hsp_x [Hfe_x0 Hfe_x1]]]].
    destruct Hsp_x as [Heq_x Hd_x01].
    pose proof (Fp12_raw_FElem_split py y m_y Hfy) as Hsplit_y.
    destruct Hsplit_y as [m_y0 [m_y1 [Hsp_y [Hfe_y0 Hfe_y1]]]].
    destruct Hsp_y as [Heq_y Hd_y01].
    pose proof (Fp12_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o0 [m_o1 [Hsp_out [Hfe_o0 Hfe_o1]]]].
    destruct Hsp_out as [Heq_out Hd_o01].
    fp12_bounded_by_eq. destruct Hbx as [Hbx0 Hbx1]. destruct Hby as [Hby0 Hby1].
    subst m_x m_y m_out.
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
    (* Build master 10-way sep: x0, x1, y0, y1, o0, o1, Rr, v0, v1, t, u *)
    assert (Hsep10 :
      (FElem_Fp6 px (d0_felem x) ⋆
       (FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x) ⋆
        (FElem_Fp6 py (d0_felem y) ⋆
         (FElem_Fp6 (word.add py (word.of_Z fp6_felem_offset)) (d1_felem y) ⋆
          (FElem_Fp6 pout (d0_felem old_out) ⋆
           (FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) (d1_felem old_out) ⋆
            (Rr ⋆
             (FElem_Fp6 pv0 v0_val ⋆
              (FElem_Fp6 pv1 v1_val ⋆
               (FElem_Fp6 pt t_val ⋆ FElem_Fp6 pu u_val))))))))))
      (map.putmany m_x0 (map.putmany m_x1
        (map.putmany m_y0 (map.putmany m_y1
          (map.putmany m_o0 (map.putmany m_o1
            (map.putmany m_rr (map.putmany mStack_v0
              (map.putmany mStack_v1
                (map.putmany mStack_t mStack_u))))))))))).
    { build_sep. }
    (* Locals after all stackallocs *)
    set (lall := (#{ "out" => pout; "inx" => px; "iny" => py;
                     "v0" => pv0; "v1" => pv1; "t" => pt; "u" => pu }#)).
    (* === Call 1: v0 = mul(inx.c0, iny.c0) === *)
    exists [pv0; px; py]. split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul1 pv0 px py
           v0_val (d0_felem x) (d0_felem y) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_m1 m_m1 rets_m1 [Hrets_m1 [Htr_m1 [v0' [Hfeval_v0 [Hbound_v0 Hsep_m1]]]]].
    subst rets_m1. symmetry in Htr_m1. subst t_m1.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 2: v1 = mul(inx.c1, iny.c1) === *)
    exists [pv1; word.add px (word.of_Z fp6_felem_offset);
            word.add py (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul2 pv1
           (word.add px (word.of_Z fp6_felem_offset))
           (word.add py (word.of_Z fp6_felem_offset))
           v1_val (d1_felem x) (d1_felem y) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_m2 m_m2 rets_m2 [Hrets_m2 [Htr_m2 [v1' [Hfeval_v1 [Hbound_v1 Hsep_m2]]]]].
    subst rets_m2. symmetry in Htr_m2. subst t_m2.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 3: t = add(inx.c0, inx.c1) === *)
    exists [pt; px; word.add px (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 pt px
           (word.add px (word.of_Z fp6_felem_offset))
           t_val (d0_felem x) (d1_felem x) _ tr).
         wp_binop_precond solve_bounds. }
    intros t_a1 m_a1 rets_a1 [Hrets_a1 [Htr_a1 [t' [Hfeval_t [Hbound_t Hsep_a1]]]]].
    subst rets_a1. symmetry in Htr_a1. subst t_a1.
    cbv [map.putmany_of_list_zip].
    exists lall. split. { exact eq_refl. }
    repeat straightline.
    (* === Call 4: u = add(iny.c0, iny.c1) === *)
    exists [pu; py; word.add py (word.of_Z fp6_felem_offset)].
    split. { solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 pu py
           (word.add py (word.of_Z fp6_felem_offset))
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
       G = d0 x at px, H = d1 x at px+off,
       I = d0 y at py, J = d1 y at py+off, K = Rr
       + stack vars *)
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
    (* === Final postcondition === *)
    (* No ax/ay stack deallocation needed -- inputs are direct! *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out0' ++ out1').
    assert (Hd0_app : d0_felem (out0' ++ out1') = out0').
    { apply d0_felem_app. exact Hlen_C. }
    assert (Hd1_app : d1_felem (out0' ++ out1') = out1').
    { apply d1_felem_app. exact Hlen_C. }
    split.
    { (* feval *)
      fp12_feval_eq. rewrite Hd0_app, Hd1_app.
      rewrite Hfeval_out0, Hfeval_out1.
      rewrite Hfeval_t''.
      rewrite Hfeval_u'.
      rewrite Hfeval_t'.
      rewrite Hfeval_t, Hfeval_u.
      rewrite Hfeval_v0, Hfeval_v1.
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
    { (* sep: out result + preserved inputs + Rr *)
      assert (Hjoin_out : (FElem_Fp6 pout out0' ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset)) out1')
        (map.putmany m_C m_A)).
      { exists m_C, m_A.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HC | exact HA]. }
      pose proof (Fp12_raw_FElem_join pout out0' out1'
        (map.putmany m_C m_A) Hlen_C Hlen_A Hjoin_out) as Hfp12_out.
      (* Join inputs back to Fp12 *)
      assert (Hjoin_x : (FElem_Fp6 px (d0_felem x) ⋆
        FElem_Fp6 (word.add px (word.of_Z fp6_felem_offset)) (d1_felem x))
        (map.putmany m_G m_H)).
      { exists m_G, m_H.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HG | exact HH]. }
      pose proof (Fp12_raw_FElem_join px (d0_felem x) (d1_felem x)
        (map.putmany m_G m_H) Hlen_G Hlen_H Hjoin_x) as Hfp12_x.
      rewrite Fp12_list_decomp in Hfp12_x.
      assert (Hjoin_y : (FElem_Fp6 py (d0_felem y) ⋆
        FElem_Fp6 (word.add py (word.of_Z fp6_felem_offset)) (d1_felem y))
        (map.putmany m_I m_J)).
      { exists m_I, m_J.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact HI | exact HJ]. }
      pose proof (Fp12_raw_FElem_join py (d0_felem y) (d1_felem y)
        (map.putmany m_I m_J) Hlen_I Hlen_J Hjoin_y) as Hfp12_y.
      rewrite Fp12_list_decomp in Hfp12_y.
      (* Build final sep *)
      exists (map.putmany m_C m_A),
             (map.putmany (map.putmany m_G m_H)
               (map.putmany (map.putmany m_I m_J) m_K)).
      split; [split |].
      { solve_putmany_eq. }
      { map_disjoint_auto. }
      split; [exact Hfp12_out |].
      exists (map.putmany m_G m_H),
             (map.putmany (map.putmany m_I m_J) m_K).
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp12_x |].
      exists (map.putmany m_I m_J), m_K.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hfp12_y | exact HK]. }
  Qed.

End Fp12.
