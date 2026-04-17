(* Fp2_mul_ok proof — split from QuadraticFieldExtensions.v for fast iteration *)
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

Section Fp2_mul_proof.
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

  Local Notation F := (F M_pos).
  Local Notation Fp2 := ((F * F)%type).

  Existing Instance prime_field_parameters.

  Context {F_representation : AbstractField.FieldRepresentation (F:=F)}
          {F_representation_ok : AbstractField.FieldRepresentation_ok (F:=F)}.

  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  Variable beta : F.
  Hypothesis beta_nz : beta <> @F.zero M_pos.
  Hypothesis beta_qnr : ~(exists x, @F.mul M_pos x x = beta).
  Hypothesis M_big : 2 < Z.pos M_pos.
  Variable fp2_prefix : string.

  (* Bridge: β*y = -y (only true for β = -1).
     Each curve instantiation provides this or uses a different Fp2_mul body. *)
  Hypothesis mul_neg_1 : forall x y : F, F.sub x y = F.add x (F.mul beta y).

  Local Instance Fp2_fp : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters beta fp2_prefix.
  Local Instance Fp2_fp_ok : AbstractField.FieldParameters_ok (F:=Fp2) :=
    Fp2_field_parameters_ok beta beta_nz beta_qnr M_big fp2_prefix.
  Local Instance Fp2_repr : AbstractField.FieldRepresentation (F:=Fp2) :=
    @Fp2_field_representation width BW word mem prime_parameters F_representation beta fp2_prefix.
  Local Instance Fp2_repr_ok : AbstractField.FieldRepresentation_ok (F:=Fp2) :=
    @Fp2_field_representation_ok width BW word mem prime_parameters F_representation F_representation_ok beta fp2_prefix.

  Context {Fp2_names : FieldNames (F:=Fp2)}.
  Context {F_names : FieldNames (F:=F)}.

  Import Syntax BinInt String List.ListNotations.

  (* Automation tactics — Ltac inside Sections doesn't export across files *)
  Local Ltac saturate_disjointness :=
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      lazymatch goal with
      | _ : map.disjoint a b, _ : map.disjoint a c |- _ => fail
      | _ =>
        let H1 := fresh "Hd" in
        let H2 := fresh "Hd" in
        pose proof (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]
      end
    | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
      lazymatch goal with
      | _ : map.disjoint a c, _ : map.disjoint b c |- _ => fail
      | _ =>
        let H1 := fresh "Hd" in
        let H2 := fresh "Hd" in
        pose proof (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2]
      end
    end.

  Local Ltac map_disjoint_auto :=
    lazymatch goal with
    | |- map.disjoint ?a (map.putmany ?b ?c) =>
        apply (proj2 (map.disjoint_putmany_r a b c));
        split; [map_disjoint_auto | map_disjoint_auto]
    | |- map.disjoint (map.putmany ?a ?b) ?c =>
        apply (proj2 (map.disjoint_putmany_l a b c));
        split; [map_disjoint_auto | map_disjoint_auto]
    | |- map.disjoint ?a ?b =>
        first [ assumption
              | apply (proj1 (map.disjoint_comm _ _)); assumption
              | saturate_disjointness;
                first [ assumption
                      | apply (proj1 (map.disjoint_comm _ _)); assumption]]
    end.

  Local Notation felem_offset := (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=F))).

  Local Ltac solve_dexprs :=
    cbv [dexprs list_map expr_2nd_felem expr WeakestPrecondition.expr_body felem_offset];
    repeat (eexists; split; [
      repeat (first [apply map.get_put_same |
                     rewrite map.get_put_diff by (cbv; congruence)]) |]);
    exact eq_refl.

  (* WP goal macro — must be local per file (Definitions get generalized across Sections) *)
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

  (* F-level spec_of instances needed by callee_specs_ft *)
  Local Instance spec_of_F_mul : spec_of (AbstractField.mul (F:=F)) := AbstractField.binop_spec (F:=F) AbstractField.bin_mul.
  Local Instance spec_of_F_add : spec_of (AbstractField.add (F:=F)) := AbstractField.binop_spec (F:=F) AbstractField.bin_add.
  Local Instance spec_of_F_sub : spec_of (AbstractField.sub (F:=F)) := AbstractField.binop_spec (F:=F) AbstractField.bin_sub.

  Instance spec_of_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) := AbstractField.binop_spec AbstractField.bin_mul (F:=Fp2).

  Lemma Fp2_mul_ok : program_logic_goal_for_function! (Fp2_mul beta fp2_prefix).
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFmul1 HFmul2 HFadd1 HFadd2 HFmul3 HFsub1 HFsub2 HFsub3.
    unfold spec_of_F_mul, AbstractField.binop_spec in HFmul1.
    unfold spec_of_F_mul, AbstractField.binop_spec in HFmul2.
    unfold spec_of_F_mul, AbstractField.binop_spec in HFmul3.
    unfold spec_of_F_add, AbstractField.binop_spec in HFadd1.
    unfold spec_of_F_add, AbstractField.binop_spec in HFadd2.
    unfold spec_of_F_sub, AbstractField.binop_spec in HFsub1.
    unfold spec_of_F_sub, AbstractField.binop_spec in HFsub2.
    unfold spec_of_F_sub, AbstractField.binop_spec in HFsub3.
    unfold spec_of_Fp2_mul, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp2_mul].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === stackalloc v0 === *)
    split. { apply Z_mod_mult. }
    intros v0_addr mSV0 mv0 HstackV0 Hmv0.
    repeat straightline.
    (* === stackalloc v1 === *)
    split. { apply Z_mod_mult. }
    intros v1_addr mSV1 mv1 HstackV1 Hmv1.
    repeat straightline.
    (* === stackalloc v2 === *)
    split. { apply Z_mod_mult. }
    intros v2_addr mSV2 mv2 HstackV2 Hmv2.
    (* Convert anybytes to FElems *)
    pose proof (@AbstractField.FElem_from_bytes _ _ _ _ _ _
      F_representation word_ok mem_ok v0_addr) as Hfb0.
    pose proof (@AbstractField.FElem_from_bytes _ _ _ _ _ _
      F_representation word_ok mem_ok v1_addr) as Hfb1.
    pose proof (@AbstractField.FElem_from_bytes _ _ _ _ _ _
      F_representation word_ok mem_ok v2_addr) as Hfb2.
    unfold AbstractField.Placeholder in Hfb0, Hfb1, Hfb2.
    pose proof (proj1 (Hfb0 mSV0) HstackV0) as [v0_val Hv0]. clear Hfb0.
    pose proof (proj1 (Hfb1 mSV1) HstackV1) as [v1_val Hv1]. clear Hfb1.
    pose proof (proj1 (Hfb2 mSV2) HstackV2) as [v2_val Hv2]. clear Hfb2.
    clear HstackV0 HstackV1 HstackV2.
    destruct Hmv0 as [Heq_mv0 Hd_mv0]. subst mv0.
    destruct Hmv1 as [Heq_mv1 Hd_mv1]. subst mv1.
    destruct Hmv2 as [Heq_mv2 Hd_mv2]. subst mv2.
    (* Decompose output/x/y sep *)
    destruct Hmemout as [m_out [m_rr [Hmemout_sp [Hfelem_out Hrr]]]].
    destruct Hmemout_sp as [Heq_mem0 Hd_out_rr]. subst mem0.
    pose proof (Fp2_raw_FElem_split beta fp2_prefix pout old_out m_out Hfelem_out) as [m_o1 [m_o2 [Hsp_out [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_out as [Heq_out Hd_o12]. clear Hfelem_out. subst m_out.
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfelem_x Hrx]]]].
    destruct Hmemx_sp as [Heq_memx Hd_xrx].
    pose proof (Fp2_raw_FElem_split beta fp2_prefix px x m_x Hfelem_x) as [m_x1 [m_x2 [Hsp_x [Hfe_x1 Hfe_x2]]]].
    destruct Hsp_x as [Heq_x Hd_x12]. clear Hfelem_x. subst m_x.
    destruct Hmemy as [m_y [m_ry [Hmemy_sp [Hfelem_y Hry]]]].
    destruct Hmemy_sp as [Heq_memy Hd_yry].
    pose proof (Fp2_raw_FElem_split beta fp2_prefix py y m_y Hfelem_y) as [m_y1 [m_y2 [Hsp_y [Hfe_y1 Hfe_y2]]]].
    destruct Hsp_y as [Heq_y Hd_y12]. clear Hfelem_y. subst m_y.
    (* Decompose bounded_by *)
    cbv [AbstractField.bounded_by Fp2_repr Fp2_field_representation
         AbstractField.bin_xbounds AbstractField.bin_ybounds
         AbstractField.bin_mul fst snd] in Hbx, Hby.
    destruct Hbx as [Hbx_re Hbx_im]. destruct Hby as [Hby_re Hby_im].
    (* --- Minimal disjointness: only decompose simple composites --- *)
    pose proof (proj1 (map.disjoint_putmany_l m_o1 m_o2 m_rr) Hd_out_rr) as [Hd_o1rr Hd_o2rr].
    pose proof (proj1 (map.disjoint_putmany_l m_x1 m_x2 m_rx) Hd_xrx) as [Hd_x1rx Hd_x2rx].
    pose proof (proj1 (map.disjoint_putmany_l m_y1 m_y2 m_ry) Hd_yry) as [Hd_y1ry Hd_y2ry].
    clear Hd_out_rr Hd_xrx Hd_yry.
    (* Saturate only Hd_mv0/1/2 (out-based chain) *)
    saturate_disjointness.
    clear Hd_mv0 Hd_mv1 Hd_mv2.
    (* Derive x-side and y-side vs stack-vars disjointness *)
    assert (Hd_xsv : map.disjoint (map.putmany (map.putmany m_x1 m_x2) m_rx)
                                    (map.putmany mSV0 (map.putmany mSV1 mSV2)))
      by (rewrite <- Heq_memx; map_disjoint_auto).
    assert (Hd_ysv : map.disjoint (map.putmany (map.putmany m_y1 m_y2) m_ry)
                                    (map.putmany mSV0 (map.putmany mSV1 mSV2)))
      by (rewrite <- Heq_memy; map_disjoint_auto).
    saturate_disjointness.
    clear Hd_xsv Hd_ysv.
    (* ============ Call 1: F.mul(v0, inx, iny) — v0 := a*c ============ *)
    straightline. straightline.
    exists [v0_addr; px; py]. split.
    1: { subst l1 l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul1 v0_addr px py v0_val (fst_felem x) (fst_felem y) _ tr).
         split; [exact Hbx_re |].
         split; [exact Hby_re |].
         split.
         { (* x.re sep: FElem px (fst_felem x) in mem *)
           exists (eq (map.putmany m_x2 (map.putmany m_rx (map.putmany mSV0 (map.putmany mSV1 mSV2))))).
           exists m_x1.
           exists (map.putmany m_x2 (map.putmany m_rx (map.putmany mSV0 (map.putmany mSV1 mSV2)))).
           split; [split |].
           { rewrite Heq_memx. rewrite !map.putmany_assoc. reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_x1 | exact eq_refl]. }
         split.
         { (* y.re sep: FElem py (fst_felem y) in mem *)
           exists (eq (map.putmany m_y2 (map.putmany m_ry (map.putmany mSV0 (map.putmany mSV1 mSV2))))).
           exists m_y1.
           exists (map.putmany m_y2 (map.putmany m_ry (map.putmany mSV0 (map.putmany mSV1 mSV2)))).
           split; [split |].
           { rewrite Heq_memy. rewrite !map.putmany_assoc. reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_y1 | exact eq_refl]. }
         (* output v0 sep: FElem v0_addr v0_val in mem *)
         { unfold Separation.sep.
           exists mSV0.
           exists (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr (map.putmany mSV1 mSV2)))).
           split; [split |].
           { (* equality: rearrange left-assoc mem to putmany mSV0 rest *)
             rewrite <- !map.putmany_assoc.
             rewrite (map.putmany_assoc m_rr mSV0).
             rewrite (map.putmany_comm m_rr mSV0 Hd14).
             rewrite <- (map.putmany_assoc mSV0 m_rr).
             rewrite (map.putmany_assoc m_o2 mSV0).
             rewrite (map.putmany_comm m_o2 mSV0 Hd16).
             rewrite <- (map.putmany_assoc mSV0 m_o2).
             rewrite (map.putmany_assoc m_o1 mSV0).
             rewrite (map.putmany_comm m_o1 mSV0 Hd15).
             rewrite <- (map.putmany_assoc mSV0 m_o1).
             reflexivity. }
           { apply (proj2 (map.disjoint_putmany_r _ _ _)); split;
               [apply (proj1 (map.disjoint_comm _ _)); exact Hd15 |].
             apply (proj2 (map.disjoint_putmany_r _ _ _)); split;
               [apply (proj1 (map.disjoint_comm _ _)); exact Hd16 |].
             apply (proj2 (map.disjoint_putmany_r _ _ _)); split;
               [apply (proj1 (map.disjoint_comm _ _)); exact Hd14 |].
             apply (proj2 (map.disjoint_putmany_r _ _ _)); split;
               [exact Hd8 | exact Hd2]. }
           split; [exact Hv0 | exact eq_refl]. } }
    (* ============ Call 1 → Call 2 transition ============ *)
    intros t1 m1 rets1 [Hrets1 [Htr1 [v0_new [Hfeval_v0 [Hbounds_v0 Hsep_v0]]]]].
    subst rets1. subst t1.
    exists l1. split. { reflexivity. }
    repeat straightline.
    (* Decompose Call 1 postcondition sep *)
    destruct Hsep_v0 as [mSV0' [mframe_v0 [[Heq_m1 Hd_v0f] [Hfe_v0' Heq_fv0]]]].
    subst mframe_v0. subst m1.
    (* Helper: rewrite frame from o-basis to x-basis or y-basis *)
    assert (Heq_o2x : forall Z, map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr Z))
                               = map.putmany m_x1 (map.putmany m_x2 (map.putmany m_rx Z))).
    { intro Z. rewrite (map.putmany_assoc m_o1 m_o2).
      rewrite (map.putmany_assoc (map.putmany m_o1 m_o2) m_rr).
      rewrite Heq_memx.
      rewrite <- (map.putmany_assoc (map.putmany m_x1 m_x2) m_rx).
      rewrite <- (map.putmany_assoc m_x1 m_x2). reflexivity. }
    assert (Heq_o2y : forall Z, map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr Z))
                               = map.putmany m_y1 (map.putmany m_y2 (map.putmany m_ry Z))).
    { intro Z. rewrite (map.putmany_assoc m_o1 m_o2).
      rewrite (map.putmany_assoc (map.putmany m_o1 m_o2) m_rr).
      rewrite Heq_memy.
      rewrite <- (map.putmany_assoc (map.putmany m_y1 m_y2) m_ry).
      rewrite <- (map.putmany_assoc m_y1 m_y2). reflexivity. }
    (* Saturate mSV0' disjointness *)
    saturate_disjointness.
    assert (Hd_v0x : map.disjoint mSV0'
      (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_rx (map.putmany mSV1 mSV2)))))
      by (rewrite <- Heq_o2x; assumption).
    assert (Hd_v0y : map.disjoint mSV0'
      (map.putmany m_y1 (map.putmany m_y2 (map.putmany m_ry (map.putmany mSV1 mSV2)))))
      by (rewrite <- Heq_o2y; assumption).
    saturate_disjointness.
    (* ============ Call 2: F.mul(v1, inx.im, iny.im) — v1 := b*d ============ *)
    exists [v1_addr; word.add px (word.of_Z felem_offset); word.add py (word.of_Z felem_offset)].
    split. 1: { subst l1 l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul2 v1_addr (word.add px (word.of_Z felem_offset))
                  (word.add py (word.of_Z felem_offset))
                  v1_val (snd_felem x) (snd_felem y) _ tr).
         split; [exact Hbx_im |].
         split; [exact Hby_im |].
         split.
         { (* x.im sep *)
           exists (eq (map.putmany mSV0' (map.putmany m_x1 (map.putmany m_rx (map.putmany mSV1 mSV2))))).
           exists m_x2.
           exists (map.putmany mSV0' (map.putmany m_x1 (map.putmany m_rx (map.putmany mSV1 mSV2)))).
           split; [split |].
           { rewrite (Heq_o2x (map.putmany mSV1 mSV2)).
             rewrite (putmany_swap m_x1 m_x2 _ Hd_x12).
             rewrite (putmany_swap mSV0' m_x2 _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_x2 | exact eq_refl]. }
         split.
         { (* y.im sep *)
           exists (eq (map.putmany mSV0' (map.putmany m_y1 (map.putmany m_ry (map.putmany mSV1 mSV2))))).
           exists m_y2.
           exists (map.putmany mSV0' (map.putmany m_y1 (map.putmany m_ry (map.putmany mSV1 mSV2)))).
           split; [split |].
           { rewrite (Heq_o2y (map.putmany mSV1 mSV2)).
             rewrite (putmany_swap m_y1 m_y2 _ Hd_y12).
             rewrite (putmany_swap mSV0' m_y2 _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_y2 | exact eq_refl]. }
         (* v1 output sep *)
         { unfold Separation.sep.
           exists mSV1.
           exists (map.putmany mSV0' (map.putmany m_o1 (map.putmany m_o2 (map.putmany m_rr mSV2)))).
           split; [split |].
           { (* bubble mSV1 to front through 4 swaps *)
             rewrite (putmany_swap m_rr mSV1 mSV2 Hd10).
             rewrite (putmany_swap m_o2 mSV1 _ Hd12).
             rewrite (putmany_swap m_o1 mSV1 _ Hd11).
             rewrite (putmany_swap mSV0' mSV1 _ Hd71).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hv1 | exact eq_refl]. } }
    (* ============ Call 2 → Call 3 transition ============ *)
    intros t2 m2 rets2 [Hrets2 [Htr2 [v1_new [Hfeval_v1 [Hbounds_v1 Hsep_v1]]]]].
    subst rets2. subst t2.
    exists l1. split. { reflexivity. }
    repeat straightline.
    (* Decompose Call 2 postcondition sep *)
    destruct Hsep_v1 as [mSV1' [mframe_v1 [[Heq_m2 Hd_v1f] [Hfe_v1' Heq_fv1]]]].
    subst mframe_v1. subst m2.
    (* Saturate mSV1' disjointness *)
    saturate_disjointness.
    assert (Hd_v1x' : map.disjoint mSV1'
      (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_rx mSV2))))
      by (rewrite <- Heq_o2x; assumption).
    assert (Hd_v1y' : map.disjoint mSV1'
      (map.putmany m_y1 (map.putmany m_y2 (map.putmany m_ry mSV2))))
      by (rewrite <- Heq_o2y; assumption).
    saturate_disjointness.
    (* ============ Call 3: F.add(v2, inx, inx.im) — v2 := a+b ============ *)
    exists [v2_addr; px; word.add px (word.of_Z felem_offset)].
    split. 1: { subst l1 l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 v2_addr px (word.add px (word.of_Z felem_offset))
                  v2_val (fst_felem x) (snd_felem x) _ tr).
         split; [exact (bounds_equiv _ Hbx_re) |].
         split; [exact (bounds_equiv _ Hbx_im) |].
         split.
         { (* x.re sep *)
           exists (eq (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_x2 (map.putmany m_rx mSV2))))).
           exists m_x1.
           exists (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_x2 (map.putmany m_rx mSV2)))).
           split; [split |].
           { rewrite (Heq_o2x mSV2).
             rewrite (putmany_swap mSV0' m_x1 _ ltac:(assumption)).
             rewrite (putmany_swap mSV1' m_x1 _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_x1 | exact eq_refl]. }
         split.
         { (* x.im sep *)
           exists (eq (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_x1 (map.putmany m_rx mSV2))))).
           exists m_x2.
           exists (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_x1 (map.putmany m_rx mSV2)))).
           split; [split |].
           { rewrite (Heq_o2x mSV2).
             rewrite (putmany_swap m_x1 m_x2 _ Hd_x12).
             rewrite (putmany_swap mSV0' m_x2 _ ltac:(assumption)).
             rewrite (putmany_swap mSV1' m_x2 _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_x2 | exact eq_refl]. }
         (* v2 output sep *)
         { unfold Separation.sep.
           exists mSV2.
           exists (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 (map.putmany m_o2 m_rr)))).
           split; [split |].
           { rewrite (map.putmany_comm m_rr mSV2 ltac:(assumption)).
             rewrite (putmany_swap m_o2 mSV2 _ ltac:(assumption)).
             rewrite (putmany_swap m_o1 mSV2 _ ltac:(assumption)).
             rewrite (putmany_swap mSV0' mSV2 _ ltac:(assumption)).
             rewrite (putmany_swap mSV1' mSV2 _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hv2 | exact eq_refl]. } }
    (* ============ Call 3 → Call 4 transition ============ *)
    intros t3 m3 rets3 [Hrets3 [Htr3 [v2_new [Hfeval_v2 [Hbounds_v2 Hsep_v2]]]]].
    subst rets3. subst t3.
    exists l1. split. { reflexivity. }
    repeat straightline.
    destruct Hsep_v2 as [mSV2' [mframe_v2 [[Heq_m3 Hd_v2f] [Hfe_v2' Heq_fv2]]]].
    subst mframe_v2. subst m3.
    (* o-basis to y-basis without trailing Z *)
    assert (Heq_o2y' : map.putmany m_o1 (map.putmany m_o2 m_rr)
                       = map.putmany m_y1 (map.putmany m_y2 m_ry)).
    { rewrite map.putmany_assoc, Heq_memy, <- map.putmany_assoc. reflexivity. }
    saturate_disjointness.
    assert (Hd_v2y : map.disjoint mSV2' (map.putmany m_y1 (map.putmany m_y2 m_ry)))
      by (rewrite <- Heq_o2y'; assumption).
    saturate_disjointness.
    (* ============ Call 4: F.add(out.im, iny, iny.im) — out.im := c+d ============ *)
    exists [word.add pout (word.of_Z felem_offset); py; word.add py (word.of_Z felem_offset)].
    split. 1: { subst l1 l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd2 (word.add pout (word.of_Z felem_offset)) py
                  (word.add py (word.of_Z felem_offset))
                  (snd_felem old_out) (fst_felem y) (snd_felem y) _ tr).
         split; [exact (bounds_equiv _ Hby_re) |].
         split; [exact (bounds_equiv _ Hby_im) |].
         split.
         { (* y.re sep *)
           exists (eq (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_y2 m_ry))))).
           exists m_y1.
           exists (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_y2 m_ry)))).
           split; [split |].
           { rewrite Heq_o2y'.
             rewrite (putmany_swap mSV0' m_y1 _ ltac:(assumption)).
             rewrite (putmany_swap mSV1' m_y1 _ ltac:(assumption)).
             rewrite (putmany_swap mSV2' m_y1 _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_y1 | exact eq_refl]. }
         split.
         { (* y.im sep *)
           exists (eq (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_y1 m_ry))))).
           exists m_y2.
           exists (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_y1 m_ry)))).
           split; [split |].
           { rewrite Heq_o2y'.
             rewrite (putmany_swap m_y1 m_y2 _ Hd_y12).
             rewrite (putmany_swap mSV0' m_y2 _ ltac:(assumption)).
             rewrite (putmany_swap mSV1' m_y2 _ ltac:(assumption)).
             rewrite (putmany_swap mSV2' m_y2 _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_y2 | exact eq_refl]. }
         (* out.im output sep *)
         { unfold Separation.sep.
           exists m_o2.
           exists (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { rewrite (putmany_swap m_o1 m_o2 _ Hd_o12).
             rewrite (putmany_swap mSV0' m_o2 _ ltac:(assumption)).
             rewrite (putmany_swap mSV1' m_o2 _ ltac:(assumption)).
             rewrite (putmany_swap mSV2' m_o2 _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_o2 | exact eq_refl]. } }
    (* ============ Call 4 → Call 5 transition ============ *)
    intros t4 m4 rets4 [Hrets4 [Htr4 [out_im_1 [Hfeval_oi1 [Hbounds_oi1 Hsep_oi1]]]]].
    subst rets4. subst t4.
    exists l1. split. { reflexivity. }
    repeat straightline.
    destruct Hsep_oi1 as [m_o2' [mframe_oi1 [[Heq_m4 Hd_oi1f] [Hfe_oi1 Heq_foi1]]]].
    subst mframe_oi1. subst m4.
    saturate_disjointness.
    (* ============ Call 5: F.mul(out.im, out.im, v2) — out.im := (c+d)(a+b) ============ *)
    exists [word.add pout (word.of_Z felem_offset); word.add pout (word.of_Z felem_offset); v2_addr].
    split. 1: { subst l1 l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFmul3 (word.add pout (word.of_Z felem_offset))
                  (word.add pout (word.of_Z felem_offset)) v2_addr
                  out_im_1 out_im_1 v2_new _ tr).
         split; [exact Hbounds_oi1 |].
         split; [exact Hbounds_v2 |].
         split.
         { (* out.im as input x — m_o2' is already first *)
           exists (eq (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr))))).
           exists m_o2'.
           exists (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { reflexivity. }
           { exact Hd_oi1f. }
           split; [exact Hfe_oi1 | exact eq_refl]. }
         split.
         { (* v2 as input y *)
           exists (eq (map.putmany m_o2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr))))).
           exists mSV2'.
           exists (map.putmany m_o2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { rewrite (putmany_swap m_o2' mSV2' _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_v2' | exact eq_refl]. }
         (* out.im output sep — same as input x *)
         { unfold Separation.sep.
           exists m_o2'.
           exists (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { reflexivity. }
           { exact Hd_oi1f. }
           split; [exact Hfe_oi1 | exact eq_refl]. } }
    (* ============ Call 5 → Call 6 transition ============ *)
    intros t5 m5 rets5 [Hrets5 [Htr5 [out_im_2 [Hfeval_oi2 [Hbounds_oi2 Hsep_oi2]]]]].
    subst rets5. subst t5.
    exists l1. split. { reflexivity. }
    repeat straightline.
    destruct Hsep_oi2 as [m_oi2 [mframe_oi2 [[Heq_m5 Hd_oi2f] [Hfe_oi2 Heq_foi2]]]].
    subst mframe_oi2. subst m5.
    saturate_disjointness.
    (* ============ Call 6: F.sub(out.im, out.im, v0) — out.im -= ac ============ *)
    exists [word.add pout (word.of_Z felem_offset); word.add pout (word.of_Z felem_offset); v0_addr].
    split. 1: { subst l1 l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 (word.add pout (word.of_Z felem_offset))
                  (word.add pout (word.of_Z felem_offset)) v0_addr
                  out_im_2 out_im_2 v0_new _ tr).
         split; [exact Hbounds_oi2 |].
         split; [exact Hbounds_v0 |].
         split.
         { (* out.im as input x — m_oi2 is already first *)
           exists (eq (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr))))).
           exists m_oi2.
           exists (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { reflexivity. }
           { exact Hd_oi2f. }
           split; [exact Hfe_oi2 | exact eq_refl]. }
         split.
         { (* v0 as input y *)
           exists (eq (map.putmany m_oi2 (map.putmany mSV2' (map.putmany mSV1' (map.putmany m_o1 m_rr))))).
           exists mSV0'.
           exists (map.putmany m_oi2 (map.putmany mSV2' (map.putmany mSV1' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { rewrite (putmany_swap mSV1' mSV0' _ ltac:(assumption)).
             rewrite (putmany_swap mSV2' mSV0' _ ltac:(assumption)).
             rewrite (putmany_swap m_oi2 mSV0' _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_v0' | exact eq_refl]. }
         (* out.im output sep *)
         { unfold Separation.sep.
           exists m_oi2.
           exists (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { reflexivity. }
           { exact Hd_oi2f. }
           split; [exact Hfe_oi2 | exact eq_refl]. } }
    (* ============ Call 6 → Call 7 transition ============ *)
    intros t6 m6 rets6 [Hrets6 [Htr6 [out_im_3 [Hfeval_oi3 [Hbounds_oi3 Hsep_oi3]]]]].
    subst rets6. subst t6.
    exists l1. split. { reflexivity. }
    repeat straightline.
    destruct Hsep_oi3 as [m_oi3 [mframe_oi3 [[Heq_m6 Hd_oi3f] [Hfe_oi3 Heq_foi3]]]].
    subst mframe_oi3. subst m6.
    saturate_disjointness.
    (* ============ Call 7: F.sub(out.im, out.im, v1) — out.im -= bd ============ *)
    exists [word.add pout (word.of_Z felem_offset); word.add pout (word.of_Z felem_offset); v1_addr].
    split. 1: { subst l1 l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub2 (word.add pout (word.of_Z felem_offset))
                  (word.add pout (word.of_Z felem_offset)) v1_addr
                  out_im_3 out_im_3 v1_new _ tr).
         split; [exact (bounds_equiv _ Hbounds_oi3) |].
         split; [exact Hbounds_v1 |].
         split.
         { (* out.im as input x *)
           exists (eq (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr))))).
           exists m_oi3.
           exists (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { reflexivity. }
           { exact Hd_oi3f. }
           split; [exact Hfe_oi3 | exact eq_refl]. }
         split.
         { (* v1 as input y *)
           exists (eq (map.putmany m_oi3 (map.putmany mSV2' (map.putmany mSV0' (map.putmany m_o1 m_rr))))).
           exists mSV1'.
           exists (map.putmany m_oi3 (map.putmany mSV2' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { rewrite (putmany_swap mSV2' mSV1' _ ltac:(assumption)).
             rewrite (putmany_swap m_oi3 mSV1' _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_v1' | exact eq_refl]. }
         (* out.im output sep *)
         { unfold Separation.sep.
           exists m_oi3.
           exists (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { reflexivity. }
           { exact Hd_oi3f. }
           split; [exact Hfe_oi3 | exact eq_refl]. } }
    (* ============ Call 7 → Call 8 transition ============ *)
    intros t7 m7 rets7 [Hrets7 [Htr7 [out_im_4 [Hfeval_oi4 [Hbounds_oi4 Hsep_oi4]]]]].
    subst rets7. subst t7.
    exists l1. split. { reflexivity. }
    repeat straightline.
    destruct Hsep_oi4 as [m_oi4 [mframe_oi4 [[Heq_m7 Hd_oi4f] [Hfe_oi4 Heq_foi4]]]].
    subst mframe_oi4. subst m7.
    saturate_disjointness.
    (* ============ Call 8: F.sub(out, v0, v1) — out.re := ac - bd ============ *)
    exists [pout; v0_addr; v1_addr].
    split. 1: { subst l1 l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub3 pout v0_addr v1_addr
                  (fst_felem old_out) v0_new v1_new _ tr).
         split; [exact Hbounds_v0 |].
         split; [exact Hbounds_v1 |].
         split.
         { (* v0 as input x *)
           exists (eq (map.putmany m_oi4 (map.putmany mSV2' (map.putmany mSV1' (map.putmany m_o1 m_rr))))).
           exists mSV0'.
           exists (map.putmany m_oi4 (map.putmany mSV2' (map.putmany mSV1' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { rewrite (putmany_swap mSV1' mSV0' _ ltac:(assumption)).
             rewrite (putmany_swap mSV2' mSV0' _ ltac:(assumption)).
             rewrite (putmany_swap m_oi4 mSV0' _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_v0' | exact eq_refl]. }
         split.
         { (* v1 as input y *)
           exists (eq (map.putmany m_oi4 (map.putmany mSV2' (map.putmany mSV0' (map.putmany m_o1 m_rr))))).
           exists mSV1'.
           exists (map.putmany m_oi4 (map.putmany mSV2' (map.putmany mSV0' (map.putmany m_o1 m_rr)))).
           split; [split |].
           { rewrite (putmany_swap mSV2' mSV1' _ ltac:(assumption)).
             rewrite (putmany_swap m_oi4 mSV1' _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_v1' | exact eq_refl]. }
         (* out.re output sep *)
         { unfold Separation.sep.
           exists m_o1.
           exists (map.putmany m_oi4 (map.putmany mSV2' (map.putmany mSV1' (map.putmany mSV0' m_rr)))).
           split; [split |].
           { rewrite (putmany_swap mSV0' m_o1 _ ltac:(assumption)).
             rewrite (putmany_swap mSV1' m_o1 _ ltac:(assumption)).
             rewrite (putmany_swap mSV2' m_o1 _ ltac:(assumption)).
             rewrite (putmany_swap m_oi4 m_o1 _ ltac:(assumption)).
             reflexivity. }
           { map_disjoint_auto. }
           split; [exact Hfe_o1 | exact eq_refl]. } }
    (* ============ Final postcondition ============ *)
    intros t8 m8 rets8 [Hrets8 [Htr8 [out_re [Hfeval_re [Hbounds_re Hsep_re]]]]].
    subst rets8. subst t8.
    exists l1. split. { reflexivity. }
    destruct Hsep_re as [m_o1' [mframe_re [[Heq_m8 Hd_ref] [Hfe_re Heq_fre]]]].
    subst mframe_re. subst m8.
    saturate_disjointness.
    (* Convert stack FElems to anybytes *)
    pose proof (AbstractField.FElem_to_bytes v2_addr v2_new mSV2' Hfe_v2') as Hab_v2.
    pose proof (AbstractField.FElem_to_bytes v1_addr v1_new mSV1' Hfe_v1') as Hab_v1.
    pose proof (AbstractField.FElem_to_bytes v0_addr v0_new mSV0' Hfe_v0') as Hab_v0.
    unfold AbstractField.Placeholder in Hab_v2, Hab_v1, Hab_v0.
    (* ---- Stackdealloc v2 ---- *)
    exists (map.putmany m_o1' (map.putmany m_oi4 (map.putmany mSV1' (map.putmany mSV0' m_rr)))).
    exists mSV2'.
    split. { exact Hab_v2. }
    split.
    { split.
      { rewrite (putmany_swap m_oi4 mSV2' _ ltac:(assumption)).
        rewrite (putmany_swap m_o1' mSV2' _ ltac:(assumption)).
        assert (Hdc2 : map.disjoint mSV2' (map.putmany m_o1' (map.putmany m_oi4 (map.putmany mSV1' (map.putmany mSV0' m_rr))))) by map_disjoint_auto.
        rewrite (map.putmany_comm _ _ Hdc2).
        reflexivity. }
      { apply (proj1 (map.disjoint_comm _ _)). map_disjoint_auto. } }
    (* ---- Stackdealloc v1 ---- *)
    exists (map.putmany m_o1' (map.putmany m_oi4 (map.putmany mSV0' m_rr))).
    exists mSV1'.
    split. { exact Hab_v1. }
    split.
    { split.
      { rewrite (putmany_swap m_oi4 mSV1' _ ltac:(assumption)).
        rewrite (putmany_swap m_o1' mSV1' _ ltac:(assumption)).
        assert (Hdc1 : map.disjoint mSV1' (map.putmany m_o1' (map.putmany m_oi4 (map.putmany mSV0' m_rr)))) by map_disjoint_auto.
        rewrite (map.putmany_comm _ _ Hdc1).
        reflexivity. }
      { apply (proj1 (map.disjoint_comm _ _)). map_disjoint_auto. } }
    (* ---- Stackdealloc v0 ---- *)
    exists (map.putmany m_o1' (map.putmany m_oi4 m_rr)).
    exists mSV0'.
    split. { exact Hab_v0. }
    split.
    { split.
      { rewrite (putmany_swap m_oi4 mSV0' _ ltac:(assumption)).
        rewrite (putmany_swap m_o1' mSV0' _ ltac:(assumption)).
        assert (Hdc0 : map.disjoint mSV0' (map.putmany m_o1' (map.putmany m_oi4 m_rr))) by map_disjoint_auto.
        rewrite (map.putmany_comm _ _ Hdc0).
        reflexivity. }
      { apply (proj1 (map.disjoint_comm _ _)). map_disjoint_auto. } }
    (* ---- Final result ---- *)
    cbv beta delta [WeakestPrecondition.list_map WeakestPrecondition.get].
    cbv beta.
    split. { reflexivity. }
    split. { reflexivity. }
    exists (out_re ++ out_im_4).
    split.
    { (* feval: Fp2 mul correctness — Karatsuba identity *)
      pose proof (AbstractFElem_length _ _ _ Hfe_re) as Hlen_re.
      unfold Fp2_repr, Fp2_field_representation, Fp2_fp, Fp2_field_parameters.
      cbn [feval bin_model bin_mul Fmul].
      unfold fst_felem, snd_felem.
      rewrite (firstn_app' _ _ _ Hlen_re).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_re).
      unfold mulp2.
      cbn [fst snd].
      rewrite Hfeval_re, Hfeval_oi4, Hfeval_oi3, Hfeval_oi2, Hfeval_oi1, Hfeval_v2.
      rewrite Hfeval_v0, Hfeval_v1.
      unfold fst_felem, snd_felem.
      cbv [bin_model bin_mul bin_add bin_sub Fmul Fadd Fsub prime_field_parameters].
      f_equal.
      { (* real part: a*c + (β*b)*d = a*c - b*d *)
        symmetry. rewrite (F_mul_assoc M_pos M_prime).
        rewrite mul_neg_1. reflexivity. }
      { (* im part: (c+d)*(a+b) - a*c - b*d = a*d + b*c *)
        apply (mul_equiv M_pos M_prime). } }
    split.
    { (* bounded_by — Fp2-level bounds from F-level bounds *)
      pose proof (AbstractFElem_length _ _ _ Hfe_re) as Hlen_re.
      unfold Fp2_repr, Fp2_field_representation.
      cbn [bounded_by bin_outbounds bin_mul tight_bounds].
      unfold fst_felem, snd_felem.
      rewrite (firstn_app' _ _ _ Hlen_re).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_re).
      split; apply bounds_equiv; assumption. }
    (* Fp2 FElem sep *)
    exists (map.putmany m_o1' m_oi4). exists m_rr.
    split; [split |].
    { rewrite map.putmany_assoc. reflexivity. }
    { apply (proj2 (map.disjoint_putmany_l _ _ _)). split; assumption. }
    split.
    { apply (Fp2_raw_FElem_join beta fp2_prefix pout out_re out_im_4).
      { exact (AbstractFElem_length _ _ _ Hfe_re). }
      { exact (AbstractFElem_length _ _ _ Hfe_oi4). }
      { exists m_o1'. exists m_oi4.
        split; [split |].
        { reflexivity. }
        { assumption. }
        split; [exact Hfe_re | exact Hfe_oi4]. } }
    { exact Hrr. }
  Qed.

End Fp2_mul_proof.
