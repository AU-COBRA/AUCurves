(** * WP correctness proofs for generic cubic extension functions. *)

Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.

Import Separation SeparationLogic.

Section GenericCubicProofs.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {BaseField : Type} {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable mul_by_nr_model : BaseField -> BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Notation CE := (BaseField * BaseField * BaseField)%type.

  Local Instance CE_fp : FieldParameters CE :=
    CE_field_parameters mul_by_nr_model prefix eq_dec_base.
  Local Instance CE_repr : @FieldRepresentation _ CE_fp width BW word mem :=
    CE_field_representation mul_by_nr_model prefix eq_dec_base.

  Local Notation FElem_b := (@FElem _ base_fp _ _ _ _ base_repr).
  Local Notation c0_e := (@ce_c0_felem _ _ _ _ _ base_fp base_repr).
  Local Notation c1_e := (@ce_c1_felem _ _ _ _ _ base_fp base_repr).
  Local Notation c2_e := (@ce_c2_felem _ _ _ _ _ base_fp base_repr).
  Local Notation base_off := (word.of_Z (Memory.bytes_per_word width *
    Z.of_nat (@felem_size_in_words _ base_fp _ _ _ _ base_repr))).
  Local Notation base_off2 := (word.of_Z (2 * (Memory.bytes_per_word width *
    Z.of_nat (@felem_size_in_words _ base_fp _ _ _ _ base_repr)))).

  Context {CE_names : FieldNames (F := CE)} {base_names : FieldNames (F := BaseField)}.
  Variable mul_by_nr_name : string.
  Variable Mul_by_nr_func : string * (list String.string * list String.string * Syntax.cmd.cmd).
  Hypothesis Mul_by_nr_name_eq : fst Mul_by_nr_func = mul_by_nr_name.

  (* Helper: solve dexprs for ce_expr_c0/c1/c2 *)
  Local Ltac solve_ce_dexprs :=
    first [ solve_dexprs
          | unfold ce_expr_c1, ce_expr_c2;
            cbv [dexprs list_map list_map_body WeakestPrecondition.expr
                 WeakestPrecondition.expr_body Semantics.interp_binop literal dlet.dlet];
            repeat (eexists; split; [first [apply map.get_put_same |
              rewrite map.get_put_diff by congruence; apply map.get_put_same |
              rewrite map.get_put_diff by congruence;
              rewrite map.get_put_diff by congruence; apply map.get_put_same] |]);
            try exact eq_refl ].

  (* Helper lemma: ce_c1_felem on concatenation *)
  Local Lemma c1_app_app (a b c : list word) :
    length a = @felem_size_in_words _ base_fp _ _ _ _ base_repr ->
    length b = @felem_size_in_words _ base_fp _ _ _ _ base_repr ->
    c1_e (a ++ b ++ c) = b.
  Proof.
    intros Ha Hb. unfold ce_c1_felem.
    rewrite skipn_app_le by exact Ha.
    rewrite firstn_app_le by exact Hb. reflexivity.
  Qed.

  (* Helper lemma: ce_c2_felem on concatenation *)
  Local Lemma c2_app_app (a b c : list word) :
    length a = @felem_size_in_words _ base_fp _ _ _ _ base_repr ->
    length b = @felem_size_in_words _ base_fp _ _ _ _ base_repr ->
    c2_e (a ++ b ++ c) = c.
  Proof.
    intros Ha Hb. unfold ce_c2_felem.
    rewrite app_assoc.
    rewrite skipn_app_le by (rewrite app_length; lia).
    reflexivity.
  Qed.

  (* ================================================================ *)
  (* CE_zero_ok                                                        *)
  (* ================================================================ *)

  Lemma CE_zero_ok :
    forall functions,
    map.get functions (zero (F := CE)) =
      Some (snd (CE_zero_func mul_by_nr_model prefix eq_dec_base)) ->
    (* Callee 1: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (* Callee 2: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (* Callee 3: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    forall pout (out : @felem _ CE_fp _ _ _ _ CE_repr) Rr tr mem0,
    (@FElem _ CE_fp _ _ _ _ CE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (zero (F := CE)) tr mem0 [pout]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ CE_fp _ _ _ _ CE_repr out' = @Fzero _ CE_fp /\
          @bounded_by _ CE_fp _ _ _ _ CE_repr (@loose_bounds _ CE_fp _ _ _ _ CE_repr) out' /\
          (@FElem _ CE_fp _ _ _ _ CE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFzero1 HFzero2 HFzero3 pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func CE_zero_func GenericCubic.CE_zero_func].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Split CE FElem into 3 base components *)
    destruct Hmem0 as [m_ce [m_rr [[-> Hd_cr] [Hce Hrr]]]].
    pose proof (ce_raw_FElem_split mul_by_nr_model prefix eq_dec_base _ _ _ Hce)
      as [m0 [m12 [[-> Hd0_12] [Ho0 H12]]]].
    destruct H12 as [m1 [m2 [[-> Hd12] [Ho1 Ho2]]]].
    split_all_disjointness.

    (* Call 1: base zero at pout (c0) *)
    exists [pout]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero1 pout (c0_e out)
        (fun m => (FElem_b (word.add pout base_off) (c1_e out) *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))%sep m) tr).
      exists m0, (map.putmany m1 (map.putmany m2 m_rr)).
      split; [split; [rewrite !map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; [assumption |
              apply map.disjoint_putmany_r; split; assumption]] |].
      split; [exact Ho0 |].
      exists m1, (map.putmany m2 m_rr).
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; assumption] |].
      split; [exact Ho1 |].
      exists m2, m_rr; split; [split; [reflexivity | assumption] |].
      split; [exact Ho2 | exact Hrr]. }

    (* Process postcondition of call 1 *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base zero at pout + offset (c1) *)
    exists [word.add pout base_off]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero2 (word.add pout base_off) (c1_e out)
        (fun m => (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))%sep m)).
      (* Reorder sep: from (out0' * (c1 * (c2 * Rr))) to (c1 * (out0' * (c2 * Rr))) *)
      destruct Hsep1 as [m_a [m_bcd [[-> Hd_a] [Ha Hbcd]]]].
      destruct Hbcd as [m_b [m_cd [[-> Hd_b] [Hb Hcd]]]].
      split_all_disjointness.
      exists m_b, (map.putmany m_a m_cd).
      split; [split; [rewrite map.putmany_assoc;
              rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
              rewrite <- map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_cd.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hcd]. }

    (* Process postcondition of call 2 *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 3: base zero at pout + 2*offset (c2) *)
    exists [word.add pout base_off2]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero3 (word.add pout base_off2) (c2_e out)
        (fun m => (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off) out1' * Rr))%sep m)).
      (* Reorder sep: from (out1' * (out0' * (c2 * Rr))) to (c2 * (out0' * (out1' * Rr))) *)
      destruct Hsep2 as [m_a [m_bcd [[-> Hd_a] [Ha Hbcd]]]].
      destruct Hbcd as [m_b [m_cd [[-> Hd_b] [Hb Hcd]]]].
      destruct Hcd as [m_c [m_d [[-> Hd_c] [Hc Hd_rest]]]].
      split_all_disjointness.
      exists m_c, (map.putmany m_b (map.putmany m_a m_d)).
      split; [split; [
        rewrite (map.putmany_assoc m_a m_b (map.putmany m_c m_d));
        rewrite (map.putmany_assoc (map.putmany m_a m_b) m_c m_d);
        rewrite (map.putmany_comm (map.putmany m_a m_b) m_c)
          by (apply map.disjoint_putmany_l; split; map_disjoint_auto);
        rewrite <- (map.putmany_assoc m_c (map.putmany m_a m_b) m_d);
        rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
        rewrite <- (map.putmany_assoc m_b m_a m_d);
        reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Hc |].
      exists m_b, (map.putmany m_a m_d).
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_d.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hd_rest]. }

    (* Process postcondition of call 3 *)
    intros t3 m3' rets3 [-> [-> [out2' [Hfeval2 [Hbound2 Hsep3]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble CE result *)
    destruct Hsep3 as [m_2' [m_fr [[-> Hd_2f] [Hout2 Hfr]]]].
    destruct Hfr as [m_0' [m_1r [[-> Hd_0_1r] [Hout0 H1r]]]].
    destruct H1r as [m_1' [m_r' [[-> Hd_1r] [Hout1 Hr']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.
    pose proof (generic_FElem_length _ _ _ Hout2) as Hlen2.

    exists (out0' ++ out1' ++ out2').
    split.
    { (* feval *)
      change (@AbstractField.feval _ CE_fp _ _ _ _ CE_repr (out0' ++ out1' ++ out2'))
        with ((@AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c0_e (out0' ++ out1' ++ out2')),
               @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c1_e (out0' ++ out1' ++ out2'))),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c2_e (out0' ++ out1' ++ out2'))).
      unfold c0_e, ce_c0_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    split.
    { (* bounded_by — 3 components *)
      split; [| split].
      - unfold c0_e, ce_c0_felem. rewrite firstn_app_le by exact Hlen0. exact Hbound0.
      - rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound1.
      - rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound2. }
    { (* sep: join 3 components back *)
      exists (map.putmany m_0' (map.putmany m_1' m_2')), m_r'.
      split.
      { split.
        { (* Permute [m_2', m_0', m_1', m_r'] -> [m_0', m_1', m_2', m_r'] *)
          rewrite (map.putmany_assoc m_2' m_0' _).
          rewrite (map.putmany_assoc (map.putmany m_2' m_0') m_1' m_r').
          rewrite (map.putmany_comm m_2' m_0') by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m_0' m_2' m_1').
          rewrite (map.putmany_comm m_2' m_1') by map_disjoint_auto.
          reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { map_disjoint_auto. }
          { apply map.disjoint_putmany_l. split; map_disjoint_auto. } } }
      split; [| exact Hr'].
      apply (ce_raw_FElem_join mul_by_nr_model prefix eq_dec_base _ _ _ _
        (map.putmany m_0' (map.putmany m_1' m_2'))
        Hlen0 Hlen1 Hlen2).
      exists m_0', (map.putmany m_1' m_2').
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hout0 |].
      exists m_1', m_2'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hout1 | exact Hout2]. }
  Qed.

  (* ================================================================ *)
  (* CE_one_ok                                                         *)
  (* ================================================================ *)

  Lemma CE_one_ok :
    forall functions,
    map.get functions (one (F := CE)) =
      Some (snd (CE_one_func mul_by_nr_model prefix eq_dec_base)) ->
    (* Callee 1: base one *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (one (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fone _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (* Callee 2: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (* Callee 3: base zero *)
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    forall pout (out : @felem _ CE_fp _ _ _ _ CE_repr) Rr tr mem0,
    (@FElem _ CE_fp _ _ _ _ CE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (one (F := CE)) tr mem0 [pout]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ CE_fp _ _ _ _ CE_repr out' = @Fone _ CE_fp /\
          @bounded_by _ CE_fp _ _ _ _ CE_repr (@loose_bounds _ CE_fp _ _ _ _ CE_repr) out' /\
          (@FElem _ CE_fp _ _ _ _ CE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFone HFzero2 HFzero3 pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func CE_one_func GenericCubic.CE_one_func].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Split CE FElem into 3 base components *)
    destruct Hmem0 as [m_ce [m_rr [[-> Hd_cr] [Hce Hrr]]]].
    pose proof (ce_raw_FElem_split mul_by_nr_model prefix eq_dec_base _ _ _ Hce)
      as [m0 [m12 [[-> Hd0_12] [Ho0 H12]]]].
    destruct H12 as [m1 [m2 [[-> Hd12] [Ho1 Ho2]]]].
    split_all_disjointness.

    (* Call 1: base one at pout (c0) *)
    exists [pout]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFone pout (c0_e out)
        (fun m => (FElem_b (word.add pout base_off) (c1_e out) *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))%sep m) tr).
      exists m0, (map.putmany m1 (map.putmany m2 m_rr)).
      split; [split; [rewrite !map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; [assumption |
              apply map.disjoint_putmany_r; split; assumption]] |].
      split; [exact Ho0 |].
      exists m1, (map.putmany m2 m_rr).
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; assumption] |].
      split; [exact Ho1 |].
      exists m2, m_rr; split; [split; [reflexivity | assumption] |].
      split; [exact Ho2 | exact Hrr]. }

    (* Process postcondition of call 1 *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base zero at pout + offset (c1) *)
    exists [word.add pout base_off]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero2 (word.add pout base_off) (c1_e out)
        (fun m => (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))%sep m)).
      destruct Hsep1 as [m_a [m_bcd [[-> Hd_a] [Ha Hbcd]]]].
      destruct Hbcd as [m_b [m_cd [[-> Hd_b] [Hb Hcd]]]].
      split_all_disjointness.
      exists m_b, (map.putmany m_a m_cd).
      split; [split; [rewrite map.putmany_assoc;
              rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
              rewrite <- map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_cd.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hcd]. }

    (* Process postcondition of call 2 *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 3: base zero at pout + 2*offset (c2) *)
    exists [word.add pout base_off2]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero3 (word.add pout base_off2) (c2_e out)
        (fun m => (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off) out1' * Rr))%sep m)).
      destruct Hsep2 as [m_a [m_bcd [[-> Hd_a] [Ha Hbcd]]]].
      destruct Hbcd as [m_b [m_cd [[-> Hd_b] [Hb Hcd]]]].
      destruct Hcd as [m_c [m_d [[-> Hd_c] [Hc Hd_rest]]]].
      split_all_disjointness.
      exists m_c, (map.putmany m_b (map.putmany m_a m_d)).
      split; [split; [
        rewrite (map.putmany_assoc m_a m_b (map.putmany m_c m_d));
        rewrite (map.putmany_assoc (map.putmany m_a m_b) m_c m_d);
        rewrite (map.putmany_comm (map.putmany m_a m_b) m_c)
          by (apply map.disjoint_putmany_l; split; map_disjoint_auto);
        rewrite <- (map.putmany_assoc m_c (map.putmany m_a m_b) m_d);
        rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
        rewrite <- (map.putmany_assoc m_b m_a m_d);
        reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Hc |].
      exists m_b, (map.putmany m_a m_d).
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_d.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hd_rest]. }

    (* Process postcondition of call 3 *)
    intros t3 m3' rets3 [-> [-> [out2' [Hfeval2 [Hbound2 Hsep3]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble CE result *)
    destruct Hsep3 as [m_2' [m_fr [[-> Hd_2f] [Hout2 Hfr]]]].
    destruct Hfr as [m_0' [m_1r [[-> Hd_0_1r] [Hout0 H1r]]]].
    destruct H1r as [m_1' [m_r' [[-> Hd_1r] [Hout1 Hr']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.
    pose proof (generic_FElem_length _ _ _ Hout2) as Hlen2.

    exists (out0' ++ out1' ++ out2').
    split.
    { (* feval *)
      change (@AbstractField.feval _ CE_fp _ _ _ _ CE_repr (out0' ++ out1' ++ out2'))
        with ((@AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c0_e (out0' ++ out1' ++ out2')),
               @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c1_e (out0' ++ out1' ++ out2'))),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c2_e (out0' ++ out1' ++ out2'))).
      unfold c0_e, ce_c0_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    split.
    { (* bounded_by *)
      split; [| split].
      - unfold c0_e, ce_c0_felem. rewrite firstn_app_le by exact Hlen0. exact Hbound0.
      - rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound1.
      - rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound2. }
    { (* sep: join 3 components back *)
      exists (map.putmany m_0' (map.putmany m_1' m_2')), m_r'.
      split.
      { split.
        { rewrite (map.putmany_assoc m_2' m_0' _).
          rewrite (map.putmany_assoc (map.putmany m_2' m_0') m_1' m_r').
          rewrite (map.putmany_comm m_2' m_0') by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m_0' m_2' m_1').
          rewrite (map.putmany_comm m_2' m_1') by map_disjoint_auto.
          reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { map_disjoint_auto. }
          { apply map.disjoint_putmany_l. split; map_disjoint_auto. } } }
      split; [| exact Hr'].
      apply (ce_raw_FElem_join mul_by_nr_model prefix eq_dec_base _ _ _ _
        (map.putmany m_0' (map.putmany m_1' m_2'))
        Hlen0 Hlen1 Hlen2).
      exists m_0', (map.putmany m_1' m_2').
      split; [split; [reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hout0 |].
      exists m_1', m_2'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hout1 | exact Hout2]. }
  Qed.

  (* ================================================================ *)
  (* CE_opp_ok                                                         *)
  (* ================================================================ *)

  Lemma CE_opp_ok :
    forall functions,
    map.get functions (opp (F := CE)) =
      Some (snd (CE_opp mul_by_nr_model prefix eq_dec_base)) ->
    (* Callee: base opp (nested sep form) — 3 copies *)
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    forall pout px (out x : @felem _ CE_fp _ _ _ _ CE_repr) Rr tr mem0,
    @bounded_by _ CE_fp _ _ _ _ CE_repr (@tight_bounds _ CE_fp _ _ _ _ CE_repr) x ->
    (@FElem _ CE_fp _ _ _ _ CE_repr px x *
     (@FElem _ CE_fp _ _ _ _ CE_repr pout out * Rr))%sep mem0 ->
    WeakestPrecondition.call functions (opp (F := CE)) tr mem0 [pout; px]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ CE_fp _ _ _ _ CE_repr out' =
                       @Fopp _ CE_fp (@feval _ CE_fp _ _ _ _ CE_repr x) /\
          @bounded_by _ CE_fp _ _ _ _ CE_repr (@loose_bounds _ CE_fp _ _ _ _ CE_repr) out' /\
          (@FElem _ CE_fp _ _ _ _ CE_repr pout out' *
           (@FElem _ CE_fp _ _ _ _ CE_repr px x * Rr))%sep mem').
  Proof.
    intros functions EnvContains HFopp1 HFopp2 HFopp3 pout px out x Rr tr mem0
           [Hbound_x0 [Hbound_x1 Hbound_x2]] Hmem0.
    (* Pin implicit args so rewrite works identically in coq-lsp and make *)
    pose proof (@map.putmany_assoc _ _ _ mem_ok word.eqb
                  (word.eqb_spec (word := word))) as putmany_assoc.
    pose proof (@map.putmany_comm _ _ _ mem_ok word.eqb
                  (word.eqb_spec (word := word))) as putmany_comm.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func CE_opp GenericCubic.CE_opp].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Destruct the nested sep: (CE_x * (CE_out * Rr)) *)
    destruct Hmem0 as [m_x [m_or [[-> Hd_xor] [Hx Hor]]]].
    destruct Hor as [m_o [m_r [[-> Hd_or] [Ho Hr]]]].
    split_all_disjointness.

    (* Split CE FElems into 3 base components each *)
    pose proof (ce_raw_FElem_split mul_by_nr_model prefix eq_dec_base _ _ _ Hx)
      as [mx0 [mx12 [[-> Hdx0_12] [Hx0 Hx12]]]].
    destruct Hx12 as [mx1 [mx2 [[-> Hdx12] [Hx1 Hx2]]]].
    pose proof (ce_raw_FElem_split mul_by_nr_model prefix eq_dec_base _ _ _ Ho)
      as [mo0 [mo12 [[-> Hdo0_12] [Ho0 Ho12]]]].
    destruct Ho12 as [mo1 [mo2 [[-> Hdo12] [Ho1 Ho2]]]].
    split_all_disjointness.

    (* ---- Call 1: base opp at (pout, px) for c0 components ---- *)
    exists [pout; px]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFopp1 pout px (c0_e out) (c0_e x)
        (fun m => (FElem_b (word.add px base_off) (c1_e x) *
                  (FElem_b (word.add px base_off2) (c2_e x) *
                  (FElem_b (word.add pout base_off) (c1_e out) *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))))%sep m) tr).
      { exact Hbound_x0. }
      exists mx0, (map.putmany mo0 (map.putmany mx1 (map.putmany mx2 (map.putmany mo1 (map.putmany mo2 m_r))))).
      split.
      { split.
        - rewrite <- !(putmany_assoc). f_equal.
          rewrite (putmany_assoc mx2 mo0 (map.putmany mo1 (map.putmany mo2 m_r))).
          rewrite (putmany_comm mx2 mo0) by map_disjoint_auto.
          rewrite <- (putmany_assoc mo0 mx2 (map.putmany mo1 (map.putmany mo2 m_r))).
          rewrite (putmany_assoc mx1 mo0 (map.putmany mx2 (map.putmany mo1 (map.putmany mo2 m_r)))).
          rewrite (putmany_comm mx1 mo0) by map_disjoint_auto.
          rewrite <- (putmany_assoc mo0 mx1 (map.putmany mx2 (map.putmany mo1 (map.putmany mo2 m_r)))).
          reflexivity.
        - apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; map_disjoint_auto]]]]. }
      split; [exact Hx0 |].
      exists mo0, (map.putmany mx1 (map.putmany mx2 (map.putmany mo1 (map.putmany mo2 m_r)))).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]]]] |].
      split; [exact Ho0 |].
      exists mx1, (map.putmany mx2 (map.putmany mo1 (map.putmany mo2 m_r))).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]]] |].
      split; [exact Hx1 |].
      exists mx2, (map.putmany mo1 (map.putmany mo2 m_r)).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Hx2 |].
      exists mo1, (map.putmany mo2 m_r).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Ho1 |].
      exists mo2, m_r.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ho2 | exact Hr]. }

    (* Process postcondition of call 1 *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* ---- Call 2: base opp at (pout+off, px+off) for c1 components ---- *)
    exists [word.add pout base_off; word.add px base_off]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFopp2 (word.add pout base_off) (word.add px base_off)
                     (c1_e out) (c1_e x)
        (fun m => (FElem_b px (c0_e x) *
                  (FElem_b (word.add px base_off2) (c2_e x) *
                  (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off2) (c2_e out) * Rr))))%sep m) t1).
      { exact Hbound_x1. }
      destruct Hsep1 as [ma [mb [[-> Hda'] [Ha' Hb']]]].
      destruct Hb' as [mc [md [[-> Hdb'] [Hc' Hd'']]]].
      destruct Hd'' as [me [mf [[-> Hdc'] [He' Hf']]]].
      destruct Hf' as [mg [mh [[-> Hdd'] [Hg' Hh']]]].
      destruct Hh' as [mi [mj [[-> Hde'] [Hi' Hj']]]].
      destruct Hj' as [mk [ml [[-> Hdf'] [Hk' Hl']]]].
      split_all_disjointness.
      (* Sub-memories: ma=out0', mc=x0, me=x1, mg=x2, mi=o1, mk=o2, ml=Rr *)
      (* Target: me, mi, mc, mg, ma, mk, ml *)
      exists me, (map.putmany mi (map.putmany mc (map.putmany mg (map.putmany ma (map.putmany mk ml))))).
      split.
      { split.
        - (* Permute right-assoc: ma mc me mg mi mk ml -> me mi mc mg ma mk ml *)
          (* Move me from pos 3 to pos 1 *)
          rewrite (putmany_assoc mc me _). rewrite (putmany_comm mc me) by map_disjoint_auto.
          rewrite <- (putmany_assoc me mc _).
          rewrite (putmany_assoc ma me _). rewrite (putmany_comm ma me) by map_disjoint_auto.
          rewrite <- (putmany_assoc me ma _).
          (* Now: me ma mc mg mi mk ml *)
          (* Move mi from pos 5 to pos 2 *)
          rewrite (putmany_assoc mg mi _). rewrite (putmany_comm mg mi) by map_disjoint_auto.
          rewrite <- (putmany_assoc mi mg _).
          rewrite (putmany_assoc mc mi _). rewrite (putmany_comm mc mi) by map_disjoint_auto.
          rewrite <- (putmany_assoc mi mc _).
          rewrite (putmany_assoc ma mi _). rewrite (putmany_comm ma mi) by map_disjoint_auto.
          rewrite <- (putmany_assoc mi ma _).
          (* Now: me mi ma mc mg mk ml *)
          (* Move ma from pos 3 to pos 5 *)
          rewrite (putmany_assoc ma mc _). rewrite (putmany_comm ma mc) by map_disjoint_auto.
          rewrite <- (putmany_assoc mc ma _).
          rewrite (putmany_assoc ma mg _). rewrite (putmany_comm ma mg) by map_disjoint_auto.
          rewrite <- (putmany_assoc mg ma _).
          (* Now: me mi mc mg ma mk ml *)
          reflexivity.
        - apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; map_disjoint_auto]]]]. }
      split; [exact He' |].
      exists mi, (map.putmany mc (map.putmany mg (map.putmany ma (map.putmany mk ml)))).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]]]] |].
      split; [exact Hi' |].
      exists mc, (map.putmany mg (map.putmany ma (map.putmany mk ml))).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]]] |].
      split; [exact Hc' |].
      exists mg, (map.putmany ma (map.putmany mk ml)).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Hg' |].
      exists ma, (map.putmany mk ml).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Ha' |].
      exists mk, ml.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hk' | exact Hl']. }

    (* Process postcondition of call 2 *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* ---- Call 3: base opp at (pout+off2, px+off2) for c2 components ---- *)
    exists [word.add pout base_off2; word.add px base_off2]; split; [solve_ce_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFopp3 (word.add pout base_off2) (word.add px base_off2)
                     (c2_e out) (c2_e x)
        (fun m => (FElem_b px (c0_e x) *
                  (FElem_b (word.add px base_off) (c1_e x) *
                  (FElem_b pout out0' *
                  (FElem_b (word.add pout base_off) out1' * Rr))))%sep m) t2).
      { exact Hbound_x2. }
      destruct Hsep2 as [m2a [m2b [[-> Hd2a] [H2a H2b]]]].
      destruct H2b as [m2c [m2d [[-> Hd2b] [H2c H2d]]]].
      destruct H2d as [m2e [m2f [[-> Hd2c] [H2e H2f]]]].
      destruct H2f as [m2g [m2h [[-> Hd2d] [H2g H2h]]]].
      destruct H2h as [m2i [m2j [[-> Hd2e] [H2i H2j]]]].
      destruct H2j as [m2k [m2l [[-> Hd2f] [H2k H2l]]]].
      split_all_disjointness.
      (* Sub-memories: m2a=out1', m2c=x1, m2e=x0, m2g=x2, m2i=out0', m2k=o2, m2l=Rr *)
      (* Target: m2g, m2k, m2e, m2c, m2i, m2a, m2l *)
      exists m2g, (map.putmany m2k (map.putmany m2e (map.putmany m2c (map.putmany m2i (map.putmany m2a m2l))))).
      split.
      { split.
        - (* Permute right-assoc: m2a m2c m2e m2g m2i m2k m2l -> m2g m2k m2e m2c m2i m2a m2l *)
          (* Move m2g from pos 4 to pos 1 *)
          rewrite (putmany_assoc m2e m2g _). rewrite (putmany_comm m2e m2g) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2g m2e _).
          rewrite (putmany_assoc m2c m2g _). rewrite (putmany_comm m2c m2g) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2g m2c _).
          rewrite (putmany_assoc m2a m2g _). rewrite (putmany_comm m2a m2g) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2g m2a _).
          (* Now: m2g m2a m2c m2e m2i m2k m2l *)
          (* Move m2k from pos 6 to pos 2 *)
          rewrite (putmany_assoc m2i m2k _). rewrite (putmany_comm m2i m2k) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2k m2i _).
          rewrite (putmany_assoc m2e m2k _). rewrite (putmany_comm m2e m2k) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2k m2e _).
          rewrite (putmany_assoc m2c m2k _). rewrite (putmany_comm m2c m2k) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2k m2c _).
          rewrite (putmany_assoc m2a m2k _). rewrite (putmany_comm m2a m2k) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2k m2a _).
          (* Now: m2g m2k m2a m2c m2e m2i m2l *)
          (* Move m2e from pos 5 to pos 3 *)
          rewrite (putmany_assoc m2c m2e _). rewrite (putmany_comm m2c m2e) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2e m2c _).
          rewrite (putmany_assoc m2a m2e _). rewrite (putmany_comm m2a m2e) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2e m2a _).
          (* Now: m2g m2k m2e m2a m2c m2i m2l *)
          (* Swap m2a,m2c then m2a,m2i *)
          rewrite (putmany_assoc m2a m2c _). rewrite (putmany_comm m2a m2c) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2c m2a _).
          rewrite (putmany_assoc m2a m2i _). rewrite (putmany_comm m2a m2i) by map_disjoint_auto.
          rewrite <- (putmany_assoc m2i m2a _).
          (* Now: m2g m2k m2e m2c m2i m2a m2l *)
          reflexivity.
        - apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; map_disjoint_auto]]]]. }
      split; [exact H2g |].
      exists m2k, (map.putmany m2e (map.putmany m2c (map.putmany m2i (map.putmany m2a m2l)))).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]]]] |].
      split; [exact H2k |].
      exists m2e, (map.putmany m2c (map.putmany m2i (map.putmany m2a m2l))).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]]] |].
      split; [exact H2e |].
      exists m2c, (map.putmany m2i (map.putmany m2a m2l)).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact H2c |].
      exists m2i, (map.putmany m2a m2l).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact H2i |].
      exists m2a, m2l.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact H2a | exact H2l]. }

    (* Process postcondition of call 3 *)
    intros t3 m3' rets3 [-> [-> [out2' [Hfeval2 [Hbound2 Hsep3]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* ---- Assemble CE results ---- *)
    destruct Hsep3 as [m3a [m3b [[-> Hd3a] [Hout2 Hrest3a]]]].
    destruct Hrest3a as [m3c [m3d [[-> Hd3b] [Hx2_final Hrest3b]]]].
    destruct Hrest3b as [m3e [m3f [[-> Hd3c] [Hx0_final Hrest3c]]]].
    destruct Hrest3c as [m3g [m3h [[-> Hd3d] [Hx1_final Hrest3d]]]].
    destruct Hrest3d as [m3i [m3j [[-> Hd3e] [Hout0 Hrest3e]]]].
    destruct Hrest3e as [m3k [m3l [[-> Hd3f] [Hout1 Hr'']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.
    pose proof (generic_FElem_length _ _ _ Hout2) as Hlen2.
    pose proof (generic_FElem_length _ _ _ Hx0_final) as Hlenx0.
    pose proof (generic_FElem_length _ _ _ Hx1_final) as Hlenx1.
    pose proof (generic_FElem_length _ _ _ Hx2_final) as Hlenx2.

    exists (out0' ++ out1' ++ out2').
    split.
    { (* feval *)
      change (@AbstractField.feval _ CE_fp _ _ _ _ CE_repr (out0' ++ out1' ++ out2'))
        with ((@AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c0_e (out0' ++ out1' ++ out2')),
               @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c1_e (out0' ++ out1' ++ out2'))),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr
                  (c2_e (out0' ++ out1' ++ out2'))).
      unfold c0_e, ce_c0_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1).
      rewrite Hfeval0, Hfeval1, Hfeval2. reflexivity. }
    split.
    { (* bounded_by -- 3 components *)
      split; [| split].
      - unfold c0_e, ce_c0_felem. rewrite firstn_app_le by exact Hlen0. exact Hbound0.
      - rewrite (c1_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound1.
      - rewrite (c2_app_app out0' out1' out2' Hlen0 Hlen1). exact Hbound2. }
    { (* sep: (CE_pout (out0'++out1'++out2') * (CE_px x * Rr)) *)
      exists (map.putmany m3i (map.putmany m3k m3a)),
             (map.putmany m3e (map.putmany m3g (map.putmany m3c m3l))).
      split.
      { split.
        { (* Permute right-assoc: m3a m3c m3e m3g m3i m3k m3l -> m3i m3k m3a m3e m3g m3c m3l *)
          (* Move m3i from pos 5 to pos 1 *)
          rewrite (putmany_assoc m3g m3i _). rewrite (putmany_comm m3g m3i) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3i m3g _).
          rewrite (putmany_assoc m3e m3i _). rewrite (putmany_comm m3e m3i) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3i m3e _).
          rewrite (putmany_assoc m3c m3i _). rewrite (putmany_comm m3c m3i) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3i m3c _).
          rewrite (putmany_assoc m3a m3i _). rewrite (putmany_comm m3a m3i) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3i m3a _).
          (* Now: m3i m3a m3c m3e m3g m3k m3l *)
          (* Move m3k from pos 6 to pos 2 *)
          rewrite (putmany_assoc m3g m3k _). rewrite (putmany_comm m3g m3k) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3k m3g _).
          rewrite (putmany_assoc m3e m3k _). rewrite (putmany_comm m3e m3k) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3k m3e _).
          rewrite (putmany_assoc m3c m3k _). rewrite (putmany_comm m3c m3k) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3k m3c _).
          rewrite (putmany_assoc m3a m3k _). rewrite (putmany_comm m3a m3k) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3k m3a _).
          (* Now: m3i m3k m3a m3c m3e m3g m3l *)
          (* Swap m3c,m3e and then m3c,m3g to move m3c to end *)
          rewrite (putmany_assoc m3c m3e _). rewrite (putmany_comm m3c m3e) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3e m3c _).
          rewrite (putmany_assoc m3c m3g _). rewrite (putmany_comm m3c m3g) by map_disjoint_auto.
          rewrite <- (putmany_assoc m3g m3c _).
          (* Now: m3i m3k m3a m3e m3g m3c m3l -- normalize associativity *)
          rewrite !putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l; split.
          { apply map.disjoint_putmany_r; split; [map_disjoint_auto |
            apply map.disjoint_putmany_r; split; [map_disjoint_auto |
            apply map.disjoint_putmany_r; split; map_disjoint_auto]]. }
          { apply map.disjoint_putmany_l; split.
            { apply map.disjoint_putmany_r; split; [map_disjoint_auto |
              apply map.disjoint_putmany_r; split; [map_disjoint_auto |
              apply map.disjoint_putmany_r; split; map_disjoint_auto]]. }
            { apply map.disjoint_putmany_r; split; [map_disjoint_auto |
              apply map.disjoint_putmany_r; split; [map_disjoint_auto |
              apply map.disjoint_putmany_r; split; map_disjoint_auto]]. } } } }
      split.
      { (* CE FElem for output: join out0', out1', out2' *)
        apply (ce_raw_FElem_join mul_by_nr_model prefix eq_dec_base _ _ _ _
          (map.putmany m3i (map.putmany m3k m3a))
          Hlen0 Hlen1 Hlen2).
        exists m3i, (map.putmany m3k m3a).
        split; [split; [reflexivity |
                apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
        split; [exact Hout0 |].
        exists m3k, m3a.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hout1 | exact Hout2]. }
      { (* (CE_px x * Rr) -- reconstruct x from c0 x ++ c1 x ++ c2 x *)
        rewrite <- (@ce_list_decomp _ _ _ _ _ base_fp base_repr x).
        exists (map.putmany m3e (map.putmany m3g m3c)), m3l.
        split.
        { split.
          - rewrite !(putmany_assoc). reflexivity.
          - apply map.disjoint_putmany_l; split.
            { map_disjoint_auto. }
            { apply map.disjoint_putmany_l; split; map_disjoint_auto. } }
        split.
        { apply (ce_raw_FElem_join mul_by_nr_model prefix eq_dec_base _ _ _ _
            (map.putmany m3e (map.putmany m3g m3c))
            Hlenx0 Hlenx1 Hlenx2).
          exists m3e, (map.putmany m3g m3c).
          split; [split; [reflexivity |
                  apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
          split; [exact Hx0_final |].
          exists m3g, m3c.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hx1_final | exact Hx2_final]. }
        { exact Hr''. } } }
  Qed.

End GenericCubicProofs.
