(** * WP correctness proofs for generic quadratic extension functions. *)

Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.

Import Separation SeparationLogic.

Section GenericQuadProofs.
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

  Variable nonresidue : BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Instance QE_fp : FieldParameters (BaseField * BaseField) :=
    QE_field_parameters nonresidue prefix eq_dec_base.
  Local Instance QE_repr : @FieldRepresentation _ QE_fp width BW word mem :=
    QE_field_representation nonresidue prefix eq_dec_base.

  Local Notation QE := (BaseField * BaseField)%type.
  Local Notation FElem_b := (@FElem _ base_fp _ _ _ _ base_repr).
  Local Notation fst_e := (@qe_fst_felem _ _ _ _ _ base_fp base_repr).
  Local Notation snd_e := (@qe_snd_felem _ _ _ _ _ base_fp base_repr).
  Local Notation base_off := (word.of_Z (Memory.bytes_per_word width *
    Z.of_nat (@felem_size_in_words _ base_fp _ _ _ _ base_repr))).

  Context {QE_names : FieldNames (F := QE)} {base_names : FieldNames (F := BaseField)}.
  Variable mul_by_nr_name : string.
  Variable Mul_by_nr_func : string * (list String.string * list String.string * Syntax.cmd.cmd).
  Hypothesis Mul_by_nr_name_eq : fst Mul_by_nr_func = mul_by_nr_name.

  (* Helper: solve dexprs for qe_expr_2nd *)
  Local Ltac solve_qe_dexprs :=
    first [ solve_dexprs
          | unfold qe_expr_2nd;
            cbv [dexprs list_map list_map_body WeakestPrecondition.expr
                 WeakestPrecondition.expr_body Semantics.interp_binop literal dlet.dlet];
            repeat (eexists; split; [first [apply map.get_put_same |
              rewrite map.get_put_diff by congruence; apply map.get_put_same] |]);
            exact eq_refl ].

  (* Helper: reorder sep for the second call *)
  Local Ltac sep_reorder_for_second_call :=
    match goal with
    | Hsep : (_ ⋆ (fun m => (_ ⋆ _)%sep m))%sep ?mem |- (_ ⋆ (fun m => (_ ⋆ _)%sep m))%sep ?mem =>
      let m_a := fresh "m" in let m_bc := fresh "m" in
      let m_b := fresh "m" in let m_c := fresh "m" in
      destruct Hsep as [m_a [m_bc [[[= ->] ?] [?H_a [m_b [m_c [[[= ->] ?] [?H_b ?H_c]]]]]]]];
      split_all_disjointness;
      exists m_b, (map.putmany m_a m_c);
      (split; [split; [rewrite map.putmany_assoc; f_equal;
               apply map.putmany_comm; map_disjoint_auto |
               apply map.disjoint_putmany_r; split; map_disjoint_auto] |]);
      split; [assumption |];
      exists m_a, m_c;
      (split; [split; [reflexivity | map_disjoint_auto] |]);
      split; assumption
    end.

  (* ================================================================ *)
  (* QE_zero_ok                                                        *)
  (* ================================================================ *)

  Lemma QE_zero_ok :
    forall functions,
    map.get functions (zero (F := QE)) =
      Some (snd (QE_zero_func nonresidue prefix eq_dec_base)) ->
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    (forall p out Rr tr m,
       (FElem_b p out * Rr)%sep m ->
       WeakestPrecondition.call functions (zero (F := BaseField)) tr m [p]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' = @Fzero _ base_fp /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b p out' * Rr)%sep m')) ->
    forall pout (out : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (zero (F := QE)) tr mem0 [pout]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' = @Fzero _ QE_fp /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFzero1 HFzero2 pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func QE_zero_func GenericQuadratic.QE_zero_func].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Split QE FElem *)
    destruct Hmem0 as [m_qe [m_rr [[-> Hd_qr] [Hqe Hrr]]]].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hqe)
      as [m0 [m1 [[-> Hd01] [Ho0 Ho1]]]].
    split_all_disjointness.

    (* Call 1: base zero at pout *)
    exists [pout]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero1 pout (fst_e out)
        (fun m => (FElem_b (word.add pout base_off) (snd_e out) * Rr)%sep m) tr).
      exists m0, (map.putmany m1 m_rr).
      split; [split; [rewrite map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; assumption] |].
      split; [exact Ho0 |].
      exists m1, m_rr; split; [split; [reflexivity | assumption] |].
      split; [exact Ho1 | exact Hrr]. }

    (* Process postcondition *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base zero at pout + offset *)
    exists [word.add pout base_off]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero2 (word.add pout base_off) (snd_e out)
        (fun m => (FElem_b pout out0' * Rr)%sep m)).
      destruct Hsep1 as [m_a [m_bc [[-> Hd_abc] [Ha Hbc]]]].
      destruct Hbc as [m_b [m_c [[-> Hd_bc] [Hb Hc]]]].
      split_all_disjointness.
      exists m_b, (map.putmany m_a m_c).
      split; [split; [rewrite map.putmany_assoc;
              rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
              rewrite <- map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_c.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hc]. }

    (* Process postcondition *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble QE result — destruct sep first *)
    destruct Hsep2 as [m_1' [m_fr [[-> Hd_1f] [Hout1 Hfr]]]].
    destruct Hfr as [m_0' [m_r' [[-> Hd_0r] [Hout0 Hr']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.

    exists (out0' ++ out1').
    split.
    { (* feval *)
      change (@AbstractField.feval _ QE_fp _ _ _ _ QE_repr (out0' ++ out1'))
        with (@AbstractField.feval _ base_fp _ _ _ _ base_repr (fst_e (out0' ++ out1')),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr (snd_e (out0' ++ out1'))).
      unfold fst_e, qe_fst_felem, snd_e, qe_snd_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite skipn_app_le by exact Hlen0.
      rewrite Hfeval0, Hfeval1. reflexivity. }
    split.
    { (* bounded_by *)
      split; unfold fst_e, snd_e, qe_fst_felem, qe_snd_felem;
        [rewrite firstn_app_le | rewrite skipn_app_le]; try exact Hlen0; assumption. }
    { (* sep: join halves *)
      exists (map.putmany m_0' m_1'), m_r'.
      split.
      { split.
        { rewrite map.putmany_assoc.
          rewrite (map.putmany_comm m_1' m_0') by map_disjoint_auto.
          rewrite <- map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l. split; [map_disjoint_auto | assumption]. } }
      split; [| exact Hr'].
      apply (qe_raw_FElem_join nonresidue prefix eq_dec_base _ _ _ _ Hlen0 Hlen1).
      exists m_0', m_1'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hout0 | exact Hout1]. }
  Qed.

  (* ================================================================ *)
  (* QE_one_ok                                                         *)
  (* ================================================================ *)

  Lemma QE_one_ok :
    forall functions,
    map.get functions (one (F := QE)) =
      Some (snd (QE_one_func nonresidue prefix eq_dec_base)) ->
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
    forall pout (out : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (one (F := QE)) tr mem0 [pout]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' = @Fone _ QE_fp /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFone HFzero pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func QE_one_func GenericQuadratic.QE_one_func].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Split QE FElem *)
    destruct Hmem0 as [m_qe [m_rr [[-> Hd_qr] [Hqe Hrr]]]].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hqe)
      as [m0 [m1 [[-> Hd01] [Ho0 Ho1]]]].
    split_all_disjointness.

    (* Call 1: base one at pout *)
    exists [pout]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFone pout (fst_e out)
        (fun m => (FElem_b (word.add pout base_off) (snd_e out) * Rr)%sep m) tr).
      exists m0, (map.putmany m1 m_rr).
      split; [split; [rewrite map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; assumption] |].
      split; [exact Ho0 |].
      exists m1, m_rr; split; [split; [reflexivity | assumption] |].
      split; [exact Ho1 | exact Hrr]. }

    (* Process postcondition *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base zero at pout + offset *)
    exists [word.add pout base_off]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFzero (word.add pout base_off) (snd_e out)
        (fun m => (FElem_b pout out0' * Rr)%sep m)).
      destruct Hsep1 as [m_a [m_bc [[-> Hd_abc] [Ha Hbc]]]].
      destruct Hbc as [m_b [m_c [[-> Hd_bc] [Hb Hc]]]].
      split_all_disjointness.
      exists m_b, (map.putmany m_a m_c).
      split; [split; [rewrite map.putmany_assoc;
              rewrite (map.putmany_comm m_a m_b) by map_disjoint_auto;
              rewrite <- map.putmany_assoc; reflexivity |
              apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hb |].
      exists m_a, m_c.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha | exact Hc]. }

    (* Process postcondition *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble QE result *)
    destruct Hsep2 as [m_1' [m_fr [[-> Hd_1f] [Hout1 Hfr]]]].
    destruct Hfr as [m_0' [m_r' [[-> Hd_0r] [Hout0 Hr']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.

    exists (out0' ++ out1').
    split.
    { (* feval *)
      change (@AbstractField.feval _ QE_fp _ _ _ _ QE_repr (out0' ++ out1'))
        with (@AbstractField.feval _ base_fp _ _ _ _ base_repr (fst_e (out0' ++ out1')),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr (snd_e (out0' ++ out1'))).
      unfold fst_e, qe_fst_felem, snd_e, qe_snd_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite skipn_app_le by exact Hlen0.
      rewrite Hfeval0, Hfeval1. reflexivity. }
    split.
    { (* bounded_by *)
      split; unfold fst_e, snd_e, qe_fst_felem, qe_snd_felem;
        [rewrite firstn_app_le | rewrite skipn_app_le]; try exact Hlen0; assumption. }
    { (* sep: join halves *)
      exists (map.putmany m_0' m_1'), m_r'.
      split.
      { split.
        { rewrite map.putmany_assoc.
          rewrite (map.putmany_comm m_1' m_0') by map_disjoint_auto.
          rewrite <- map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l. split; [map_disjoint_auto | assumption]. } }
      split; [| exact Hr'].
      apply (qe_raw_FElem_join nonresidue prefix eq_dec_base _ _ _ _ Hlen0 Hlen1).
      exists m_0', m_1'.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Hout0 | exact Hout1]. }
  Qed.

  (* ================================================================ *)
  (* QE_opp_ok                                                         *)
  (* ================================================================ *)

  Lemma QE_opp_ok :
    forall functions,
    map.get functions (opp (F := QE)) =
      Some (snd (QE_opp nonresidue prefix eq_dec_base)) ->
    (* Callee: base opp (nested sep form) *)
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    (* Same callee for second component *)
    (forall pout px out x Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       (FElem_b px x * (FElem_b pout out * Rr))%sep m ->
       WeakestPrecondition.call functions (opp (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fopp _ base_fp (@feval _ base_fp _ _ _ _ base_repr x) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * (FElem_b px x * Rr))%sep m')) ->
    forall pout px (out x : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@tight_bounds _ QE_fp _ _ _ _ QE_repr) x ->
    (@FElem _ QE_fp _ _ _ _ QE_repr px x *
     (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr))%sep mem0 ->
    WeakestPrecondition.call functions (opp (F := QE)) tr mem0 [pout; px]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' =
                       @Fopp _ QE_fp (@feval _ QE_fp _ _ _ _ QE_repr x) /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' *
           (@FElem _ QE_fp _ _ _ _ QE_repr px x * Rr))%sep mem').
  Proof.
    intros functions EnvContains HFopp1 HFopp2 pout px out x Rr tr mem0
           [Hbound_x0 Hbound_x1] Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func QE_opp GenericQuadratic.QE_opp].
    eexists; split; [exact eq_refl |]; repeat straightline.

    (* Destruct the nested sep: (QE_x * (QE_out * Rr)) *)
    destruct Hmem0 as [m_x [m_or [[-> Hd_xor] [Hx Hor]]]].
    destruct Hor as [m_o [m_r [[-> Hd_or] [Ho Hr]]]].
    split_all_disjointness.

    (* Split QE FElems into base components *)
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hx)
      as [mx0 [mx1 [[-> Hdx01] [Hx0 Hx1]]]].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Ho)
      as [mo0 [mo1 [[-> Hdo01] [Ho0 Ho1]]]].
    split_all_disjointness.

    (* Call 1: base opp at (pout, px) for first components *)
    exists [pout; px]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFopp1 pout px (fst_e out) (fst_e x)
        (fun m => (FElem_b (word.add px base_off) (snd_e x) *
                  (FElem_b (word.add pout base_off) (snd_e out) * Rr))%sep m) tr).
      { exact Hbound_x0. }
      (* mem0 = putmany (putmany mx0 mx1) (putmany (putmany mo0 mo1) m_r) *)
      (* Need: (FElem_b px x0 * (FElem_b pout o0 * Frame)) mem0 *)
      exists mx0, (map.putmany mo0 (map.putmany mx1 (map.putmany mo1 m_r))).
      split.
      { split.
        - rewrite map.putmany_assoc.
          rewrite <- !map.putmany_assoc.
          rewrite (map.putmany_assoc mx1 mo0 _).
          rewrite (map.putmany_comm mx1 mo0) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc mo0 mx1 _). reflexivity.
        - apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; map_disjoint_auto]]. }
      split; [exact Hx0 |].
      exists mo0, (map.putmany mx1 (map.putmany mo1 m_r)).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Ho0 |].
      exists mx1, (map.putmany mo1 m_r).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hx1 |].
      exists mo1, m_r.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ho1 | exact Hr]. }

    (* Process postcondition of call 1 *)
    intros t1 m1' rets1 [-> [-> [out0' [Hfeval0 [Hbound0 Hsep1]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |]; repeat straightline.

    (* Call 2: base opp at (pout+off, px+off) for second components *)
    exists [word.add pout base_off; word.add px base_off]; split; [solve_qe_dexprs |].
    eapply Semantics.weaken_call.
    { eapply (HFopp2 (word.add pout base_off) (word.add px base_off)
                     (snd_e out) (snd_e x)
        (fun m => (FElem_b px (fst_e x) *
                  (FElem_b pout out0' * Rr))%sep m) t1).
      { exact Hbound_x1. }
      (* From Hsep1: (out0' * (x0 * (x1 * (o1 * Rr)))) on m1' *)
      (* Need: (x1 * (o1 * (x0 * (out0' * Rr)))) on m1' *)
      destruct Hsep1 as [ma [mb [[-> Hda'] [Ha' Hb']]]].
      destruct Hb' as [mc [md [[-> Hdb'] [Hc' Hd'']]]].
      destruct Hd'' as [me [mf [[-> Hdc'] [He' Hf']]]].
      destruct Hf' as [mg [mh [[-> Hdd'] [Hg' Hh']]]].
      split_all_disjointness.
      (* Permute [ma,mc,me,mg,mh] -> [me,mg,mc,ma,mh] *)
      exists me, (map.putmany mg (map.putmany mc (map.putmany ma mh))).
      split.
      { split.
        - rewrite (map.putmany_assoc mc me _).
          rewrite (map.putmany_comm mc me) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc me mc _).
          rewrite (map.putmany_assoc ma me _).
          rewrite (map.putmany_comm ma me) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc me ma _).
          rewrite (map.putmany_assoc mc mg _).
          rewrite (map.putmany_comm mc mg) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc mg mc _).
          rewrite (map.putmany_assoc ma mg _).
          rewrite (map.putmany_comm ma mg) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc mg ma _).
          rewrite (map.putmany_assoc ma mc _).
          rewrite (map.putmany_comm ma mc) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc mc ma _). reflexivity.
        - apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; [map_disjoint_auto |
          apply map.disjoint_putmany_r; split; map_disjoint_auto]]. }
      split; [exact He' |].
      exists mg, (map.putmany mc (map.putmany ma mh)).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; [map_disjoint_auto |
        apply map.disjoint_putmany_r; split; map_disjoint_auto]] |].
      split; [exact Hg' |].
      exists mc, (map.putmany ma mh).
      split; [split; [reflexivity |
        apply map.disjoint_putmany_r; split; map_disjoint_auto] |].
      split; [exact Hc' |].
      exists ma, mh.
      split; [split; [reflexivity | map_disjoint_auto] |].
      split; [exact Ha' | exact Hh']. }

    (* Process postcondition of call 2 *)
    intros t2 m2' rets2 [-> [-> [out1' [Hfeval1 [Hbound1 Hsep2]]]]].
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    cbv [list_map get list_map_body]; split; [exact eq_refl |].
    split; [exact eq_refl |].

    (* Assemble QE results *)
    (* Hsep2: (out1' * (x1 * (x0 * (out0' * Rr)))) *)
    destruct Hsep2 as [m2a [m2b [[-> Hd2a] [Hout1 Hrest2a]]]].
    destruct Hrest2a as [m2c [m2d [[-> Hd2b] [Hx1_final Hrest2b]]]].
    destruct Hrest2b as [m2e [m2f [[-> Hd2c] [Hx0_final Hrest2c]]]].
    destruct Hrest2c as [m2g [m2h [[-> Hd2d] [Hout0 Hr'']]]].
    split_all_disjointness.
    pose proof (generic_FElem_length _ _ _ Hout0) as Hlen0.
    pose proof (generic_FElem_length _ _ _ Hout1) as Hlen1.
    pose proof (generic_FElem_length _ _ _ Hx0_final) as Hlenx0.
    pose proof (generic_FElem_length _ _ _ Hx1_final) as Hlenx1.

    exists (out0' ++ out1').
    split.
    { (* feval *)
      change (@AbstractField.feval _ QE_fp _ _ _ _ QE_repr (out0' ++ out1'))
        with (@AbstractField.feval _ base_fp _ _ _ _ base_repr (fst_e (out0' ++ out1')),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr (snd_e (out0' ++ out1'))).
      unfold fst_e, qe_fst_felem, snd_e, qe_snd_felem.
      rewrite firstn_app_le by exact Hlen0.
      rewrite skipn_app_le by exact Hlen0.
      rewrite Hfeval0, Hfeval1. reflexivity. }
    split.
    { (* bounded_by *)
      split; unfold fst_e, snd_e, qe_fst_felem, qe_snd_felem;
        [rewrite firstn_app_le | rewrite skipn_app_le]; try exact Hlen0; assumption. }
    { (* sep: (QE_pout (out0'++out1') * (QE_px x * Rr)) *)
      (* Current mem: putmany m2a (putmany m2c (putmany m2e (putmany m2g m2h))) *)
      (* m2a=out1', m2c=x1, m2e=x0, m2g=out0', m2h=Rr *)
      exists (map.putmany m2g m2a), (map.putmany m2e (map.putmany m2c m2h)).
      split.
      { split.
        - (* Permute [m2a,m2c,m2e,m2g,m2h] -> [m2g,m2a,m2e,m2c,m2h] *)
          rewrite (map.putmany_assoc m2e m2g _).
          rewrite (map.putmany_comm m2e m2g) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m2g m2e _).
          rewrite (map.putmany_assoc m2c m2g _).
          rewrite (map.putmany_comm m2c m2g) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m2g m2c _).
          rewrite (map.putmany_assoc m2a m2g _).
          rewrite (map.putmany_comm m2a m2g) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m2g m2a _).
          rewrite (map.putmany_assoc m2c m2e _).
          rewrite (map.putmany_comm m2c m2e) by map_disjoint_auto.
          rewrite <- (map.putmany_assoc m2e m2c _).
          rewrite <- (map.putmany_assoc m2g m2a _). reflexivity.
        - apply map.disjoint_putmany_l; split;
            [apply map.disjoint_putmany_r; split; [map_disjoint_auto |
             apply map.disjoint_putmany_r; split; map_disjoint_auto] |
             apply map.disjoint_putmany_r; split; [map_disjoint_auto |
             apply map.disjoint_putmany_r; split; map_disjoint_auto]]. }
      split.
      { (* QE FElem for output *)
        apply (qe_raw_FElem_join nonresidue prefix eq_dec_base _ _ _ _ Hlen0 Hlen1).
        exists m2g, m2a.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hout0 | exact Hout1]. }
      { (* (QE_px x * Rr) — need to reconstruct x from fst_e x ++ snd_e x *)
        rewrite <- (@qe_list_decomp _ _ _ _ _ base_fp base_repr x).
        exists (map.putmany m2e m2c), m2h.
        split.
        { split.
          - rewrite (map.putmany_assoc m2e m2c m2h). reflexivity.
          - apply map.disjoint_putmany_l; split; map_disjoint_auto. }
        split.
        { apply (qe_raw_FElem_join nonresidue prefix eq_dec_base _ _ _ _ Hlenx0 Hlenx1).
          exists m2e, m2c.
          split; [split; [reflexivity | map_disjoint_auto] |].
          split; [exact Hx0_final | exact Hx1_final]. }
        { exact Hr''. } } }
  Qed.

  (* ================================================================ *)
  (* QE_felem_copy_ok                                                  *)
  (* ================================================================ *)

  Lemma QE_felem_copy_ok :
    forall functions,
    map.get functions (felem_copy (F := QE)) =
      Some (snd (QE_felem_copy nonresidue prefix eq_dec_base)) ->
    (* Callee: base felem_copy *)
    (forall pout px out x R Rout tr m,
       (FElem_b px x * FElem_b pout out * R)%sep m /\
       (FElem_b pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (FElem_b pout x * Rout)%sep m')) ->
    (forall pout px out x R Rout tr m,
       (FElem_b px x * FElem_b pout out * R)%sep m /\
       (FElem_b pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (FElem_b pout x * Rout)%sep m')) ->
    forall pout px (out x : @felem _ QE_fp _ _ _ _ QE_repr) R Rout tr mem0,
    (@FElem _ QE_fp _ _ _ _ QE_repr px x *
     @FElem _ QE_fp _ _ _ _ QE_repr pout out * R)%sep mem0 /\
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rout)%sep mem0 ->
    WeakestPrecondition.call functions (felem_copy (F := QE)) tr mem0 [pout; px]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        (@FElem _ QE_fp _ _ _ _ QE_repr pout x * Rout)%sep mem').
  Proof.
    intros functions EnvContains HFcopy1 HFcopy2 pout px out x R Rout tr mem0 [Hmem0_1 Hmem0_2].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func QE_felem_copy GenericQuadratic.QE_felem_copy].
    eexists; split; [exact eq_refl |]; repeat straightline.
    (* dexprs for first call *)
    exists [pout; px]; split; [solve_qe_dexprs |].
    (* Decompose precondition 1 *)
    destruct Hmem0_1 as [m_x [m_or [[-> Hd_xor] [Hx Hor]]]].
    destruct Hor as [m_o [m_r [[-> Hd_or] [Ho Hr]]]].
    (* Split QE FElems into base halves *)
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hx)
      as [m_x1 [m_x2 [Hsep_x [Hx1 Hx2]]]].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Ho)
      as [m_o1 [m_o2 [Hsep_o [Ho1 Ho2]]]].
    (* Decompose precondition 2 and use split_diff *)
    destruct Hmem0_2 as [m_o' [m_rout [Hsep2 [Ho' Hrout]]]].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ QE_fp QE_repr pout out m_o Ho) as Hph_o.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ QE_fp QE_repr pout out m_o' Ho') as Hph_o'.
    unfold AbstractField.Placeholder in Hph_o, Hph_o'.
    pose proof (Memory.anybytes_unique_domain _ _ _ _ Hph_o Hph_o') as Hsd.
    destruct Hsep_x as [Heq_x Hd_x12]. destruct Hsep_o as [Heq_o Hd_o12].
    subst m_x m_o.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_xor) as [Hd_x_o Hd_x_r].
    assert (Hsplit_mem : map.split (map.putmany (map.putmany m_x1 m_x2) (map.putmany (map.putmany m_o1 m_o2) m_r)) (map.putmany m_o1 m_o2) (map.putmany (map.putmany m_x1 m_x2) m_r)).
    { split.
      { rewrite map.putmany_assoc.
        rewrite (map.putmany_comm (map.putmany m_x1 m_x2) (map.putmany m_o1 m_o2) Hd_x_o).
        symmetry. apply map.putmany_assoc. }
      { apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x_o k v2 v1 Hg2 Hg1). }
        { exact Hd_or. } } }
    pose proof (proj1 (map.split_comm _ _ _) Hsplit_mem) as Hsplit_mem'.
    pose proof (proj1 (map.split_comm _ _ _) Hsep2) as Hsep2'.
    pose proof (map.split_diff Hsd Hsplit_mem' Hsep2') as [Heq_rout Heq_o'].
    subst m_o'.
    rewrite <- Heq_rout in Hrout.
    clear Heq_rout Hsd Hsep2 Hsep2' Hsplit_mem Hsplit_mem' Hph_o Hph_o' Ho'.
    (* Derive pairwise disjointness *)
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_o) as [Hd_x1_o Hd_x2_o].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x1_o) as [Hd_x1_o1 Hd_x1_o2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x2_o) as [Hd_x2_o1 Hd_x2_o2].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_r) as [Hd_x1_r Hd_x2_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_or) as [Hd_o1_r Hd_o2_r].
    clear Hd_x_o Hd_x_r Hd_or Hd_xor Hd_x1_o Hd_x2_o.
    (* === First base copy call via weaken_call (eq-based Rout) === *)
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 pout px (fst_e out) (fst_e x)
        (fun m => (FElem_b (word.add px base_off) (snd_e x) *
                   (FElem_b (word.add pout base_off) (snd_e out) * R))%sep m)
        (fun m => m = map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o2 m_r)))
        tr).
      split.
      { (* Condition 1: (FElem_b px x0 * FElem_b pout o0 * Frame) mem0 *)
        exists (map.putmany m_x1 m_o1), (map.putmany m_x2 (map.putmany m_o2 m_r)).
        split; [split |].
        { rewrite <- (map.putmany_assoc m_o1 m_o2 m_r).
          rewrite (map.putmany_assoc (map.putmany m_x1 m_x2) m_o1 (map.putmany m_o2 m_r)).
          rewrite (map.disjoint_putmany_commutes _ _ _ Hd_x2_o1).
          symmetry. apply map.putmany_assoc. }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_x12 |].
            apply map.disjoint_putmany_r. split; [exact Hd_x1_o2 | exact Hd_x1_r]. }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x2_o1 k v2 v1 Hg2 Hg1). }
            apply map.disjoint_putmany_r. split; [exact Hd_o12 | exact Hd_o1_r]. } }
        split.
        { exists m_x1, m_o1. split; [split; [reflexivity | exact Hd_x1_o1] |].
          split; [exact Hx1 | exact Ho1]. }
        { exists m_x2, (map.putmany m_o2 m_r).
          split; [split; [reflexivity |] |].
          { apply map.disjoint_putmany_r. split; [exact Hd_x2_o2 | exact Hd_x2_r]. }
          split; [exact Hx2 |].
          exists m_o2, m_r.
          split; [split; [reflexivity | exact Hd_o2_r] |].
          split; [exact Ho2 | exact Hr]. } }
      { (* Condition 2: (FElem_b pout o0 * Rout1_eq) mem0 *)
        exists m_o1, (map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o2 m_r))).
        split; [split |].
        { assert (Hd_x12_o1 : map.disjoint (map.putmany m_x1 m_x2) m_o1)
            by (apply map.disjoint_putmany_l; split; [exact Hd_x1_o1 | exact Hd_x2_o1]).
          rewrite <- (map.putmany_assoc m_o1 m_o2 m_r).
          rewrite (map.putmany_assoc (map.putmany m_x1 m_x2) m_o1 (map.putmany m_o2 m_r)).
          rewrite (map.putmany_comm _ _ Hd_x12_o1).
          rewrite <- (map.putmany_assoc m_o1 (map.putmany m_x1 m_x2) (map.putmany m_o2 m_r)).
          rewrite <- (map.putmany_assoc m_x1 m_x2 (map.putmany m_o2 m_r)).
          reflexivity. }
        { apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x1_o1 k v2 v1 Hg2 Hg1). }
          apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x2_o1 k v2 v1 Hg2 Hg1). }
          apply map.disjoint_putmany_r. split; [exact Hd_o12 | exact Hd_o1_r]. }
        split; [exact Ho1 | exact eq_refl]. } }
    (* === Process postcondition of first call === *)
    intros t' m' rets [Htr [Hrets Hsep_post1]].
    subst rets t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for second call *)
    exists [word.add pout base_off; word.add px base_off]; split; [solve_qe_dexprs |].
    (* Destruct first postcondition *)
    destruct Hsep_post1 as [m_new1 [m_frame1 [[Heq_p1 Hd_p1] [Hnew1 Hframe1]]]].
    subst m_frame1 m'.
    (* Derive disjointness for m_new1 vs original sub-memories *)
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p1) as [Hd_n1_x1 Hd_n1_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest) as [Hd_n1_x2 Hd_n1_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest2) as [Hd_n1_o2 Hd_n1_r].
    clear Hd_n1_rest Hd_n1_rest2.
    (* === Second base copy call (eq-based Rout) === *)
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 (word.add pout base_off) (word.add px base_off)
        (snd_e out) (snd_e x)
        (fun m => (FElem_b pout (fst_e x) * (FElem_b px (fst_e x) * R))%sep m)
        (fun m => m = map.putmany m_new1 (map.putmany m_x1 (map.putmany m_x2 m_r)))
        tr).
      split.
      { (* Condition 1: (FElem_b (px+off) (snd x) * FElem_b (pout+off) (snd out) * R2) m' *)
        assert (Hd_n1x1_x2o2 : map.disjoint (map.putmany m_new1 m_x1) (map.putmany m_x2 m_o2)).
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_n1_x2 | exact Hd_n1_o2]. }
          { apply map.disjoint_putmany_r. split; [exact Hd_x12 | exact Hd_x1_o2]. } }
        exists (map.putmany m_x2 m_o2), (map.putmany m_new1 (map.putmany m_x1 m_r)).
        split; [split |].
        { rewrite (map.putmany_assoc m_new1 m_x1).
          rewrite (map.putmany_assoc m_x2 m_o2 m_r).
          rewrite (map.putmany_assoc (map.putmany m_new1 m_x1) (map.putmany m_x2 m_o2) m_r).
          rewrite (map.putmany_comm _ _ Hd_n1x1_x2o2).
          rewrite <- (map.putmany_assoc (map.putmany m_x2 m_o2) (map.putmany m_new1 m_x1) m_r).
          rewrite <- (map.putmany_assoc m_new1 m_x1 m_r).
          reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n1_x2 k v2 v1 Hg2 Hg1). }
            apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x12 k v2 v1 Hg2 Hg1). }
            exact Hd_x2_r. }
          { apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n1_o2 k v2 v1 Hg2 Hg1). }
            apply map.disjoint_putmany_r. split.
            { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x1_o2 k v2 v1 Hg2 Hg1). }
            exact Hd_o2_r. } }
        split.
        { exists m_x2, m_o2. split; [split; [reflexivity | exact Hd_x2_o2] |].
          split; [exact Hx2 | exact Ho2]. }
        { exists m_new1, (map.putmany m_x1 m_r).
          split; [split; [reflexivity |] |].
          { apply map.disjoint_putmany_r. split; [exact Hd_n1_x1 | exact Hd_n1_r]. }
          split; [exact Hnew1 |].
          exists m_x1, m_r.
          split; [split; [reflexivity | exact Hd_x1_r] |].
          split; [exact Hx1 | exact Hr]. } }
      { (* Condition 2: (FElem_b (pout+off) (snd out) * Rout2_eq) m' *)
        exists m_o2, (map.putmany m_new1 (map.putmany m_x1 (map.putmany m_x2 m_r))).
        split; [split |].
        { rewrite (map.putmany_assoc m_x2 m_o2 m_r).
          rewrite (map.putmany_comm m_x2 m_o2 Hd_x2_o2).
          rewrite <- (map.putmany_assoc m_o2 m_x2 m_r).
          rewrite (map.putmany_assoc m_x1 m_o2).
          rewrite (map.putmany_comm m_x1 m_o2 Hd_x1_o2).
          rewrite <- (map.putmany_assoc m_o2 m_x1).
          rewrite (map.putmany_assoc m_new1 m_o2).
          rewrite (map.putmany_comm m_new1 m_o2 Hd_n1_o2).
          rewrite <- (map.putmany_assoc m_o2 m_new1).
          reflexivity. }
        { apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n1_o2 k v2 v1 Hg2 Hg1). }
          apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x1_o2 k v2 v1 Hg2 Hg1). }
          apply map.disjoint_putmany_r. split.
          { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_x2_o2 k v2 v1 Hg2 Hg1). }
          { exact Hd_o2_r. } }
        split; [exact Ho2 | exact eq_refl]. } }
    (* === Process postcondition of second call and close proof === *)
    intros t'' m'' rets [Htr2 [Hrets Hsep_post2]].
    subst rets.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    cbv [list_map get]. split. { exact Htr2. }
    split. { exact eq_refl. }
    (* Destruct second postcondition *)
    destruct Hsep_post2 as [m_new2 [m_frame2 [[Heq_p2 Hd_p2] [Hnew2 Hframe2]]]].
    subst m_frame2.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p2) as [Hd_n2_n1 Hd_n2_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest) as [Hd_n2_x1 Hd_n2_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest2) as [Hd_n2_x2 Hd_n2_r].
    clear Hd_n2_rest Hd_n2_rest2.
    (* Rewrite x = fst_e x ++ snd_e x *)
    rewrite <- (@qe_list_decomp _ _ _ _ _ base_fp base_repr x).
    subst m''.
    (* Provide witnesses for sep *)
    exists (map.putmany m_new1 m_new2), (map.putmany (map.putmany m_x1 m_x2) m_r).
    split; [split |].
    { (* equation: m'' = putmany (putmany m_new1 m_new2) (putmany (putmany m_x1 m_x2) m_r) *)
      rewrite (map.putmany_assoc m_new2 m_new1).
      rewrite (map.putmany_comm m_new2 m_new1 Hd_n2_n1).
      rewrite (map.putmany_assoc m_x1 m_x2 m_r).
      reflexivity. }
    { apply map.disjoint_putmany_l. split.
      { apply map.disjoint_putmany_r. split.
        { apply map.disjoint_putmany_r. split; [exact Hd_n1_x1 | exact Hd_n1_x2]. }
        { exact Hd_n1_r. } }
      { apply map.disjoint_putmany_r. split.
        { apply map.disjoint_putmany_r. split; [exact Hd_n2_x1 | exact Hd_n2_x2]. }
        { exact Hd_n2_r. } } }
    split.
    { (* QE FElem join *)
      pose proof (generic_FElem_length _ _ _ Hnew1) as Hlen1.
      pose proof (generic_FElem_length _ _ _ Hnew2) as Hlen2.
      apply (qe_raw_FElem_join nonresidue prefix eq_dec_base _ _ _ _ Hlen1 Hlen2).
      exists m_new1, m_new2.
      split; [split; [reflexivity |] |].
      { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n2_n1 k v2 v1 Hg2 Hg1). }
      split; [exact Hnew1 | exact Hnew2]. }
    { exact Hrout. }
    Qed.

  (* ================================================================ *)
  (* QE_add_ok                                                         *)
  (* ================================================================ *)

  Lemma QE_add_ok :
    forall functions,
    map.get functions (add (F := QE)) =
      Some (snd (QE_add nonresidue prefix eq_dec_base)) ->
    (* Callee: base felem_copy (for stackalloc copies) *)
    (forall pout px out x R Rout tr m,
       (FElem_b px x * FElem_b pout out * R)%sep m /\
       (FElem_b pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (FElem_b pout x * Rout)%sep m')) ->
    (* Callee: QE felem_copy *)
    (forall pout px (out x : @felem _ QE_fp _ _ _ _ QE_repr) R Rout tr m,
       (@FElem _ QE_fp _ _ _ _ QE_repr px x *
        @FElem _ QE_fp _ _ _ _ QE_repr pout out * R)%sep m /\
       (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := QE)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (@FElem _ QE_fp _ _ _ _ QE_repr pout x * Rout)%sep m')) ->
    (* Callee: base add *)
    (forall pout px py out x y Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) x ->
       @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) y ->
       (exists Rx, (FElem_b px x * Rx)%sep m) ->
       (exists Ry, (FElem_b py y * Ry)%sep m) ->
       (FElem_b pout out * Rr)%sep m ->
       WeakestPrecondition.call functions (add (F := BaseField)) tr m [pout; px; py]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fadd _ base_fp (@feval _ base_fp _ _ _ _ base_repr x)
                                          (@feval _ base_fp _ _ _ _ base_repr y) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * Rr)%sep m')) ->
    forall pout px py (out x y : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) x ->
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) y ->
    (exists Rx, (@FElem _ QE_fp _ _ _ _ QE_repr px x * Rx)%sep mem0) ->
    (exists Ry, (@FElem _ QE_fp _ _ _ _ QE_repr py y * Ry)%sep mem0) ->
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (add (F := QE)) tr mem0 [pout; px; py]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' =
                       @Fadd _ QE_fp (@feval _ QE_fp _ _ _ _ QE_repr x)
                                     (@feval _ QE_fp _ _ _ _ QE_repr y) /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFbasecopy HFqecopy HFadd
      pout px py out x y Rr tr mem0
      [Hbx0 Hbx1] [Hby0 Hby1] [Rx Hmemx] [Ry Hmemy] Hmemout.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func QE_add GenericQuadratic.QE_add].
    eexists; split; [exact eq_refl |]; repeat straightline.
    (* === First stackalloc: allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Second stackalloc: allocy === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    (* Convert anybytes to QE FElems *)
    pose proof (@AbstractField.FElem_from_bytes _ QE_fp _ _ _ _ QE_repr word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ QE_fp _ _ _ _ QE_repr word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    (* Decompose splits *)
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_mem0_sY Hd_sX_sY].
    (* Decompose Hmemx *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfelem_x Hrx]]]].
    destruct Hmemx_sp as [Heq_mem0 Hd_xrx]. subst mem0.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_mem0_sY) as [Hd_x_sY Hd_rx_sY].
    (* === First QE copy call: inx → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFqecopy allocx px allocx_val x
           (fun m => (Rx * @FElem _ QE_fp _ _ _ _ QE_repr allocy allocy_val)%sep m)
           (eq (map.putmany (map.putmany m_x m_rx) mStackY))
           tr).
         split.
         { (* Condition 1: (FElem px x * FElem allocx allocx_val * R1) m2 *)
           exists (map.putmany m_x mStackX), (map.putmany m_rx mStackY).
           split; [split |].
           { rewrite (map.disjoint_putmany_commutes m_x m_rx mStackX Hd_rx_sX).
             rewrite <- map.putmany_assoc. reflexivity. }
           { apply map.disjoint_putmany_l. split.
             { apply map.disjoint_putmany_r. split; [exact Hd_xrx | exact Hd_x_sY]. }
             { apply map.disjoint_putmany_r. split.
               { unfold map.disjoint in *; intros k v1 v2 H1 H2;
                 exact (Hd_rx_sX k v2 v1 H2 H1). }
               { exact Hd_sX_sY. } } }
           split.
           { exists m_x, mStackX.
             split; [split; [reflexivity | exact Hd_x_sX] |].
             split; [exact Hfelem_x | exact Hallocx]. }
           { exists m_rx, mStackY.
             split; [split; [reflexivity | exact Hd_rx_sY] |].
             split; [exact Hrx | exact Hallocy]. } }
         { (* Condition 2: (FElem allocx allocx_val * Rout1) m2 *)
           exists mStackX, (map.putmany (map.putmany m_x m_rx) mStackY).
           split; [split |].
           { rewrite (map.disjoint_putmany_commutes _ _ _ Hd_sX_sY).
             apply map.putmany_comm.
             apply map.disjoint_putmany_l. split; [exact Hd_m1 |].
             unfold map.disjoint in *; intros k v1 v2 H1 H2;
             exact (Hd_sX_sY k v2 v1 H2 H1). }
           { apply map.disjoint_putmany_r. split.
             { unfold map.disjoint in *; intros k v1 v2 H1 H2;
               exact (Hd_m1 k v2 v1 H2 H1). }
             { exact Hd_sX_sY. } }
           split; [exact Hallocx | exact eq_refl]. } }
    (* Process first copy postcondition *)
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets t'.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* Decompose copy1 postcondition *)
    destruct Hsep_copy1 as [m_new1 [m_frame1 [[Heq_m' Hd_n1_f1] [Hfelem_allocx Hframe1]]]].
    subst m_frame1 m'.
    (* Decompose Hmemy *)
    destruct Hmemy as [m_y [m_ry [Hmemy_sp [Hfelem_y Hry]]]].
    destruct Hmemy_sp as [Heq_mem0_y Hd_yry].
    (* Derive disjointness facts *)
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_f1) as [Hd_n1_mem0 Hd_n1_sY].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_x Hd_n1_rx].
    rewrite Heq_mem0_y in Hd_n1_mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_y Hd_n1_ry].
    rewrite Heq_mem0_y in Hd_mem0_sY.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_mem0_sY) as [Hd_y_sY Hd_ry_sY'].
    (* dexprs for second copy *)
    exists [allocy; py]. split.
    1: { subst l0 l.
         eexists. split. { apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFqecopy allocy py allocy_val y
           (fun m => (@FElem _ QE_fp _ _ _ _ QE_repr allocx x * Ry)%sep m)
           (eq (map.putmany m_new1 (map.putmany m_y m_ry)))
           tr).
         split.
         { (* Condition 1: (FElem py y * FElem allocy allocy_val * R2) *)
           rewrite Heq_mem0_y.
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
         { (* Condition 2: (FElem allocy allocy_val * Rout2) *)
           rewrite Heq_mem0_y.
           exists mStackY, (map.putmany m_new1 (map.putmany m_y m_ry)).
           split; [split |].
           { transitivity (map.putmany (map.putmany m_new1 (map.putmany m_y m_ry)) mStackY).
             { apply map.putmany_assoc. }
             apply map.putmany_comm.
             apply map.disjoint_putmany_l. split; [exact Hd_n1_sY | exact Hd_mem0_sY]. }
           { apply map.disjoint_putmany_r. split.
             { unfold map.disjoint in *; intros k v1 v2 H1 H2;
               exact (Hd_n1_sY k v2 v1 H2 H1). }
             { unfold map.disjoint in *; intros k v1 v2 H1 H2;
               exact (Hd_mem0_sY k v2 v1 H2 H1). } }
           split; [exact Hallocy | exact eq_refl]. } }
    (* Process second copy postcondition *)
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* Decompose copy2 postcondition *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    (* Split QE FElems into base halves *)
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax1 [m_ax2 [Hsp_ax [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax as [Heq_new1 Hd_ax].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay1 [m_ay2 [Hsp_ay [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay as [Heq_new2 Hd_ay].
    (* Decompose Hmemout *)
    rewrite Heq_mem0_y in Hmemout.
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_yr Hd_out_rr].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o1 [m_o2 [Hsp_out [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_out as [Heq_out Hd_o12].
    (* Derive disjointness for atomic regions *)
    subst m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* Build 7-way sep fact *)
    assert (Hsep7 : ((FElem_b allocy (fst_e y) *
      FElem_b (word.add allocy base_off) (snd_e y)) *
      ((FElem_b allocx (fst_e x) *
        FElem_b (word.add allocx base_off) (snd_e x)) *
        ((FElem_b pout (fst_e out) *
          FElem_b (word.add pout base_off) (snd_e out)) * Rr)))%sep
      (map.putmany (map.putmany m_ay1 m_ay2)
        (map.putmany (map.putmany m_ax1 m_ax2)
          (map.putmany (map.putmany m_o1 m_o2) m_rr)))).
    { exists (map.putmany m_ay1 m_ay2),
        (map.putmany (map.putmany m_ax1 m_ax2)
          (map.putmany (map.putmany m_o1 m_o2) m_rr)).
      split; [split; [reflexivity | exact Hd_n2_f2] |].
      split.
      { exists m_ay1, m_ay2.
        split; [split; [reflexivity | exact Hd_ay] |].
        split; [exact Hfe_ay1 | exact Hfe_ay2]. }
      exists (map.putmany m_ax1 m_ax2),
        (map.putmany (map.putmany m_o1 m_o2) m_rr).
      split; [split; [reflexivity | exact Hd_n1_mem0] |].
      split.
      { exists m_ax1, m_ax2.
        split; [split; [reflexivity | exact Hd_ax] |].
        split; [exact Hfe_ax1 | exact Hfe_ax2]. }
      exists (map.putmany m_o1 m_o2), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o1, m_o2.
        split; [split; [reflexivity | exact Hd_o12] |].
        split; [exact Hfe_o1 | exact Hfe_o2]. }
      exact Hrr_out. }
    (* === First base add call === *)
    exists [pout; allocx; allocy]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd pout allocx allocy
           (fst_e out) (fst_e x) (fst_e y)
           _ tr).
         { exact Hbx0. }
         { exact Hby0. }
         { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         { pose proof Hsep7 as H'. ecancel_assumption. } }
    (* Process first add postcondition *)
    intros t_add1 m_add1 rets_add1 [Hrets_add1 [Htr_add1 [out1 [Hfeval1 [Hbound1 Hsep_add1]]]]].
    subst rets_add1 t_add1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second base add call === *)
    exists [word.add pout base_off; word.add allocx base_off;
            word.add allocy base_off].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map qe_expr_2nd WeakestPrecondition.expr WeakestPrecondition.expr_body Semantics.interp_binop literal dlet.dlet].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd (word.add pout base_off)
           (word.add allocx base_off) (word.add allocy base_off)
           (snd_e out) (snd_e x) (snd_e y)
           _ tr).
         { exact Hbx1. }
         { exact Hby1. }
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         { pose proof Hsep_add1 as H'. ecancel_assumption. } }
    (* Process second add postcondition *)
    intros t_add2 m_add2 rets_add2 [Hrets_add2 [Htr_add2 [out2 [Hfeval2 [Hbound2 Hsep_add2]]]]].
    subst rets_add2 t_add2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    (* Destructure Hsep_add2 into 7 map components *)
    destruct Hsep_add2 as [m_A [m_rest1 [[Heq_add2 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_F' [m_G' [[Heq_r5 Hd_FG] [HF' HG']]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_add2.
    (* Derive pairwise disjointness from chain *)
    pose proof (proj1 (map.disjoint_putmany_r m_C m_D _) Hd_C) as [Hd_CD Hd_C4].
    pose proof (proj1 (map.disjoint_putmany_r m_D m_E _) Hd_D) as [Hd_DE Hd_D5].
    pose proof (proj1 (map.disjoint_putmany_r m_E m_F' m_G') Hd_E) as [Hd_EF' Hd_EG'].
    pose proof (proj1 (map.disjoint_putmany_r m_B m_C _) Hd_B) as [Hd_BC Hd_B_rest].
    pose proof (proj1 (map.disjoint_putmany_r m_B m_D _) Hd_B_rest) as [Hd_BD Hd_B_rest2].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_B _) Hd_A) as [Hd_AB Hd_A_rest].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_C _) Hd_A_rest) as [Hd_AC Hd_A_rest2].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_D _) Hd_A_rest2) as [Hd_AD Hd_A_rest3].
    pose proof (proj1 (map.disjoint_putmany_r m_B m_E _) Hd_B_rest2) as [Hd_BE Hd_B_rest3].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_E _) Hd_A_rest3) as [Hd_AE Hd_A_rest4].
    pose proof (proj1 (map.disjoint_putmany_r m_C m_E _) Hd_C4) as [Hd_CE Hd_C5].
    pose proof (proj1 (map.disjoint_putmany_r m_C m_F' m_G') Hd_C5) as [Hd_CF' Hd_CG'].
    pose proof (proj1 (map.disjoint_putmany_r m_D m_F' m_G') Hd_D5) as [Hd_DF' Hd_DG'].
    pose proof (proj1 (map.disjoint_putmany_r m_B m_F' m_G') Hd_B_rest3) as [Hd_BF' Hd_BG'].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_F' m_G') Hd_A_rest4) as [Hd_AF' Hd_AG'].
    (* Get lengths for FElem joins *)
    pose proof (generic_FElem_length _ _ _ HC) as Hlen_yC.
    pose proof (generic_FElem_length _ _ _ HD) as Hlen_yD.
    pose proof (generic_FElem_length _ _ _ HE) as Hlen_xE.
    pose proof (generic_FElem_length _ _ _ HF') as Hlen_xF'.
    (* === Stack dealloc allocy === *)
    assert (Hjoin_y : (FElem_b allocy (fst_e y) *
      FElem_b (word.add allocy base_off) (snd_e y))%sep
      (map.putmany m_C m_D)).
    { exists m_C, m_D. split; [split; [reflexivity | exact Hd_CD] |].
      split; [exact HC | exact HD]. }
    pose proof (qe_raw_FElem_join nonresidue prefix eq_dec_base allocy (fst_e y) (snd_e y) _
      Hlen_yC Hlen_yD Hjoin_y) as Hqe_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      QE_fp QE_repr allocy (fst_e y ++ snd_e y)
      (map.putmany m_C m_D) Hqe_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_E (map.putmany m_F' m_G')))),
           (map.putmany m_C m_D).
    split. { exact Hanybytes_y. }
    split.
    { split.
      { rewrite (map.putmany_assoc m_C m_D).
        rewrite (map.putmany_assoc m_B (map.putmany m_C m_D)).
        rewrite (map.putmany_comm m_B (map.putmany m_C m_D)).
        2: { apply map.disjoint_putmany_r. split; [exact Hd_BC | exact Hd_BD]. }
        rewrite <- (map.putmany_assoc (map.putmany m_C m_D) m_B).
        rewrite (map.putmany_assoc m_A (map.putmany m_C m_D)).
        rewrite (map.putmany_comm m_A (map.putmany m_C m_D)).
        2: { apply map.disjoint_putmany_r. split; [exact Hd_AC | exact Hd_AD]. }
        rewrite <- (map.putmany_assoc (map.putmany m_C m_D) m_A).
        apply map.putmany_comm.
        apply map.disjoint_putmany_l. split.
        { apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_AC). }
          apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_BC). }
          apply map.disjoint_putmany_r. split; [exact Hd_CE |].
          apply map.disjoint_putmany_r. split; [exact Hd_CF' | exact Hd_CG']. }
        { apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_AD). }
          apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_BD). }
          apply map.disjoint_putmany_r. split; [exact Hd_DE |].
          apply map.disjoint_putmany_r. split; [exact Hd_DF' | exact Hd_DG']. } }
      { apply map.disjoint_putmany_r. split.
        { apply map.disjoint_putmany_l. split; [exact Hd_AC |].
          apply map.disjoint_putmany_l. split; [exact Hd_BC |].
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_CE). }
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_CF'). }
          { apply (proj1 (map.disjoint_comm _ _) Hd_CG'). } }
        { apply map.disjoint_putmany_l. split; [exact Hd_AD |].
          apply map.disjoint_putmany_l. split; [exact Hd_BD |].
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_DE). }
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_DF'). }
          { apply (proj1 (map.disjoint_comm _ _) Hd_DG'). } } } }
    (* === Stack dealloc allocx === *)
    assert (Hjoin_x : (FElem_b allocx (fst_e x) *
      FElem_b (word.add allocx base_off) (snd_e x))%sep
      (map.putmany m_E m_F')).
    { exists m_E, m_F'. split; [split; [reflexivity | exact Hd_EF'] |].
      split; [exact HE | exact HF']. }
    pose proof (qe_raw_FElem_join nonresidue prefix eq_dec_base allocx (fst_e x) (snd_e x) _
      Hlen_xE Hlen_xF' Hjoin_x) as Hqe_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      QE_fp QE_repr allocx (fst_e x ++ snd_e x)
      (map.putmany m_E m_F') Hqe_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_B m_G')),
           (map.putmany m_E m_F').
    split. { exact Hanybytes_x. }
    split.
    { split.
      { rewrite (map.putmany_assoc m_E m_F' m_G').
        rewrite (map.putmany_assoc m_B (map.putmany m_E m_F')).
        rewrite (map.putmany_comm m_B (map.putmany m_E m_F')).
        2: { apply map.disjoint_putmany_r. split; [exact Hd_BE | exact Hd_BF']. }
        rewrite <- (map.putmany_assoc (map.putmany m_E m_F') m_B).
        rewrite (map.putmany_assoc m_A (map.putmany m_E m_F')).
        rewrite (map.putmany_comm m_A (map.putmany m_E m_F')).
        2: { apply map.disjoint_putmany_r. split; [exact Hd_AE | exact Hd_AF']. }
        rewrite <- (map.putmany_assoc (map.putmany m_E m_F') m_A).
        apply map.putmany_comm.
        apply map.disjoint_putmany_l. split.
        { apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_AE). }
          apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_BE). }
          { exact Hd_EG'. } }
        { apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_AF'). }
          apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_BF'). }
          { exact Hd_FG. } } }
      { apply map.disjoint_putmany_r. split.
        { apply map.disjoint_putmany_l. split; [exact Hd_AE |].
          apply map.disjoint_putmany_l. split; [exact Hd_BE |].
          apply (proj1 (map.disjoint_comm _ _) Hd_EG'). }
        { apply map.disjoint_putmany_l. split; [exact Hd_AF' |].
          apply map.disjoint_putmany_l. split; [exact Hd_BF' |].
          apply (proj1 (map.disjoint_comm _ _) Hd_FG). } } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out1 ++ out2).
    pose proof (generic_FElem_length _ _ _ HB) as Hlen_out1.
    pose proof (generic_FElem_length _ _ _ HA) as Hlen_out2.
    split.
    { (* feval *)
      change (@AbstractField.feval _ QE_fp _ _ _ _ QE_repr (out1 ++ out2))
        with (@AbstractField.feval _ base_fp _ _ _ _ base_repr (fst_e (out1 ++ out2)),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr (snd_e (out1 ++ out2))).
      unfold fst_e, qe_fst_felem, snd_e, qe_snd_felem.
      rewrite firstn_app_le by exact Hlen_out1.
      rewrite skipn_app_le by exact Hlen_out1.
      rewrite Hfeval1, Hfeval2. reflexivity. }
    split.
    { (* bounded_by *)
      split; unfold fst_e, snd_e, qe_fst_felem, qe_snd_felem;
        [rewrite firstn_app_le | rewrite skipn_app_le]; try exact Hlen_out1; assumption. }
    { (* sep: (QE pout (out1++out2) * Rr) *)
      assert (Hfe_join : (FElem_b pout out1 *
        FElem_b (word.add pout base_off) out2)%sep
        (map.putmany m_B m_A)).
      { exists m_B, m_A. split; [split; [reflexivity |] |].
        { apply (proj1 (map.disjoint_comm _ _) Hd_AB). }
        split; [exact HB | exact HA]. }
      pose proof (qe_raw_FElem_join nonresidue prefix eq_dec_base pout out1 out2 _ Hlen_out1 Hlen_out2 Hfe_join) as Hqe_out.
      exists (map.putmany m_B m_A), m_G'.
      split; [split |].
      { rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. exact Hd_AB. }
      { apply map.disjoint_putmany_l. split; [exact Hd_BG' | exact Hd_AG']. }
      split; [exact Hqe_out | exact HG']. }
    Qed.

  (* ================================================================ *)
  (* QE_sub_ok                                                         *)
  (* ================================================================ *)

  Lemma QE_sub_ok :
    forall functions,
    map.get functions (sub (F := QE)) =
      Some (snd (QE_sub nonresidue prefix eq_dec_base)) ->
    (* Callee: base felem_copy *)
    (forall pout px out x R Rout tr m,
       (FElem_b px x * FElem_b pout out * R)%sep m /\
       (FElem_b pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := BaseField)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (FElem_b pout x * Rout)%sep m')) ->
    (* Callee: QE felem_copy *)
    (forall pout px (out x : @felem _ QE_fp _ _ _ _ QE_repr) R Rout tr m,
       (@FElem _ QE_fp _ _ _ _ QE_repr px x *
        @FElem _ QE_fp _ _ _ _ QE_repr pout out * R)%sep m /\
       (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rout)%sep m ->
       WeakestPrecondition.call functions (felem_copy (F := QE)) tr m [pout; px]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           (@FElem _ QE_fp _ _ _ _ QE_repr pout x * Rout)%sep m')) ->
    (* Callee: base sub *)
    (forall pout px py out x y Rr tr m,
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) x ->
       @bounded_by _ base_fp _ _ _ _ base_repr (@tight_bounds _ base_fp _ _ _ _ base_repr) y ->
       (exists Rx, (FElem_b px x * Rx)%sep m) ->
       (exists Ry, (FElem_b py y * Ry)%sep m) ->
       (FElem_b pout out * Rr)%sep m ->
       WeakestPrecondition.call functions (sub (F := BaseField)) tr m [pout; px; py]
         (fun tr' m' rets => tr = tr' /\ rets = nil /\
           exists out', @feval _ base_fp _ _ _ _ base_repr out' =
                          @Fsub _ base_fp (@feval _ base_fp _ _ _ _ base_repr x)
                                          (@feval _ base_fp _ _ _ _ base_repr y) /\
             @bounded_by _ base_fp _ _ _ _ base_repr (@loose_bounds _ base_fp _ _ _ _ base_repr) out' /\
             (FElem_b pout out' * Rr)%sep m')) ->
    forall pout px py (out x y : @felem _ QE_fp _ _ _ _ QE_repr) Rr tr mem0,
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@tight_bounds _ QE_fp _ _ _ _ QE_repr) x ->
    @bounded_by _ QE_fp _ _ _ _ QE_repr (@tight_bounds _ QE_fp _ _ _ _ QE_repr) y ->
    (exists Rx, (@FElem _ QE_fp _ _ _ _ QE_repr px x * Rx)%sep mem0) ->
    (exists Ry, (@FElem _ QE_fp _ _ _ _ QE_repr py y * Ry)%sep mem0) ->
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * Rr)%sep mem0 ->
    WeakestPrecondition.call functions (sub (F := QE)) tr mem0 [pout; px; py]
      (fun tr' mem' rets => tr = tr' /\ rets = nil /\
        exists out', @feval _ QE_fp _ _ _ _ QE_repr out' =
                       @Fsub _ QE_fp (@feval _ QE_fp _ _ _ _ QE_repr x)
                                     (@feval _ QE_fp _ _ _ _ QE_repr y) /\
          @bounded_by _ QE_fp _ _ _ _ QE_repr (@loose_bounds _ QE_fp _ _ _ _ QE_repr) out' /\
          (@FElem _ QE_fp _ _ _ _ QE_repr pout out' * Rr)%sep mem').
  Proof.
    intros functions EnvContains HFbasecopy HFqecopy HFsub
      pout px py out x y Rr tr mem0
      [Hbx0 Hbx1] [Hby0 Hby1] [Rx Hmemx] [Ry Hmemy] Hmemout.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func QE_sub GenericQuadratic.QE_sub].
    eexists; split; [exact eq_refl |]; repeat straightline.
    (* === First stackalloc: allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Second stackalloc: allocy === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    (* Convert anybytes to QE FElems *)
    pose proof (@AbstractField.FElem_from_bytes _ QE_fp _ _ _ _ QE_repr word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ QE_fp _ _ _ _ QE_repr word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    (* Decompose splits *)
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_mem0_sY Hd_sX_sY].
    (* Decompose Hmemx *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfelem_x Hrx]]]].
    destruct Hmemx_sp as [Heq_mem0 Hd_xrx]. subst mem0.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_mem0_sY) as [Hd_x_sY Hd_rx_sY].
    (* === First QE copy call: inx → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFqecopy allocx px allocx_val x
           (fun m => (Rx * @FElem _ QE_fp _ _ _ _ QE_repr allocy allocy_val)%sep m)
           (eq (map.putmany (map.putmany m_x m_rx) mStackY))
           tr).
         split.
         { exists (map.putmany m_x mStackX), (map.putmany m_rx mStackY).
           split; [split |].
           { rewrite (map.disjoint_putmany_commutes m_x m_rx mStackX Hd_rx_sX).
             rewrite <- map.putmany_assoc. reflexivity. }
           { apply map.disjoint_putmany_l. split.
             { apply map.disjoint_putmany_r. split; [exact Hd_xrx | exact Hd_x_sY]. }
             { apply map.disjoint_putmany_r. split.
               { unfold map.disjoint in *; intros k v1 v2 H1 H2;
                 exact (Hd_rx_sX k v2 v1 H2 H1). }
               { exact Hd_sX_sY. } } }
           split.
           { exists m_x, mStackX.
             split; [split; [reflexivity | exact Hd_x_sX] |].
             split; [exact Hfelem_x | exact Hallocx]. }
           { exists m_rx, mStackY.
             split; [split; [reflexivity | exact Hd_rx_sY] |].
             split; [exact Hrx | exact Hallocy]. } }
         { exists mStackX, (map.putmany (map.putmany m_x m_rx) mStackY).
           split; [split |].
           { rewrite (map.disjoint_putmany_commutes _ _ _ Hd_sX_sY).
             apply map.putmany_comm.
             apply map.disjoint_putmany_l. split; [exact Hd_m1 |].
             unfold map.disjoint in *; intros k v1 v2 H1 H2;
             exact (Hd_sX_sY k v2 v1 H2 H1). }
           { apply map.disjoint_putmany_r. split.
             { unfold map.disjoint in *; intros k v1 v2 H1 H2;
               exact (Hd_m1 k v2 v1 H2 H1). }
             { exact Hd_sX_sY. } }
           split; [exact Hallocx | exact eq_refl]. } }
    (* Process first copy postcondition *)
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets t'.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    destruct Hsep_copy1 as [m_new1 [m_frame1 [[Heq_m' Hd_n1_f1] [Hfelem_allocx Hframe1]]]].
    subst m_frame1 m'.
    destruct Hmemy as [m_y [m_ry [Hmemy_sp [Hfelem_y Hry]]]].
    destruct Hmemy_sp as [Heq_mem0_y Hd_yry].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_f1) as [Hd_n1_mem0 Hd_n1_sY].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_x Hd_n1_rx].
    rewrite Heq_mem0_y in Hd_n1_mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_y Hd_n1_ry].
    rewrite Heq_mem0_y in Hd_mem0_sY.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_mem0_sY) as [Hd_y_sY Hd_ry_sY'].
    (* Second QE copy call: iny -> allocy *)
    exists [allocy; py]. split.
    1: { subst l0 l.
         eexists. split. { apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFqecopy allocy py allocy_val y
           (fun m => (@FElem _ QE_fp _ _ _ _ QE_repr allocx x * Ry)%sep m)
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
             apply map.disjoint_putmany_l. split; [exact Hd_n1_sY | exact Hd_mem0_sY]. }
           { apply map.disjoint_putmany_r. split.
             { unfold map.disjoint in *; intros k v1 v2 H1 H2;
               exact (Hd_n1_sY k v2 v1 H2 H1). }
             { unfold map.disjoint in *; intros k v1 v2 H1 H2;
               exact (Hd_mem0_sY k v2 v1 H2 H1). } }
           split; [exact Hallocy | exact eq_refl]. } }
    (* Process second copy postcondition *)
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax1 [m_ax2 [Hsp_ax [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax as [Heq_new1 Hd_ax].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay1 [m_ay2 [Hsp_ay [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay as [Heq_new2 Hd_ay].
    rewrite Heq_mem0_y in Hmemout.
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_yr Hd_out_rr].
    pose proof (qe_raw_FElem_split nonresidue prefix eq_dec_base _ _ _ Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o1 [m_o2 [Hsp_out [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_out as [Heq_out Hd_o12].
    subst m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* Build 7-way sep fact *)
    assert (Hsep7 : ((FElem_b allocy (fst_e y) *
      FElem_b (word.add allocy base_off) (snd_e y)) *
      ((FElem_b allocx (fst_e x) *
        FElem_b (word.add allocx base_off) (snd_e x)) *
        ((FElem_b pout (fst_e out) *
          FElem_b (word.add pout base_off) (snd_e out)) * Rr)))%sep
      (map.putmany (map.putmany m_ay1 m_ay2)
        (map.putmany (map.putmany m_ax1 m_ax2)
          (map.putmany (map.putmany m_o1 m_o2) m_rr)))).
    { exists (map.putmany m_ay1 m_ay2),
        (map.putmany (map.putmany m_ax1 m_ax2)
          (map.putmany (map.putmany m_o1 m_o2) m_rr)).
      split; [split; [reflexivity | exact Hd_n2_f2] |].
      split.
      { exists m_ay1, m_ay2.
        split; [split; [reflexivity | exact Hd_ay] |].
        split; [exact Hfe_ay1 | exact Hfe_ay2]. }
      exists (map.putmany m_ax1 m_ax2),
        (map.putmany (map.putmany m_o1 m_o2) m_rr).
      split; [split; [reflexivity | exact Hd_n1_mem0] |].
      split.
      { exists m_ax1, m_ax2.
        split; [split; [reflexivity | exact Hd_ax] |].
        split; [exact Hfe_ax1 | exact Hfe_ax2]. }
      exists (map.putmany m_o1 m_o2), m_rr.
      split; [split; [reflexivity | exact Hd_out_rr] |].
      split.
      { exists m_o1, m_o2.
        split; [split; [reflexivity | exact Hd_o12] |].
        split; [exact Hfe_o1 | exact Hfe_o2]. }
      exact Hrr_out. }
    (* === First base sub call === *)
    exists [pout; allocx; allocy]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map WeakestPrecondition.expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub pout allocx allocy
           (fst_e out) (fst_e x) (fst_e y)
           _ tr).
         { exact Hbx0. }
         { exact Hby0. }
         { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         { pose proof Hsep7 as H'. ecancel_assumption. } }
    (* Process first sub postcondition *)
    intros t_sub1 m_sub1 rets_sub1 [Hrets_sub1 [Htr_sub1 [out1 [Hfeval1 [Hbound1 Hsep_sub1]]]]].
    subst rets_sub1 t_sub1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second base sub call === *)
    exists [word.add pout base_off; word.add allocx base_off;
            word.add allocy base_off].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map qe_expr_2nd WeakestPrecondition.expr WeakestPrecondition.expr_body Semantics.interp_binop literal dlet.dlet].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub (word.add pout base_off)
           (word.add allocx base_off) (word.add allocy base_off)
           (snd_e out) (snd_e x) (snd_e y)
           _ tr).
         { exact Hbx1. }
         { exact Hby1. }
         { eexists. pose proof Hsep_sub1 as H'. ecancel_assumption. }
         { eexists. pose proof Hsep_sub1 as H'. ecancel_assumption. }
         { pose proof Hsep_sub1 as H'. ecancel_assumption. } }
    (* Process second sub postcondition *)
    intros t_sub2 m_sub2 rets_sub2 [Hrets_sub2 [Htr_sub2 [out2 [Hfeval2 [Hbound2 Hsep_sub2]]]]].
    subst rets_sub2 t_sub2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    destruct Hsep_sub2 as [m_A [m_rest1 [[Heq_sub2 Hd_A] [HA Hrest1]]]].
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]].
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]].
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]].
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]].
    destruct Hrest5 as [m_F' [m_G' [[Heq_r5 Hd_FG] [HF' HG']]]].
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_sub2.
    pose proof (proj1 (map.disjoint_putmany_r m_C m_D _) Hd_C) as [Hd_CD Hd_C4].
    pose proof (proj1 (map.disjoint_putmany_r m_D m_E _) Hd_D) as [Hd_DE Hd_D5].
    pose proof (proj1 (map.disjoint_putmany_r m_E m_F' m_G') Hd_E) as [Hd_EF' Hd_EG'].
    pose proof (proj1 (map.disjoint_putmany_r m_B m_C _) Hd_B) as [Hd_BC Hd_B_rest].
    pose proof (proj1 (map.disjoint_putmany_r m_B m_D _) Hd_B_rest) as [Hd_BD Hd_B_rest2].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_B _) Hd_A) as [Hd_AB Hd_A_rest].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_C _) Hd_A_rest) as [Hd_AC Hd_A_rest2].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_D _) Hd_A_rest2) as [Hd_AD Hd_A_rest3].
    pose proof (proj1 (map.disjoint_putmany_r m_B m_E _) Hd_B_rest2) as [Hd_BE Hd_B_rest3].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_E _) Hd_A_rest3) as [Hd_AE Hd_A_rest4].
    pose proof (proj1 (map.disjoint_putmany_r m_C m_E _) Hd_C4) as [Hd_CE Hd_C5].
    pose proof (proj1 (map.disjoint_putmany_r m_C m_F' m_G') Hd_C5) as [Hd_CF' Hd_CG'].
    pose proof (proj1 (map.disjoint_putmany_r m_D m_F' m_G') Hd_D5) as [Hd_DF' Hd_DG'].
    pose proof (proj1 (map.disjoint_putmany_r m_B m_F' m_G') Hd_B_rest3) as [Hd_BF' Hd_BG'].
    pose proof (proj1 (map.disjoint_putmany_r m_A m_F' m_G') Hd_A_rest4) as [Hd_AF' Hd_AG'].
    pose proof (generic_FElem_length _ _ _ HC) as Hlen_yC.
    pose proof (generic_FElem_length _ _ _ HD) as Hlen_yD.
    pose proof (generic_FElem_length _ _ _ HE) as Hlen_xE.
    pose proof (generic_FElem_length _ _ _ HF') as Hlen_xF'.
    (* === Stack dealloc allocy === *)
    assert (Hjoin_y : (FElem_b allocy (fst_e y) *
      FElem_b (word.add allocy base_off) (snd_e y))%sep
      (map.putmany m_C m_D)).
    { exists m_C, m_D. split; [split; [reflexivity | exact Hd_CD] |].
      split; [exact HC | exact HD]. }
    pose proof (qe_raw_FElem_join nonresidue prefix eq_dec_base allocy (fst_e y) (snd_e y) _
      Hlen_yC Hlen_yD Hjoin_y) as Hqe_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      QE_fp QE_repr allocy (fst_e y ++ snd_e y)
      (map.putmany m_C m_D) Hqe_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_E (map.putmany m_F' m_G')))),
           (map.putmany m_C m_D).
    split. { exact Hanybytes_y. }
    split.
    { split.
      { rewrite (map.putmany_assoc m_C m_D).
        rewrite (map.putmany_assoc m_B (map.putmany m_C m_D)).
        rewrite (map.putmany_comm m_B (map.putmany m_C m_D)).
        2: { apply map.disjoint_putmany_r. split; [exact Hd_BC | exact Hd_BD]. }
        rewrite <- (map.putmany_assoc (map.putmany m_C m_D) m_B).
        rewrite (map.putmany_assoc m_A (map.putmany m_C m_D)).
        rewrite (map.putmany_comm m_A (map.putmany m_C m_D)).
        2: { apply map.disjoint_putmany_r. split; [exact Hd_AC | exact Hd_AD]. }
        rewrite <- (map.putmany_assoc (map.putmany m_C m_D) m_A).
        apply map.putmany_comm.
        apply map.disjoint_putmany_l. split.
        { apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_AC). }
          apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_BC). }
          apply map.disjoint_putmany_r. split; [exact Hd_CE |].
          apply map.disjoint_putmany_r. split; [exact Hd_CF' | exact Hd_CG']. }
        { apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_AD). }
          apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_BD). }
          apply map.disjoint_putmany_r. split; [exact Hd_DE |].
          apply map.disjoint_putmany_r. split; [exact Hd_DF' | exact Hd_DG']. } }
      { apply map.disjoint_putmany_r. split.
        { apply map.disjoint_putmany_l. split; [exact Hd_AC |].
          apply map.disjoint_putmany_l. split; [exact Hd_BC |].
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_CE). }
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_CF'). }
          { apply (proj1 (map.disjoint_comm _ _) Hd_CG'). } }
        { apply map.disjoint_putmany_l. split; [exact Hd_AD |].
          apply map.disjoint_putmany_l. split; [exact Hd_BD |].
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_DE). }
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_DF'). }
          { apply (proj1 (map.disjoint_comm _ _) Hd_DG'). } } } }
    (* === Stack dealloc allocx === *)
    assert (Hjoin_x : (FElem_b allocx (fst_e x) *
      FElem_b (word.add allocx base_off) (snd_e x))%sep
      (map.putmany m_E m_F')).
    { exists m_E, m_F'. split; [split; [reflexivity | exact Hd_EF'] |].
      split; [exact HE | exact HF']. }
    pose proof (qe_raw_FElem_join nonresidue prefix eq_dec_base allocx (fst_e x) (snd_e x) _
      Hlen_xE Hlen_xF' Hjoin_x) as Hqe_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      QE_fp QE_repr allocx (fst_e x ++ snd_e x)
      (map.putmany m_E m_F') Hqe_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    exists (map.putmany m_A (map.putmany m_B m_G')),
           (map.putmany m_E m_F').
    split. { exact Hanybytes_x. }
    split.
    { split.
      { rewrite (map.putmany_assoc m_E m_F' m_G').
        rewrite (map.putmany_assoc m_B (map.putmany m_E m_F')).
        rewrite (map.putmany_comm m_B (map.putmany m_E m_F')).
        2: { apply map.disjoint_putmany_r. split; [exact Hd_BE | exact Hd_BF']. }
        rewrite <- (map.putmany_assoc (map.putmany m_E m_F') m_B).
        rewrite (map.putmany_assoc m_A (map.putmany m_E m_F')).
        rewrite (map.putmany_comm m_A (map.putmany m_E m_F')).
        2: { apply map.disjoint_putmany_r. split; [exact Hd_AE | exact Hd_AF']. }
        rewrite <- (map.putmany_assoc (map.putmany m_E m_F') m_A).
        apply map.putmany_comm.
        apply map.disjoint_putmany_l. split.
        { apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_AE). }
          apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_BE). }
          { exact Hd_EG'. } }
        { apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_AF'). }
          apply map.disjoint_putmany_r. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_BF'). }
          { exact Hd_FG. } } }
      { apply map.disjoint_putmany_r. split.
        { apply map.disjoint_putmany_l. split; [exact Hd_AE |].
          apply map.disjoint_putmany_l. split; [exact Hd_BE |].
          apply (proj1 (map.disjoint_comm _ _) Hd_EG'). }
        { apply map.disjoint_putmany_l. split; [exact Hd_AF' |].
          apply map.disjoint_putmany_l. split; [exact Hd_BF' |].
          apply (proj1 (map.disjoint_comm _ _) Hd_FG). } } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    exists (out1 ++ out2).
    pose proof (generic_FElem_length _ _ _ HB) as Hlen_out1.
    pose proof (generic_FElem_length _ _ _ HA) as Hlen_out2.
    split.
    { change (@AbstractField.feval _ QE_fp _ _ _ _ QE_repr (out1 ++ out2))
        with (@AbstractField.feval _ base_fp _ _ _ _ base_repr (fst_e (out1 ++ out2)),
              @AbstractField.feval _ base_fp _ _ _ _ base_repr (snd_e (out1 ++ out2))).
      unfold fst_e, qe_fst_felem, snd_e, qe_snd_felem.
      rewrite firstn_app_le by exact Hlen_out1.
      rewrite skipn_app_le by exact Hlen_out1.
      rewrite Hfeval1, Hfeval2. reflexivity. }
    split.
    { split; unfold fst_e, snd_e, qe_fst_felem, qe_snd_felem;
        [rewrite firstn_app_le | rewrite skipn_app_le]; try exact Hlen_out1; assumption. }
    { assert (Hfe_join : (FElem_b pout out1 *
        FElem_b (word.add pout base_off) out2)%sep
        (map.putmany m_B m_A)).
      { exists m_B, m_A. split; [split; [reflexivity |] |].
        { apply (proj1 (map.disjoint_comm _ _) Hd_AB). }
        split; [exact HB | exact HA]. }
      pose proof (qe_raw_FElem_join nonresidue prefix eq_dec_base pout out1 out2 _ Hlen_out1 Hlen_out2 Hfe_join) as Hqe_out.
      exists (map.putmany m_B m_A), m_G'.
      split; [split |].
      { rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. exact Hd_AB. }
      { apply map.disjoint_putmany_l. split; [exact Hd_BG' | exact Hd_AG']. }
      split; [exact Hqe_out | exact HG']. }
    Qed.

End GenericQuadProofs.
