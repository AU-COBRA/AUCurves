Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Export Crypto.Spec.ModularArithmetic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Ltac2.Ltac2.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.
Set Default Proof Mode "Classic".

(*Move elsewhere*)
Lemma firstn_skipn {A : Type} : forall (l : list A) n, (firstn n l) ++ (skipn n l) = l.
Proof.
  intros. generalize dependent n. induction l.
  - destruct n; auto.
  - intros. destruct n; simpl; auto.
    rewrite IHl; auto.
Qed.

Lemma length_firstn {A: Type} : forall (l :list A) n, (length l >= n)%nat -> length (firstn n l) = n.
Proof.
  intros. generalize dependent n. induction l.
  - intros. simpl in H. destruct n; try lia. simpl. auto.
  - intros. destruct n; simpl; auto.
    eapply f_equal. simpl in H. eapply IHl. lia.
Qed.

Lemma length_skipn {A: Type} : forall (l : list A) n, (length l = n + n)%nat -> length (skipn n l) = n.
Proof.
  intros. pose proof H. pose proof (firstn_skipn l n).
  rewrite <- H1 in H.
  rewrite app_length in H.
  rewrite length_firstn in H; try lia.
Qed.

Lemma firstn_app {A : Type} : forall (a b : list A) n, (Datatypes.length a >= n)%nat -> firstn n (a ++ b) = firstn n a.
Proof.
  intros. generalize dependent n. induction a.
  - intros. simpl. simpl in H. destruct n; try discriminate.
    + simpl. auto.
    + inversion H.
  - intros. simpl. destruct n.
    + simpl; auto.
    + simpl. rewrite IHa; auto.
      simpl in H. lia.
Qed.

Lemma skipn_app {A : Type} : forall (a b : list A) n, (Datatypes.length a = n)%nat -> skipn n (a ++ b) = b.
Proof.
  intros. generalize dependent n. induction a.
  - intros; destruct n; try discriminate. auto.
  - intros. simpl. destruct n; try discriminate. simpl in *. inversion H. rewrite H1. apply IHa. auto.
Qed.

Lemma firstn_app' {A : Type} : forall (a b : list A) n, (Datatypes.length a = n)%nat -> firstn n (a ++ b) = a.
Proof.
  intros. rewrite firstn_app; try lia.
  generalize dependent n. induction a.
  - intros. destruct n; simpl; auto.
  - intros. destruct n; try discriminate. simpl in *. inversion H. rewrite H1. rewrite IHa; auto.
Qed.
(* end move elsewhere *)

Section Fp2.
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

  (* note that this excludes non-saturated representations *)
  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  (* Quadratic non-residue β — declared after F_representation to match Specs arg order *)
  Variable beta : F.
  Hypothesis beta_nz : beta <> @F.zero M_pos.
  Hypothesis beta_qnr : ~(exists x, @F.mul M_pos x x = beta).
  Hypothesis M_big : 2 < Z.pos M_pos.

  Local Ltac cancel_impl_step :=
    let RHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps _) (seps ?RHS) => RHS end in
    let jy := index_and_element_of RHS in
    let j := lazymatch jy with (?i, _) => i end in
    let y := lazymatch jy with (_, ?y) => y end in
    assert_fails (idtac; let y := rdelta_var y in is_evar y);
    let LHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
    let i := find_syntactic_unify_deltavar LHS y in
    cancel_seps_at_indices_by_implication i j;
    [exact (impl1_refl _)|].

  Local Ltac ecancel_fast :=
    cancel;
    lazymatch goal with
    | |- Lift1Prop.impl1 _ _ =>
      repeat cancel_impl_step;
      repeat ecancel_step_by_implication;
      cbv [seps]; exact impl1_refl
    | |- Lift1Prop.iff1 _ _ =>
      ecancel_steps_at O;
      ecancel_done
    end.

  Local Ltac ecancel_assumption_fast :=
    multimatch goal with
    | |- ?PG ?m1 =>
      multimatch goal with
      | H: _ ?m2 |- _ =>
        syntactic_unify_deltavar m1 m2;
        let H' := fresh "Hcopy" in
        pose proof H as H';
        cbv beta iota zeta in H';
        lazymatch type of H' with
        | (_ * _)%sep _ =>
          refine (Morphisms.subrelation_refl
                    Lift1Prop.impl1 _ _ _ _ H');
          clear H';
          ecancel_fast
        end
      end
    end.

  Local Ltac ecancel_assumption ::= ecancel_assumption_fast.

  (* Prefix for Fp2 function names — passed explicitly to avoid typeclass issues *)
  Variable fp2_prefix : string.

  (* FElem with optional bounds, polymorphic over field type *)
  Local Definition FElem
    {F' : Type} {fp' : AbstractField.FieldParameters F'}
    {fr' : @AbstractField.FieldRepresentation F' fp' width BW word mem}
    (mbounds : option (@AbstractField.bounds F' fp' _ _ _ _ fr'))
    (px : word) (v : F') : mem -> Prop :=
    Lift1Prop.ex1 (fun ws : @AbstractField.felem F' fp' _ _ _ _ fr' =>
      (emp (@AbstractField.feval F' fp' _ _ _ _ fr' ws = v /\
            match mbounds with
            | Some b => @AbstractField.bounded_by F' fp' _ _ _ _ fr' b ws
            | None => True
            end)
       * @AbstractField.FElem F' fp' _ _ _ _ fr' px ws)%sep).

  Lemma equiv_bounds_FElem x_ptr x
    : Lift1Prop.iff1 (FElem (Some tight_bounds) x_ptr x)
        (FElem (Some loose_bounds) x_ptr x).
  Proof.
    unfold Lift1Prop.iff1, FElem; intro m; split;
    intros [ws [m1 [m2 [Hsplit [[Heq [Heval Hbounds]] Hmem]]]]];
    exists ws, m1, m2; (split; [exact Hsplit | split; [split; [exact Heq | split; [exact Heval |]] | exact Hmem]]);
    [eapply AbstractField.relax_bounds; exact Hbounds
    | eapply bounds_equiv; exact Hbounds].
  Qed.
  #[local] Hint Immediate equiv_bounds_FElem : ecancel_impl.

  Lemma drop_bounds_FElem x_ptr x bounds
    : Lift1Prop.impl1 (FElem bounds x_ptr x) (FElem None x_ptr x).
  Proof.
    unfold Lift1Prop.impl1, FElem; intro m;
    intros [ws [m1 [m2 [Hsplit [[Heq [Heval Hbounds]] Hmem]]]]];
    exists ws, m1, m2; split; [exact Hsplit | split; [split; [exact Heq | split; [exact Heval | exact I]] | exact Hmem]].
  Qed.
  #[local] Hint Immediate drop_bounds_FElem : ecancel_impl.

  Lemma relax_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (F':=F) (Some tight_bounds) x_ptr x) (FElem (F':=F) (Some loose_bounds) x_ptr x).
  Proof.
    unfold Lift1Prop.impl1, FElem; intro m;
    intros [ws [m1 [m2 [Hsplit [[Heq [Heval Hbounds]] Hmem]]]]];
    exists ws, m1, m2; split; [exact Hsplit | split; [split; [exact Heq | split; [exact Heval | eapply AbstractField.relax_bounds; exact Hbounds]] | exact Hmem]].
  Qed.
  #[local] Hint Immediate relax_bounds_FElem : ecancel_impl.

  Lemma FElem_from_bytes (p : word) :
    Lift1Prop.iff1 (AbstractField.Placeholder p) (Lift1Prop.ex1 (AbstractField.FElem p)).
  Proof. apply AbstractField.FElem_from_bytes. Qed.

  Instance spec_of_F_felem_copy : spec_of (AbstractField.felem_copy (F:=F)) := AbstractField.spec_of_felem_copy.
  Instance spec_of_F_select_znz : spec_of (AbstractField.select_znz (F:=F)) := AbstractField.spec_of_selectznz.
  Instance spec_of_F_add : spec_of (AbstractField.add (F:=F)) := AbstractField.binop_spec AbstractField.bin_add.
  Instance spec_of_F_mul : spec_of (AbstractField.mul (F:=F)) := AbstractField.binop_spec AbstractField.bin_mul.
  Instance spec_of_F_sub : spec_of (AbstractField.sub (F:=F)) := AbstractField.binop_spec AbstractField.bin_sub.

  Local Notation felem_offset := (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=F))).
  Local Notation felem_offset_word := (word.of_Z felem_offset).

  Local Instance Fp2_fp_inst : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters beta fp2_prefix.
  Local Instance Fp2_fp_ok_inst : @AbstractField.FieldParameters_ok _ Fp2_fp_inst.
  Proof. exact (Fp2_field_parameters_ok beta beta_nz beta_qnr M_big fp2_prefix). Defined.
  Local Instance Fp2_repr_inst : @AbstractField.FieldRepresentation Fp2 Fp2_fp_inst width BW word mem :=
    @Fp2_field_representation width BW word mem prime_parameters F_representation beta fp2_prefix.
  Local Instance Fp2_repr_ok_inst : @AbstractField.FieldRepresentation_ok Fp2 Fp2_fp_inst _ _ _ _ Fp2_repr_inst :=
    @Fp2_field_representation_ok width BW word mem prime_parameters F_representation F_representation_ok beta fp2_prefix.

  Lemma Fp2_list_decomp : forall l, fst_felem l ++ snd_felem l = l.
  Proof.
    intros. cbv [fst_felem snd_felem]. rewrite firstn_skipn. auto.
  Qed.

  Lemma Fp_FElem_to_Fp2_sep : forall px (x : Fp2) m bounds,
      ((FElem (F':=F) bounds px (fst x)) *
         (FElem (F':=F) bounds (word.add px felem_offset_word) (snd x)))%sep m
      -> (FElem (F':=Fp2) bounds px x m).
  Proof.
    intros px x m bounds0 H.
    unfold FElem in *.
    (* Extract witnesses from the two Fp FElems *)
    destruct H as [m1 [m2 [Hsplit [[ws1 H1] [ws2 H2]]]]].
    destruct H1 as [m1a [m1b [Hsplit1 [[Heq1 Hb1] Hfelem1]]]].
    destruct H2 as [m2a [m2b [Hsplit2 [[Heq2 Hb2] Hfelem2]]]].
    subst m1a m2a.
    assert (m1 = m1b) by (apply Properties.map.split_empty_l in Hsplit1; exact Hsplit1).
    assert (m2 = m2b) by (apply Properties.map.split_empty_l in Hsplit2; exact Hsplit2).
    subst m1b m2b.
    (* Unfold Bignum to get lengths and arrays *)
    unfold AbstractField.FElem, Bignum.Bignum in Hfelem1, Hfelem2.
    destruct Hfelem1 as [me1 [ma1 [Hs1 [[Hme1 Hlen1] Ha1]]]].
    destruct Hfelem2 as [me2 [ma2 [Hs2 [[Hme2 Hlen2] Ha2]]]].
    subst me1 me2.
    assert (m1 = ma1) by (apply Properties.map.split_empty_l in Hs1; exact Hs1).
    assert (m2 = ma2) by (apply Properties.map.split_empty_l in Hs2; exact Hs2).
    subst ma1 ma2.
    (* Provide ws1 ++ ws2 as the Fp2 witness *)
    exists (ws1 ++ ws2).
    exists map.empty, m.
    split. { apply Properties.map.split_empty_l. reflexivity. }
    split.
    + (* Pure facts: feval and bounded_by *)
      cbv [emp]. refine (conj eq_refl _).
      change (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst (ws1 ++ ws2))
        with (@AbstractField.feval _ _ _ _ _ _ F_representation (fst_felem (ws1 ++ ws2)),
              @AbstractField.feval _ _ _ _ _ _ F_representation (snd_felem (ws1 ++ ws2))).
      unfold fst_felem, snd_felem.
      rewrite firstn_app' by exact Hlen1.
      rewrite skipn_app by exact Hlen1.
      destruct Hb1 as [Heval1 Hbnd1]. destruct Hb2 as [Heval2 Hbnd2].
      rewrite Heval1, Heval2.
      split.
      * destruct x; reflexivity.
      * destruct bounds0; [|exact I].
        change (@AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
          with (fun b ws => @AbstractField.bounded_by _ _ _ _ _ _ F_representation b (fst_felem ws)
                         /\ @AbstractField.bounded_by _ _ _ _ _ _ F_representation b (snd_felem ws)).
        unfold fst_felem, snd_felem.
        rewrite firstn_app' by exact Hlen1.
        rewrite skipn_app by exact Hlen1.
        split; assumption.
    + (* AbstractField.FElem: reconstruct Bignum (2*n) from two Bignum n *)
      unfold AbstractField.FElem, Bignum.Bignum.
      exists map.empty, m.
      split. { apply Properties.map.split_empty_l. reflexivity. }
      split.
      * cbv [emp]. refine (conj eq_refl _).
        rewrite app_length, Hlen1, Hlen2.
        change (@AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
          with (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat.
        lia.
      * (* array scalar for ws1 ++ ws2 from the two pieces *)
        apply array_append'.
        exists m1, m2.
        split. { exact Hsplit. }
        split.
        -- exact Ha1.
        -- rewrite Hlen1.
           rewrite word.ring_morph_mul in Ha2 by assumption.
           exact Ha2.
  Qed.

  Lemma Fp2_FElem_to_Fp_sep : forall px x m bounds,
    (FElem (F':=Fp2) bounds px x m) -> ((FElem (F':=F) bounds px (fst x)) * (FElem (F':=F) bounds (word.add px felem_offset_word) (snd x)))%sep m.
  Proof.
    intros px x m bounds0 H.
    unfold FElem in *.
    (* Extract Fp2 witness *)
    destruct H as [ws [m1 [m2 [Hsplit [[Heq Hb] Hfelem]]]]].
    subst m1.
    assert (Hm : m = m2) by (apply Properties.map.split_empty_l in Hsplit; exact Hsplit).
    subst m2.
    (* Extract length from Bignum *)
    assert (Hlen : Datatypes.length ws = @AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst).
    { unfold AbstractField.FElem, Bignum.Bignum in Hfelem.
      destruct Hfelem as [? [? [? [[? ?] ?]]]]. auto. }
    change (@AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
      with (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat in Hlen.
    set (n := @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation) in *.
    (* Decompose feval and bounded_by *)
    destruct Hb as [Hfevalp2 Hbndp2].
    change (@AbstractField.feval _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst ws)
      with (@AbstractField.feval _ _ _ _ _ _ F_representation (fst_felem ws),
            @AbstractField.feval _ _ _ _ _ _ F_representation (snd_felem ws)) in Hfevalp2.
    assert (Heval1 : @AbstractField.feval _ _ _ _ _ _ F_representation (fst_felem ws) = fst x).
    { destruct x. simpl in *. congruence. }
    assert (Heval2 : @AbstractField.feval _ _ _ _ _ _ F_representation (snd_felem ws) = snd x).
    { destruct x. simpl in *. congruence. }
    (* Decompose bounded_by *)
    (* Decompose Fp2 bounded_by into two Fp bounded_by *)
    assert (Hbnd1 : match bounds0 with Some b => @AbstractField.bounded_by _ _ _ _ _ _ F_representation b (fst_felem ws) | None => True end /\
                    match bounds0 with Some b => @AbstractField.bounded_by _ _ _ _ _ _ F_representation b (snd_felem ws) | None => True end).
    { destruct bounds0; [|exact (conj I I)].
      change (@AbstractField.bounded_by _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        with (fun b0 ws0 => @AbstractField.bounded_by _ _ _ _ _ _ F_representation b0 (fst_felem ws0)
                          /\ @AbstractField.bounded_by _ _ _ _ _ _ F_representation b0 (snd_felem ws0)) in Hbndp2.
      exact Hbndp2. }
    destruct Hbnd1 as [Hbnd1 Hbnd2].
    (* Split the array *)
    assert (ws = fst_felem ws ++ snd_felem ws) as Hdecomp.
    { symmetry. apply Fp2_list_decomp. }
    unfold AbstractField.FElem, Bignum.Bignum in Hfelem.
    destruct Hfelem as [me [ma [Hse [[Hme Hle] Ha]]]].
    subst me.
    assert (Hma : m = ma) by (apply Properties.map.split_empty_l in Hse; exact Hse). subst ma.
    rewrite Hdecomp in Ha.
    apply array_append' in Ha.
    destruct Ha as [ml [mr [Hsm [Hal Har]]]].
    (* Construct the two FElem witnesses *)
    exists ml, mr.
    split. { exact Hsm. }
    split.
    - (* FElem for fst *)
      exists (fst_felem ws). exists map.empty, ml.
      split. { apply Properties.map.split_empty_l. reflexivity. }
      split.
      * cbv [emp]. refine (conj eq_refl (conj Heval1 Hbnd1)).
      * unfold AbstractField.FElem, Bignum.Bignum.
        exists map.empty, ml.
        split. { apply Properties.map.split_empty_l. reflexivity. }
        split.
        -- cbv [emp]. refine (conj eq_refl _). unfold fst_felem. apply length_firstn. lia.
        -- exact Hal.
    - (* FElem for snd *)
      exists (snd_felem ws). exists map.empty, mr.
      split. { apply Properties.map.split_empty_l. reflexivity. }
      split.
      * cbv [emp]. refine (conj eq_refl (conj Heval2 Hbnd2)).
      * unfold AbstractField.FElem, Bignum.Bignum.
        exists map.empty, mr.
        split. { apply Properties.map.split_empty_l. reflexivity. }
        split.
        -- cbv [emp]. refine (conj eq_refl _). unfold snd_felem. apply length_skipn. lia.
        -- (* Fix offset *)
           unfold fst_felem in Har. rewrite length_firstn in Har; [|lia]. fold n in Har.
           rewrite <- (@word.ring_morph_mul _ _ word_ok) in Har. exact Har.
  Qed.

  Lemma Fp2_Fp_FElem : forall px x bounds,
    Lift1Prop.iff1
      (FElem (F':=Fp2) bounds px x)
      ((FElem (F':=F) bounds px (fst x)) ⋆ (FElem (F':=F) bounds (word.add px felem_offset_word) (snd x))).
  Proof.
    intros; split.
    - apply Fp2_FElem_to_Fp_sep.
    - apply Fp_FElem_to_Fp2_sep.
  Qed.

  (* Raw AbstractField.FElem splitting: Fp2 Bignum → two Fp Bignums *)
  Lemma Fp2_raw_FElem_split pout out m :
    @AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst pout out m ->
    (@AbstractField.FElem _ _ _ _ _ _ F_representation pout (fst_felem out) *
     @AbstractField.FElem _ _ _ _ _ _ F_representation (word.add pout felem_offset_word) (snd_felem out))%sep m.
  Proof.
    intros H.
    unfold AbstractField.FElem, Bignum.Bignum in *.
    destruct H as [me [ma [Hms [[Hme Hlen] Ha]]]].
    subst me. assert (m = ma) by (apply Properties.map.split_empty_l in Hms; exact Hms). subst.
    change (@AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
      with (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)%nat in Hlen.
    set (n := @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation) in *.
    assert (out = fst_felem out ++ snd_felem out) as Hdecomp by (symmetry; apply Fp2_list_decomp).
    rewrite Hdecomp in Ha.
    apply array_append' in Ha.
    destruct Ha as [m1 [m2 [Hms2 [Ha1 Ha2]]]].
    assert (Hlen1 : length (fst_felem out) = n) by (unfold fst_felem; apply length_firstn; lia).
    rewrite Hlen1 in Ha2.
    rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha2.
    exists m1, m2. split; [exact Hms2 |]. split.
    - exists map.empty, m1. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [split; [exact eq_refl | exact Hlen1] | exact Ha1].
    - exists map.empty, m2. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [split; [exact eq_refl |] |].
      + unfold snd_felem. apply length_skipn. lia.
      + exact Ha2.
  Qed.

  (* Join two Fp FElems into Fp2 FElem *)
  Lemma Fp2_raw_FElem_join pout out1 out2 m :
    length out1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation ->
    length out2 = @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation ->
    (@AbstractField.FElem _ _ _ _ _ _ F_representation pout out1 *
     @AbstractField.FElem _ _ _ _ _ _ F_representation (word.add pout felem_offset_word) out2)%sep m ->
    @AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst pout (out1 ++ out2) m.
  Proof.
    intros Hlen1 Hlen2 H.
    unfold AbstractField.FElem, Bignum.Bignum in *.
    destruct H as [m1 [m2 [Hms [H1 H2]]]].
    destruct H1 as [me1 [ma1 [Hms1 [[Hme1 Hlen1'] Ha1]]]].
    subst me1. assert (m1 = ma1) by (apply Properties.map.split_empty_l in Hms1; exact Hms1). subst.
    destruct H2 as [me2 [ma2 [Hms2' [[Hme2 Hlen2'] Ha2]]]].
    subst me2. assert (m2 = ma2) by (apply Properties.map.split_empty_l in Hms2'; exact Hms2'). subst.
    set (n := @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation) in *.
    exists map.empty, m. split. { apply Properties.map.split_empty_l. reflexivity. }
    split.
    - split; [exact eq_refl |].
      rewrite length_app.
      change (@AbstractField.felem_size_in_words _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst)
        with (2 * n)%nat. lia.
    - (* Reconstruct array from two halves *)
      pose proof (proj2 (array_append'
        scalar (word.of_Z (Memory.bytes_per_word width))
        out1 out2 pout m)) as Hback.
      apply Hback. clear Hback.
      exists ma1, ma2. split; [exact Hms |]. split; [exact Ha1 |].
      (* Align address: array_append' expects word.mul size (word.of_Z (length out1)),
         Ha2 has felem_offset_word = word.of_Z (bpw * n) *)
      rewrite Hlen1'.
      rewrite <- (@word.ring_morph_mul _ _ word_ok).
      exact Ha2.
  Qed.

  (* Extract length from AbstractField.FElem *)
  Lemma AbstractFElem_length pout (out : @AbstractField.felem _ _ _ _ _ _ F_representation) m :
    @AbstractField.FElem _ _ _ _ _ _ F_representation pout out m ->
    length out = @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation.
  Proof.
    unfold AbstractField.FElem, Bignum.Bignum.
    intros [me [ma [_ [[_ H] _]]]]. exact H.
  Qed.

  Definition expr_2nd_felem (x : Syntax.expr) := expr.op bopname.add x (expr.literal felem_offset).

  Context {Fp2_names : FieldNames (F:=Fp2)}.
  Context {F_names : FieldNames (F:=F)}.

  Definition Fp2_felem_copy : string * Syntax.func :=
    (AbstractField.felem_copy (F:=Fp2), (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr.var "out"; expr.var "x"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "x")])
    ))).

  Instance spec_of_Fp2_copy : spec_of (AbstractField.felem_copy (F:=Fp2)) := AbstractField.spec_of_felem_copy (F:=Fp2).

  Definition Fp2_select_znz : string * Syntax.func :=
    (AbstractField.select_znz (F:=Fp2), (["out"; "c"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as allocy;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr.var "allocy"; expr.var "iny"]);
      coq:(cmd.call [] (AbstractField.select_znz (F:=F)) [expr.var "out"; expr.var "c"; expr.var "allocx"; expr.var "allocy"]);
      coq:(cmd.call [] (AbstractField.select_znz (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "c"; expr_2nd_felem (expr.var "allocx"); expr_2nd_felem (expr.var "allocy")])
    ))).

  Instance spec_of_Fp2_select_znz : spec_of (AbstractField.select_znz (F:=Fp2)) := AbstractField.spec_of_selectznz (F:=Fp2).

  Definition Fp2_add : string * Syntax.func :=
    (AbstractField.add (F:=Fp2), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as allocy;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr.var "allocy"; expr.var "iny"]);
      coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "out"; expr.var "allocx"; expr.var "allocy"]);
      coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "allocx"); expr_2nd_felem (expr.var "allocy")])
    ))).

  Instance spec_of_Fp2_add : spec_of (AbstractField.add (F:=Fp2)) := AbstractField.binop_spec AbstractField.bin_add (F:=Fp2).

  Definition Fp2_zero : string * Syntax.func :=
    (zero (F:=Fp2), (["out"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (zero (F:=F)) [expr.var "out"]);
      coq:(cmd.call [] (zero (F:=F)) [expr_2nd_felem (expr.var "out")])
    ))).

  Instance spec_of_F_zero : spec_of (zero (F:=F)) :=
    AbstractField.nullop_spec (field_representation := F_representation)
      (AbstractField.null_zero (field_names := F_names)).
  Instance spec_of_Fp2_zero : spec_of (zero (F:=Fp2)) := AbstractField.nullop_spec AbstractField.null_zero (F:=Fp2).

  Definition Fp2_one : string * Syntax.func :=
    (one (F:=Fp2), (["out"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (one (F:=F)) [expr.var "out"]);
      coq:(cmd.call [] (zero (F:=F)) [expr_2nd_felem (expr.var "out")])
    ))).

  Instance spec_of_F_one : spec_of (one (F:=F)) :=
    AbstractField.nullop_spec (field_representation := F_representation)
      (AbstractField.null_one (field_names := F_names)).
  Instance spec_of_Fp2_one : spec_of (one (F:=Fp2)) := AbstractField.nullop_spec AbstractField.null_one (F:=Fp2).

  Import Syntax BinInt String List.ListNotations.

  (* Generate real WP goals for (string * func) definitions.
     Adapts bedrock2's program_logic_goal_for_function! Ltac2 to work with
     function_t = (string * func) by extracting the name from the pair. *)
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
  (* Automation tactics for WP proofs                                 *)
  (* ================================================================ *)

  (* Derive all pairwise disjointness from compound disjointness hypotheses *)
  Ltac saturate_disjointness :=
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

  (* Solve disjointness goals from (saturated) hypotheses *)
  Ltac map_disjoint_auto :=
    lazymatch goal with
    | |- map.disjoint ?a (map.putmany ?b ?c) =>
        apply (proj2 (map.disjoint_putmany_r a b c));
        split; [map_disjoint_auto | map_disjoint_auto]
    | |- map.disjoint (map.putmany ?a ?b) ?c =>
        apply (proj2 (map.disjoint_putmany_l a b c));
        split; [map_disjoint_auto | map_disjoint_auto]
    | |- map.disjoint ?a ?b =>
        first [assumption | exact (proj1 (map.disjoint_comm b a) ltac:(assumption))]
    end.

  (* Swap adjacent elements in a putmany chain: a(bc) = b(ac) *)
  Lemma putmany_swap (a b c : @map.rep _ _ mem) :
    map.disjoint a b ->
    map.putmany a (map.putmany b c) = map.putmany b (map.putmany a c).
  Proof.
    intros Hd.
    rewrite map.putmany_assoc.
    rewrite (map.putmany_comm a b Hd).
    rewrite <- map.putmany_assoc.
    reflexivity.
  Qed.

  (* Solve dexprs goals for variable lookups in locals map *)
  Ltac solve_dexprs :=
    cbv [dexprs list_map expr_2nd_felem expr WeakestPrecondition.expr_body felem_offset];
    repeat (eexists; split; [
      repeat (first [apply map.get_put_same |
                     rewrite map.get_put_diff by (cbv; congruence)]) |]);
    exact eq_refl.

  (* Prove fst_felem (out1 ++ out2) = out1 given length out1 = felem_size_in_words *)
  Ltac prove_fst_app :=
    unfold fst_felem;
    match goal with
    | H : Datatypes.length ?out1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ _ |- _ =>
      rewrite <- H;
      rewrite List.firstn_app, Nat.sub_diag; simpl (ListDef.firstn 0 _);
      rewrite List.app_nil_r; exact (List.firstn_all out1)
    end.

  (* Prove snd_felem (out1 ++ out2) = out2 given length out1 = felem_size_in_words *)
  Ltac prove_snd_app :=
    unfold snd_felem;
    match goal with
    | H : Datatypes.length ?out1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ _ |- _ =>
      rewrite <- H;
      rewrite List.skipn_app, Nat.sub_diag; simpl (ListDef.skipn 0 _);
      rewrite List.skipn_all; [reflexivity | lia]
    end.

  (* Prove firstn_skipn identity: firstn n l ++ skipn n l = l *)
  Ltac prove_firstn_skipn :=
    match goal with
    | |- fst_felem ?l ++ snd_felem ?l = ?l =>
      unfold fst_felem, snd_felem; apply List.firstn_skipn
    end.

  Lemma Fp2_zero_ok : program_logic_goal_for_function! Fp2_zero.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFzero1 HFzero2.
    unfold spec_of_Fp2_zero, AbstractField.nullop_spec.
    intros pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp2_zero].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for first call: expr.var "out" *)
    exists [pout]. split.
    1: { eexists. split. { apply map.get_put_same. }
         cbv [list_map]. exact eq_refl. }
    (* First call to F_zero on pout *)
    set (FElem_Fp := @AbstractField.FElem _ _ _ _ _ _ F_representation).
    pose proof (Fp2_raw_FElem_split pout out) as Hsplit_lem.
    destruct Hmem0 as [m_fp2 [m_r [Hsplit [Hfp2 Hrr]]]].
    pose proof (Hsplit_lem m_fp2 Hfp2) as Hsep_fp2. clear Hsplit_lem.
    destruct Hsep_fp2 as [m_fst [m_snd [Hsplit2 [Hfst Hsnd]]]].
    assert (Hsep_rearr : (FElem_Fp pout (fst_felem out) ⋆
      (fun m => (FElem_Fp (word.add pout felem_offset_word) (snd_felem out) ⋆ Rr) m)) mem0).
    { destruct Hsplit as [Heq0 Hd0]. destruct Hsplit2 as [Heq2 Hd2].
      subst m_fp2.
      pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd0) as [Hd_fst_r Hd_snd_r].
      exists m_fst, (map.putmany m_snd m_r).
      split; [split |].
      { subst mem0. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_r. split; [exact Hd2 | exact Hd_fst_r]. }
      split; [exact Hfst |].
      exists m_snd, m_r.
      split; [split; [reflexivity | exact Hd_snd_r] |].
      split; [exact Hsnd | exact Hrr]. }
    eapply Semantics.weaken_call.
    1: { eapply HFzero1. exact Hsep_rearr. }
    (* Process postcondition of first call *)
    intros t' m' rets [Hrets [Htr [out1 [Hfeval1 [Hbounded1 Hsep1]]]]].
    subst rets t'.
    exists (#{ "out" => pout }#). split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for second call: expr_2nd_felem (expr.var "out") *)
    exists [word.add pout felem_offset_word]. split.
    1: { eexists. split. { apply map.get_put_same. }
         cbv [expr WeakestPrecondition.expr_body list_map felem_offset].
         exact eq_refl. }
    (* Rearrange sep for second call *)
    assert (Hsep2 : (FElem_Fp (word.add pout felem_offset_word) (snd_felem out) ⋆
      (fun m => (FElem_Fp pout out1 ⋆ Rr) m)) m').
    { destruct Hsep1 as [m_a [m_b [Hsp1 [Ha Hb]]]].
      destruct Hb as [m_c [m_d [Hsp2 [Hc Hd]]]].
      destruct Hsp1 as [Heq1 Hd1]. destruct Hsp2 as [Heq2 Hd2].
      subst m_b.
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_ac Hd_ad].
      exists m_c, (map.putmany m_a m_d).
      split; [split |].
      { subst m'. do 2 rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. exact Hd_ac. }
      { apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
          exact (Hd_ac k v2 v1 Hg2 Hg1). }
        { exact Hd2. } }
      split; [exact Hc |].
      exists m_a, m_d.
      split; [split; [reflexivity | exact Hd_ad] |].
      split; [exact Ha | exact Hd]. }
    (* Second call to F_zero on pout + offset *)
    eapply Semantics.weaken_call.
    1: { eapply HFzero2. exact Hsep2. }
    (* Process postcondition of second call *)
    intros t'' m'' rets [Hrets [Htr [out2 [Hfeval2 [Hbounded2 Hsep3]]]]].
    subst rets.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout }#). split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact Htr. }
    (* Provide out1 ++ out2 as the Fp2 output *)
    exists (out1 ++ out2).
    (* feval condition *)
    split.
    { assert (Hlen_out1 : Datatypes.length out1 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).
      { destruct Hsep3 as [? [? [? [? Htmp]]]].
        destruct Htmp as [? [? [? [Htmp2 ?]]]].
        exact (AbstractFElem_length _ _ _ Htmp2). }
      unfold feval. simpl @AbstractField.feval.
      unfold Fp2_repr_inst, Fp2_field_representation, fst_felem, snd_felem.
      rewrite <- Hlen_out1.
      rewrite List.firstn_app, Nat.sub_diag. simpl (ListDef.firstn 0 _).
      rewrite List.app_nil_r.
      rewrite List.skipn_app, Nat.sub_diag. simpl (ListDef.skipn 0 _).
      rewrite List.firstn_all, List.skipn_all; [| lia].
      simpl.
      rewrite Hfeval1, Hfeval2. unfold null_model, null_zero, zerop2.
      reflexivity. }
    split.
    (* bounded_by condition *)
    { unfold bounded_by, Fp2_repr_inst, Fp2_field_representation, fst_felem, snd_felem.
      assert (Hlen_out1 : Datatypes.length out1 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).
      { destruct Hsep3 as [? [? [? [? Htmp]]]].
        destruct Htmp as [? [? [? [Htmp2 ?]]]].
        exact (AbstractFElem_length _ _ _ Htmp2). }
      rewrite <- Hlen_out1.
      rewrite List.firstn_app, Nat.sub_diag. simpl (ListDef.firstn 0 _).
      rewrite List.app_nil_r.
      rewrite List.skipn_app, Nat.sub_diag. simpl (ListDef.skipn 0 _).
      rewrite List.firstn_all, List.skipn_all; [| lia]. simpl.
      split; [exact Hbounded1 | exact Hbounded2]. }
    (* sep reconstruction: (FElem_Fp2 pout (out1++out2) ⋆ Rr) m'' *)
    { destruct Hsep3 as [m_a [m_b [Hsp3 [HQ3 HR3]]]].
      destruct HR3 as [m_c [m_d [Hsp4 [HP3 HD3]]]].
      destruct Hsp3 as [Heq3 Hd3]. destruct Hsp4 as [Heq4 Hd4].
      subst m_b.
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd3) as [Hd_ac Hd_ad].
      assert (Hlen1 : Datatypes.length out1 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)
        by exact (AbstractFElem_length _ _ _ HP3).
      assert (Hlen2 : Datatypes.length out2 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)
        by exact (AbstractFElem_length _ _ _ HQ3).
      assert (Hfe_join : (FElem_Fp pout out1 ⋆
        FElem_Fp (word.add pout felem_offset_word) out2)
        (map.putmany m_c m_a)).
      { exists m_c, m_a. split; [split; [reflexivity |] |].
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
          exact (Hd_ac k v2 v1 Hg2 Hg1). }
        split; [exact HP3 | exact HQ3]. }
      pose proof (Fp2_raw_FElem_join pout out1 out2 _ Hlen1 Hlen2 Hfe_join) as Hfp2_out.
      exists (map.putmany m_c m_a), m_d.
      split; [split |].
      { subst m''. rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. exact Hd_ac. }
      { apply map.disjoint_putmany_l.
        split; [exact Hd4 | exact Hd_ad]. }
      split; [exact Hfp2_out | exact HD3]. }
  Qed.

  Lemma Fp2_one_ok : program_logic_goal_for_function! Fp2_one.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFone HFzero.
    unfold spec_of_Fp2_one, AbstractField.nullop_spec.
    intros pout out Rr tr mem0 Hmem0.
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp2_one].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    exists [pout]. split.
    1: { eexists. split. { apply map.get_put_same. }
         cbv [list_map]. exact eq_refl. }
    set (FElem_Fp := @AbstractField.FElem _ _ _ _ _ _ F_representation).
    pose proof (Fp2_raw_FElem_split pout out) as Hsplit_lem.
    destruct Hmem0 as [m_fp2 [m_r [Hsplit [Hfp2 Hrr]]]].
    pose proof (Hsplit_lem m_fp2 Hfp2) as Hsep_fp2. clear Hsplit_lem.
    destruct Hsep_fp2 as [m_fst [m_snd [Hsplit2 [Hfst Hsnd]]]].
    assert (Hsep_rearr : (FElem_Fp pout (fst_felem out) ⋆
      (fun m => (FElem_Fp (word.add pout felem_offset_word) (snd_felem out) ⋆ Rr) m)) mem0).
    { destruct Hsplit as [Heq0 Hd0]. destruct Hsplit2 as [Heq2 Hd2].
      subst m_fp2.
      pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd0) as [Hd_fst_r Hd_snd_r].
      exists m_fst, (map.putmany m_snd m_r).
      split; [split |].
      { subst mem0. rewrite map.putmany_assoc. reflexivity. }
      { apply map.disjoint_putmany_r. split; [exact Hd2 | exact Hd_fst_r]. }
      split; [exact Hfst |].
      exists m_snd, m_r.
      split; [split; [reflexivity | exact Hd_snd_r] |].
      split; [exact Hsnd | exact Hrr]. }
    eapply Semantics.weaken_call.
    1: { eapply HFone. exact Hsep_rearr. }
    intros t' m' rets [Hrets [Htr [out1 [Hfeval1 [Hbounded1 Hsep1]]]]].
    subst rets t'.
    exists (#{ "out" => pout }#). split. { exact eq_refl. }
    repeat straightline.
    exists [word.add pout felem_offset_word]. split.
    1: { eexists. split. { apply map.get_put_same. }
         cbv [expr WeakestPrecondition.expr_body list_map felem_offset].
         exact eq_refl. }
    assert (Hsep2 : (FElem_Fp (word.add pout felem_offset_word) (snd_felem out) ⋆
      (fun m => (FElem_Fp pout out1 ⋆ Rr) m)) m').
    { destruct Hsep1 as [m_a [m_b [Hsp1 [Ha Hb]]]].
      destruct Hb as [m_c [m_d [Hsp2 [Hc Hd]]]].
      destruct Hsp1 as [Heq1 Hd1]. destruct Hsp2 as [Heq2 Hd2].
      subst m_b.
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd1) as [Hd_ac Hd_ad].
      exists m_c, (map.putmany m_a m_d).
      split; [split |].
      { subst m'. do 2 rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. exact Hd_ac. }
      { apply map.disjoint_putmany_r. split.
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
          exact (Hd_ac k v2 v1 Hg2 Hg1). }
        { exact Hd2. } }
      split; [exact Hc |].
      exists m_a, m_d.
      split; [split; [reflexivity | exact Hd_ad] |].
      split; [exact Ha | exact Hd]. }
    eapply Semantics.weaken_call.
    1: { eapply HFzero. exact Hsep2. }
    intros t'' m'' rets [Hrets [Htr [out2 [Hfeval2 [Hbounded2 Hsep3]]]]].
    subst rets.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout }#). split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact Htr. }
    exists (out1 ++ out2).
    split.
    { assert (Hlen_out1 : Datatypes.length out1 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).
      { destruct Hsep3 as [? [? [? [? Htmp]]]].
        destruct Htmp as [? [? [? [Htmp2 ?]]]].
        exact (AbstractFElem_length _ _ _ Htmp2). }
      unfold feval. simpl @AbstractField.feval.
      unfold Fp2_repr_inst, Fp2_field_representation, fst_felem, snd_felem.
      rewrite <- Hlen_out1.
      rewrite List.firstn_app, Nat.sub_diag. simpl (ListDef.firstn 0 _).
      rewrite List.app_nil_r.
      rewrite List.skipn_app, Nat.sub_diag. simpl (ListDef.skipn 0 _).
      rewrite List.firstn_all, List.skipn_all; [| lia]. simpl.
      rewrite Hfeval1, Hfeval2. unfold null_model, null_one, null_zero, onep2.
      reflexivity. }
    split.
    { unfold bounded_by, Fp2_repr_inst, Fp2_field_representation, fst_felem, snd_felem.
      assert (Hlen_out1 : Datatypes.length out1 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation).
      { destruct Hsep3 as [? [? [? [? Htmp]]]].
        destruct Htmp as [? [? [? [Htmp2 ?]]]].
        exact (AbstractFElem_length _ _ _ Htmp2). }
      rewrite <- Hlen_out1.
      rewrite List.firstn_app, Nat.sub_diag. simpl (ListDef.firstn 0 _).
      rewrite List.app_nil_r.
      rewrite List.skipn_app, Nat.sub_diag. simpl (ListDef.skipn 0 _).
      rewrite List.firstn_all, List.skipn_all; [| lia]. simpl.
      split; [exact Hbounded1 | exact Hbounded2]. }
    { destruct Hsep3 as [m_a [m_b [Hsp3 [HQ3 HR3]]]].
      destruct HR3 as [m_c [m_d [Hsp4 [HP3 HD3]]]].
      destruct Hsp3 as [Heq3 Hd3]. destruct Hsp4 as [Heq4 Hd4].
      subst m_b.
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd3) as [Hd_ac Hd_ad].
      assert (Hlen1 : Datatypes.length out1 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)
        by exact (AbstractFElem_length _ _ _ HP3).
      assert (Hlen2 : Datatypes.length out2 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)
        by exact (AbstractFElem_length _ _ _ HQ3).
      assert (Hfe_join : (FElem_Fp pout out1 ⋆
        FElem_Fp (word.add pout felem_offset_word) out2)
        (map.putmany m_c m_a)).
      { exists m_c, m_a. split; [split; [reflexivity |] |].
        { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2;
          exact (Hd_ac k v2 v1 Hg2 Hg1). }
        split; [exact HP3 | exact HQ3]. }
      pose proof (Fp2_raw_FElem_join pout out1 out2 _ Hlen1 Hlen2 Hfe_join) as Hfp2_out.
      exists (map.putmany m_c m_a), m_d.
      split; [split |].
      { subst m''. rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. exact Hd_ac. }
      { apply map.disjoint_putmany_l.
        split; [exact Hd4 | exact Hd_ad]. }
      split; [exact Hfp2_out | exact HD3]. }
  Qed.

  Lemma Fp2_select_znz_ok : program_logic_goal_for_function! Fp2_select_znz.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFp2copy1 HFp2copy2 HFsel1 HFsel2.
    unfold spec_of_Fp2_select_znz, AbstractField.spec_of_selectznz.
    intros pout pc px py out Rout Rx Ry x y tr mem0
      [Hmem_out [Hmem_x [Hmem_y Hbit_range]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp2_select_znz].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Stackalloc allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Stackalloc allocy === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    set (FElem_Fp := @AbstractField.FElem _ _ _ _ _ _ F_representation).
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_mem0_sY Hd_sX_sY].
    destruct Hmem_x as [m_x [m_rx [Hmemx_sp [Hfelem_x Hrx]]]].
    destruct Hmemx_sp as [Heq_mem0 Hd_xrx]. subst mem0.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_mem0_sY) as [Hd_x_sY Hd_rx_sY].
    (* === First copy call: inx → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    1: { subst l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFp2copy1 allocx px allocx_val x
           (fun m => (Rx ⋆ @AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst allocy allocy_val) m)
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
           { exists m_x, mStackX. split; [split; [reflexivity | exact Hd_x_sX] |].
             split; [exact Hfelem_x | exact Hallocx]. }
           { exists m_rx, mStackY. split; [split; [reflexivity | exact Hd_rx_sY] |].
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
    intros t' m' rets [Hrets [Htr Hsep_copy1]].
    subst rets t'.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second copy call: iny → allocy === *)
    destruct Hsep_copy1 as [m_new1 [m_frame1 [[Heq_m' Hd_n1_f1] [Hfelem_allocx Hframe1]]]].
    subst m_frame1 m'.
    destruct Hmem_y as [m_y [m_ry [Hmemy_sp [Hfelem_y Hry]]]].
    destruct Hmemy_sp as [Heq_mem0_y Hd_yry].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_f1) as [Hd_n1_mem0 Hd_n1_sY].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_x Hd_n1_rx].
    rewrite Heq_mem0_y in Hd_n1_mem0.
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_mem0) as [Hd_n1_y Hd_n1_ry].
    rewrite Heq_mem0_y in Hd_mem0_sY.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_mem0_sY) as [Hd_y_sY Hd_ry_sY'].
    exists [allocy; py]. split.
    1: { subst l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFp2copy2 allocy py allocy_val y
           (fun m => (AbstractField.FElem allocx x ⋆ Ry) m)
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
           { exists m_y, mStackY. split; [split; [reflexivity | exact Hd_y_sY] |].
             split; [exact Hfelem_y | exact Hallocy]. }
           { exists m_new1, m_ry. split; [split; [reflexivity | exact Hd_n1_ry] |].
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
    intros t'' m'' rets2 [Hrets2 [Htr2 Hsep_copy2]].
    subst rets2 t''.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Phase 4: F-level select_znz calls === *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    pose proof (Fp2_raw_FElem_split allocx x m_new1 Hfelem_allocx) as [m_ax1 [m_ax2 [Hsp_ax [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax as [Heq_new1 Hd_ax].
    pose proof (Fp2_raw_FElem_split allocy y m_new2 Hfelem_allocy) as [m_ay1 [m_ay2 [Hsp_ay [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay as [Heq_new2 Hd_ay].
    rewrite Heq_mem0_y in Hmem_out.
    destruct Hmem_out as [m_oo [m_rout [Hsp_mo [Hfe_out Hrout]]]].
    destruct Hsp_mo as [Heq_yr Hd_out_rout].
    pose proof (Fp2_raw_FElem_split pout out m_oo Hfe_out) as [m_o1 [m_o2 [Hsp_out [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_out as [Heq_out Hd_o12].
    subst m_oo m_new1 m_new2 m''.
    rewrite Heq_yr in Hd_n2_f2, Hd_n1_mem0.
    rewrite Heq_yr.
    assert (Hsep7 : ((FElem_Fp allocy (fst_felem y) ⋆
      FElem_Fp (word.add allocy felem_offset_word) (snd_felem y)) ⋆
      ((FElem_Fp allocx (fst_felem x) ⋆
        FElem_Fp (word.add allocx felem_offset_word) (snd_felem x)) ⋆
        ((FElem_Fp pout (fst_felem out) ⋆
          FElem_Fp (word.add pout felem_offset_word) (snd_felem out)) ⋆ Rout)))
      (map.putmany (map.putmany m_ay1 m_ay2)
        (map.putmany (map.putmany m_ax1 m_ax2)
          (map.putmany (map.putmany m_o1 m_o2) m_rout)))).
    { exists (map.putmany m_ay1 m_ay2),
        (map.putmany (map.putmany m_ax1 m_ax2)
          (map.putmany (map.putmany m_o1 m_o2) m_rout)).
      split; [split; [reflexivity | exact Hd_n2_f2] |].
      split.
      { exists m_ay1, m_ay2. split; [split; [reflexivity | exact Hd_ay] |].
        split; [exact Hfe_ay1 | exact Hfe_ay2]. }
      exists (map.putmany m_ax1 m_ax2), (map.putmany (map.putmany m_o1 m_o2) m_rout).
      split; [split; [reflexivity | exact Hd_n1_mem0] |].
      split.
      { exists m_ax1, m_ax2. split; [split; [reflexivity | exact Hd_ax] |].
        split; [exact Hfe_ax1 | exact Hfe_ax2]. }
      exists (map.putmany m_o1 m_o2), m_rout.
      split; [split; [reflexivity | exact Hd_out_rout] |].
      split.
      { exists m_o1, m_o2. split; [split; [reflexivity | exact Hd_o12] |].
        split; [exact Hfe_o1 | exact Hfe_o2]. }
      exact Hrout. }
    (* === First F.select_znz call === *)
    exists [pout; pc; allocx; allocy]. split.
    1: { subst l0 l. solve_dexprs. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsel1 pout pc allocx allocy
           (fst_felem out) _ _ _ (fst_felem x) (fst_felem y) tr).
         split; [pose proof Hsep7 as H'; ecancel_assumption |].
         split; [pose proof Hsep7 as H'; ecancel_assumption |].
         split; [pose proof Hsep7 as H'; ecancel_assumption |].
         exact Hbit_range. }
    intros t_sel1 m_sel1 rets_sel1 [Hrets_sel1 Hsep_sel1].
    subst rets_sel1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second F.select_znz call === *)
    exists [word.add pout felem_offset_word; pc;
            word.add allocx felem_offset_word; word.add allocy felem_offset_word].
    split.
    1: { subst l0 l. solve_dexprs. }
    (* Case split on condition to make postconditions concrete *)
    destruct (word.unsigned pc =? 1) eqn:Hpc.
    all: (
    eapply Semantics.weaken_call;
    [eapply (HFsel2 (word.add pout felem_offset_word) pc
       (word.add allocx felem_offset_word) (word.add allocy felem_offset_word)
       (snd_felem out) _ _ _ (snd_felem x) (snd_felem y) t_sel1);
     split; [pose proof Hsep_sel1 as H'; ecancel_assumption |];
     split; [pose proof Hsep_sel1 as H'; ecancel_assumption |];
     split; [pose proof Hsep_sel1 as H'; ecancel_assumption |];
     exact Hbit_range |]).
    all: (
    intros t_sel2 m_sel2 rets_sel2 [Hrets_sel2 Hsep_sel2];
    subst rets_sel2;
    rewrite Hpc in Hsep_sel2;
    cbv [map.putmany_of_list_zip];
    exists l0; split; [exact eq_refl |];
    repeat straightline).
    (* === Both branches: destructure + stack dealloc + final postcondition === *)
    all: (
    destruct Hsep_sel2 as [m_A [m_rest1 [[Heq_sel2 Hd_A] [HA Hrest1]]]];
    destruct Hrest1 as [m_B [m_rest2 [[Heq_r1 Hd_B] [HB Hrest2]]]];
    destruct Hrest2 as [m_C [m_rest3 [[Heq_r2 Hd_C] [HC Hrest3]]]];
    destruct Hrest3 as [m_D [m_rest4 [[Heq_r3 Hd_D] [HD Hrest4]]]];
    destruct Hrest4 as [m_E [m_rest5 [[Heq_r4 Hd_E] [HE Hrest5]]]];
    destruct Hrest5 as [m_F' [m_G' [[Heq_r5 Hd_FG] [HF' HG']]]];
    subst m_rest1 m_rest2 m_rest3 m_rest4 m_rest5 m_sel2;
    saturate_disjointness).
    (* Stack dealloc allocy *)
    all: (
    pose proof (AbstractFElem_length _ _ _ HC) as Hlen_yC;
    pose proof (AbstractFElem_length _ _ _ HD) as Hlen_yD;
    assert (Hjoin_y : (FElem_Fp allocy (fst_felem y) ⋆
      FElem_Fp (word.add allocy felem_offset_word) (snd_felem y))
      (map.putmany m_C m_D));
    [exists m_C, m_D; split; [split; [reflexivity | assumption] |];
     split; [exact HC | exact HD] |];
    pose proof (Fp2_raw_FElem_join allocy (fst_felem y) (snd_felem y) _
      Hlen_yC Hlen_yD Hjoin_y) as Hfp2_y;
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp2_fp_inst Fp2_repr_inst allocy (fst_felem y ++ snd_felem y)
      (map.putmany m_C m_D) Hfp2_y) as Hanybytes_y;
    unfold AbstractField.Placeholder in Hanybytes_y;
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_E (map.putmany m_F' m_G')))),
           (map.putmany m_C m_D);
    split; [exact Hanybytes_y |];
    split; [split;
      [rewrite (map.putmany_assoc m_C m_D);
       rewrite (map.putmany_assoc m_B (map.putmany m_C m_D));
       rewrite (map.putmany_comm m_B (map.putmany m_C m_D));
       [| map_disjoint_auto];
       rewrite <- (map.putmany_assoc (map.putmany m_C m_D) m_B);
       rewrite (map.putmany_assoc m_A (map.putmany m_C m_D));
       rewrite (map.putmany_comm m_A (map.putmany m_C m_D));
       [| map_disjoint_auto];
       rewrite <- (map.putmany_assoc (map.putmany m_C m_D) m_A);
       apply map.putmany_comm; map_disjoint_auto
      | map_disjoint_auto] |]).
    (* Stack dealloc allocx *)
    all: (
    pose proof (AbstractFElem_length _ _ _ HE) as Hlen_xE;
    pose proof (AbstractFElem_length _ _ _ HF') as Hlen_xF';
    assert (Hjoin_x : (FElem_Fp allocx (fst_felem x) ⋆
      FElem_Fp (word.add allocx felem_offset_word) (snd_felem x))
      (map.putmany m_E m_F'));
    [exists m_E, m_F'; split; [split; [reflexivity | assumption] |];
     split; [exact HE | exact HF'] |];
    pose proof (Fp2_raw_FElem_join allocx (fst_felem x) (snd_felem x) _
      Hlen_xE Hlen_xF' Hjoin_x) as Hfp2_x;
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp2_fp_inst Fp2_repr_inst allocx (fst_felem x ++ snd_felem x)
      (map.putmany m_E m_F') Hfp2_x) as Hanybytes_x;
    unfold AbstractField.Placeholder in Hanybytes_x;
    exists (map.putmany m_A (map.putmany m_B m_G')),
           (map.putmany m_E m_F');
    split; [exact Hanybytes_x |];
    split; [split;
      [rewrite (map.putmany_assoc m_E m_F' m_G');
       rewrite (map.putmany_assoc m_B (map.putmany m_E m_F'));
       rewrite (map.putmany_comm m_B (map.putmany m_E m_F'));
       [| map_disjoint_auto];
       rewrite <- (map.putmany_assoc (map.putmany m_E m_F') m_B);
       rewrite (map.putmany_assoc m_A (map.putmany m_E m_F'));
       rewrite (map.putmany_comm m_A (map.putmany m_E m_F'));
       [| map_disjoint_auto];
       rewrite <- (map.putmany_assoc (map.putmany m_E m_F') m_A);
       apply map.putmany_comm; map_disjoint_auto
      | map_disjoint_auto] |]).
    (* === Final postcondition === *)
    all: (
    cbv [list_map get];
    split; [exact eq_refl |]).
    (* True branch: output = y *)
    { pose proof (AbstractFElem_length _ _ _ HB) as Hlen_B.
      pose proof (AbstractFElem_length _ _ _ HA) as Hlen_A.
      assert (Hfe_join : (FElem_Fp pout (fst_felem y) ⋆
        FElem_Fp (word.add pout felem_offset_word) (snd_felem y))
        (map.putmany m_B m_A)).
      { exists m_B, m_A. split; [split; [reflexivity |] |].
        { map_disjoint_auto. }
        split; [exact HB | exact HA]. }
      pose proof (Fp2_raw_FElem_join pout (fst_felem y) (snd_felem y) _ Hlen_B Hlen_A Hfe_join) as Hfp2_out.
      replace (fst_felem y ++ snd_felem y) with y in Hfp2_out
        by (unfold fst_felem, snd_felem; symmetry; apply List.firstn_skipn).
      exists (map.putmany m_B m_A), m_G'.
      split; [split |].
      { rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. map_disjoint_auto. }
      { map_disjoint_auto. }
      split; [exact Hfp2_out | exact HG']. }
    (* False branch: output = x *)
    { pose proof (AbstractFElem_length _ _ _ HB) as Hlen_B.
      pose proof (AbstractFElem_length _ _ _ HA) as Hlen_A.
      assert (Hfe_join : (FElem_Fp pout (fst_felem x) ⋆
        FElem_Fp (word.add pout felem_offset_word) (snd_felem x))
        (map.putmany m_B m_A)).
      { exists m_B, m_A. split; [split; [reflexivity |] |].
        { map_disjoint_auto. }
        split; [exact HB | exact HA]. }
      pose proof (Fp2_raw_FElem_join pout (fst_felem x) (snd_felem x) _ Hlen_B Hlen_A Hfe_join) as Hfp2_out.
      replace (fst_felem x ++ snd_felem x) with x in Hfp2_out
        by (unfold fst_felem, snd_felem; symmetry; apply List.firstn_skipn).
      exists (map.putmany m_B m_A), m_G'.
      split; [split |].
      { rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. map_disjoint_auto. }
      { map_disjoint_auto. }
      split; [exact Hfp2_out | exact HG']. }
  Qed.

  Lemma Fp2_add_ok : program_logic_goal_for_function! Fp2_add.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFp2copy1 HFp2copy2 HFadd1 HFadd2.
    unfold spec_of_Fp2_add, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp2_add].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === First stackalloc: allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Second stackalloc: allocy === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    (* Convert anybytes to Fp2 FElems *)
    set (FElem_Fp := @AbstractField.FElem _ _ _ _ _ _ F_representation).
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    (* Decompose splits *)
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_mem0_sY Hd_sX_sY].
    (* Decompose Hmemx for later use *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfelem_x Hrx]]]].
    destruct Hmemx_sp as [Heq_mem0 Hd_xrx]. subst mem0.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_mem0_sY) as [Hd_x_sY Hd_rx_sY].
    (* === First copy call: inx → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFp2copy1 allocx px allocx_val x
           (fun m => (Rx ⋆ @AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst allocy allocy_val) m)
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
    (* === Second copy call: iny → allocy === *)
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
         cbv [list_map expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFp2copy2 allocy py allocy_val y
           (fun m => (AbstractField.FElem allocx x ⋆ Ry) m)
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
    (* === Phase 4: Two F.add calls at Fp level === *)
    (* Decompose copy2 postcondition *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    (* Split Fp2 FElems into Fp halves *)
    pose proof (Fp2_raw_FElem_split allocx x m_new1 Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax1 [m_ax2 [Hsp_ax [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax as [Heq_new1 Hd_ax].
    pose proof (Fp2_raw_FElem_split allocy y m_new2 Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay1 [m_ay2 [Hsp_ay [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay as [Heq_new2 Hd_ay].
    (* Decompose Hmemout into output and frame *)
    rewrite Heq_mem0_y in Hmemout.
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_yr Hd_out_rr].
    pose proof (Fp2_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o1 [m_o2 [Hsp_out [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_out as [Heq_out Hd_o12].
    (* Decompose bounded_by at Fp level *)
    unfold bounded_by, Fp2_repr_inst, Fp2_field_representation in Hbx, Hby.
    destruct Hbx as [Hbx1 Hbx2]. destruct Hby as [Hby1 Hby2].
    (* Derive disjointness for atomic regions *)
    subst m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* Build 7-way sep fact matching the putmany structure *)
    assert (Hsep7 : ((FElem_Fp allocy (fst_felem y) ⋆
      FElem_Fp (word.add allocy felem_offset_word) (snd_felem y)) ⋆
      ((FElem_Fp allocx (fst_felem x) ⋆
        FElem_Fp (word.add allocx felem_offset_word) (snd_felem x)) ⋆
        ((FElem_Fp pout (fst_felem old_out) ⋆
          FElem_Fp (word.add pout felem_offset_word) (snd_felem old_out)) ⋆ Rr)))
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
    (* === First F.add call: add(out, allocx, allocy) at Fp level === *)
    exists [pout; allocx; allocy]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFadd1 pout allocx allocy
           (fst_felem old_out) (fst_felem x) (fst_felem y)
           _ tr).
         split; [exact Hbx1 |].
         split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         pose proof Hsep7 as H'. ecancel_assumption. }
    (* Process first F.add postcondition *)
    intros t_add1 m_add1 rets_add1 [Hrets_add1 [Htr_add1 [out1 [Hfeval1 [Hbound1 Hsep_add1]]]]].
    subst rets_add1 t_add1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second F.add call: add(out+off, allocx+off, allocy+off) at Fp level === *)
    exists [word.add pout felem_offset_word; word.add allocx felem_offset_word;
            word.add allocy felem_offset_word].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_2nd_felem expr WeakestPrecondition.expr_body felem_offset].
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
    1: { eapply (HFadd2 (word.add pout felem_offset_word)
           (word.add allocx felem_offset_word) (word.add allocy felem_offset_word)
           (snd_felem old_out) (snd_felem x) (snd_felem y)
           _ tr).
         split; [exact Hbx2 |].
         split; [exact Hby2 |].
         split.
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         pose proof Hsep_add1 as H'. ecancel_assumption. }
    (* Process second F.add postcondition *)
    intros t_add2 m_add2 rets_add2 [Hrets_add2 [Htr_add2 [out2 [Hfeval2 [Hbound2 Hsep_add2]]]]].
    subst rets_add2 t_add2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
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
    pose proof (AbstractFElem_length _ _ _ HC) as Hlen_yC.
    pose proof (AbstractFElem_length _ _ _ HD) as Hlen_yD.
    pose proof (AbstractFElem_length _ _ _ HE) as Hlen_xE.
    pose proof (AbstractFElem_length _ _ _ HF') as Hlen_xF'.
    (* === Stack dealloc allocy === *)
    (* Join allocy Fp halves into Fp2 FElem *)
    assert (Hjoin_y : (FElem_Fp allocy (fst_felem y) ⋆
      FElem_Fp (word.add allocy felem_offset_word) (snd_felem y))
      (map.putmany m_C m_D)).
    { exists m_C, m_D. split; [split; [reflexivity | exact Hd_CD] |].
      split; [exact HC | exact HD]. }
    pose proof (Fp2_raw_FElem_join allocy (fst_felem y) (snd_felem y) _
      Hlen_yC Hlen_yD Hjoin_y) as Hfp2_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp2_fp_inst Fp2_repr_inst allocy (fst_felem y ++ snd_felem y)
      (map.putmany m_C m_D) Hfp2_y) as Hanybytes_y.
    unfold AbstractField.Placeholder in Hanybytes_y.
    (* Provide witnesses for allocy dealloc *)
    exists (map.putmany m_A (map.putmany m_B (map.putmany m_E (map.putmany m_F' m_G')))),
           (map.putmany m_C m_D).
    split. { exact Hanybytes_y. }
    split.
    { (* map.split: m = putmany m' mStack' /\ disjoint m' mStack' *)
      split.
      { (* Equality: rearrange putmany to move m_C, m_D to the end *)
        rewrite (map.putmany_assoc m_C m_D).
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
      { (* Disjointness: disjoint m' (putmany m_C m_D) *)
        apply map.disjoint_putmany_r. split.
        { (* disjoint m' m_C *)
          apply map.disjoint_putmany_l. split; [exact Hd_AC |].
          apply map.disjoint_putmany_l. split; [exact Hd_BC |].
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_CE). }
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_CF'). }
          { apply (proj1 (map.disjoint_comm _ _) Hd_CG'). } }
        { (* disjoint m' m_D *)
          apply map.disjoint_putmany_l. split; [exact Hd_AD |].
          apply map.disjoint_putmany_l. split; [exact Hd_BD |].
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_DE). }
          apply map.disjoint_putmany_l. split.
          { apply (proj1 (map.disjoint_comm _ _) Hd_DF'). }
          { apply (proj1 (map.disjoint_comm _ _) Hd_DG'). } } } }
    (* === Stack dealloc allocx === *)
    (* Join allocx Fp halves into Fp2 FElem *)
    assert (Hjoin_x : (FElem_Fp allocx (fst_felem x) ⋆
      FElem_Fp (word.add allocx felem_offset_word) (snd_felem x))
      (map.putmany m_E m_F')).
    { exists m_E, m_F'. split; [split; [reflexivity | exact Hd_EF'] |].
      split; [exact HE | exact HF']. }
    pose proof (Fp2_raw_FElem_join allocx (fst_felem x) (snd_felem x) _
      Hlen_xE Hlen_xF' Hjoin_x) as Hfp2_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp2_fp_inst Fp2_repr_inst allocx (fst_felem x ++ snd_felem x)
      (map.putmany m_E m_F') Hfp2_x) as Hanybytes_x.
    unfold AbstractField.Placeholder in Hanybytes_x.
    (* Provide witnesses for allocx dealloc *)
    exists (map.putmany m_A (map.putmany m_B m_G')),
           (map.putmany m_E m_F').
    split. { exact Hanybytes_x. }
    split.
    { (* map.split *)
      split.
      { (* Equality *)
        rewrite (map.putmany_assoc m_E m_F' m_G').
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
      { (* Disjointness: disjoint m'0 (putmany m_E m_F') *)
        apply map.disjoint_putmany_r. split.
        { (* disjoint m'0 m_E *)
          apply map.disjoint_putmany_l. split; [exact Hd_AE |].
          apply map.disjoint_putmany_l. split; [exact Hd_BE |].
          apply (proj1 (map.disjoint_comm _ _) Hd_EG'). }
        { (* disjoint m'0 m_F' *)
          apply map.disjoint_putmany_l. split; [exact Hd_AF' |].
          apply map.disjoint_putmany_l. split; [exact Hd_BF' |].
          apply (proj1 (map.disjoint_comm _ _) Hd_FG). } } }
    (* === Final postcondition === *)
    cbv [list_map get].
    split. { exact eq_refl. }
    split. { exact eq_refl. }
    (* Provide out1 ++ out2 as the Fp2 output *)
    exists (out1 ++ out2).
    assert (Hlen_out1 : Datatypes.length out1 =
      @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)
      by exact (AbstractFElem_length _ _ _ HB).
    assert (Hfst_app : fst_felem (out1 ++ out2) = out1).
    { unfold fst_felem. rewrite <- Hlen_out1.
      rewrite List.firstn_app, Nat.sub_diag. simpl (ListDef.firstn 0 _).
      rewrite List.app_nil_r. exact (List.firstn_all out1). }
    assert (Hsnd_app : snd_felem (out1 ++ out2) = out2).
    { unfold snd_felem. rewrite <- Hlen_out1.
      rewrite List.skipn_app, Nat.sub_diag. simpl (ListDef.skipn 0 _).
      rewrite List.skipn_all; [reflexivity | lia]. }
    (* feval condition *)
    split.
    { unfold feval. simpl @AbstractField.feval.
      unfold Fp2_repr_inst, Fp2_field_representation.
      rewrite Hfst_app, Hsnd_app.
      unfold addp2. simpl fst. simpl snd.
      rewrite Hfeval1, Hfeval2. reflexivity. }
    split.
    (* bounded_by condition *)
    { unfold bounded_by, Fp2_repr_inst, Fp2_field_representation.
      rewrite Hfst_app, Hsnd_app.
      split; [exact Hbound1 | exact Hbound2]. }
    (* sep reconstruction: (FElem_Fp2 pout (out1++out2) ⋆ Rr) m'0 *)
    { assert (Hlen_out2 : Datatypes.length out2 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)
        by exact (AbstractFElem_length _ _ _ HA).
      assert (Hfe_join : (FElem_Fp pout out1 ⋆
        FElem_Fp (word.add pout felem_offset_word) out2)
        (map.putmany m_B m_A)).
      { exists m_B, m_A. split; [split; [reflexivity |] |].
        { apply (proj1 (map.disjoint_comm _ _) Hd_AB). }
        split; [exact HB | exact HA]. }
      pose proof (Fp2_raw_FElem_join pout out1 out2 _ Hlen_out1 Hlen_out2 Hfe_join) as Hfp2_out.
      exists (map.putmany m_B m_A), m_G'.
      split; [split |].
      { rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. exact Hd_AB. }
      { apply map.disjoint_putmany_l. split; [exact Hd_BG' | exact Hd_AG']. }
      split; [exact Hfp2_out | exact HG']. }
  Qed.

  (* Fp2 multiplication: (a+bi)(c+di) = (ac+β·bd) + ((a+b)(c+d)-ac-bd)i
     Uses Karatsuba trick with 3 Fp-sized temps: v0=ac, v1=bd, v2=a+b
     Note: β=-1 for BLS12-381, so re = v0-v1, im = (a+b)(c+d)-v0-v1 *)
  Definition Fp2_mul : string * Syntax.func :=
    (AbstractField.mul (F:=Fp2), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v0;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v1;
        stackalloc (AbstractField.felem_size_in_bytes (F:=F)) as v2;
        (* v0 = inx.re * iny.re *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr.var "v0"; expr.var "inx"; expr.var "iny"]);
        (* v1 = inx.im * iny.im *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr.var "v1"; expr_2nd_felem (expr.var "inx"); expr_2nd_felem (expr.var "iny")]);
        (* v2 = inx.re + inx.im *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr.var "v2"; expr.var "inx"; expr_2nd_felem (expr.var "inx")]);
        (* out.im = iny.re + iny.im *)
        coq:(cmd.call [] (AbstractField.add (F:=F)) [expr_2nd_felem (expr.var "out"); expr.var "iny"; expr_2nd_felem (expr.var "iny")]);
        (* out.im = (iny.re+iny.im) * (inx.re+inx.im) *)
        coq:(cmd.call [] (AbstractField.mul (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v2"]);
        (* out.im = out.im - v0 *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v0"]);
        (* out.im = out.im - v1 = (a+b)(c+d) - ac - bd = ad+bc *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "out"); expr.var "v1"]);
        (* out.re = v0 - v1 = ac - bd *)
        coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "v0"; expr.var "v1"])
    ))).

  (* spec_of_Fp2_mul moved to QuadraticFieldExtensionsMul.v *)

  Lemma M_pos_prime : Znumtheory.prime (Z.pos M_pos).
  Proof.
    destruct prime_parameters_ok; auto.
  Qed.

  (* Fp2_mul_ok proof is in QuadraticFieldExtensionsMul.v for fast iteration *)

  (*subtraction in Fp2*)
  Definition Fp2_sub : string * Syntax.func :=
    (AbstractField.sub (F:=Fp2), (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as allocx;
      stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as allocy;
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (AbstractField.felem_copy (F:=Fp2)) [expr.var "allocy"; expr.var "iny"]);
      coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr.var "out"; expr.var "allocx"; expr.var "allocy"]);
      coq:(cmd.call [] (AbstractField.sub (F:=F)) [expr_2nd_felem (expr.var "out"); expr_2nd_felem (expr.var "allocx"); expr_2nd_felem (expr.var "allocy")])
    ))).

  Instance spec_of_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) := AbstractField.binop_spec AbstractField.bin_sub (F:=Fp2).

  Lemma Fp2_sub_ok : program_logic_goal_for_function! Fp2_sub.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFp2copy1 HFp2copy2 HFsub1 HFsub2.
    unfold spec_of_Fp2_sub, AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp2_sub].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === First stackalloc: allocx === *)
    split. { apply Z_mod_mult. }
    intros allocx mStackX m1 HstackX Hm1.
    repeat straightline.
    (* === Second stackalloc: allocy === *)
    split. { apply Z_mod_mult. }
    intros allocy mStackY m2 HstackY Hm2.
    (* Convert anybytes to Fp2 FElems *)
    set (FElem_Fp := @AbstractField.FElem _ _ _ _ _ _ F_representation).
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok allocx) as Hfbx.
    pose proof (@AbstractField.FElem_from_bytes _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst word_ok mem_ok allocy) as Hfby.
    unfold AbstractField.Placeholder in Hfbx, Hfby.
    pose proof (proj1 (Hfbx mStackX) HstackX) as [allocx_val Hallocx]. clear Hfbx.
    pose proof (proj1 (Hfby mStackY) HstackY) as [allocy_val Hallocy]. clear Hfby.
    (* Decompose splits *)
    destruct Hm1 as [Heq_m1 Hd_m1]. subst m1.
    destruct Hm2 as [Heq_m2 Hd_m2]. subst m2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m2) as [Hd_mem0_sY Hd_sX_sY].
    (* Decompose Hmemx for later use *)
    destruct Hmemx as [m_x [m_rx [Hmemx_sp [Hfelem_x Hrx]]]].
    destruct Hmemx_sp as [Heq_mem0 Hd_xrx]. subst mem0.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_m1) as [Hd_x_sX Hd_rx_sX].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_mem0_sY) as [Hd_x_sY Hd_rx_sY].
    (* === First copy call: inx → allocx === *)
    repeat straightline.
    exists [allocx; px]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFp2copy1 allocx px allocx_val x
           (fun m => (Rx ⋆ @AbstractField.FElem _ Fp2_fp_inst _ _ _ _ Fp2_repr_inst allocy allocy_val) m)
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
    (* === Second copy call: iny → allocy === *)
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
         cbv [list_map expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFp2copy2 allocy py allocy_val y
           (fun m => (AbstractField.FElem allocx x ⋆ Ry) m)
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
    (* === Phase 4: Two F.sub calls at Fp level === *)
    (* Decompose copy2 postcondition *)
    destruct Hsep_copy2 as [m_new2 [m_frame2 [[Heq_m'' Hd_n2_f2] [Hfelem_allocy Hframe2]]]].
    subst m_frame2.
    (* Split Fp2 FElems into Fp halves *)
    pose proof (Fp2_raw_FElem_split allocx x m_new1 Hfelem_allocx) as Hsplit_ax.
    destruct Hsplit_ax as [m_ax1 [m_ax2 [Hsp_ax [Hfe_ax1 Hfe_ax2]]]].
    destruct Hsp_ax as [Heq_new1 Hd_ax].
    pose proof (Fp2_raw_FElem_split allocy y m_new2 Hfelem_allocy) as Hsplit_ay.
    destruct Hsplit_ay as [m_ay1 [m_ay2 [Hsp_ay [Hfe_ay1 Hfe_ay2]]]].
    destruct Hsp_ay as [Heq_new2 Hd_ay].
    (* Decompose Hmemout into output and frame *)
    rewrite Heq_mem0_y in Hmemout.
    destruct Hmemout as [m_out [m_rr [Hsp_mo [Hfe_out Hrr_out]]]].
    destruct Hsp_mo as [Heq_yr Hd_out_rr].
    pose proof (Fp2_raw_FElem_split pout old_out m_out Hfe_out) as Hsplit_out.
    destruct Hsplit_out as [m_o1 [m_o2 [Hsp_out [Hfe_o1 Hfe_o2]]]].
    destruct Hsp_out as [Heq_out Hd_o12].
    (* Decompose bounded_by at Fp level *)
    unfold bounded_by, Fp2_repr_inst, Fp2_field_representation in Hbx, Hby.
    destruct Hbx as [Hbx1 Hbx2]. destruct Hby as [Hby1 Hby2].
    (* Derive disjointness for atomic regions *)
    subst m_out m_new1 m_new2.
    rewrite Heq_yr in Hd_n2_f2.
    rewrite Heq_yr in Hd_n1_mem0.
    subst m''.
    rewrite Heq_yr.
    (* Build 7-way sep fact matching the putmany structure *)
    assert (Hsep7 : ((FElem_Fp allocy (fst_felem y) ⋆
      FElem_Fp (word.add allocy felem_offset_word) (snd_felem y)) ⋆
      ((FElem_Fp allocx (fst_felem x) ⋆
        FElem_Fp (word.add allocx felem_offset_word) (snd_felem x)) ⋆
        ((FElem_Fp pout (fst_felem old_out) ⋆
          FElem_Fp (word.add pout felem_offset_word) (snd_felem old_out)) ⋆ Rr)))
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
    (* === First F.sub call: sub(out, allocx, allocy) at Fp level === *)
    exists [pout; allocx; allocy]. split.
    1: { subst l0 l.
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         cbv [list_map expr WeakestPrecondition.expr_body].
         eexists. split.
         { repeat (rewrite map.get_put_diff by (cbv; congruence)).
           apply map.get_put_same. }
         eexists. split.
         { apply map.get_put_same. }
         exact eq_refl. }
    eapply Semantics.weaken_call.
    1: { eapply (HFsub1 pout allocx allocy
           (fst_felem old_out) (fst_felem x) (fst_felem y)
           _ tr).
         split; [exact Hbx1 |].
         split; [exact Hby1 |].
         split.
         { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep7 as H'. ecancel_assumption. }
         pose proof Hsep7 as H'. ecancel_assumption. }
    (* Process first F.sub postcondition *)
    intros t_add1 m_add1 rets_add1 [Hrets_add1 [Htr_add1 [out1 [Hfeval1 [Hbound1 Hsep_add1]]]]].
    subst rets_add1 t_add1.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
    (* === Second F.sub call: sub(out+off, allocx+off, allocy+off) at Fp level === *)
    exists [word.add pout felem_offset_word; word.add allocx felem_offset_word;
            word.add allocy felem_offset_word].
    split.
    1: { subst l0 l.
         cbv [dexprs list_map expr_2nd_felem expr WeakestPrecondition.expr_body felem_offset].
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
    1: { eapply (HFsub2 (word.add pout felem_offset_word)
           (word.add allocx felem_offset_word) (word.add allocy felem_offset_word)
           (snd_felem old_out) (snd_felem x) (snd_felem y)
           _ tr).
         split; [exact Hbx2 |].
         split; [exact Hby2 |].
         split.
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         split.
         { eexists. pose proof Hsep_add1 as H'. ecancel_assumption. }
         pose proof Hsep_add1 as H'. ecancel_assumption. }
    (* Process second F.sub postcondition *)
    intros t_add2 m_add2 rets_add2 [Hrets_add2 [Htr_add2 [out2 [Hfeval2 [Hbound2 Hsep_add2]]]]].
    subst rets_add2 t_add2.
    cbv [map.putmany_of_list_zip].
    exists l0. split. { exact eq_refl. }
    repeat straightline.
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
    pose proof (AbstractFElem_length _ _ _ HC) as Hlen_yC.
    pose proof (AbstractFElem_length _ _ _ HD) as Hlen_yD.
    pose proof (AbstractFElem_length _ _ _ HE) as Hlen_xE.
    pose proof (AbstractFElem_length _ _ _ HF') as Hlen_xF'.
    (* === Stack dealloc allocy === *)
    assert (Hjoin_y : (FElem_Fp allocy (fst_felem y) ⋆
      FElem_Fp (word.add allocy felem_offset_word) (snd_felem y))
      (map.putmany m_C m_D)).
    { exists m_C, m_D. split; [split; [reflexivity | exact Hd_CD] |].
      split; [exact HC | exact HD]. }
    pose proof (Fp2_raw_FElem_join allocy (fst_felem y) (snd_felem y) _
      Hlen_yC Hlen_yD Hjoin_y) as Hfp2_y.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp2_fp_inst Fp2_repr_inst allocy (fst_felem y ++ snd_felem y)
      (map.putmany m_C m_D) Hfp2_y) as Hanybytes_y.
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
    assert (Hjoin_x : (FElem_Fp allocx (fst_felem x) ⋆
      FElem_Fp (word.add allocx felem_offset_word) (snd_felem x))
      (map.putmany m_E m_F')).
    { exists m_E, m_F'. split; [split; [reflexivity | exact Hd_EF'] |].
      split; [exact HE | exact HF']. }
    pose proof (Fp2_raw_FElem_join allocx (fst_felem x) (snd_felem x) _
      Hlen_xE Hlen_xF' Hjoin_x) as Hfp2_x.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _
      Fp2_fp_inst Fp2_repr_inst allocx (fst_felem x ++ snd_felem x)
      (map.putmany m_E m_F') Hfp2_x) as Hanybytes_x.
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
    assert (Hlen_out1 : Datatypes.length out1 =
      @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)
      by exact (AbstractFElem_length _ _ _ HB).
    assert (Hfst_app : fst_felem (out1 ++ out2) = out1).
    { unfold fst_felem. rewrite <- Hlen_out1.
      rewrite List.firstn_app, Nat.sub_diag. simpl (ListDef.firstn 0 _).
      rewrite List.app_nil_r. exact (List.firstn_all out1). }
    assert (Hsnd_app : snd_felem (out1 ++ out2) = out2).
    { unfold snd_felem. rewrite <- Hlen_out1.
      rewrite List.skipn_app, Nat.sub_diag. simpl (ListDef.skipn 0 _).
      rewrite List.skipn_all; [reflexivity | lia]. }
    split.
    { unfold feval. simpl @AbstractField.feval.
      unfold Fp2_repr_inst, Fp2_field_representation.
      rewrite Hfst_app, Hsnd_app.
      unfold subp2. simpl fst. simpl snd.
      rewrite Hfeval1, Hfeval2. reflexivity. }
    split.
    { unfold bounded_by, Fp2_repr_inst, Fp2_field_representation.
      rewrite Hfst_app, Hsnd_app.
      split; [exact Hbound1 | exact Hbound2]. }
    { assert (Hlen_out2 : Datatypes.length out2 =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ F_representation)
        by exact (AbstractFElem_length _ _ _ HA).
      assert (Hfe_join : (FElem_Fp pout out1 ⋆
        FElem_Fp (word.add pout felem_offset_word) out2)
        (map.putmany m_B m_A)).
      { exists m_B, m_A. split; [split; [reflexivity |] |].
        { apply (proj1 (map.disjoint_comm _ _) Hd_AB). }
        split; [exact HB | exact HA]. }
      pose proof (Fp2_raw_FElem_join pout out1 out2 _ Hlen_out1 Hlen_out2 Hfe_join) as Hfp2_out.
      exists (map.putmany m_B m_A), m_G'.
      split; [split |].
      { rewrite map.putmany_assoc. f_equal.
        apply map.putmany_comm. exact Hd_AB. }
      { apply map.disjoint_putmany_l. split; [exact Hd_BG' | exact Hd_AG']. }
      split; [exact Hfp2_out | exact HG']. }
  Qed.

  Lemma Fp2_felem_copy_ok : program_logic_goal_for_function! Fp2_felem_copy.
  Proof.
    cbv beta delta [program_logic_goal_for].
    intros functions EnvContains HFcopy1 HFcopy2.
    unfold spec_of_Fp2_copy, AbstractField.spec_of_felem_copy.
    intros pout px out x R Rout tr mem0 [Hmem0_1 Hmem0_2].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func Fp2_felem_copy].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for first call: [expr.var "out"; expr.var "x"] *)
    exists [pout; px]. split; [repeat straightline |].
    exists pout. split.
    { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
    cbv [list_map]. eexists. split.
    { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
      apply map.get_put_same. }
    exact eq_refl.
    (* === Set up context for first Fp copy call === *)
    set (FElem_Fp := @AbstractField.FElem _ _ _ _ _ _ F_representation).
    (* Decompose precondition 1 *)
    destruct Hmem0_1 as [m_x [m_or [Hsep1 [Hx Hor]]]].
    destruct Hor as [m_o [m_r [Hsep_or [Ho Hr]]]].
    (* Split Fp2 FElems into Fp halves *)
    pose proof (Fp2_raw_FElem_split px x m_x Hx) as [m_x1 [m_x2 [Hsep_x [Hx1 Hx2]]]].
    pose proof (Fp2_raw_FElem_split pout out m_o Ho) as [m_o1 [m_o2 [Hsep_o [Ho1 Ho2]]]].
    (* Decompose precondition 2 and use split_diff to relate decompositions *)
    destruct Hmem0_2 as [m_o' [m_rout [Hsep2 [Ho' Hrout]]]].
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp2_fp_inst Fp2_repr_inst pout out m_o Ho) as Hph_o.
    pose proof (@AbstractField.FElem_to_bytes _ _ _ _ word_ok mem_ok _ Fp2_fp_inst Fp2_repr_inst pout out m_o' Ho') as Hph_o'.
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
    subst m_o'.
    rewrite <- Heq_rout in Hrout.
    clear Heq_rout Hsd Hsep2 Hsep2' Hsplit_mem Hsplit_mem' Hph_o Hph_o' Ho'.
    (* Now: Hrout : Rout (map.putmany m_x m_r) *)
    (* Destruct inner splits and derive pairwise disjointness *)
    destruct Hsep_x as [Heq_x Hd_x12]. destruct Hsep_o as [Heq_o Hd_o12].
    subst m_x m_o.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_o) as [Hd_x1_o Hd_x2_o].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x1_o) as [Hd_x1_o1 Hd_x1_o2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_x2_o) as [Hd_x2_o1 Hd_x2_o2].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_x_r) as [Hd_x1_r Hd_x2_r].
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd_or) as [Hd_o1_r Hd_o2_r].
    clear Hd_x_o Hd_x_r Hd_or Hd1 Hd_x1_o Hd_x2_o.
    (* === First Fp copy call via weaken_call (eq-based Rout) === *)
    eapply Semantics.weaken_call.
    { eapply (HFcopy1 pout px (fst_felem out) (fst_felem x)
        (fun m => (FElem_Fp (word.add px felem_offset_word) (snd_felem x) ⋆
                   (FElem_Fp (word.add pout felem_offset_word) (snd_felem out) ⋆ R)) m)
        (fun m => m = map.putmany m_x1 (map.putmany m_x2 (map.putmany m_o2 m_r)))
        tr).
      split.
      { (* Condition 1: (FElem px (fst x) * FElem pout (fst out) * frame) mem0 *)
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
      { (* Condition 2: (FElem pout (fst out) * Rout1_eq) mem0 *)
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
    intros t' m' rets [Hrets [Htr Hsep_post1]].
    subst rets t'.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    repeat straightline.
    (* dexprs for second call — use eexists to avoid reduction issues *)
    eexists. split.
    { unfold dexprs. repeat straightline.
      exists pout. split.
      { rewrite map.get_put_diff by congruence. apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body felem_offset].
      repeat straightline.
      unfold list_map, expr_2nd_felem, felem_offset. repeat straightline.
      exists px. split. { apply map.get_put_same. }
      cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
      repeat straightline. exact eq_refl. }
    (* NOW destruct postcondition: eq-based Rout gives back original sub-memories *)
    destruct Hsep_post1 as [m_new1 [m_frame1 [Hsp_post1 [Hnew1 Hframe1]]]].
    subst m_frame1.
    destruct Hsp_post1 as [Heq_p1 Hd_p1].
    (* Derive disjointness for m_new1 vs original sub-memories *)
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p1) as [Hd_n1_x1 Hd_n1_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest) as [Hd_n1_x2 Hd_n1_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n1_rest2) as [Hd_n1_o2 Hd_n1_r].
    clear Hd_n1_rest Hd_n1_rest2.
    (* === Second Fp copy call (eq-based Rout) === *)
    eapply Semantics.weaken_call.
    { eapply (HFcopy2 (word.add pout felem_offset_word) (word.add px felem_offset_word)
        (snd_felem out) (snd_felem x)
        (fun m => (FElem_Fp pout (fst_felem x) ⋆ (FElem_Fp px (fst_felem x) ⋆ R)) m)
        (fun m => m = map.putmany m_new1 (map.putmany m_x1 (map.putmany m_x2 m_r)))
        tr).
      split.
      { (* Condition 1: (FElem (px+off) (snd x) * FElem (pout+off) (snd out) * R2) m' *)
        assert (Hd_n1x1_x2o2 : map.disjoint (map.putmany m_new1 m_x1) (map.putmany m_x2 m_o2)).
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_n1_x2 | exact Hd_n1_o2]. }
          { apply map.disjoint_putmany_r. split; [exact Hd_x12 | exact Hd_x1_o2]. } }
        exists (map.putmany m_x2 m_o2), (map.putmany m_new1 (map.putmany m_x1 m_r)).
        split; [split |].
        { subst m'.
          rewrite (map.putmany_assoc m_new1 m_x1).
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
      { (* Condition 2: (FElem (pout+off) (snd out) * Rout2_eq) m' *)
        exists m_o2, (map.putmany m_new1 (map.putmany m_x1 (map.putmany m_x2 m_r))).
        split; [split |].
        { subst m'.
          rewrite (map.putmany_assoc m_x2 m_o2 m_r).
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
    intros t'' m'' rets [Hrets [Htr2 Hsep_post2]].
    subst rets.
    cbv [map.putmany_of_list_zip].
    exists (#{ "out" => pout; "x" => px }#). split. { exact eq_refl. }
    cbv [list_map get]. split. { exact eq_refl. }
    split. { exact Htr2. }
    (* Destruct second postcondition *)
    destruct Hsep_post2 as [m_new2 [m_frame2 [Hsp_post2 [Hnew2 Hframe2]]]].
    subst m_frame2.
    destruct Hsp_post2 as [Heq_p2 Hd_p2].
    (* m'' = putmany m_new2 (putmany m_new1 (putmany m_x1 (putmany m_x2 m_r))) *)
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_p2) as [Hd_n2_n1 Hd_n2_rest].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest) as [Hd_n2_x1 Hd_n2_rest2].
    pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_n2_rest2) as [Hd_n2_x2 Hd_n2_r].
    clear Hd_n2_rest Hd_n2_rest2.
    (* Rewrite x = fst_felem x ++ snd_felem x *)
    assert (Hdecomp : x = fst_felem x ++ snd_felem x) by (symmetry; apply Fp2_list_decomp).
    rewrite Hdecomp.
    (* Provide witnesses for sep *)
    exists (map.putmany m_new1 m_new2), (map.putmany (map.putmany m_x1 m_x2) m_r).
    split; [split |].
    { (* equation: m'' = putmany (putmany m_new1 m_new2) (putmany (putmany m_x1 m_x2) m_r) *)
      subst m''.
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
    { (* Fp2_raw_FElem_join *)
      apply (Fp2_raw_FElem_join pout (fst_felem x) (snd_felem x)).
      { exact (AbstractFElem_length _ _ _ Hnew1). }
      { exact (AbstractFElem_length _ _ _ Hnew2). }
      exists m_new1, m_new2.
      split; [split; [reflexivity |] |].
      { unfold map.disjoint in *; intros k v1 v2 Hg1 Hg2; exact (Hd_n2_n1 k v2 v1 Hg2 Hg1). }
      split; [exact Hnew1 | exact Hnew2]. }
    { exact Hrout. }
  Qed.
End Fp2.
