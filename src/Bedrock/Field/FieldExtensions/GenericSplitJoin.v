(** * Generic FElem split/join for quadratic and cubic extensions.

    Provides parameterized split/join lemmas and Ltac tactics for any
    GenericQuadraticSpecs or GenericCubicSpecs instantiation.

    These replace the per-layer Fp2_raw_FElem_split/join,
    Fp6_raw_FElem_split/join, Fp12_raw_FElem_split/join with
    reusable generic versions.

    Key lemmas:
      - [qe_raw_FElem_split] / [qe_raw_FElem_join] — 2-way
      - [ce_raw_FElem_split] / [ce_raw_FElem_join] — 3-way
      - [qe_list_decomp] / [ce_list_decomp]
      - [generic_FElem_length]

    Key tactics:
      - [wp_qe_split] / [wp_qe_join]
      - [wp_ce_split] / [wp_ce_join] *)

Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.

Import Separation SeparationLogic.

(* ================================================================ *)
(* Reusable list lemmas (same as in QuadraticFieldExtensions.v)      *)
(* ================================================================ *)

Section ListLemmas.
  Context {A : Type}.

  Lemma firstn_skipn_app : forall (l : list A) n, firstn n l ++ skipn n l = l.
  Proof.
    intros. generalize dependent n. induction l.
    - destruct n; auto.
    - intros. destruct n; simpl; auto. rewrite IHl; auto.
  Qed.

  Lemma length_firstn_ge : forall (l : list A) n,
    (length l >= n)%nat -> length (firstn n l) = n.
  Proof.
    intros. generalize dependent n. induction l.
    - intros. simpl in H. destruct n; try lia. simpl. auto.
    - intros. destruct n; simpl; auto. apply f_equal. apply IHl. simpl in H. lia.
  Qed.

  Lemma length_skipn_double : forall (l : list A) n,
    (length l = n + n)%nat -> length (skipn n l) = n.
  Proof.
    intros l n H. pose proof (firstn_skipn_app l n) as H0.
    assert (Hge : (length l >= n)%nat) by lia.
    pose proof (length_firstn_ge l n Hge) as H1.
    rewrite <- H0 in H. rewrite app_length in H. lia.
  Qed.

  Lemma firstn_app_exact : forall (a b : list A),
    firstn (length a) (a ++ b) = a.
  Proof.
    intros. induction a; simpl; auto. rewrite IHa. auto.
  Qed.

  Lemma skipn_app_exact : forall (a b : list A),
    skipn (length a) (a ++ b) = b.
  Proof.
    intros. induction a; simpl; auto.
  Qed.

  Lemma firstn_app_le : forall (a b : list A) n,
    (length a = n)%nat -> firstn n (a ++ b) = a.
  Proof.
    intros. subst. apply firstn_app_exact.
  Qed.

  Lemma skipn_app_le : forall (a b : list A) n,
    (length a = n)%nat -> skipn n (a ++ b) = b.
  Proof.
    intros. subst. apply skipn_app_exact.
  Qed.
End ListLemmas.

(* ================================================================ *)
(* Generic AbstractField.FElem length extraction                    *)
(* ================================================================ *)

Section GenericLength.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.

  Context {F : Type} {fp : FieldParameters F}
          {fr : @FieldRepresentation F fp width BW word mem}.

  Lemma generic_FElem_length pout (out : @felem F fp _ _ _ _ fr) m :
    @FElem F fp _ _ _ _ fr pout out m ->
    length out = @felem_size_in_words F fp _ _ _ _ fr.
  Proof.
    unfold FElem, Bignum.Bignum.
    intros H. destruct H as [m1 [m2 [Hsplit [Hemp Harray]]]].
    destruct Hemp. assumption.
  Qed.
End GenericLength.

(* ================================================================ *)
(* Quadratic extension: 2-way split/join                            *)
(* ================================================================ *)

Section QuadraticSplitJoin.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.

  Context {BaseField : Type}.
  Context {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable nonresidue : BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Notation QE := (BaseField * BaseField)%type.

  Local Instance QE_fp : FieldParameters QE :=
    QE_field_parameters nonresidue prefix eq_dec_base.
  Local Instance QE_repr : @FieldRepresentation QE QE_fp width BW word mem :=
    QE_field_representation nonresidue prefix eq_dec_base.
  Local Notation base_size := (@felem_size_in_words _ base_fp _ _ _ _ base_repr).
  Local Notation base_offset :=
    (Memory.bytes_per_word width * Z.of_nat base_size).
  Local Notation base_offset_word := (word.of_Z base_offset).

  (* Use canonical decomposition from GenericQuadraticSpecs *)
  Local Notation qe_fst := (qe_fst_felem (base_repr:=base_repr)).
  Local Notation qe_snd := (qe_snd_felem (base_repr:=base_repr)).

  Lemma qe_list_decomp : forall l, qe_fst l ++ qe_snd l = l.
  Proof. intros. unfold qe_fst, qe_snd. apply firstn_skipn_app. Qed.

  (* Raw FElem split: QE → two base *)
  Lemma qe_raw_FElem_split pout out m :
    @FElem _ QE_fp _ _ _ _ QE_repr pout out m ->
    (@FElem _ base_fp _ _ _ _ base_repr pout (qe_fst out) *
     @FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word)
            (qe_snd out))%sep m.
  Proof.
    unfold FElem, Bignum.Bignum. intros [me [ma [Hms [Hemp Ha]]]].
    destruct Hemp as [Hme Hlen]. subst me.
    assert (m = ma) by (apply Properties.map.split_empty_l in Hms; exact Hms). subst.
    assert (Hlen2 : length out = (2 * base_size)%nat) by exact Hlen.
    assert (Hdecomp : out = qe_fst out ++ qe_snd out) by (symmetry; apply qe_list_decomp).
    rewrite Hdecomp in Ha.
    apply array_append' in Ha. destruct Ha as [m1 [m2 [Hms2 [Ha1 Ha2]]]].
    assert (Hlen1 : length (qe_fst out) = base_size)
      by (unfold qe_fst; apply length_firstn_ge; lia).
    rewrite Hlen1 in Ha2.
    rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha2.
    exists m1, m2. split; [exact Hms2 |]. split.
    - exists map.empty, m1. split. { apply Properties.map.split_empty_l. reflexivity. }
      split. { exact (conj eq_refl Hlen1). } exact Ha1.
    - exists map.empty, m2. split. { apply Properties.map.split_empty_l. reflexivity. }
      split. { split. { exact eq_refl. }
        unfold qe_snd. apply length_skipn_double. lia. }
      exact Ha2.
  Qed.

  (* Raw FElem join: two base → QE *)
  Lemma qe_raw_FElem_join pout out1 out2 m :
    length out1 = base_size ->
    length out2 = base_size ->
    (@FElem _ base_fp _ _ _ _ base_repr pout out1 *
     @FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word) out2)%sep m ->
    @FElem _ QE_fp _ _ _ _ QE_repr pout (out1 ++ out2) m.
  Proof.
    unfold FElem, Bignum.Bignum. intros Hlen1 Hlen2 [m1 [m2 [Hms [H1 H2]]]].
    destruct H1 as [me1 [ma1 [Hms1 [Hemp1 Ha1]]]].
    destruct Hemp1 as [Hme1 Hlen1']. subst me1.
    assert (m1 = ma1) by (apply Properties.map.split_empty_l in Hms1; exact Hms1). subst.
    destruct H2 as [me2 [ma2 [Hms2 [Hemp2 Ha2]]]].
    destruct Hemp2 as [Hme2 Hlen2']. subst me2.
    assert (m2 = ma2) by (apply Properties.map.split_empty_l in Hms2; exact Hms2). subst.
    exists map.empty, m. split. { apply Properties.map.split_empty_l. reflexivity. }
    split.
    - split; [exact eq_refl |]. rewrite app_length.
      change (@felem_size_in_words _ QE_fp _ _ _ _ QE_repr)
        with (2 * base_size)%nat. lia.
    - apply array_append'.
      exists ma1, ma2. split; [exact Hms |]. split; [exact Ha1 |].
      rewrite Hlen1'. rewrite <- (@word.ring_morph_mul _ _ word_ok). exact Ha2.
  Qed.

  (** Framed split: given (QE_FElem p x * R) m, produce
      (Base_FElem p (fst x) * (Base_FElem (p+off) (snd x) * R)) m. *)
  Lemma qe_raw_FElem_split_in_sep pout (out : list word) (R : mem -> Prop) m :
    (@FElem _ QE_fp _ _ _ _ QE_repr pout out * R)%sep m ->
    (@FElem _ base_fp _ _ _ _ base_repr pout (qe_fst out) *
     (@FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word)
             (qe_snd out) * R))%sep m.
  Proof.
    intros [m1 [m2 [[Heq Hd] [Hqe HR]]]].
    pose proof (qe_raw_FElem_split pout out m1 Hqe)
      as [ma [mb [[Heq2 Hd2] [Ha Hb]]]].
    subst m1.
    pose proof (proj1 (Properties.map.disjoint_putmany_l _ _ _) Hd) as [Hd_a Hd_b].
    exists ma, (map.putmany mb m2).
    split; [split |].
    { subst m. rewrite Properties.map.putmany_assoc. reflexivity. }
    { apply Properties.map.disjoint_putmany_r. split; [exact Hd2 | exact Hd_a]. }
    split; [exact Ha |].
    exists mb, m2.
    split; [split; [reflexivity | exact Hd_b] |].
    split; [exact Hb | exact HR].
  Qed.

  (** Framed join: given (Base_FElem p a * (Base_FElem (p+off) b * R)) m
      plus length witnesses, produce (QE_FElem p (a++b) * R) m. *)
  Lemma qe_raw_FElem_join_in_sep pout (a b : list word) (R : mem -> Prop) m :
    length a = base_size ->
    length b = base_size ->
    (@FElem _ base_fp _ _ _ _ base_repr pout a *
     (@FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word) b * R))%sep m ->
    (@FElem _ QE_fp _ _ _ _ QE_repr pout (a ++ b) * R)%sep m.
  Proof.
    intros Hla Hlb [ma [mr1 [[Heq1 Hd1] [Ha Hr1]]]].
    destruct Hr1 as [mb [mr2 [[Heq2 Hd2] [Hb HR]]]].
    subst mr1.
    pose proof (proj1 (Properties.map.disjoint_putmany_r _ _ _) Hd1) as [Hd_ab Hd_ar].
    exists (map.putmany ma mb), mr2.
    split; [split |].
    { subst m. rewrite Properties.map.putmany_assoc. reflexivity. }
    { apply Properties.map.disjoint_putmany_l. split; [exact Hd_ar |exact Hd2]. }
    split.
    - apply (qe_raw_FElem_join pout a b (map.putmany ma mb) Hla Hlb).
      exists ma, mb. split; [split; [reflexivity | exact Hd_ab] |].
      split; [exact Ha | exact Hb].
    - exact HR.
  Qed.

End QuadraticSplitJoin.

(* ================================================================ *)
(* Cubic extension: 3-way split/join                                *)
(* ================================================================ *)

Section CubicSplitJoin.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.

  Context {BaseField : Type}.
  Context {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable mul_by_nr : BaseField -> BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Notation CE := (BaseField * BaseField * BaseField)%type.

  Local Instance CE_fp : FieldParameters CE :=
    CE_field_parameters mul_by_nr prefix eq_dec_base.
  Local Instance CE_repr : @FieldRepresentation CE CE_fp width BW word mem :=
    CE_field_representation mul_by_nr prefix eq_dec_base.
  Local Notation base_size := (@felem_size_in_words _ base_fp _ _ _ _ base_repr).
  Local Notation base_offset :=
    (Memory.bytes_per_word width * Z.of_nat base_size).
  Local Notation base_offset_word := (word.of_Z base_offset).

  (* List decomposition *)
  (* Local decomposition — avoids cross-section typeclass resolution *)
  Local Definition ce_c0 (l : list word) := firstn base_size l.
  Local Definition ce_c1 (l : list word) := firstn base_size (skipn base_size l).
  Local Definition ce_c2 (l : list word) := skipn (2 * base_size) l.

  Lemma ce_list_decomp : forall l, ce_c0 l ++ ce_c1 l ++ ce_c2 l = l.
  Proof.
    intros l. unfold ce_c0, ce_c1, ce_c2.
    set (n := base_size).
    transitivity (firstn n l ++ skipn n l).
    2: { apply firstn_skipn_app. }
    f_equal.
    transitivity (firstn n (skipn n l) ++ skipn n (skipn n l)).
    2: { apply firstn_skipn_app. }
    f_equal.
    replace (2 * n)%nat with (n + n)%nat by lia.
    symmetry. apply List.skipn_skipn.
  Qed.

  Local Lemma ce_size_eq :
    @felem_size_in_words _ CE_fp _ _ _ _ CE_repr = (3 * base_size)%nat.
  Proof. reflexivity. Qed.

  (* Raw Bignum split: CE Bignum → three base Bignums *)
  Lemma ce_raw_FElem_split pout out m :
    @FElem _ CE_fp _ _ _ _ CE_repr pout out m ->
    (@FElem _ base_fp _ _ _ _ base_repr pout (ce_c0 out) *
     (@FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word)
             (ce_c1 out) *
      @FElem _ base_fp _ _ _ _ base_repr
             (word.add pout (word.of_Z (2 * base_offset)))
             (ce_c2 out)))%sep m.
  Proof.
    unfold FElem, Bignum.Bignum.
    intros [me [ma [Hms [Hemp Ha]]]]. destruct Hemp as [Hme Hlen]. subst me.
    assert (m = ma) by (apply Properties.map.split_empty_l in Hms; exact Hms). subst.
    change (@felem_size_in_words _ CE_fp _ _ _ _ CE_repr)
      with (3 * base_size)%nat in Hlen.
    (* Step 1: split c0 from (c1++c2) — DON'T use app_assoc *)
    assert (Hdecomp : out = ce_c0 out ++ (ce_c1 out ++ ce_c2 out))
      by (symmetry; apply ce_list_decomp).
    rewrite Hdecomp in Ha.
    apply array_append' in Ha. destruct Ha as [m0 [m12 [Hms0 [Ha0 Ha12]]]].
    assert (Hlen0 : length (ce_c0 out) = base_size)
      by (unfold ce_c0; apply length_firstn_ge; lia).
    (* Step 2: split c1 from c2 *)
    rewrite Hlen0 in Ha12. rewrite <- (@word.ring_morph_mul _ _ word_ok) in Ha12.
    apply array_append' in Ha12. destruct Ha12 as [m1 [m2 [Hms12 [Ha1 Ha2]]]].
    assert (Hlen1 : length (ce_c1 out) = base_size).
    { unfold ce_c1. apply length_firstn_ge.
      rewrite skipn_length. lia. }
    rewrite Hlen1 in Ha2.
    replace (word.add (word.add pout base_offset_word)
                      (word.mul (word.of_Z (Memory.bytes_per_word width))
                                (word.of_Z (Z.of_nat base_size))))
      with (word.add pout (word.of_Z (2 * base_offset))) in Ha2.
    2: { unfold base_offset_word.
         rewrite <- !(@word.ring_morph_mul _ _ word_ok).
         rewrite <- word.add_assoc.
         rewrite <- (@word.ring_morph_add _ _ word_ok).
         fold (@word.of_Z _ word).
         replace (base_offset + base_offset) with (2 * base_offset) by lia.
         reflexivity. }
    (* Build 3-way sep *)
    exists m0, (map.putmany m1 m2).
    split.
    { destruct Hms0 as [Hms0eq Hms0d]. destruct Hms12 as [Hms12eq Hms12d].
      split.
      - rewrite Hms0eq, Hms12eq. reflexivity.
      - rewrite Hms12eq in Hms0d.
        apply map.disjoint_putmany_r in Hms0d. destruct Hms0d.
        apply map.disjoint_putmany_r. split; assumption. }
    split.
    - exists map.empty, m0. split. { apply Properties.map.split_empty_l. reflexivity. }
      split; [exact (conj eq_refl Hlen0) | exact Ha0].
    - exists m1, m2.
      destruct Hms12 as [-> Hd].
      split; [split; [reflexivity | exact Hd] |].
      split.
      + exists map.empty, m1. split. { apply Properties.map.split_empty_l. reflexivity. }
        split; [exact (conj eq_refl Hlen1) | exact Ha1].
      + exists map.empty, m2. split. { apply Properties.map.split_empty_l. reflexivity. }
        split; [split; [exact eq_refl |] | exact Ha2].
        unfold ce_c2. replace (2 * base_size)%nat with (base_size + base_size)%nat by lia.
        rewrite <- List.skipn_skipn. rewrite skipn_length.
        rewrite skipn_length. lia.
  Qed.

  (* Raw Bignum join: three base Bignums → CE Bignum *)
  Lemma ce_raw_FElem_join pout out0 out1 out2 m :
    length out0 = base_size ->
    length out1 = base_size ->
    length out2 = base_size ->
    (@FElem _ base_fp _ _ _ _ base_repr pout out0 *
     (@FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word) out1 *
      @FElem _ base_fp _ _ _ _ base_repr
             (word.add pout (word.of_Z (2 * base_offset))) out2))%sep m ->
    @FElem _ CE_fp _ _ _ _ CE_repr pout (out0 ++ out1 ++ out2) m.
  Proof.
    intros Hlen0 Hlen1 Hlen2 H.
    unfold FElem, Bignum.Bignum in *.
    destruct H as [m0 [m12 [Hms0 [H0 H12]]]].
    destruct H0 as [me0 [ma0 [Hms_0 [Hemp0 Ha0]]]].
    destruct Hemp0 as [Hme0 Hlen0']. subst me0.
    assert (m0 = ma0) by (apply Properties.map.split_empty_l in Hms_0; exact Hms_0). subst.
    destruct H12 as [m1 [m2 [Hms12 [H1 H2]]]].
    destruct H1 as [me1 [ma1 [Hms_1 [Hemp1 Ha1]]]].
    destruct Hemp1 as [Hme1 Hlen1']. subst me1.
    assert (m1 = ma1) by (apply Properties.map.split_empty_l in Hms_1; exact Hms_1). subst.
    destruct H2 as [me2 [ma2 [Hms_2 [Hemp2 Ha2]]]].
    destruct Hemp2 as [Hme2 Hlen2']. subst me2.
    assert (m2 = ma2) by (apply Properties.map.split_empty_l in Hms_2; exact Hms_2). subst.
    exists map.empty, m. split. { apply Properties.map.split_empty_l. reflexivity. }
    split.
    - split; [exact eq_refl |].
      rewrite !app_length.
      change (@felem_size_in_words _ CE_fp _ _ _ _ CE_repr)
        with (3 * base_size)%nat. lia.
    - (* Reconstruct array: out0 ++ out1 ++ out2 = out0 ++ (out1 ++ out2) *)
      destruct Hms0 as [-> Hms0d]. destruct Hms12 as [-> Hms12d].
      apply array_append'.
      (* First: combine out1 ++ out2 array *)
      assert (Harray12 :
        array scalar (word.of_Z (Memory.bytes_per_word width))
              (word.add pout base_offset_word) (out1 ++ out2)
              (map.putmany ma1 ma2)).
      { apply array_append'.
        exists ma1, ma2. split; [split; [reflexivity | exact Hms12d] |]. split; [exact Ha1 |].
        rewrite Hlen1'.
        replace (word.add (word.add pout base_offset_word)
                          (word.mul (word.of_Z (Memory.bytes_per_word width))
                                    (word.of_Z (Z.of_nat base_size))))
          with (word.add pout (word.of_Z (2 * base_offset))).
        2: { unfold base_offset_word.
             rewrite <- !(@word.ring_morph_mul _ _ word_ok).
             rewrite <- word.add_assoc. rewrite <- (@word.ring_morph_add _ _ word_ok).
             fold (@word.of_Z _ word).
             replace (base_offset + base_offset) with (2 * base_offset) by lia.
             reflexivity. }
        exact Ha2. }
      exists ma0, (map.putmany ma1 ma2).
      split.
      { split; [reflexivity |].
        apply map.disjoint_putmany_r in Hms0d. destruct Hms0d.
        apply map.disjoint_putmany_r. split; assumption. }
      split; [exact Ha0 |].
      rewrite Hlen0'. rewrite <- (@word.ring_morph_mul _ _ word_ok).
      exact Harray12.
  Qed.

  (** Framed split: given (CE_FElem p x * R) m, produce
      (Base_FElem p (c0 x) * (Base_FElem (p+off) (c1 x) *
       (Base_FElem (p+2*off) (c2 x) * R))) m. *)
  Lemma ce_raw_FElem_split_in_sep pout (out : list word) (R : mem -> Prop) m :
    (@FElem _ CE_fp _ _ _ _ CE_repr pout out * R)%sep m ->
    (@FElem _ base_fp _ _ _ _ base_repr pout (ce_c0 out) *
     (@FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word)
             (ce_c1 out) *
      (@FElem _ base_fp _ _ _ _ base_repr
              (word.add pout (word.of_Z (2 * base_offset)))
              (ce_c2 out) * R)))%sep m.
  Proof.
    intros [mce [mR [[HeqM HdM] [Hce HR]]]].
    pose proof (ce_raw_FElem_split pout out mce Hce)
      as [m0 [m12 [Hsp012 [H0 H12]]]].
    destruct Hsp012 as [Heq012 Hd012].
    destruct H12 as [m1 [m2 [Hsp12 [H1 H2]]]].
    destruct Hsp12 as [Heq12 Hd12].
    subst m12 mce m.
    (* Derive disjointness facts *)
    pose proof (proj1 (Properties.map.disjoint_putmany_l _ _ _) HdM) as [Hd0R Hd12R].
    pose proof (proj1 (Properties.map.disjoint_putmany_l _ _ _) Hd12R) as [Hd1R Hd2R].
    pose proof (proj1 (Properties.map.disjoint_putmany_r _ _ _) Hd012) as [Hd01 Hd02].
    (* Rebuild 4-way framed sep *)
    exists m0, (map.putmany m1 (map.putmany m2 mR)).
    split; [split |].
    { rewrite !Properties.map.putmany_assoc. reflexivity. }
    { apply Properties.map.disjoint_putmany_r. split; [exact Hd01 |].
      apply Properties.map.disjoint_putmany_r. split; [exact Hd02 | exact Hd0R]. }
    split; [exact H0 |].
    exists m1, (map.putmany m2 mR).
    split; [split; [reflexivity |] |].
    { apply Properties.map.disjoint_putmany_r. split; [exact Hd12 | exact Hd1R]. }
    split; [exact H1 |].
    exists m2, mR.
    split; [split; [reflexivity | exact Hd2R] |].
    split; [exact H2 | exact HR].
  Qed.

  (** Framed join: given 3 Base_FElems at consecutive offsets + R,
      produce (CE_FElem p (c0++c1++c2) * R) m. *)
  Lemma ce_raw_FElem_join_in_sep pout (c0v c1v c2v : list word) (R : mem -> Prop) m :
    length c0v = base_size ->
    length c1v = base_size ->
    length c2v = base_size ->
    (@FElem _ base_fp _ _ _ _ base_repr pout c0v *
     (@FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word) c1v *
      (@FElem _ base_fp _ _ _ _ base_repr
              (word.add pout (word.of_Z (2 * base_offset)))
              c2v * R)))%sep m ->
    (@FElem _ CE_fp _ _ _ _ CE_repr pout (c0v ++ c1v ++ c2v) * R)%sep m.
  Proof.
    intros Hl0 Hl1 Hl2 [m0 [mr0 [[Heq0 Hd0] [H0 Hr0]]]].
    destruct Hr0 as [m1 [mr1 [[Heq1 Hd1] [H1 Hr1]]]].
    destruct Hr1 as [m2 [mr2 [[Heq2 Hd2] [H2 HR]]]].
    subst mr0 mr1.
    (* Derive all pairwise disjointness from nested putmany *)
    pose proof (proj1 (Properties.map.disjoint_putmany_r _ _ _) Hd0) as [Hd01 Hd0_2r].
    pose proof (proj1 (Properties.map.disjoint_putmany_r _ _ _) Hd0_2r) as [Hd02 Hd0r].
    pose proof (proj1 (Properties.map.disjoint_putmany_r _ _ _) Hd1) as [Hd12 Hd1r].
    (* Build 3-way bare sep for ce_raw_FElem_join *)
    set (mce := map.putmany m0 (map.putmany m1 m2)).
    assert (Hbare : (@FElem _ base_fp _ _ _ _ base_repr pout c0v *
      (@FElem _ base_fp _ _ _ _ base_repr (word.add pout base_offset_word) c1v *
       @FElem _ base_fp _ _ _ _ base_repr
              (word.add pout (word.of_Z (2 * base_offset))) c2v))%sep mce).
    { exists m0, (map.putmany m1 m2).
      split; [split; [reflexivity |] |].
      { apply Properties.map.disjoint_putmany_r. split; [exact Hd01 | exact Hd02]. }
      split; [exact H0 |].
      exists m1, m2. split; [split; [reflexivity | exact Hd12] |].
      split; [exact H1 | exact H2]. }
    pose proof (ce_raw_FElem_join pout c0v c1v c2v mce Hl0 Hl1 Hl2 Hbare) as Hce.
    exists mce, mr2.
    split; [split |].
    { subst mce m. rewrite !Properties.map.putmany_assoc. reflexivity. }
    { subst mce. apply Properties.map.disjoint_putmany_l. split; [exact Hd0r |].
      apply Properties.map.disjoint_putmany_l. split; [exact Hd1r | exact Hd2]. }
    split; [exact Hce | exact HR].
  Qed.

End CubicSplitJoin.

(* ================================================================ *)
(* Ltac: generic split/join tactics                                 *)
(* ================================================================ *)

(** [wp_qe_split H] — Split a quadratic extension FElem hypothesis H
    into two base-field FElem hypotheses + disjointness facts. *)
Ltac wp_qe_split H :=
  let m1 := fresh "m" in let m2 := fresh "m" in
  let Hsep := fresh "Hsep" in
  let H1 := fresh "Hfe" in let H2 := fresh "Hfe" in
  let Heq := fresh "Heq" in let Hd := fresh "Hd" in
  pose proof (qe_raw_FElem_split _ _ _ _ _ _ _ H)
    as [m1 [m2 [Hsep [H1 H2]]]];
  destruct Hsep as [Heq Hd]; try subst;
  split_all_disjointness.

(** [wp_qe_join ptr Hfst Hsnd m_fst m_snd] — Join two base-field
    FElem hypotheses back into a quadratic extension FElem. *)
Ltac wp_qe_join ptr Hfst Hsnd m_fst m_snd :=
  let Hlen_fst := fresh "Hlen" in
  let Hlen_snd := fresh "Hlen" in
  pose proof (generic_FElem_length _ _ _ Hfst) as Hlen_fst;
  pose proof (generic_FElem_length _ _ _ Hsnd) as Hlen_snd;
  let Hjoin := fresh "Hjoin" in
  assert (Hjoin : (@FElem _ _ _ _ _ _ _ ptr _ *
                   @FElem _ _ _ _ _ _ _ _ _)%sep (map.putmany m_fst m_snd))
    by (exists m_fst, m_snd; split;
        [split; [reflexivity | map_disjoint_auto] |];
        split; [exact Hfst | exact Hsnd]);
  let Hqe := fresh "Hqe" in
  pose proof (qe_raw_FElem_join _ _ _ _ _ _ ptr _ _ (map.putmany m_fst m_snd)
    Hlen_fst Hlen_snd Hjoin) as Hqe.

(** [wp_ce_split H] — Split a cubic extension FElem hypothesis H
    into three base-field FElem hypotheses + disjointness facts. *)
Ltac wp_ce_split H :=
  let m0 := fresh "m" in let m12 := fresh "m" in
  let m1 := fresh "m" in let m2 := fresh "m" in
  let Hsep0 := fresh "Hsep" in let Hsep12 := fresh "Hsep" in
  let H0 := fresh "Hfe" in let H12 := fresh "Hfe" in
  let H1 := fresh "Hfe" in let H2 := fresh "Hfe" in
  let Heq := fresh "Heq" in let Hd := fresh "Hd" in
  pose proof (ce_raw_FElem_split _ _ _ _ _ _ _ H)
    as [m0 [m12 [Hsep0 [H0 H12]]]];
  destruct Hsep0 as [Heq Hd]; try subst;
  destruct H12 as [m1 [m2 [Hsep12 [H1 H2]]]];
  destruct Hsep12 as [Heq Hd]; try subst;
  split_all_disjointness.

(** [wp_ce_join ptr H0 H1 H2 m0 m1 m2] — Join three base-field
    FElem hypotheses back into a cubic extension FElem. *)
Ltac wp_ce_join ptr H0 H1 H2 m0 m1 m2 :=
  let Hlen0 := fresh "Hlen" in
  let Hlen1 := fresh "Hlen" in
  let Hlen2 := fresh "Hlen" in
  pose proof (generic_FElem_length _ _ _ H0) as Hlen0;
  pose proof (generic_FElem_length _ _ _ H1) as Hlen1;
  pose proof (generic_FElem_length _ _ _ H2) as Hlen2;
  let Hjoin := fresh "Hjoin" in
  assert (Hjoin : (@FElem _ _ _ _ _ _ _ ptr _ *
                   (@FElem _ _ _ _ _ _ _ _ _ *
                    @FElem _ _ _ _ _ _ _ _ _))%sep
                  (map.putmany m0 (map.putmany m1 m2)))
    by (exists m0, (map.putmany m1 m2); split;
        [split; [reflexivity | map_disjoint_auto] |];
        split; [exact H0 |
                exists m1, m2; split;
                [split; [reflexivity | map_disjoint_auto] |];
                split; [exact H1 | exact H2]]);
  let Hce := fresh "Hce" in
  pose proof (ce_raw_FElem_join _ _ _ _ _ _ ptr _ _ _
    (map.putmany m0 (map.putmany m1 m2))
    Hlen0 Hlen1 Hlen2 Hjoin) as Hce.
