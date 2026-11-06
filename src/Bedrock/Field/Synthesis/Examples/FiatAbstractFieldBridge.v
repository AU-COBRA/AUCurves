(** * From fiat-crypto's field specs to the AbstractField specs.

    fiat-crypto ([Crypto.Bedrock.Specs.Field]) states the specs of its synthesized field
    functions with [felem = {l | length l = n}], memory layout [array scalar], and the output
    buffer given as bytes ([out$@pout], of length [felem_size_in_bytes]).  The AUCurves tower
    ([Bedrock.Specs.AbstractField]) uses [felem = list word] and the layout
    [FElem = Bignum n] (length fact + [array scalar]) for inputs and outputs alike.

    [abstract_rep] is the AbstractField representation that reuses the fields of a fiat
    representation (as [BLS12_MillerStepFunctional.bls12_Fp_rep] does).  For it:
    - [binop_spec_of_fiat], [unop_spec_of_fiat]: a fiat binop / unop spec implies the
      AbstractField spec with the same name, model and bounds;
    - [felem_copy_spec_of_fiat]: the fiat [felem_copy] spec implies the AbstractField one;
    - [from_word_spec_of_fiat]: the fiat [from_word] spec implies [PrimeField.spec_of_from_word].
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import coqutil.Byte.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Crypto.Bedrock.Specs.Field.
Require Bedrock.Specs.AbstractField.
Require Bedrock.Specs.PrimeField.
Import bedrock2.Memory.

Local Open Scope Z_scope.

Section Bridge.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {fparams : Field.FieldParameters}
          {frep : Field.FieldRepresentation (field_parameters:=fparams)}
          {frep_ok : Field.FieldRepresentation_ok (field_representation:=frep)}.
  Context {aparams : AbstractField.FieldParameters (F Field.M_pos)}.

  Definition abstract_rep : AbstractField.FieldRepresentation (F:=F Field.M_pos) :=
    {| AbstractField.feval := @Field.feval _ _ _ _ _ frep;
       AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ frep;
       AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ frep;
       AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ frep;
       AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ frep;
       AbstractField.bounds := @Field.bounds _ _ _ _ _ frep;
       AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ frep;
       AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ frep;
       AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ frep |}.

  Local Notation n := (@Field.felem_size_in_words _ _ _ _ _ frep).
  Local Notation AFElem := (@AbstractField.FElem _ aparams _ _ _ _ abstract_rep).
  Local Notation FFElem := (@Field.FElem _ _ _ _ _ frep).

  (** ** Memory layout *)

  Lemma AFElem_length p x m R : (AFElem p x * R)%sep m -> length x = n.
  Proof.
    intros H. cbv [AbstractField.FElem abstract_rep Bignum] in H.
    eapply sep_assoc in H. eapply sep_emp_l in H. exact (proj1 H).
  Qed.

  Lemma AFElem_iff_FFElem p x (Hx : length x = n) :
    Lift1Prop.iff1 (AFElem p x) (FFElem p (exist _ x Hx)).
  Proof.
    cbv [AbstractField.FElem abstract_rep Bignum Field.FElem proj1_sig].
    split; intros H.
    - eapply sep_emp_l in H. exact (proj2 H).
    - eapply sep_emp_l. exact (conj Hx H).
  Qed.

  Lemma FFElem_iff_AFElem p (x : Field.felem) :
    Lift1Prop.iff1 (FFElem p x) (AFElem p (proj1_sig x)).
  Proof.
    destruct x as [x Hx]. symmetry. exact (AFElem_iff_FFElem p x Hx).
  Qed.

  (** The bytes of an AbstractField element, as the fiat output buffer. *)
  Lemma AFElem_to_bytes p x (Hx : length x = n) :
    Lift1Prop.iff1 (AFElem p x)
      (eq (map.of_list_word_at p (ws2bs (Z.to_nat (bytes_per_word width)) x))).
  Proof.
    rewrite (AFElem_iff_FFElem p x Hx). exact (Field.felem_to_bytes p (exist _ x Hx)).
  Qed.

  Lemma AFElem_bytes_length (x : list (@word.rep _ word)) (Hx : length x = n) :
    length (ws2bs (Z.to_nat (bytes_per_word width)) x) = Z.to_nat Field.felem_size_in_bytes.
  Proof. exact (Field.ws2bs_felem_length (exist _ x Hx)). Qed.

  Lemma sep_AFElem_to_bytes p x R m :
    (AFElem p x * R)%sep m ->
    exists Hx : length x = n,
      (eq (map.of_list_word_at p (ws2bs (Z.to_nat (bytes_per_word width)) x)) * R)%sep m.
  Proof.
    intros H. pose proof (AFElem_length _ _ _ _ H) as Hx. exists Hx.
    seprewrite_in (AFElem_to_bytes p x Hx) H. exact H.
  Qed.

  Lemma ex_sep_AFElem p x m :
    (exists R, (AFElem p x * R)%sep m) ->
    exists Hx : length x = n, exists R, (FFElem p (exist _ x Hx) * R)%sep m.
  Proof.
    intros [R H]. pose proof (AFElem_length _ _ _ _ H) as Hx. exists Hx, R.
    seprewrite_in (AFElem_iff_FFElem p x Hx) H. exact H.
  Qed.

  (** ** Specs *)

  Import WeakestPrecondition.

  Lemma binop_spec_of_fiat {name aname}
        (op : Field.BinOp name)
        (aop : AbstractField.BinOp (field_parameters:=aparams) (field_representation:=abstract_rep) aname) functions :
    aname = name ->
    (forall a b, AbstractField.bin_model a b = Field.bin_model a b) ->
    AbstractField.bin_xbounds = Field.bin_xbounds ->
    AbstractField.bin_ybounds = Field.bin_ybounds ->
    AbstractField.bin_outbounds = Field.bin_outbounds ->
    Field.binop_spec op functions ->
    AbstractField.binop_spec aop functions.
  Proof.
    intros Hname Hmodel Hxb Hyb Hob H.
    cbv [AbstractField.binop_spec]. subst aname.
    intros pout px py out x y Rr tr m (Hbx & Hby & HX & HY & HO).
    rewrite Hxb in Hbx. rewrite Hyb in Hby.
    destruct (ex_sep_AFElem _ _ _ HX) as (Hx & HX').
    destruct (ex_sep_AFElem _ _ _ HY) as (Hy & HY').
    destruct (sep_AFElem_to_bytes _ _ _ _ HO) as (Ho & HO').
    eapply WeakestPreconditionProperties.Proper_call;
      [ | exact (H pout px py (exist _ x Hx) (exist _ y Hy) _ Rr tr m
                   (conj Hbx
                   (conj Hby
                   (conj (AFElem_bytes_length out Ho) (conj HX' (conj HY' HO')))))) ].
    intros tr' m' rets (Hrets & Htr & out' & Hval & Hb & Hsep). subst rets.
    split; [reflexivity|]. split; [exact Htr|].
    exists (proj1_sig out'). split; [|split].
    - cbn [AbstractField.feval abstract_rep proj1_sig]. rewrite Hmodel.
      destruct out'; exact Hval.
    - rewrite Hob. destruct out'; exact Hb.
    - seprewrite_in (FFElem_iff_AFElem pout out') Hsep. exact Hsep.
  Qed.

  Lemma unop_spec_of_fiat {name aname}
        (op : Field.UnOp name)
        (aop : AbstractField.UnOp (field_parameters:=aparams) (field_representation:=abstract_rep) aname) functions :
    aname = name ->
    (forall a, AbstractField.un_model a = Field.un_model a) ->
    AbstractField.un_xbounds = Field.un_xbounds ->
    AbstractField.un_outbounds = Field.un_outbounds ->
    Field.unop_spec op functions ->
    AbstractField.unop_spec aop functions.
  Proof.
    intros Hname Hmodel Hxb Hob H.
    cbv [AbstractField.unop_spec]. subst aname.
    intros pout px out x Rr tr m (Hbx & HX & HO).
    rewrite Hxb in Hbx.
    destruct (ex_sep_AFElem _ _ _ HX) as (Hx & HX').
    destruct (sep_AFElem_to_bytes _ _ _ _ HO) as (Ho & HO').
    eapply WeakestPreconditionProperties.Proper_call;
      [ | exact (H pout px (exist _ x Hx) _ Rr tr m
                   (conj Hbx
                   (conj (AFElem_bytes_length out Ho) (conj HX' HO')))) ].
    intros tr' m' rets (Hrets & Htr & out' & Hval & Hb & Hsep). subst rets.
    split; [reflexivity|]. split; [exact Htr|].
    exists (proj1_sig out'). split; [|split].
    - cbn [AbstractField.feval abstract_rep proj1_sig]. rewrite Hmodel.
      destruct out'; exact Hval.
    - rewrite Hob. destruct out'; exact Hb.
    - seprewrite_in (FFElem_iff_AFElem pout out') Hsep. exact Hsep.
  Qed.

  (** [felem_copy]: the AbstractField spec frames the output with a second frame [Rout]; the
      fiat spec frames everything with one [R].  Since an element's memory is determined by
      its address and value, the remainder of [pout] is the same under both frames. *)
  Lemma split_same_l (m m1 m2 m3 : mem) :
    map.split m m1 m2 -> map.split m m1 m3 -> m2 = m3.
  Proof.
    intros H1 H2.
    apply map.split_comm in H1. apply map.split_comm in H2.
    exact (proj1 (map.split_diff (map.same_domain_refl m1) H1 H2)).
  Qed.

  Lemma felem_copy_spec_of_fiat functions :
    @AbstractField.felem_copy _ aparams = Field.felem_copy ->
    Field.spec_of_felem_copy functions ->
    AbstractField.spec_of_felem_copy (field_parameters:=aparams) (field_representation:=abstract_rep) functions.
  Proof.
    intros Hname H.
    cbv [AbstractField.spec_of_felem_copy]. rewrite Hname.
    intros pout px out x R Rout tr m (H1 & H2).
    pose proof (AFElem_length _ _ _ _ (proj1 (sep_assoc _ _ _ _) H1)) as Hx.
    pose proof (AFElem_length _ _ _ _ H2) as Ho.
    (* the frame of [pout] under [R], made exact *)
    destruct H1 as (mxo & mR & Hs1 & Hxo & HR).
    destruct Hxo as (mx & mo & Hs2 & Hmx & Hmo).
    destruct H2 as (mo' & mrest & Hs3 & Hmo' & Hrest).
    assert (Emo : mo' = mo).
    { apply (AFElem_to_bytes pout out Ho) in Hmo.
      apply (AFElem_to_bytes pout out Ho) in Hmo'. congruence. }
    subst mo'.
    (* [mem = mo + (mx + mR)] *)
    pose proof Hs1 as Hs1'.
    destruct Hs1 as (Em1 & Hd1). destruct Hs2 as (Em2 & Hd2). subst mxo.
    assert (Hd_xR : map.disjoint mx mR).
    { intros k v1 v2 G1 G2. apply (Hd1 k v1 v2); [|exact G2].
      rewrite map.get_putmany_dec. destruct (map.get mo k) eqn:E; [|exact G1].
      exfalso. exact (Hd2 k v1 _ G1 E). }
    assert (Hs4 : map.split m mo (map.putmany mx mR)).
    { split.
      - rewrite Em1. rewrite map.putmany_assoc.
        rewrite (map.putmany_comm mx mo) by exact Hd2. reflexivity.
      - apply map.disjoint_putmany_r. split.
        + exact (proj1 (map.disjoint_comm mx mo) Hd2).
        + intros k v1 v2 G1 G2. apply (Hd1 k v1 v2); [|exact G2].
          rewrite map.get_putmany_dec. rewrite G1. reflexivity. }
    pose proof (split_same_l _ _ _ _ Hs3 Hs4) as Erest. subst mrest.
    (* the fiat call, with the frame [eq mR] *)
    assert (Hpre : (FFElem px (exist _ x Hx) *
                    eq (map.of_list_word_at pout (ws2bs (Z.to_nat (bytes_per_word width)) out)) *
                    eq mR)%sep m).
    { exists (map.putmany mx mo), mR. split; [exact Hs1'|]. split; [|reflexivity].
      exists mx, mo. split; [exact (conj eq_refl Hd2)|]. split.
      - exact (proj1 (AFElem_iff_FFElem px x Hx mx) Hmx).
      - exact (proj1 (AFElem_to_bytes pout out Ho mo) Hmo). }
    eapply WeakestPreconditionProperties.Proper_call;
      [ | exact (H pout px (exist _ x Hx) _ (eq mR) tr m
                   (conj Hpre (AFElem_bytes_length out Ho))) ].
    intros tr' m' rets (Hrets & Htr & Hpost). subst rets.
    split; [reflexivity|]. split; [exact Htr|].
    (* [m' = mx' + mo'' + mR] with [mx' = mx] *)
    destruct Hpost as (mxo' & mR' & Hs5 & Hxo' & EmR). subst mR'.
    destruct Hxo' as (mx' & mo'' & Hs6 & Hmx' & Hmo'').
    assert (Emx : mx' = mx).
    { apply (AFElem_iff_FFElem px x Hx) in Hmx.
      apply (Field.felem_to_bytes px (exist _ x Hx)) in Hmx.
      apply (Field.felem_to_bytes px (exist _ x Hx)) in Hmx'. congruence. }
    subst mx'.
    destruct Hs5 as (Em5 & Hd5). destruct Hs6 as (Em6 & Hd6). subst mxo' m'.
    exists mo'', (map.putmany mx mR). split; [split|]; [ | | split].
    - rewrite map.putmany_assoc.
      rewrite (map.putmany_comm mx mo'') by exact Hd6. reflexivity.
    - apply map.disjoint_putmany_r. split.
      + exact (proj1 (map.disjoint_comm mx mo'') Hd6).
      + intros k v1 v2 G1 G2. apply (Hd5 k v1 v2); [|exact G2].
        rewrite map.get_putmany_dec. rewrite G1. reflexivity.
    - exact (proj1 (FFElem_iff_AFElem pout (exist _ x Hx) mo'') Hmo'').
    - exact Hrest.
  Qed.

  (** [from_word], stated as the body of [PrimeField.spec_of_from_word] for [abstract_rep]
      (the instance of a [PrimeFieldParameters] is convertible to it when its modulus is
      [Field.M_pos]). *)
  Definition abstract_spec_of_from_word (fw : string) : spec_of fw :=
    fnspec! fw (pout x : word) / out R,
    { requires tr mem0 :=
        (AFElem pout out * R)%sep mem0;
      ensures tr' mem' :=
        tr = tr' /\
        exists X, @AbstractField.feval _ aparams _ _ _ _ abstract_rep X = F.of_Z _ (word.unsigned x)
            /\ @AbstractField.bounded_by _ aparams _ _ _ _ abstract_rep
                  (@AbstractField.tight_bounds _ aparams _ _ _ _ abstract_rep) X
            /\ (AFElem pout X * R)%sep mem' }.

  Lemma from_word_spec_of_fiat (fw : string) functions :
    fw = Field.from_word ->
    Field.spec_of_from_word functions ->
    abstract_spec_of_from_word fw functions.
  Proof.
    intros Hname H. subst fw.
    cbv [abstract_spec_of_from_word].
    intros pout x out R tr m HO.
    destruct (sep_AFElem_to_bytes _ _ _ _ HO) as (Ho & HO').
    eapply WeakestPreconditionProperties.Proper_call;
      [ | exact (H pout x _ R tr m (conj HO' (AFElem_bytes_length out Ho))) ].
    intros tr' m' rets (Hrets & Htr & out' & Hval & Hb & Hsep). subst rets.
    split; [reflexivity|]. split; [exact Htr|].
    exists (proj1_sig out'). split; [|split].
    - destruct out'; exact Hval.
    - destruct out'; exact Hb.
    - seprewrite_in (FFElem_iff_AFElem pout out') Hsep. exact Hsep.
  Qed.
End Bridge.
