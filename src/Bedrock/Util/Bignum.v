
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import bedrock2.Semantics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import coqutil.Map.Properties.
Require Import bedrock2.Array.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Bedrock.Util.Word.
Import ListNotations.

(*Alternative characterization of Bignum using a fixpoint. This is useful for recursing over the Scalars of a Bignum.*)

Section bignum.
    Context {p : Types.parameters}
            {ok : Types.ok}.
            Existing Instance semantics_ok.

    Local Open Scope string_scope.
    Local Infix "*" := sep : sep_scope.
    Delimit Scope sep_scope with sep.

    Local Notation wordof_Z := (@word.of_Z width word).

    Fixpoint many_Scalars n a lv :=
        match n with
        | O => (emp True)
        | S (m) => (Scalars.scalar a (hd (wordof_Z 0%Z) lv) * (many_Scalars m (word.add (word.of_Z word_size_in_bytes) a) (tl lv)))%sep
        end.


    Lemma many_Scalars_next n a v l :
    (many_Scalars (S n) a (v :: l)) = ((Scalars.scalar a v) * (many_Scalars n (word.add (word.of_Z word_size_in_bytes) a) l))%sep.
    Proof. auto. Qed.

    Lemma many_Scalars_nil a : many_Scalars (0%nat) a [] = emp True.
    Proof.
    auto.
    Qed.


    (*Intermediate Lemmas; TODO: move*)

    Lemma length_nil {A : Type} (l : list A) : length l = 0%nat -> l = [].
    Proof.
        intros.
        destruct l.
        - auto.
        - simpl in H. discriminate.
    Qed.

    Notation msplit := Interface.map.split.

    Lemma split_empty_r: forall x, @msplit (@Semantics.word (@semantics p)) Init.Byte.byte
    (@Semantics.mem (@semantics p)) x x Interface.map.empty.
    Proof.
        split.
        - rewrite map.putmany_empty_r. auto.
        - apply map.disjoint_empty_r.
    Qed.

    Lemma split_empty_l: forall x, @msplit (@Semantics.word (@semantics p)) Init.Byte.byte
    (@Semantics.mem (@semantics p)) x Interface.map.empty x.
    Proof.
        intros; rewrite Properties.map.split_comm. apply split_empty_r.
    Qed.

    Lemma Scalar_cons (a : word) v l : Lift1Prop.iff1 (array Scalars.scalar (word.of_Z word_size_in_bytes) a (v :: l))
    ((Scalars.scalar a v) * array Scalars.scalar (word.of_Z word_size_in_bytes) (word.add (word.of_Z word_size_in_bytes) a) l)%sep.
    Proof.
        rewrite word_add_comm.
        destruct p. destruct semantics.
        pose proof (@array_cons width word Init.Byte.byte mem word Scalars.scalar (word.of_Z word_size_in_bytes) v l a).
        auto.
    Qed.


    Lemma Bignum_next n a l v : Lift1Prop.iff1 (Bignum (S n) a (v :: l)) ((Bignum n (word.add (word.of_Z word_size_in_bytes) a) l) * (Bignum 1 a [v]))%sep.
    Proof.
        split; intros.
        - unfold Bignum in H. sepsimpl_hyps. apply Scalar_cons in H0. apply sep_comm.
            do 3 destruct H0. destruct H1. exists x0. exists x1. split; auto. split.
            + unfold Bignum. simpl. exists Interface.map.empty. exists x0. split.
                * apply split_empty_l. 
                * split.
                {
                    sepsimpl. auto.
                }
                exists x0; exists Interface.map.empty. split.
                {
                    apply split_empty_r.
                }
                split; auto.
                sepsimpl. auto.
            + unfold Bignum. sepsimpl.
                * simpl in H. auto.
                * auto.
        - unfold Bignum. sepsimpl.
            + unfold Bignum in H. sepsimpl_hyps. simpl. auto.
            + apply Scalar_cons. unfold Bignum in H. sepsimpl_hyps. do 3 destruct H1. destruct H2.
            exists x0; exists x1. split; auto. split.
            * simpl in H2. sepsimpl_hyps. auto.
            * auto.
    Qed.

    Lemma Bignum_n_Scalar n a lv : Lift1Prop.iff1 (Bignum n a lv)  (emp (length lv = n) * (many_Scalars n a lv))%sep.
    Proof.
        generalize dependent a. generalize dependent lv. induction n.
        - intros. simpl. unfold Bignum. split.
            + intros. sepsimpl_hyps. simpl in H0. apply length_nil in H. rewrite H in H0. simpl in H0.
            exists x; exists x. split.
            * sepsimpl; rewrite H0. apply split_empty_l.
            * split; auto. sepsimpl. rewrite H; auto.
            + intros. sepsimpl; auto.
            apply length_nil in H. rewrite H; simpl. unfold emp; split; auto.
        - intros. split; intros.
            + unfold Bignum in H; sepsimpl; auto. destruct lv; try discriminate.
            rewrite many_Scalars_next.
            apply Scalar_cons in H0. do 3 destruct H0. destruct H1. exists x0; exists x1; auto. split; auto. split.
                * auto.
                * assert (Bignum n (word.add (word.of_Z word_size_in_bytes ) a) lv x1).
                {
                    unfold Bignum. sepsimpl; auto.
                }
                apply IHn in H3. sepsimpl_hyps; auto.
            + sepsimpl_hyps; destruct lv; try discriminate. apply Bignum_next. rewrite many_Scalars_next in H0.
            apply sep_comm. do 3 destruct H0. destruct H1. exists x0; exists x1. split; auto. split; auto.
            * unfold Bignum. sepsimpl; auto.
                simpl. sepsimpl; auto.
            * apply IHn. sepsimpl; auto.
    Qed.

    Lemma Bignum_manyScalars_R n a lv R : Lift1Prop.iff1 ((Bignum n a lv) * R)%sep ((emp (length lv = n) * (many_Scalars n a lv)) * R)%sep.
    Proof.
        rewrite sep_comm. rewrite (sep_comm _ R).
        apply iff1_sep_cancel. apply Bignum_n_Scalar.
    Qed.

    Lemma Bignum_anybytes: forall (n : nat) m num a wa (Hn : num = Z.of_nat (n * Z.to_nat word_size_in_bytes)), Bignum n a wa m -> anybytes a (num) m.
    Proof.
    intros. pose proof (Bignum_to_bytes n a wa).
    unfold Lift1Prop.impl1 in H0.
    pose proof (H0 m H). unfold Lift1Prop.ex1 in H1. destruct H1.
    pose proof (array_1_to_anybytes x m a). sepsimpl_hyps. apply H2 in H3.
    rewrite Hn. rewrite <- H1. auto.
    Qed.

    Lemma ftprint_length : forall (a : word) n, length (ftprint a n) = Z.to_nat n.
    Proof.
        intros. unfold ftprint. generalize dependent a. induction (BinIntDef.Z.to_nat n) as [|n0 IHn0]; auto.
        intros; simpl; auto. 
    Qed.

    Lemma anybytes_Bignum: forall n m num a (Hn : num = Z.of_nat (n * Z.to_nat word_size_in_bytes)), anybytes a (num) m -> exists wa, (Bignum n a wa) m.
    Proof.
    intros. destruct H.
    pose proof (Bignum_of_bytes n a x). assert (length x =  (n * (Z.to_nat word_size_in_bytes))%nat).
        {
        simpl. simpl in H. pose proof (map.of_disjoint_list_zip_length (ftprint a num) x m H). rewrite ftprint_length in H1. auto with zarith.
        }
    apply H0 in H1. unfold Lift1Prop.impl1 in H1. unfold Lift1Prop.ex1 in H1.
    pose proof (of_disjoint_list_zip_to_array_1 (Z.to_nat num) a x m).
    assert (Z.of_nat (Z.to_nat num) = num) by auto with zarith.
    rewrite H3 in H2. apply H2 in H.
    apply H1. auto.
    Qed.

    Lemma Bignum_eq: forall n x p, Bignum n p x = (emp (Datatypes.length x = n) * array Scalars.scalar (word.of_Z word_size_in_bytes) p x)%sep.
    Proof. auto. Qed.

End bignum.