Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Coq.Init.Byte.
Require Import bedrock2.Map.SeparationLogic.
Require Import Bedrock.Util.Word.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Implementations.SOS.SOSReduction.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.

Section util.
    Context {p : Types.parameters}
            {ok : Types.ok}.
    Existing Instance semantics_ok.
    
    Local Open Scope string_scope.
    Local Infix "*" := sep : sep_scope.
    Delimit Scope sep_scope with sep.

    Lemma empty_frame: forall (P : (@Interface.map.rep _ _ Semantics.mem) -> Prop) (m : (Interface.map.rep)),
        P m -> exists R, (P * R)%sep m.
    Proof. intros. exists (emp True). ecancel_assumption. Qed.

    Lemma sep_assoc_proj1 (m : @Interface.map.rep _ _ Semantics.mem) P Q R : ((P * Q) * R)%sep m -> (P * (Q * R))%sep m.
    Proof. apply (sep_assoc _ _ _ m). Qed. 

    Lemma sep_assoc_proj2 (m : @Interface.map.rep _ _ Semantics.mem) P Q R : (P * (Q * R))%sep m -> (P * Q * R)%sep m.
    Proof. apply (sep_assoc _ _ _ m). Qed.

    Lemma alloc_seps_alt (m m1 m2 : @Interface.map.rep _ _ Semantics.mem)
        P1 P2 : Interface.map.split m m1 m2 ->
        (exists R1, (P1 * R1)%sep m1) -> (exists R2, (P2 * R2)%sep m2) ->
            exists (R' : Interface.map.rep -> Prop), (P1 * P2 * R')%sep m.
    Proof.
    intros; destruct H0; destruct H1; exists (x * x0)%sep.
    assert (((P1 * x) * (P2 * x0))%sep m) by (exists m1, m2; auto);
    ecancel_assumption.
    Qed.

End util.

Section Montgomery.
  (*Montgomery Arithmetic*)

  Local Open Scope Z_scope.
  Local Coercion Z.of_nat : nat >-> Z.

  Context {p : Semantics.parameters}
          {p_ok : Semantics.parameters_ok p}
          (n : nat)
          (n_nz : n <> O).

  Local Notation thisword := (@Semantics.word p).
  Local Notation bw := Semantics.width.

  Context (n_small : n < 2 ^ bw).

  Local Lemma bw_big: 0 < bw.
  Proof.
      destruct p_ok. destruct width_cases; lia.
  Qed.

  Lemma map_id_restr {A : Type} (f : A -> A) (l : list A) : Forall (fun x => (f x = x)) l -> map f l = l.
  Proof.
      intros. induction l as [|x l' IHl']; [auto|].
      simpl.
      assert ( x = f x) by (apply Forall_inv in H; auto).
      rewrite <- H0.
      apply Forall_inv_tail in H. apply IHl' in H. rewrite H. auto.
  Qed.

  Lemma small_id_restr m l : @WordByWordMontgomery.valid Semantics.width n m l -> (forall x, In x l -> (@word.unsigned Semantics.width thisword (word.of_Z x) = x)).
  Proof.
    intros.
    destruct H.
    apply (SOSReduction.WordByWordMontgomery.small_sc_small _ 1) in H .
        - pose proof (Forall_forall (WordByWordMontgomery.sc_small bw) l).
          destruct H2. apply H2 with (x := x) in H; auto.
          simpl. unfold WordByWordMontgomery.sc_small in H.
          destruct p_ok, word_ok. rewrite unsigned_of_Z. unfold wrap.
          rewrite Zmod_small; auto.
        - apply bw_big.
        - auto.
        - simpl; lia.
  Qed.

  Lemma toZ_ofZ_eq' x : @WordByWordMontgomery.small Semantics.width n x -> List.map (@Interface.word.unsigned Semantics.width thisword ) (map (@word.of_Z Semantics.width _) x) = x.
  Proof.
    intros.
    rewrite map_map.
    simpl. apply map_id_restr.
    destruct (WordByWordMontgomery.small_if_Forall_sc_small bw n bw_big n_nz n_small n x) as [H' _].
    apply H' in H. destruct H. apply Forall_forall.
    intros.
    destruct (Forall_forall (WordByWordMontgomery.sc_small bw) x) as [H'' _].
    destruct p_ok. destruct word_ok. rewrite unsigned_of_Z. 
    apply Zmod_small.
    assert (WordByWordMontgomery.sc_small bw x0).
    {
      apply H''; auto.
    }
    unfold WordByWordMontgomery.sc_small in H2. split; try lia.
  Qed.

  Lemma toZ_ofZ_eq m x : @WordByWordMontgomery.valid Semantics.width n m x -> List.map (@Interface.word.unsigned Semantics.width thisword ) (map (@word.of_Z Semantics.width _) x) = x.
  Proof.
    intros. destruct H. apply toZ_ofZ_eq'. auto.
  Qed.

  Local Notation toZ x := (List.map Interface.word.unsigned x).

  Lemma valid_toZ m : forall l, @WordByWordMontgomery.valid Semantics.width n m l -> List.map (@Interface.word.unsigned Semantics.width thisword ) (map (@word.of_Z Semantics.width _) l) = l.
  Proof.
    intros. rewrite map_map. rewrite map_id_restr; auto.
    pose proof small_id_restr. apply Forall_forall. intros.
    apply small_id_restr with (x := x) in H; auto.
  Qed.

End Montgomery.