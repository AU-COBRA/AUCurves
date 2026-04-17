Require Import Coq.Init.Byte.
Require Import bedrock2.Map.SeparationLogic.
Require Import Bedrock.Util.Word.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Properties.

Section util.
    Context
      {width : Z} {BW : Bitwidth.Bitwidth width} {word : word.word width}
      {word_ok : word.ok word}
      {mem : Interface.map.map word Byte.byte} {mem_ok : Interface.map.ok mem}.
    
    Local Open Scope string_scope.
    Local Infix "*" := sep : sep_scope.
    Delimit Scope sep_scope with sep.

    Lemma empty_frame: forall (P : (@Interface.map.rep _ _ mem) -> Prop) (m : (@Interface.map.rep _ _ mem)),
        P m -> exists R, (P * R)%sep m.
    Proof. intros. exists (emp True). ecancel_assumption. Qed.

    Lemma sep_assoc_proj1 (m : @Interface.map.rep _ _ mem) P Q R : ((P * Q) * R)%sep m -> (P * (Q * R))%sep m.
    Proof. apply (sep_assoc _ _ _ m). Qed. 

    Lemma sep_assoc_proj2 (m : @Interface.map.rep _ _ mem) P Q R : (P * (Q * R))%sep m -> (P * Q * R)%sep m.
    Proof. apply (sep_assoc _ _ _ m). Qed.

    Lemma alloc_seps_alt (m m1 m2 : @Interface.map.rep _ _ mem)
        P1 P2 : Interface.map.split m m1 m2 ->
        (exists R1, (P1 * R1)%sep m1) -> (exists R2, (P2 * R2)%sep m2) ->
            exists (R' : @Interface.map.rep _ _ mem -> Prop), (P1 * P2 * R')%sep m.
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

  Context {width : Z} {BW : Bitwidth.Bitwidth width}
          {word : word.word width} {word_ok : word.ok word}
          (n : nat)
          (n_nz : n <> O).

  Context (n_small : n < 2 ^ width).

  Local Lemma bw_big: 0 < width.
  Proof.
      destruct (Bitwidth.width_cases); lia.
  Qed.

  Lemma map_id_restr {A : Type} (f : A -> A) (l : list A) : Forall (fun x => (f x = x)) l -> map f l = l.
  Proof.
      intros. induction l as [|x l' IHl']; [auto|].
      simpl.
      assert ( x = f x) by (apply Forall_inv in H; auto).
      rewrite <- H0.
      apply Forall_inv_tail in H. apply IHl' in H. rewrite H. auto.
  Qed.

  (* small_sc_small after section closing requires several side
     conditions that depend on dummy values for R_numlimbs, N, etc.
     We isolate the primary goal and discharge the side conditions
     via [shelve]/[Unshelve] at the end. *)
  Lemma small_id_restr m l : @WordByWordMontgomery.valid width n m l -> (forall x, In x l -> (@word.unsigned width word (word.of_Z x) = x)).
  Proof.
    intros [Hsmall _] x Hin.
    rewrite word.unsigned_of_Z. unfold word.wrap. apply Z.mod_small.
    unfold WordByWordMontgomery.small in Hsmall.
    rewrite Hsmall in Hin.
    unfold Partition.Partition.partition in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [i [Hxi Hin]]. subst x.
    rewrite UniformWeight.uweight_S by (pose proof bw_big; lia).
    rewrite UniformWeight.uweight_eq_alt by (pose proof bw_big; lia).
    pose proof bw_big as Hbw;
    pose proof (Z.pow_pos_nonneg 2 (Z.of_nat i) ltac:(lia) ltac:(lia)) as Hpi;
    pose proof (Z.pow_pos_nonneg 2 width ltac:(lia) ltac:(lia)) as Hpw;
    split;
    [apply Z_div_nonneg_nonneg; [apply Z.mod_pos_bound; nia | lia]
    |apply Z.div_lt_upper_bound; [lia | rewrite Z.mul_comm; apply Z.mod_pos_bound; nia]].
  Qed.

  Lemma toZ_ofZ_eq' x : @WordByWordMontgomery.small width n x -> List.map (@Interface.word.unsigned width word ) (map (@word.of_Z width _) x) = x.
  Proof.
    intros Hsmall.
    rewrite map_map. apply map_id_restr. apply Forall_forall. intros x0 Hin.
    rewrite word.unsigned_of_Z. unfold word.wrap. apply Z.mod_small.
    unfold WordByWordMontgomery.small in Hsmall.
    rewrite Hsmall in Hin.
    unfold Partition.Partition.partition in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [i [Hxi Hin]]. subst x0.
    rewrite UniformWeight.uweight_S by (pose proof bw_big; lia).
    rewrite UniformWeight.uweight_eq_alt by (pose proof bw_big; lia).
    pose proof bw_big as Hbw;
    pose proof (Z.pow_pos_nonneg 2 (Z.of_nat i) ltac:(lia) ltac:(lia)) as Hpi;
    pose proof (Z.pow_pos_nonneg 2 width ltac:(lia) ltac:(lia)) as Hpw;
    split;
    [apply Z_div_nonneg_nonneg; [apply Z.mod_pos_bound; nia | lia]
    |apply Z.div_lt_upper_bound; [lia | rewrite Z.mul_comm; apply Z.mod_pos_bound; nia]].
  Qed.

  Lemma toZ_ofZ_eq m x : @WordByWordMontgomery.valid width n m x -> List.map (@Interface.word.unsigned width word ) (map (@word.of_Z width _) x) = x.
  Proof.
    intros. destruct H. apply toZ_ofZ_eq'. auto.
  Qed.

  Local Notation toZ x := (List.map Interface.word.unsigned x).

  Lemma valid_toZ m : forall l, @WordByWordMontgomery.valid width n m l -> List.map (@Interface.word.unsigned width word ) (map (@word.of_Z width _) l) = l.
  Proof.
    intros. rewrite map_map. rewrite map_id_restr; auto.
    pose proof small_id_restr. apply Forall_forall. intros.
    apply small_id_restr with (x := x) in H; auto.
  Qed.

End Montgomery.