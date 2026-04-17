Require Import bedrock2.Array.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Memory.
Require Import Coq.Lists.List Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Tactics.eplace.

Section Array.
    Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
    Context {value} {mem : map.map word value} {mem_ok : map.ok mem}.
    Context {T} (element : word -> T -> mem -> Prop) (size : word).

    Lemma array_append_R xs ys start R:
    iff1 ((array element size start (xs ++ ys)) * R)%sep
         (array element size start xs * array element size (word.add start
                                           (word.mul size (word.of_Z (Z.of_nat (length xs))))) ys * R)%sep.
    Proof.
        split; intros.
            - destruct H, H, H, H0.
              do 2 eexists; split; [| split]; eauto.
              eapply array_append' in H0. auto.
            - destruct H, H, H, H0.
              do 2 eexists; split; [| split]; eauto.
              eapply array_append'. eauto.
    Qed.

    Lemma array_append_R' xs ys start R:
    iff1 ((array element size start (xs ++ ys)) * R)%sep
         (array element size (word.add start
         (word.mul size (word.of_Z (Z.of_nat (length xs))))) ys * (array element size start xs * R))%sep.
    Proof.
        split; intros.
            - eapply array_append_R in H. ecancel_assumption.
            - eapply array_append_R. ecancel_assumption.
    Qed.
End Array.