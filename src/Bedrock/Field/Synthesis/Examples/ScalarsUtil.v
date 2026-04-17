Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Memory.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.

Section Scalars.
    Context {width : Z} {BW : Bitwidth.Bitwidth width} {word : Word.Interface.word width} {word_ok : word.ok word}.
    Context {mem : map.map word Init.Byte.byte} {mem_ok : map.ok mem}.

    Lemma store_word_of_sep_2 addr (oldvalue1 oldvalue2 value: word) R1 R2 m (post:_->Prop)
    (Hsep1 : sep (scalar addr oldvalue1) R1 m)
    (Hsep2 : sep (scalar addr oldvalue2) R2 m)
    (Hpost : forall m, sep (scalar addr value) R1 m /\ sep (scalar addr value) R2 m -> post m)
    : exists m1, Memory.store Syntax.access_size.word m addr value = Some m1 /\ post m1.
    Proof.
        edestruct (store_word_of_sep addr oldvalue1 value R1 m
                     (fun m => sep (scalar addr value) R1 m) Hsep1)
          as [m1 [Hst1 HR1]].
        { intros; assumption. }
        edestruct (store_word_of_sep addr oldvalue2 value R2 m
                     (fun m => sep (scalar addr value) R2 m) Hsep2)
          as [m2 [Hst2 HR2]].
        { intros; assumption. }
        exists m1; split; [exact Hst1 |].
        apply Hpost; split; [exact HR1 |].
        replace m1 with m2 by congruence.
        exact HR2.
    Qed.
End Scalars.
