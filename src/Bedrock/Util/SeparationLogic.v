Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Array.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import coqutil.Byte.
Require Import coqutil.Datatypes.HList.
Require Import bedrock2.Memory.


Section Scalars.
    Context {width : Z} {BW : Bitwidth.Bitwidth width}
            {word : Word.Interface.word width} {word_ok : word.ok word}.
    Context {mem : map.map word byte} {mem_ok : map.ok mem}.

    Lemma store_word_of_sep_2 addr (oldvalue1 oldvalue2 value: word) R1 R2 m (post:_->Prop)
    (Hsep1 : sep (scalar addr oldvalue1) R1 m)
    (Hsep2 : sep (scalar addr oldvalue2) R2 m)
    (Hpost : forall m, sep (scalar addr value) R1 m /\ sep (scalar addr value) R2 m -> post m)
    : exists m1, Memory.store Syntax.access_size.word m addr value = Some m1 /\ post m1.
    Proof.
        destruct (store_of_sep Syntax.access_size.word addr oldvalue1 value R1 m
                    (fun m' => sep (scalar addr value) R1 m')
                    Hsep1 (fun m' H => H)) as [m1 [Hstore1 HR1]].
        destruct (store_of_sep Syntax.access_size.word addr oldvalue2 value R2 m
                    (fun m' => sep (scalar addr value) R2 m')
                    Hsep2 (fun m' H => H)) as [m2 [Hstore2 HR2]].
        assert (m1 = m2) by congruence. subst m2.
        exists m1. split; [exact Hstore1|]. apply Hpost. auto.
    Qed.
End Scalars.
