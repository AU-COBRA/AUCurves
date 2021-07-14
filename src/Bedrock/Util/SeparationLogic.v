Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Semantics bedrock2.Array coqutil.Word.LittleEndian.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import coqutil.Byte.
Require Import coqutil.Datatypes.HList.
Require Import bedrock2.ptsto_bytes.


Section ptsto_bytes.
    Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
    Context {mem : map.map word byte} {mem_ok : map.ok mem}.

    Lemma unchecked_store_bytes_of_sep_2(a: word)(n: nat)(oldbs1 oldbs2 bs: tuple byte n)(R1 R2: mem -> Prop)(m: mem)
    (Hsep1 : sep (ptsto_bytes n a oldbs1) R1 m)
    (Hsep2 : sep (ptsto_bytes n a oldbs2) R2 m)
    : sep (ptsto_bytes n a bs) R2 (Memory.unchecked_store_bytes n m a bs) /\ sep (ptsto_bytes n a bs) R1 (Memory.unchecked_store_bytes n m a bs).
    Proof.
        split; eauto using unchecked_store_bytes_of_sep.
    Qed.

    Lemma store_bytes_of_sep_2(a: word)(n: nat)(oldbs1 oldbs2 bs: tuple byte n)(R1 R2 post: mem -> Prop)(m: mem)
    (Hsep1 : sep (ptsto_bytes n a oldbs1) R1 m)
    (Hsep2 : sep (ptsto_bytes n a oldbs2) R2 m)
    (Hpost : forall m, sep (ptsto_bytes n a bs) R1 m /\ sep (ptsto_bytes n a bs) R2 m -> post m)
    : exists m1, Memory.store_bytes n m a bs = Some m1 /\ post m1.
    Proof.
        cbv [store_bytes]. erewrite load_bytes_of_sep. all: try eauto using unchecked_store_bytes_of_sep_2.
    Qed.
End ptsto_bytes.


Section Scalars.
    Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
    Context {mem : map.map word byte} {mem_ok : map.ok mem}.

    Lemma store_word_of_sep_2 addr (oldvalue1 oldvalue2 value: word) R1 R2 m (post:_->Prop)
    (Hsep1 : sep (scalar addr oldvalue1) R1 m)
    (Hsep2 : sep (scalar addr oldvalue2) R2 m)
    (Hpost : forall m, sep (scalar addr value) R1 m /\ sep (scalar addr value) R2 m -> post m)
    : exists m1, Memory.store Syntax.access_size.word m addr value = Some m1 /\ post m1.
    Proof. eapply store_bytes_of_sep_2; [eapply Hsep1| eapply Hsep2| eapply Hpost]. Qed.
End Scalars.