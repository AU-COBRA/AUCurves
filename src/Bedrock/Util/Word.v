Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Coq.Lists.List.
Require Import Implementations.SOS.SOSReduction.

Section word.

Context {p : Types.parameters}
        {ok : Types.ok}.
        Existing Instance semantics_ok.

Local Notation ws := word_size_in_bytes.

Notation N aw := (word.add (word.of_Z ws) aw).
Local Coercion Z.of_nat : nat >-> Z.

Add Ring Wring : Word.Properties.word.ring_theory.

Lemma word_add_0' : forall (a : Semantics.word), word.add a (word.of_Z (0)) = a.
Proof. 
  intros. ring.
Qed.

Lemma word_add_0 : forall (a : Semantics.word), word.add a (word.of_Z (0 * ws)) = a.
Proof.
  intros. assert (0 = 0 * ws) by auto. rewrite <- H. ring.
Qed.

Lemma word_add_assoc (a : Semantics.word) b c : word.add a (word.add b c) = word.add (word.add a b) c.
Proof.
    ring.
Qed.

Lemma word_add_comm (a b : Semantics.word) : word.add a b = word.add b a.
Proof.
    ring.
Qed.

Lemma next_word' (a : Semantics.word) n : word.add a (word.of_Z (n)) = N (word.add a (word.of_Z (n - ws))).
Proof.
    ring_simplify.
    rewrite <- word_add_assoc.
    rewrite <- Properties.word.ring_morph_add. assert (ws + (n - ws)= n) by auto with zarith.
    rewrite H. auto.
Qed.

End word.

