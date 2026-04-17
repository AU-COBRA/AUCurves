Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.

Section word.

Context
  {width : Z} {BW : Bitwidth width} {word : word.word width}
  {word_ok : word.ok word}.

Require Import bedrock2.Memory.
Local Notation word_size_in_bytes := (Memory.bytes_per_word width).
Local Notation ws := word_size_in_bytes.

Notation N aw := (word.add (word.of_Z ws) aw).
Local Coercion Z.of_nat : nat >-> Z.

Add Ring Wring : word.ring_theory.

Lemma word_add_0' : forall (a : word), word.add a (word.of_Z (0)) = a.
Proof.
  intros. ring.
Qed.

Lemma word_add_0 : forall (a : word), word.add a (word.of_Z (0 * ws)) = a.
Proof.
  intros. assert (0 = 0 * ws) by auto. rewrite <- H. ring.
Qed.

Lemma word_add_assoc (a : word) b c : word.add a (word.add b c) = word.add (word.add a b) c.
Proof.
    ring.
Qed.

Lemma word_add_comm (a b : word) : word.add a b = word.add b a.
Proof.
    ring.
Qed.

Lemma next_word' (a : word) n : word.add a (word.of_Z (n)) = N (word.add a (word.of_Z (n - ws))).
Proof.
    ring_simplify.
    rewrite <- word_add_assoc.
    rewrite <- word.ring_morph_add. assert (ws + (n - ws)= n) by auto with zarith.
    rewrite H. auto.
Qed.

End word.
