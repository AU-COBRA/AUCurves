(** * Helper: bit extraction lemma for Ed25519 scalarmult loop body.
 *
 * The scalarmult body computes
 *   bit = (byte >> (i & 7)) & 1
 * to extract the i-th bit of the scalar.  We prove that the result is
 * always either word.of_Z 0 or word.of_Z 1 — needed so that
 * [cmov_5felems(ACC, TMP, bit)] satisfies its mask precondition. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
From Stdlib Require Import ZArith Lia.

Local Open Scope Z_scope.

Lemma word_and_one_in_zero_one (b : Naive.word 64) :
  word.unsigned (word.and b (word.of_Z 1)) = 0 \/
  word.unsigned (word.and b (word.of_Z 1)) = 1.
Proof.
  rewrite Properties.word.unsigned_and_nowrap.
  rewrite Properties.word.unsigned_of_Z_1.
  pose proof (Properties.word.unsigned_range b) as Hrange.
  pose proof (Z.land_ones (word.unsigned b) 1 ltac:(lia)) as Hland.
  change (Z.ones 1) with 1 in Hland.
  rewrite Hland.
  pose proof (Z.mod_pos_bound (word.unsigned b) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma bit_extraction_in_zero_one :
  forall (b : Naive.word 64) (k : Z),
    word.and (word.sru b (word.of_Z k)) (word.of_Z 1) = word.of_Z 0 \/
    word.and (word.sru b (word.of_Z k)) (word.of_Z 1) = word.of_Z 1.
Proof.
  intros b k.
  pose proof (word_and_one_in_zero_one (word.sru b (word.of_Z k))) as [H | H];
    [left | right]; apply Properties.word.unsigned_inj; rewrite H.
  - rewrite Properties.word.unsigned_of_Z_0. reflexivity.
  - rewrite Properties.word.unsigned_of_Z_1. reflexivity.
Qed.
