(** * BLS12_MSM_WordArith: Standalone word-arithmetic helpers

    Extracted from [BLS12_MSM.v] to give MCP a testable surface
    for word-arithmetic facts needed by [msm_bls12_distribute_wp].

    Each lemma is parametrized over an abstract [word : Interface.word width]
    with [width = 64], and takes the concrete numeric bounds as hypotheses.
*)

From Stdlib Require Import ZArith Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import bedrock2.ZnWords.

Open Scope Z_scope.

Section WordArith.
  Context {width : Z} {word : Interface.word width}
          {word_ok : word.ok word}
          (Hwidth64 : width = 64).

  (** Shift amount: [word.unsigned (word.and (word.of_Z w * word.of_Z c) (word.of_Z 63))]
      equals [w * c mod 64] when the product is within word range. *)
  Lemma wunsigned_shift_mask
      (w c : Z)
      (Hw : 0 <= w < 2^32) (Hc : 0 <= c < 2^32) :
      word.unsigned (word.and (word.mul (word.of_Z w : word) (word.of_Z c))
                              (word.of_Z 63)) = w * c mod 64.
  Proof.
    rewrite word.unsigned_and.
    rewrite word.unsigned_mul_nowrap.
    2: { rewrite !word.unsigned_of_Z.
         unfold word.wrap; rewrite Hwidth64; simpl.
         rewrite Z.mod_small by lia.
         rewrite Z.mod_small by lia.
         nia. }
    rewrite !word.unsigned_of_Z.
    unfold word.wrap; rewrite Hwidth64; simpl.
    rewrite (Z.mod_small w (Z.pow_pos 2 64)) by (unfold Z.pow_pos; simpl; lia).
    rewrite (Z.mod_small c (Z.pow_pos 2 64)) by (unfold Z.pow_pos; simpl; lia).
    rewrite (Z.mod_small 63 (Z.pow_pos 2 64)) by (unfold Z.pow_pos; simpl; lia).
    change 63 with (Z.ones 6).
    rewrite Z.land_ones by lia.
    rewrite Z.mod_small.
    { change (2^6) with 64. reflexivity. }
    { pose proof (Z.mod_pos_bound (w*c) (2^6) ltac:(lia)) as Hmod6.
      split; [lia|].
      apply Z.lt_trans with (2^6); [lia|unfold Z.pow_pos; simpl; lia]. }
  Qed.

  (** Load-address equation: the bedrock2 address computation
      [(scalars_p + i*32) + (w*c/64 * 8)] equals the abstract form
      [scalars_p + (i*32 + limb_nat*8)] when all components fit in 64 bits. *)
  Lemma la1_eq_helper
      (scalars_p iw' : word) (w : Z) (n limb_nat : nat)
      (Hw : 0 <= w < 2^32)
      (Hiw'_unsigned : word.unsigned iw' = Z.of_nat n)
      (Hlimb_unsigned_abs : Z.of_nat limb_nat = w * 9 / 64)
      (Hn_small : Z.of_nat n < 2^width)
      (Hlimb_small : Z.of_nat limb_nat < 2^width) :
      word.add (word.add scalars_p (word.mul iw' (word.of_Z 32)))
               (word.mul (word.of_Z (Z.of_nat limb_nat)) (word.of_Z 8))
      = word.add scalars_p (word.of_Z (Z.of_nat n * 32 + Z.of_nat limb_nat * 8)).
  Proof. ZnWords. Qed.

End WordArith.
