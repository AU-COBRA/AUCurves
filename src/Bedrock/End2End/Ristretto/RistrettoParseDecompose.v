(** * RistrettoParseDecompose — byte/bit-level decomposition of
 *    [ristretto_parse_canonical_felem] (Task T4, algebraic core).
 *
 *  The parser (RistrettoHelpers.v) rejects on three conditions over
 *  [z = le_combine bs] (length 32):
 *    (1) bit 255 set,
 *    (2) [z >= p]  (non-canonical),
 *    (3) bit 0 set (is_negative).
 *  Conditions (1) and (3) are direct bit tests on bytes 31 and 0.
 *  Condition (2) — a 256-bit magnitude compare against [p] — is the
 *  only one awkward in straight-line IR.  This file proves the
 *  standard overflow trick that turns it into ANOTHER bit test:
 *
 *      for 0 <= z < 2^255:   z < p  <->  bit 255 of (z + 19) is 0
 *
 *  (because p = 2^255 - 19, so z >= p iff z + 19 >= 2^255, and since
 *  z + 19 < 2^255 + 19 < 2^256 the only bit that can carry into is 255).
 *  This lets the decoder AST realise the canonicality check as a single
 *  add of the constant 19 followed by a bit-255 test — no trusted
 *  comparison leaf. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Local Open Scope Z_scope.

(** Bit 255 of a value [w] in [0, 2^256) equals its quotient by 2^255
    being 1, which (in our range of interest) is just [2^255 <=? w]. *)
Lemma testbit_255_eq_geb :
  forall w, 0 <= w < 2 ^ 256 ->
    Z.testbit w 255 = (2 ^ 255 <=? w).
Proof.
  intros w [Hlo Hhi].
  rewrite Z.testbit_eqb by lia.
  assert (Hq : w / 2 ^ 255 = if 2 ^ 255 <=? w then 1 else 0).
  { destruct (Z.leb_spec (2 ^ 255) w) as [Hge|Hlt].
    - symmetry. apply (Z.div_unique _ _ 1 (w - 2 ^ 255)); lia.
    - rewrite Z.div_small by lia. reflexivity. }
  rewrite Hq. destruct (2 ^ 255 <=? w); reflexivity.
Qed.

(** The headline trick.  For a value already known to fit in 255 bits,
    canonicality [z < p] is equivalent to bit 255 of [z + 19] being clear. *)
Lemma canonical_lt_p_iff_bit255 :
  forall z, 0 <= z < 2 ^ 255 ->
    (z <? ed25519_p) = negb (Z.testbit (z + 19) 255).
Proof.
  intros z [Hlo Hhi].
  unfold ed25519_p.
  rewrite testbit_255_eq_geb by lia.
  destruct (Z.ltb_spec z (2 ^ 255 - 19)) as [Hltp|Hgep];
  destruct (Z.leb_spec (2 ^ 255) (z + 19)) as [Hge2|Hlt2]; cbn; lia.
Qed.

(** Corollary in the form the parser uses: the [z <? ed25519_p] guard
    inside [ristretto_parse_canonical_felem] (reached only after the
    bit-255 check guarantees [z < 2^255]) equals the bit test. *)
Corollary parse_canonical_lt_guard :
  forall bs,
    length bs = 32%nat ->
    Z.testbit (le_combine bs) 255 = false ->
    (le_combine bs <? ed25519_p)
      = negb (Z.testbit (le_combine bs + 19) 255).
Proof.
  intros bs Hlen Hbit.
  pose proof (le_combine_bound bs) as Hbound.
  rewrite Hlen in Hbound.
  replace (8 * Z.of_nat 32) with 256 in Hbound by lia.
  apply canonical_lt_p_iff_bit255.
  split; [lia|].
  (* le_combine bs < 2^255: bit 255 clear and value < 2^256. *)
  destruct (Z.lt_ge_cases (le_combine bs) (2 ^ 255)) as [H|H]; [exact H|].
  exfalso.
  assert (Hb255 : Z.testbit (le_combine bs) 255 = true).
  { rewrite testbit_255_eq_geb by lia.
    apply Z.leb_le. lia. }
  rewrite Hbit in Hb255. discriminate.
Qed.
