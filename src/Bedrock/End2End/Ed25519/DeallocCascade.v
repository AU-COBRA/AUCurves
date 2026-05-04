(** * Generic byte-buffer-to-anybytes helper for stackalloc dealloc cascades.
 *
 * When proving the post of an [ed25519_scalarmult_base]-style function with
 * one or more [stackalloc] frames, the dealloc step requires turning a
 * sep-predicated byte buffer (i.e. [(bs$@addr) ⋆ R]) back into the
 * [Memory.anybytes] form bedrock2 expects so the stack frame can be popped.
 *
 * This file provides a parametric helper [byte_buffer_to_anybytes] that
 * extracts the [anybytes] split from any sep'd byte buffer.  The proof
 * unfolds the top-level [sep] to a [map.split], unfolds the [bs$@addr]
 * sep-clause (which is just [Logic.eq (bs$@addr)]), and constructs the
 * [anybytes] witness directly from its definition
 *   [anybytes a n m := exists bs, of_list_word_at a bs = m /\
 *                                  length bs = n /\ length bs <= 2^width].
 *
 * Usage: in a stackalloc-dealloc cascade, after [solve_deallocation], when
 * the goal looks like
 *   exists mStack mInner, anybytes addr 200 mStack /\
 *                          map.split m mStack mInner /\ R mInner
 * and the hypothesis bag contains [((bs$@addr) ⋆ R)%sep m] with
 * [Datatypes.length bs = 200%nat], call this lemma to discharge the
 * existentials in one shot.
 *
 * The 200- and 120-byte specializations are provided as corollaries, since
 * the Ed25519 scalarmult proof has both: ACC/TMP are 200 bytes (5 felems)
 * and B_pre is 120 bytes (3 felems).  In each specialization the bound
 * [length bs <= 2^64] is trivially numeric. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.

Section ByteBufferToAnybytes.
  Local Open Scope Z_scope.
  Local Open Scope sep_scope.

  Local Notation word := (Naive.word 64).
  Local Notation mem := BasicC64Semantics.mem.

  (** Generic, length-parametric form: take a sep'd byte buffer of any
      length [n] back to [Memory.anybytes].

      Three hypotheses:
        - [Hlen : Z.of_nat (length bs) = n] — fixes the numeric length.
        - [Hbound : Z.of_nat (length bs) <= 2 ^ 64] — fits in address space.
        - [Hsep : ((bs$@addr) ⋆ R) m] — the sep'd buffer.

      The bound is required by [Memory.anybytes]'s definition.  In the
      specializations below it's trivially numeric. *)
  Lemma byte_buffer_to_anybytes :
    forall (n : Z) (bs : list Byte.byte) (addr : word)
           (R : mem -> Prop) (m : mem),
      Z.of_nat (Datatypes.length bs) = n ->
      Z.of_nat (Datatypes.length bs) <= 2 ^ 64 ->
      ((bs$@addr) ⋆ R)%sep m ->
      exists mStack mInner,
        Memory.anybytes addr n mStack /\
        map.split m mStack mInner /\
        R mInner.
  Proof.
    intros n bs addr R m Hlen Hbound Hsep.
    (* Unfold the top-level sep to extract the split + the byte-buffer
       memory mBuf, plus R-frame mInner. *)
    unfold sep at 1 in Hsep.
    destruct Hsep as (mBuf & mInner & Hsplit & Hbuf & HR).
    (* [Hbuf : sepclause_of_map (bs$@addr) mBuf] is just
       [bs$@addr = mBuf] (definitionally, by the [Logic.eq] coercion). *)
    cbv [sepclause_of_map] in Hbuf.
    (* Construct the [anybytes] witness directly from its definition. *)
    exists mBuf, mInner; ssplit; [|exact Hsplit|exact HR].
    cbv [Memory.anybytes].
    exists bs; ssplit; [exact Hbuf|exact Hlen|exact Hbound].
  Qed.

  (** Convenience specialization: 200-byte buffer (Ed25519 ACC/TMP). *)
  Lemma byte_buffer_to_anybytes_200 :
    forall (bs : list Byte.byte) (addr : word)
           (R : mem -> Prop) (m : mem),
      Datatypes.length bs = 200%nat ->
      ((bs$@addr) ⋆ R)%sep m ->
      exists mStack mInner,
        Memory.anybytes addr 200 mStack /\
        map.split m mStack mInner /\
        R mInner.
  Proof.
    intros bs addr R m Hlen Hsep.
    apply (byte_buffer_to_anybytes 200 bs addr R m).
    - rewrite Hlen. reflexivity.
    - rewrite Hlen. cbv. intros HC. discriminate HC.
    - exact Hsep.
  Qed.

  (** Convenience specialization: 120-byte buffer (Ed25519 B_pre). *)
  Lemma byte_buffer_to_anybytes_120 :
    forall (bs : list Byte.byte) (addr : word)
           (R : mem -> Prop) (m : mem),
      Datatypes.length bs = 120%nat ->
      ((bs$@addr) ⋆ R)%sep m ->
      exists mStack mInner,
        Memory.anybytes addr 120 mStack /\
        map.split m mStack mInner /\
        R mInner.
  Proof.
    intros bs addr R m Hlen Hsep.
    apply (byte_buffer_to_anybytes 120 bs addr R m).
    - rewrite Hlen. reflexivity.
    - rewrite Hlen. cbv. intros HC. discriminate HC.
    - exact Hsep.
  Qed.

End ByteBufferToAnybytes.
