(** * Materialize Ed25519 basepoint in precomputed form (3 felems, 96 LE bytes).
 *
 * Computes [Ed25519XYZT.B_precomputed] = [Precomputed.of_twisted Curve25519.E.B]
 * and emits the result as a 96-byte little-endian byte sequence
 * (3 × 32 = 96 bytes). The bedrock2 wrapper for [ed25519_scalarmult_base]
 * stores these bytes onto the stack, calls [fe25519_from_bytes] 3× to
 * expand to limb form, and passes the resulting 120-byte limb buffer
 * to [ed25519_scalarmult_base_parametric].
 *
 * STATUS: Definition stated. The vm_compute may take noticeable time
 * (F.div = F.inv via Fermat = x^(p-2) for 255-bit p). To be tested. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Import Bedrock.End2End.Ed25519.EdwardsXYZT25519.
Require Import coqutil.Word.LittleEndianList.

Section BPrecomputed64.
  Local Open Scope Z_scope.

  Definition B_precomputed_F : F Curve25519.p * F Curve25519.p * F Curve25519.p :=
    Eval vm_compute in
      precomputed_coordinates Ed25519XYZT.B_precomputed.

  (** 96-byte LE encoding: 32 bytes for each of half_ypx, half_ymx, xyd.
      Each F p value's underlying Z is < p < 2^255, so 32 bytes suffice. *)
  Definition B_precomputed_bytes : list Byte.byte :=
    Eval vm_compute in
      let '(half_ypx, half_ymx, xyd) := B_precomputed_F in
      le_split 32 (F.to_Z half_ypx) ++
      le_split 32 (F.to_Z half_ymx) ++
      le_split 32 (F.to_Z xyd).

  Lemma B_precomputed_bytes_length : Datatypes.length B_precomputed_bytes = 96%nat.
  Proof. vm_compute. reflexivity. Qed.

  (** Pack the 96-byte LE encoding into 12 u64 values for cheaper
      bedrock2 materialization (12 word stores vs 96 byte stores).
      Each u64 holds 8 consecutive bytes in little-endian order.

      Defined symbolically via [List.chunk] so the round-trip lemma below
      can use [flat_map_le_split_combine_chunk] directly. *)
  Definition B_precomputed_u64s : list Z :=
    List.map le_combine (List.chunk 8 B_precomputed_bytes).

  Lemma B_precomputed_u64s_length : Datatypes.length B_precomputed_u64s = 12%nat.
  Proof.
    unfold B_precomputed_u64s.
    rewrite List.length_map, List.length_chunk by Lia.lia.
    rewrite B_precomputed_bytes_length. reflexivity.
  Qed.

  (** Round-trip: re-splitting reconstructs B_precomputed_bytes. Used by
      [ed25519_scalarmult_base_correct] (R10.E) to bridge between
      [init_u64_seq B_precomputed_u64s] (writes le_split bytes) and the
      byte form expected by [fe25519_from_bytes]. *)
  Lemma B_precomputed_u64s_to_bytes :
    List.flat_map (le_split 8) B_precomputed_u64s = B_precomputed_bytes.
  Proof.
    unfold B_precomputed_u64s.
    apply ArrayCasts.flat_map_le_split_combine_chunk; [Lia.lia |].
    rewrite B_precomputed_bytes_length. reflexivity.
  Qed.

  (** Each u64 in [B_precomputed_u64s] fits in [2^64] — needed as a
      [Forall] precondition for [init_u64_seq_correct]. *)
  Lemma B_precomputed_u64s_bound :
    List.Forall (fun v => 0 <= v < 2^64) B_precomputed_u64s.
  Proof.
    unfold B_precomputed_u64s.
    apply List.Forall_map.
    pose proof (List.Forall_chunk_length_le 8 ltac:(Lia.lia) B_precomputed_bytes) as Hchunks.
    eapply List.Forall_impl; [|exact Hchunks].
    intros bs [Hpos Hle].
    pose proof (le_combine_bound bs) as Hbnd.
    split; [Lia.lia |].
    apply Z.lt_le_trans with (1 := proj2 Hbnd).
    apply Z.pow_le_mono_r; [Lia.lia |]. Lia.lia.
  Qed.

  (** [bytes_in_bounds] for each 32-byte chunk of [B_precomputed_bytes].
      These are isolated as [Qed]-clean helpers so the [vm_compute] proof
      term stays in this file (small) rather than bleeding into the
      [ed25519_scalarmult_base_correct] proof's [Qed] kernel-check
      (where it becomes part of an exponential blowup). *)
  Lemma chunk32_0_in_bounds :
    bytes_in_bounds (FieldRepresentation:=frep25519) (List.firstn 32 B_precomputed_bytes).
  Proof. vm_compute. intuition. Qed.

  Lemma chunk32_1_in_bounds :
    bytes_in_bounds (FieldRepresentation:=frep25519)
      (List.firstn 32 (List.skipn 32 B_precomputed_bytes)).
  Proof. vm_compute. intuition. Qed.

  Lemma chunk32_2_in_bounds :
    bytes_in_bounds (FieldRepresentation:=frep25519)
      (List.skipn 64 B_precomputed_bytes).
  Proof. vm_compute. intuition. Qed.

End BPrecomputed64.
