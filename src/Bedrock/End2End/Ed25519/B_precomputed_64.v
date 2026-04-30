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
      Each u64 holds 8 consecutive bytes in little-endian order. *)
  Definition B_precomputed_u64s : list Z :=
    Eval vm_compute in
      List.map (fun i =>
        le_combine (List.firstn 8 (List.skipn (i * 8) B_precomputed_bytes)))
        (List.seq 0 12).

  Lemma B_precomputed_u64s_length : Datatypes.length B_precomputed_u64s = 12%nat.
  Proof. vm_compute. reflexivity. Qed.

End BPrecomputed64.
