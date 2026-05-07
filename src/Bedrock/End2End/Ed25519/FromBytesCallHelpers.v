(** * Helper lemmas for the [fe25519_from_bytes] call discharges in
 *    [ed25519_scalarmult_base_correct].
 *
 *    Phase 4 of the deep-embedding refactor: each of the 3 [fe25519_from_bytes]
 *    calls' 4-conjunct precondition discharge (input bytes / output buffer /
 *    length / bytes_in_bounds) is packaged into its own [Qed]-sealed Lemma,
 *    so the main lemma's proof term — and hence its [Qed] kernel-check time —
 *    shrinks accordingly.
 *
 *    Per-call structure (matching [Field.spec_of_from_bytes]):
 *      Goal 1: [exists Ra, (array ptsto (word.of_Z 1) <input_addr> <input_bytes>
 *                            * Ra)%sep m']
 *      Goal 2: [(<output_chunk>$@<output_addr> * Rr)%sep m']
 *      Goal 3: [length <output_chunk> = felem_size_in_bytes]
 *      Goal 4: [bytes_in_bounds <input_bytes>]
 *
 *    These helpers produce all 4 conjuncts simultaneously from the ambient
 *    sep state, so the call site only has to supply one [apply] / [exact]
 *    instead of the inline [ssplit] cascade.
 *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Import Bedrock.End2End.Ed25519.DeallocCascadeHelper.
Require Import Bedrock.End2End.Ed25519.Felems3ToBytes.
Require Import Bedrock.Util.SepReflectiveAC.
Require Import coqutil.Map.SeparationMemory.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.

Section FromBytesCallHelpers.
  Local Open Scope Z_scope.

  Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
  Local Notation felem := (felem(FieldRepresentation:=frep25519)).
  Local Notation word := (Naive.word 64).
  Local Notation mem := BasicC64Semantics.mem.

  (** [from_bytes_precond_b0]: produces the 4-conjunct precondition for the
      1st [fe25519_from_bytes(B_pre, B_pre_bytes)] call.

      Inputs:
        - [m']             : ambient memory at the call point
        - [chunk32_0/1/2]  : 32-byte chunks of the source [B_precomputed_bytes]
        - [chunk40_0/1/2]  : 40-byte raw output buffers (carved from B_pre)
        - [out_init scalar]: the 200-byte output + 32-byte scalar
        - [out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr]: addresses
        - [R]              : outer separating frame
        - [Hsep']          : the live sep state (chunked form)
        - [Hc0_len]        : [length chunk32_0 = 32]
        - [Hb0_len]        : [length chunk40_0 = 40]
        - [Hbib_c0]        : [bytes_in_bounds chunk32_0]
   *)
  Lemma from_bytes_precond_b0
    (m' : mem)
    (chunk32_0 chunk32_1 chunk32_2 chunk40_0 chunk40_1 chunk40_2 : list Byte.byte)
    (out_init scalar : list Byte.byte)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (R : mem -> Prop)
    (Hsep' :
      (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
       ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
       ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
       ⋆ sepclause_of_map (chunk40_0$@B_pre_addr)
       ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
       ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
       ⋆ sepclause_of_map (out_init$@out_ptr)
       ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep m')
    (Hc0_len : Datatypes.length chunk32_0 = 32%nat)
    (Hb0_len : Datatypes.length chunk40_0 = 40%nat)
    (Hbib_c0 : Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_0) :
    (* Goal 1: input bytes ⊆ memory *)
    (exists Ra, (Array.array ptsto (word.of_Z 1) B_pre_bytes_addr chunk32_0 ⋆ Ra)%sep m')
    /\
    (* Goal 2: output buffer carved out *)
    (sepclause_of_map (chunk40_0$@B_pre_addr) ⋆
     (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
      ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
      ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
      ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
      ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
      ⋆ sepclause_of_map (out_init$@out_ptr)
      ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m'
    /\
    (* Goal 3: output length *)
    Datatypes.length chunk40_0 = Z.to_nat (Field.felem_size_in_bytes (FieldRepresentation:=frep25519))
    /\
    (* Goal 4: bytes_in_bounds *)
    Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_0.
  Proof.
    ssplit.
    - (* Goal 1: input bytes ⊆ memory — use array1_iff_eq_of_list_word_at to
         convert the [chunk32_0$@B_pre_bytes_addr] sepclause to [array ptsto]
         form, then existential witness with the rest. *)
      pose proof (array1_iff_eq_of_list_word_at B_pre_bytes_addr chunk32_0
                    ltac:(rewrite Hc0_len; cbn; lia)) as Hiff_c0.
      apply iff1ToEq in Hiff_c0.
      eexists. setoid_rewrite Hiff_c0. reflective_ecancel Hsep'.
    - (* Goal 2: output buffer — apply Qed-sealed iff1 helper [reshape_iff_b0]. *)
      pose proof (reshape_iff_b0 chunk32_0 chunk32_1 chunk32_2
                    chunk40_0 chunk40_1 chunk40_2 out_init scalar
                    out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr R) as Hiff_b0.
      apply iff1ToEq in Hiff_b0.
      rewrite <- Hiff_b0. ecancel_assumption.
    - (* Goal 3: length — felem_size_in_bytes computes to 40. *)
      change (Z.to_nat (Field.felem_size_in_bytes (FieldRepresentation:=frep25519)))
        with 40%nat.
      exact Hb0_len.
    - (* Goal 4: bytes_in_bounds passed in. *)
      exact Hbib_c0.
  Qed.

  (** [from_bytes_precond_b1]: produces the 4-conjunct precondition for the
      2nd [fe25519_from_bytes(B_pre + 40, B_pre_bytes + 32)] call.

      Mirrors [from_bytes_precond_b0] with [chunk32_0]→[chunk32_1],
      [chunk40_0]→[chunk40_1], and [reshape_iff_b0]→[reshape_b1].  The
      output buffer is now [chunk40_1] at offset 40, and the [FElem] for
      [X_b0] is taken as a [mem -> Prop] argument [FE_b0] to avoid the
      [FElem] notation/typeclass mismatch (matching [reshape_b1]). *)
  Lemma from_bytes_precond_b1
    (m' : mem)
    (chunk32_0 chunk32_1 chunk32_2 chunk40_1 chunk40_2 : list Byte.byte)
    (FE_b0 : mem -> Prop)
    (out_init scalar : list Byte.byte)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (R : mem -> Prop)
    (Hsep_b0_post :
      (FE_b0
       ⋆ (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
          ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
          ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
          ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
          ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
          ⋆ sepclause_of_map (out_init$@out_ptr)
          ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m')
    (Hc1_len : Datatypes.length chunk32_1 = 32%nat)
    (Hb1_len : Datatypes.length chunk40_1 = 40%nat)
    (Hbib_c1 : Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_1) :
    (* Goal 1: input bytes ⊆ memory *)
    (exists Ra, (Array.array ptsto (word.of_Z 1)
                  (word.add B_pre_bytes_addr (word.of_Z 32)) chunk32_1 ⋆ Ra)%sep m')
    /\
    (* Goal 2: output buffer carved out *)
    (sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40))) ⋆
     (FE_b0
      ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
      ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
      ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
      ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
      ⋆ sepclause_of_map (out_init$@out_ptr)
      ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m'
    /\
    (* Goal 3: output length *)
    Datatypes.length chunk40_1 = Z.to_nat (Field.felem_size_in_bytes (FieldRepresentation:=frep25519))
    /\
    (* Goal 4: bytes_in_bounds *)
    Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_1.
  Proof.
    ssplit.
    - pose proof (array1_iff_eq_of_list_word_at
                    (word.add B_pre_bytes_addr (word.of_Z 32)) chunk32_1
                    ltac:(rewrite Hc1_len; cbn; lia)) as Hiff_c1.
      apply iff1ToEq in Hiff_c1.
      eexists. setoid_rewrite Hiff_c1. reflective_ecancel Hsep_b0_post.
    - apply (reshape_b1 m' chunk32_0 chunk32_1 chunk32_2
                chunk40_1 chunk40_2 FE_b0
                out_init scalar
                out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr R).
      exact Hsep_b0_post.
    - change (Z.to_nat (Field.felem_size_in_bytes (FieldRepresentation:=frep25519)))
        with 40%nat.
      exact Hb1_len.
    - exact Hbib_c1.
  Qed.

  (** [from_bytes_precond_b2]: produces the 4-conjunct precondition for the
      3rd [fe25519_from_bytes(B_pre + 80, B_pre_bytes + 64)] call.

      Symmetric to [from_bytes_precond_b1]: pulls [chunk32_2] / [chunk40_2]
      and uses [reshape_b2] for the output-buffer reshape. *)
  Lemma from_bytes_precond_b2
    (m' : mem)
    (chunk32_0 chunk32_1 chunk32_2 chunk40_2 : list Byte.byte)
    (FE_b0 FE_b1 : mem -> Prop)
    (out_init scalar : list Byte.byte)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (R : mem -> Prop)
    (Hsep_b1_post :
      (FE_b1
       ⋆ (FE_b0
          ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
          ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
          ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
          ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
          ⋆ sepclause_of_map (out_init$@out_ptr)
          ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m')
    (Hc2_len : Datatypes.length chunk32_2 = 32%nat)
    (Hb2_len : Datatypes.length chunk40_2 = 40%nat)
    (Hbib_c2 : Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_2) :
    (* Goal 1: input bytes ⊆ memory *)
    (exists Ra, (Array.array ptsto (word.of_Z 1)
                  (word.add B_pre_bytes_addr (word.of_Z 64)) chunk32_2 ⋆ Ra)%sep m')
    /\
    (* Goal 2: output buffer carved out *)
    (sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80))) ⋆
     (FE_b1
      ⋆ FE_b0
      ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
      ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
      ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
      ⋆ sepclause_of_map (out_init$@out_ptr)
      ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m'
    /\
    (* Goal 3: output length *)
    Datatypes.length chunk40_2 = Z.to_nat (Field.felem_size_in_bytes (FieldRepresentation:=frep25519))
    /\
    (* Goal 4: bytes_in_bounds *)
    Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_2.
  Proof.
    ssplit.
    - pose proof (array1_iff_eq_of_list_word_at
                    (word.add B_pre_bytes_addr (word.of_Z 64)) chunk32_2
                    ltac:(rewrite Hc2_len; cbn; lia)) as Hiff_c2.
      apply iff1ToEq in Hiff_c2.
      eexists. setoid_rewrite Hiff_c2. reflective_ecancel Hsep_b1_post.
    - apply (reshape_b2 m' chunk32_0 chunk32_1 chunk32_2 chunk40_2
                FE_b0 FE_b1
                out_init scalar
                out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr R).
      exact Hsep_b1_post.
    - change (Z.to_nat (Field.felem_size_in_bytes (FieldRepresentation:=frep25519)))
        with 40%nat.
      exact Hb2_len.
    - exact Hbib_c2.
  Qed.

  (** [parametric_call_precond]: produces the 4-conjunct precondition for the
      [ed25519_scalarmult_base_parametric] call.

      Unlike the 3 [from_bytes] helpers, this one uses the 3-arg parametric
      [fnspec] shape: 3 length conjuncts ([out=200], [scalar=32], [B_pre=120])
      plus a single sep-state with 4 atoms ([out * scalar * B_pre * R']).

      Strategy: instantiate [B_pre] to the 120-byte concat of three
      [ws2bs (felem_to_list X_bi)] (the felem-to-bytes encoding from
      [Felems3ToBytes.v]); instantiate the spec's outer frame [R'] to the
      three [chunk32_*] ⋆ outer R.  Then [felems3_to_bytes_iff] rewrites
      the goal's concat$@B_pre_addr back to the FElem chain that
      [Hsep_b2_post] already exposes.  *)
  Lemma parametric_call_precond
    (m' : mem)
    (chunk32_0 chunk32_1 chunk32_2 out_init scalar : list Byte.byte)
    (X_b0 X_b1 X_b2 : felem)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (R : mem -> Prop)
    (Hlen_out : Datatypes.length out_init = 200%nat)
    (Hlen_scalar : Datatypes.length scalar = 32%nat)
    (Hsep_b2_post :
      (FElem (word.add B_pre_addr (word.of_Z 80)) X_b2
       ⋆ (FElem (word.add B_pre_addr (word.of_Z 40)) X_b1
          ⋆ FElem B_pre_addr X_b0
          ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
          ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
          ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
          ⋆ sepclause_of_map (out_init$@out_ptr)
          ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m') :
    (* Goal 1: length out *)
    Datatypes.length out_init = 200%nat
    /\
    (* Goal 2: length scalar *)
    Datatypes.length scalar = 32%nat
    /\
    (* Goal 3: length B_pre — the 120-byte concat. *)
    Datatypes.length
      (((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b0))
        ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b1))
        ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b2)))%list)
      = 120%nat
    /\
    (* Goal 4: combined sep — concat$@B_pre_addr alongside the spec's frame. *)
    (sepclause_of_map (out_init$@out_ptr)
     ⋆ sepclause_of_map (scalar$@scalar_ptr)
     ⋆ sepclause_of_map (((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b0))
                          ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b1))
                          ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b2)))%list$@B_pre_addr)
     ⋆ (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
        ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
        ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
        ⋆ R))%sep m'.
  Proof.
    ssplit.
    - exact Hlen_out.
    - exact Hlen_scalar.
    - rewrite !List.length_app, !ws2bs_felem_length. cbn. reflexivity.
    - pose proof (felems3_to_bytes_iff X_b0 X_b1 X_b2 B_pre_addr) as Hhelper.
      apply iff1ToEq in Hhelper.
      rewrite <- Hhelper.
      ecancel_assumption_impl.
  Qed.

End FromBytesCallHelpers.
