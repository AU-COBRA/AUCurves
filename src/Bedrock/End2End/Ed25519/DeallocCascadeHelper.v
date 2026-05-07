(** * Helper lemma for the post-parametric-call dealloc cascade in
 *    [ed25519_scalarmult_base_correct].
 *
 *    Isolates the cascade body in its own [Qed]-able lemma so the main
 *    lemma's kernel-check operates on a small proof term.  Without this
 *    factoring, the inline cascade's [Qed] is exponential due to
 *    deeply-nested [chunk32_*]/[chunk40_*]/[bs] let-bindings.
 *
 *    The cascade takes the live post-parametric sep state and produces
 *    the 2-level dealloc + final post.
 *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Import Bedrock.End2End.Ed25519.DeallocCascade.
Require Import coqutil.Map.SeparationMemory.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.TransferSepsOrder.
Require Import coqutil.Sorting.OrderToPermutation.

Section DeallocCascadeHelper.
  Local Open Scope Z_scope.

  Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
  Local Notation felem := (felem(FieldRepresentation:=frep25519)).
  Local Notation word := (Naive.word 64).
  Local Notation mem := BasicC64Semantics.mem.

  (** The dealloc cascade lemma.  Given:
        - 3 felems X_b0, X_b1, X_b2,
        - 3 chunks of 32 bytes each,
        - the post-parametric sep,
      produces the 2-level [anybytes] split with the final
      [out_par/scalar/R]-frame at the inner memory. *)
  (** Sep-rearrangement for the post-parametric state.  The parametric
      spec gives
        [(out'$@out_ptr ⋆ scalar$@scalar_ptr ⋆ B_pre$@B_pre_addr ⋆ R)%sep m]
      with our instantiated [R := chunk32_0$@... ⋆ chunk32_1$@... ⋆ chunk32_2$@... ⋆ R_outer],
      i.e.,
        [(out'$@out_ptr ⋆ scalar$@scalar_ptr ⋆ concat$@B_pre_addr ⋆ (chunks ⋆ R_outer))%sep m].
      The cascade helper wants
        [(concat$@B_pre_addr ⋆ (out'$@out_ptr ⋆ scalar$@scalar_ptr ⋆ chunks ⋆ R_outer))%sep m].
      This lemma is just commutativity + flatten the inner chunks group. *)
  Lemma sep_rearrange_for_dealloc
    (m : mem) (out_par scalar concat_120 chunk32_0 chunk32_1 chunk32_2 : list Byte.byte)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (R : mem -> Prop) :
    (sepclause_of_map (out_par$@out_ptr) ⋆ sepclause_of_map (scalar$@scalar_ptr)
     ⋆ sepclause_of_map (concat_120$@B_pre_addr)
     ⋆ (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
        ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
        ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
        ⋆ R))%sep m ->
    (sepclause_of_map (concat_120$@B_pre_addr)
     ⋆ (sepclause_of_map (out_par$@out_ptr) ⋆ sepclause_of_map (scalar$@scalar_ptr)
        ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
        ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
        ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
        ⋆ R))%sep m.
  Proof.
    intros H. ecancel_assumption.
  Qed.

  Lemma dealloc_cascade_helper
    (m : mem) (out_par scalar : list Byte.byte)
    (X_b0 X_b1 X_b2 : felem)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (chunk32_0 chunk32_1 chunk32_2 : list Byte.byte)
    (R : mem -> Prop) :
    Datatypes.length chunk32_0 = 32%nat ->
    Datatypes.length chunk32_1 = 32%nat ->
    Datatypes.length chunk32_2 = 32%nat ->
    (sepclause_of_map (((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b0))
                        ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b1))
                        ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b2)))$@B_pre_addr)
      ⋆ (sepclause_of_map (out_par$@out_ptr) ⋆ sepclause_of_map (scalar$@scalar_ptr)
        ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
        ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
        ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
        ⋆ R))%sep m ->
    exists mInner mStack,
      Memory.anybytes B_pre_addr 120 mStack /\
      map.split m mInner mStack /\
      (exists mInner2 mStack2,
         Memory.anybytes B_pre_bytes_addr 96 mStack2 /\
         map.split mInner mInner2 mStack2 /\
         (sepclause_of_map (out_par$@out_ptr)
           ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep mInner2).
  Proof.
    intros Hc0_len Hc1_len Hc2_len Hsep_par_b.
    (* Dealloc 1: B_pre (120 bytes). *)
    assert (Hbs_120_len :
      Datatypes.length
        (((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b0))
          ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b1))
          ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b2)))%list)
      = 120%nat).
    { rewrite !List.length_app, !ws2bs_felem_length. cbn. reflexivity. }
    pose proof (byte_buffer_to_anybytes_120 _ B_pre_addr _ _ Hbs_120_len Hsep_par_b) as Hb120.
    destruct Hb120 as (mStack_120 & mInner_120 & Hany_120 & Hsplit_120 & HRest_120).
    exists mInner_120, mStack_120.
    split; [exact Hany_120 |].
    split; [apply Properties.map.split_comm; exact Hsplit_120 |].
    (* Dealloc 2: B_pre_bytes (96 bytes).  Combine 3 × 32-byte chunks. *)
    epose proof (sep_eq_of_list_word_at_app B_pre_bytes_addr
                   chunk32_0 (chunk32_1 ++ chunk32_2)%list 32
                   ltac:(rewrite Hc0_len; reflexivity)
                   ltac:(rewrite Hc0_len, !List.length_app, Hc1_len, Hc2_len; cbv [Bitwidth64.BW64]; lia)) as Hbpb0.
    epose proof (sep_eq_of_list_word_at_app
                   (word.add B_pre_bytes_addr (word.of_Z 32))
                   chunk32_1 chunk32_2 32
                   ltac:(rewrite Hc1_len; reflexivity)
                   ltac:(rewrite Hc1_len, Hc2_len; cbv [Bitwidth64.BW64]; lia)) as Hbpb1.
    replace (word.add (word.add B_pre_bytes_addr (word.of_Z 32)) (word.of_Z 32))
      with (word.add B_pre_bytes_addr (word.of_Z 64)) in Hbpb1 by ring.
    apply iff1ToEq in Hbpb0. apply iff1ToEq in Hbpb1.
    assert (Hbpb_combined :
      (sepclause_of_map ((chunk32_0 ++ chunk32_1 ++ chunk32_2)%list$@B_pre_bytes_addr)
        ⋆ (sepclause_of_map (out_par$@out_ptr)
          ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep mInner_120).
    { rewrite Hbpb0, Hbpb1. ecancel_assumption_impl. }
    clear Hbpb0 Hbpb1.
    assert (Hbs_96_len : Datatypes.length (chunk32_0 ++ chunk32_1 ++ chunk32_2)%list = 96%nat).
    { rewrite !List.length_app, Hc0_len, Hc1_len, Hc2_len. reflexivity. }
    pose proof (byte_buffer_to_anybytes 96 _ B_pre_bytes_addr _ _
                  ltac:(rewrite Hbs_96_len; reflexivity)
                  ltac:(rewrite Hbs_96_len; cbv [Bitwidth64.BW64]; lia)
                  Hbpb_combined) as Hb96.
    destruct Hb96 as (mStack_96 & mInner_96 & Hany_96 & Hsplit_96 & HRest_96).
    exists mInner_96, mStack_96.
    split; [exact Hany_96 |].
    split; [apply Properties.map.split_comm; exact Hsplit_96 |].
    exact HRest_96.
  Qed.

  (** Sep-reshape helpers for the 3 from_bytes call discharges in
      [ed25519_scalarmult_base_correct].  Each lemma's [Qed]-sealed body
      runs [cancel] once on the AC-permutation between the call's input
      sep state and the asserted output shape (chunk40_X isolated for the
      from_bytes destination buffer).  Factoring these out shrinks the
      main lemma's proof term, easing the [Qed] kernel-check.

      Usage at the call site (replaces inline [(use_sep_assumption; cancel)]):
        assert (Hsep_bN : <output>%sep mN) by
          (apply (proj1 (reshape_iff_bN ...)); ecancel_assumption).
   *)

  Lemma reshape_iff_b0
    (chunk32_0 chunk32_1 chunk32_2 chunk40_0 chunk40_1 chunk40_2 : list Byte.byte)
    (out_init scalar : list Byte.byte)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (R : mem -> Prop) :
    Lift1Prop.iff1
      (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
       ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
       ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
       ⋆ sepclause_of_map (chunk40_0$@B_pre_addr)
       ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
       ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
       ⋆ sepclause_of_map (out_init$@out_ptr)
       ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep
      (sepclause_of_map (chunk40_0$@B_pre_addr) ⋆
       (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
        ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
        ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
        ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
        ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
        ⋆ sepclause_of_map (out_init$@out_ptr)
        ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep.
  Proof. cancel. Qed.

  (* Note: b1 / b2 take the FElem chunks as abstract [mem -> Prop] arguments
     to avoid the [FElem] notation/typeclass mismatch between this file and
     [Scalarmult_Impl_64.v].  The caller passes
       [FElem B_pre_addr X_b0]   for [FE_b0]
       [FElem (B_pre_addr+40) X_b1] for [FE_b1] *)
  (* Input shape must match Hsep_b0_post's literal form so [exact Hsep_b0_post]
     closes the apply goal — no inline cancel needed at the call site. *)
  Lemma reshape_b1
    (m : mem)
    (chunk32_0 chunk32_1 chunk32_2 chunk40_1 chunk40_2 : list Byte.byte)
    (FE_b0 : mem -> Prop)
    (out_init scalar : list Byte.byte)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (R : mem -> Prop) :
    (FE_b0
     ⋆ (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
        ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
        ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
        ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
        ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
        ⋆ sepclause_of_map (out_init$@out_ptr)
        ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m ->
    (sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40))) ⋆
     (FE_b0
      ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
      ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
      ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
      ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
      ⋆ sepclause_of_map (out_init$@out_ptr)
      ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m.
  Proof. intros H. use_sep_assumption; cancel; reflexivity. Qed.

  Lemma reshape_b2
    (m : mem)
    (chunk32_0 chunk32_1 chunk32_2 chunk40_2 : list Byte.byte)
    (FE_b0 FE_b1 : mem -> Prop)
    (out_init scalar : list Byte.byte)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (R : mem -> Prop) :
    (FE_b1
     ⋆ (FE_b0
        ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
        ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
        ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
        ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
        ⋆ sepclause_of_map (out_init$@out_ptr)
        ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m ->
    (sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80))) ⋆
     (FE_b1
      ⋆ FE_b0
      ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
      ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
      ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
      ⋆ sepclause_of_map (out_init$@out_ptr)
      ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m.
  Proof. intros H. use_sep_assumption; cancel; reflexivity. Qed.

  (** [split_3x32_iff1]: Split a 96-byte buffer into 3 × 32-byte chunks.
      Replaces 2× sep_eq_of_list_word_at_app + 2× apply iff1ToEq + 2× rewrite +
      1× replace ring with one Qed-sealed iff1 application. *)
  Lemma split_3x32_iff1
    (bs c0 c1 c2 : list Byte.byte)
    (addr : word)
    (R : mem -> Prop)
    (Hsplit : bs = (c0 ++ c1 ++ c2)%list)
    (Hc0_len : Datatypes.length c0 = 32%nat)
    (Hc1_len : Datatypes.length c1 = 32%nat)
    (Hc2_len : Datatypes.length c2 = 32%nat) :
    Lift1Prop.iff1
      (sepclause_of_map (bs$@addr) ⋆ R)%sep
      (sepclause_of_map (c0$@addr)
       ⋆ sepclause_of_map (c1$@(word.add addr (word.of_Z 32)))
       ⋆ sepclause_of_map (c2$@(word.add addr (word.of_Z 64)))
       ⋆ R)%sep.
  Proof.
    rewrite Hsplit.
    epose proof (sep_eq_of_list_word_at_app addr c0 (c1 ++ c2)%list 32
                   ltac:(rewrite Hc0_len; reflexivity)
                   ltac:(rewrite Hc0_len, !List.length_app, Hc1_len, Hc2_len;
                         cbv [Bitwidth64.BW64]; lia)) as Hs0.
    epose proof (sep_eq_of_list_word_at_app
                   (word.add addr (word.of_Z 32))
                   c1 c2 32
                   ltac:(rewrite Hc1_len; reflexivity)
                   ltac:(rewrite Hc1_len, Hc2_len; cbv [Bitwidth64.BW64]; lia)) as Hs1.
    rewrite Hs0, Hs1.
    replace (word.add (word.add addr (word.of_Z 32)) (word.of_Z 32))
      with (word.add addr (word.of_Z 64)) by ring.
    cancel; reflexivity.
  Qed.

  (** [split_3x40_iff1]: Split a 120-byte buffer into 3 × 40-byte chunks. *)
  Lemma split_3x40_iff1
    (bs c0 c1 c2 : list Byte.byte)
    (addr : word)
    (R : mem -> Prop)
    (Hsplit : bs = (c0 ++ c1 ++ c2)%list)
    (Hc0_len : Datatypes.length c0 = 40%nat)
    (Hc1_len : Datatypes.length c1 = 40%nat)
    (Hc2_len : Datatypes.length c2 = 40%nat) :
    Lift1Prop.iff1
      (sepclause_of_map (bs$@addr) ⋆ R)%sep
      (sepclause_of_map (c0$@addr)
       ⋆ sepclause_of_map (c1$@(word.add addr (word.of_Z 40)))
       ⋆ sepclause_of_map (c2$@(word.add addr (word.of_Z 80)))
       ⋆ R)%sep.
  Proof.
    rewrite Hsplit.
    epose proof (sep_eq_of_list_word_at_app addr c0 (c1 ++ c2)%list 40
                   ltac:(rewrite Hc0_len; reflexivity)
                   ltac:(rewrite Hc0_len, !List.length_app, Hc1_len, Hc2_len;
                         cbv [Bitwidth64.BW64]; lia)) as Hs0.
    epose proof (sep_eq_of_list_word_at_app
                   (word.add addr (word.of_Z 40))
                   c1 c2 40
                   ltac:(rewrite Hc1_len; reflexivity)
                   ltac:(rewrite Hc1_len, Hc2_len; cbv [Bitwidth64.BW64]; lia)) as Hs1.
    rewrite Hs0, Hs1.
    replace (word.add (word.add addr (word.of_Z 40)) (word.of_Z 40))
      with (word.add addr (word.of_Z 80)) by ring.
    cancel; reflexivity.
  Qed.

End DeallocCascadeHelper.

(** [reflective_reshape Hin] replaces a goal of shape [(<target ⋆-tree>)%sep m]
    with [exact Hin]-style discharge by:
    1. flattening both the goal and [Hin]'s sep into [seps [...] m] form,
    2. computing the permutation order between target and input via
       [vm_compute] (delegated to [TransferSepsOrder]'s [get_order]),
    3. applying the [Qed]-sealed [reorder_is_iff1] with the concrete order.
    The resulting proof term is small: a [vm_compute]-checked [eq_refl]
    plus an opaque application of [reorder_is_iff1].
*)
Ltac reflective_reshape Hin :=
  flatten_seps_in_goal;
  flatten_seps_in Hin;
  lazymatch goal with
  | |- seps ?target ?m =>
      lazymatch type of Hin with
      | seps ?input _ =>
          (* get_order's convention: arg1 = desired order, arg2 = current.
             Result is [priority of input[i]] such that reorder order input = target. *)
          let order := get_order target input in
          let E := fresh "Eperm" in
          eassert (Lift1Prop.iff1 (seps input) (seps target)) as E;
          [ etransitivity;
            [ eapply (reorder_is_iff1 order input); reflexivity |];
            cbv [reorder];
            let r := eval vm_compute in (order_to_permutation order) in
              change (order_to_permutation order) with r;
            cbv [apply_permutation apply_permutation_with_default
                 my_list_map my_list_nth];
            cbn [seps];
            reflexivity
          | apply (proj1 (E m)); exact Hin ]
      end
  end.
