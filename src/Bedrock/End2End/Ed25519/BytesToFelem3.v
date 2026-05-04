(** * Bridge: 120-byte buffer ↔ 3 × 40-byte FElem chunks.
 *
 * Direct port of [BytesToFelem5.byte_acc_5felem_iff], scaled down
 * from 200 bytes / 5 chunks to 120 bytes / 3 chunks.  Used at
 * [B_pre]'s extraction in [ed25519_scalarmult_base_parametric_correct]
 * — the precomputed basepoint is 3 × 40-byte FElem chunks
 * (half_ypx, half_ymx, xyd). *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Import coqutil.Map.SeparationMemory.

Section BytesToFelem3.
  Local Open Scope Z_scope.

  Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
  Local Notation bs2felem := (bs2felem(field_representation:=frep25519)).

  Lemma byte_3felem_iff (acc : list byte) (addr : Naive.word 64)
    (Hlen : Datatypes.length acc = 120%nat) :
    Lift1Prop.iff1
      (sepclause_of_map (acc$@addr))
      (let X  := bs2felem (List.firstn 40 acc) in
       let Y  := bs2felem (List.firstn 40 (List.skipn 40 acc)) in
       let Z  := bs2felem (List.firstn 40 (List.skipn 80 acc)) in
       (FElem addr X
        ⋆ FElem (word.add addr (word.of_Z 40)) Y
        ⋆ FElem (word.add addr (word.of_Z 80)) Z)%sep).
  Proof.
    cbv zeta.
    set (chunk0 := ListDef.firstn 40 acc).
    set (chunk1 := ListDef.firstn 40 (ListDef.skipn 40 acc)).
    set (chunk2 := ListDef.firstn 40 (ListDef.skipn 80 acc)).
    assert (Hlen0 : Datatypes.length chunk0 = 40%nat) by
      (subst chunk0; rewrite List.length_firstn, Hlen; lia).
    assert (Hlen1 : Datatypes.length chunk1 = 40%nat) by
      (subst chunk1; rewrite List.length_firstn, List.length_skipn, Hlen; lia).
    assert (Hlen2 : Datatypes.length chunk2 = 40%nat) by
      (subst chunk2; rewrite List.length_firstn, List.length_skipn, Hlen; lia).
    assert (Hsplit : acc = chunk0 ++ chunk1 ++ chunk2) by
      ( subst chunk0 chunk1 chunk2;
        rewrite <- (List.firstn_skipn 40 acc) at 1; f_equal;
        rewrite <- (List.firstn_skipn 40 (ListDef.skipn 40 acc)) at 1;
        rewrite skipn_skipn; f_equal;
        ( replace (40 + 40)%nat with 80%nat by lia );
        rewrite (List.firstn_all2 (n:=40) (ListDef.skipn 80 acc))
          by (rewrite List.length_skipn, Hlen; lia);
        reflexivity ).
    rewrite Hsplit at 1.
    (* Two rounds of sep_eq_of_list_word_at_app to split the
       contiguous-bytes claim into three 40-byte chunks. *)
    epose proof (sep_eq_of_list_word_at_app addr chunk0
                   (chunk1 ++ chunk2) 40
      ltac:(rewrite Hlen0; reflexivity)
      ltac:(rewrite Hlen0, !List.length_app,
                    Hlen1, Hlen2;
            cbv [Bitwidth64.BW64]; lia)) as Hsep0.
    apply iff1ToEq in Hsep0; rewrite Hsep0; clear Hsep0.
    epose proof (sep_eq_of_list_word_at_app
                   (word.add addr (word.of_Z 40))
                   chunk1 chunk2 40
      ltac:(rewrite Hlen1; reflexivity)
      ltac:(rewrite Hlen1, Hlen2; cbv [Bitwidth64.BW64]; lia)) as Hsep1.
    apply iff1ToEq in Hsep1; rewrite Hsep1; clear Hsep1.
    (* Normalise the chained-add offset 40+40 to 80. *)
    replace (word.add (word.add addr (word.of_Z 40)) (word.of_Z 40)) with
      (word.add addr (word.of_Z 80)) by ring.
    (* Convert each [chunk_i$@addr_i] to [FElem addr_i (bs2felem chunk_i)]. *)
    epose proof (felem_from_bytes addr chunk0
                   ltac:(rewrite Hlen0; reflexivity)) as Hf0.
    apply iff1ToEq in Hf0; rewrite Hf0; clear Hf0.
    epose proof (felem_from_bytes (word.add addr (word.of_Z 40)) chunk1
                   ltac:(rewrite Hlen1; reflexivity)) as Hf1.
    apply iff1ToEq in Hf1; rewrite Hf1; clear Hf1.
    epose proof (felem_from_bytes (word.add addr (word.of_Z 80)) chunk2
                   ltac:(rewrite Hlen2; reflexivity)) as Hf2.
    apply iff1ToEq in Hf2; rewrite Hf2; clear Hf2.
    rewrite ?sep_assoc; reflexivity.
  Qed.

End BytesToFelem3.
