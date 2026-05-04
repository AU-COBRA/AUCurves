(** * Bridge: 200-byte buffer ↔ 5 × 40-byte FElem chunks.
 *
 * Used by [ed25519_scalarmult_base] to translate the byte-typed
 * accumulator (as managed by [cmov_5felems], a byte-level routine)
 * into the [p5@]-style FElem chunk view that the underlying
 * [add_precomputed]/[double] callees consume in their preconditions.
 *
 * The lemma is a pure separation-logic re-association: 200 bytes
 * = 5 × 40 bytes, and each 40-byte chunk corresponds to one FElem
 * via fiat-crypto's [felem_from_bytes] iff1.
 *
 * [FElem] shape: bare [Field.FElem ptr v] (no [Some bounds]
 * argument), matching the [p5@] notation in [EdwardsXYZT64.v]
 * and the preconditions of [add_precomputed64_ok]/[double64_ok]. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Import coqutil.Map.SeparationMemory.

Section BytesToFelem5.
  Local Open Scope Z_scope.

  Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
  Local Notation bs2felem := (bs2felem(field_representation:=frep25519)).

  (** Bridge: a 200-byte buffer at [addr] is iff1-equivalent to five
      40-byte FElem chunks placed at offsets 0/40/80/120/160.

      The proof:
      1. names the five 40-byte chunks via [set];
      2. proves a list-level decomposition [acc = c0++c1++c2++c3++c4];
      3. four rounds of [sep_eq_of_list_word_at_app] split the
         contiguous-bytes claim at offsets 40/80/120/160 (the
         intermediate offsets come out as nested [word.add (... 40) 40]
         and are normalised back via [ring]);
      4. five rounds of [felem_from_bytes] flip each 40-byte chunk
         into [FElem ptr (bs2felem chunk)];
      5. a final [rewrite ?sep_assoc] reconciles the LHS' right-assoc
         tower with the RHS' left-assoc form. *)
  Lemma byte_acc_5felem_iff (acc : list byte) (addr : Naive.word 64)
    (Hlen : Datatypes.length acc = 200%nat) :
    Lift1Prop.iff1
      (sepclause_of_map (acc$@addr))
      (let X  := bs2felem (List.firstn 40 acc) in
       let Y  := bs2felem (List.firstn 40 (List.skipn 40 acc)) in
       let Z  := bs2felem (List.firstn 40 (List.skipn 80 acc)) in
       let Ta := bs2felem (List.firstn 40 (List.skipn 120 acc)) in
       let Tb := bs2felem (List.firstn 40 (List.skipn 160 acc)) in
       (FElem addr X
        ⋆ FElem (word.add addr (word.of_Z 40)) Y
        ⋆ FElem (word.add addr (word.of_Z 80)) Z
        ⋆ FElem (word.add addr (word.of_Z 120)) Ta
        ⋆ FElem (word.add addr (word.of_Z 160)) Tb)%sep).
  Proof.
    cbv zeta.
    set (chunk0 := ListDef.firstn 40 acc).
    set (chunk1 := ListDef.firstn 40 (ListDef.skipn 40 acc)).
    set (chunk2 := ListDef.firstn 40 (ListDef.skipn 80 acc)).
    set (chunk3 := ListDef.firstn 40 (ListDef.skipn 120 acc)).
    set (chunk4 := ListDef.firstn 40 (ListDef.skipn 160 acc)).
    assert (Hlen0 : Datatypes.length chunk0 = 40%nat) by
      (subst chunk0; rewrite List.length_firstn, Hlen; lia).
    assert (Hlen1 : Datatypes.length chunk1 = 40%nat) by
      (subst chunk1; rewrite List.length_firstn, List.length_skipn, Hlen; lia).
    assert (Hlen2 : Datatypes.length chunk2 = 40%nat) by
      (subst chunk2; rewrite List.length_firstn, List.length_skipn, Hlen; lia).
    assert (Hlen3 : Datatypes.length chunk3 = 40%nat) by
      (subst chunk3; rewrite List.length_firstn, List.length_skipn, Hlen; lia).
    assert (Hlen4 : Datatypes.length chunk4 = 40%nat) by
      (subst chunk4; rewrite List.length_firstn, List.length_skipn, Hlen; lia).
    assert (Hsplit : acc = chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4) by
      ( subst chunk0 chunk1 chunk2 chunk3 chunk4;
        rewrite <- (List.firstn_skipn 40 acc) at 1; f_equal;
        rewrite <- (List.firstn_skipn 40 (ListDef.skipn 40 acc)) at 1;
        rewrite skipn_skipn; f_equal;
        ( replace (40 + 40)%nat with 80%nat by lia );
        rewrite <- (List.firstn_skipn 40 (ListDef.skipn 80 acc)) at 1;
        rewrite skipn_skipn; f_equal;
        ( replace (40 + 80)%nat with 120%nat by lia );
        rewrite <- (List.firstn_skipn 40 (ListDef.skipn 120 acc)) at 1;
        rewrite skipn_skipn; f_equal;
        ( replace (40 + 120)%nat with 160%nat by lia );
        rewrite (List.firstn_all2 (n:=40) (ListDef.skipn 160 acc))
          by (rewrite List.length_skipn, Hlen; lia);
        reflexivity ).
    rewrite Hsplit at 1.
    (* Four rounds of sep_eq_of_list_word_at_app to split the
       contiguous-bytes claim into five 40-byte chunks. *)
    epose proof (sep_eq_of_list_word_at_app addr chunk0
                   (chunk1 ++ chunk2 ++ chunk3 ++ chunk4) 40
      ltac:(rewrite Hlen0; reflexivity)
      ltac:(rewrite Hlen0, !List.length_app,
                    Hlen1, Hlen2, Hlen3, Hlen4;
            cbv [Bitwidth64.BW64]; lia)) as Hsep0.
    apply iff1ToEq in Hsep0; rewrite Hsep0; clear Hsep0.
    epose proof (sep_eq_of_list_word_at_app
                   (word.add addr (word.of_Z 40))
                   chunk1 (chunk2 ++ chunk3 ++ chunk4) 40
      ltac:(rewrite Hlen1; reflexivity)
      ltac:(rewrite Hlen1, !List.length_app,
                    Hlen2, Hlen3, Hlen4;
            cbv [Bitwidth64.BW64]; lia)) as Hsep1.
    apply iff1ToEq in Hsep1; rewrite Hsep1; clear Hsep1.
    epose proof (sep_eq_of_list_word_at_app
                   (word.add (word.add addr (word.of_Z 40)) (word.of_Z 40))
                   chunk2 (chunk3 ++ chunk4) 40
      ltac:(rewrite Hlen2; reflexivity)
      ltac:(rewrite Hlen2, !List.length_app, Hlen3, Hlen4;
            cbv [Bitwidth64.BW64]; lia)) as Hsep2.
    apply iff1ToEq in Hsep2; rewrite Hsep2; clear Hsep2.
    epose proof (sep_eq_of_list_word_at_app
                   (word.add (word.add (word.add addr (word.of_Z 40))
                                       (word.of_Z 40))
                             (word.of_Z 40))
                   chunk3 chunk4 40
      ltac:(rewrite Hlen3; reflexivity)
      ltac:(rewrite Hlen3, Hlen4; cbv [Bitwidth64.BW64]; lia)) as Hsep3.
    apply iff1ToEq in Hsep3; rewrite Hsep3; clear Hsep3.
    (* Normalise the chained-add offsets to single [word.add addr (...)]. *)
    replace (word.add (word.add addr (word.of_Z 40)) (word.of_Z 40)) with
      (word.add addr (word.of_Z 80)) by ring.
    replace (word.add (word.add addr (word.of_Z 80)) (word.of_Z 40)) with
      (word.add addr (word.of_Z 120)) by ring.
    replace (word.add (word.add addr (word.of_Z 120)) (word.of_Z 40)) with
      (word.add addr (word.of_Z 160)) by ring.
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
    epose proof (felem_from_bytes (word.add addr (word.of_Z 120)) chunk3
                   ltac:(rewrite Hlen3; reflexivity)) as Hf3.
    apply iff1ToEq in Hf3; rewrite Hf3; clear Hf3.
    epose proof (felem_from_bytes (word.add addr (word.of_Z 160)) chunk4
                   ltac:(rewrite Hlen4; reflexivity)) as Hf4.
    apply iff1ToEq in Hf4; rewrite Hf4; clear Hf4.
    (* LHS is right-assoc, RHS is left-assoc; reconcile. *)
    rewrite ?sep_assoc; reflexivity.
  Qed.

End BytesToFelem5.
