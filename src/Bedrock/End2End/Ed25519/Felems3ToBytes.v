(** * Bridge: 3 × FElem chunks ↔ 120-byte concatenation.
 *
 * Reverse direction of [BytesToFelem3.byte_3felem_iff] — given 3
 * concrete [felem] values [X0, X1, X2] at consecutive 40-byte offsets,
 * the FElem chain is iff1 to a single 120-byte byte-string laid out
 * at [addr], where the byte-string is the concatenation of the three
 * encoded representations [ws2bs 8 (felem_to_list X_i)].
 *
 * Used at the parametric call discharge in
 * [ed25519_scalarmult_base_correct] (Scalarmult_Impl_64.v), where the
 * three [from_bytes] calls produce 3 [FElem]s but the parametric spec
 * requires a single 120-byte raw view at [B_pre]. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Import coqutil.Map.SeparationMemory.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.

Section Felems3ToBytes.
  Local Open Scope Z_scope.

  Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
  Local Notation felem := (felem(FieldRepresentation:=frep25519)).

  Lemma felems3_to_bytes_iff (X0 X1 X2 : felem) (addr : Naive.word 64) :
    Lift1Prop.iff1
      (FElem addr X0
       ⋆ FElem (word.add addr (word.of_Z 40)) X1
       ⋆ FElem (word.add addr (word.of_Z 80)) X2)%sep
      (sepclause_of_map
         (((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X0))
           ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X1))
           ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X2)))$@addr)).
  Proof.
    pose proof (felem_to_bytes (field_representation:=frep25519) addr X0) as Hf2b0.
    pose proof (felem_to_bytes (field_representation:=frep25519) (word.add addr (word.of_Z 40)) X1) as Hf2b1.
    pose proof (felem_to_bytes (field_representation:=frep25519) (word.add addr (word.of_Z 80)) X2) as Hf2b2.
    epose proof (sep_eq_of_list_word_at_app addr
                   (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X0))
                   ((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X1))
                    ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X2)))%list 40
                   ltac:(rewrite ws2bs_felem_length; cbn; reflexivity)
                   ltac:(rewrite !List.length_app, !ws2bs_felem_length;
                         change (Z.to_nat felem_size_in_bytes) with 40%nat in *; cbv [Bitwidth64.BW64]; lia)) as Hcat0.
    epose proof (sep_eq_of_list_word_at_app (word.add addr (word.of_Z 40))
                   (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X1))
                   (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X2)) 40
                   ltac:(rewrite ws2bs_felem_length; cbn; reflexivity)
                   ltac:(rewrite !ws2bs_felem_length;
                         change (Z.to_nat felem_size_in_bytes) with 40%nat in *; cbv [Bitwidth64.BW64]; lia)) as Hcat1.
    replace (word.add (word.add addr (word.of_Z 40)) (word.of_Z 40))
      with (word.add addr (word.of_Z 80)) in Hcat1 by ring.
    intros m. split; intros HH.
    - seprewrite_in Hf2b0 HH.
      seprewrite_in Hf2b1 HH.
      seprewrite_in Hf2b2 HH.
      seprewrite Hcat0.
      seprewrite Hcat1.
      ecancel_assumption_impl.
    - seprewrite_in Hcat0 HH.
      seprewrite_in Hcat1 HH.
      seprewrite Hf2b0.
      seprewrite Hf2b1.
      seprewrite Hf2b2.
      ecancel_assumption_impl.
  Qed.

End Felems3ToBytes.
