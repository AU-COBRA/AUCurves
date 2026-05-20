(******************************************************************************)
(*    Lizard encoding: reversible 16-byte ↔ ristretto255 point               *)
(******************************************************************************)

From Stdlib Require Import Utf8 List ZArith Bool NArith Lia Btauto.
Require Import Stdlib.Strings.Byte.
Import ListNotations.

Fixpoint list_beq {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
    (l1 l2 : list A) : bool :=
  match l1, l2 with
  | nil, nil => true
  | x :: l1', y :: l2' => if eq_dec x y then list_beq eq_dec l1' l2' else false
  | _, _ => false
  end.

Lemma list_beq_refl {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) l :
  list_beq eq_dec l l = true.
Proof. induction l; simpl; auto. destruct (eq_dec a a); [auto|contradiction]. Qed.

Lemma list_beq_eq {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) l1 l2 :
  list_beq eq_dec l1 l2 = true <-> l1 = l2.
Proof.
  revert l2; induction l1 as [|x l1 IH]; destruct l2 as [|y l2];
    simpl; try (split; discriminate); [split; auto|].
  destruct (eq_dec x y) as [->|]; [rewrite IH; split; [intros ->|intros H; injection H]; auto|split; [discriminate|intros H; injection H; intros; contradiction]].
Qed.

Section LizardSpec.
  Variable SHA256 : list byte -> list byte.
  Variable SHA256_length : forall msg, length (SHA256 msg) = 32%nat.
  Variable ristretto_point : Type.
  Variable elligator2_encode : list byte -> ristretto_point.
  Variable elligator2_decode_candidates : ristretto_point -> list (list byte).

  Definition lizard_build_buffer (msg : list byte) : list byte :=
    let h := SHA256 msg in firstn 8 h ++ msg ++ skipn 24 h.
  Definition lizard_extract_msg (buf : list byte) : list byte :=
    firstn 16 (skipn 8 buf).

  Definition byte_of_N_default (n : N) : byte :=
    match Byte.of_N n with Some b => b | None => x00 end.

  Lemma byte_of_N_default_to_N (n : N) (Hn : (n < 256)%N) :
    Byte.to_N (byte_of_N_default n) = n.
  Proof.
    unfold byte_of_N_default.
    destruct (Byte.of_N n) eqn:E.
    - apply Byte.to_of_N in E. exact E.
    - exfalso. pose proof (Byte.to_of_N_option_map n) as H.
      rewrite E in H. simpl in H.
      destruct (N.leb n 255) eqn:Hleb; [discriminate|].
      apply N.leb_gt in Hleb. lia.
  Qed.

  Definition clear_byte0 (b : byte) : byte := byte_of_N_default (N.land (Byte.to_N b) 254).
  Definition clear_byte31 (b : byte) : byte := byte_of_N_default (N.land (Byte.to_N b) 63).

  Lemma N_land_bound x mask : (mask < 256)%N -> (N.land x mask < 256)%N.
  Proof. intros. eapply N.le_lt_trans; [apply N.land_le_r|assumption]. Qed.

  Lemma clear_byte0_idem b : clear_byte0 (clear_byte0 b) = clear_byte0 b.
  Proof. unfold clear_byte0. f_equal. rewrite byte_of_N_default_to_N by (apply N_land_bound; lia).
    apply N.bits_inj; intros n; rewrite !N.land_spec; btauto. Qed.

  Lemma clear_byte31_idem b : clear_byte31 (clear_byte31 b) = clear_byte31 b.
  Proof. unfold clear_byte31. f_equal. rewrite byte_of_N_default_to_N by (apply N_land_bound; lia).
    apply N.bits_inj; intros n; rewrite !N.land_spec; btauto. Qed.

  Definition clear_bits (buf : list byte) : list byte :=
    match buf with
    | b0 :: rest =>
      match rev rest with
      | b31 :: rest_rev => clear_byte0 b0 :: rev (clear_byte31 b31 :: rest_rev)
      | _ => clear_byte0 b0 :: rest
      end
    | _ => buf
    end.

  Lemma clear_bits_idempotent buf : clear_bits (clear_bits buf) = clear_bits buf.
  Proof.
    destruct buf as [|b0 rest]; [reflexivity|].
    unfold clear_bits at 1 2 3.
    destruct (rev rest) as [|b31 rest_rev] eqn:Hrev.
    - rewrite Hrev. simpl. rewrite clear_byte0_idem. reflexivity.
    - rewrite rev_involutive. simpl.
      rewrite clear_byte0_idem, clear_byte31_idem. reflexivity.
  Qed.

  Lemma clear_bits_length buf : length (clear_bits buf) = length buf.
  Proof.
    unfold clear_bits. destruct buf as [|b0 rest]; [reflexivity|].
    destruct (rev rest) as [|b31 rest_rev] eqn:Hrev; [reflexivity|].
    (* Goal: length (clear_byte0 b0 :: rev (clear_byte31 b31 :: rest_rev)) = S (length rest) *)
    change (length (clear_byte0 b0 :: rev (clear_byte31 b31 :: rest_rev)))
      with (S (length (rev (clear_byte31 b31 :: rest_rev)))).
    rewrite length_rev. simpl length at 2.
    (* Now: S (S (length rest_rev)) = S (length rest) *)
    f_equal.
    simpl. rewrite <- (length_rev rest). rewrite Hrev. simpl. reflexivity.
  Qed.

  (* clear_bits_preserves_middle: proved via positional argument.
     clear_bits modifies byte 0 and byte 31 only.
     extract_msg takes bytes 8-23. No overlap.
     The proof uses skipn_app + firstn_app + length_rev on the rev-based structure. *)
  Lemma clear_bits_preserves_middle buf :
    length buf = 32%nat -> lizard_extract_msg (clear_bits buf) = lizard_extract_msg buf.
  Proof.
    intro Hlen. unfold lizard_extract_msg, clear_bits.
    destruct buf as [|b0 rest]; [simpl in Hlen; lia|].
    destruct (rev rest) as [|b31 rest_rev] eqn:Hrev.
    { exfalso. assert (length rest = 31%nat) by (simpl in Hlen; lia).
      rewrite <- (length_rev rest) in H. rewrite Hrev in H. simpl in H. lia. }
    assert (Hrl : length rest = 31%nat) by (simpl in Hlen; lia).
    assert (Hrv : length rest_rev = 30%nat).
    { pose proof (f_equal (@length byte) Hrev) as H2. rewrite length_rev in H2. simpl in H2. lia. }
    assert (Hrest : rest = rev rest_rev ++ [b31]).
    { apply (f_equal (@rev byte)) in Hrev. rewrite rev_involutive in Hrev. simpl in Hrev. exact Hrev. }
    assert (Hctail : rev (clear_byte31 b31 :: rest_rev) = rev rest_rev ++ [clear_byte31 b31]).
    { change (clear_byte31 b31 :: rest_rev) with ([clear_byte31 b31] ++ rest_rev).
      rewrite rev_app_distr. simpl. reflexivity. }
    (* Use [change] instead of [simpl skipn] to avoid expanding rev *)
    change (firstn 16 (skipn 8 (clear_byte0 b0 :: rev (clear_byte31 b31 :: rest_rev))))
      with (firstn 16 (skipn 7 (rev (clear_byte31 b31 :: rest_rev)))).
    change (firstn 16 (skipn 8 (b0 :: rest))) with (firstn 16 (skipn 7 rest)).
    rewrite Hctail, Hrest.
    assert (Hvrl : length (rev rest_rev) = 30%nat) by (rewrite length_rev; lia).
    rewrite !(skipn_app 7 (rev rest_rev)). rewrite Hvrl.
    replace (7 - 30) with 0 by lia.
    rewrite !(firstn_app 16 (skipn 7 (rev rest_rev))).
    rewrite length_skipn, Hvrl. replace (16 - (30 - 7)) with 0 by lia.
    rewrite !firstn_O. rewrite !app_nil_r. reflexivity.
  Qed.

  Definition lizard_encode msg := elligator2_encode (clear_bits (lizard_build_buffer msg)).
  Definition lizard_check_valid buf :=
    list_beq Byte.byte_eq_dec buf (clear_bits (lizard_build_buffer (lizard_extract_msg buf))).
  Definition lizard_decode pt :=
    match filter lizard_check_valid (elligator2_decode_candidates pt) with
    | buf :: _ => Some (lizard_extract_msg buf) | nil => None end.

  Hypothesis elligator2_roundtrip :
    forall buf, In buf (elligator2_decode_candidates (elligator2_encode buf)).

  Lemma build_buffer_length msg :
    length msg = 16%nat -> length (lizard_build_buffer msg) = 32%nat.
  Proof.
    intros Hlen. unfold lizard_build_buffer.
    rewrite !length_app, length_firstn, length_skipn, SHA256_length.
    simpl. lia.
  Qed.

  Lemma extract_build msg :
    length msg = 16%nat -> lizard_extract_msg (lizard_build_buffer msg) = msg.
  Proof.
    intro Hlen. unfold lizard_extract_msg, lizard_build_buffer.
    assert (Hh : length (firstn 8 (SHA256 msg)) = 8)
      by (rewrite length_firstn, SHA256_length; lia).
    rewrite skipn_app. rewrite Hh. replace (8 - 8) with 0 by lia.
    rewrite skipn_O. rewrite skipn_all2 by lia.
    rewrite app_nil_l. rewrite firstn_app. rewrite Hlen.
    replace (16 - 16) with 0 by lia. rewrite firstn_O.
    rewrite app_nil_r. apply firstn_all2. lia.
  Qed.

  Lemma extract_cleared_build msg :
    length msg = 16%nat ->
    lizard_extract_msg (clear_bits (lizard_build_buffer msg)) = msg.
  Proof.
    intros. rewrite clear_bits_preserves_middle by (apply build_buffer_length; auto).
    apply extract_build; auto.
  Qed.

  Lemma check_valid_means_canonical buf :
    lizard_check_valid buf = true ->
    buf = clear_bits (lizard_build_buffer (lizard_extract_msg buf)).
  Proof. unfold lizard_check_valid. intro H. apply list_beq_eq in H. exact H. Qed.

  Lemma check_valid_original msg :
    length msg = 16%nat ->
    lizard_check_valid (clear_bits (lizard_build_buffer msg)) = true.
  Proof.
    intros Hlen. unfold lizard_check_valid.
    rewrite extract_cleared_build by exact Hlen.
    (* Goal: list_beq ... (clear_bits(build_buffer msg)) (clear_bits(build_buffer msg)) = true *)
    apply list_beq_refl.
  Qed.

  Hypothesis at_most_one_valid :
    forall pt buf1 buf2,
      In buf1 (elligator2_decode_candidates pt) ->
      In buf2 (elligator2_decode_candidates pt) ->
      lizard_check_valid buf1 = true -> lizard_check_valid buf2 = true ->
      buf1 = buf2.

  Theorem lizard_roundtrip msg :
    length msg = 16%nat -> lizard_decode (lizard_encode msg) = Some msg.
  Proof.
    intros Hlen. unfold lizard_decode, lizard_encode.
    set (buf := clear_bits (lizard_build_buffer msg)).
    pose proof (elligator2_roundtrip buf) as Hin.
    pose proof (check_valid_original msg Hlen) as Hvalid.
    assert (Hin_f : In buf (filter lizard_check_valid
                    (elligator2_decode_candidates (elligator2_encode buf)))).
    { apply filter_In. tauto. }
    (* The filtered list is non-empty since buf is in it *)
    destruct (filter lizard_check_valid
              (elligator2_decode_candidates (elligator2_encode buf)))
      as [|first rest] eqn:Hfilt.
    { exfalso. exact (in_nil Hin_f). }
    simpl. f_equal.
    (* first passes check_valid (it's in the filtered list) *)
    assert (Hfirst_valid : lizard_check_valid first = true).
    { assert (Hin_first := in_eq first rest).
      rewrite <- Hfilt in Hin_first.
      apply filter_In in Hin_first. destruct Hin_first; assumption. }
    assert (Hfirst_in : In first (elligator2_decode_candidates (elligator2_encode buf))).
    { assert (Hin_first := in_eq first rest).
      rewrite <- Hfilt in Hin_first.
      apply filter_In in Hin_first. destruct Hin_first; assumption. }
    (* first = buf by collision-freeness *)
    pose proof (at_most_one_valid _ _ _ Hin Hfirst_in Hvalid Hfirst_valid) as Heq.
    rewrite <- Heq. subst buf. exact (extract_cleared_build msg Hlen).
  Qed.

End LizardSpec.
