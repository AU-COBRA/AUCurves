(** * BLS12_MSM_WindowBridge: extracted bridge lemmas for Phase A

    Minimal dependencies: just word + Stdlib.  This file exists so MCP can
    iterate on the [window_zero_from_idx_zero] bridge in seconds instead of
    waiting for the full [BLS12_MSM.v] compile.
*)

From Stdlib Require Import ZArith Lia List.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import bedrock2.ZnWords.

Import ListNotations.
Local Open Scope Z_scope.

(** BLS12-381 Pippenger constants. *)
Definition c : Z := 9.
Definition scalar_limbs : nat := 4.
Definition num_windows : Z := 29.

(** Extract the w-th c-bit window from a 256-bit scalar (as 4 u64 limbs). *)
Definition get_window (scalar : list Z) (w c : nat) : Z :=
  let bit_offset := (w * c)%nat in
  let limb := (bit_offset / 64)%nat in
  let shift := (bit_offset mod 64)%nat in
  let mask := Z.ones (Z.of_nat c) in
  let val := match nth_error scalar limb with
             | Some v => Z.shiftr v (Z.of_nat shift)
             | None => 0
             end in
  let val' := if Nat.ltb 64 (shift + c) then
                match nth_error scalar (limb + 1) with
                | Some v2 => Z.lor val (Z.shiftl v2 (Z.of_nat (64 - shift)))
                | None => val
                end
              else val in
  Z.land val' mask.

Section WindowBridge.
  Context {width : Z} {word : Interface.word width}
          {word_ok : word.ok word}
          (Hwidth64 : width = 64).

  (** Word-level get_window correctness.  Copied verbatim from BLS12_MSM.v
      so this file is self-contained. *)
  Lemma get_window_word_correct
      (scalar_ws : list word) (w_val : Z) (val_w : word)
      (Hw_val : 0 <= w_val)
      (Hw_val_lt : w_val < num_windows)
      (Hscalar_len : length scalar_ws = scalar_limbs)
      (Hval_unsigned :
        word.unsigned val_w =
        (let bit_offset := w_val * c in
         let limb := (bit_offset / 64)%Z in
         let shift := (bit_offset mod 64)%Z in
         let v1 := Z.shiftr
           (word.unsigned (nth (Z.to_nat limb) scalar_ws (word.of_Z 0)))
           shift in
         if Nat.ltb 64 (Z.to_nat (w_val * c mod 64) + Z.to_nat c)
         then
           (if Z.ltb limb 3
            then
              Z.lor v1
                (Z.shiftl
                   (word.unsigned (nth (Z.to_nat (limb + 1)) scalar_ws (word.of_Z 0)))
                   (64 - shift))
            else v1)
         else v1)) :
      word.unsigned (word.and val_w (word.of_Z (Z.ones c))) =
      get_window (List.map word.unsigned scalar_ws) (Z.to_nat w_val) (Z.to_nat c).
  Proof.
    unfold get_window.
    rewrite word.unsigned_and.
    rewrite !word.unsigned_of_Z.
    unfold word.wrap.
    assert (Hwidth_ge9 : (9 <= width)%Z) by (rewrite Hwidth64; lia).
    change (Z.ones c) with 511.
    assert (Hones_small : (511 mod 2^width = 511)%Z).
    { apply Z.mod_small; split; [lia|].
      apply Z.lt_le_trans with (2^9). { change (2^9) with 512; lia. }
      apply Z.pow_le_mono_r; lia. }
    rewrite Hones_small.
    assert (Hland_small : (Z.land (word.unsigned val_w) 511) mod 2^width =
                          Z.land (word.unsigned val_w) 511).
    { apply Z.mod_small; split.
      - apply Z.land_nonneg; left; apply (proj1 (word.unsigned_range val_w)).
      - apply Z.lt_le_trans with (2^9).
        { change 511 with (Z.ones 9).
          rewrite Z.land_ones by lia.
          apply Z.mod_pos_bound. lia. }
        apply Z.pow_le_mono_r; lia. }
    rewrite Hland_small.
    rewrite Hval_unsigned.
    cbv [c].
    assert (Hne_limb : forall limb : nat,
        nth_error (List.map word.unsigned scalar_ws) limb =
        if Nat.ltb limb (length scalar_ws)
        then Some (word.unsigned (nth limb scalar_ws (word.of_Z 0)))
        else None).
    { intros idx. destruct (Nat.ltb_spec idx (length scalar_ws)).
      - rewrite nth_error_map.
        rewrite (@nth_error_nth' _ scalar_ws idx (word.of_Z 0) H).
        reflexivity.
      - rewrite nth_error_map.
        apply nth_error_None in H. rewrite H. reflexivity. }
    set (limb := (w_val * 9 / 64)%Z).
    set (shift := (w_val * 9 mod 64)%Z).
    assert (Hlimb_bound : (0 <= limb < 4)%Z).
    { unfold limb. split; [apply Z_div_nonneg_nonneg; lia|].
      apply Z.div_lt_upper_bound; [lia|].
      cbv [num_windows] in Hw_val_lt. lia. }
    assert (Hlimb_in_bounds : (Z.to_nat limb < length scalar_ws)%nat).
    { rewrite Hscalar_len. unfold scalar_limbs.
      apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia. }
    assert (Hnat_lim : (Z.to_nat w_val * 9 / 64 = Z.to_nat limb)%nat).
    { unfold limb. rewrite Z2Nat.inj_div by lia.
      rewrite Z2Nat.inj_mul by lia. reflexivity. }
    assert (Hnat_sh : (Z.to_nat w_val * 9 mod 64 = Z.to_nat shift)%nat).
    { unfold shift. rewrite Z2Nat.inj_mod by lia.
      rewrite Z2Nat.inj_mul by lia. reflexivity. }
    change (Z.to_nat 9) with 9%nat.
    rewrite Hnat_lim, Hnat_sh.
    rewrite (Hne_limb (Z.to_nat limb)).
    rewrite (proj2 (Nat.ltb_lt _ _) Hlimb_in_bounds).
    assert (Hshift_nonneg : 0 <= shift) by (unfold shift; apply Z.mod_pos_bound; lia).
    rewrite Z2Nat.id; [|exact Hshift_nonneg].
    destruct (Bool.bool_dec (Nat.ltb 64 (Z.to_nat shift + 9)) true) as [Hctrue | Hcfalse].
    - rewrite Hctrue.
      apply Nat.ltb_lt in Hctrue as Hcross.
      assert (Hlim_le3 : limb <= 3) by lia.
      destruct (Z.ltb_spec limb 3) as [Hlim3 | Hlim3].
      + assert (Hlim1_in : (Z.to_nat limb + 1 < length scalar_ws)%nat).
        { rewrite Hscalar_len. apply Nat2Z.inj_lt.
          rewrite Nat2Z.inj_add. rewrite Z2Nat.id by lia. simpl. lia. }
        rewrite Z2Nat.inj_add by lia.
        change (Z.to_nat 1) with 1%nat.
        rewrite (Hne_limb ((Z.to_nat limb + 1)%nat)).
        rewrite (proj2 (Nat.ltb_lt _ _) Hlim1_in).
        assert (Hsh_le63 : (Z.to_nat shift <= 63)%nat).
        { apply Nat.lt_succ_r. apply Nat2Z.inj_lt.
          rewrite Z2Nat.id by exact Hshift_nonneg.
          unfold shift. apply Z.mod_pos_bound; lia. }
        rewrite Nat2Z.inj_sub by Lia.lia.
        rewrite Z2Nat.id; [reflexivity|exact Hshift_nonneg].
      + assert (Hlim1_oob : (length scalar_ws <= Z.to_nat limb + 1)%nat).
        { rewrite Hscalar_len. apply Nat2Z.inj_le.
          rewrite Nat2Z.inj_add. rewrite Z2Nat.id by lia. simpl. lia. }
        rewrite (Hne_limb ((Z.to_nat limb + 1)%nat)).
        rewrite (proj2 (Nat.ltb_nlt _ _) (proj2 (Nat.nlt_ge _ _) Hlim1_oob)).
        reflexivity.
    - apply Bool.not_true_iff_false in Hcfalse.
      rewrite Hcfalse. reflexivity.
  Qed.

  (** Given:
        - shift_w : word = word.and (w * c) 63         (bit shift in [0,63])
        - mask_w  : word = word.slu 1 c - 1            (low-c-bits mask)
        - val1_w  : word = word.sru scalar_limb shift_w
        - idx_w   : word = word.and val1_w mask_w
        - word.unsigned idx_w = 0
        - word.unsigned shift_w = w * c mod 64         (shift-amount bound)
        - word.unsigned (word.ltu 64 (shift_w + c)) = 0  (no cross-limb)
        - length scalars = scalar_limbs
        - 0 <= w < num_windows
      Conclude: [get_window (List.map unsigned scalars) w c = 0].

      Used to close the [idx = 0] branch of L3's distribute-loop body.  *)
  Lemma window_zero_from_idx_zero
      (w : Z) (scalars : list word)
      (shift_w mask_w val1_w idx_w : word)
      (Hw_lo : 0 <= w) (Hw_hi : w < num_windows)
      (Hscalar_len : length scalars = scalar_limbs)
      (Hshift_def : shift_w =
        word.and (word.mul (word.of_Z w : word) (word.of_Z c)) (word.of_Z 63))
      (Hmask_def : mask_w =
        word.sub (word.slu (word.of_Z 1 : word) (word.of_Z c)) (word.of_Z 1))
      (Hval1_def : val1_w =
        word.sru (nth (Z.to_nat (w * c / 64)) scalars (word.of_Z 0)) shift_w)
      (Hidx_def : idx_w = word.and val1_w mask_w)
      (Hidx_z : word.unsigned idx_w = 0)
      (Hshift_unsigned : word.unsigned shift_w = w * c mod 64)
      (Hno_cross : word.unsigned shift_w + c <= 64) :
      get_window (List.map word.unsigned scalars) (Z.to_nat w) (Z.to_nat c) = 0.
  Proof.
    (* Step 1: mask_w unfolds to word.of_Z (Z.ones c). *)
    assert (Hmask_eq : mask_w = word.of_Z (Z.ones c)).
    { rewrite Hmask_def. cbv [c]. change (Z.ones 9) with 511.
      ZnWords. }
    (* Step 2: val1_w matches the get_window_word_correct Hval_unsigned shape. *)
    assert (Hval1_unsigned : word.unsigned val1_w =
        (let bit_offset := w * c in
         let limb := (bit_offset / 64)%Z in
         let shift := (bit_offset mod 64)%Z in
         let v1 := Z.shiftr
           (word.unsigned (nth (Z.to_nat limb) scalars (word.of_Z 0)))
           shift in
         if Nat.ltb 64 (Z.to_nat (w * c mod 64) + Z.to_nat c)
         then
           (if Z.ltb limb 3
            then
              Z.lor v1
                (Z.shiftl
                   (word.unsigned (nth (Z.to_nat (limb + 1)) scalars (word.of_Z 0)))
                   (64 - shift))
            else v1)
         else v1)).
    { assert (Hcross_false :
          Nat.ltb 64 (Z.to_nat (w * c mod 64) + Z.to_nat c) = false).
      { apply Nat.ltb_ge.
        rewrite <- Hshift_unsigned.
        rewrite <- Z2Nat.inj_add by
          (try apply word.unsigned_range; cbv [c]; lia).
        apply Nat2Z.inj_le.
        rewrite Z2Nat.id by
          (pose proof (word.unsigned_range shift_w); cbv [c]; lia).
        change (Z.of_nat 64) with 64.
        exact Hno_cross. }
      rewrite Hcross_false.
      rewrite Hval1_def.
      rewrite word.unsigned_sru_nowrap
        by (rewrite Hshift_unsigned, Hwidth64; apply Z.mod_pos_bound; lia).
      rewrite Hshift_unsigned. reflexivity. }
    (* Step 3: apply get_window_word_correct. *)
    pose proof (get_window_word_correct scalars w val1_w
                  Hw_lo Hw_hi Hscalar_len Hval1_unsigned) as Hgw.
    (* Step 4: connect word.unsigned idx_w = word.unsigned (val1_w & (Z.ones c)). *)
    assert (Hidx_eq : idx_w = word.and val1_w (word.of_Z (Z.ones c))).
    { rewrite Hidx_def. rewrite Hmask_eq. reflexivity. }
    rewrite Hidx_eq in Hidx_z. rewrite Hgw in Hidx_z.
    exact Hidx_z.
  Qed.

  (** Bedrock2-form variant: [Hno_cross] here has the shape produced by
      [cmd.cond]'s FALSE branch, i.e.,
      [word.unsigned (if word.ltu 64 (shift_w + c) then 1 else 0) = 0]. *)
  Lemma window_zero_from_idx_zero_bedrock
      (w : Z) (scalars : list word)
      (shift_w mask_w val1_w idx_w : word)
      (Hw_lo : 0 <= w) (Hw_hi : w < num_windows)
      (Hscalar_len : length scalars = scalar_limbs)
      (Hshift_def : shift_w =
        word.and (word.mul (word.of_Z w : word) (word.of_Z c)) (word.of_Z 63))
      (Hmask_def : mask_w =
        word.sub (word.slu (word.of_Z 1 : word) (word.of_Z c)) (word.of_Z 1))
      (Hval1_def : val1_w =
        word.sru (nth (Z.to_nat (w * c / 64)) scalars (word.of_Z 0)) shift_w)
      (Hidx_def : idx_w = word.and val1_w mask_w)
      (Hidx_z : word.unsigned idx_w = 0)
      (Hshift_unsigned : word.unsigned shift_w = w * c mod 64)
      (Hno_cross :
         word.unsigned
           (if word.ltu (word.of_Z 64 : word) (word.add shift_w (word.of_Z c))
            then (word.of_Z 1 : word) else word.of_Z 0) = 0) :
      get_window (List.map word.unsigned scalars) (Z.to_nat w) (Z.to_nat c) = 0.
  Proof.
    assert (Hshift_small : word.unsigned shift_w < 64).
    { rewrite Hshift_unsigned. apply Z.mod_pos_bound; lia. }
    assert (Hno_cross_bound : word.unsigned shift_w + c <= 64).
    { destruct (word.ltu (word.of_Z 64 : word) (word.add shift_w (word.of_Z c))) eqn:Hltu.
      - rewrite word.unsigned_of_Z_nowrap in Hno_cross
          by (rewrite Hwidth64; lia). discriminate.
      - rewrite word.unsigned_ltu in Hltu.
        rewrite word.unsigned_of_Z_nowrap in Hltu by (rewrite Hwidth64; lia).
        rewrite word.unsigned_add_nowrap in Hltu.
        + rewrite word.unsigned_of_Z_nowrap in Hltu
            by (rewrite Hwidth64; cbv [c]; lia).
          apply Z.ltb_ge. exact Hltu.
        + rewrite word.unsigned_of_Z_nowrap
            by (rewrite Hwidth64; cbv [c]; lia).
          subst width. cbv [c]. lia. }
    exact (window_zero_from_idx_zero w scalars shift_w mask_w val1_w idx_w
             Hw_lo Hw_hi Hscalar_len Hshift_def Hmask_def Hval1_def Hidx_def
             Hidx_z Hshift_unsigned Hno_cross_bound).
  Qed.

End WindowBridge.
