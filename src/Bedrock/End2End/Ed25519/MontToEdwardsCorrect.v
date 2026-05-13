(** * MontToEdwardsCorrect — functional correctness of the
 *     Montgomery-u → Edwards-y compressed encoder.
 *
 *  Proves [mont_to_edwards_body] outputs the 32-byte LE
 *  packing of [(u - 1) · inv(u + 1) mod p], with bit 255 set to the
 *  caller-supplied sign bit.
 *
 *  Mirrors [Scalar25519FromWideCorrect.v]:  Section parameterised
 *  by [Fp25519_holds] and [Bytes32_holds] predicates plus 7 leaf
 *  [Hypothesis]es (one + add + sub + invert + mul + to_bytes +
 *  set_sign_bit) and 2 frame [Hypothesis]es.
 *
 *  We re-use the SHAPE of [fe25519_invert] as a single FFI leaf —
 *  the actual semantic content of [fe25519_invert] is verified in
 *  [Fe25519InvertCorrect.v].  The two correctness theorems compose
 *  trivially: the leaf-correctness [Hypothesis] [invert_correct]
 *  below states exactly what [fe25519_invert_correct] establishes.
 *
 *  Total LoC: ~360.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.MontToEdwardsBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters                                            *)
(* ================================================================ *)

Section MontToEdwardsCorrect.

  (** The base field modulus [p = 2^255 - 19]. *)
  Local Notation p := Curve25519.p.

  Variable Fp25519_holds : rust_state_ed -> String.string -> F p -> Prop.
  Variable Bytes32_holds : rust_state_ed -> String.string ->
                           list Byte.byte -> Prop.

  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec :=
    (rust_exec_ed callee_post callee_post_n function_table).

  (** Combined frame: an Fp value or a 32-byte value at [y] survive
      a leaf call whose dest [exclude] is distinct from [y]. *)
  Definition leaf_frame (rs1 rs2 : rust_state_ed) (exclude : String.string) :
      Prop :=
    (forall y v, y <> exclude -> Fp25519_holds rs1 y v ->
                 Fp25519_holds rs2 y v) /\
    (forall y v, y <> exclude -> Bytes32_holds rs1 y v ->
                 Bytes32_holds rs2 y v).

  (* ================================================================ *)
  (* §2.  Leaf-algebra hypotheses                                      *)
  (* ================================================================ *)

  Hypothesis one_correct :
    forall (dest : located_ed) (rs1 rs2 : rust_state_ed),
      dest.(loc_type) = TFp25519 ->
      Hexec (REdCall "fe25519_one" dest []) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.one) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  Hypothesis add_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      b.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Fp25519_holds rs1 b.(loc_var) xb ->
      Hexec (REdCall "fe25519_add" dest [a; b]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.add xa xb) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  Hypothesis sub_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      b.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Fp25519_holds rs1 b.(loc_var) xb ->
      Hexec (REdCall "fe25519_sub" dest [a; b]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.sub xa xb) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  Hypothesis mul_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      b.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Fp25519_holds rs1 b.(loc_var) xb ->
      Hexec (REdCall "fe25519_mul" dest [a; b]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xb) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  (** [invert_correct] supplies the verified [fe25519_invert]
      result.  The hypothesis matches what
      [Fe25519InvertCorrect.fe25519_invert_correct] proves modulo
      the wrapping in [REdCall "fe25519_invert"]: namely, that
      after the call, [dest] holds [src^(p-2)].  We only require
      the [src ≠ 0] side condition here for the math to be
      *meaningful* (downstream consumer); the leaf itself returns
      [x^(p-2)] regardless of whether [x = 0]. *)
  Hypothesis invert_correct :
    forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (x : F p),
      dest.(loc_type) = TFp25519 ->
      src.(loc_type) = TFp25519 ->
      dest.(loc_var) <> src.(loc_var) ->
      Fp25519_holds rs1 src.(loc_var) x ->
      Hexec (REdCall "fe25519_invert" dest [src]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.pow x (Z.to_N (p - 2))) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  (** [to_bytes] correctness: the 32-byte LE pack of [x] is
      [le_split 32 (F.to_Z x)] in the byte slot.  We keep the
      witness abstract: any byte list [bs] s.t.
      [encode_y_witness x bs] (defined here as the pack equality)
      is OK.  This keeps the bridge layer free to instantiate with
      [LittleEndianList.le_split]. *)
  Variable encode_y : F p -> list Byte.byte.
  Hypothesis encode_y_length :
    forall x : F p, length (encode_y x) = 32%nat.

  Hypothesis to_bytes_correct :
    forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (x : F p),
      dest.(loc_type) = TBytes 32 ->
      src.(loc_type) = TFp25519 ->
      Fp25519_holds rs1 src.(loc_var) x ->
      Hexec (REdCall "fe25519_to_bytes" dest [src]) rs1 rs2 ->
      Bytes32_holds rs2 dest.(loc_var) (encode_y x) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  (** [set_sign_bit]: takes a 32-byte slot [src] of bytes [bs] and
      a 32-byte slot [sgn] whose byte-0 holds [b ∈ {0,1}]; produces
      the byte list [set_sign_bit bs b] = first 31 bytes of [bs],
      then the 32nd byte's low 7 bits OR-ed with [b << 7].

      We expose this as an abstract function [set_sign_bit_bytes]
      with the obvious specification — the concrete pack/unpack is
      identical to [CompressVerified.set_sign_bit].  The bridge
      layer instantiates it. *)
  Variable set_sign_bit_bytes :
    list Byte.byte (* y_bytes *) ->
    list Byte.byte (* sign-input bytes: byte 0 holds 0/1 *) ->
    list Byte.byte.

  Hypothesis set_sign_bit_correct :
    forall (dest a sgn : located_ed) (rs1 rs2 : rust_state_ed)
           (bs_y bs_sgn : list Byte.byte),
      dest.(loc_type) = TBytes 32 ->
      a.(loc_type) = TBytes 32 ->
      sgn.(loc_type) = TBytes 32 ->
      Bytes32_holds rs1 a.(loc_var) bs_y ->
      Bytes32_holds rs1 sgn.(loc_var) bs_sgn ->
      Hexec (REdCall "bytes_set_sign_bit" dest [a; sgn]) rs1 rs2 ->
      Bytes32_holds rs2 dest.(loc_var) (set_sign_bit_bytes bs_y bs_sgn) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  (** [REdLetZero] preserves both slot predicates at a distinct key. *)
  Hypothesis let_zero_preserves_holds_Fp :
    forall (rs : rust_state_ed) (x : String.string) (t : tower_type_ed)
           (v : rust_val_ed t) (y : String.string) (vp : F p),
      y <> x ->
      Fp25519_holds rs y vp ->
      Fp25519_holds (rs_set_tower_ed rs x (exist_tval_ed t v)) y vp.

  Hypothesis let_zero_preserves_holds_B32 :
    forall (rs : rust_state_ed) (x : String.string) (t : tower_type_ed)
           (v : rust_val_ed t) (y : String.string)
           (vp : list Byte.byte),
      y <> x ->
      Bytes32_holds rs y vp ->
      Bytes32_holds (rs_set_tower_ed rs x (exist_tval_ed t v)) y vp.

  (* ================================================================ *)
  (* §3.  Convenience lemmas                                           *)
  (* ================================================================ *)

  Lemma leaf_frame_refl rs x : leaf_frame rs rs x.
  Proof. split; intros y v _ H; exact H. Qed.

  Lemma seq_inv c1 c2 rs1 rs3 :
    Hexec (REdSeq c1 c2) rs1 rs3 ->
    exists rs2, Hexec c1 rs1 rs2 /\ Hexec c2 rs2 rs3.
  Proof. intros Hseq. inversion Hseq; subst. eexists; eauto. Qed.

  Lemma letzero_inv x t c rs1 rs2 :
    Hexec (REdLetZero x t c) rs1 rs2 ->
    exists v : rust_val_ed t,
      well_formed_ed v /\
      Hexec c (rs_set_tower_ed rs1 x (exist_tval_ed t v)) rs2.
  Proof. intros H. inversion H; subst. eexists; split; eauto. Qed.

  Lemma leaf_frame_fp rs1 rs2 e y v :
    leaf_frame rs1 rs2 e -> y <> e -> Fp25519_holds rs1 y v ->
    Fp25519_holds rs2 y v.
  Proof. intros [HfpL _]; apply HfpL. Qed.

  Lemma leaf_frame_b32 rs1 rs2 e y v :
    leaf_frame rs1 rs2 e -> y <> e -> Bytes32_holds rs1 y v ->
    Bytes32_holds rs2 y v.
  Proof. intros [_ Hb32]; apply Hb32. Qed.

  (* ================================================================ *)
  (* §4.  Top-level theorem                                            *)
  (* ================================================================ *)

  Definition mte_scratch_names : list String.string :=
    [ "one_v"; "u_plus_1"; "u_minus_1"; "inv_v"; "y_v"; "y_bytes" ].

  Definition not_in_mte_scratch (s : String.string) : Prop :=
    ~ List.In s mte_scratch_names.

  Theorem mont_to_edwards_correct :
    forall (rs1 rs2 : rust_state_ed)
           (u_loc sign_loc dest : located_ed)
           (u : F p) (bs_sgn : list Byte.byte),
      u_loc.(loc_type) = TFp25519 ->
      sign_loc.(loc_type) = TBytes 32 ->
      dest.(loc_type) = TBytes 32 ->
      not_in_mte_scratch u_loc.(loc_var) ->
      not_in_mte_scratch sign_loc.(loc_var) ->
      not_in_mte_scratch dest.(loc_var) ->
      u_loc.(loc_var) <> sign_loc.(loc_var) ->
      dest.(loc_var) <> sign_loc.(loc_var) ->
      Fp25519_holds rs1 u_loc.(loc_var) u ->
      Bytes32_holds rs1 sign_loc.(loc_var) bs_sgn ->
      Hexec (mont_to_edwards_body dest [u_loc; sign_loc]) rs1 rs2 ->
      Bytes32_holds rs2 dest.(loc_var)
        (set_sign_bit_bytes
          (encode_y (F.mul (F.sub u F.one)
                           (F.pow (F.add u F.one) (Z.to_N (p - 2)))))
          bs_sgn).
  Proof.
    intros rs1 rs2 u_loc sign_loc dest u bs_sgn
           Hut Hst Hdt Huf Hsf Hdf Husn Hdsn Hu_v Hsgn_v Hexec_n.
    cbn [mont_to_edwards_body seqN] in Hexec_n.

    (* Extract disequations from [not_in_mte_scratch]. *)
    unfold not_in_mte_scratch, mte_scratch_names in Huf, Hsf, Hdf.
    assert (Hu_one  : u_loc.(loc_var) <> "one_v")
      by (intro Heq; apply Huf; rewrite Heq; cbn; tauto).
    assert (Hu_up   : u_loc.(loc_var) <> "u_plus_1")
      by (intro Heq; apply Huf; rewrite Heq; cbn; tauto).
    assert (Hu_um   : u_loc.(loc_var) <> "u_minus_1")
      by (intro Heq; apply Huf; rewrite Heq; cbn; tauto).
    assert (Hu_inv  : u_loc.(loc_var) <> "inv_v")
      by (intro Heq; apply Huf; rewrite Heq; cbn; tauto).
    assert (Hu_yv   : u_loc.(loc_var) <> "y_v")
      by (intro Heq; apply Huf; rewrite Heq; cbn; tauto).
    assert (Hu_yb   : u_loc.(loc_var) <> "y_bytes")
      by (intro Heq; apply Huf; rewrite Heq; cbn; tauto).
    assert (Hs_one  : sign_loc.(loc_var) <> "one_v")
      by (intro Heq; apply Hsf; rewrite Heq; cbn; tauto).
    assert (Hs_up   : sign_loc.(loc_var) <> "u_plus_1")
      by (intro Heq; apply Hsf; rewrite Heq; cbn; tauto).
    assert (Hs_um   : sign_loc.(loc_var) <> "u_minus_1")
      by (intro Heq; apply Hsf; rewrite Heq; cbn; tauto).
    assert (Hs_inv  : sign_loc.(loc_var) <> "inv_v")
      by (intro Heq; apply Hsf; rewrite Heq; cbn; tauto).
    assert (Hs_yv   : sign_loc.(loc_var) <> "y_v")
      by (intro Heq; apply Hsf; rewrite Heq; cbn; tauto).
    assert (Hs_yb   : sign_loc.(loc_var) <> "y_bytes")
      by (intro Heq; apply Hsf; rewrite Heq; cbn; tauto).
    assert (Hd_one  : dest.(loc_var) <> "one_v")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_up   : dest.(loc_var) <> "u_plus_1")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_um   : dest.(loc_var) <> "u_minus_1")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_inv  : dest.(loc_var) <> "inv_v")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_yv   : dest.(loc_var) <> "y_v")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_yb   : dest.(loc_var) <> "y_bytes")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).

    (* =================================================== *)
    (* Peel the 6 REdLetZero introductions.                *)
    (* =================================================== *)

    (* 1: one_v *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_a := rs_set_tower_ed rs1 "one_v" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hu_a : Fp25519_holds rs_a u_loc.(loc_var) u)
      by (unfold rs_a; apply let_zero_preserves_holds_Fp; auto).
    assert (Hs_a : Bytes32_holds rs_a sign_loc.(loc_var) bs_sgn)
      by (unfold rs_a; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_a. clear rs1 Hu_v Hsgn_v v0. rename Hexec_n' into Hexec_n.

    (* 2: u_plus_1 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_b := rs_set_tower_ed rs_a "u_plus_1" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hu_b : Fp25519_holds rs_b u_loc.(loc_var) u)
      by (unfold rs_b; apply let_zero_preserves_holds_Fp; auto).
    assert (Hs_b : Bytes32_holds rs_b sign_loc.(loc_var) bs_sgn)
      by (unfold rs_b; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_b. clear rs_a Hu_a Hs_a v0. rename Hexec_n' into Hexec_n.

    (* 3: u_minus_1 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_c := rs_set_tower_ed rs_b "u_minus_1" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hu_c : Fp25519_holds rs_c u_loc.(loc_var) u)
      by (unfold rs_c; apply let_zero_preserves_holds_Fp; auto).
    assert (Hs_c : Bytes32_holds rs_c sign_loc.(loc_var) bs_sgn)
      by (unfold rs_c; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_c. clear rs_b Hu_b Hs_b v0. rename Hexec_n' into Hexec_n.

    (* 4: inv_v *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_d := rs_set_tower_ed rs_c "inv_v" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hu_d : Fp25519_holds rs_d u_loc.(loc_var) u)
      by (unfold rs_d; apply let_zero_preserves_holds_Fp; auto).
    assert (Hs_d : Bytes32_holds rs_d sign_loc.(loc_var) bs_sgn)
      by (unfold rs_d; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_d. clear rs_c Hu_c Hs_c v0. rename Hexec_n' into Hexec_n.

    (* 5: y_v *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_e := rs_set_tower_ed rs_d "y_v" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hu_e : Fp25519_holds rs_e u_loc.(loc_var) u)
      by (unfold rs_e; apply let_zero_preserves_holds_Fp; auto).
    assert (Hs_e : Bytes32_holds rs_e sign_loc.(loc_var) bs_sgn)
      by (unfold rs_e; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_e. clear rs_d Hu_d Hs_d v0. rename Hexec_n' into Hexec_n.

    (* 6: y_bytes *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_f := rs_set_tower_ed rs_e "y_bytes" (exist_tval_ed (TBytes 32) v0)) in *.
    assert (Hu_f : Fp25519_holds rs_f u_loc.(loc_var) u)
      by (unfold rs_f; apply let_zero_preserves_holds_Fp; auto).
    assert (Hs_f : Bytes32_holds rs_f sign_loc.(loc_var) bs_sgn)
      by (unfold rs_f; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_f. clear rs_e Hu_e Hs_e v0. rename Hexec_n' into Hexec_n.

    (* =================================================== *)
    (* Walk the 7-command seqN.                            *)
    (* =================================================== *)

    (* --- Step 1: one_v := 1 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs01 [H1 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (one_correct (LFp "one_v") rs_f rs01 eq_refl H1)
      as [Hone_v Hfr_1].
    cbn [LFp loc_var loc_type] in Hone_v.
    assert (Hu_01 : Fp25519_holds rs01 u_loc.(loc_var) u)
      by (eapply leaf_frame_fp; [exact Hfr_1|exact Hu_one|exact Hu_f]).
    assert (Hs_01 : Bytes32_holds rs01 sign_loc.(loc_var) bs_sgn)
      by (eapply leaf_frame_b32; [exact Hfr_1|exact Hs_one|exact Hs_f]).
    clear Hu_f Hs_f.

    (* --- Step 2: u_plus_1 := u + 1 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs02 [H2 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    assert (Hne_up_u : (LFp "u_plus_1").(loc_var) <> u_loc.(loc_var))
      by (cbn; intro Heq; apply Hu_up; symmetry; exact Heq).
    pose proof (add_correct (LFp "u_plus_1") u_loc (LFp "one_v")
                rs01 rs02 u F.one
                eq_refl Hut eq_refl
                Hne_up_u (ltac:(cbn; discriminate))
                Hu_01 Hone_v H2) as [Hup_v Hfr_2].
    cbn [LFp loc_var loc_type] in Hup_v.
    assert (Hu_02 : Fp25519_holds rs02 u_loc.(loc_var) u)
      by (eapply leaf_frame_fp; [exact Hfr_2|exact Hu_up|exact Hu_01]).
    assert (Hs_02 : Bytes32_holds rs02 sign_loc.(loc_var) bs_sgn)
      by (eapply leaf_frame_b32; [exact Hfr_2|exact Hs_up|exact Hs_01]).
    assert (Hone_02 : Fp25519_holds rs02 "one_v" F.one)
      by (eapply leaf_frame_fp; [exact Hfr_2|discriminate|exact Hone_v]).
    clear Hu_01 Hs_01 Hone_v.

    (* --- Step 3: u_minus_1 := u - 1 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs03 [H3 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    assert (Hne_um_u : (LFp "u_minus_1").(loc_var) <> u_loc.(loc_var))
      by (cbn; intro Heq; apply Hu_um; symmetry; exact Heq).
    pose proof (sub_correct (LFp "u_minus_1") u_loc (LFp "one_v")
                rs02 rs03 u F.one
                eq_refl Hut eq_refl
                Hne_um_u (ltac:(cbn; discriminate))
                Hu_02 Hone_02 H3) as [Hum_v Hfr_3].
    cbn [LFp loc_var loc_type] in Hum_v.
    assert (Hu_03 : Fp25519_holds rs03 u_loc.(loc_var) u)
      by (eapply leaf_frame_fp; [exact Hfr_3|exact Hu_um|exact Hu_02]).
    assert (Hs_03 : Bytes32_holds rs03 sign_loc.(loc_var) bs_sgn)
      by (eapply leaf_frame_b32; [exact Hfr_3|exact Hs_um|exact Hs_02]).
    assert (Hup_03 : Fp25519_holds rs03 "u_plus_1" (F.add u F.one))
      by (eapply leaf_frame_fp; [exact Hfr_3|discriminate|exact Hup_v]).
    clear Hu_02 Hs_02 Hone_02 Hup_v.

    (* --- Step 4: inv_v := invert(u_plus_1) = (u+1)^(p-2) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs04 [H4 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (invert_correct (LFp "inv_v") (LFp "u_plus_1")
                rs03 rs04 (F.add u F.one)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Hup_03 H4) as [Hinv_v Hfr_4].
    cbn [LFp loc_var loc_type] in Hinv_v.
    assert (Hu_04 : Fp25519_holds rs04 u_loc.(loc_var) u)
      by (eapply leaf_frame_fp; [exact Hfr_4|exact Hu_inv|exact Hu_03]).
    assert (Hs_04 : Bytes32_holds rs04 sign_loc.(loc_var) bs_sgn)
      by (eapply leaf_frame_b32; [exact Hfr_4|exact Hs_inv|exact Hs_03]).
    assert (Hum_04 : Fp25519_holds rs04 "u_minus_1" (F.sub u F.one))
      by (eapply leaf_frame_fp; [exact Hfr_4|discriminate|exact Hum_v]).
    clear Hu_03 Hs_03 Hum_v Hup_03.

    (* --- Step 5: y_v := u_minus_1 · inv_v = (u-1)(u+1)^(p-2) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs05 [H5 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "y_v") (LFp "u_minus_1") (LFp "inv_v")
                rs04 rs05 (F.sub u F.one) (F.pow (F.add u F.one) (Z.to_N (p - 2)))
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Hum_04 Hinv_v H5) as [Hyv_v Hfr_5].
    cbn [LFp loc_var loc_type] in Hyv_v.
    assert (Hu_05 : Fp25519_holds rs05 u_loc.(loc_var) u)
      by (eapply leaf_frame_fp; [exact Hfr_5|exact Hu_yv|exact Hu_04]).
    assert (Hs_05 : Bytes32_holds rs05 sign_loc.(loc_var) bs_sgn)
      by (eapply leaf_frame_b32; [exact Hfr_5|exact Hs_yv|exact Hs_04]).
    clear Hu_04 Hs_04 Hum_04 Hinv_v.

    (* --- Step 6: y_bytes := to_bytes(y_v) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs06 [H6 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (to_bytes_correct (LBytes32 "y_bytes") (LFp "y_v")
                rs05 rs06
                (F.mul (F.sub u F.one) (F.pow (F.add u F.one) (Z.to_N (p - 2))))
                eq_refl eq_refl Hyv_v H6) as [Hyb_v Hfr_6].
    cbn [LBytes32 LFp loc_var loc_type] in Hyb_v.
    assert (Hs_06 : Bytes32_holds rs06 sign_loc.(loc_var) bs_sgn)
      by (eapply leaf_frame_b32; [exact Hfr_6|exact Hs_yb|exact Hs_05]).
    clear Hu_05 Hs_05 Hyv_v.

    (* --- Step 7 (final): dest := set_sign_bit(y_bytes, sign_loc) --- *)
    cbn [seqN] in Hexec_n.
    assert (Hne_d_yb : dest.(loc_var) <> (LBytes32 "y_bytes").(loc_var))
      by (cbn; exact Hd_yb).
    assert (Hne_d_sgn : dest.(loc_var) <> sign_loc.(loc_var)) by exact Hdsn.
    pose proof (set_sign_bit_correct dest (LBytes32 "y_bytes") sign_loc
                rs06 rs2
                (encode_y (F.mul (F.sub u F.one)
                                 (F.pow (F.add u F.one) (Z.to_N (p - 2)))))
                bs_sgn
                Hdt eq_refl Hst Hyb_v Hs_06 Hexec_n) as [Hdest_v _].
    exact Hdest_v.
  Qed.

End MontToEdwardsCorrect.

(* Sanity check: list assumptions. *)
Print Assumptions mont_to_edwards_correct.
