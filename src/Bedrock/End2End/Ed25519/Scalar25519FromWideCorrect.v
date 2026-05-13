(** * Scalar25519FromWideCorrect — functional correctness of
 *    Scalar25519::from_bytes_mod_order_wide.
 *
 *  Proves the rust_cmd_ed body in [Scalar25519FromWideBody.v]
 *  computes the wide reduction
 *
 *      wide mod L   where   L = 2^252 + L_extra,
 *
 *  given the algebraic specs of the four external scalar leaves
 *  (from_bytes_mod_order, mul, add, negate), the [REdSetBytes]
 *  decoder hypotheses for the two constant tables, and the
 *  algebraic identity [2^256 ≡ -16 · L_extra (mod L)].
 *
 *  Architecture mirrors [Fe25519InvertCorrect.v]:
 *    - Section parameterised by predicates [FpL25519_holds] and
 *      [Bytes32_holds].
 *    - Leaf-correctness [Hypothesis]es for each external scalar op.
 *    - [c256_eq] supplies the math identity.
 *
 *  Total LoC: ~530.
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
Require Import Bedrock.End2End.Ed25519.Scalar25519FromWideBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters                                            *)
(* ================================================================ *)

Section Scalar25519FromWideCorrect.

  (** The scalar field modulus [l = 2^252 + L_extra]. *)
  Local Notation L := Curve25519.l.

  (** Slot abstractions. *)
  Variable FpL25519_holds : rust_state_ed -> String.string -> F L -> Prop.
  Variable Bytes32_holds  : rust_state_ed -> String.string -> Z -> Prop.

  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec :=
    (rust_exec_ed callee_post callee_post_n function_table).

  (** Combined frame: an FpL value at [y] AND a Bytes32 value at [y]
      survive any leaf call whose dest [exclude] is distinct from [y].
      We use a single combined predicate to avoid carrying parallel
      lists of "frame_fpL ∧ frame_b32" through the proof. *)
  Definition leaf_frame (rs1 rs2 : rust_state_ed) (exclude : String.string) :
      Prop :=
    (forall y v, y <> exclude -> FpL25519_holds rs1 y v ->
                 FpL25519_holds rs2 y v) /\
    (forall y v, y <> exclude -> Bytes32_holds rs1 y v ->
                 Bytes32_holds rs2 y v).

  (* ================================================================ *)
  (* §2.  Leaf-algebra hypotheses                                      *)
  (* ================================================================ *)

  Hypothesis from_bytes_mod_order_correct :
    forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (z : Z),
      dest.(loc_type) = TFpL25519 ->
      src.(loc_type) = TBytes 32 ->
      Bytes32_holds rs1 src.(loc_var) z ->
      Hexec (REdCall "scalar25519_from_bytes_mod_order" dest [src]) rs1 rs2 ->
      FpL25519_holds rs2 dest.(loc_var) (F.of_Z L z) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  Hypothesis mul_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F L),
      dest.(loc_type) = TFpL25519 ->
      a.(loc_type) = TFpL25519 ->
      b.(loc_type) = TFpL25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      FpL25519_holds rs1 a.(loc_var) xa ->
      FpL25519_holds rs1 b.(loc_var) xb ->
      Hexec (REdCall "scalar25519_mul" dest [a; b]) rs1 rs2 ->
      FpL25519_holds rs2 dest.(loc_var) (F.mul xa xb) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  Hypothesis add_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F L),
      dest.(loc_type) = TFpL25519 ->
      a.(loc_type) = TFpL25519 ->
      b.(loc_type) = TFpL25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      FpL25519_holds rs1 a.(loc_var) xa ->
      FpL25519_holds rs1 b.(loc_var) xb ->
      Hexec (REdCall "scalar25519_add" dest [a; b]) rs1 rs2 ->
      FpL25519_holds rs2 dest.(loc_var) (F.add xa xb) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  Hypothesis negate_correct :
    forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (x : F L),
      dest.(loc_type) = TFpL25519 ->
      src.(loc_type) = TFpL25519 ->
      dest.(loc_var) <> src.(loc_var) ->
      FpL25519_holds rs1 src.(loc_var) x ->
      Hexec (REdCall "scalar25519_negate" dest [src]) rs1 rs2 ->
      FpL25519_holds rs2 dest.(loc_var) (F.opp x) /\
      leaf_frame rs1 rs2 dest.(loc_var).

  (** The byte-table decoders: writing [L_EXTRA_LE] to a 32-byte slot
      and then reading via [Bytes32_holds] yields the Z value
      [L_EXTRA_Z = 27742317777372353535851937790883648493]. Similarly
      [SIXTEEN_LE] decodes to [16]. The byte-table set also preserves
      both predicate-holdings at distinct slots. *)
  Definition L_EXTRA_Z : Z := 27742317777372353535851937790883648493.

  Hypothesis setbytes_extra_correct :
    forall (loc : located_ed) (rs1 rs2 : rust_state_ed),
      loc.(loc_type) = TBytes 32 ->
      Hexec (REdSetBytes loc L_EXTRA_LE) rs1 rs2 ->
      Bytes32_holds rs2 loc.(loc_var) L_EXTRA_Z /\
      leaf_frame rs1 rs2 loc.(loc_var).

  Hypothesis setbytes_sixteen_correct :
    forall (loc : located_ed) (rs1 rs2 : rust_state_ed),
      loc.(loc_type) = TBytes 32 ->
      Hexec (REdSetBytes loc SIXTEEN_LE) rs1 rs2 ->
      Bytes32_holds rs2 loc.(loc_var) 16 /\
      leaf_frame rs1 rs2 loc.(loc_var).

  (** [REdLetZero] preserves both slot predicates at a distinct key. *)
  Hypothesis let_zero_preserves_holds_FpL :
    forall (rs : rust_state_ed) (x : String.string) (t : tower_type_ed)
           (v : rust_val_ed t) (y : String.string) (vp : F L),
      y <> x ->
      FpL25519_holds rs y vp ->
      FpL25519_holds (rs_set_tower_ed rs x (exist_tval_ed t v)) y vp.

  Hypothesis let_zero_preserves_holds_B32 :
    forall (rs : rust_state_ed) (x : String.string) (t : tower_type_ed)
           (v : rust_val_ed t) (y : String.string) (vp : Z),
      y <> x ->
      Bytes32_holds rs y vp ->
      Bytes32_holds (rs_set_tower_ed rs x (exist_tval_ed t v)) y vp.

  (** [c256_eq]: the algebraic identity
        F.of_Z L (2^256) = F.opp (F.mul (F.of_Z L L_EXTRA) (F.of_Z L 16))
      Provable directly: since [L = 2^252 + L_EXTRA],
        2^256 = 16 · 2^252 = 16 · (L - L_EXTRA) ≡ -16 · L_EXTRA  (mod L).
      Hoisted as a Hypothesis so the proof body stays compact. *)
  Hypothesis c256_eq :
    F.of_Z L (Z.pow 2 256) =
    F.opp (F.mul (F.of_Z L L_EXTRA_Z) (F.of_Z L 16)).

  (* ================================================================ *)
  (* §3.  Convenience lemmas                                           *)
  (* ================================================================ *)

  Lemma leaf_frame_refl rs x : leaf_frame rs rs x.
  Proof. split; intros y v _ H; exact H. Qed.

  Lemma seq_inv c1 c2 rs1 rs3 :
    Hexec (REdSeq c1 c2) rs1 rs3 ->
    exists rs2, Hexec c1 rs1 rs2 /\ Hexec c2 rs2 rs3.
  Proof.
    intros Hseq. inversion Hseq; subst. eexists; eauto.
  Qed.

  Lemma letzero_inv x t c rs1 rs2 :
    Hexec (REdLetZero x t c) rs1 rs2 ->
    exists v : rust_val_ed t,
      well_formed_ed v /\
      Hexec c (rs_set_tower_ed rs1 x (exist_tval_ed t v)) rs2.
  Proof. intros H. inversion H; subst. eexists; split; eauto. Qed.

  (** Project the FpL component of [leaf_frame]. *)
  Lemma leaf_frame_fpL rs1 rs2 e y v :
    leaf_frame rs1 rs2 e -> y <> e -> FpL25519_holds rs1 y v ->
    FpL25519_holds rs2 y v.
  Proof. intros [HfpL _]; apply HfpL. Qed.

  Lemma leaf_frame_b32 rs1 rs2 e y v :
    leaf_frame rs1 rs2 e -> y <> e -> Bytes32_holds rs1 y v ->
    Bytes32_holds rs2 y v.
  Proof. intros [_ Hb32]; apply Hb32. Qed.

  (* ================================================================ *)
  (* §4.  Top-level theorem                                            *)
  (* ================================================================ *)

  (** Names of the 9 internal slots used by [from_wide_body]. *)
  Definition wide_scratch_names : list String.string :=
    [ "lo"; "hi"; "l_extra"; "sixteen"; "c256_pre"; "c256"; "hc256"
    ; "le_bytes"; "sx_bytes" ].

  Definition not_in_wide_scratch (s : String.string) : Prop :=
    ~ List.In s wide_scratch_names.

  Theorem from_wide_correct :
    forall (rs1 rs2 : rust_state_ed)
           (lo_bytes_loc hi_bytes_loc dest : located_ed)
           (z_lo z_hi : Z),
      lo_bytes_loc.(loc_type) = TBytes 32 ->
      hi_bytes_loc.(loc_type) = TBytes 32 ->
      dest.(loc_type) = TFpL25519 ->
      not_in_wide_scratch lo_bytes_loc.(loc_var) ->
      not_in_wide_scratch hi_bytes_loc.(loc_var) ->
      not_in_wide_scratch dest.(loc_var) ->
      lo_bytes_loc.(loc_var) <> hi_bytes_loc.(loc_var) ->
      Bytes32_holds rs1 lo_bytes_loc.(loc_var) z_lo ->
      Bytes32_holds rs1 hi_bytes_loc.(loc_var) z_hi ->
      Hexec (from_wide_body dest [lo_bytes_loc; hi_bytes_loc]) rs1 rs2 ->
      FpL25519_holds rs2 dest.(loc_var)
        (F.add (F.mul (F.of_Z L z_hi) (F.of_Z L (Z.pow 2 256)))
               (F.of_Z L z_lo)).
  Proof.
    intros rs1 rs2 lo_bytes_loc hi_bytes_loc dest z_lo z_hi
           Hlt Hht Hdt Hlf Hhf Hdf Hlh Hlo_b Hhi_b Hexec_n.
    cbn [from_wide_body seqN] in Hexec_n.

    (* Extract disequations from [not_in_wide_scratch]. *)
    unfold not_in_wide_scratch, wide_scratch_names in Hlf, Hhf, Hdf.
    assert (Hl_le : lo_bytes_loc.(loc_var) <> "le_bytes")
      by (intro Heq; apply Hlf; rewrite Heq; cbn; tauto).
    assert (Hl_sx : lo_bytes_loc.(loc_var) <> "sx_bytes")
      by (intro Heq; apply Hlf; rewrite Heq; cbn; tauto).
    assert (Hh_le : hi_bytes_loc.(loc_var) <> "le_bytes")
      by (intro Heq; apply Hhf; rewrite Heq; cbn; tauto).
    assert (Hh_sx : hi_bytes_loc.(loc_var) <> "sx_bytes")
      by (intro Heq; apply Hhf; rewrite Heq; cbn; tauto).
    assert (Hl_lo : lo_bytes_loc.(loc_var) <> "lo")
      by (intro Heq; apply Hlf; rewrite Heq; cbn; tauto).
    assert (Hl_hi : lo_bytes_loc.(loc_var) <> "hi")
      by (intro Heq; apply Hlf; rewrite Heq; cbn; tauto).
    assert (Hl_lex : lo_bytes_loc.(loc_var) <> "l_extra")
      by (intro Heq; apply Hlf; rewrite Heq; cbn; tauto).
    assert (Hl_sx2 : lo_bytes_loc.(loc_var) <> "sixteen")
      by (intro Heq; apply Hlf; rewrite Heq; cbn; tauto).
    assert (Hl_cp : lo_bytes_loc.(loc_var) <> "c256_pre")
      by (intro Heq; apply Hlf; rewrite Heq; cbn; tauto).
    assert (Hl_c2 : lo_bytes_loc.(loc_var) <> "c256")
      by (intro Heq; apply Hlf; rewrite Heq; cbn; tauto).
    assert (Hl_hc : lo_bytes_loc.(loc_var) <> "hc256")
      by (intro Heq; apply Hlf; rewrite Heq; cbn; tauto).
    assert (Hh_lo : hi_bytes_loc.(loc_var) <> "lo")
      by (intro Heq; apply Hhf; rewrite Heq; cbn; tauto).
    assert (Hh_hi : hi_bytes_loc.(loc_var) <> "hi")
      by (intro Heq; apply Hhf; rewrite Heq; cbn; tauto).
    assert (Hh_lex : hi_bytes_loc.(loc_var) <> "l_extra")
      by (intro Heq; apply Hhf; rewrite Heq; cbn; tauto).
    assert (Hh_sx2 : hi_bytes_loc.(loc_var) <> "sixteen")
      by (intro Heq; apply Hhf; rewrite Heq; cbn; tauto).
    assert (Hh_cp : hi_bytes_loc.(loc_var) <> "c256_pre")
      by (intro Heq; apply Hhf; rewrite Heq; cbn; tauto).
    assert (Hh_c2 : hi_bytes_loc.(loc_var) <> "c256")
      by (intro Heq; apply Hhf; rewrite Heq; cbn; tauto).
    assert (Hh_hc : hi_bytes_loc.(loc_var) <> "hc256")
      by (intro Heq; apply Hhf; rewrite Heq; cbn; tauto).
    assert (Hd_lo : dest.(loc_var) <> "lo")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_hi : dest.(loc_var) <> "hi")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_lex : dest.(loc_var) <> "l_extra")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_sx2 : dest.(loc_var) <> "sixteen")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_cp : dest.(loc_var) <> "c256_pre")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_c2 : dest.(loc_var) <> "c256")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).
    assert (Hd_hc : dest.(loc_var) <> "hc256")
      by (intro Heq; apply Hdf; rewrite Heq; cbn; tauto).

    (* =================================================== *)
    (* Peel the 9 REdLetZero introductions.                *)
    (* =================================================== *)

    (* Helper macro inlined: each [REdLetZero] adds a fresh slot,
       and we propagate the two byte facts forward via
       [let_zero_preserves_holds_B32]. *)

    (* 1: lo *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_a := rs_set_tower_ed rs1 "lo" (exist_tval_ed TFpL25519 v0)) in *.
    assert (Hlo_a : Bytes32_holds rs_a lo_bytes_loc.(loc_var) z_lo)
      by (unfold rs_a; apply let_zero_preserves_holds_B32; auto).
    assert (Hhi_a : Bytes32_holds rs_a hi_bytes_loc.(loc_var) z_hi)
      by (unfold rs_a; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_a. clear rs1 Hlo_b Hhi_b v0. rename Hexec_n' into Hexec_n.

    (* 2: hi *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_b := rs_set_tower_ed rs_a "hi" (exist_tval_ed TFpL25519 v0)) in *.
    assert (Hlo_b' : Bytes32_holds rs_b lo_bytes_loc.(loc_var) z_lo)
      by (unfold rs_b; apply let_zero_preserves_holds_B32; auto).
    assert (Hhi_b' : Bytes32_holds rs_b hi_bytes_loc.(loc_var) z_hi)
      by (unfold rs_b; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_b. clear rs_a Hlo_a Hhi_a v0. rename Hexec_n' into Hexec_n.

    (* 3: l_extra *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_c := rs_set_tower_ed rs_b "l_extra" (exist_tval_ed TFpL25519 v0)) in *.
    assert (Hlo_c : Bytes32_holds rs_c lo_bytes_loc.(loc_var) z_lo)
      by (unfold rs_c; apply let_zero_preserves_holds_B32; auto).
    assert (Hhi_c : Bytes32_holds rs_c hi_bytes_loc.(loc_var) z_hi)
      by (unfold rs_c; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_c. clear rs_b Hlo_b' Hhi_b' v0. rename Hexec_n' into Hexec_n.

    (* 4: sixteen *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_d := rs_set_tower_ed rs_c "sixteen" (exist_tval_ed TFpL25519 v0)) in *.
    assert (Hlo_d : Bytes32_holds rs_d lo_bytes_loc.(loc_var) z_lo)
      by (unfold rs_d; apply let_zero_preserves_holds_B32; auto).
    assert (Hhi_d : Bytes32_holds rs_d hi_bytes_loc.(loc_var) z_hi)
      by (unfold rs_d; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_d. clear rs_c Hlo_c Hhi_c v0. rename Hexec_n' into Hexec_n.

    (* 5: c256_pre *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_e := rs_set_tower_ed rs_d "c256_pre" (exist_tval_ed TFpL25519 v0)) in *.
    assert (Hlo_e : Bytes32_holds rs_e lo_bytes_loc.(loc_var) z_lo)
      by (unfold rs_e; apply let_zero_preserves_holds_B32; auto).
    assert (Hhi_e : Bytes32_holds rs_e hi_bytes_loc.(loc_var) z_hi)
      by (unfold rs_e; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_e. clear rs_d Hlo_d Hhi_d v0. rename Hexec_n' into Hexec_n.

    (* 6: c256 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_f := rs_set_tower_ed rs_e "c256" (exist_tval_ed TFpL25519 v0)) in *.
    assert (Hlo_f : Bytes32_holds rs_f lo_bytes_loc.(loc_var) z_lo)
      by (unfold rs_f; apply let_zero_preserves_holds_B32; auto).
    assert (Hhi_f : Bytes32_holds rs_f hi_bytes_loc.(loc_var) z_hi)
      by (unfold rs_f; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_f. clear rs_e Hlo_e Hhi_e v0. rename Hexec_n' into Hexec_n.

    (* 7: hc256 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_g := rs_set_tower_ed rs_f "hc256" (exist_tval_ed TFpL25519 v0)) in *.
    assert (Hlo_g : Bytes32_holds rs_g lo_bytes_loc.(loc_var) z_lo)
      by (unfold rs_g; apply let_zero_preserves_holds_B32; auto).
    assert (Hhi_g : Bytes32_holds rs_g hi_bytes_loc.(loc_var) z_hi)
      by (unfold rs_g; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_g. clear rs_f Hlo_f Hhi_f v0. rename Hexec_n' into Hexec_n.

    (* 8: le_bytes *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_h := rs_set_tower_ed rs_g "le_bytes" (exist_tval_ed (TBytes 32) v0)) in *.
    assert (Hlo_h : Bytes32_holds rs_h lo_bytes_loc.(loc_var) z_lo)
      by (unfold rs_h; apply let_zero_preserves_holds_B32; auto).
    assert (Hhi_h : Bytes32_holds rs_h hi_bytes_loc.(loc_var) z_hi)
      by (unfold rs_h; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_h. clear rs_g Hlo_g Hhi_g v0. rename Hexec_n' into Hexec_n.

    (* 9: sx_bytes *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [_ Hexec_n']]; clear Hexec_n.
    set (rs_i := rs_set_tower_ed rs_h "sx_bytes" (exist_tval_ed (TBytes 32) v0)) in *.
    assert (Hlo_i : Bytes32_holds rs_i lo_bytes_loc.(loc_var) z_lo)
      by (unfold rs_i; apply let_zero_preserves_holds_B32; auto).
    assert (Hhi_i : Bytes32_holds rs_i hi_bytes_loc.(loc_var) z_hi)
      by (unfold rs_i; apply let_zero_preserves_holds_B32; auto).
    clearbody rs_i. clear rs_h Hlo_h Hhi_h v0. rename Hexec_n' into Hexec_n.

    (* =================================================== *)
    (* Walk the 10-command seqN.                           *)
    (* =================================================== *)

    (* --- Step 1: lo := from_bytes_mod_order(lo_bytes_loc) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs01 [H1 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (from_bytes_mod_order_correct (LFpL "lo") lo_bytes_loc rs_i rs01
                z_lo eq_refl Hlt Hlo_i H1) as [Hlo_v Hfr_1].
    cbn [LFpL loc_var loc_type] in Hlo_v.
    assert (Hhi_01 : Bytes32_holds rs01 hi_bytes_loc.(loc_var) z_hi)
      by (eapply leaf_frame_b32; [exact Hfr_1| cbn; intro; apply Hh_lo; symmetry; auto |exact Hhi_i]).
    clear Hlo_i Hhi_i.

    (* --- Step 2: hi := from_bytes_mod_order(hi_bytes_loc) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs02 [H2 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (from_bytes_mod_order_correct (LFpL "hi") hi_bytes_loc rs01 rs02
                z_hi eq_refl Hht Hhi_01 H2) as [Hhi_v Hfr_2].
    cbn [LFpL loc_var loc_type] in Hhi_v.
    assert (Hlo_02 : FpL25519_holds rs02 "lo" (F.of_Z L z_lo))
      by (eapply leaf_frame_fpL; [exact Hfr_2|discriminate|exact Hlo_v]).
    clear Hlo_v Hhi_01.

    (* --- Step 3: REdSetBytes "le_bytes" L_EXTRA_LE --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs03 [H3 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (setbytes_extra_correct (LBytes32 "le_bytes") rs02 rs03
                eq_refl H3) as [Hle_v Hfr_3].
    cbn [LBytes32 loc_var loc_type] in Hle_v.
    assert (Hlo_03 : FpL25519_holds rs03 "lo" (F.of_Z L z_lo))
      by (eapply leaf_frame_fpL; [exact Hfr_3|discriminate|exact Hlo_02]).
    assert (Hhi_03 : FpL25519_holds rs03 "hi" (F.of_Z L z_hi))
      by (eapply leaf_frame_fpL; [exact Hfr_3|discriminate|exact Hhi_v]).
    clear Hlo_02 Hhi_v.

    (* --- Step 4: REdSetBytes "sx_bytes" SIXTEEN_LE --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs04 [H4 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (setbytes_sixteen_correct (LBytes32 "sx_bytes") rs03 rs04
                eq_refl H4) as [Hsx_v Hfr_4].
    cbn [LBytes32 loc_var loc_type] in Hsx_v.
    assert (Hlo_04 : FpL25519_holds rs04 "lo" (F.of_Z L z_lo))
      by (eapply leaf_frame_fpL; [exact Hfr_4|discriminate|exact Hlo_03]).
    assert (Hhi_04 : FpL25519_holds rs04 "hi" (F.of_Z L z_hi))
      by (eapply leaf_frame_fpL; [exact Hfr_4|discriminate|exact Hhi_03]).
    assert (Hle_04 : Bytes32_holds rs04 "le_bytes" L_EXTRA_Z)
      by (eapply leaf_frame_b32; [exact Hfr_4|discriminate|exact Hle_v]).
    clear Hlo_03 Hhi_03 Hle_v.

    (* --- Step 5: l_extra := from_bytes_mod_order(le_bytes) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs05 [H5 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (from_bytes_mod_order_correct (LFpL "l_extra")
                (LBytes32 "le_bytes") rs04 rs05 L_EXTRA_Z
                eq_refl eq_refl Hle_04 H5) as [Hlext_v Hfr_5].
    cbn [LFpL LBytes32 loc_var loc_type] in Hlext_v.
    assert (Hlo_05 : FpL25519_holds rs05 "lo" (F.of_Z L z_lo))
      by (eapply leaf_frame_fpL; [exact Hfr_5|discriminate|exact Hlo_04]).
    assert (Hhi_05 : FpL25519_holds rs05 "hi" (F.of_Z L z_hi))
      by (eapply leaf_frame_fpL; [exact Hfr_5|discriminate|exact Hhi_04]).
    assert (Hsx_05 : Bytes32_holds rs05 "sx_bytes" 16)
      by (eapply leaf_frame_b32; [exact Hfr_5|discriminate|exact Hsx_v]).
    clear Hlo_04 Hhi_04 Hle_04 Hsx_v.

    (* --- Step 6: sixteen := from_bytes_mod_order(sx_bytes) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs06 [H6 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (from_bytes_mod_order_correct (LFpL "sixteen")
                (LBytes32 "sx_bytes") rs05 rs06 16
                eq_refl eq_refl Hsx_05 H6) as [Hsxt_v Hfr_6].
    cbn [LFpL LBytes32 loc_var loc_type] in Hsxt_v.
    assert (Hlo_06 : FpL25519_holds rs06 "lo" (F.of_Z L z_lo))
      by (eapply leaf_frame_fpL; [exact Hfr_6|discriminate|exact Hlo_05]).
    assert (Hhi_06 : FpL25519_holds rs06 "hi" (F.of_Z L z_hi))
      by (eapply leaf_frame_fpL; [exact Hfr_6|discriminate|exact Hhi_05]).
    assert (Hlext_06 : FpL25519_holds rs06 "l_extra" (F.of_Z L L_EXTRA_Z))
      by (eapply leaf_frame_fpL; [exact Hfr_6|discriminate|exact Hlext_v]).
    clear Hlo_05 Hhi_05 Hsx_05 Hlext_v.

    (* --- Step 7: c256_pre := l_extra · sixteen --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs07 [H7 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFpL "c256_pre") (LFpL "l_extra") (LFpL "sixteen")
                rs06 rs07 (F.of_Z L L_EXTRA_Z) (F.of_Z L 16)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Hlext_06 Hsxt_v H7) as [Hcp_v Hfr_7].
    cbn [LFpL loc_var loc_type] in Hcp_v.
    assert (Hlo_07 : FpL25519_holds rs07 "lo" (F.of_Z L z_lo))
      by (eapply leaf_frame_fpL; [exact Hfr_7|discriminate|exact Hlo_06]).
    assert (Hhi_07 : FpL25519_holds rs07 "hi" (F.of_Z L z_hi))
      by (eapply leaf_frame_fpL; [exact Hfr_7|discriminate|exact Hhi_06]).
    clear Hlo_06 Hhi_06 Hlext_06 Hsxt_v.

    (* --- Step 8: c256 := negate(c256_pre)
       = -(L_extra · 16) = -16 · L_extra (mod L) = 2^256 (by c256_eq). *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs08 [H8 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (negate_correct (LFpL "c256") (LFpL "c256_pre") rs07 rs08
                (F.mul (F.of_Z L L_EXTRA_Z) (F.of_Z L 16))
                eq_refl eq_refl (ltac:(cbn; discriminate)) Hcp_v H8)
      as [Hc2_v Hfr_8].
    cbn [LFpL loc_var loc_type] in Hc2_v.
    (* Rewrite via [c256_eq]: F.opp (L_extra · 16) = F.of_Z L (2^256). *)
    rewrite <- c256_eq in Hc2_v.
    assert (Hlo_08 : FpL25519_holds rs08 "lo" (F.of_Z L z_lo))
      by (eapply leaf_frame_fpL; [exact Hfr_8|discriminate|exact Hlo_07]).
    assert (Hhi_08 : FpL25519_holds rs08 "hi" (F.of_Z L z_hi))
      by (eapply leaf_frame_fpL; [exact Hfr_8|discriminate|exact Hhi_07]).
    clear Hlo_07 Hhi_07 Hcp_v.

    (* --- Step 9: hc256 := hi · c256 = z_hi · 2^256. --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs09 [H9 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFpL "hc256") (LFpL "hi") (LFpL "c256")
                rs08 rs09 (F.of_Z L z_hi) (F.of_Z L (Z.pow 2 256))
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Hhi_08 Hc2_v H9) as [Hhc_v Hfr_9].
    cbn [LFpL loc_var loc_type] in Hhc_v.
    assert (Hlo_09 : FpL25519_holds rs09 "lo" (F.of_Z L z_lo))
      by (eapply leaf_frame_fpL; [exact Hfr_9|discriminate|exact Hlo_08]).
    clear Hlo_08 Hhi_08 Hc2_v.

    (* --- Step 10 (final): dest := hc256 + lo. --- *)
    cbn [seqN] in Hexec_n.
    (* Distinct: dest ≠ hc256 (by Hd_hc), dest ≠ lo (by Hd_lo). *)
    assert (Hne_d_hc : dest.(loc_var) <> (LFpL "hc256").(loc_var))
      by (cbn; exact Hd_hc).
    assert (Hne_d_lo : dest.(loc_var) <> (LFpL "lo").(loc_var))
      by (cbn; exact Hd_lo).
    pose proof (add_correct dest (LFpL "hc256") (LFpL "lo") rs09 rs2
                (F.mul (F.of_Z L z_hi) (F.of_Z L (Z.pow 2 256)))
                (F.of_Z L z_lo)
                Hdt eq_refl eq_refl
                Hne_d_hc Hne_d_lo Hhc_v Hlo_09 Hexec_n) as [Hdest_v _].
    exact Hdest_v.
  Qed.

End Scalar25519FromWideCorrect.

(* Sanity check: only Section [Hypothesis]es show up. *)
Print Assumptions from_wide_correct.
