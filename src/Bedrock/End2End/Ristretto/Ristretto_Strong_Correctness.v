(** * Ristretto_Strong_Correctness — full functional simulation for
 *    [ristretto_decode_rs].
 *
 * Mirrors [End2End/Ed25519/Sign_Strong_Correctness.v]: from a
 * [rust_exec_ed strong_callee_post_ristretto strong_callee_post_n_ristretto
 *  function_table ristretto_decode_rs rs1 rs2] derivation plus the slot
 * preconditions, the output slot ["out_var"] in [rs2] equals
 * [ristretto_decode_gallina_nlet bs] (= [ristretto_decode_gallina bs]).
 *
 * Status (2026-05-23):
 *   - [ristretto_decode_rhoare_reject] — Qed, "Closed under the global
 *     context" (0 axioms).  A GENUINE full-AST functional simulation of
 *     the REJECTION path: parse = None ⇒ out = bad_point.  Plus 51 Qed
 *     support lemmas (notably [rhoare_byte_load_slot] /
 *     [rhoare_set_bytes_slot], which recover the slot type tag that the
 *     type-agnostic [strong_callee_post] cannot supply).
 *   - The SUCCESS-path theorem [ristretto_decode_strong_correct] is NOT
 *     yet Qed.  It is preserved as a validated BLOCKED blueprint (§7, in
 *     a comment) — every construct compiled individually via MCP, but
 *     the assembled proof hits two issues: (1) one [admit] for the
 *     [REdFor] byte-sum accumulator of the y=0 check, and (2) term
 *     blowup from repeatedly traversing the giant unfolded gallina post
 *     (the known bedrock2-WP cumulative-large-term cost).  Fix
 *     identified: keep the post folded as [ristretto_decode_gallina_nlet
 *     bs] and unfold only at the leaves.  The blueprint contains the
 *     only [Admitted] in this file, and it is INSIDE the comment, so the
 *     file compiles with ZERO active admits / axioms.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Bool.Bool.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdRupicola.
Require Import Bedrock.RustCmdRupicolaRistretto.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Lizard.RistrettoConsts.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Require Import Bedrock.End2End.Lizard.RistrettoDecode.
Require Import Bedrock.End2End.Ristretto.RistrettoBridges.
Require Import Bedrock.End2End.Ristretto.Ristretto_RustCmd.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0. Constant-slot simulation lemmas (REdSetBytes byte lists).      *)
(* ================================================================ *)

Lemma map_const_one : List.map Z_to_byte const_one_zs = fe25519_const_one_spec.
Proof. unfold fe25519_const_one_spec. vm_compute. reflexivity. Qed.
Lemma map_const_two : List.map Z_to_byte const_two_zs = fe25519_const_two_spec.
Proof. unfold fe25519_const_two_spec. vm_compute. reflexivity. Qed.
Lemma map_const_d : List.map Z_to_byte const_d_zs = fe25519_const_d_spec.
Proof. unfold fe25519_const_d_spec. vm_compute. reflexivity. Qed.
Lemma map_const_p : List.map Z_to_byte const_p_zs = le_split 32 ed25519_p.
Proof. vm_compute. reflexivity. Qed.
Lemma map_bad : List.map Z_to_byte (List.repeat 0%Z 200) = ristretto_bad_point.
Proof. unfold ristretto_bad_point. vm_compute. reflexivity. Qed.

Lemma const_one_eq : fe25519_const_one_spec = le_split 32 1.
Proof. reflexivity. Qed.
Lemma const_two_eq : fe25519_const_two_spec = le_split 32 2.
Proof. reflexivity. Qed.
Lemma const_d_eq : fe25519_const_d_spec = le_split 32 ed25519_d.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §1. Arithmetic glue.                                               *)
(* ================================================================ *)

(** [ed25519_p] is in [0, 2^256). *)
Lemma ed25519_p_lt : 0 <= ed25519_p < 2 ^ 256.
Proof. unfold ed25519_p. lia. Qed.

(** A value reduced mod [ed25519_p] is in range. *)
Lemma mod_p_range : forall z, 0 <= z mod ed25519_p < ed25519_p.
Proof. intros z. apply Z.mod_pos_bound. unfold ed25519_p. lia. Qed.

(** [le_combine (le_split 32 z) = z] when [0 <= z < ed25519_p]. *)
Lemma le_combine_split_p : forall z, 0 <= z < ed25519_p ->
  le_combine (le_split 32 z) = z.
Proof.
  intros z Hz. rewrite le_combine_split.
  change (2 ^ (Z.of_nat 32 * 8)) with (2 ^ 256).
  apply Z.mod_small. unfold ed25519_p in Hz. lia.
Qed.

(** Specialisation for canonical (mod-p) values; no hypothesis needed. *)
Lemma le_combine_split_modp : forall z,
  le_combine (le_split 32 (z mod ed25519_p)) = z mod ed25519_p.
Proof. intros z. apply le_combine_split_p, mod_p_range. Qed.

(** [le_split 40 z = le_split 32 z ++ repeat 0 8] for in-range [z]. *)
Lemma le_split_40_32 : forall z, 0 <= z < ed25519_p ->
  le_split 40 z = (le_split 32 z ++ List.repeat Byte.x00 8)%list.
Proof.
  intros z Hz. apply le_combine_inj.
  - rewrite length_app, !length_le_split, List.repeat_length. reflexivity.
  - rewrite le_combine_app_0, !le_combine_split.
    change (2 ^ (Z.of_nat 32 * 8)) with (2 ^ 256).
    change (2 ^ (Z.of_nat 40 * 8)) with (2 ^ 320).
    rewrite (Z.mod_small z (2 ^ 256)) by (unfold ed25519_p in Hz; lia).
    rewrite (Z.mod_small z (2 ^ 320)) by (unfold ed25519_p in Hz; lia).
    reflexivity.
Qed.

(* ================================================================ *)
(* §2. byte-0 / is_negative bridge.                                   *)
(* ================================================================ *)

(** [nth_error (le_split 32 z) 0 = Some (byte.of_Z z)]. *)
Lemma nth_error_le_split_0 : forall z,
  nth_error (le_split 32 z) 0 = Some (byte.of_Z z).
Proof.
  intros z. rewrite (nth_error_le_split 0 32 z) by lia.
  cbn [Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
Qed.

(** Scalar value of the [byte.of_Z z] byte is [z mod 256]. *)
Lemma byteN_of_Z : forall z,
  Z.of_N (Byte.to_N (byte.of_Z z)) = z mod 256.
Proof.
  intros z.
  change (Z.of_N (Byte.to_N (byte.of_Z z))) with (byte.unsigned (byte.of_Z z)).
  rewrite byte.unsigned_of_Z. unfold byte.wrap. reflexivity.
Qed.

(** [is_negative z = (z mod 256) bit 0]; for [0 <= z < ed25519_p],
    [Z.land (z mod 256) 1 <> 0 <-> ristretto_is_negative z = true]. *)
Lemma land_mod256_1_testbit : forall z,
  Z.land (z mod 256) 1 = (if Z.testbit z 0 then 1 else 0).
Proof.
  intros z. transitivity ((z mod 256) mod 2).
  - change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
  - rewrite Z.mod_mod_divide by (exists 128; reflexivity).
    rewrite <- Z.bit0_mod. destruct (Z.testbit z 0); reflexivity.
Qed.

(* ================================================================ *)
(* §3. y = 0 byte-sum bridge (for the REdFor accumulator).            *)
(* ================================================================ *)

(** Recursive sum of the scalar values of a byte list. *)
Fixpoint byte_sum (bs : list Byte.byte) : Z :=
  match bs with
  | [] => 0
  | b :: r => Z.of_N (Byte.to_N b) + byte_sum r
  end.

(** Every byte value is non-negative. *)
Lemma byteN_nonneg : forall b, 0 <= Z.of_N (Byte.to_N b).
Proof. intros b. apply N2Z.is_nonneg. Qed.

(** [byte_sum] is non-negative. *)
Lemma byte_sum_nonneg : forall bs, 0 <= byte_sum bs.
Proof.
  induction bs as [|b r IH]; cbn; [lia|].
  pose proof (byteN_nonneg b). lia.
Qed.

(** [byte_sum] is bounded by [255 * length]. *)
Lemma byte_sum_bound : forall bs, byte_sum bs <= 255 * Z.of_nat (length bs).
Proof.
  induction bs as [|b r IH]; cbn; [lia|].
  pose proof (Byte.to_N_bounded b) as Hb.
  assert (Z.of_N (Byte.to_N b) <= 255) by lia.
  lia.
Qed.

(** Cons-skipn step: peeling index [i]. *)
Lemma byte_sum_skipn_S : forall i bs,
  (i < length bs)%nat ->
  byte_sum (skipn i bs) =
    Z.of_N (Byte.to_N (nth_default Byte.x00 bs i)) + byte_sum (skipn (S i) bs).
Proof.
  induction i as [|i IH]; intros bs Hlt.
  - destruct bs as [|b r]; cbn in *; [lia|]. reflexivity.
  - destruct bs as [|b r]; cbn in Hlt; [lia|].
    cbn [skipn]. rewrite IH by lia.
    f_equal.
Qed.

(** [byte_sum bs = 0] iff all bytes are zero, packaged as
    [le_combine bs = 0] when [length bs = 32]. *)
Lemma byte_sum_zero_iff_le_combine : forall bs,
  length bs = 32%nat ->
  (byte_sum bs = 0 <-> le_combine bs = 0).
Proof.
  intros bs Hlen. split.
  - intros Hsum.
    (* All bytes are zero, hence bs = repeat x00 32, hence le_combine = 0. *)
    assert (Hall : bs = List.repeat Byte.x00 (length bs)).
    { clear Hlen. induction bs as [|b r IH]; cbn in *; [reflexivity|].
      pose proof (byteN_nonneg b). pose proof (byte_sum_nonneg r).
      assert (Z.of_N (Byte.to_N b) = 0) by lia.
      assert (byte_sum r = 0) by lia.
      assert (Byte.to_N b = 0%N) by lia.
      assert (b = Byte.x00).
      { destruct b; cbn in *; try reflexivity; discriminate. }
      subst b. f_equal. apply IH. assumption. }
    rewrite Hall. apply le_combine_0.
  - intros Hcomb.
    (* le_combine bs = 0, length 32, so bs = le_split 32 0 = repeat x00 32. *)
    assert (Hbs : bs = le_split 32 (le_combine bs)).
    { rewrite <- Hlen. symmetry. apply split_le_combine. }
    rewrite Hcomb in Hbs. rewrite Hbs.
    vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(* §4. Mod-arith glue (reduce-then-multiply identities).             *)
(* ================================================================ *)

(** [((a mod p) * b) mod p = (a * b) mod p]. *)
Lemma mul_mod_l : forall a b,
  ((a mod ed25519_p) * b) mod ed25519_p = (a * b) mod ed25519_p.
Proof. intros a b. apply Z.mul_mod_idemp_l. unfold ed25519_p; lia. Qed.

(** Dy step: [((I*Dx mod p) * v) mod p = (I*Dx*v) mod p]. *)
Lemma Dy_glue : forall I Dx v,
  (((I * Dx) mod ed25519_p) * v) mod ed25519_p = (I * Dx * v) mod ed25519_p.
Proof. intros. apply mul_mod_l. Qed.

(** x_raw step: [((2*s mod p) * Dx) mod p = (2*s*Dx) mod p]. *)
Lemma x_raw_glue : forall s Dx,
  (((2 * s) mod ed25519_p) * Dx) mod ed25519_p = (2 * s * Dx) mod ed25519_p.
Proof. intros. apply mul_mod_l. Qed.

(* ================================================================ *)
(* §5. fe25519 spec evaluated on canonical inputs.                   *)
(* ================================================================ *)

Lemma fe_mul_eval : forall a b, 0 <= a < ed25519_p -> 0 <= b < ed25519_p ->
  fe25519_mul_spec (le_split 32 a) (le_split 32 b) = le_split 32 ((a * b) mod ed25519_p).
Proof.
  intros a b Ha Hb. unfold fe25519_mul_spec.
  rewrite !le_combine_split_p by assumption. reflexivity.
Qed.

Lemma fe_add_eval : forall a b, 0 <= a < ed25519_p -> 0 <= b < ed25519_p ->
  fe25519_add_spec (le_split 32 a) (le_split 32 b) = le_split 32 ((a + b) mod ed25519_p).
Proof.
  intros a b Ha Hb. unfold fe25519_add_spec.
  rewrite !le_combine_split_p by assumption. reflexivity.
Qed.

Lemma fe_sub_eval : forall a b, 0 <= a < ed25519_p -> 0 <= b < ed25519_p ->
  fe25519_sub_spec (le_split 32 a) (le_split 32 b) = le_split 32 ((a - b) mod ed25519_p).
Proof.
  intros a b Ha Hb. unfold fe25519_sub_spec.
  rewrite !le_combine_split_p by assumption. reflexivity.
Qed.

Lemma fe_sq_eval : forall a, 0 <= a < ed25519_p ->
  fe25519_sq_spec (le_split 32 a) = le_split 32 ((a * a) mod ed25519_p).
Proof.
  intros a Ha. unfold fe25519_sq_spec.
  rewrite !le_combine_split_p by assumption. reflexivity.
Qed.

(** Subtraction with the prime constant [p] as the (non-canonical, but
    [< 2^256]) minuend: equals the canonical negation. *)
Lemma fe_sub_p_eval : forall z, 0 <= z < ed25519_p ->
  fe25519_sub_spec (le_split 32 ed25519_p) (le_split 32 z)
  = le_split 32 ((ed25519_p - z) mod ed25519_p).
Proof.
  intros z Hz. rewrite fe25519_sub_p_eq_canonical_negate.
  unfold canonical_negate_spec, ristretto_canonical_negate.
  rewrite le_combine_split_p by assumption. reflexivity.
Qed.

(** The constant-one slot, expressed via [le_split 32 1]. *)
Lemma one_split : fe25519_const_one_spec = le_split 32 1.
Proof. reflexivity. Qed.
Lemma two_split : fe25519_const_two_spec = le_split 32 2.
Proof. reflexivity. Qed.
Lemma d_split : fe25519_const_d_spec = le_split 32 ed25519_d.
Proof. reflexivity. Qed.

(** [ed25519_d] is in range. *)
Lemma ed25519_d_range : 0 <= ed25519_d < ed25519_p.
Proof. unfold ed25519_d, ed25519_p. lia. Qed.

(** [1] and [2] are in range. *)
Lemma one_range : 0 <= 1 < ed25519_p.
Proof. unfold ed25519_p. lia. Qed.
Lemma two_range : 0 <= 2 < ed25519_p.
Proof. unfold ed25519_p. lia. Qed.

(** Byte-load from a slot whose bytes are known via [slot_holds].
    Unlike [compile_red_byte_load] (which demands an explicit typed
    tower fact [rs_get_tower = Some (exist (TBytes n) (VBytes n bs))]
    that the type-agnostic [slot_holds] cannot supply for callee
    outputs), this lemma does INVERSION on the byte-load execution:
    the [rexec_byte_load] rule itself provides the stored type tag
    [TBytes n], which the AST's [loc_type = TBytes n] then pins, and
    [slot_holds] reconciles the stored bytes with the known [sbs]. *)
Lemma rhoare_byte_load_slot :
  forall (cp : String.string -> list located_ed -> located_ed ->
               rust_state_ed -> rust_state_ed -> Prop)
         (cpn : String.string -> list located_ed -> list located_ed ->
                rust_state_ed -> rust_state_ed -> Prop)
         (ft : function_table_ed)
         (rs : rust_state_ed) (x : var) (loc : located_ed) (idx_e : sexpr_ed)
         (idx_v : Z) (n : nat) (sbs : list Byte.byte) (b : Byte.byte)
         (pred : rust_state_ed -> Prop),
    eval_sexpr_ed rs idx_e = Some idx_v ->
    loc.(loc_type) = TBytes n ->
    slot_holds rs loc.(loc_var) sbs ->
    nth_error sbs (Z.to_nat idx_v) = Some b ->
    pred (rs_set_scalar_ed rs x (Z.of_N (Byte.to_N b))) ->
    rhoare cp cpn ft rs (REdByteLoad x loc idx_e) pred.
Proof.
  intros cp cpn ft rs x loc idx_e idx_v n sbs b pred
         Hidx Hty Hslot Hnth Hpred rs' Hexec.
  inversion Hexec; subst.
  (* From inversion: eval idx = Some idx_v0, loc_type = TBytes n0,
     rs_get_tower loc = Some (exist (TBytes n0) (VBytes n0 bs0)),
     nth_error bs0 idx_v0 = Some b0, result = set_scalar x (b0 value). *)
  match goal with
  | He : eval_sexpr_ed rs idx_e = Some _ |- _ =>
      rewrite Hidx in He; inversion He; subst
  end.
  unfold slot_holds, bytes_at in Hslot.
  match goal with
  | Hg : rs_get_tower_ed rs loc.(loc_var) = Some _ |- _ =>
      rewrite Hg in Hslot
  end.
  match goal with
  | Hg : rs_get_tower_ed rs loc.(loc_var) =
           Some (exist_tval_ed (TBytes ?n0) (VBytes ?n0 ?bs0)) |- _ =>
      cbn in Hslot; inversion Hslot; subst bs0
  end.
  (* Now nth_error sbs idx_v = Some b (Hnth) and inversion's nth = Some b0. *)
  match goal with
  | Hn : nth_error sbs (Z.to_nat ?iv) = Some _ |- _ =>
      rewrite Hnth in Hn; inversion Hn; subst
  end.
  exact Hpred.
Qed.

(** [REdSetBytes] into a slot of the AST-declared type [TBytes n].
    Inversion on the execution provides the stored type tag (which the
    rule forces to equal the AST's [loc_type = TBytes n]), so no typed
    tower precondition is needed — the resulting slot holds
    [map Z_to_byte bytes]. *)
Lemma rhoare_set_bytes_slot :
  forall (cp : String.string -> list located_ed -> located_ed ->
               rust_state_ed -> rust_state_ed -> Prop)
         (cpn : String.string -> list located_ed -> list located_ed ->
                rust_state_ed -> rust_state_ed -> Prop)
         (ft : function_table_ed)
         (rs : rust_state_ed) (loc : located_ed) (bytes : list Z)
         (n : nat) (pred : rust_state_ed -> Prop),
    loc.(loc_type) = TBytes n ->
    List.length bytes = n ->
    pred (rs_set_tower_ed rs loc.(loc_var)
            (exist_tval_ed (TBytes n) (VBytes n (List.map Z_to_byte bytes)))) ->
    rhoare cp cpn ft rs (REdSetBytes loc bytes) pred.
Proof.
  intros cp cpn ft rs loc bytes n pred Hty Hlen Hpred rs' Hexec.
  inversion Hexec; subst.
  match goal with
  | Hg : loc.(loc_type) = TBytes ?n0 |- _ =>
      rewrite Hty in Hg; inversion Hg; subst
  end.
  exact Hpred.
Qed.

(** Any [rust_val_ed (TBytes n)] is [VBytes n bs] for some [bs]. *)
Lemma rust_val_TBytes_inv : forall n (v : rust_val_ed (TBytes n)),
  exists bs, v = VBytes n bs.
Proof.
  intros n v. refine (match v with VBytes n0 bs => _ end). exists bs. reflexivity.
Qed.

(** Sequenced [REdSetBytes; k]: run [k] in the post-write state. *)
Lemma rhoare_set_bytes_seq :
  forall (cp : String.string -> list located_ed -> located_ed ->
               rust_state_ed -> rust_state_ed -> Prop)
         (cpn : String.string -> list located_ed -> list located_ed ->
                rust_state_ed -> rust_state_ed -> Prop)
         (ft : function_table_ed)
         (rs : rust_state_ed) (loc : located_ed) (bytes : list Z)
         (n : nat) (k : rust_cmd_ed) (pred : rust_state_ed -> Prop),
    loc.(loc_type) = TBytes n ->
    List.length bytes = n ->
    rhoare cp cpn ft
      (rs_set_tower_ed rs loc.(loc_var)
         (exist_tval_ed (TBytes n) (VBytes n (List.map Z_to_byte bytes)))) k pred ->
    rhoare cp cpn ft rs (REdSeq (REdSetBytes loc bytes) k) pred.
Proof.
  intros cp cpn ft rs loc bytes n k pred Hty Hlen Hk.
  eapply compile_red_seq with
    (pred0 := fun rsm => rsm = rs_set_tower_ed rs loc.(loc_var)
       (exist_tval_ed (TBytes n) (VBytes n (List.map Z_to_byte bytes)))).
  - eapply rhoare_set_bytes_slot; [exact Hty | exact Hlen | reflexivity].
  - intros rsm Hrsm; subst rsm. exact Hk.
Qed.

(** Sequenced [REdByteLoad; k]: run [k] with the scalar set from the
    known slot bytes. *)
Lemma rhoare_byte_load_seq :
  forall (cp : String.string -> list located_ed -> located_ed ->
               rust_state_ed -> rust_state_ed -> Prop)
         (cpn : String.string -> list located_ed -> list located_ed ->
                rust_state_ed -> rust_state_ed -> Prop)
         (ft : function_table_ed)
         (rs : rust_state_ed) (x : var) (loc : located_ed) (idx_e : sexpr_ed)
         (idx_v : Z) (n : nat) (sbs : list Byte.byte) (b : Byte.byte)
         (k : rust_cmd_ed) (pred : rust_state_ed -> Prop),
    eval_sexpr_ed rs idx_e = Some idx_v ->
    loc.(loc_type) = TBytes n ->
    slot_holds rs loc.(loc_var) sbs ->
    nth_error sbs (Z.to_nat idx_v) = Some b ->
    rhoare cp cpn ft (rs_set_scalar_ed rs x (Z.of_N (Byte.to_N b))) k pred ->
    rhoare cp cpn ft rs (REdSeq (REdByteLoad x loc idx_e) k) pred.
Proof.
  intros cp cpn ft rs x loc idx_e idx_v n sbs b k pred Hidx Hty Hslot Hnth Hk.
  eapply compile_red_seq with
    (pred0 := fun rsm => rsm = rs_set_scalar_ed rs x (Z.of_N (Byte.to_N b))).
  - eapply rhoare_byte_load_slot; [exact Hidx | exact Hty | exact Hslot | exact Hnth | reflexivity].
  - intros rsm Hrsm; subst rsm. exact Hk.
Qed.

(** Sequenced [REdSelect; k]: the CT cmov copies the chosen source's
    [tval] into [dest], then [k] runs.  The continuation receives the
    chosen source's [tval] and the post-copy state. *)
Lemma rhoare_select_seq :
  forall (cp : String.string -> list located_ed -> located_ed ->
               rust_state_ed -> rust_state_ed -> Prop)
         (cpn : String.string -> list located_ed -> list located_ed ->
                rust_state_ed -> rust_state_ed -> Prop)
         (ft : function_table_ed)
         (rs : rust_state_ed) (cond : sexpr_ed)
         (if_t if_f dest : located_ed) (cond_v : Z)
         (k : rust_cmd_ed) (pred : rust_state_ed -> Prop),
    eval_sexpr_ed rs cond = Some cond_v ->
    if_t.(loc_type) = dest.(loc_type) ->
    if_f.(loc_type) = dest.(loc_type) ->
    (forall tv,
       rs_get_tower_ed rs (if Z.eqb cond_v 0 then if_f else if_t).(loc_var) = Some tv ->
       rhoare cp cpn ft (rs_set_tower_ed rs dest.(loc_var) tv) k pred) ->
    rhoare cp cpn ft rs (REdSeq (REdSelect cond if_t if_f dest) k) pred.
Proof.
  intros cp cpn ft rs cond if_t if_f dest cond_v k pred Hcond Ht Hf Hk.
  eapply compile_red_seq with
    (pred0 := fun rsm =>
       exists tv, rs_get_tower_ed rs (if Z.eqb cond_v 0 then if_f else if_t).(loc_var) = Some tv
                  /\ rsm = rs_set_tower_ed rs dest.(loc_var) tv).
  - intros rsm Hexec. inversion Hexec; subst.
    match goal with
    | He : eval_sexpr_ed rs cond = Some _ |- _ =>
        rewrite Hcond in He; inversion He; subst
    end.
    eexists; split; [|reflexivity].
    match goal with
    | Hg : rs_get_tower_ed rs _ = Some _ |- _ => exact Hg
    end.
  - intros rsm [tv [Hgt ->]]. apply Hk. exact Hgt.
Qed.

(** Extract a slot's [tval] in a typed form from [slot_holds]. *)
Lemma slot_holds_tval : forall rs x bs,
  slot_holds rs x bs ->
  exists n, rs_get_tower_ed rs x = Some (exist_tval_ed (TBytes n) (VBytes n bs)).
Proof.
  intros rs x bs H. unfold slot_holds, bytes_at in H.
  destruct (rs_get_tower_ed rs x) as [[t0 vv]|] eqn:Hget; try discriminate.
  destruct t0; try discriminate.
  revert H. refine (match vv with VBytes n b => _ end). intros H.
  inversion H; subst. exists n. reflexivity.
Qed.

(** Reading back a slot just written with a [VBytes n b]. *)
Lemma slot_holds_set_tower_same : forall rs x n b,
  slot_holds (rs_set_tower_ed rs x (exist_tval_ed (TBytes n) (VBytes n b))) x b.
Proof.
  intros rs x n b.
  unfold slot_holds, bytes_at, rs_get_tower_ed, rs_set_tower_ed; simpl.
  rewrite lookup_t_ed_update_at. reflexivity.
Qed.

(** Raw tower lookup survives a set of a different slot. *)
Lemma rs_get_tower_set_other : forall rs x t v y,
  y <> x ->
  rs_get_tower_ed (rs_set_tower_ed rs x (exist_tval_ed t v)) y =
  rs_get_tower_ed rs y.
Proof.
  intros rs x t v y Hne.
  unfold rs_get_tower_ed, rs_set_tower_ed; simpl.
  apply lookup_update_in_place_ed_other. congruence.
Qed.

(** Same, for an arbitrary [tval_ed] (used after [REdSelect], whose
    copied [tval] is opaque). *)
Lemma rs_get_tower_set_other_tval : forall rs x (tv : tval_ed) y,
  y <> x ->
  rs_get_tower_ed (rs_set_tower_ed rs x tv) y = rs_get_tower_ed rs y.
Proof.
  intros rs x tv y Hne.
  unfold rs_get_tower_ed, rs_set_tower_ed; simpl.
  apply lookup_update_in_place_ed_other. congruence.
Qed.

Lemma slot_holds_set_tower_other_tval : forall rs x (tv : tval_ed) y bs,
  y <> x -> slot_holds rs y bs -> slot_holds (rs_set_tower_ed rs x tv) y bs.
Proof.
  intros rs x tv y bs Hne Hh.
  unfold slot_holds, bytes_at in *.
  rewrite rs_get_tower_set_other_tval by congruence. exact Hh.
Qed.

(** Reading back a slot just written with an arbitrary [tval]. *)
Lemma rs_get_tower_set_same_tval : forall rs x (tv : tval_ed),
  rs_get_tower_ed (rs_set_tower_ed rs x tv) x = Some tv.
Proof.
  intros rs x tv. unfold rs_get_tower_ed, rs_set_tower_ed; simpl.
  apply lookup_t_ed_update_at.
Qed.

(** Tower lookup is unaffected by a scalar set. *)
Lemma rs_get_tower_set_scalar : forall rs x v y,
  rs_get_tower_ed (rs_set_scalar_ed rs x v) y = rs_get_tower_ed rs y.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §6. Slot-name disequality tactic.                                  *)
(* ================================================================ *)

Ltac rd_neq :=
  cbv [v_rd_bs v_rd_out v_rd_s v_rd_status v_rd_one v_rd_two v_rd_d v_rd_p
       v_rd_ss v_rd_u1 v_rd_u2 v_rd_u1_sq v_rd_u2_sqr v_rd_d_u1sq
       v_rd_neg_du1sq v_rd_v v_rd_den v_rd_ws v_rd_I v_rd_Dx v_rd_IDx
       v_rd_Dy v_rd_s2 v_rd_x_raw v_rd_x_neg v_rd_x v_rd_y v_rd_t
       v_rd_statusb v_rd_xbit v_rd_tbit v_rd_wsb v_rd_yacc v_rd_ybyte
       v_rd_loop];
  discriminate.

(** [sqrt_ratio_m1]'s second output is canonical (in [0, p)). *)
Lemma sqrt_ratio_m1_snd_range : forall u v,
  0 <= snd (ristretto_sqrt_ratio_m1 u v) < ed25519_p.
Proof.
  intros u v. unfold ristretto_sqrt_ratio_m1. cbn zeta.
  destruct (ristretto_is_negative _); cbn [snd].
  - unfold ristretto_canonical_negate. apply Z.mod_pos_bound; unfold ed25519_p; lia.
  - destruct (Z.eqb _ _); [|destruct (Z.eqb _ _); [|destruct (Z.eqb _ _)]];
      apply Z.mod_pos_bound; unfold ed25519_p; lia.
Qed.

(** The parser only returns [Some z] for canonical [z] in [0, p). *)
Lemma parse_some_range : forall bs z,
  ristretto_parse_canonical_felem bs = Some z -> 0 <= z < ed25519_p.
Proof.
  intros bs z H. unfold ristretto_parse_canonical_felem in H.
  destruct (Nat.eqb (length bs) 32); [|discriminate].
  destruct (Z.testbit (le_combine bs) 255); [discriminate|].
  destruct (Z.ltb (le_combine bs) ed25519_p) eqn:Hlt; [|discriminate].
  destruct (ristretto_is_negative (le_combine bs)); [discriminate|].
  inversion H; subst. split; [apply le_combine_bound | apply Z.ltb_lt; exact Hlt].
Qed.

(** Reframe all [slot_holds] hyps over the pre-call state through a
    [frames_except rs_pre rs_post dst] frame (slots [<> dst] survive). *)
Ltac rd_reframe Hframe :=
  repeat match goal with
  | H : slot_holds ?rs ?x ?b |- _ =>
      match type of Hframe with
      | frames_except rs _ _ =>
          apply (slot_holds_frame _ _ _ _ _ Hframe) in H; [|rd_neq]
      end
  end.

(** Peel a single-output [REdCall fname dst args; k] and expose the
    [strong_callee_post_ristretto] obligation as [Hcp] over [rs_pre]
    [rs_post]; leaves the continuation [k] goal. *)
Ltac rd_peel_call Hcp :=
  eapply compile_red_seq;
  [ eapply compile_red_call; intros ? Hcp; exact Hcp
  | let rsx := fresh "rs_i" in intros rsx Hcp ].

(** One fe25519_sq step: source slot fact [Hsrc].  Leaves [Htgt :
    slot_holds <new> result (fe25519_sq_spec <src bytes>)] and reframes
    all surviving slot facts + [HoutC] to the new state. *)
Ltac rd_sq Hsrc :=
  let Hframe := fresh "Hframe" in
  let Hcp := fresh "Hcp" in
  let aa := fresh "aa" in let Haa := fresh "Haa" in
  rd_peel_call Hcp;
  cbv [strong_callee_post_ristretto strong_callee_post_fe25519_sq] in Hcp;
  cbn [loc_var LE_TBytes_r] in Hcp;
  destruct Hcp as [Hframe [aa [Haa Htgt]]];
  pose proof (slot_holds_inj _ _ _ _ Haa Hsrc); subst aa; clear Haa;
  match goal with
  | Hh : rs_get_tower_ed _ v_rd_out = _ |- _ =>
      rewrite (Hframe v_rd_out ltac:(rd_neq)) in Hh
  end;
  rd_reframe Hframe; clear Hframe.

(** One binary fe25519 step ([lem] = the per-op branch Definition);
    source slot facts [Ha], [Hb]. *)
Ltac rd_bin lem Ha Hb :=
  let Hframe := fresh "Hframe" in
  let Hcp := fresh "Hcp" in
  let aa := fresh "aa" in let bb := fresh "bb" in
  let Haa := fresh "Haa" in let Hbb := fresh "Hbb" in
  rd_peel_call Hcp;
  cbv [strong_callee_post_ristretto lem] in Hcp;
  cbn [loc_var LE_TBytes_r] in Hcp;
  destruct Hcp as [Hframe [aa [bb [Haa [Hbb Htgt]]]]];
  pose proof (slot_holds_inj _ _ _ _ Haa Ha); subst aa; clear Haa;
  pose proof (slot_holds_inj _ _ _ _ Hbb Hb); subst bb; clear Hbb;
  match goal with
  | Hh : rs_get_tower_ed _ v_rd_out = _ |- _ =>
      rewrite (Hframe v_rd_out ltac:(rd_neq)) in Hh
  end;
  rd_reframe Hframe; clear Hframe.

(* ================================================================ *)
(* §6b. Rejection-path simulation (Qed).                              *)
(*                                                                    *)
(* The decode-reject path is fully closed: when                       *)
(* [ristretto_parse_canonical_felem bs = None], the decoder writes    *)
(* the 200-byte [ristretto_bad_point], matching the gallina spec.     *)
(* This is the success-path's complement and is term-blowup-free      *)
(* (no field-arithmetic chain), so it lands as a clean Qed.           *)
(* ================================================================ *)

Lemma ristretto_decode_rhoare_reject :
  forall (function_table : function_table_ed)
         (rs1 : rust_state_ed)
         (bs out0 : list Byte.byte),
    length bs = 32%nat ->
    ristretto_parse_canonical_felem bs = None ->
    slot_holds rs1 v_rd_bs bs ->
    rs_get_tower_ed rs1 v_rd_out =
      Some (exist_tval_ed (TBytes 200) (VBytes 200 out0)) ->
    rhoare strong_callee_post_ristretto strong_callee_post_n_ristretto
           function_table rs1 ristretto_decode_rs
      (fun rs' => slot_holds rs' v_rd_out (ristretto_decode_gallina_nlet bs)).
Proof.
  intros function_table rs1 bs out0 Hlen Hreject Hbs Hout.
  unfold ristretto_decode_rs.
  do 26 (apply compile_red_let_zero; intros ? ?).
  set (rs_a := rs_set_tower_ed _ v_rd_t (exist_tval_ed (TBytes 32) v24)) in *.
  assert (Hbs_a : slot_holds rs_a v_rd_bs bs).
  { unfold rs_a. repeat (apply slot_holds_set_tower_other; [rd_neq|]). exact Hbs. }
  assert (Hout_a : rs_get_tower_ed rs_a v_rd_out = Some (exist_tval_ed (TBytes 200) (VBytes 200 out0))).
  { unfold rs_a. repeat (rewrite rs_get_tower_set_other by rd_neq). exact Hout. }
  clearbody rs_a. clear Hbs Hout rs1.
  unfold ristretto_decode_gallina_nlet. rewrite Hreject.
  clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24.
  clear v v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24.
  eapply compile_red_seq.
  { eapply compile_red_calln. intros rs_p Hpp. exact Hpp. }
  intros rs_p Hpp.
  cbv [strong_callee_post_n_ristretto strong_callee_post_ristretto_parse_canonical] in Hpp.
  cbn in Hpp.
  destruct Hpp as [Hframe_s [Hframe_st [_Hne_loc [bs' [Hbs' [Htgt_s Htgt_st]]]]]].
  pose proof (slot_holds_inj _ _ _ _ Hbs' Hbs_a) as Heq; subst bs'. clear Hbs' Hbs_a.
  assert (Hout_p : rs_get_tower_ed rs_p v_rd_out = Some (exist_tval_ed (TBytes 200) (VBytes 200 out0))).
  { rewrite <- (Hframe_st v_rd_out) by rd_neq. exact Hout_a. }
  clear Hframe_s Hframe_st Hout_a rs_a.
  unfold parse_canonical_felem_status_spec in Htgt_st. rewrite Hreject in Htgt_st.
  eapply rhoare_byte_load_seq with (n := 1%nat) (sbs := ["001"%byte]) (idx_v := 0) (b := "001"%byte).
  { cbn. reflexivity. } { reflexivity. } { exact Htgt_st. } { reflexivity. }
  eapply compile_red_if_nz.
  - intros vv Hev Hnz. unfold rd_bad_cmd.
    eapply rhoare_set_bytes_slot with (n := 200%nat); [reflexivity|reflexivity|].
    rewrite map_bad. apply slot_holds_set_tower_same.
  - intros Hev0. cbn in Hev0.
    unfold rs_get_scalar_ed, rs_set_scalar_ed in Hev0. cbn in Hev0.
    rewrite lookup_s_ed_update_at in Hev0. inversion Hev0.
Qed.

(* ================================================================ *)
(* §7. Main rhoare triple.                                            *)
(*                                                                    *)
(* STATUS: the full functional-simulation proof below is logically   *)
(* complete and was validated construct-by-construct interactively   *)
(* (parse dispatch, status byte-check, the 4 verified [REdSetBytes]   *)
(* constants, all 13 [fe25519_*] arithmetic ops, the 2-output         *)
(* sqrt_ratio_m1, the 6 chained muls, the CT [REdSelect] conditional  *)
(* negation, y and t, both bad-point branches).  TWO items remain:    *)
(*                                                                    *)
(*   (1) the [y = 0] check is realised by the [REdFor] byte-sum fold  *)
(*       in the AST; its [compile_red_for] accumulator proof (using   *)
(*       [byte_sum] / [byte_sum_skipn_S] /                            *)
(*       [byte_sum_zero_iff_le_combine] below) is the last [admit];   *)
(*   (2) the assembled proof exceeds practical compile time: each     *)
(*       intermediate field value is carried as a nested [_ mod p]    *)
(*       term and, without the per-step [set]-based value sharing,    *)
(*       the term size blows up (the recurring bedrock2-WP cumulative  *)
(*       large-term issue).  The [set (vV := ...) in *] abstraction    *)
(*       added per step mitigates but the goal/post traversal cost    *)
(*       still pushes the file past the 5-min build budget.           *)
(*                                                                    *)
(* The proof is therefore kept in a BLOCKED comment so the file       *)
(* compiles cleanly (helper lemmas all Qed; ZERO admits, ZERO         *)
(* axioms).  The AST in [Ristretto_RustCmd.ristretto_decode_rs] is    *)
(* the CORRECT faithful decoder (RFC 9496 §3.2.1) and compiles.       *)
(* ================================================================ *)

(* BLOCKED (see status note above): full proof body retained as a
   blueprint; reactivate once (1) the REdFor byte-sum lemma lands and
   (2) the term-sharing performance refactor is complete.
[[
Lemma ristretto_decode_rhoare :
  forall (function_table : function_table_ed)
         (rs1 : rust_state_ed)
         (bs out0 : list Byte.byte),
    length bs = 32%nat ->
    slot_holds rs1 v_rd_bs bs ->
    rs_get_tower_ed rs1 v_rd_out =
      Some (exist_tval_ed (TBytes 200) (VBytes 200 out0)) ->
    rhoare strong_callee_post_ristretto strong_callee_post_n_ristretto
           function_table rs1 ristretto_decode_rs
      (fun rs' => slot_holds rs' v_rd_out (ristretto_decode_gallina_nlet bs)).
Proof.
  intros function_table rs1 bs out0 Hlen Hbs Hout.
  unfold ristretto_decode_rs.
  do 26 (apply compile_red_let_zero; intros ? ?).
  set (rs_a := rs_set_tower_ed _ v_rd_t (exist_tval_ed (TBytes 32) v24)) in *.
  assert (Hbs_a : slot_holds rs_a v_rd_bs bs).
  { unfold rs_a. repeat (apply slot_holds_set_tower_other; [rd_neq|]). exact Hbs. }
  assert (Hout_a : rs_get_tower_ed rs_a v_rd_out = Some (exist_tval_ed (TBytes 200) (VBytes 200 out0))).
  { unfold rs_a. repeat (rewrite rs_get_tower_set_other by rd_neq). exact Hout. }
  clearbody rs_a. clear Hbs Hout rs1.
  unfold ristretto_decode_gallina_nlet.
  clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24.
  clear v v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24.
  (* === parse === *)
  eapply compile_red_seq.
  { eapply compile_red_calln. intros rs_p Hpp. exact Hpp. }
  intros rs_p Hpp.
  cbv [strong_callee_post_n_ristretto strong_callee_post_ristretto_parse_canonical] in Hpp.
  cbn in Hpp.
  destruct Hpp as [Hframe_s [Hframe_st [_Hne_loc [bs' [Hbs' [Htgt_s Htgt_st]]]]]].
  pose proof (slot_holds_inj _ _ _ _ Hbs' Hbs_a) as Heq; subst bs'. clear Hbs' Hbs_a.
  assert (Hout_p : rs_get_tower_ed rs_p v_rd_out = Some (exist_tval_ed (TBytes 200) (VBytes 200 out0))).
  { rewrite <- (Hframe_st v_rd_out) by rd_neq. exact Hout_a. }
  clear Hframe_s Hframe_st Hout_a rs_a.
  unfold parse_canonical_felem_status_spec, parse_canonical_felem_s_spec in *.
  destruct (ristretto_parse_canonical_felem bs) as [s_z|] eqn:Hparse.
  - (* === Some s_z: success-eligible path === *)
    eapply rhoare_byte_load_seq with (n := 1%nat) (sbs := ["000"%byte]) (idx_v := 0) (b := "000"%byte).
    { cbn. reflexivity. } { reflexivity. } { exact Htgt_st. } { reflexivity. }
    eapply compile_red_if_nz.
    + intros vv Hev Hnz. cbn in Hev. unfold rs_get_scalar_ed, rs_set_scalar_ed in Hev. cbn in Hev.
      rewrite lookup_s_ed_update_at in Hev. inversion Hev. subst vv. contradiction.
    + intros _Hev0.
      pose proof (parse_some_range _ _ Hparse) as Hsz_range.
      clear Htgt_st _Hev0.
      (* === constants === *)
      eapply rhoare_set_bytes_seq with (n := 32%nat); [reflexivity|reflexivity|].
      eapply rhoare_set_bytes_seq with (n := 32%nat); [reflexivity|reflexivity|].
      eapply rhoare_set_bytes_seq with (n := 32%nat); [reflexivity|reflexivity|].
      eapply rhoare_set_bytes_seq with (n := 32%nat); [reflexivity|reflexivity|].
      match goal with |- rhoare _ _ _ ?S _ _ => set (rsC := S) end.
      assert (HsC : slot_holds rsC v_rd_s (le_split 32 s_z)).
      { unfold rsC. repeat (apply slot_holds_set_tower_other; [rd_neq|]). exact Htgt_s. }
      assert (HoneC : slot_holds rsC v_rd_one (le_split 32 1)).
      { unfold rsC. repeat (apply slot_holds_set_tower_other; [rd_neq|]).
        rewrite map_const_one, const_one_eq. apply slot_holds_set_tower_same. }
      assert (HtwoC : slot_holds rsC v_rd_two (le_split 32 2)).
      { unfold rsC. repeat (apply slot_holds_set_tower_other; [rd_neq|]).
        rewrite map_const_two, const_two_eq. apply slot_holds_set_tower_same. }
      assert (HpC : slot_holds rsC v_rd_p (le_split 32 ed25519_p)).
      { unfold rsC. repeat (apply slot_holds_set_tower_other; [rd_neq|]).
        rewrite map_const_p. apply slot_holds_set_tower_same. }
      assert (HdC : slot_holds rsC v_rd_d (le_split 32 ed25519_d)).
      { unfold rsC. repeat (apply slot_holds_set_tower_other; [rd_neq|]).
        rewrite map_const_d, const_d_eq. apply slot_holds_set_tower_same. }
      assert (HoutC : rs_get_tower_ed rsC v_rd_out = Some (exist_tval_ed (TBytes 200) (VBytes 200 out0))).
      { unfold rsC. repeat (rewrite rs_get_tower_set_other by rd_neq). exact Hout_p. }
      clearbody rsC. clear Htgt_s Hout_p rs_p.
      cbv [nlet_red RustCmdRupicolaGallina.stack].
      (* === arithmetic chain (each value abstracted via [set] to keep
             terms linear; ranges via [unfold; apply mod_p_range]). === *)
      (* ss = s*s *)
      rd_sq HsC. rewrite (fe_sq_eval s_z Hsz_range) in Htgt.
      set (ssV := (s_z * s_z) mod ed25519_p) in *. rename Htgt into HssC.
      assert (HssR : 0 <= ssV < ed25519_p) by (unfold ssV; apply mod_p_range).
      (* u1 = one - ss *)
      rd_bin strong_callee_post_fe25519_sub HoneC HssC.
      rewrite (fe_sub_eval 1 ssV one_range HssR) in Htgt.
      set (u1V := (1 - ssV) mod ed25519_p) in *. rename Htgt into Hu1C.
      assert (Hu1R : 0 <= u1V < ed25519_p) by (unfold u1V; apply mod_p_range).
      (* u2 = one + ss *)
      rd_bin strong_callee_post_fe25519_add HoneC HssC.
      rewrite (fe_add_eval 1 ssV one_range HssR) in Htgt.
      set (u2V := (1 + ssV) mod ed25519_p) in *. rename Htgt into Hu2C.
      assert (Hu2R : 0 <= u2V < ed25519_p) by (unfold u2V; apply mod_p_range).
      (* u2_sqr = u2*u2 *)
      rd_sq Hu2C. rewrite (fe_sq_eval u2V Hu2R) in Htgt.
      set (u2sqV := (u2V * u2V) mod ed25519_p) in *. rename Htgt into Hu2sqC.
      assert (Hu2sqR : 0 <= u2sqV < ed25519_p) by (unfold u2sqV; apply mod_p_range).
      (* u1_sq = u1*u1 *)
      rd_sq Hu1C. rewrite (fe_sq_eval u1V Hu1R) in Htgt.
      set (u1sqV := (u1V * u1V) mod ed25519_p) in *. rename Htgt into Hu1sqC.
      assert (Hu1sqR : 0 <= u1sqV < ed25519_p) by (unfold u1sqV; apply mod_p_range).
      (* d_u1sq = d * u1_sq *)
      rd_bin strong_callee_post_fe25519_mul HdC Hu1sqC.
      rewrite (fe_mul_eval ed25519_d u1sqV ed25519_d_range Hu1sqR) in Htgt.
      set (du1sqV := (ed25519_d * u1sqV) mod ed25519_p) in *. rename Htgt into Hdu1sqC.
      assert (Hdu1sqR : 0 <= du1sqV < ed25519_p) by (unfold du1sqV; apply mod_p_range).
      (* neg_du1sq = p - d_u1sq *)
      rd_bin strong_callee_post_fe25519_sub HpC Hdu1sqC.
      rewrite (fe_sub_p_eval du1sqV Hdu1sqR) in Htgt.
      set (negV := (ed25519_p - du1sqV) mod ed25519_p) in *. rename Htgt into HnegC.
      assert (HnegR : 0 <= negV < ed25519_p) by (unfold negV; apply mod_p_range).
      (* v = neg_du1sq - u2_sqr *)
      rd_bin strong_callee_post_fe25519_sub HnegC Hu2sqC.
      rewrite (fe_sub_eval negV u2sqV HnegR Hu2sqR) in Htgt.
      set (vV := (negV - u2sqV) mod ed25519_p) in *. rename Htgt into HvC.
      assert (HvR : 0 <= vV < ed25519_p) by (unfold vV; apply mod_p_range).
      (* den = v * u2_sqr *)
      rd_bin strong_callee_post_fe25519_mul HvC Hu2sqC.
      rewrite (fe_mul_eval vV u2sqV HvR Hu2sqR) in Htgt.
      set (denV := (vV * u2sqV) mod ed25519_p) in *. rename Htgt into HdenC.
      assert (HdenR : 0 <= denV < ed25519_p) by (unfold denV; apply mod_p_range).
      (* === sqrt_ratio_m1(one, den) === *)
      eapply compile_red_seq.
      { eapply compile_red_calln. intros rs_q Hqq. exact Hqq. }
      intros rs_q Hqq.
      cbv [strong_callee_post_n_ristretto strong_callee_post_ristretto_sqrt_ratio_m1] in Hqq.
      cbn [loc_var LE_TBytes_r] in Hqq.
      destruct Hqq as [Hframe_ws [Hframe_r [_Hne_wr [ubs [vbs [Hu' [Hv' [Htgt_ws Htgt_I]]]]]]]].
      pose proof (slot_holds_inj _ _ _ _ Hu' HoneC); subst ubs; clear Hu'.
      pose proof (slot_holds_inj _ _ _ _ Hv' HdenC); subst vbs; clear Hv'.
      cbv [sqrt_ratio_m1_was_square_spec sqrt_ratio_m1_r_spec] in Htgt_ws, Htgt_I.
      rewrite !(le_combine_split_p 1 one_range), !(le_combine_split_p denV HdenR) in Htgt_ws, Htgt_I.
      destruct (ristretto_sqrt_ratio_m1 1 denV) as [was_square I_val] eqn:Hsqrt.
      assert (HI_r : 0 <= I_val < ed25519_p).
      { pose proof (sqrt_ratio_m1_snd_range 1 denV) as Hsr.
        rewrite Hsqrt in Hsr. cbn [snd] in Hsr. exact Hsr. }
      cbn [fst snd] in Htgt_ws, Htgt_I.
      rewrite (Hframe_r v_rd_out ltac:(rd_neq)) in HoutC.
      rd_reframe Hframe_r. clear Hframe_r Hframe_ws.
      (* === Dx = I * u2 === *)
      rd_bin strong_callee_post_fe25519_mul Htgt_I Hu2C.
      rewrite (fe_mul_eval I_val u2V HI_r Hu2R) in Htgt.
      set (DxV := (I_val * u2V) mod ed25519_p) in *. rename Htgt into HDxC.
      assert (HDxR : 0 <= DxV < ed25519_p) by (unfold DxV; apply mod_p_range).
      (* === IDx = I * Dx === *)
      rd_bin strong_callee_post_fe25519_mul Htgt_I HDxC.
      rewrite (fe_mul_eval I_val DxV HI_r HDxR) in Htgt.
      set (IDxV := (I_val * DxV) mod ed25519_p) in *. rename Htgt into HIDxC.
      assert (HIDxR : 0 <= IDxV < ed25519_p) by (unfold IDxV; apply mod_p_range).
      (* === Dy = IDx * v  (= I*Dx*v) === *)
      rd_bin strong_callee_post_fe25519_mul HIDxC HvC.
      rewrite (fe_mul_eval IDxV vV HIDxR HvR) in Htgt.
      unfold IDxV in Htgt at 1. rewrite Dy_glue in Htgt.
      set (DyV := (I_val * DxV * vV) mod ed25519_p) in *. rename Htgt into HDyC.
      assert (HDyR : 0 <= DyV < ed25519_p) by (unfold DyV; apply mod_p_range).
      (* === s2 = two * s === *)
      rd_bin strong_callee_post_fe25519_mul HtwoC HsC.
      rewrite (fe_mul_eval 2 s_z two_range Hsz_range) in Htgt.
      set (s2V := (2 * s_z) mod ed25519_p) in *. rename Htgt into Hs2C.
      assert (Hs2R : 0 <= s2V < ed25519_p) by (unfold s2V; apply mod_p_range).
      (* === x_raw = s2 * Dx  (= 2*s*Dx) === *)
      rd_bin strong_callee_post_fe25519_mul Hs2C HDxC.
      rewrite (fe_mul_eval s2V DxV Hs2R HDxR) in Htgt.
      unfold s2V in Htgt at 1. rewrite x_raw_glue in Htgt.
      set (xrV := (2 * s_z * DxV) mod ed25519_p) in *. rename Htgt into HxrawC.
      assert (HxrawR : 0 <= xrV < ed25519_p) by (unfold xrV; apply mod_p_range).
      (* === x_neg = p - x_raw  (= canonical_negate x_raw) === *)
      rd_bin strong_callee_post_fe25519_sub HpC HxrawC.
      rewrite (fe_sub_p_eval xrV HxrawR) in Htgt. rename Htgt into HxnegC.
      (* === xbit = byte0 of x_raw; select === *)
      eapply rhoare_byte_load_seq with (n := 32%nat) (idx_v := 0)
        (sbs := le_split 32 xrV) (b := byte.of_Z xrV).
      { cbn. reflexivity. } { reflexivity. } { exact HxrawC. } { apply nth_error_le_split_0. }
      eapply (rhoare_select_seq _ _ _ _ _ _ _ _ (Z.land (xrV mod 256) 1)); try reflexivity.
      { cbn [eval_sexpr_ed]. unfold rs_get_scalar_ed, rs_set_scalar_ed; cbn.
        rewrite lookup_s_ed_update_at, byteN_of_Z.
        cbn [mask64]. change (Z.land 1 (Z.ones 64)) with 1. reflexivity. }
      intros tv Hgt.
      rewrite land_mod256_1_testbit in Hgt.
      apply slot_holds_tval in HxnegC. destruct HxnegC as [nneg Hxn_neg].
      apply slot_holds_tval in HxrawC. destruct HxrawC as [nraw Hxn_raw].
      match goal with |- rhoare _ _ _ ?S _ _ => set (rsx := S) end.
      assert (HxC : slot_holds rsx v_rd_x
                      (le_split 32 (if ristretto_is_negative xrV then ristretto_canonical_negate xrV else xrV))).
      { unfold ristretto_is_negative in *.
        unfold slot_holds, bytes_at, rsx. rewrite rs_get_tower_set_same_tval.
        rewrite rs_get_tower_set_scalar in Hgt.
        destruct (Z.testbit xrV 0) eqn:Hb; cbn [loc_var LE_TBytes_r Z.eqb] in Hgt.
        - rewrite Hxn_neg in Hgt. inversion Hgt; subst tv.
          unfold ristretto_canonical_negate. reflexivity.
        - rewrite Hxn_raw in Hgt. inversion Hgt; subst tv. reflexivity. }
      clear Hxn_neg Hxn_raw Hgt.
      set (xV := if ristretto_is_negative xrV then ristretto_canonical_negate xrV else xrV) in *.
      assert (HxR : 0 <= xV < ed25519_p).
      { unfold xV. destruct (ristretto_is_negative xrV).
        - unfold ristretto_canonical_negate. apply Z.mod_pos_bound; unfold ed25519_p; lia.
        - exact HxrawR. }
      assert (HoutX : rs_get_tower_ed rsx v_rd_out = Some (exist_tval_ed (TBytes 200) (VBytes 200 out0))).
      { unfold rsx. rewrite rs_get_tower_set_other_tval by rd_neq. exact HoutC. }
      assert (HDyX : slot_holds rsx v_rd_Dy (le_split 32 DyV)).
      { unfold rsx. apply slot_holds_set_tower_other_tval; [rd_neq|]. exact HDyC. }
      assert (Hu1X : slot_holds rsx v_rd_u1 (le_split 32 u1V)).
      { unfold rsx. apply slot_holds_set_tower_other_tval; [rd_neq|]. exact Hu1C. }
      assert (HoneX : slot_holds rsx v_rd_one (le_split 32 1)).
      { unfold rsx. apply slot_holds_set_tower_other_tval; [rd_neq|]. exact HoneC. }
      assert (HwsX : slot_holds rsx v_rd_ws (if was_square then [Byte.x01] else [Byte.x00])).
      { unfold rsx. apply slot_holds_set_tower_other_tval; [rd_neq|]. exact Htgt_ws. }
      clearbody rsx.
      clear Htgt_ws HDyC Hu1C HoneC HsC HtwoC HpC HdC HssC Hu2C Hu2sqC Hu1sqC
            Hdu1sqC HnegC HvC HdenC HDxC HIDxC Hs2C Htgt_I HoutC HxnegC HxrawC.
      (* === y = Dy * u1 === *)
      rd_bin strong_callee_post_fe25519_mul HDyX Hu1X.
      rewrite (fe_mul_eval DyV u1V HDyR Hu1R) in Htgt.
      set (yV := (DyV * u1V) mod ed25519_p) in *. rename Htgt into HyC.
      assert (HyR : 0 <= yV < ed25519_p) by (unfold yV; apply mod_p_range).
      (* === t = x * y === *)
      rd_bin strong_callee_post_fe25519_mul HxC HyC.
      rewrite (fe_mul_eval xV yV HxR HyR) in Htgt.
      set (tV := (xV * yV) mod ed25519_p) in *. rename Htgt into HtC.
      assert (HtR : 0 <= tV < ed25519_p) by (unfold tV; apply mod_p_range).
      (* === failure dispatch: was_square byte === *)
      eapply rhoare_byte_load_seq with (n := 1%nat) (idx_v := 0)
        (sbs := (if was_square then [Byte.x01] else [Byte.x00]))
        (b := (if was_square then Byte.x01 else Byte.x00)).
      { cbn. reflexivity. } { reflexivity. } { exact HwsX. } { destruct was_square; reflexivity. }
      eapply compile_red_if_nz.
      * (* ws byte <> 0 ⇒ was_square = true ⇒ check is_negative(t) *)
        intros vv Hev Hnz.
        cbn [eval_sexpr_ed] in Hev. unfold rs_get_scalar_ed, rs_set_scalar_ed in Hev. cbn in Hev.
        rewrite lookup_s_ed_update_at in Hev.
        assert (Hwst : was_square = true).
        { destruct was_square; [reflexivity|]. cbn in Hev. inversion Hev; subst. contradiction. }
        clear Hev Hnz vv. rewrite Hwst.
        (* t byte0 *)
        eapply rhoare_byte_load_seq with (n := 32%nat) (idx_v := 0)
          (sbs := le_split 32 tV) (b := byte.of_Z tV).
        { cbn. reflexivity. } { reflexivity. } { exact HtC. } { apply nth_error_le_split_0. }
        eapply compile_red_if_nz.
        -- (* is_negative(t) = true ⇒ bad *)
           intros vv2 Hev2 Hnz2. unfold rd_bad_cmd.
           eapply rhoare_set_bytes_slot with (n := 200%nat); [reflexivity|reflexivity|].
           rewrite map_bad.
           cbn [eval_sexpr_ed] in Hev2. unfold rs_get_scalar_ed, rs_set_scalar_ed in Hev2. cbn in Hev2.
           rewrite lookup_s_ed_update_at, byteN_of_Z in Hev2. cbn [mask64] in Hev2.
           change (Z.land 1 (Z.ones 64)) with 1 in Hev2.
           rewrite land_mod256_1_testbit in Hev2. inversion Hev2; subst vv2.
           destruct (ristretto_is_negative tV) eqn:Htneg; [|cbn in Hnz2; congruence].
           rewrite Htneg, orb_true_r, orb_true_l. apply slot_holds_set_tower_same.
        -- (* is_negative(t) = false ⇒ y == 0 check via REdFor *)
           intros Hev20.
           cbn [eval_sexpr_ed] in Hev20. unfold rs_get_scalar_ed, rs_set_scalar_ed in Hev20. cbn in Hev20.
           rewrite lookup_s_ed_update_at, byteN_of_Z in Hev20. cbn [mask64] in Hev20.
           change (Z.land 1 (Z.ones 64)) with 1 in Hev20.
           rewrite land_mod256_1_testbit in Hev20.
           assert (Htneg : ristretto_is_negative tV = false).
           { unfold ristretto_is_negative.
             destruct (Z.testbit tV 0); [inversion Hev20|reflexivity]. }
           clear Hev20.
           (* y==0 check: yacc := 0; for i in 0..32 { yacc += y[i] }; if yacc<>0 pack else bad. *)
           unfold rd_yzero_check.
           eapply compile_red_seq.
           { eapply compile_red_scalar_set with (v := 0). cbn; reflexivity. shelve. }
           intros rs_z Hz0. Unshelve. 2:{ exact (fun rs => rs = rs_set_scalar_ed _ v_rd_yacc 0). }
           cbn beta in Hz0. admit.
      * (* ws byte = 0 ⇒ was_square = false ⇒ bad *)
        intros Hev0.
        cbn [eval_sexpr_ed] in Hev0. unfold rs_get_scalar_ed, rs_set_scalar_ed in Hev0. cbn in Hev0.
        rewrite lookup_s_ed_update_at in Hev0.
        assert (Hwsf : was_square = false).
        { destruct was_square; [cbn in Hev0; inversion Hev0|reflexivity]. }
        unfold rd_bad_cmd.
        eapply rhoare_set_bytes_slot with (n := 200%nat); [reflexivity|reflexivity|].
        rewrite map_bad. rewrite Hwsf. cbn [negb orb]. apply slot_holds_set_tower_same.
  - (* === None: parse rejected ⇒ bad point === *)
    eapply rhoare_byte_load_seq with (n := 1%nat) (sbs := ["001"%byte]) (idx_v := 0) (b := "001"%byte).
    { cbn. reflexivity. } { reflexivity. } { exact Htgt_st. } { reflexivity. }
    eapply compile_red_if_nz.
    + intros vv Hev Hnz. unfold rd_bad_cmd.
      eapply rhoare_set_bytes_slot with (n := 200%nat); [reflexivity|reflexivity|].
      rewrite map_bad. apply slot_holds_set_tower_same.
    + intros Hev0. cbn in Hev0.
      unfold rs_get_scalar_ed, rs_set_scalar_ed in Hev0. cbn in Hev0.
      rewrite lookup_s_ed_update_at in Hev0. inversion Hev0.
Admitted.
]]
*)
