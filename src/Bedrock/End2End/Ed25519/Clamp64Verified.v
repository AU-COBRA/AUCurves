(** * Clamp64Verified — verified [function_body_ed] replacement for
 *                     the axiomatic [clamp_64_spec] leaf.
 *
 *  Paper claim demonstrated by this file:
 *    "Leaves in [strong_callee_post] can be EITHER axiomatic Gallina
 *    specs OR verified [rust_cmd_ed] bodies dispatched through
 *    [REdCallFn] — interchangeably."
 *
 *  This file is standalone (does NOT touch
 *  [Sign_Strong_Correctness.v]).  It establishes:
 *
 *    §1  [clamp_64_gallina : list byte -> list byte]
 *        — concrete RFC-8032 clamping reference (Definition, 0 axioms).
 *
 *    §2  [clamp_64_body    : function_body_ed]
 *        — in-place rust_cmd_ed body matching the
 *          ["clamp_64", []]  branch of [strong_callee_post]
 *          (reads/writes [dst.(loc_var)] in place; args = []).
 *
 *    §3  [clamp_64_body_correct]
 *        — for any [callee_post] / [callee_post_n] / [function_table],
 *          [rust_exec_ed _ _ _ (clamp_64_body dst []) rs1 rs2]
 *          implies that the [dst] slot in [rs2] holds
 *          [clamp_64_gallina in_bs] where [in_bs] is the [dst] slot in
 *          [rs1].  Qed-clean, no axiom dependency.
 *
 *  RFC 8032 clamping (32-byte little-endian scalar [bs]):
 *    bs'[0]  =  bs[0]  AND 0xF8        — clear low 3 bits
 *    bs'[31] = (bs[31] AND 0x7F) OR 0x40
 *               = (bs[31] AND 0x3F) + 0x40   (equivalent — see Note A)
 *    bs'[i]  =  bs[i]                  for 1 ≤ i ≤ 30
 *
 *  Note A: `(b AND 0x7F) OR 0x40 = (b AND 0x3F) + 0x40` because
 *   - bits 0–5 of the result equal bits 0–5 of b in both forms.
 *   - bit 6 is forced to 1 in both forms ((AND 0x7F) preserves bit 6
 *     then OR 0x40 sets it; (AND 0x3F) clears it then +0x40 sets it).
 *   - bit 7 is forced to 0 in both forms.
 *  The [sexpr_ed] AST has SAnd / SAdd but no SOr, hence the +0x40
 *  encoding.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1.  Concrete Gallina reference                                    *)
(* ================================================================ *)

(** Mask a single byte by ANDing with [mask : Z], then truncating
    back to a [byte].  Used for byte 0 (mask = 0xF8). *)
Definition byte_and (b : Byte.byte) (mask : Z) : Byte.byte :=
  Z_to_byte (Z.land (Z.of_N (Byte.to_N b)) mask).

(** Set top two bits of a byte: clear bit 7, set bit 6.
    Implemented as [(b AND 0x3F) + 0x40] — see Note A in header. *)
Definition byte_clamp_top (b : Byte.byte) : Byte.byte :=
  Z_to_byte (Z.land (Z.of_N (Byte.to_N b)) 63 + 64).

(** Reference clamping function — concrete, NOT an axiom. *)
Definition clamp_64_gallina (bs : list Byte.byte) : list Byte.byte :=
  match bs with
  | b0 :: rest =>
      let bs0 := byte_and b0 248 :: rest in
      match List.nth_error bs0 31 with
      | Some b31 => list_set_byte 31 (byte_clamp_top b31) bs0
      | None     => bs0
      end
  | [] => []
  end.

Lemma clamp_64_gallina_length :
  forall bs, length bs = 32%nat -> length (clamp_64_gallina bs) = 32%nat.
Proof.
  intros bs Hlen.
  destruct bs as [|b0 rest]; cbn in Hlen; [discriminate|].
  unfold clamp_64_gallina.
  destruct (List.nth_error (byte_and b0 248 :: rest) 31) eqn:E.
  - rewrite list_set_byte_length. cbn. cbn in Hlen. lia.
  - cbn. cbn in Hlen. lia.
Qed.

(* ================================================================ *)
(* §2.  Verified rust_cmd_ed body                                    *)
(* ================================================================ *)

(** In-place clamp body.  Signature matches the
    ["clamp_64", []] branch of [strong_callee_post] — args is [],
    reads/writes happen on [dst].

    Performs exactly four AST operations:
      1.  Load dst[0]  → "b0_tmp"
      2.  Load dst[31] → "b31_tmp"
      3.  Store dst[0]  := b0_tmp AND 0xF8
      4.  Store dst[31] := (b31_tmp AND 0x3F) + 0x40

    Steps 3 and 4 are independent of each other once the loads are
    done, so the order between them does not matter; we keep this
    fixed sequence for a determinate AST.  *)
Definition clamp_64_body : function_body_ed :=
  fun dst args =>
    match args with
    | [] =>
        REdSeq (REdByteLoad "b0_tmp"  dst (SLit 0))
       (REdSeq (REdByteLoad "b31_tmp" dst (SLit 31))
       (REdSeq (REdByteStore dst (SLit 0)
                  (SAnd (SVar "b0_tmp") (SLit 248)))
               (REdByteStore dst (SLit 31)
                  (SAdd (SAnd (SVar "b31_tmp") (SLit 63))
                        (SLit 64)))))
    | _ => REdSkip   (* defensive — unused on well-typed sites *)
    end.

(* ================================================================ *)
(* §3.  Correctness                                                  *)
(* ================================================================ *)

(** Tower-level read of [dst] before / after a single [REdByteStore]
    on a different (or same) index: helper to keep the main proof
    short. *)

(** Tiny helper: writing to [x] then reading [x] yields the new value. *)
Lemma rs_get_tower_set_same :
  forall rs x v,
    rs_get_tower_ed (rs_set_tower_ed rs x v) x = Some v.
Proof.
  intros rs x v. cbv [rs_get_tower_ed rs_set_tower_ed]. cbn.
  induction (rs_tower_ed rs) as [|[y w] rest IH].
  - cbn. now rewrite String.eqb_refl.
  - cbn. destruct (String.eqb y x) eqn:Eyx.
    + cbn. apply String.eqb_eq in Eyx; subst y.
      now rewrite String.eqb_refl.
    + cbn. rewrite String.eqb_sym. rewrite Eyx. exact IH.
Qed.

(** Scalar-set / tower-read commute. *)
Lemma rs_get_tower_set_scalar :
  forall rs x v y,
    rs_get_tower_ed (rs_set_scalar_ed rs x v) y = rs_get_tower_ed rs y.
Proof.
  intros. cbv [rs_get_tower_ed rs_set_scalar_ed]. reflexivity.
Qed.

(** Scalar-get / scalar-set on the same key. *)
Lemma rs_get_scalar_set_same :
  forall rs x v,
    rs_get_scalar_ed (rs_set_scalar_ed rs x v) x = Some v.
Proof.
  intros rs x v. cbv [rs_get_scalar_ed rs_set_scalar_ed]. cbn.
  induction (rs_scalar_ed rs) as [|[y w] rest IH].
  - cbn. now rewrite String.eqb_refl.
  - cbn. destruct (String.eqb y x) eqn:Eyx.
    + cbn. apply String.eqb_eq in Eyx; subst y.
      now rewrite String.eqb_refl.
    + cbn. rewrite String.eqb_sym. rewrite Eyx. exact IH.
Qed.

(** Scalar-get / scalar-set on different keys. *)
Lemma rs_get_scalar_set_diff :
  forall rs x v y,
    x <> y -> rs_get_scalar_ed (rs_set_scalar_ed rs x v) y =
              rs_get_scalar_ed rs y.
Proof.
  intros rs x v y Hxy. cbv [rs_get_scalar_ed rs_set_scalar_ed]. cbn.
  induction (rs_scalar_ed rs) as [|[z w] rest IH].
  - cbn. destruct (String.eqb y x) eqn:Eyx.
    + apply String.eqb_eq in Eyx. congruence.
    + reflexivity.
  - cbn. destruct (String.eqb z x) eqn:Ezx.
    + cbn. apply String.eqb_eq in Ezx; subst z.
      destruct (String.eqb y x) eqn:Eyx.
      * apply String.eqb_eq in Eyx. congruence.
      * reflexivity.
    + cbn. destruct (String.eqb y z) eqn:Eyz; [reflexivity | exact IH].
Qed.

(** A note on the proof strategy below: each step of the unrolled
    body has a unique inversion lemma; we walk through them with
    [inversion ... ; subst] and accumulate the resulting state
    rewrites. *)

(** Helper: [Z.to_nat (mask64 z)] for small non-negative [z]. *)
Lemma mask64_small : forall z, 0 <= z < 2 ^ 64 -> mask64 z = z.
Proof.
  intros z H. cbv [mask64]. rewrite Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

(** Auxiliary [byte_and] / [byte_clamp_top] equalities used in the
    main proof.  Both expand to [Z_to_byte (...)], matching the
    operand the byte_store will see. *)
Lemma byte_and_eq_Z_to_byte :
  forall b m, byte_and b m =
              Z_to_byte (Z.land (Z.of_N (Byte.to_N b)) m).
Proof. reflexivity. Qed.

Lemma byte_clamp_top_eq_Z_to_byte :
  forall b, byte_clamp_top b =
            Z_to_byte (Z.land (Z.of_N (Byte.to_N b)) 63 + 64).
Proof. reflexivity. Qed.

(** Main correctness theorem. *)
Theorem clamp_64_body_correct :
  forall callee_post callee_post_n function_table
         (dst : located_ed)
         (rs1 rs2 : rust_state_ed)
         (in_bs : list Byte.byte),
    dst.(loc_type) = TBytes 32 ->
    length in_bs = 32%nat ->
    rs_get_tower_ed rs1 dst.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 in_bs)) ->
    rust_exec_ed callee_post callee_post_n function_table
                 (clamp_64_body dst []) rs1 rs2 ->
    rs_get_tower_ed rs2 dst.(loc_var)
      = Some (exist_tval_ed (TBytes 32)
                            (VBytes 32 (clamp_64_gallina in_bs))).
Proof.
  intros callee_post callee_post_n function_table dst rs1 rs2 in_bs
         Htype Hlen Hin Hexec.
  cbv [clamp_64_body] in Hexec.
  (* Helper: lookup_s_ed (update_in_place_s_ed env k v) k = Some v *)
  assert (Hlk_same: forall env k v,
    lookup_s_ed (update_in_place_s_ed env k v) k = Some v).
  { intros env k v. induction env as [|[y w] rest IH].
    - cbn. now rewrite String.eqb_refl.
    - cbn. destruct (String.eqb y k) eqn:E.
      + cbn. apply String.eqb_eq in E. subst.
        now rewrite String.eqb_refl.
      + cbn. rewrite String.eqb_sym. rewrite E. exact IH. }
  (* Helper: lookup_s_ed (update_in_place_s_ed env k v) k' = lookup_s_ed env k'
     when k <> k'. *)
  assert (Hlk_diff: forall env k k' v,
    k <> k' ->
    lookup_s_ed (update_in_place_s_ed env k v) k' = lookup_s_ed env k').
  { intros env k k' v Hkk'. induction env as [|[y w] rest IH].
    - cbn. destruct (String.eqb k' k) eqn:E; [|reflexivity].
      apply String.eqb_eq in E; congruence.
    - cbn. destruct (String.eqb y k) eqn:E.
      + cbn. apply String.eqb_eq in E; subst y.
        destruct (String.eqb k' k) eqn:E2; [|reflexivity].
        apply String.eqb_eq in E2; congruence.
      + cbn. destruct (String.eqb k' y) eqn:E2; [reflexivity | exact IH]. }

  (* Step 1: peel outer REdSeq, then invert REdByteLoad. *)
  inversion Hexec; clear Hexec; subst.
  inversion H1; clear H1; subst.
  cbn in H3.
  inversion H3; clear H3.
  rewrite Htype in H5; inversion H5; subst n; clear H5.
  rewrite Hin in H8; inversion H8; clear H8; subst.
  destruct bs as [|b0 bs_rest]; cbn in Hlen; [discriminate|].
  cbn in H9. inversion H9; subst b0; clear H9.

  (* Step 2: peel next REdSeq, then invert REdByteLoad for "b31_tmp". *)
  inversion H4; clear H4; subst.
  rename H1 into Hstep2.  rename H5 into Hrest2.
  inversion Hstep2; clear Hstep2; subst.
  cbn in H2.
  inversion H2; clear H2.
  rewrite Htype in H3; inversion H3; subst n; clear H3.
  rewrite rs_get_tower_set_scalar in H6.
  rewrite Hin in H6; inversion H6; clear H6; subst.
  cbn in H7.

  (* Step 3: peel next REdSeq, then invert first REdByteStore (dst[0]). *)
  inversion Hrest2; clear Hrest2; subst.
  rename H1 into Hstep3.  rename H4 into Hstep4.
  inversion Hstep3; clear Hstep3; subst.
  cbn in H2. inversion H2; clear H2; subst idx_v.
  cbn in H3.
  (* H3 looks up "b0_tmp" through the chain
     (update (update env "b0_tmp" v0) "b31_tmp" v1).  The outer
     update is on "b31_tmp" (≠ "b0_tmp"), so skip; then Hlk_same. *)
  rewrite (Hlk_diff _ "b31_tmp" "b0_tmp") in H3 by discriminate.
  rewrite Hlk_same in H3.
  cbn in H3. inversion H3; clear H3; subst val_v.
  rewrite Htype in H4; inversion H4; subst n; clear H4.
  do 2 rewrite rs_get_tower_set_scalar in H8.
  rewrite Hin in H8; inversion H8; clear H8; subst.

  (* Step 4: invert REdByteStore (dst[31]). *)
  inversion Hstep4; clear Hstep4; subst.
  cbn in H3.
  rewrite Hlk_same in H3.
  cbn in H3. inversion H3; clear H3; subst val_v.
  cbn in H2. inversion H2; clear H2; subst idx_v.
  rewrite Htype in H4; inversion H4; subst n; clear H4.
  rewrite rs_get_tower_set_same in H8.
  inversion H8; clear H8; subst bs_old.

  (* Compute the final dst slot. *)
  rewrite rs_get_tower_set_same.
  do 2 f_equal.

  (* Reduce both sides to the same [list_set_byte … (… :: bs_rest)] shape. *)
  unfold clamp_64_gallina at 1.
  cbn [nth_error].
  change (PosDef.Pos.to_nat 31) with 31%nat in H7.
  cbn [nth_error] in H7.
  rewrite H7.
  unfold byte_and.
  change (Z.to_nat 31) with 31%nat.
  unfold byte_clamp_top.
  do 3 f_equal.
  apply mask64_small.
  split.
  - assert (0 <= Z.land (Z.of_N (Byte.to_N b0)) 63)
      by (apply Z.land_nonneg; right; lia).
    lia.
  - assert (Hb63 : Z.land (Z.of_N (Byte.to_N b0)) 63 < 64).
    { replace 63 with (Z.ones 6) by reflexivity.
      rewrite Z.land_ones by lia.
      apply Z.mod_pos_bound. lia. }
    lia.
Qed.

(* ================================================================ *)
(* §4.  Test vector                                                  *)
(* ================================================================ *)

(** Concrete input: all bytes = 0xFF.  Expected output:
      byte 0  = 0xFF AND 0xF8 = 0xF8
      byte 31 = (0xFF AND 0x3F) + 0x40 = 0x3F + 0x40 = 0x7F
      bytes 1..30 unchanged (= 0xFF). *)

Definition test_input  : list Byte.byte := List.repeat Byte.xff 32.
Definition test_output : list Byte.byte := clamp_64_gallina test_input.

Lemma test_byte0  : List.nth_error test_output 0  = Some Byte.xf8.
Proof. cbv. reflexivity. Qed.
Lemma test_byte31 : List.nth_error test_output 31 = Some Byte.x7f.
Proof. cbv. reflexivity. Qed.
(** Spot-check a few middle indices instead of universal-quantifying. *)
Lemma test_byte_1  : List.nth_error test_output 1  = Some Byte.xff.
Proof. cbv. reflexivity. Qed.
Lemma test_byte_15 : List.nth_error test_output 15 = Some Byte.xff.
Proof. cbv. reflexivity. Qed.
Lemma test_byte_30 : List.nth_error test_output 30 = Some Byte.xff.
Proof. cbv. reflexivity. Qed.
Lemma test_length : length test_output = 32%nat.
Proof. apply clamp_64_gallina_length. reflexivity. Qed.

(* ================================================================ *)
(* §5.  Print-assumptions guard                                      *)
(* ================================================================ *)

(** Both items below should report "Closed under the global context"
    — confirming the verified body has 0 axiom dependencies. *)
(* Print Assumptions clamp_64_gallina. *)
(* Print Assumptions clamp_64_body_correct. *)
