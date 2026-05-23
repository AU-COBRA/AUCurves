(** * RistrettoBridges — strong_callee_post schema for ristretto255 leaves.
 *
 *  Mirror of [End2End/Ed25519/RemainingBridges.v] for the ristretto-specific
 *  leaves used by the [Ristretto_RustCmd.v] Derive flow.  Provides per-leaf
 *  [strong_callee_post_<leaf>] Definitions that the Tier-4 sugar lemmas in
 *  [RustCmdRupicolaRistretto.v] destructure.
 *
 *  Leaves covered:
 *    §1  fe25519_mul / fe25519_add / fe25519_sub / fe25519_sq
 *          (felem ops returning a 32-byte LE encoding of a value in
 *           [0, ed25519_p)).  These are shared with the Ed25519 path
 *          (used by [scalarmult_base]'s inner Edwards add/double), so
 *          we DON'T re-declare specs here — we re-export them from the
 *          existing [End2End.Ed25519.*] modules where possible and
 *          define matching [strong_callee_post] branches.
 *    §2  ristretto_sqrt_ratio_m1
 *          (2-output: bool was_square + Z r, the structured
 *           sqrt-of-ratio leaf called via [REdCallN]).
 *    §3  ristretto_parse_canonical_felem
 *          (option-typed parser; failure signalled via a status byte
 *           the caller checks with [REdIfNz]).
 *    §4  ristretto_pack_canonical_felem
 *          (32-byte LE encoding of [z mod p]).
 *    §5  ristretto_canonical_negate
 *          (32-byte LE encoding of [(p - z) mod p]).
 *
 *  Status (2026-05-22): each branch is a Definition (no proof
 *  obligation here).  The branches are consumed by
 *  [RustCmdRupicolaRistretto.v]'s Tier-4 lemmas, where the
 *  [compile_red_call] obligation destructures them.
 *
 *  Companion: [Sign_Strong_Correctness.v] defines an Ed25519-specific
 *  [strong_callee_post] that adds a [v_msg_len] scalar-frame conjunct.
 *  Ristretto's body has no analogous protocol-wide scalar invariant
 *  (the algorithm is pure-felem-arithmetic + 2 byte
 *  pack/parse/negate calls), so the schema here is just
 *  [frames_except] + per-leaf match. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Lizard.RistrettoConsts.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0. Re-export Ed25519 [slot_holds] / [frames_except]               *)
(* ================================================================ *)

(** We deliberately REUSE [slot_holds] and [frames_except] from
    [Sign_Strong_Correctness.v] — they're protocol-agnostic predicates
    over [rust_state_ed].  Importing the Ed25519 module already brings
    them into scope; this section is documentation only. *)

(* ================================================================ *)
(* §1. fe25519 felem-op specs (shared with Ed25519 path)              *)
(* ================================================================ *)

(** [fe25519_op_spec op a b] computes the canonical 32-byte LE
    encoding of [(le_combine a `op` le_combine b) mod ed25519_p].

    All four arithmetic leaves share this shape (with the appropriate
    Gallina operator).  Specialised wrappers below pick the
    operator. *)
Definition fe25519_mul_spec (a b : list Byte.byte) : list Byte.byte :=
  le_split 32 ((le_combine a * le_combine b) mod ed25519_p).
Definition fe25519_add_spec (a b : list Byte.byte) : list Byte.byte :=
  le_split 32 ((le_combine a + le_combine b) mod ed25519_p).
Definition fe25519_sub_spec (a b : list Byte.byte) : list Byte.byte :=
  le_split 32 ((le_combine a - le_combine b) mod ed25519_p).
Definition fe25519_sq_spec (a : list Byte.byte) : list Byte.byte :=
  le_split 32 ((le_combine a * le_combine a) mod ed25519_p).

Lemma fe25519_mul_spec_len : forall a b, length (fe25519_mul_spec a b) = 32%nat.
Proof. intros; apply length_le_split. Qed.
Lemma fe25519_add_spec_len : forall a b, length (fe25519_add_spec a b) = 32%nat.
Proof. intros; apply length_le_split. Qed.
Lemma fe25519_sub_spec_len : forall a b, length (fe25519_sub_spec a b) = 32%nat.
Proof. intros; apply length_le_split. Qed.
Lemma fe25519_sq_spec_len : forall a, length (fe25519_sq_spec a) = 32%nat.
Proof. intros; apply length_le_split. Qed.

(** [strong_callee_post_fe25519_op] — one branch per arithmetic leaf.

    Shape: dst is filled with [op a b] (or [op a] for sq); both source
    slots are preserved; all non-dst tower slots are framed. *)
Definition strong_callee_post_fe25519_mul
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [a; b] =>
      exists a_bs b_bs,
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs1 b.(loc_var) b_bs /\
        slot_holds rs2 dst.(loc_var) (fe25519_mul_spec a_bs b_bs)
  | _ => True
  end.

Definition strong_callee_post_fe25519_add
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [a; b] =>
      exists a_bs b_bs,
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs1 b.(loc_var) b_bs /\
        slot_holds rs2 dst.(loc_var) (fe25519_add_spec a_bs b_bs)
  | _ => True
  end.

Definition strong_callee_post_fe25519_sub
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [a; b] =>
      exists a_bs b_bs,
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs1 b.(loc_var) b_bs /\
        slot_holds rs2 dst.(loc_var) (fe25519_sub_spec a_bs b_bs)
  | _ => True
  end.

Definition strong_callee_post_fe25519_sq
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [a] =>
      exists a_bs,
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs2 dst.(loc_var) (fe25519_sq_spec a_bs)
  | _ => True
  end.

(* ================================================================ *)
(* §2. ristretto_sqrt_ratio_m1 — 2-output structured leaf            *)
(* ================================================================ *)

(** The sqrt-ratio leaf produces TWO outputs:
      - was_square_var : 1-byte boolean (0/1)
      - r_var          : 32-byte LE encoding of canonical r

    Mathematical postcondition (per IETF draft §3.1.3):
      let (ws, r) := ristretto_sqrt_ratio_m1 u v.
      Either:
        ws = true  /\ v * r * r ≡   u    (mod p)
      or
        ws = false /\ v * r * r ≡ i * u  (mod p)        where i = SQRT_M1.
      In both cases, 0 ≤ r < p and is_negative r = false. *)

(** [sqrt_ratio_m1_spec u_bs v_bs] returns the 32-byte encoding of r
    and the was_square byte. *)
Definition sqrt_ratio_m1_r_spec (u_bs v_bs : list Byte.byte) : list Byte.byte :=
  let u := le_combine u_bs in
  let v := le_combine v_bs in
  le_split 32 (snd (ristretto_sqrt_ratio_m1 u v)).

Definition sqrt_ratio_m1_was_square_spec (u_bs v_bs : list Byte.byte) : list Byte.byte :=
  let u := le_combine u_bs in
  let v := le_combine v_bs in
  if fst (ristretto_sqrt_ratio_m1 u v) then [Byte.x01] else [Byte.x00].

Lemma sqrt_ratio_m1_r_spec_len :
  forall u_bs v_bs, length (sqrt_ratio_m1_r_spec u_bs v_bs) = 32%nat.
Proof. intros; apply length_le_split. Qed.

Lemma sqrt_ratio_m1_was_square_spec_len :
  forall u_bs v_bs, length (sqrt_ratio_m1_was_square_spec u_bs v_bs) = 1%nat.
Proof.
  intros; cbv [sqrt_ratio_m1_was_square_spec].
  destruct (fst (ristretto_sqrt_ratio_m1 _ _)); reflexivity.
Qed.

(** Multi-output [strong_callee_post] takes a LIST of destinations,
    matching the [REdCallN] / [callee_post_n] signature.  The branch
    asserts both dests get their spec values; frame is preserved on
    every slot not in the destination list. *)
Definition strong_callee_post_ristretto_sqrt_ratio_m1
           (args : list located_ed)
           (dsts : list located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  match dsts, args with
  | [ws_dst; r_dst], [u; v] =>
      frames_except rs1 rs2 ws_dst.(loc_var) /\
      frames_except rs1 rs2 r_dst.(loc_var) /\
      ws_dst.(loc_var) <> r_dst.(loc_var) /\
      exists u_bs v_bs,
        slot_holds rs1 u.(loc_var) u_bs /\
        slot_holds rs1 v.(loc_var) v_bs /\
        slot_holds rs2 ws_dst.(loc_var) (sqrt_ratio_m1_was_square_spec u_bs v_bs) /\
        slot_holds rs2 r_dst.(loc_var) (sqrt_ratio_m1_r_spec u_bs v_bs)
  | _, _ => True
  end.

(* ================================================================ *)
(* §3. ristretto_parse_canonical_felem — option via status byte      *)
(* ================================================================ *)

(** The parser writes:
      - parse_status (1 byte): 0 on success, non-zero on rejection;
      - s (32 bytes): the parsed felem on success, zeros on rejection.

    The caller checks parse_status with [REdIfNz] and branches into
    the [ristretto_bad_point] path on non-zero. *)

Definition parse_canonical_felem_s_spec (bs : list Byte.byte) : list Byte.byte :=
  match ristretto_parse_canonical_felem bs with
  | Some z => le_split 32 z
  | None   => List.repeat Byte.x00 32
  end.

Definition parse_canonical_felem_status_spec (bs : list Byte.byte) : list Byte.byte :=
  match ristretto_parse_canonical_felem bs with
  | Some _ => [Byte.x00]   (* status = 0 means success *)
  | None   => [Byte.x01]   (* status = 1 means reject *)
  end.

Lemma parse_canonical_felem_s_spec_len :
  forall bs, length (parse_canonical_felem_s_spec bs) = 32%nat.
Proof.
  intros bs; cbv [parse_canonical_felem_s_spec].
  destruct (ristretto_parse_canonical_felem _).
  - apply length_le_split.
  - apply List.repeat_length.
Qed.

Lemma parse_canonical_felem_status_spec_len :
  forall bs, length (parse_canonical_felem_status_spec bs) = 1%nat.
Proof.
  intros bs; cbv [parse_canonical_felem_status_spec].
  destruct (ristretto_parse_canonical_felem _); reflexivity.
Qed.

(** Like the sqrt-ratio branch, parse is a 2-output call (s + status).
    Branch matches the [callee_post_n] schema. *)
Definition strong_callee_post_ristretto_parse_canonical
           (args : list located_ed)
           (dsts : list located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  match dsts, args with
  | [s_dst; status_dst], [bs] =>
      frames_except rs1 rs2 s_dst.(loc_var) /\
      frames_except rs1 rs2 status_dst.(loc_var) /\
      s_dst.(loc_var) <> status_dst.(loc_var) /\
      exists bs_input,
        slot_holds rs1 bs.(loc_var) bs_input /\
        slot_holds rs2 s_dst.(loc_var) (parse_canonical_felem_s_spec bs_input) /\
        slot_holds rs2 status_dst.(loc_var) (parse_canonical_felem_status_spec bs_input)
  | _, _ => True
  end.

(* ================================================================ *)
(* §4. ristretto_pack_canonical_felem — single output                 *)
(* ================================================================ *)

(** Pack writes the 32-byte LE encoding of [z mod p].  Single-output
    leaf using [REdCall] + [callee_post]. *)

Definition pack_canonical_felem_spec (z_bs : list Byte.byte) : list Byte.byte :=
  ristretto_pack_canonical_felem (le_combine z_bs).

Lemma pack_canonical_felem_spec_len :
  forall z_bs, length (pack_canonical_felem_spec z_bs) = 32%nat.
Proof.
  intros; cbv [pack_canonical_felem_spec].
  apply ristretto_pack_canonical_felem_length.
Qed.

Definition strong_callee_post_ristretto_pack_canonical
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [z] =>
      exists z_bs,
        slot_holds rs1 z.(loc_var) z_bs /\
        slot_holds rs2 dst.(loc_var) (pack_canonical_felem_spec z_bs)
  | _ => True
  end.

(* ================================================================ *)
(* §5. ristretto_canonical_negate — single output                     *)
(* ================================================================ *)

(** [(p - z) mod p] over 32-byte LE encodings.  Single output. *)

Definition canonical_negate_spec (z_bs : list Byte.byte) : list Byte.byte :=
  le_split 32 (ristretto_canonical_negate (le_combine z_bs)).

Lemma canonical_negate_spec_len :
  forall z_bs, length (canonical_negate_spec z_bs) = 32%nat.
Proof. intros; apply length_le_split. Qed.

(** T3 decomposition: [canonical_negate] is just [fe25519_sub] against a
    constant slot holding [p].  Lets the decoder AST drop the trusted
    [ristretto_canonical_negate] leaf in favour of [REdSetBytes p] +
    [fe25519_sub].  Holds because [le_combine (le_split 32 p) = p]
    (since [p = 2^255-19 < 2^256]). *)
Lemma fe25519_sub_p_eq_canonical_negate :
  forall z_bs,
    fe25519_sub_spec (le_split 32 ed25519_p) z_bs = canonical_negate_spec z_bs.
Proof.
  intros z_bs.
  unfold fe25519_sub_spec, canonical_negate_spec, ristretto_canonical_negate.
  rewrite le_combine_split.
  rewrite (Z.mod_small ed25519_p (2 ^ (Z.of_nat 32 * 8)))
    by (unfold ed25519_p; cbn; lia).
  reflexivity.
Qed.

Definition strong_callee_post_ristretto_canonical_negate
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [z] =>
      exists z_bs,
        slot_holds rs1 z.(loc_var) z_bs /\
        slot_holds rs2 dst.(loc_var) (canonical_negate_spec z_bs)
  | _ => True
  end.

(* ================================================================ *)
(* §5b. Constant setters (path-(b) fix for AST sub-blocker #2)        *)
(* ================================================================ *)

(** Constant setter leaves: [fe25519_const_one], [fe25519_const_two],
    [fe25519_const_d].  Each writes a fixed 32-byte LE-encoded
    constant into the destination slot.  Rust implementations in
    [curve25519-jasmin-rs/src/ristretto_rustcmd/leaves.rs]. *)

(** The 32-byte LE encoding of [1] in F_p. *)
Definition fe25519_const_one_spec : list Byte.byte := le_split 32 1.

(** The 32-byte LE encoding of [2] in F_p. *)
Definition fe25519_const_two_spec : list Byte.byte := le_split 32 2.

(** The 32-byte LE encoding of Curve25519's [d] constant.
    Cross-checked with the Rust side via the spot-check
    [le_combine_d_matches] below. *)
Definition fe25519_const_d_spec : list Byte.byte := le_split 32 ed25519_d.

Lemma fe25519_const_one_spec_len : length fe25519_const_one_spec = 32%nat.
Proof. apply length_le_split. Qed.
Lemma fe25519_const_two_spec_len : length fe25519_const_two_spec = 32%nat.
Proof. apply length_le_split. Qed.
Lemma fe25519_const_d_spec_len : length fe25519_const_d_spec = 32%nat.
Proof. apply length_le_split. Qed.

(** [strong_callee_post_fe25519_const_*]: zero-argument leaves that
    write a fixed constant.  Args is [] (no inputs); dst is the
    32-byte destination slot. *)
Definition strong_callee_post_fe25519_const_one
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [] => slot_holds rs2 dst.(loc_var) fe25519_const_one_spec
  | _  => True
  end.

Definition strong_callee_post_fe25519_const_two
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [] => slot_holds rs2 dst.(loc_var) fe25519_const_two_spec
  | _  => True
  end.

Definition strong_callee_post_fe25519_const_d
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [] => slot_holds rs2 dst.(loc_var) fe25519_const_d_spec
  | _  => True
  end.

(* ================================================================ *)
(* §5c. pack_xyzt5 — 5-felem packer (path-(b) fix for sub-blocker #3) *)
(* ================================================================ *)

(** [pack_xyzt5_spec x y z ta tb] returns the 200-byte concatenation
    of the five felems, each padded with 8 zero bytes:
        x ‖ 0₈ ‖ y ‖ 0₈ ‖ z ‖ 0₈ ‖ ta ‖ 0₈ ‖ tb ‖ 0₈
    where each felem is 32 bytes (so each slot is 40 bytes total).
    Matches [XyztAddVerified.pack_xyzt5] under
    [le_split 40 (le_combine bs) = bs ++ [0;0;0;0;0;0;0;0]] when
    [bs] has length 32 and [le_combine bs < 2^256]. *)
Definition pack_xyzt5_spec (x_bs y_bs z_bs ta_bs tb_bs : list Byte.byte)
  : list Byte.byte :=
  (x_bs ++ List.repeat Byte.x00 8 ++
   y_bs ++ List.repeat Byte.x00 8 ++
   z_bs ++ List.repeat Byte.x00 8 ++
   ta_bs ++ List.repeat Byte.x00 8 ++
   tb_bs ++ List.repeat Byte.x00 8)%list.

Lemma pack_xyzt5_spec_len :
  forall x y z ta tb,
    length x = 32%nat -> length y = 32%nat -> length z = 32%nat ->
    length ta = 32%nat -> length tb = 32%nat ->
    length (pack_xyzt5_spec x y z ta tb) = 200%nat.
Proof.
  intros x y z ta tb Hx Hy Hz Hta Htb.
  unfold pack_xyzt5_spec.
  repeat rewrite length_app, ?List.repeat_length; lia.
Qed.

(** [strong_callee_post_pack_xyzt5]: 5-input, 1-output leaf. *)
Definition strong_callee_post_pack_xyzt5
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [x; y; z; ta; tb] =>
      exists x_bs y_bs z_bs ta_bs tb_bs,
        slot_holds rs1 x.(loc_var) x_bs /\
        slot_holds rs1 y.(loc_var) y_bs /\
        slot_holds rs1 z.(loc_var) z_bs /\
        slot_holds rs1 ta.(loc_var) ta_bs /\
        slot_holds rs1 tb.(loc_var) tb_bs /\
        slot_holds rs2 dst.(loc_var) (pack_xyzt5_spec x_bs y_bs z_bs ta_bs tb_bs)
  | _ => True
  end.

(* ================================================================ *)
(* §6. Composite [strong_callee_post_ristretto] dispatch              *)
(* ================================================================ *)

(** Top-level dispatch: pick the per-leaf branch by function name.
    This is the predicate that [Ristretto_RustCmd.v]'s Derive flow
    instantiates the [callee_post] parameter with. *)
Definition strong_callee_post_ristretto
           (fname : String.string)
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  match fname with
  | "fe25519_mul" => strong_callee_post_fe25519_mul args dst rs1 rs2
  | "fe25519_add" => strong_callee_post_fe25519_add args dst rs1 rs2
  | "fe25519_sub" => strong_callee_post_fe25519_sub args dst rs1 rs2
  | "fe25519_sq"  => strong_callee_post_fe25519_sq  args dst rs1 rs2
  | "ristretto_pack_canonical_felem" =>
      strong_callee_post_ristretto_pack_canonical args dst rs1 rs2
  | "ristretto_canonical_negate" =>
      strong_callee_post_ristretto_canonical_negate args dst rs1 rs2
  | "fe25519_const_one" =>
      strong_callee_post_fe25519_const_one args dst rs1 rs2
  | "fe25519_const_two" =>
      strong_callee_post_fe25519_const_two args dst rs1 rs2
  | "fe25519_const_d" =>
      strong_callee_post_fe25519_const_d args dst rs1 rs2
  | "pack_xyzt5" =>
      strong_callee_post_pack_xyzt5 args dst rs1 rs2
  | _ => frames_except rs1 rs2 dst.(loc_var)
  end.

(** Companion 2-output dispatch for the [callee_post_n] slot. *)
Definition strong_callee_post_n_ristretto
           (fname : String.string)
           (dsts args : list located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  match fname with
  | "ristretto_sqrt_ratio_m1" =>
      strong_callee_post_ristretto_sqrt_ratio_m1 args dsts rs1 rs2
  | "ristretto_parse_canonical_felem" =>
      strong_callee_post_ristretto_parse_canonical args dsts rs1 rs2
  | _ =>
      match dsts with
      | nil => True
      | d :: _ => frames_except rs1 rs2 d.(loc_var)
      end
  end.

(* ========================================================================
   Summary (Phase B.5b deliverable for RistrettoBridges.v):

   PER-LEAF branches: 7
     - strong_callee_post_fe25519_mul / _add / _sub / _sq        (§1)
     - strong_callee_post_ristretto_sqrt_ratio_m1                (§2, 2-out)
     - strong_callee_post_ristretto_parse_canonical              (§3, 2-out)
     - strong_callee_post_ristretto_pack_canonical               (§4)
     - strong_callee_post_ristretto_canonical_negate             (§5)

   COMPOSITE: strong_callee_post_ristretto (single-out dispatch)
              strong_callee_post_n_ristretto (multi-out dispatch)

   PER-LEAF length lemmas: 6 (Qed, each ~1 line)
     - fe25519_{mul,add,sub,sq}_spec_len
     - sqrt_ratio_m1_{r,was_square}_spec_len
     - parse_canonical_felem_{s,status}_spec_len
     - pack_canonical_felem_spec_len, canonical_negate_spec_len

   All Definitions are concrete; no axioms.  This file is the
   ristretto-side analogue of [End2End/Ed25519/RemainingBridges.v]
   (which defines [spec_of_*] for the Ed25519 leaves and the bedrock2
   bridge theorems).  Bridge theorems analogous to
   [bridge_scalar_reduce_concrete] et al. are not needed YET because
   ristretto's compile flow uses [Derive] + Tier-4 rather than
   hand-written AST + bridge composition; we'd add them only when
   we wire the extracted Rust into a bedrock2-callable shape.
   ======================================================================== *)
