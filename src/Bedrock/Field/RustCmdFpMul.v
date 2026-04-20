(** * RustCmdFpMul.v
 *
 * Worked example of the rust_cmd + borrow-checker approach for
 * field arithmetic.
 *
 * Demonstrates:
 *   1. Writing a composed field operation directly in [rust_cmd]
 *   2. [borrow_ok] certifying memory safety in one step
 *   3. [borrow_ok_call_frame] deriving that inputs are preserved,
 *      replacing the per-function sep-logic postcondition proofs
 *
 * Example: [fp_mul_add] computes [out = fp_add(fp_mul(a, b), c)].
 * The proof that a, b, c are unchanged after the computation
 * follows entirely from [borrow_ok] — no separation logic needed.
 *
 * Contrast with the current approach (e.g. BLS12Curve_G1.v):
 *   - Current: ~400 lines per function, explicit sep(FElem ptr1 v1)(FElem ptr2 v2)...
 *   - Here:    borrow_ok fp_mul_step = true.  Proof: reflexivity.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustBorrowCheck.

(* ================================================================ *)
(* §1. Located values for named Fp variables                       *)
(* ================================================================ *)

(** A plain Fp variable: no sub-field path, src = dst = TFp. *)
Definition mk_fp_loc (x : string) : located :=
  mkLocated x TFp TFp (PathNil TFp).

Definition loc_a   := mk_fp_loc "a".
Definition loc_b   := mk_fp_loc "b".
Definition loc_c   := mk_fp_loc "c".
Definition loc_tmp := mk_fp_loc "tmp".
Definition loc_out := mk_fp_loc "out".

(* ================================================================ *)
(* §2. The composed program                                        *)
(* ================================================================ *)

(** Step 1: tmp = fp_mul(a, b) *)
Definition fp_mul_step : rust_cmd :=
  RCall "fp_mul" loc_tmp [loc_a; loc_b].

(** Step 2: out = fp_add(tmp, c) *)
Definition fp_add_step : rust_cmd :=
  RCall "fp_add" loc_out [loc_tmp; loc_c].

(** Full computation: out = fp_add(fp_mul(a, b), c) *)
Definition fp_mul_add : rust_cmd :=
  RSeq fp_mul_step fp_add_step.

(* ================================================================ *)
(* §3. Borrow checking — one reflexivity each                      *)
(* ================================================================ *)

(** [borrow_ok] computes statically; each check is a single [reflexivity]. *)
Example fp_mul_step_borrow_ok : borrow_ok fp_mul_step = true.
Proof. reflexivity. Qed.

Example fp_add_step_borrow_ok : borrow_ok fp_add_step = true.
Proof. reflexivity. Qed.

Example fp_mul_add_borrow_ok  : borrow_ok fp_mul_add  = true.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §4. Frame theorems derived from borrow_ok_call_frame            *)
(* ================================================================ *)

Section FpMulFrame.

Variable N       : nat.
Variable u64_max : nat.
Variable leaf_spec :
  string ->
  forall (dt : tower_type) (in_ts : list tower_type),
    rust_val dt ->
    list { t : tower_type & rust_val t } ->
    rust_val dt.

(** After executing fp_mul(a, b) → tmp, the inputs a and b are unchanged.
    This replaces the separation-logic postcondition
    [sep (FElem src1_ptr a) (FElem src2_ptr b) ...] that the current
    WP proofs carry. *)
Theorem fp_mul_step_preserves_inputs :
  forall (rs rs' : rust_state),
    rust_exec N u64_max leaf_spec fp_mul_step rs rs' ->
    located_lookup rs' loc_a = located_lookup rs loc_a /\
    located_lookup rs' loc_b = located_lookup rs loc_b.
Proof.
  intros rs rs' Hexec.
  split.
  - apply (borrow_ok_call_frame N u64_max leaf_spec "fp_mul" loc_tmp [loc_a; loc_b]).
    + reflexivity.
    + exact Hexec.
    + left. reflexivity.
  - apply (borrow_ok_call_frame N u64_max leaf_spec "fp_mul" loc_tmp [loc_a; loc_b]).
    + reflexivity.
    + exact Hexec.
    + right. left. reflexivity.
Qed.

(** After executing fp_add(tmp, c) → out, the inputs tmp and c are unchanged. *)
Theorem fp_add_step_preserves_inputs :
  forall (rs rs' : rust_state),
    rust_exec N u64_max leaf_spec fp_add_step rs rs' ->
    located_lookup rs' loc_tmp = located_lookup rs loc_tmp /\
    located_lookup rs' loc_c   = located_lookup rs loc_c.
Proof.
  intros rs rs' Hexec.
  split.
  - apply (borrow_ok_call_frame N u64_max leaf_spec "fp_add" loc_out [loc_tmp; loc_c]).
    + reflexivity.
    + exact Hexec.
    + left. reflexivity.
  - apply (borrow_ok_call_frame N u64_max leaf_spec "fp_add" loc_out [loc_tmp; loc_c]).
    + reflexivity.
    + exact Hexec.
    + right. left. reflexivity.
Qed.

(** Composition: after the full fp_mul_add program, the original inputs
    a, b, c are all unchanged.

    In the current WP approach this would require composing two
    separation-logic frame applications and carrying 6 pointer
    distinctness hypotheses through a 3-function pre/postcondition
    chain.  Here it follows directly from [borrow_ok_call_frame]
    applied twice. *)
Theorem fp_mul_add_preserves_inputs :
  forall (rs r1 rs' : rust_state),
    rust_exec N u64_max leaf_spec fp_mul_step rs r1 ->
    rust_exec N u64_max leaf_spec fp_add_step r1 rs' ->
    located_lookup rs' loc_a = located_lookup rs loc_a /\
    located_lookup rs' loc_b = located_lookup rs loc_b /\
    located_lookup rs' loc_c = located_lookup rs loc_c.
Proof.
  intros rs r1 rs' Hmul Hadd.
  destruct (fp_mul_step_preserves_inputs rs r1 Hmul) as [Ha_r1 Hb_r1].
  destruct (fp_add_step_preserves_inputs r1 rs' Hadd) as [_ Hc_rs'].
  (* fp_mul_step writes to tmp, so c is preserved across it *)
  assert (Hc_r1 : located_lookup r1 loc_c = located_lookup rs loc_c).
  { apply (call_frame_non_dest N u64_max leaf_spec "fp_mul" loc_tmp [loc_a; loc_b]
                                rs r1 loc_c Hmul).
    discriminate. }
  (* a and b are preserved by fp_add because loc_out.loc_var = "out" ≠ "a","b" *)
  assert (Ha : located_lookup rs' loc_a = located_lookup r1 loc_a).
  { apply (call_frame_non_dest N u64_max leaf_spec "fp_add" loc_out [loc_tmp; loc_c]
                                r1 rs' loc_a Hadd).
    discriminate. }
  assert (Hb : located_lookup rs' loc_b = located_lookup r1 loc_b).
  { apply (call_frame_non_dest N u64_max leaf_spec "fp_add" loc_out [loc_tmp; loc_c]
                                r1 rs' loc_b Hadd).
    discriminate. }
  repeat split.
  - rewrite Ha. exact Ha_r1.
  - rewrite Hb. exact Hb_r1.
  - rewrite Hc_rs'. exact Hc_r1.
Qed.

End FpMulFrame.
