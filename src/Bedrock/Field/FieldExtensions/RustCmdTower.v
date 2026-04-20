(** * RustCmdTower.v
 *
 * Tower-field operations (Fp2, Fp6, Fp12) in rust_cmd, with borrow
 * checking certifying memory safety.
 *
 * Pattern: each operation is defined as a rust_cmd program; one
 * reflexivity call proves borrow_ok; frame theorems follow from
 * borrow_ok_call_frame and call_frame_non_dest.
 *
 * Contrast with DodecicFieldExtensions*.v:
 *   - Current: 400+ lines per file, explicit sep-logic WP proofs
 *   - Here:    borrow_ok checks statically; frame is free
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustBorrowCheck.

(* ================================================================ *)
(* §1. Located-value constructors                                   *)
(* ================================================================ *)

Definition mk_loc (x : string) (t : tower_type) : located :=
  mkLocated x t t (PathNil t).

(** Fp2 variable locations *)
Definition loc_fp2_a   := mk_loc "a"   TFp2.
Definition loc_fp2_b   := mk_loc "b"   TFp2.
Definition loc_fp2_c   := mk_loc "c"   TFp2.
Definition loc_fp2_tmp := mk_loc "tmp" TFp2.
Definition loc_fp2_out := mk_loc "out" TFp2.

(** Fp6 variable locations *)
Definition loc_fp6_a   := mk_loc "a"   TFp6.
Definition loc_fp6_b   := mk_loc "b"   TFp6.
Definition loc_fp6_out := mk_loc "out" TFp6.

(** Fp12 variable locations *)
Definition loc_fp12_a   := mk_loc "a"   TFp12.
Definition loc_fp12_b   := mk_loc "b"   TFp12.
Definition loc_fp12_out := mk_loc "out" TFp12.

(* ================================================================ *)
(* §2. Fp2 operations                                              *)
(* ================================================================ *)

(** fp2_mul(a, b) → out *)
Definition fp2_mul : rust_cmd :=
  RCall "fp2_mul" loc_fp2_out [loc_fp2_a; loc_fp2_b].

(** fp2_add(a, b) → out *)
Definition fp2_add : rust_cmd :=
  RCall "fp2_add" loc_fp2_out [loc_fp2_a; loc_fp2_b].

(** fp2_sqr(a) → out *)
Definition fp2_sqr : rust_cmd :=
  RCall "fp2_sqr" loc_fp2_out [loc_fp2_a].

(** Composed: fp2_mul_add(a,b,c) computes out = fp2_add(fp2_mul(a,b), c) *)
Definition fp2_mul_step : rust_cmd :=
  RCall "fp2_mul" loc_fp2_tmp [loc_fp2_a; loc_fp2_b].

Definition fp2_add_step : rust_cmd :=
  RCall "fp2_add" loc_fp2_out [loc_fp2_tmp; loc_fp2_c].

Definition fp2_mul_add : rust_cmd :=
  RSeq fp2_mul_step fp2_add_step.

(* ================================================================ *)
(* §3. Fp6 operations                                              *)
(* ================================================================ *)

Definition fp6_mul : rust_cmd :=
  RCall "fp6_mul" loc_fp6_out [loc_fp6_a; loc_fp6_b].

Definition fp6_add : rust_cmd :=
  RCall "fp6_add" loc_fp6_out [loc_fp6_a; loc_fp6_b].

(* ================================================================ *)
(* §4. Fp12 operations                                             *)
(* ================================================================ *)

Definition fp12_mul : rust_cmd :=
  RCall "fp12_mul" loc_fp12_out [loc_fp12_a; loc_fp12_b].

Definition fp12_sqr : rust_cmd :=
  RCall "fp12_sqr" loc_fp12_out [loc_fp12_a].

(* ================================================================ *)
(* §5. Borrow checking — one reflexivity each                      *)
(* ================================================================ *)

Example fp2_mul_borrow_ok     : borrow_ok fp2_mul     = true. Proof. reflexivity. Qed.
Example fp2_add_borrow_ok     : borrow_ok fp2_add     = true. Proof. reflexivity. Qed.
Example fp2_sqr_borrow_ok     : borrow_ok fp2_sqr     = true. Proof. reflexivity. Qed.
Example fp2_mul_step_borrow_ok: borrow_ok fp2_mul_step= true. Proof. reflexivity. Qed.
Example fp2_add_step_borrow_ok: borrow_ok fp2_add_step= true. Proof. reflexivity. Qed.
Example fp2_mul_add_borrow_ok : borrow_ok fp2_mul_add = true. Proof. reflexivity. Qed.
Example fp6_mul_borrow_ok     : borrow_ok fp6_mul     = true. Proof. reflexivity. Qed.
Example fp6_add_borrow_ok     : borrow_ok fp6_add     = true. Proof. reflexivity. Qed.
Example fp12_mul_borrow_ok    : borrow_ok fp12_mul    = true. Proof. reflexivity. Qed.
Example fp12_sqr_borrow_ok    : borrow_ok fp12_sqr    = true. Proof. reflexivity. Qed.

(* ================================================================ *)
(* §6. Frame theorems                                              *)
(* ================================================================ *)

Section TowerFrame.

Variable N       : nat.
Variable u64_max : nat.
Variable leaf_spec :
  string ->
  forall (dt : tower_type) (in_ts : list tower_type),
    rust_val dt ->
    list { t : tower_type & rust_val t } ->
    rust_val dt.

(** fp2_mul preserves inputs a and b. *)
Theorem fp2_mul_preserves_inputs :
  forall (rs rs' : rust_state),
    rust_exec N u64_max leaf_spec fp2_mul rs rs' ->
    located_lookup rs' loc_fp2_a = located_lookup rs loc_fp2_a /\
    located_lookup rs' loc_fp2_b = located_lookup rs loc_fp2_b.
Proof.
  intros rs rs' Hexec. split.
  - apply (borrow_ok_call_frame N u64_max leaf_spec
             "fp2_mul" loc_fp2_out [loc_fp2_a; loc_fp2_b]).
    + reflexivity.
    + exact Hexec.
    + left. reflexivity.
  - apply (borrow_ok_call_frame N u64_max leaf_spec
             "fp2_mul" loc_fp2_out [loc_fp2_a; loc_fp2_b]).
    + reflexivity.
    + exact Hexec.
    + right. left. reflexivity.
Qed.

(** fp2_sqr preserves input a. *)
Theorem fp2_sqr_preserves_input :
  forall (rs rs' : rust_state),
    rust_exec N u64_max leaf_spec fp2_sqr rs rs' ->
    located_lookup rs' loc_fp2_a = located_lookup rs loc_fp2_a.
Proof.
  intros rs rs' Hexec.
  apply (borrow_ok_call_frame N u64_max leaf_spec
           "fp2_sqr" loc_fp2_out [loc_fp2_a]).
  - reflexivity.
  - exact Hexec.
  - left. reflexivity.
Qed.

(** fp2_mul_add: a, b, c all preserved across the composed program. *)
Theorem fp2_mul_add_preserves_inputs :
  forall (rs r1 rs' : rust_state),
    rust_exec N u64_max leaf_spec fp2_mul_step rs r1 ->
    rust_exec N u64_max leaf_spec fp2_add_step r1 rs' ->
    located_lookup rs' loc_fp2_a = located_lookup rs loc_fp2_a /\
    located_lookup rs' loc_fp2_b = located_lookup rs loc_fp2_b /\
    located_lookup rs' loc_fp2_c = located_lookup rs loc_fp2_c.
Proof.
  intros rs r1 rs' Hmul Hadd.
  (* fp2_mul_step: a and b preserved *)
  assert (Ha_r1 : located_lookup r1 loc_fp2_a = located_lookup rs loc_fp2_a).
  { apply (borrow_ok_call_frame N u64_max leaf_spec
             "fp2_mul" loc_fp2_tmp [loc_fp2_a; loc_fp2_b]).
    - reflexivity. - exact Hmul. - left. reflexivity. }
  assert (Hb_r1 : located_lookup r1 loc_fp2_b = located_lookup rs loc_fp2_b).
  { apply (borrow_ok_call_frame N u64_max leaf_spec
             "fp2_mul" loc_fp2_tmp [loc_fp2_a; loc_fp2_b]).
    - reflexivity. - exact Hmul. - right. left. reflexivity. }
  (* fp2_mul_step: c preserved (not the dest) *)
  assert (Hc_r1 : located_lookup r1 loc_fp2_c = located_lookup rs loc_fp2_c).
  { apply (call_frame_non_dest N u64_max leaf_spec
             "fp2_mul" loc_fp2_tmp [loc_fp2_a; loc_fp2_b] rs r1 loc_fp2_c Hmul).
    discriminate. }
  (* fp2_add_step: a, b preserved (not dest, not in args) *)
  assert (Ha_rs' : located_lookup rs' loc_fp2_a = located_lookup r1 loc_fp2_a).
  { apply (call_frame_non_dest N u64_max leaf_spec
             "fp2_add" loc_fp2_out [loc_fp2_tmp; loc_fp2_c] r1 rs' loc_fp2_a Hadd).
    discriminate. }
  assert (Hb_rs' : located_lookup rs' loc_fp2_b = located_lookup r1 loc_fp2_b).
  { apply (call_frame_non_dest N u64_max leaf_spec
             "fp2_add" loc_fp2_out [loc_fp2_tmp; loc_fp2_c] r1 rs' loc_fp2_b Hadd).
    discriminate. }
  (* fp2_add_step: c preserved (in args) *)
  assert (Hc_rs' : located_lookup rs' loc_fp2_c = located_lookup r1 loc_fp2_c).
  { apply (borrow_ok_call_frame N u64_max leaf_spec
             "fp2_add" loc_fp2_out [loc_fp2_tmp; loc_fp2_c]).
    - reflexivity. - exact Hadd. - right. left. reflexivity. }
  repeat split.
  - rewrite Ha_rs'. exact Ha_r1.
  - rewrite Hb_rs'. exact Hb_r1.
  - rewrite Hc_rs'. exact Hc_r1.
Qed.

(** fp12_mul preserves inputs. *)
Theorem fp12_mul_preserves_inputs :
  forall (rs rs' : rust_state),
    rust_exec N u64_max leaf_spec fp12_mul rs rs' ->
    located_lookup rs' loc_fp12_a = located_lookup rs loc_fp12_a /\
    located_lookup rs' loc_fp12_b = located_lookup rs loc_fp12_b.
Proof.
  intros rs rs' Hexec. split.
  - apply (borrow_ok_call_frame N u64_max leaf_spec
             "fp12_mul" loc_fp12_out [loc_fp12_a; loc_fp12_b]).
    + reflexivity. + exact Hexec. + left. reflexivity.
  - apply (borrow_ok_call_frame N u64_max leaf_spec
             "fp12_mul" loc_fp12_out [loc_fp12_a; loc_fp12_b]).
    + reflexivity. + exact Hexec. + right. left. reflexivity.
Qed.

End TowerFrame.
