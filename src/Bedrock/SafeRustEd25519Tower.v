(** * Ed25519 tower types for the SafeRust simulation
 *
 * Parallel to [SafeRustSimulation.v]'s BLS12 tower (TFp/TFp2/TFp6/TFp12),
 * this module provides the Ed25519-minimal constructor set:
 *   - [TFp25519]   — base field, 5×u64 = 40 bytes (radix-2^51)
 *   - [TFp25519_64] — base field, 4×u64 = 32 bytes (saturated)
 *   - [TFpL25519]  — scalar field (mod L = 2^252 + δ), 4×u64 = 32 bytes
 *   - [TBytes n]   — fixed-size byte array (sigs, pubkeys, msgs)
 *   - [TU64]       — unsigned 64-bit scalar (loop counters / index)
 *
 * Per [R10_RUSTCMD_PORT_PLAN.md], this is a parallel enum to BLS12's
 * [tower_type] (depth-4 tower), since Ed25519 doesn't share the
 * BLS12 tower structure.  Both modules co-exist; clients import
 * whichever they need.
 *
 * Phase J (information-flow / SecretLevel) and Phase D (TFp25519_4Bounded
 * refinement type) are deferred — not needed for R10 functional
 * correctness.
 *
 * Reference: [SafeRustSimulation.v] §1 for the BLS12 analogue.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Init.Byte.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Ed25519 tower type tags                                       *)
(* ================================================================ *)

Inductive tower_type_ed :=
  | TFp25519     (* 5×u64 = 40 bytes (radix-2^51) *)
  | TFp25519_64  (* 4×u64 = 32 bytes (saturated)  *)
  | TFpL25519    (* scalar field, 4×u64 = 32 bytes *)
  | TBytes (n : nat)  (* n-byte fixed array (sigs/pubkeys/msgs) *)
  | TU64.        (* unsigned 64-bit scalar *)

Definition tower_type_ed_eq_dec (t1 t2 : tower_type_ed) :
  {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1, t2;
    try (left; reflexivity);
    try (right; congruence).
  - destruct (Nat.eq_dec n n0).
    + left; subst; reflexivity.
    + right; intro H; apply n1; injection H; trivial.
Defined.

(** Storage byte size for each tower type.  Used by [tt_bytes_ed]
    and by the bedrock2 bridge for sep-state layout. *)
Definition tt_bytes_ed (t : tower_type_ed) : nat :=
  match t with
  | TFp25519     => 40%nat
  | TFp25519_64  => 32%nat
  | TFpL25519    => 32%nat
  | TBytes n     => n
  | TU64         => 8%nat
  end.

(** Unique numeric encoding for determinism proofs.  Each constructor
    occupies a disjoint range of nat (legacy 5 fixed tags then offset
    constructors).  Mirrors Lean's [TowerType.encode]. *)
Definition tt_encode (t : tower_type_ed) : nat :=
  match t with
  | TFp25519     => 1
  | TFp25519_64  => 2
  | TFpL25519    => 3
  | TU64         => 4
  | TBytes n     => 1000 + n
  end.

Lemma tt_encode_inj : forall t1 t2,
  tt_encode t1 = tt_encode t2 -> t1 = t2.
Proof.
  intros [| | | n |] [| | | m |]; cbn; intro H; try discriminate; try reflexivity.
  injection H as Hnm; subst; reflexivity.
Qed.

(* ================================================================ *)
(* §2. Inductive Rust values                                         *)
(* ================================================================ *)

(** Inductive Rust value indexed by its tower type.  Each constructor
    enforces the correct limb count / byte length via a [Prop]
    side-condition (rather than Sigma types — keeps decide_equality
    tractable).  See [R10_RUSTCMD_PORT_PLAN.md] §Q1 for the design
    rationale (predicate over Sigma). *)
Inductive rust_val_ed : tower_type_ed -> Type :=
  | VFp25519     (limbs : list Z) : rust_val_ed TFp25519
  | VFp25519_64  (limbs : list Z) : rust_val_ed TFp25519_64
  | VFpL25519    (limbs : list Z) : rust_val_ed TFpL25519
  | VBytes       (n : nat) (bs : list Byte.byte) : rust_val_ed (TBytes n)
  | VU64         (z : Z)          : rust_val_ed TU64.

(** Well-formedness: limb count / byte length matches the type tag.
    Preserved by all [rust_exec_ed] transitions (proved separately).
    Exposed as a [Prop] rather than baked into [rust_val_ed] so the
    inductive stays decidable-equality-friendly. *)
Definition well_formed_ed {t : tower_type_ed} (v : rust_val_ed t) : Prop :=
  match v with
  | VFp25519 ls    => length ls = 5%nat
  | VFp25519_64 ls => length ls = 4%nat
  | VFpL25519 ls   => length ls = 4%nat
  | VBytes n bs    => length bs = n
  | VU64 _         => True
  end.

(* ================================================================ *)
(* §3. Zero values (for stackalloc initialization)                   *)
(* ================================================================ *)

Fixpoint zero_limbs_ed (k : nat) : list Z :=
  match k with O => [] | S k' => 0 :: zero_limbs_ed k' end.

Lemma zero_limbs_ed_length : forall k, length (zero_limbs_ed k) = k.
Proof. induction k; cbn; congruence. Qed.

Fixpoint zero_bytes_ed (k : nat) : list Byte.byte :=
  match k with O => [] | S k' => Byte.x00 :: zero_bytes_ed k' end.

Lemma zero_bytes_ed_length : forall k, length (zero_bytes_ed k) = k.
Proof. induction k; cbn; congruence. Qed.

Definition vfp25519_zero : rust_val_ed TFp25519 :=
  VFp25519 (zero_limbs_ed 5).

Definition vfp25519_64_zero : rust_val_ed TFp25519_64 :=
  VFp25519_64 (zero_limbs_ed 4).

Definition vfpL25519_zero : rust_val_ed TFpL25519 :=
  VFpL25519 (zero_limbs_ed 4).

Definition vbytes_zero (n : nat) : rust_val_ed (TBytes n) :=
  VBytes n (zero_bytes_ed n).

Definition vu64_zero : rust_val_ed TU64 :=
  VU64 0.

Definition tt_zero_ed (t : tower_type_ed) : rust_val_ed t :=
  match t with
  | TFp25519     => vfp25519_zero
  | TFp25519_64  => vfp25519_64_zero
  | TFpL25519    => vfpL25519_zero
  | TBytes n     => vbytes_zero n
  | TU64         => vu64_zero
  end.

Lemma tt_zero_ed_well_formed : forall t, well_formed_ed (tt_zero_ed t).
Proof.
  destruct t; cbn; try apply zero_limbs_ed_length;
    try apply zero_bytes_ed_length; trivial.
Qed.

(* ================================================================ *)
(* §4. Located values (named storage slots)                          *)
(* ================================================================ *)

(** A located value: a named variable together with its tower type.
    Mirrors Lean's [Located] structure.  Used by [rust_cmd_ed] to
    name source/destination slots in [RAssign] / [RCall] etc. *)
Record located_ed : Type := mkLocated_ed
  { loc_var : String.string;
    loc_type : tower_type_ed }.

Definition located_ed_eq_dec (l1 l2 : located_ed) : {l1 = l2} + {l1 <> l2}.
Proof.
  destruct l1 as [v1 t1], l2 as [v2 t2].
  destruct (String.string_dec v1 v2);
    [ destruct (tower_type_ed_eq_dec t1 t2) | ];
    [ left; congruence | right; congruence | right; congruence ].
Defined.

(* ================================================================ *)
(* §5. Sanity                                                        *)
(* ================================================================ *)

Lemma tt_bytes_ed_TBytes : forall n, tt_bytes_ed (TBytes n) = n.
Proof. reflexivity. Qed.

Lemma well_formed_ed_zero : forall t, well_formed_ed (tt_zero_ed t).
Proof. apply tt_zero_ed_well_formed. Qed.

(** Print Assumptions check: this module should report
    [Closed under the global context] for all definitions and lemmas. *)
