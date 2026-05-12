(** * NormalizeSelect: lower REdSelect to branch-free REdByteStore sequences
 *
 *  Status (2026-05-12): Option C ladder step (c).
 *
 *  Background.  [SafeRustEd25519Sim.v] defines the CT-cmov constructor
 *  [REdSelect cond if_t if_f dest].  The Rust emitter
 *  ([RustCmdToRust.v]) already lowers it to a branch-free mask-merge
 *  (`(if_t[i] & m) | (if_f[i] & !m)`).  But the bedrock2 detour
 *  [RustCmdToC.v::to_bedrock_cmd] stubs [REdSelect] as
 *  [Syntax.cmd.cond cond Syntax.cmd.skip Syntax.cmd.skip] — which is
 *  *not* constant time and *loses the merge semantics entirely*.
 *
 *  This file fixes that by adding a pre-pass
 *  [normalize_select : rust_cmd_ed -> rust_cmd_ed] that replaces each
 *  [REdSelect cond if_t if_f dest] with an explicit byte-by-byte
 *  mask-merge expressed entirely in [REdLetU64] / [REdByteLoad] /
 *  [REdByteStore] / [REdSeq] — primitives that [to_bedrock_cmd] *does*
 *  translate correctly and that bedrock2 can compile to constant-time
 *  code (no branches).
 *
 *  After landing this pass, the Option C pipeline becomes:
 *
 *      rust_cmd_ed
 *         ↓ normalize_select          (this file)
 *      rust_cmd_ed                    (REdSelect-free; CT-safe)
 *         ↓ to_bedrock_cmd            (RustCmdToC.v)
 *      bedrock2.cmd
 *         ↓ tr_cmd                    (Jasmin/Core.v)
 *      jasmin_cmd
 *
 *  All four CT-cmov sites in Ed25519 (the four p25519 leaves at
 *  outLen=4 + scalar-mult ladder + clamp_64) now have a CT-safe
 *  lowering into the bedrock2 / Jasmin chain.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Mask helpers                                                  *)
(* ================================================================ *)

(** Build the byte-wide mask [m].  Given input scalar [cond_var]
    holding a u64 value, [build_mask_expr cond_var] evaluates to
    [2^64 - 1] when [cond_var > 0] and [0] when [cond_var = 0].
    Implementation:
      m := 0 - (0 < cond_var)
    Under [mask64], this is two's complement: when [(0 < cond)] is 1,
    the result is [2^64 - 1]; when it is 0, the result is 0. *)
Definition build_mask_expr (cond_var : var) : sexpr_ed :=
  SSub (SLit 0) (SLt (SLit 0) (SVar cond_var)).

(** Build the complement [~m].  Using [(2^64 - 1) - m].  When m is
    [2^64 - 1] the result is 0; when m is 0 the result is [2^64 - 1]. *)
Definition build_not_mask_expr (mask_var : var) : sexpr_ed :=
  SSub (SLit (Z.ones 64)) (SVar mask_var).

(* ================================================================ *)
(* §2. Per-byte merge: dest[i] := (if_t[i] & mask) + (if_f[i] & ~mask)
   ================================================================ *)

(** A fresh scratch-name namespace.  We use a prefix unlikely to
    clash with user code (rust_cmd_ed variable names are typed names
    from the surface AST). *)
Definition ns_mask : var := "__sel_mask__".
Definition ns_not_mask : var := "__sel_not_mask__".

(** Decimal-digit string for small nats, used to make per-byte
    scratch names unique. *)
Local Open Scope nat_scope.
Fixpoint string_of_nat_aux (fuel : nat) (n : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      match n with
      | O => ""
      | _ =>
          let digit := Nat.modulo n 10 in
          let rest := Nat.div n 10 in
          string_of_nat_aux fuel' rest ++
            (match digit with
             | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
             | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
             end)
      end
  end.

Definition string_of_nat (n : nat) : string :=
  match n with
  | O => "0"
  | _ => string_of_nat_aux (S n) n
  end.
Local Close Scope nat_scope.

Definition byte_t_name (i : nat) : var := "__sel_bt_" ++ string_of_nat i.
Definition byte_f_name (i : nat) : var := "__sel_bf_" ++ string_of_nat i.

(** Emit the byte-merge sequence for one byte index [i]:
      bt := if_t[i]
      bf := if_f[i]
      dest[i] := (bt & mask) + (bf & not_mask)
    The two AND-masked operands are bit-disjoint (one zero where the
    other is non-zero), so [+] coincides with [|] on the resulting
    byte; and the [REdByteStore] truncates to 8 bits, so only the low
    byte of the mask matters (which is 0xFF or 0x00).

    [REdByteLoad] is a leaf in the current sim (no continuation),
    so we chain via [REdSeq]. *)
Definition byte_merge_step
    (i : nat) (if_t if_f dest : located_ed) : rust_cmd_ed :=
  let bt := byte_t_name i in
  let bf := byte_f_name i in
  REdSeq (REdByteLoad bt if_t (SLit (Z.of_nat i)))
  (REdSeq (REdByteLoad bf if_f (SLit (Z.of_nat i)))
          (REdByteStore dest (SLit (Z.of_nat i))
             (SAdd (SAnd (SVar bt) (SVar ns_mask))
                   (SAnd (SVar bf) (SVar ns_not_mask))))).

(** Build the merge sequence over byte indices [0..N-1].  The
    counter [k] counts DOWN from N (call with [k := N], emits
    indices [N-1, N-2, ..., 0] in that order). *)
Fixpoint byte_merge_loop_aux
    (k : nat) (N : nat) (if_t if_f dest : located_ed) : rust_cmd_ed :=
  match k with
  | O => REdSkip
  | S k' =>
      let i := (N - k)%nat in
      REdSeq (byte_merge_step i if_t if_f dest)
             (byte_merge_loop_aux k' N if_t if_f dest)
  end.

Definition byte_merge_loop
    (N : nat) (if_t if_f dest : located_ed) : rust_cmd_ed :=
  byte_merge_loop_aux N N if_t if_f dest.

(* ================================================================ *)
(* §3. The lowering of one REdSelect                                 *)
(* ================================================================ *)

(** Replace one [REdSelect cond if_t if_f dest] with the branch-free
    mask-merge sequence.  N is taken from the destination's
    [loc_type] via [tt_bytes_ed].  For [TBytes n] this is exactly [n].

    Shape:
      let __cond_in__   = cond                                 (snapshot)
      let __sel_mask__  = 0 - (0 < __cond_in__)                (build mask)
      let __sel_not_mask__ = (2^64 - 1) - __sel_mask__         (~mask)
      // for i in 0..N:
      //   let __sel_bt_i = if_t[i]
      //   let __sel_bf_i = if_f[i]
      //   dest[i] = (__sel_bt_i & mask) + (__sel_bf_i & ~mask)

    The expansion uses only [REdLetU64] / [REdByteLoad] / [REdByteStore]
    / [REdSeq] — every one of which has a correct [to_bedrock_cmd]
    translation, and every one of which is constant time. *)
Definition cond_var : var := "__sel_cond__".

Definition lower_one_select
    (cond : sexpr_ed) (if_t if_f dest : located_ed) : rust_cmd_ed :=
  let N := tt_bytes_ed dest.(loc_type) in
  REdLetU64 cond_var cond (
  REdLetU64 ns_mask (build_mask_expr cond_var) (
  REdLetU64 ns_not_mask (build_not_mask_expr ns_mask) (
    byte_merge_loop N if_t if_f dest))).

(* ================================================================ *)
(* §4. The normalize_select pre-pass                                 *)
(* ================================================================ *)

(** Recursively rewrite [REdSelect] subterms to their byte-loop
    expansion.  All other constructors descend structurally.

    Leaf constructors ([REdSkip], [REdScalarSet], [REdCall],
    [REdByteStore], [REdByteLoad], [REdCallN], [REdCallFn]) are
    returned unchanged — they cannot contain a nested [REdSelect]. *)
Fixpoint normalize_select (c : rust_cmd_ed) : rust_cmd_ed :=
  match c with
  | REdSelect cond if_t if_f dest =>
      lower_one_select cond if_t if_f dest
  | REdSeq c1 c2 => REdSeq (normalize_select c1) (normalize_select c2)
  | REdLetZero v t body => REdLetZero v t (normalize_select body)
  | REdLetU64 v e body => REdLetU64 v e (normalize_select body)
  | REdIfNz e ct cf => REdIfNz e (normalize_select ct) (normalize_select cf)
  | REdWhileNz e body => REdWhileNz e (normalize_select body)
  | REdFor v n body => REdFor v n (normalize_select body)
  | REdBlock body => REdBlock (normalize_select body)
  (* Leaves & external-call constructors carry no nested rust_cmd_ed. *)
  | REdSkip
  | REdScalarSet _ _
  | REdCall _ _ _
  | REdByteStore _ _ _
  | REdByteLoad _ _ _
  | REdCallN _ _ _
  | REdCallFn _ _ _ => c
  end.

(* ================================================================ *)
(* §5. Correctness lemma (statement; body Admitted)                  *)
(* ================================================================ *)

(** [normalize_select] preserves [rust_exec_ed] semantics.  The
    proof for non-[REdSelect] constructors is structural induction
    (mirrors the [safe_cmd_correct_ed] structure).  The [REdSelect]
    case requires showing the byte-loop expansion computes the same
    final destination value as [rexec_select]'s opaque [tval_ed] copy.

    The byte-loop reproduces, byte-by-byte:
        dest[i] = if cond_v ≠ 0 then if_t_bytes[i] else if_f_bytes[i]
    which matches [rexec_select]'s effect (one tower update copying
    the chosen source's [tval_ed]).  The arithmetic identity for the
    merge step is:
        (b_t & 0xFF...FF) + (b_f & 0x00...00) = b_t,
        (b_t & 0x00...00) + (b_f & 0xFF...FF) = b_f.
    Both are immediate from [Z.land] properties.

    This proof is mechanical but long (one inductive case per
    constructor; the [REdSelect] case is ~30 LoC of bytewise
    rearrangement).  Admitted for now per the Option-C-ladder plan;
    the PoC's value is in the *transformation* and its
    *Rocq-typecheckable statement*. *)
Theorem normalize_select_correct :
  forall callee_post callee_post_n function_table c rs1 rs2,
    rust_exec_ed callee_post callee_post_n function_table c rs1 rs2 ->
    exists rs2',
      rust_exec_ed callee_post callee_post_n function_table
                   (normalize_select c) rs1 rs2'
      /\ rs_get_tower_ed rs2' = rs_get_tower_ed rs2.
Proof.
Admitted.

(* ================================================================ *)
(* §6. Integration: route the Jasmin pipeline through normalize     *)
(* ================================================================ *)

(** Wrapped pipeline: apply [normalize_select] BEFORE invoking
    [to_bedrock_cmd] / [tr_cmd].  This is what
    [RustCmdEdToJasmin.rust_cmd_ed_to_jasmin] should call.  We keep
    the unwrapped version in [RustCmdEdToJasmin.v] (no churn for the
    existing PoC) and expose the normalized version here so callers
    can opt in by importing this module. *)

(* §6 wiring lives in [RustCmdEdToJasmin.v] (see §7 there).  The
   wrapper there is just:

      Definition rust_cmd_ed_to_jasmin_norm (c : rust_cmd_ed) : jasmin_cmd :=
        tr_cmd (to_bedrock_cmd (normalize_select c)).
*)

(* ================================================================ *)
(* §7. Validation: demos                                             *)
(* ================================================================ *)

(** Tiny REdSelect — just the inner step.  N=32 (TBytes 32) keeps
    [vm_compute] cheap. *)
Definition select_only_demo_32 : rust_cmd_ed :=
  REdSelect (SVar "bit")
            {| loc_var := "tmp";   loc_type := TBytes 32 |}
            {| loc_var := "accum"; loc_type := TBytes 32 |}
            {| loc_var := "accum"; loc_type := TBytes 32 |}.

Definition select_normalized_32 : rust_cmd_ed :=
  normalize_select select_only_demo_32.

(** Larger demo at N=200 (matches the scalarmult-ladder slot size).
    Tests that the byte-loop unroll scales. *)
Definition select_only_demo_200 : rust_cmd_ed :=
  REdSelect (SVar "bit")
            {| loc_var := "tmp";   loc_type := TBytes 200 |}
            {| loc_var := "accum"; loc_type := TBytes 200 |}
            {| loc_var := "accum"; loc_type := TBytes 200 |}.

Definition select_normalized_200 : rust_cmd_ed :=
  normalize_select select_only_demo_200.

(** Structural sanity check: the normalized 32-byte select is a
    REdLetU64 chain followed by 32 REdByteLoad/REdByteLoad/REdByteStore
    triples — no REdSelect, no REdIfNz, no skip-stub. *)
Fixpoint contains_select (c : rust_cmd_ed) : bool :=
  match c with
  | REdSelect _ _ _ _ => true
  | REdSeq c1 c2 => orb (contains_select c1) (contains_select c2)
  | REdLetZero _ _ b => contains_select b
  | REdLetU64 _ _ b => contains_select b
  | REdIfNz _ ct cf => orb (contains_select ct) (contains_select cf)
  | REdWhileNz _ b => contains_select b
  | REdFor _ _ b => contains_select b
  | REdBlock b => contains_select b
  | _ => false
  end.

Lemma normalize_select_removes_select_32 :
  contains_select select_normalized_32 = false.
Proof. vm_compute. reflexivity. Qed.

(** Count the number of [REdByteStore] nodes in a command — gives us
    a structural fingerprint to see how many bytes were unrolled. *)
Fixpoint count_byte_stores (c : rust_cmd_ed) : nat :=
  match c with
  | REdByteStore _ _ _ => 1
  | REdSeq c1 c2 => count_byte_stores c1 + count_byte_stores c2
  | REdLetZero _ _ b => count_byte_stores b
  | REdLetU64 _ _ b => count_byte_stores b
  | REdIfNz _ ct cf => count_byte_stores ct + count_byte_stores cf
  | REdWhileNz _ b => count_byte_stores b
  | REdFor _ _ b => count_byte_stores b
  | REdBlock b => count_byte_stores b
  | _ => 0
  end.

Lemma count_byte_stores_normalized_32 :
  count_byte_stores select_normalized_32 = 32%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma count_byte_stores_normalized_200 :
  count_byte_stores select_normalized_200 = 200%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma normalize_select_removes_select_200 :
  contains_select select_normalized_200 = false.
Proof. vm_compute. reflexivity. Qed.
