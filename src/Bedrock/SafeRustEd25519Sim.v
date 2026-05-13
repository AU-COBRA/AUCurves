(** * Ed25519 SafeRust simulation — semantics + bedrock2 bridge
 *
 * Companion to [SafeRustEd25519Tower.v].  Provides:
 *   §1 Rust subset commands (rust_cmd_ed)
 *   §2 Rust state (named slots + tagged values)
 *   §3 Big-step semantics (rust_exec_ed)
 *   §4 bedrock2 bridge (compile_ed25519, state_refine_ed)  — Part B
 *   §5 Simulation theorem (safe_cmd_correct_ed)             — Part B
 *
 * Status (2026-05-08): §1-§3 done.  §4-§5 stubbed (Admitted)
 * for now — Week 1 Day 5-6 deliverable.
 *
 * Reference: [SafeRustSimulation.v] (BLS12 analogue, §3-§5).
 * Plan: [R10_RUSTCMD_PORT_PLAN.md] Week 1.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Rust subset commands                                          *)
(* ================================================================ *)

Definition var := String.string.

(** Tagged value: pairs a tower type with a value of that type. *)
Inductive tval_ed : Type :=
  | exist_tval_ed : forall t, rust_val_ed t -> tval_ed.

(** Symbolic Z-valued expressions used for index/loop scalars + for
    inline computations (e.g., RFC 8032 byte access).  Subset large
    enough for Ed25519's [byte = load1(scalar + (i >> 3))] etc. *)
Inductive sexpr_ed : Type :=
  | SVar    : var -> sexpr_ed              (* lookup u64 named slot *)
  | SLit    : Z -> sexpr_ed                (* literal *)
  | SAdd    : sexpr_ed -> sexpr_ed -> sexpr_ed
  | SSub    : sexpr_ed -> sexpr_ed -> sexpr_ed
  | SMul    : sexpr_ed -> sexpr_ed -> sexpr_ed
  | SShr    : sexpr_ed -> sexpr_ed -> sexpr_ed   (* right shift *)
  | SAnd    : sexpr_ed -> sexpr_ed -> sexpr_ed   (* bitwise and *)
  | SLt     : sexpr_ed -> sexpr_ed -> sexpr_ed   (* x < y → 0/1 *)
  | SLimb   : var -> nat -> sexpr_ed.            (* Phase 0b: read limb [i] of TFp25519 / TFp25519_64
                                                   / TFpL25519 slot named [v] as a Z scalar.  Used
                                                   to express fiat-crypto's radix-2^51 carry chain
                                                   inline rather than via an FFI [REdCall].  When
                                                   [v]'s slot type is not a limb-bearing tower type
                                                   or [i] is out of range, evaluation produces
                                                   [None] (stuck state). *)

(** The Rust subset commands.  Parallel to BLS12 [rust_cmd] in
    [SafeRustSimulation.v:282], adapted to Ed25519 (no Fp tower
    structure, byte buffers / scalar field instead). *)
Inductive rust_cmd_ed :=
  | REdSkip
  | REdSeq      : rust_cmd_ed -> rust_cmd_ed -> rust_cmd_ed
  | REdLetZero  : var -> tower_type_ed -> rust_cmd_ed -> rust_cmd_ed
  | REdLetU64   : var -> sexpr_ed -> rust_cmd_ed -> rust_cmd_ed
  | REdScalarSet : var -> sexpr_ed -> rust_cmd_ed
  | REdCall     : String.string -> located_ed -> list located_ed -> rust_cmd_ed
  | REdIfNz     : sexpr_ed -> rust_cmd_ed -> rust_cmd_ed -> rust_cmd_ed
  | REdWhileNz  : sexpr_ed -> rust_cmd_ed -> rust_cmd_ed
  | REdByteStore : located_ed -> sexpr_ed -> sexpr_ed -> rust_cmd_ed
                            (* dst[idx] := byte_value *)
  | REdByteLoad : var -> located_ed -> sexpr_ed -> rust_cmd_ed
                            (* x : u64 := src[idx] *)
  | REdFor : var -> nat -> rust_cmd_ed -> rust_cmd_ed
                            (* for x in 0..n { body } — counts up 0..n-1 *)
  | REdSelect : sexpr_ed -> located_ed -> located_ed -> located_ed -> rust_cmd_ed
                            (* CT conditional move:
                               REdSelect cond if_true if_false dest
                               If [cond] is non-zero, copy [if_true] to [dest]; else copy
                               [if_false] to [dest].  All three locations must share
                               [loc_type].  In real Rust output this becomes a
                               [subtle::ConditionallySelectable]-style mask-merge — the
                               two source values are ALWAYS read, no branch on cond. *)
  | REdCallN  : String.string -> list located_ed -> list located_ed -> rust_cmd_ed
                            (* Multi-output FFI call:
                               REdCallN fname dests args
                               Generalises [REdCall] to multiple destinations written
                               by a single call (e.g. ed25519_decompress_split_xy
                               writing both X and Y).  The borrow check
                               ([call_aliases_n_ed]) requires dests pairwise distinct
                               AND no dest name appearing in args. *)
  | REdCallFn : String.string -> located_ed -> list located_ed -> rust_cmd_ed
                            (* Verified-helper-function call:
                               REdCallFn fname dest args
                               Same surface as [REdCall], but the body is looked
                               up in a [function_table] (third Section parameter
                               of [rust_exec_ed]) and executed by inlining the
                               body's [rust_cmd_ed].  Lets us discharge a
                               leaf's correctness mechanically (rhoare of the
                               body) instead of axiomatically (callee_post).
                               Roadmap Tier 6 (2). *)
  | REdBlock  : rust_cmd_ed -> rust_cmd_ed
                            (* Scoped-allocation block: REdBlock body
                               executes [body] in a fresh lexical scope.
                               Semantically transparent — same big-step
                               behaviour as [body] alone — but the Rust /
                               C emitters wrap [body] in a [{ ... }]
                               block so that any [REdLetZero] declared
                               inside has its lifetime end at the closing
                               brace.  This matches Rust's block-scoped
                               variables and CatCrypt's [RBlock].
                               Roadmap Tier 6 (3). *)
  | REdSetBytes : located_ed -> list Z -> rust_cmd_ed
                            (* Whole-array byte-list write:
                               REdSetBytes loc bytes
                               Initializes a [TBytes n] slot with the
                               given list of Z values (each truncated to
                               a single byte via [Z_to_byte]).  Length
                               mismatch (|bytes| ≠ n) is a stuck state
                               (no semantic rule fires).  In emitted
                               Rust this is a single
                               [loc = [b0u8, b1u8, ..., bN-1u8];]
                               literal-array assignment — replaces the
                               paste-through shims for hand-coded
                               constants like [B_COMPRESSED_LE] and
                               [L_EXTRA_LE].  Mirrors Lean's
                               [RLimbStore].  Additive: existing IR
                               programs are unaffected. *)
  | REdArrLoad  : located_ed -> located_ed -> sexpr_ed -> rust_cmd_ed
                            (* Array-of-slots read:
                               REdArrLoad dst src idx_expr
                               [dst := src[eval idx_expr]].  Requires
                               [src.loc_type = TArr n t] and
                               [dst.loc_type = t].  Mirrors Lean's
                               [RArrLoad].  Additive: existing IR
                               programs are unaffected. *)
  | REdArrStore : located_ed -> sexpr_ed -> located_ed -> rust_cmd_ed
                            (* Array-of-slots write:
                               REdArrStore arr idx_expr src
                               [arr[eval idx_expr] := src].  Requires
                               [arr.loc_type = TArr n t] and
                               [src.loc_type = t].  Mirrors Lean's
                               [RArrStore].  Additive: existing IR
                               programs are unaffected. *)
  | REdLimbStore : located_ed -> nat -> sexpr_ed -> rust_cmd_ed.
                            (* Phase 0b limb-level write into a limb-
                               bearing tower slot (TFp25519 /
                               TFp25519_64 / TFpL25519).
                               REdLimbStore loc i e
                               [loc.limbs[i] := eval e].  Combined with
                               the [SLimb v i] sexpr (reads limb [i] of
                               [v]), this pair gives the IR enough power
                               to express fiat-crypto's bedrock2
                               carry-chain bodies for [fe25519_add],
                               [fe25519_sub], [fe25519_mul], etc.
                               inline, without an [extern "C"] call.
                               Phase 0b scaffold (2026-05-13): semantics
                               implemented for [TFp25519]; other types
                               leave the slot untouched (no-op).  Other
                               IR passes (BorrowCheck, NormalizeSelect,
                               InlineCallFn, RustCmdToC, RustCmdToRust)
                               carry trivial stub cases — see those
                               files for the per-pass treatment. *)

(* ================================================================ *)
(* §2. Rust state                                                    *)
(* ================================================================ *)

Record rust_state_ed := mkRustState_ed
  { rs_tower_ed  : list (var * tval_ed);
    rs_scalar_ed : list (var * Z) }.

Definition rs_empty_ed : rust_state_ed :=
  {| rs_tower_ed := []; rs_scalar_ed := [] |}.

Fixpoint lookup_t_ed (env : list (var * tval_ed)) (x : var) : option tval_ed :=
  match env with
  | [] => None
  | (y, v) :: rest => if String.eqb x y then Some v else lookup_t_ed rest x
  end.

Fixpoint lookup_s_ed (env : list (var * Z)) (x : var) : option Z :=
  match env with
  | [] => None
  | (y, v) :: rest => if String.eqb x y then Some v else lookup_s_ed rest x
  end.

Definition rs_get_tower_ed (rs : rust_state_ed) (x : var) : option tval_ed :=
  lookup_t_ed (rs_tower_ed rs) x.

Definition rs_get_scalar_ed (rs : rust_state_ed) (x : var) : option Z :=
  lookup_s_ed (rs_scalar_ed rs) x.

Fixpoint update_in_place_ed (env : list (var * tval_ed)) (x : var) (v : tval_ed)
    : list (var * tval_ed) :=
  match env with
  | [] => [(x, v)]
  | (y, w) :: rest =>
      if String.eqb y x then (x, v) :: rest
      else (y, w) :: update_in_place_ed rest x v
  end.

Definition rs_set_tower_ed (rs : rust_state_ed) (x : var) (v : tval_ed)
    : rust_state_ed :=
  {| rs_tower_ed := update_in_place_ed (rs_tower_ed rs) x v;
     rs_scalar_ed := rs_scalar_ed rs |}.

Fixpoint update_in_place_s_ed (env : list (var * Z)) (x : var) (v : Z)
    : list (var * Z) :=
  match env with
  | [] => [(x, v)]
  | (y, w) :: rest =>
      if String.eqb y x then (x, v) :: rest
      else (y, w) :: update_in_place_s_ed rest x v
  end.

Definition rs_set_scalar_ed (rs : rust_state_ed) (x : var) (v : Z)
    : rust_state_ed :=
  {| rs_tower_ed := rs_tower_ed rs;
     rs_scalar_ed := update_in_place_s_ed (rs_scalar_ed rs) x v |}.

(* ================================================================ *)
(* §3. sexpr evaluation                                              *)
(* ================================================================ *)

(** 64-bit mask for keeping eval_sexpr_ed results in [0, 2^64) so they
    are preserved by [state_refine_ed]'s scalar invariant
    ([word.unsigned w = v]).  All arithmetic operations are masked;
    SLt produces 0/1; SVar reads bounded scalars; SLit users should
    use values in range. *)
Definition mask64 (z : Z) : Z := Z.land z (Z.ones 64).

Fixpoint eval_sexpr_ed (rs : rust_state_ed) (e : sexpr_ed) : option Z :=
  match e with
  | SVar x => rs_get_scalar_ed rs x
  | SLit z => Some (mask64 z)
  | SAdd a b =>
      match eval_sexpr_ed rs a, eval_sexpr_ed rs b with
      | Some va, Some vb => Some (mask64 (va + vb))
      | _, _ => None
      end
  | SSub a b =>
      match eval_sexpr_ed rs a, eval_sexpr_ed rs b with
      | Some va, Some vb => Some (mask64 (va - vb))
      | _, _ => None
      end
  | SMul a b =>
      match eval_sexpr_ed rs a, eval_sexpr_ed rs b with
      | Some va, Some vb => Some (mask64 (va * vb))
      | _, _ => None
      end
  | SShr a b =>
      match eval_sexpr_ed rs a, eval_sexpr_ed rs b with
      | Some va, Some vb => Some (Z.shiftr va vb)
      | _, _ => None
      end
  | SAnd a b =>
      match eval_sexpr_ed rs a, eval_sexpr_ed rs b with
      | Some va, Some vb => Some (Z.land va vb)
      | _, _ => None
      end
  | SLt a b =>
      match eval_sexpr_ed rs a, eval_sexpr_ed rs b with
      | Some va, Some vb => Some (if Z.ltb va vb then 1 else 0)
      | _, _ => None
      end
  | SLimb v i =>
      (* Phase 0b: read limb [i] from the limb-bearing tower slot
         named [v].  Three variants of "limb-bearing tower type" are
         supported: [TFp25519] (5 × u64 radix-2^51), [TFp25519_64]
         (4 × u64 saturated), and [TFpL25519] (4 × u64 group-order
         representative).  Out-of-range / wrong-type / missing-slot
         yields [None].  The returned limb value is masked through
         [mask64] so the bounded-eval lemma stays uniform — the
         real radix-2^51 representation has each limb in
         [0, 2^51 + slack), which is preserved by [mask64]. *)
      match rs_get_tower_ed rs v with
      | Some (exist_tval_ed TFp25519     (VFp25519     limbs)) =>
          match List.nth_error limbs i with
          | Some z => Some (mask64 z)
          | None => None
          end
      | Some (exist_tval_ed TFp25519_64  (VFp25519_64  limbs)) =>
          match List.nth_error limbs i with
          | Some z => Some (mask64 z)
          | None => None
          end
      | Some (exist_tval_ed TFpL25519    (VFpL25519    limbs)) =>
          match List.nth_error limbs i with
          | Some z => Some (mask64 z)
          | None => None
          end
      | _ => None
      end
  end.

(** Eval results are always in [0, 2^64) when scalar values are bounded.
    The hypothesis "scalar values are bounded" is supplied at use sites
    by [state_refine_ed]'s second component, whose witness
    [word.unsigned w = v] implies [v ∈ [0, 2^64)]. *)
Lemma mask64_bounded : forall z, 0 <= mask64 z < 2^64.
Proof.
  intros z. unfold mask64. rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

(** Helper: bounded numbers stay bounded under [Z.land]. *)
Lemma Z_land_bounded :
  forall a b n, 0 <= n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.land a b < 2^n.
Proof.
  intros a b n Hn [Ha1 Ha2] [Hb1 Hb2].
  split.
  - apply Z.land_nonneg. left. exact Ha1.
  - rewrite <- (Z.mod_small a (2^n)) by lia.
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc.
    rewrite (Z.land_comm (Z.ones n) b).
    rewrite Z.land_assoc.
    rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma eval_sexpr_ed_bounded :
  forall rs e v,
    (forall x v', rs_get_scalar_ed rs x = Some v' -> 0 <= v' < 2^64) ->
    eval_sexpr_ed rs e = Some v ->
    0 <= v < 2^64.
Proof.
  intros rs e. induction e as [x|z|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2|
                               e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2|vlimb i];
    intros vv Hbnd Heval; cbn in Heval.
  - (* SVar *) eapply Hbnd; eauto.
  - (* SLit *) inversion Heval; subst. apply mask64_bounded.
  - (* SAdd *)
    destruct (eval_sexpr_ed rs e1) as [va|] eqn:Hva; [|discriminate].
    destruct (eval_sexpr_ed rs e2) as [vb|] eqn:Hvb; [|discriminate].
    inversion Heval; subst. apply mask64_bounded.
  - (* SSub *)
    destruct (eval_sexpr_ed rs e1) as [va|] eqn:Hva; [|discriminate].
    destruct (eval_sexpr_ed rs e2) as [vb|] eqn:Hvb; [|discriminate].
    inversion Heval; subst. apply mask64_bounded.
  - (* SMul *)
    destruct (eval_sexpr_ed rs e1) as [va|] eqn:Hva; [|discriminate].
    destruct (eval_sexpr_ed rs e2) as [vb|] eqn:Hvb; [|discriminate].
    inversion Heval; subst. apply mask64_bounded.
  - (* SShr *)
    destruct (eval_sexpr_ed rs e1) as [va|] eqn:Hva; [|discriminate].
    destruct (eval_sexpr_ed rs e2) as [vb|] eqn:Hvb; [|discriminate].
    inversion Heval; subst.
    specialize (IHe1 va Hbnd eq_refl).
    specialize (IHe2 vb Hbnd eq_refl).
    rewrite Z.shiftr_div_pow2 by lia.
    split.
    + apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
    + apply Z.le_lt_trans with va; [|lia].
      apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia |].
      assert (Hpvb : 0 < 2^vb) by (apply Z.pow_pos_nonneg; lia).
      nia.
  - (* SAnd *)
    destruct (eval_sexpr_ed rs e1) as [va|] eqn:Hva; [|discriminate].
    destruct (eval_sexpr_ed rs e2) as [vb|] eqn:Hvb; [|discriminate].
    inversion Heval; subst.
    specialize (IHe1 va Hbnd eq_refl).
    specialize (IHe2 vb Hbnd eq_refl).
    apply Z_land_bounded; lia.
  - (* SLt *)
    destruct (eval_sexpr_ed rs e1) as [va|] eqn:Hva; [|discriminate].
    destruct (eval_sexpr_ed rs e2) as [vb|] eqn:Hvb; [|discriminate].
    inversion Heval; subst.
    destruct (Z.ltb va vb); split; lia.
  - (* SLimb vlimb i: masked through mask64 above *)
    destruct (rs_get_tower_ed rs vlimb) as [[t' tv]|] eqn:Hgt; try discriminate.
    destruct t'; try discriminate;
      destruct tv; try discriminate;
      destruct (List.nth_error limbs i) as [z|] eqn:Hnth; try discriminate;
      inversion Heval; subst; apply mask64_bounded.
Qed.

(** The earlier [eval_sexpr_ed_bounded_for_arith] placeholder is
    superseded by [eval_sexpr_ed_bounded] above — call sites should
    derive the scalar-bound hypothesis from [state_refine_ed] (whose
    second component supplies [word.unsigned w = v], hence
    [0 <= v < 2^64]). *)

(* ================================================================ *)
(* §3.5. Byte-list helpers (used in byte-mem semantics)              *)
(* ================================================================ *)

Fixpoint list_set_byte (idx : nat) (b : Byte.byte) (bs : list Byte.byte)
    : list Byte.byte :=
  match bs, idx with
  | [], _ => []
  | _ :: rest, O => b :: rest
  | x :: rest, S k => x :: list_set_byte k b rest
  end.

Lemma list_set_byte_length : forall idx b bs,
  length (list_set_byte idx b bs) = length bs.
Proof. induction idx; intros; destruct bs; cbn; auto. Qed.

(** Phase Ext (2026-05-12): replace the [idx]th element of [xs] with
    [x].  Used by [REdArrStore].  Out-of-range index leaves the list
    unchanged (matches [list_set_byte]'s pattern). *)
Fixpoint list_set {A : Type} (idx : nat) (x : A) (xs : list A) : list A :=
  match xs, idx with
  | [], _ => []
  | _ :: rest, O => x :: rest
  | y :: rest, S k => y :: list_set k x rest
  end.

Lemma list_set_length : forall {A} idx (x : A) xs,
  length (list_set idx x xs) = length xs.
Proof. induction idx; intros; destruct xs; cbn; auto. Qed.

(** Truncate a Z to a single byte (mod 256). *)
Definition Z_to_byte (z : Z) : Byte.byte :=
  match Byte.of_N (Z.to_N (Z.modulo z 256)) with
  | Some b => b
  | None => Byte.x00
  end.

(* ================================================================ *)
(* §3.6. Verified-function bodies (used by REdCallFn)                 *)
(* ================================================================ *)

(** A verified function body is parameterized over its destination
    slot and the (positional) argument slots; the body returns a
    [rust_cmd_ed] that, when executed, realizes the function. *)
Definition function_body_ed : Type :=
  located_ed -> list located_ed -> rust_cmd_ed.

(** A function table maps a function name to its body.  Used by
    [rexec_callfn] to look up and inline the body of a verified
    helper. *)
Definition function_table_ed : Type :=
  list (String.string * function_body_ed).

(* ================================================================ *)
(* §4. Big-step semantics                                            *)
(* ================================================================ *)

(** [rust_exec_ed c rs1 rs2]: command [c] takes state [rs1] to state
    [rs2].  External calls (REdCall) are handled by an oracle —
    parameterized over a per-callee post relation.  Multi-output
    calls (REdCallN) use a parallel oracle [callee_post_n] taking
    a LIST of destinations (additive — keeps the existing
    [callee_post] untouched so all REdCall proofs remain Qed).
    Verified-helper calls (REdCallFn) look up a body in
    [function_table] (third Section parameter) and execute it
    inline (additive — REdCall and REdCallN remain unchanged). *)
Inductive rust_exec_ed
  (callee_post :
    String.string ->
    list located_ed ->
    located_ed ->
    rust_state_ed ->
    rust_state_ed ->
    Prop)
  (callee_post_n :
    String.string ->
    list located_ed ->        (* dests *)
    list located_ed ->        (* args *)
    rust_state_ed ->
    rust_state_ed ->
    Prop)
  (function_table : function_table_ed)
  : rust_cmd_ed -> rust_state_ed -> rust_state_ed -> Prop :=
  | rexec_skip : forall rs,
      rust_exec_ed callee_post callee_post_n function_table REdSkip rs rs
  | rexec_seq : forall c1 c2 rs1 rs2 rs3,
      rust_exec_ed callee_post callee_post_n function_table c1 rs1 rs2 ->
      rust_exec_ed callee_post callee_post_n function_table c2 rs2 rs3 ->
      rust_exec_ed callee_post callee_post_n function_table (REdSeq c1 c2) rs1 rs3
  | rexec_let_zero : forall x t v c rs1 rs2,
      well_formed_ed v ->
      rust_exec_ed callee_post callee_post_n function_table c
        (rs_set_tower_ed rs1 x (exist_tval_ed t v))
        rs2 ->
      rust_exec_ed callee_post callee_post_n function_table (REdLetZero x t c) rs1 rs2
  | rexec_let_u64 : forall x e c rs1 rs2 v,
      eval_sexpr_ed rs1 e = Some v ->
      rust_exec_ed callee_post callee_post_n function_table c (rs_set_scalar_ed rs1 x v) rs2 ->
      rust_exec_ed callee_post callee_post_n function_table (REdLetU64 x e c) rs1 rs2
  | rexec_scalar_set : forall x e rs v,
      eval_sexpr_ed rs e = Some v ->
      rust_exec_ed callee_post callee_post_n function_table (REdScalarSet x e) rs (rs_set_scalar_ed rs x v)
  | rexec_call : forall fname dst args rs1 rs2,
      callee_post fname args dst rs1 rs2 ->
      rust_exec_ed callee_post callee_post_n function_table (REdCall fname dst args) rs1 rs2
  | rexec_if_zero : forall e c1 c2 rs1 rs2,
      eval_sexpr_ed rs1 e = Some 0 ->
      rust_exec_ed callee_post callee_post_n function_table c2 rs1 rs2 ->
      rust_exec_ed callee_post callee_post_n function_table (REdIfNz e c1 c2) rs1 rs2
  | rexec_if_nonzero : forall e c1 c2 rs1 rs2 v,
      eval_sexpr_ed rs1 e = Some v ->
      v <> 0 ->
      rust_exec_ed callee_post callee_post_n function_table c1 rs1 rs2 ->
      rust_exec_ed callee_post callee_post_n function_table (REdIfNz e c1 c2) rs1 rs2
  | rexec_while_zero : forall e c rs,
      eval_sexpr_ed rs e = Some 0 ->
      rust_exec_ed callee_post callee_post_n function_table (REdWhileNz e c) rs rs
  | rexec_while_nonzero : forall e c rs1 rs2 rs3 v,
      eval_sexpr_ed rs1 e = Some v ->
      v <> 0 ->
      rust_exec_ed callee_post callee_post_n function_table c rs1 rs2 ->
      rust_exec_ed callee_post callee_post_n function_table (REdWhileNz e c) rs2 rs3 ->
      rust_exec_ed callee_post callee_post_n function_table (REdWhileNz e c) rs1 rs3
  | rexec_byte_store : forall loc idx_e val_e rs idx_v val_v bs_old bs_new n,
      eval_sexpr_ed rs idx_e = Some idx_v ->
      eval_sexpr_ed rs val_e = Some val_v ->
      loc.(loc_type) = TBytes n ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed (TBytes n) (VBytes n bs_old)) ->
      bs_new = list_set_byte (Z.to_nat idx_v) (Z_to_byte val_v) bs_old ->
      rust_exec_ed callee_post callee_post_n function_table (REdByteStore loc idx_e val_e) rs
        (rs_set_tower_ed rs loc.(loc_var)
           (exist_tval_ed (TBytes n) (VBytes n bs_new)))
  | rexec_byte_load : forall x loc idx_e rs idx_v bs n b,
      eval_sexpr_ed rs idx_e = Some idx_v ->
      loc.(loc_type) = TBytes n ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed (TBytes n) (VBytes n bs)) ->
      List.nth_error bs (Z.to_nat idx_v) = Some b ->
      rust_exec_ed callee_post callee_post_n function_table (REdByteLoad x loc idx_e) rs
        (rs_set_scalar_ed rs x (Z.of_N (Byte.to_N b)))
  | rexec_for_zero : forall x body rs,
      rust_exec_ed callee_post callee_post_n function_table (REdFor x 0%nat body) rs rs
  | rexec_for_succ : forall x n body rs1 rs2 rs3,
      (* In [REdFor x (S n) body], body runs first with x := n,
         then [REdFor x n body] runs (so x sees n, n-1, ..., 0 in order). *)
      rust_exec_ed callee_post callee_post_n function_table body
        (rs_set_scalar_ed rs1 x (Z.of_nat n)) rs2 ->
      rust_exec_ed callee_post callee_post_n function_table (REdFor x n body) rs2 rs3 ->
      rust_exec_ed callee_post callee_post_n function_table (REdFor x (S n) body) rs1 rs3
  | rexec_select : forall cond if_t if_f dest rs cond_v src tv,
      (* CT conditional move: pick if_t when cond ≠ 0, else if_f, copy
         the chosen source's value into dest's slot.  Both branches
         produce the SAME-shaped state (one tower update at
         [dest.(loc_var)]), which is what makes this constant-time.
         We require all three locs share [loc_type] (enforced
         syntactically at the AST level) and copy the [tval_ed]
         opaquely — no decode-then-re-encode at the simulation level. *)
      eval_sexpr_ed rs cond = Some cond_v ->
      src = (if Z.eqb cond_v 0 then if_f else if_t) ->
      if_t.(loc_type) = dest.(loc_type) ->
      if_f.(loc_type) = dest.(loc_type) ->
      rs_get_tower_ed rs src.(loc_var) = Some tv ->
      rust_exec_ed callee_post callee_post_n function_table (REdSelect cond if_t if_f dest) rs
        (rs_set_tower_ed rs dest.(loc_var) tv)
  | rexec_calln : forall fname dests args rs1 rs2,
      (* Multi-output call: defers to the [callee_post_n] oracle.
         Mirrors [rexec_call] but with a list of destinations. *)
      callee_post_n fname dests args rs1 rs2 ->
      rust_exec_ed callee_post callee_post_n function_table (REdCallN fname dests args) rs1 rs2
  | rexec_callfn : forall fname (dest : located_ed) (args : list located_ed)
                          (body : function_body_ed) rs1 rs2,
      (* Verified-helper call: look up [body] in [function_table] by
         name, then execute [body dest args] inline. *)
      List.find (fun p => String.eqb (fst p) fname) function_table = Some (fname, body) ->
      rust_exec_ed callee_post callee_post_n function_table (body dest args) rs1 rs2 ->
      rust_exec_ed callee_post callee_post_n function_table
                   (REdCallFn fname dest args) rs1 rs2
  | rexec_block : forall body rs1 rs2,
      (* Scoped-allocation block: semantically transparent — the body
         runs in the same state and produces the same final state.
         The Rust / C emitters wrap [body] in a [{ ... }] block so any
         [REdLetZero] inside has its lifetime end at the brace, but
         the simulation level does not need to model that. *)
      rust_exec_ed callee_post callee_post_n function_table body rs1 rs2 ->
      rust_exec_ed callee_post callee_post_n function_table (REdBlock body) rs1 rs2
  | rexec_setbytes : forall loc bytes rs n bs_old,
      (* Whole-array byte-list write: replaces the [TBytes n] slot at
         [loc] with the list [bytes] of length [n], each Z value
         truncated to a single byte via [Z_to_byte].  Length mismatch
         is a stuck state (no rule fires). *)
      loc.(loc_type) = TBytes n ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed (TBytes n) (VBytes n bs_old)) ->
      List.length bytes = n ->
      rust_exec_ed callee_post callee_post_n function_table (REdSetBytes loc bytes) rs
        (rs_set_tower_ed rs loc.(loc_var)
           (exist_tval_ed (TBytes n) (VBytes n (List.map Z_to_byte bytes))))
  | rexec_arr_load : forall dst src idx_e rs idx_v n t arr_v elem_v,
      (* Array-of-slots read: dst := src[idx_v].  Requires
         [src.loc_type = TArr n t] and [dst.loc_type = t].
         The loaded element's [well_formed_ed] is a side condition;
         it is supplied by the call site whose invariant promises the
         array's per-element well-formedness (e.g., a comb table
         whose elements are precomputed limbs). *)
      eval_sexpr_ed rs idx_e = Some idx_v ->
      src.(loc_type) = TArr n t ->
      dst.(loc_type) = t ->
      rs_get_tower_ed rs src.(loc_var) =
        Some (exist_tval_ed (TArr n t) (VArr n t arr_v)) ->
      (Z.to_nat idx_v < n)%nat ->
      List.nth_error arr_v (Z.to_nat idx_v) = Some elem_v ->
      well_formed_ed elem_v ->
      rust_exec_ed callee_post callee_post_n function_table (REdArrLoad dst src idx_e) rs
        (rs_set_tower_ed rs dst.(loc_var) (exist_tval_ed t elem_v))
  | rexec_arr_store : forall arr idx_e src rs idx_v n t arr_v_old arr_v_new src_v,
      (* Array-of-slots write: arr[idx_v] := src.  Requires
         [arr.loc_type = TArr n t] and [src.loc_type = t]. *)
      eval_sexpr_ed rs idx_e = Some idx_v ->
      arr.(loc_type) = TArr n t ->
      src.(loc_type) = t ->
      rs_get_tower_ed rs arr.(loc_var) =
        Some (exist_tval_ed (TArr n t) (VArr n t arr_v_old)) ->
      rs_get_tower_ed rs src.(loc_var) =
        Some (exist_tval_ed t src_v) ->
      (Z.to_nat idx_v < n)%nat ->
      arr_v_new = list_set (Z.to_nat idx_v) src_v arr_v_old ->
      rust_exec_ed callee_post callee_post_n function_table (REdArrStore arr idx_e src) rs
        (rs_set_tower_ed rs arr.(loc_var)
           (exist_tval_ed (TArr n t) (VArr n t arr_v_new)))
  | rexec_limb_store_fp25519 : forall loc i e rs val_v limbs_old limbs_new,
      (* Phase 0b: limb write into a [TFp25519] slot.  Replaces limb
         [i] in the slot's limb list with [val_v].  Requires
         [loc.loc_type = TFp25519], a well-formed [VFp25519] payload,
         and [i < 5]. *)
      eval_sexpr_ed rs e = Some val_v ->
      loc.(loc_type) = TFp25519 ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed TFp25519 (VFp25519 limbs_old)) ->
      (i < 5)%nat ->
      length limbs_old = 5%nat ->
      limbs_new = list_set i val_v limbs_old ->
      rust_exec_ed callee_post callee_post_n function_table (REdLimbStore loc i e) rs
        (rs_set_tower_ed rs loc.(loc_var)
           (exist_tval_ed TFp25519 (VFp25519 limbs_new))).

(* ================================================================ *)
(* §5. bedrock2 bridge — Part B (Week 1 Day 5-6, IN PROGRESS)        *)
(* ================================================================ *)

(** Mirroring [SafeRustSimulation.v]'s BLS12 design (§3-§5):
    instead of connecting [rust_exec_ed] directly to
    [WeakestPrecondition.cmd], we introduce a parallel
    [bedrock_exec_ed] inductive operating on the SAME
    [rust_state_ed], then prove the translator-correctness
    [bedrock_exec_ed c rs1 rs2 -> rust_exec_ed (btranslate_ed c) rs1 rs2].

    The connection to actual bedrock2 [WeakestPrecondition] semantics
    happens at a separate layer (per the BLS12 §12.5 design), not
    inside this file. *)

(** Bedrock-level command parallel to [rust_cmd_ed], representing the
    bedrock2 source from which [btranslate_ed] derives the Rust
    output.  Same constructor structure; the difference is that the
    bedrock-side commands are what bedrock2 emits, while the rust-side
    are what [ToSafeRustBody] would print. *)
Inductive bedrock_cmd_ed :=
  | BEdSkip
  | BEdSeq      : bedrock_cmd_ed -> bedrock_cmd_ed -> bedrock_cmd_ed
  | BEdLetZero  : var -> tower_type_ed -> bedrock_cmd_ed -> bedrock_cmd_ed
  | BEdLetU64   : var -> sexpr_ed -> bedrock_cmd_ed -> bedrock_cmd_ed
  | BEdScalarSet : var -> sexpr_ed -> bedrock_cmd_ed
  | BEdCall     : String.string -> located_ed -> list located_ed -> bedrock_cmd_ed
  | BEdIfNz     : sexpr_ed -> bedrock_cmd_ed -> bedrock_cmd_ed -> bedrock_cmd_ed
  | BEdWhileNz  : sexpr_ed -> bedrock_cmd_ed -> bedrock_cmd_ed
  | BEdByteStore : located_ed -> sexpr_ed -> sexpr_ed -> bedrock_cmd_ed
  | BEdByteLoad : var -> located_ed -> sexpr_ed -> bedrock_cmd_ed
  | BEdFor : var -> nat -> bedrock_cmd_ed -> bedrock_cmd_ed
  | BEdSelect : sexpr_ed -> located_ed -> located_ed -> located_ed -> bedrock_cmd_ed
  | BEdCallN : String.string -> list located_ed -> list located_ed -> bedrock_cmd_ed
                            (* Multi-output FFI mirror of REdCallN. *)
  | BEdCallFn : String.string -> located_ed -> list located_ed -> bedrock_cmd_ed
                            (* Verified-helper mirror of REdCallFn. *)
  | BEdBlock  : bedrock_cmd_ed -> bedrock_cmd_ed
                            (* Scoped-allocation block (mirror of REdBlock).
                               Transparent at semantics level; emitters
                               wrap [body] in [{ ... }]. *)
  | BEdSetBytes : located_ed -> list Z -> bedrock_cmd_ed
                            (* Whole-array byte-list write (mirror of
                               REdSetBytes). *)
  | BEdArrLoad  : located_ed -> located_ed -> sexpr_ed -> bedrock_cmd_ed
                            (* Array-of-slots read (mirror of REdArrLoad). *)
  | BEdArrStore : located_ed -> sexpr_ed -> located_ed -> bedrock_cmd_ed
                            (* Array-of-slots write (mirror of REdArrStore). *)
  | BEdLimbStore : located_ed -> nat -> sexpr_ed -> bedrock_cmd_ed.
                            (* Phase 0b: limb-level write (mirror of
                               REdLimbStore). *)

(** Direct translation: bedrock_cmd_ed → rust_cmd_ed. *)
Fixpoint btranslate_ed (c : bedrock_cmd_ed) : rust_cmd_ed :=
  match c with
  | BEdSkip => REdSkip
  | BEdSeq c1 c2 => REdSeq (btranslate_ed c1) (btranslate_ed c2)
  | BEdLetZero x t c' => REdLetZero x t (btranslate_ed c')
  | BEdLetU64 x e c' => REdLetU64 x e (btranslate_ed c')
  | BEdScalarSet x e => REdScalarSet x e
  | BEdCall fname dst args => REdCall fname dst args
  | BEdIfNz e c1 c2 => REdIfNz e (btranslate_ed c1) (btranslate_ed c2)
  | BEdWhileNz e c' => REdWhileNz e (btranslate_ed c')
  | BEdByteStore loc idx val => REdByteStore loc idx val
  | BEdByteLoad x loc idx => REdByteLoad x loc idx
  | BEdFor x n c' => REdFor x n (btranslate_ed c')
  | BEdSelect cond if_t if_f dest => REdSelect cond if_t if_f dest
  | BEdCallN fname dests args => REdCallN fname dests args
  | BEdCallFn fname dest args => REdCallFn fname dest args
  | BEdBlock body => REdBlock (btranslate_ed body)
  | BEdSetBytes loc bytes => REdSetBytes loc bytes
  | BEdArrLoad dst src idx_e => REdArrLoad dst src idx_e
  | BEdArrStore arr idx_e src => REdArrStore arr idx_e src
  | BEdLimbStore loc i e => REdLimbStore loc i e
  end.

(** Bedrock-level execution.  Same shape as [rust_exec_ed], shares
    [callee_post] oracle.  In the BLS12 analogue the two semantics
    differ in clone-call handling; for Ed25519 (no Tfp tower of
    references), they're isomorphic — kept separate to maintain the
    same proof architecture. *)
Inductive bedrock_exec_ed
  (callee_post :
    String.string ->
    list located_ed ->
    located_ed ->
    rust_state_ed ->
    rust_state_ed ->
    Prop)
  (callee_post_n :
    String.string ->
    list located_ed ->        (* dests *)
    list located_ed ->        (* args *)
    rust_state_ed ->
    rust_state_ed ->
    Prop)
  (function_table : function_table_ed)
  : bedrock_cmd_ed -> rust_state_ed -> rust_state_ed -> Prop :=
  | bexec_skip : forall rs,
      bedrock_exec_ed callee_post callee_post_n function_table BEdSkip rs rs
  | bexec_seq : forall c1 c2 rs1 rs2 rs3,
      bedrock_exec_ed callee_post callee_post_n function_table c1 rs1 rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table c2 rs2 rs3 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdSeq c1 c2) rs1 rs3
  | bexec_let_zero : forall x t v c rs1 rs2,
      well_formed_ed v ->
      bedrock_exec_ed callee_post callee_post_n function_table c
        (rs_set_tower_ed rs1 x (exist_tval_ed t v))
        rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdLetZero x t c) rs1 rs2
  | bexec_let_u64 : forall x e c rs1 rs2 v,
      eval_sexpr_ed rs1 e = Some v ->
      bedrock_exec_ed callee_post callee_post_n function_table c (rs_set_scalar_ed rs1 x v) rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdLetU64 x e c) rs1 rs2
  | bexec_scalar_set : forall x e rs v,
      eval_sexpr_ed rs e = Some v ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdScalarSet x e) rs (rs_set_scalar_ed rs x v)
  | bexec_call : forall fname dst args rs1 rs2,
      callee_post fname args dst rs1 rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdCall fname dst args) rs1 rs2
  | bexec_if_zero : forall e c1 c2 rs1 rs2,
      eval_sexpr_ed rs1 e = Some 0 ->
      bedrock_exec_ed callee_post callee_post_n function_table c2 rs1 rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdIfNz e c1 c2) rs1 rs2
  | bexec_if_nonzero : forall e c1 c2 rs1 rs2 v,
      eval_sexpr_ed rs1 e = Some v ->
      v <> 0 ->
      bedrock_exec_ed callee_post callee_post_n function_table c1 rs1 rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdIfNz e c1 c2) rs1 rs2
  | bexec_while_zero : forall e c rs,
      eval_sexpr_ed rs e = Some 0 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdWhileNz e c) rs rs
  | bexec_while_nonzero : forall e c rs1 rs2 rs3 v,
      eval_sexpr_ed rs1 e = Some v ->
      v <> 0 ->
      bedrock_exec_ed callee_post callee_post_n function_table c rs1 rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdWhileNz e c) rs2 rs3 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdWhileNz e c) rs1 rs3
  | bexec_byte_store : forall loc idx_e val_e rs idx_v val_v bs_old bs_new n,
      eval_sexpr_ed rs idx_e = Some idx_v ->
      eval_sexpr_ed rs val_e = Some val_v ->
      loc.(loc_type) = TBytes n ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed (TBytes n) (VBytes n bs_old)) ->
      bs_new = list_set_byte (Z.to_nat idx_v) (Z_to_byte val_v) bs_old ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdByteStore loc idx_e val_e) rs
        (rs_set_tower_ed rs loc.(loc_var)
           (exist_tval_ed (TBytes n) (VBytes n bs_new)))
  | bexec_byte_load : forall x loc idx_e rs idx_v bs n b,
      eval_sexpr_ed rs idx_e = Some idx_v ->
      loc.(loc_type) = TBytes n ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed (TBytes n) (VBytes n bs)) ->
      List.nth_error bs (Z.to_nat idx_v) = Some b ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdByteLoad x loc idx_e) rs
        (rs_set_scalar_ed rs x (Z.of_N (Byte.to_N b)))
  | bexec_for_zero : forall x body rs,
      bedrock_exec_ed callee_post callee_post_n function_table (BEdFor x 0%nat body) rs rs
  | bexec_for_succ : forall x n body rs1 rs2 rs3,
      bedrock_exec_ed callee_post callee_post_n function_table body
        (rs_set_scalar_ed rs1 x (Z.of_nat n)) rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdFor x n body) rs2 rs3 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdFor x (S n) body) rs1 rs3
  | bexec_select : forall cond if_t if_f dest rs cond_v src tv,
      eval_sexpr_ed rs cond = Some cond_v ->
      src = (if Z.eqb cond_v 0 then if_f else if_t) ->
      if_t.(loc_type) = dest.(loc_type) ->
      if_f.(loc_type) = dest.(loc_type) ->
      rs_get_tower_ed rs src.(loc_var) = Some tv ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdSelect cond if_t if_f dest) rs
        (rs_set_tower_ed rs dest.(loc_var) tv)
  | bexec_calln : forall fname dests args rs1 rs2,
      callee_post_n fname dests args rs1 rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdCallN fname dests args) rs1 rs2
  | bexec_callfn : forall fname (dest : located_ed) (args : list located_ed)
                          (body : function_body_ed) rs1 rs2,
      (* Verified-helper call: look up [body] in [function_table] and
         execute (the rust-side projection of) [body dest args] via
         [rust_exec_ed].  We defer to [rust_exec_ed] since
         [function_body_ed] is the rust-side type; [safe_cmd_correct_ed]
         then connects the two sides at the top level. *)
      List.find (fun p => String.eqb (fst p) fname) function_table = Some (fname, body) ->
      rust_exec_ed callee_post callee_post_n function_table (body dest args) rs1 rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table
                      (BEdCallFn fname dest args) rs1 rs2
  | bexec_block : forall body rs1 rs2,
      (* Scoped-allocation block (transparent). *)
      bedrock_exec_ed callee_post callee_post_n function_table body rs1 rs2 ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdBlock body) rs1 rs2
  | bexec_setbytes : forall loc bytes rs n bs_old,
      (* Mirror of rexec_setbytes at the bedrock level. *)
      loc.(loc_type) = TBytes n ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed (TBytes n) (VBytes n bs_old)) ->
      List.length bytes = n ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdSetBytes loc bytes) rs
        (rs_set_tower_ed rs loc.(loc_var)
           (exist_tval_ed (TBytes n) (VBytes n (List.map Z_to_byte bytes))))
  | bexec_arr_load : forall dst src idx_e rs idx_v n t arr_v elem_v,
      (* Mirror of rexec_arr_load at the bedrock level. *)
      eval_sexpr_ed rs idx_e = Some idx_v ->
      src.(loc_type) = TArr n t ->
      dst.(loc_type) = t ->
      rs_get_tower_ed rs src.(loc_var) =
        Some (exist_tval_ed (TArr n t) (VArr n t arr_v)) ->
      (Z.to_nat idx_v < n)%nat ->
      List.nth_error arr_v (Z.to_nat idx_v) = Some elem_v ->
      well_formed_ed elem_v ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdArrLoad dst src idx_e) rs
        (rs_set_tower_ed rs dst.(loc_var) (exist_tval_ed t elem_v))
  | bexec_arr_store : forall arr idx_e src rs idx_v n t arr_v_old arr_v_new src_v,
      (* Mirror of rexec_arr_store at the bedrock level. *)
      eval_sexpr_ed rs idx_e = Some idx_v ->
      arr.(loc_type) = TArr n t ->
      src.(loc_type) = t ->
      rs_get_tower_ed rs arr.(loc_var) =
        Some (exist_tval_ed (TArr n t) (VArr n t arr_v_old)) ->
      rs_get_tower_ed rs src.(loc_var) =
        Some (exist_tval_ed t src_v) ->
      (Z.to_nat idx_v < n)%nat ->
      arr_v_new = list_set (Z.to_nat idx_v) src_v arr_v_old ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdArrStore arr idx_e src) rs
        (rs_set_tower_ed rs arr.(loc_var)
           (exist_tval_ed (TArr n t) (VArr n t arr_v_new)))
  | bexec_limb_store_fp25519 : forall loc i e rs val_v limbs_old limbs_new,
      (* Mirror of rexec_limb_store_fp25519 at the bedrock level. *)
      eval_sexpr_ed rs e = Some val_v ->
      loc.(loc_type) = TFp25519 ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed TFp25519 (VFp25519 limbs_old)) ->
      (i < 5)%nat ->
      length limbs_old = 5%nat ->
      limbs_new = list_set i val_v limbs_old ->
      bedrock_exec_ed callee_post callee_post_n function_table (BEdLimbStore loc i e) rs
        (rs_set_tower_ed rs loc.(loc_var)
           (exist_tval_ed TFp25519 (VFp25519 limbs_new))).

(** Simulation theorem.  Mirrors [SafeRustSimulation.v:1241]'s
    [safe_cmd_correct].  Proof: induction on [bedrock_exec_ed], 10
    cases, each constructor maps directly to its rust_exec_ed
    counterpart via [btranslate_ed]. *)
Theorem safe_cmd_correct_ed
    (callee_post :
      String.string -> list located_ed -> located_ed ->
      rust_state_ed -> rust_state_ed -> Prop)
    (callee_post_n :
      String.string -> list located_ed -> list located_ed ->
      rust_state_ed -> rust_state_ed -> Prop)
    (function_table : function_table_ed)
    (c : bedrock_cmd_ed) (rs1 rs2 : rust_state_ed) :
  bedrock_exec_ed callee_post callee_post_n function_table c rs1 rs2 ->
  rust_exec_ed callee_post callee_post_n function_table (btranslate_ed c) rs1 rs2.
Proof.
  intros H.
  induction H; cbn [btranslate_ed].
  - apply rexec_skip.
  - eapply rexec_seq; eauto.
  - eapply rexec_let_zero; eauto.
  - eapply rexec_let_u64; eauto.
  - eapply rexec_scalar_set; eauto.
  - eapply rexec_call; eauto.
  - eapply rexec_if_zero; eauto.
  - eapply rexec_if_nonzero; eauto.
  - eapply rexec_while_zero; eauto.
  - eapply rexec_while_nonzero; eauto.
  - eapply rexec_byte_store; eauto.
  - eapply rexec_byte_load; eauto.
  - apply rexec_for_zero.
  - eapply rexec_for_succ; eauto.
  - eapply rexec_select; eauto.
  - eapply rexec_calln; eauto.
  - eapply rexec_callfn; eauto.
  - eapply rexec_block; eauto.
  - eapply rexec_setbytes; eauto.
  - eapply rexec_arr_load; eauto.
  - eapply rexec_arr_store; eauto.
  - eapply rexec_limb_store_fp25519; eauto.
Qed.

(* ================================================================ *)
(* §6. Well-formedness preservation                                  *)
(* ================================================================ *)

(** Well-formedness of a tower environment: every binding's value
    has matching limb-count / byte-length per its type tag. *)
Definition tower_env_well_formed (env : list (var * tval_ed)) : Prop :=
  forall x t v, lookup_t_ed env x = Some (exist_tval_ed t v) -> well_formed_ed v.

Definition rs_well_formed (rs : rust_state_ed) : Prop :=
  tower_env_well_formed (rs_tower_ed rs).

(** Helper: lookup_t_ed of [(x, v) :: rest] at x is Some v. *)
Lemma lookup_t_ed_head : forall x v rest,
  lookup_t_ed ((x, v) :: rest) x = Some v.
Proof. intros; cbn; rewrite String.eqb_refl; reflexivity. Qed.

(** Helper: lookup_t_ed at x in a cons with different head ignores
    the head. *)
Lemma lookup_t_ed_cons_ne : forall x y v rest,
  x <> y -> lookup_t_ed ((y, v) :: rest) x = lookup_t_ed rest x.
Proof.
  intros x y v rest Hne. cbn.
  destruct (String.eqb x y) eqn:Heq; [| reflexivity].
  apply String.eqb_eq in Heq. contradiction.
Qed.

From Stdlib Require Import Program.Equality.

(** Helper: type-index injection for exist_tval_ed. *)
Lemma exist_tval_ed_inj_t : forall t1 t2 (v1 : rust_val_ed t1) (v2 : rust_val_ed t2),
  exist_tval_ed t1 v1 = exist_tval_ed t2 v2 -> t1 = t2.
Proof. intros t1 t2 v1 v2 H; injection H; auto. Qed.

(** Helper: value-equality from same-type exist_tval_ed equality.
    Discharged via [dependent destruction]. *)
Lemma exist_tval_ed_inj_v : forall t (v1 v2 : rust_val_ed t),
  exist_tval_ed t v1 = exist_tval_ed t v2 -> v1 = v2.
Proof.
  intros t v1 v2 H.
  dependent destruction H.
  reflexivity.
Qed.

(** Lookup at the updated key returns the new value. *)
Lemma lookup_t_ed_update_at : forall env x v,
  lookup_t_ed (update_in_place_ed env x v) x = Some v.
Proof.
  induction env as [| [y w] rest IH]; intros x v.
  - cbn. rewrite String.eqb_refl. reflexivity.
  - cbn. destruct (String.eqb y x) eqn:Heqyx.
    + (* y = x *) cbn. rewrite String.eqb_refl. reflexivity.
    + (* y ≠ x *) cbn.
      destruct (String.eqb x y) eqn:Hxy.
      * apply String.eqb_eq in Hxy; subst.
        rewrite String.eqb_refl in Heqyx; discriminate.
      * apply IH.
Qed.

(** Lookup at a different key in an updated env equals lookup in the
    original env. *)
Lemma lookup_t_ed_update_other : forall env x v y,
  y <> x ->
  lookup_t_ed (update_in_place_ed env x v) y = lookup_t_ed env y.
Proof.
  induction env as [| [z w] rest IH]; intros x v y Hne.
  - cbn. destruct (String.eqb y x) eqn:Heq; [| reflexivity].
    apply String.eqb_eq in Heq. contradiction.
  - cbn. destruct (String.eqb z x) eqn:Heqzx.
    + (* z = x *) apply String.eqb_eq in Heqzx; subst z.
      cbn. destruct (String.eqb y x) eqn:Heqy; [| reflexivity].
      apply String.eqb_eq in Heqy. contradiction.
    + (* z ≠ x *) cbn.
      destruct (String.eqb y z) eqn:Heqy; [reflexivity |].
      apply IH; exact Hne.
Qed.

(** [update_in_place_ed] preserves well-formedness when the new value
    is itself well-formed.  Direct proof via the two helper lemmas. *)
Lemma update_in_place_ed_preserves_wf :
  forall env x t v,
    tower_env_well_formed env ->
    well_formed_ed v ->
    tower_env_well_formed (update_in_place_ed env x (exist_tval_ed t v)).
Proof.
  intros env x t v Henv Hv y' t' v' Hl.
  destruct (String.string_dec y' x) as [Heq | Hne].
  - (* y' = x : lookup in updated env returns the new value *)
    subst y'.
    rewrite lookup_t_ed_update_at in Hl.
    injection Hl as Heqt H.
    subst t'.
    apply Eqdep_dec.inj_pair2_eq_dec in H;
      [subst | apply tower_type_ed_eq_dec].
    exact Hv.
  - (* y' ≠ x : lookup in updated env equals lookup in original env *)
    rewrite lookup_t_ed_update_other in Hl by exact Hne.
    apply (Henv y' t' v' Hl).
Qed.

(** Setting a tower slot with a well-formed value preserves rs's
    well-formedness. *)
Lemma rs_set_tower_ed_preserves_wf :
  forall rs x t v,
    rs_well_formed rs ->
    well_formed_ed v ->
    rs_well_formed (rs_set_tower_ed rs x (exist_tval_ed t v)).
Proof.
  intros rs x t v Hrs Hv.
  unfold rs_well_formed, rs_set_tower_ed; cbn.
  apply update_in_place_ed_preserves_wf; assumption.
Qed.

(** Setting a scalar slot doesn't affect tower well-formedness. *)
Lemma rs_set_scalar_ed_preserves_wf :
  forall rs x z, rs_well_formed rs -> rs_well_formed (rs_set_scalar_ed rs x z).
Proof.
  intros rs x z H y t v Hl.
  unfold rs_set_scalar_ed in Hl; cbn in Hl.
  apply (H y t v Hl).
Qed.

(** Master well-formedness preservation theorem.  Provided the
    callee_post oracle preserves well-formedness, [rust_exec_ed]
    preserves it.  Discharge: induction on rust_exec_ed. *)
Definition callee_post_well_formed
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall fname args dest rs1 rs2,
    callee_post fname args dest rs1 rs2 ->
    rs_well_formed rs1 ->
    rs_well_formed rs2.

(** Multi-output analog: every multi-dest callee preserves wf. *)
Definition callee_post_n_well_formed
    (callee_post_n : String.string -> list located_ed -> list located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall fname dests args rs1 rs2,
    callee_post_n fname dests args rs1 rs2 ->
    rs_well_formed rs1 ->
    rs_well_formed rs2.

Theorem rust_exec_ed_preserves_wf :
  forall callee_post callee_post_n function_table c rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rust_exec_ed callee_post callee_post_n function_table c rs1 rs2 ->
    rs_well_formed rs1 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table c rs1 rs2 Hcp Hcpn Hexec.
  induction Hexec; intros Hwf.
  - (* rexec_skip *) exact Hwf.
  - (* rexec_seq *) apply IHHexec2. apply IHHexec1. exact Hwf.
  - (* rexec_let_zero *)
    apply IHHexec.
    apply rs_set_tower_ed_preserves_wf; [exact Hwf | exact H].
  - (* rexec_let_u64 *)
    apply IHHexec.
    eapply rs_set_scalar_ed_preserves_wf; exact Hwf.
  - (* rexec_scalar_set *)
    eapply rs_set_scalar_ed_preserves_wf; exact Hwf.
  - (* rexec_call *)
    eapply Hcp; eauto.
  - (* rexec_if_zero *) apply IHHexec; exact Hwf.
  - (* rexec_if_nonzero *) apply IHHexec; exact Hwf.
  - (* rexec_while_zero *) exact Hwf.
  - (* rexec_while_nonzero *)
    apply IHHexec2. apply IHHexec1. exact Hwf.
  - (* rexec_byte_store *)
    subst bs_new.
    assert (Hbs_old_len : length bs_old = n).
    { exact (Hwf loc.(loc_var) (TBytes n) (VBytes n bs_old) H2). }
    apply rs_set_tower_ed_preserves_wf with
      (t := TBytes n) (v := VBytes n (list_set_byte (Z.to_nat idx_v) (Z_to_byte val_v) bs_old)).
    + exact Hwf.
    + cbn. rewrite list_set_byte_length. exact Hbs_old_len.
  - (* rexec_byte_load *)
    eapply rs_set_scalar_ed_preserves_wf; exact Hwf.
  - (* rexec_for_zero *) exact Hwf.
  - (* rexec_for_succ *)
    apply IHHexec2.
    apply IHHexec1.
    eapply rs_set_scalar_ed_preserves_wf; exact Hwf.
  - (* rexec_select *)
    (* tv = exist_tval_ed t' v' for some t' v'; well-formedness
       of the source slot transfers to dest. *)
    rename H3 into Hget.
    destruct tv as [t' v'].
    apply rs_set_tower_ed_preserves_wf; [exact Hwf |].
    unfold rs_get_tower_ed in Hget.
    exact (Hwf src.(loc_var) t' v' Hget).
  - (* rexec_calln *)
    eapply Hcpn; eauto.
  - (* rexec_callfn *)
    apply IHHexec; exact Hwf.
  - (* rexec_block *)
    apply IHHexec; exact Hwf.
  - (* rexec_setbytes *)
    apply rs_set_tower_ed_preserves_wf with
      (t := TBytes n) (v := VBytes n (List.map Z_to_byte bytes)).
    + exact Hwf.
    + cbn. rewrite List.length_map. exact H1.
  - (* rexec_arr_load *)
    (* The semantic rule includes [well_formed_ed elem_v] as a side
       condition supplied by the call site (last premise). *)
    apply rs_set_tower_ed_preserves_wf; [exact Hwf|].
    match goal with
    | [ H : well_formed_ed _ |- _ ] => exact H
    end.
  - (* rexec_arr_store *)
    subst arr_v_new.
    apply rs_set_tower_ed_preserves_wf with
      (t := TArr n t)
      (v := VArr n t (list_set (Z.to_nat idx_v) src_v arr_v_old)).
    + exact Hwf.
    + cbn. rewrite list_set_length.
      (* length arr_v_old = n from well-formedness of the slot *)
      exact (Hwf arr.(loc_var) (TArr n t) (VArr n t arr_v_old) H2).
  - (* rexec_limb_store_fp25519 *)
    subst limbs_new.
    apply rs_set_tower_ed_preserves_wf with
      (t := TFp25519)
      (v := VFp25519 (list_set i val_v limbs_old)).
    + exact Hwf.
    + cbn. rewrite list_set_length. assumption.
Qed.
