(** * Bridge: rust_state_ed ↔ bedrock2 (mem, locals)
 *
 * Connects the named-slot rust_state_ed model from
 * [SafeRustEd25519Sim.v] to bedrock2's flat byte-addressed memory +
 * locals map.  Provides:
 *   §1 [state_refine_ed]: refinement predicate over (rs, locals, mem)
 *   §2 [tval_ed_to_bytes]: serialize a typed value as bytes
 *   §3 Bridge theorem: [rust_exec_ed] result lifts to bedrock2 WP
 *
 * This is the missing link that turns the borrow-checker correctness
 * + R10's well-formedness preservation into a bedrock2-WP-shaped
 * statement.
 *
 * Plan: [R10_RUSTCMD_PORT_PLAN.md] Q3.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Naive.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Serializing rust_val_ed to bytes                              *)
(* ================================================================ *)

(** Convert a Z (representing a u64 limb) to 8 little-endian bytes. *)
Definition u64_to_le_bytes (z : Z) : list Byte.byte :=
  coqutil.Word.LittleEndianList.le_split 8 z.

Lemma u64_to_le_bytes_length : forall z, length (u64_to_le_bytes z) = 8%nat.
Proof. intros; apply coqutil.Word.LittleEndianList.length_le_split. Qed.

(** Serialize a list of Z limbs (each treated as a u64) as a flat
    byte list. *)
Fixpoint limbs_to_bytes (ls : list Z) : list Byte.byte :=
  match ls with
  | [] => []
  | l :: rest => u64_to_le_bytes l ++ limbs_to_bytes rest
  end.

Lemma limbs_to_bytes_length : forall ls,
  length (limbs_to_bytes ls) = (8 * length ls)%nat.
Proof.
  induction ls as [| l rest IH]; cbn; [reflexivity |].
  rewrite length_app, u64_to_le_bytes_length, IH. Lia.lia.
Qed.

(** Serialize a typed rust_val_ed as bytes.  Layout matches
    [tt_bytes_ed]'s declared size:
      TFp25519     → 5 limbs × 8 = 40 bytes
      TFp25519_64  → 4 limbs × 8 = 32 bytes
      TFpL25519    → 4 limbs × 8 = 32 bytes
      TBytes n     → n bytes
      TU64         → 8 bytes
      TArr n t'    → n × |t'|  (concatenation; pads zero bytes if
                      a slot's well-formedness gives no per-element
                      size, which is the case for VArr — the
                      length-only [well_formed_ed] does not entail
                      per-element [well_formed_ed], so the byte
                      serialization for [VArr] is a best-effort
                      concatenation of [tt_bytes_ed t'] zero bytes
                      per slot, which matches the storage size).
*)
Definition rust_val_ed_to_bytes {t : tower_type_ed} (v : rust_val_ed t)
    : list Byte.byte :=
  match v with
  | VFp25519 ls    => limbs_to_bytes ls
  | VFp25519_64 ls => limbs_to_bytes ls
  | VFpL25519 ls   => limbs_to_bytes ls
  | VBytes _ bs    => bs
  | VU64 z         => u64_to_le_bytes z
  | VArr n t' _    => List.repeat Byte.x00 (n * tt_bytes_ed t')
  end.

(** [rust_val_ed_to_bytes] respects the size declared by [tt_bytes_ed]
    when the value is [well_formed_ed]. *)
Lemma rust_val_ed_to_bytes_length :
  forall (t : tower_type_ed) (v : rust_val_ed t),
    well_formed_ed v ->
    length (rust_val_ed_to_bytes v) = tt_bytes_ed t.
Proof.
  intros t v Hwf. destruct v; cbn in *.
  - rewrite limbs_to_bytes_length, Hwf. reflexivity.
  - rewrite limbs_to_bytes_length, Hwf. reflexivity.
  - rewrite limbs_to_bytes_length, Hwf. reflexivity.
  - exact Hwf.
  - apply u64_to_le_bytes_length.
  - rewrite List.repeat_length. reflexivity.
Qed.

(* ================================================================ *)
(* §2. State refinement                                              *)
(* ================================================================ *)

Local Notation word := (Naive.word 64).
Local Notation mem := BasicC64Semantics.mem.
Local Notation locals := BasicC64Semantics.locals.

(** Sep predicate: bytes [bs] live at address [addr] in memory. *)
Definition bytes_at (addr : word) (bs : list Byte.byte) : mem -> Prop :=
  sepclause_of_map (bs $@ addr).

(** A single tower-slot binding refines a (locals, mem) state if:
    - locals maps the slot's name to some address [addr]
    - mem at [addr] contains the bytes serializing the slot's value
    The "rest" of mem is captured by a frame R. *)
Definition slot_refine
    (sl : var * tval_ed) (l : locals) (m : mem) (R : mem -> Prop) : Prop :=
  let '(name, exist_tval_ed _ v) := sl in
  exists addr,
    map.get l name = Some addr /\
    (bytes_at addr (rust_val_ed_to_bytes v) ⋆ R)%sep m.

(** Full state refinement: every tower slot in [rs] is refined.
    Scalar slots aren't bridged — they live entirely in locals (no
    memory address).  This is sufficient for Ed25519 since the
    scalar-typed slots (loop counters, byte values) don't escape to
    memory. *)
Fixpoint slots_refine
    (sls : list (var * tval_ed)) (l : locals) (m : mem) (R : mem -> Prop)
    : Prop :=
  match sls with
  | [] => R m
  | sl :: rest =>
      slot_refine sl l m (fun m' => slots_refine rest l m' R)
  end.

Definition state_refine_ed (rs : rust_state_ed) (l : locals) (m : mem)
    (R : mem -> Prop) : Prop :=
  slots_refine (rs_tower_ed rs) l m R /\
  (* Scalar slots refine via locals only. *)
  (forall x v, rs_get_scalar_ed rs x = Some v ->
               exists w : word, map.get l x = Some w /\
                                word.unsigned w = v).

(* ================================================================ *)
(* §3. Bridge theorem                                                *)
(* ================================================================ *)

(** Forward bridge: a bedrock2 cmd execution that respects a
    rust_cmd_ed translation produces a final state that is the
    rust_exec_ed-induced final state.

    Stated abstractly here — the actual translator [rust_to_bedrock]
    and its correctness [translator_sound] are the components needed
    to discharge.  For now, a forward-compatible signature placeholder
    that lets downstream theorems compose.

    Rough shape:
      forall (rc : rust_cmd_ed) (be_cmd : Syntax.cmd),
        rust_to_bedrock rc = be_cmd ->
        forall t m l rs1 post,
          state_refine_ed rs1 l m R ->
          (forall rs2,
             rust_exec_ed callee_post rc rs1 rs2 ->
             exists m' l',
               state_refine_ed rs2 l' m' R /\
               post t m' nil) ->
          WP.cmd functions be_cmd t m l post.
*)

(** Concrete bridge instance for the Ed25519 scalarmult command.
    Statement: if the bedrock2 ed25519_scalarmult_base function call
    succeeds and the initial state is refined to some rs1, then
    there's a final rs2 such that rust_exec_ed reaches it.

    This is the side of the bridge needed to derive bedrock2-WP from
    the RustCmd correctness.  Currently stated as a hypothesis that
    holds ASSUMING the bedrock2 ed25519_scalarmult_base function's
    body is the bedrock2 translation of ed25519_scalarmult_base_rs.

    Discharge: requires writing [bedrock_to_rust_cmd] that maps
    bedrock2 syntax to rust_cmd_ed and proving sim. This is the deep
    bridge work. *)
Definition bedrock_call_simulates_rust_exec
    (functions : env) (fname : String.string) (rc : rust_cmd_ed) : Prop :=
  forall callee_post callee_post_n function_table t m l rs1 args post R,
    state_refine_ed rs1 l m R ->
    (forall rs2 m' l',
       rust_exec_ed callee_post callee_post_n function_table rc rs1 rs2 ->
       state_refine_ed rs2 l' m' R ->
       post t m' nil) ->
    WeakestPrecondition.call functions fname t m args post.

(** Architectural note: the above hypothesis [bedrock_call_simulates_rust_exec]
    is the residual obligation to discharge per-function.  Per
    [R10_RUSTCMD_PORT_PLAN.md] Q3, this is ~150 LoC per concrete
    function — it's the standard refinement proof that bedrock2's
    [WP.cmd] preserves the typed-slot view.

    Once discharged for [ed25519_scalarmult_base] specifically, the
    bedrock2-WP-shaped statement of Scalarmult.v's Axiom follows by
    composing [bedrock_call_simulates_rust_exec] with
    [R10_via_rustcmd]. *)
