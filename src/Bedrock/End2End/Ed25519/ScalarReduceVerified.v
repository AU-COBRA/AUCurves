(** * ScalarReduceVerified — concrete Gallina spec and framework
 *                            scaffolding for the [scalar_reduce] leaf.
 *
 *  Companion to [Clamp64Verified.v] (which fully replaces the
 *  axiomatic [clamp_64_spec] leaf with a verified [function_body_ed]).
 *
 *  Paper claim demonstrated by this file:
 *    The same "leaves can be either axiomatic Gallina specs OR
 *    verified rust_cmd_ed bodies" pattern that worked for clamp_64
 *    also applies to scalar_reduce — we provide here the concrete
 *    Rocq Definition of the reduction (§1, 0 axioms), the length and
 *    boundedness lemmas it satisfies (§2, 0 axioms), and the
 *    REdCallFn-based framework scaffolding for a future Barrett-style
 *    body (§3).  The expanded ~200-byte-store body is deferred as
 *    mechanical future work — what matters for the paper is that the
 *    spec is concrete (mod L over Z) and the dispatch infrastructure
 *    is identical to the verified-clamp variant.
 *
 *  Status note (§3):
 *    The placeholder body [scalar_reduce_body_stub] delegates to a
 *    [REdCall "scalar_reduce" ...] inside, so the axiom count of any
 *    theorem that consumes it does NOT drop yet.  The
 *    [scalar_reduce_body_contract] theorem documents the precise
 *    obligation a future Barrett-style body must satisfy — and how
 *    [clamp_64_body_slot_holds] from [Clamp64Verified.v] would be
 *    instantiated in its place.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1.  Concrete Gallina reference                                    *)
(* ================================================================ *)

(** Ed25519 curve order:
      L = 2^252 + 27742317777372353535851937790883648493.  *)
Definition L_curve_order : Z :=
  2 ^ 252 + 27742317777372353535851937790883648493.

Lemma L_curve_order_pos : 0 < L_curve_order.
Proof. cbv [L_curve_order]. lia. Qed.

(** Reduce a 64-byte little-endian integer mod L and re-encode as a
    32-byte little-endian buffer.  This is the standard mathematical
    definition of [sc_reduce] from RFC 8032 (independent of how an
    optimized implementation computes it — Barrett, Montgomery, or
    schoolbook all converge on this Z-level spec).

    NOT an axiom: this is a concrete Rocq Definition that reduces by
    [vm_compute] on any concrete input. *)
Definition scalar_reduce_gallina (bs64 : list Byte.byte) : list Byte.byte :=
  let n : Z := le_combine bs64 in
  let r : Z := Z.modulo n L_curve_order in
  le_split 32 r.

(* ================================================================ *)
(* §2.  Length and boundedness                                       *)
(* ================================================================ *)

Lemma scalar_reduce_gallina_length :
  forall bs64, length (scalar_reduce_gallina bs64) = 32%nat.
Proof.
  intros bs64. cbv [scalar_reduce_gallina].
  apply length_le_split.
Qed.

(** The Z-decoding of the reduced 32-byte output is strictly less
    than L. *)
Lemma scalar_reduce_gallina_bounded :
  forall bs64,
    0 <= le_combine (scalar_reduce_gallina bs64) < L_curve_order.
Proof.
  intros bs64. cbv [scalar_reduce_gallina].
  rewrite le_combine_split.
  (* Goal: 0 <= (le_combine bs64 mod L) mod 2^(32*8) < L. *)
  set (n := le_combine bs64).
  set (r := n mod L_curve_order).
  assert (HrLo : 0 <= r) by (apply Z.mod_pos_bound, L_curve_order_pos).
  assert (HrHi : r < L_curve_order)
    by (apply Z.mod_pos_bound, L_curve_order_pos).
  (* L < 2^252 < 2^256, so r mod 2^256 = r. *)
  assert (HL256 : L_curve_order < 2 ^ (Z.of_nat 32 * 8)).
  { change (Z.of_nat 32 * 8) with 256.
    cbv [L_curve_order]. lia. }
  rewrite Z.mod_small by lia. lia.
Qed.

(** A direct mod-L equality, useful for downstream callers that want
    to see [reduce(x) ≡ x (mod L)] explicitly. *)
Lemma scalar_reduce_gallina_mod :
  forall bs64,
    le_combine (scalar_reduce_gallina bs64) =
    Z.modulo (le_combine bs64) L_curve_order.
Proof.
  intros bs64. cbv [scalar_reduce_gallina].
  rewrite le_combine_split.
  set (n := le_combine bs64).
  set (r := n mod L_curve_order).
  assert (HrLo : 0 <= r) by (apply Z.mod_pos_bound, L_curve_order_pos).
  assert (HrHi : r < L_curve_order)
    by (apply Z.mod_pos_bound, L_curve_order_pos).
  assert (HL256 : L_curve_order < 2 ^ (Z.of_nat 32 * 8)).
  { change (Z.of_nat 32 * 8) with 256.
    cbv [L_curve_order]. lia. }
  apply Z.mod_small. lia.
Qed.

(* ================================================================ *)
(* §3.  Framework scaffolding for a verified body                    *)
(* ================================================================ *)

(** Placeholder body that delegates to the axiomatic
    [scalar_reduce_spec] via [REdCall].  This is INTENTIONALLY not a
    full Barrett-style unrolling — the point of this file is to
    provide the spec ([scalar_reduce_gallina]), its length and
    boundedness guarantees (above), and the dispatch shape so that
    swapping in a future verified body (~200 REdLetU64 / REdByteStore
    operations) is a mechanical drop-in.

    A future Barrett body would look like:
      fun dest args =>
        match args with
        | [src] =>
            REdLetU64 "lo0" (... 8-byte loads from src ...) (
            ...
            REdByteStore dest 0 (... extract byte 0 of n mod L ...) (
            ...
            REdSkip))
        | _ => REdSkip end
    and would be paired with a [scalar_reduce_body_correct] theorem
    matching exactly the shape of [clamp_64_body_correct] from
    [Clamp64Verified.v].  Until that body is written, this stub keeps
    the file building and demonstrates the wiring. *)
Definition scalar_reduce_body_stub : function_body_ed :=
  fun dest args =>
    match args with
    | [src] => REdCall "scalar_reduce" dest [src]
    | _     => REdSkip
    end.

(** The contract a future verified body must satisfy: given the input
    bytes [in_bs] in [src] at [rs1], after executing the body the
    [dst] slot at [rs2] must hold [scalar_reduce_gallina in_bs].

    This is the EXACT statement that
    [clamp_64_body_correct] satisfies for clamping.  We prove that
    IF the [callee_post] supplied to [rust_exec_ed] agrees with
    [scalar_reduce_gallina] on the relevant call site, THEN the stub
    body satisfies the contract — i.e. the framework composes. *)
Definition scalar_reduce_body_contract_stmt
  (callee_post : String.string -> list located_ed -> located_ed ->
                 rust_state_ed -> rust_state_ed -> Prop)
  (callee_post_n : String.string -> list located_ed -> list located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop)
  (function_table : function_table_ed)
  (body : function_body_ed) : Prop :=
  forall (dst src : located_ed)
         (rs1 rs2 : rust_state_ed)
         (in_bs : list Byte.byte),
    dst.(loc_type) = TBytes 32 ->
    src.(loc_type) = TBytes 64 ->
    length in_bs = 64%nat ->
    rs_get_tower_ed rs1 src.(loc_var)
      = Some (exist_tval_ed (TBytes 64) (VBytes 64 in_bs)) ->
    rust_exec_ed callee_post callee_post_n function_table
                 (body dst [src]) rs1 rs2 ->
    rs_get_tower_ed rs2 dst.(loc_var)
      = Some (exist_tval_ed (TBytes 32)
                            (VBytes 32 (scalar_reduce_gallina in_bs))).

(** **Conditional theorem.**  If a [callee_post] honors
    [scalar_reduce_gallina] for the "scalar_reduce" call site (i.e.
    the per-call obligation already used in
    [strong_callee_post_no_clamp]), then the stub body satisfies the
    body-contract above.

    This is the contract a real Barrett-style body would discharge
    unconditionally (without the [callee_post] hypothesis).  Until
    that body is written, the conditional form makes precise what the
    body must compute. *)
Theorem scalar_reduce_body_contract_via_oracle :
  forall callee_post callee_post_n function_table,
    (forall (src : located_ed) (dst_var : String.string)
            (rs1 rs2 : rust_state_ed) (in_bs : list Byte.byte),
        src.(loc_type) = TBytes 64 ->
        length in_bs = 64%nat ->
        rs_get_tower_ed rs1 src.(loc_var)
          = Some (exist_tval_ed (TBytes 64) (VBytes 64 in_bs)) ->
        callee_post "scalar_reduce" [src]
          {| loc_var := dst_var; loc_type := TBytes 32 |}
          rs1 rs2 ->
        rs_get_tower_ed rs2 dst_var
          = Some (exist_tval_ed (TBytes 32)
                  (VBytes 32 (scalar_reduce_gallina in_bs)))) ->
    scalar_reduce_body_contract_stmt
      callee_post callee_post_n function_table scalar_reduce_body_stub.
Proof.
  intros callee_post callee_post_n function_table Horacle
         dst src rs1 rs2 in_bs Hdst_t Hsrc_t Hlen Hin Hexec.
  cbv [scalar_reduce_body_stub] in Hexec.
  inversion Hexec; subst; clear Hexec.
  (* Hypothesis from rexec_call: callee_post "scalar_reduce" [src] dst rs1 rs2. *)
  destruct dst as [dst_var dst_t]; cbn in Hdst_t. subst dst_t.
  cbn [loc_var].
  eapply Horacle; eauto.
Qed.

(* ================================================================ *)
(* §4.  Test vectors                                                 *)
(* ================================================================ *)

(** Reducing the all-zero 64-byte input yields the all-zero
    32-byte output. *)
Definition test_zero_in  : list Byte.byte := List.repeat Byte.x00 64.
Definition test_zero_out : list Byte.byte :=
  scalar_reduce_gallina test_zero_in.

Lemma test_zero_length : length test_zero_out = 32%nat.
Proof. apply scalar_reduce_gallina_length. Qed.

Lemma test_zero_byte0 : List.nth_error test_zero_out 0 = Some Byte.x00.
Proof. vm_compute. reflexivity. Qed.

Lemma test_zero_byte31 : List.nth_error test_zero_out 31 = Some Byte.x00.
Proof. vm_compute. reflexivity. Qed.

(** Reducing the constant [L_curve_order] (a 32-byte value
    zero-extended to 64 bytes) yields zero. *)
Definition L_as_bytes64 : list Byte.byte :=
  le_split 32 L_curve_order ++ List.repeat Byte.x00 32.

Lemma test_L_reduces_to_zero :
  scalar_reduce_gallina L_as_bytes64 = le_split 32 0.
Proof.
  cbv [scalar_reduce_gallina L_as_bytes64].
  vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(* §5.  Print-assumptions guard                                      *)
(* ================================================================ *)

(** [scalar_reduce_gallina] and its length / boundedness / mod
    lemmas should report "Closed under the global context" — these
    are 0-axiom definitions over Z.  Only the §3 framework lemma
    threads through the (still axiomatic) callee_post oracle. *)
(* Print Assumptions scalar_reduce_gallina. *)
(* Print Assumptions scalar_reduce_gallina_length. *)
(* Print Assumptions scalar_reduce_gallina_bounded. *)
(* Print Assumptions scalar_reduce_gallina_mod. *)
(* Print Assumptions scalar_reduce_body_contract_via_oracle. *)
