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
(* §1.  Concrete Gallina reference (re-exported from RemainingBridges)*)
(* ================================================================ *)

(** Ed25519 curve order [L_curve_order] and the Gallina reduction
    [scalar_reduce_gallina] are now defined in [RemainingBridges.v]
    so that the previously axiomatic [scalar_reduce_spec] can be
    discharged to that same Definition.  We keep the long-form names
    here for backward compatibility — they are aliases. *)
Notation L_curve_order := RemainingBridges.L_curve_order.
Notation scalar_reduce_gallina := RemainingBridges.scalar_reduce_spec.

Lemma L_curve_order_pos : 0 < L_curve_order.
Proof. exact RemainingBridges.L_curve_order_pos. Qed.

(* ================================================================ *)
(* §2.  Length and boundedness                                       *)
(* ================================================================ *)

Lemma scalar_reduce_gallina_length :
  forall bs64, length (scalar_reduce_gallina bs64) = 32%nat.
Proof. exact RemainingBridges.scalar_reduce_output_32. Qed.

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
(* §4.  Concrete Barrett-style reducer (Gallina algorithm)            *)
(* ================================================================ *)

(** Precomputed Barrett constant:
      mu_barrett = floor(2^512 / L_curve_order).

    For Ed25519's L = 2^252 + 27742317777372353535851937790883648493,
    this value fits in 260 bits (top bit at index 259).  It is the
    standard Barrett-reduction multiplier used by libsodium / ref10 /
    curve25519-dalek (where it is stored as a fixed 33-byte / 5×64-bit
    constant).

    We compute it by definition rather than hardcoding a literal, so
    no axiom is introduced. *)
Definition mu_barrett : Z := 2 ^ 512 / L_curve_order.

(** Barrett's reduction algorithm, expressed at the Z level using the
    same arithmetic skeleton an unrolled 64-bit-limb body would use:

      1. Decode 64 input bytes to an integer  n  in [0, 2^512).
      2. Estimate quotient            q := (n * mu_barrett) >> 512.
      3. Form remainder candidate     r := n - q * L.
      4. Two conditional subtractions to land r in [0, L).

    The output is re-encoded as 32 little-endian bytes.  This is a
    concrete sequence of `Z.add / Z.mul / Z.sub / Z.shiftr / Z.ltb`
    operations — no [Z.modulo].  An unrolled rust_cmd_ed body would
    replace each Z-op by a multi-limb 64-bit chain; the algorithm is
    identical. *)
Definition barrett_reduce_step (n : Z) : Z :=
  let q := Z.shiftr (n * mu_barrett) 512 in
  let r := n - q * L_curve_order in
  let r1 := if Z.ltb r L_curve_order then r else r - L_curve_order in
  if Z.ltb r1 L_curve_order then r1 else r1 - L_curve_order.

Definition scalar_reduce_concrete (bs64 : list Byte.byte) : list Byte.byte :=
  let n : Z := le_combine bs64 in
  let r : Z := barrett_reduce_step n in
  le_split 32 r.

(** Numerical sanity check: the precomputed mu fits in 260 bits
    (since L ≈ 2^252, mu_barrett = floor(2^512/L) ≈ 2^260, and one
    can verify by [vm_compute] that the actual top bit is at index
    259).  This bound is not used in the correctness proof but
    documents the size of the constant. *)
Lemma mu_barrett_bound :
  2 ^ 259 <= mu_barrett < 2 ^ 260.
Proof.
  cbv [mu_barrett L_curve_order]. vm_compute.
  split; [intro Hx; discriminate Hx | reflexivity].
Qed.

(** **Key Z-arithmetic lemma.**  Barrett's algorithm returns the same
    value as [Z.modulo] for any non-negative input bounded by 2^512.
    This is the standard Barrett correctness statement, sufficient
    for any 64-byte input because [le_combine] of a 64-byte list is
    bounded by 2^(8*64) = 2^512.

    Proof strategy: bound the quotient estimate's error to at most 2,
    so two conditional subtractions suffice. *)
Lemma barrett_reduce_step_correct :
  forall n, 0 <= n < 2 ^ 512 ->
            barrett_reduce_step n = n mod L_curve_order.
Proof.
  intros n Hn.
  cbv [barrett_reduce_step].
  set (q := Z.shiftr (n * mu_barrett) 512).
  set (r := n - q * L_curve_order).
  assert (HL : 0 < L_curve_order) by exact L_curve_order_pos.
  (* Decompose 2^512 = mu*L + (2^512 mod L). *)
  pose proof (Z.div_mod (2 ^ 512) L_curve_order ltac:(lia)) as Hmu.
  pose proof (Z.mod_pos_bound (2 ^ 512) L_curve_order ltac:(lia)) as Hmu_mod.
  change (2 ^ 512 / L_curve_order) with mu_barrett in Hmu.
  (* Express q via division. *)
  assert (Hq_eq : q = (n * mu_barrett) / 2 ^ 512).
  { unfold q. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  (* Quotient/remainder for n*mu by 2^512. *)
  pose proof (Z.div_mod (n * mu_barrett) (2 ^ 512) ltac:(lia)) as Hnq.
  pose proof (Z.mod_pos_bound (n * mu_barrett) (2 ^ 512) ltac:(lia)) as Hnq_mod.
  (* Lower bound on r: r = n - q*L >= 0.
     Equivalent: q*L <= n.  Using q = (n*mu)/2^512 and mu*L <= 2^512:
     q*2^512 <= n*mu  =>  q*L*2^512 <= n*mu*L <= n*2^512  =>  q*L <= n. *)
  assert (Hr_lo : 0 <= r).
  { unfold r.
    pose proof (Z.mul_div_le (n * mu_barrett) (2 ^ 512) ltac:(lia)) as Hdl.
    rewrite Hq_eq. nia. }
  (* Upper bound on r: r < 3L.  Equivalent to q*L > n - 3L.
     Using q+1 > (n*mu)/2^512 + 1, i.e. (q+1)*2^512 > n*mu, and
     n*mu*L = n*(2^512 - delta) where delta = 2^512 mod L < L, n < 2^512:
       (q+1)*2^512*L > n*mu*L = n*2^512 - n*delta > n*2^512 - L*2^512
     so (q+1)*L > n - L, i.e. q*L > n - 2L > n - 3L. *)
  assert (Hr_hi : r < 3 * L_curve_order).
  { unfold r.
    (* Key inequality: n*mu < (q+1) * 2^512. *)
    assert (Hq_hi : n * mu_barrett < (q + 1) * 2 ^ 512).
    { rewrite Hq_eq. nia. }
    (* Multiply Hmu by n: n * 2^512 = n*mu*L + n*(2^512 mod L). *)
    assert (Hn_dec : n * 2 ^ 512 = n * mu_barrett * L_curve_order + n * (2 ^ 512 mod L_curve_order))
      by nia.
    (* n * (2^512 mod L) < 2^512 * L, since 2^512 mod L < L and n < 2^512. *)
    assert (Hnd_bnd : n * (2 ^ 512 mod L_curve_order) < 2 ^ 512 * L_curve_order) by nia.
    (* Combine: n*mu*L > n*2^512 - 2^512 * L, so n*mu*L > (n-L)*2^512. *)
    assert (Hnmul : n * mu_barrett * L_curve_order > (n - L_curve_order) * 2 ^ 512) by nia.
    (* From Hq_hi multiplied by L: (q+1) * 2^512 * L > n*mu*L. *)
    assert (Hqplus : (q + 1) * 2 ^ 512 * L_curve_order > n * mu_barrett * L_curve_order) by nia.
    (* Chain: (q+1) * 2^512 * L > (n - L) * 2^512, hence (q+1)*L > n - L. *)
    assert (Hcl : (q + 1) * L_curve_order > n - L_curve_order) by nia.
    nia. }
  (* Mod-L equivalence of r vs n. *)
  assert (Hr_mod : r mod L_curve_order = n mod L_curve_order).
  { unfold r.
    replace (n - q * L_curve_order) with (n + (- q) * L_curve_order) by ring.
    rewrite Z.mod_add by lia. reflexivity. }
  (* Two conditional subtractions: collapse r in [0, 3L) to [0, L). *)
  set (r1 := if Z.ltb r L_curve_order then r else r - L_curve_order).
  assert (Hr1_bnd : 0 <= r1 < 2 * L_curve_order).
  { unfold r1. destruct (Z.ltb_spec r L_curve_order); lia. }
  assert (Hr1_mod : r1 mod L_curve_order = n mod L_curve_order).
  { unfold r1. destruct (Z.ltb_spec r L_curve_order); [exact Hr_mod|].
    rewrite <- Hr_mod.
    replace (r - L_curve_order) with (r + (- 1) * L_curve_order) by ring.
    rewrite Z.mod_add by lia. reflexivity. }
  destruct (Z.ltb_spec r1 L_curve_order) as [Hlt | Hge].
  - rewrite <- Hr1_mod. symmetry. apply Z.mod_small. lia.
  - rewrite <- Hr1_mod.
    assert (Hred : r1 mod L_curve_order = r1 - L_curve_order)
      by (symmetry; apply Z.mod_unique_pos with 1; lia).
    lia.
Qed.

(** **Main concrete-equals-abstract theorem.**  For any 64-byte
    input, the Barrett-style concrete reducer produces exactly the
    same 32-byte output as the abstract [mod L] spec. *)
Theorem scalar_reduce_concrete_correct :
  forall bs, length bs = 64%nat ->
             scalar_reduce_concrete bs = scalar_reduce_gallina bs.
Proof.
  intros bs Hlen.
  cbv [scalar_reduce_concrete scalar_reduce_gallina].
  rewrite barrett_reduce_step_correct; [reflexivity|].
  pose proof (le_combine_bound bs) as Hb.
  rewrite Hlen in Hb. cbn in Hb. exact Hb.
Qed.

(** Length and boundedness lemmas transport for free. *)
Lemma scalar_reduce_concrete_length :
  forall bs, length bs = 64%nat ->
             length (scalar_reduce_concrete bs) = 32%nat.
Proof.
  intros bs Hlen.
  rewrite scalar_reduce_concrete_correct by exact Hlen.
  apply scalar_reduce_gallina_length.
Qed.

(* ================================================================ *)
(* §5.  Test vectors                                                 *)
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

(** Cross-check: the concrete Barrett reducer agrees on the
    zero-extended-L test vector. *)
Lemma test_L_concrete_matches :
  scalar_reduce_concrete L_as_bytes64 = scalar_reduce_gallina L_as_bytes64.
Proof.
  apply scalar_reduce_concrete_correct.
  cbv [L_as_bytes64]. rewrite length_app, length_le_split, repeat_length. reflexivity.
Qed.

(** Cross-check: the concrete Barrett reducer agrees on the all-zero
    input. *)
Lemma test_zero_concrete_matches :
  scalar_reduce_concrete test_zero_in = scalar_reduce_gallina test_zero_in.
Proof.
  apply scalar_reduce_concrete_correct.
  cbv [test_zero_in]. apply repeat_length.
Qed.

(** Direct [vm_compute] sanity check on the concrete reducer:
    reducing L (zero-extended) gives all-zero 32 bytes. *)
Lemma test_L_concrete_value :
  scalar_reduce_concrete L_as_bytes64 = List.repeat Byte.x00 32.
Proof.
  rewrite test_L_concrete_matches.
  cbv [scalar_reduce_gallina L_as_bytes64].
  vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(* §6.  Print-assumptions guard                                      *)
(* ================================================================ *)

(** [scalar_reduce_gallina] and its length / boundedness / mod
    lemmas should report "Closed under the global context" — these
    are 0-axiom definitions over Z.  Only the §3 framework lemma
    threads through the (still axiomatic) callee_post oracle.

    Likewise [scalar_reduce_concrete] (Barrett-style algorithm) and
    its main correctness theorem [scalar_reduce_concrete_correct]
    are 0-axiom — they reduce by [vm_compute] on any concrete input
    and are equal to [scalar_reduce_gallina] for any 64-byte list. *)
(* Print Assumptions scalar_reduce_gallina. *)
(* Print Assumptions scalar_reduce_gallina_length. *)
(* Print Assumptions scalar_reduce_gallina_bounded. *)
(* Print Assumptions scalar_reduce_gallina_mod. *)
(* Print Assumptions scalar_reduce_body_contract_via_oracle. *)
(* Print Assumptions scalar_reduce_concrete. *)
(* Print Assumptions barrett_reduce_step_correct. *)
(* Print Assumptions scalar_reduce_concrete_correct. *)
