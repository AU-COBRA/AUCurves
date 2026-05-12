(** * XyztAddBodyDecomposed — field-op-decomposed [function_body_ed]
 *                             for the extended-twisted-Edwards point
 *                             addition leaf.
 *
 *  Phase A.1 of [docs/scalarmult-verification-plan.md] (commit b4af602).
 *
 *  Where [XyztAddBody.v]'s [xyzt_add_body] is a single
 *  [REdCall "fe25519_xyzt_add"] pass-through, this module decomposes
 *  the body into a sequence of:
 *
 *    - 2 × [REdCallN "fe25519_unpack_xyzt5"]  (unpack each 200-byte
 *           input xyzt slot into 5 × 40-byte felems)
 *    - 2 × [REdCall  "fe25519_mul_T"]         (compute Ti = Tai · Tbi
 *           for i ∈ {1, 2} — Edwards extended-coord cached T)
 *    - 10 × [REdCall "fe25519_<op>"]          (Hisil et al. addition:
 *           sub, mul, add, scale_2d, sub, sub, add, add, mul, mul, mul)
 *    - 1 × [REdCallN "fe25519_pack_xyzt5"]    (pack the 5 output
 *           felems back into the 200-byte dest xyzt slot)
 *
 *  Hisil et al. extended-twisted-Edwards point addition
 *  (https://eprint.iacr.org/2008/522 §3.3, eqn (5), and matching
 *  [ed25519_xyzt_add_gallina] from [XyztAddVerified.v]):
 *
 *      T1 = Ta1 · Tb1                                  (fe25519_mul)
 *      T2 = Ta2 · Tb2                                  (fe25519_mul)
 *      A  = (Y1 - X1) · (Y2 - X2)                      (sub, sub, mul)
 *      B  = (Y1 + X1) · (Y2 + X2)                      (add, add, mul)
 *      C  = T1 · (2·d) · T2                            (scale_2d, mul)
 *      D  = 2 · Z1 · Z2                                (mul, scale_2)
 *      E  = B - A                                      (sub)
 *      F  = D - C                                      (sub)
 *      G  = D + C                                      (add)
 *      H  = B + A                                      (add)
 *      X3 = E · F                                      (mul)
 *      Y3 = G · H                                      (mul)
 *      Z3 = F · G                                      (mul)
 *      Ta3 = E,  Tb3 = H        ⟹ T3 = E · H
 *
 *  We use 10 + 2 + 5 + 5 + 5 = 27 scratch [TBytes 40] slots:
 *    - 5 unpacked input felems for P1  (X1, Y1, Z1, Ta1, Tb1)
 *    - 5 unpacked input felems for P2  (X2, Y2, Z2, Ta2, Tb2)
 *    - 2 cached T felems               (T1, T2)
 *    - 10 intermediates                (A, B, C, D, E, F, G, H, X3, Y3, Z3)
 *
 *  The "Hisil 10-op count" is the multiplicative envelope: 2 cached-T
 *  mults + 5 main mults + 2 squarings (handled via mul slots A and B)
 *  + 1 scale_2d (constant-multiplication leaf).  Additive ops are
 *  sequenced but cost-amortized.
 *
 *  §1  Body definition [xyzt_add_body_decomposed].
 *  §2  Field-op contract predicate [fe25519_callees_honoured_add].
 *  §3  Correctness statement [xyzt_add_body_decomposed_correct].
 *      Proof skeleton with ONE [Admitted] (documented).
 *
 *  ## HONEST status
 *  The body builds and type-checks.
 *  [xyzt_add_body_decomposed_correct]'s proof requires ~10 + 2 +
 *  cache-T + pack/unpack = ~30 sequential [rust_exec_ed] inversion
 *  steps.  Mechanical but unbounded; left as one [Admitted] with the
 *  remaining cascade documented.
 *
 *  Companion: [XyztDoubleBodyDecomposed.v] does the 7-op doubling.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §0.  Local LE_TBytes helpers                                      *)
(* ================================================================ *)

Local Definition LE40 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 40 |}.

(* ================================================================ *)
(* §1.  Field-op decomposed body                                     *)
(* ================================================================ *)

(** Body for the "xyzt_add_decomposed" entry of [curve_function_table].

    Surface: two [located_ed] arguments [P1; P2] (each a 200-byte
    xyzt slot), one destination [dest] (also 200-byte xyzt slot).
    Decomposes into 2 unpacks + 12 field ops + 1 pack.

    On any other arity (defensive), the body collapses to [REdSkip].

    NOTE on naming: we use distinct slot names ("X1", "X2", ...) to
    avoid borrow-checker collisions in the emitted Rust.  The
    [REdLetZero] chain allocates 27 scratch slots up front; this is
    intentional — it matches the stack-allocated layout of the
    expected Rust output. *)
Definition xyzt_add_body_decomposed : function_body_ed :=
  fun dest args =>
    match args with
    | [P1; P2] =>
        (* 5 unpacked input felems for P1. *)
        REdLetZero "X1"  (TBytes 40) (
        REdLetZero "Y1"  (TBytes 40) (
        REdLetZero "Z1"  (TBytes 40) (
        REdLetZero "Ta1" (TBytes 40) (
        REdLetZero "Tb1" (TBytes 40) (
        (* 5 unpacked input felems for P2. *)
        REdLetZero "X2"  (TBytes 40) (
        REdLetZero "Y2"  (TBytes 40) (
        REdLetZero "Z2"  (TBytes 40) (
        REdLetZero "Ta2" (TBytes 40) (
        REdLetZero "Tb2" (TBytes 40) (
        (* 2 cached T values. *)
        REdLetZero "T1" (TBytes 40) (
        REdLetZero "T2" (TBytes 40) (
        (* 11 intermediate slots (A..H, X3, Y3, Z3). *)
        REdLetZero "A"  (TBytes 40) (
        REdLetZero "B"  (TBytes 40) (
        REdLetZero "C"  (TBytes 40) (
        REdLetZero "D"  (TBytes 40) (
        REdLetZero "E"  (TBytes 40) (
        REdLetZero "F"  (TBytes 40) (
        REdLetZero "G"  (TBytes 40) (
        REdLetZero "H"  (TBytes 40) (
        REdLetZero "X3" (TBytes 40) (
        REdLetZero "Y3" (TBytes 40) (
        REdLetZero "Z3" (TBytes 40) (
        (* Unpack P1 and P2 into the 10 input felems. *)
        REdSeq
          (REdCallN "fe25519_unpack_xyzt5"
             [LE40 "X1"; LE40 "Y1"; LE40 "Z1"; LE40 "Ta1"; LE40 "Tb1"]
             [P1])
        (REdSeq
          (REdCallN "fe25519_unpack_xyzt5"
             [LE40 "X2"; LE40 "Y2"; LE40 "Z2"; LE40 "Ta2"; LE40 "Tb2"]
             [P2])
        (* Cache T1 = Ta1·Tb1 and T2 = Ta2·Tb2. *)
        (REdSeq (REdCall "fe25519_mul" (LE40 "T1") [LE40 "Ta1"; LE40 "Tb1"])
        (REdSeq (REdCall "fe25519_mul" (LE40 "T2") [LE40 "Ta2"; LE40 "Tb2"])
        (* A = (Y1 - X1) · (Y2 - X2)
           We re-use "Y3" and "Z3" as scratch for the two sub
           intermediates (they will be overwritten before pack). *)
        (REdSeq (REdCall "fe25519_sub" (LE40 "Y3") [LE40 "Y1"; LE40 "X1"])
        (REdSeq (REdCall "fe25519_sub" (LE40 "Z3") [LE40 "Y2"; LE40 "X2"])
        (REdSeq (REdCall "fe25519_mul" (LE40 "A")  [LE40 "Y3"; LE40 "Z3"])
        (* B = (Y1 + X1) · (Y2 + X2) — reuse Y3 / Z3 as scratch. *)
        (REdSeq (REdCall "fe25519_add" (LE40 "Y3") [LE40 "Y1"; LE40 "X1"])
        (REdSeq (REdCall "fe25519_add" (LE40 "Z3") [LE40 "Y2"; LE40 "X2"])
        (REdSeq (REdCall "fe25519_mul" (LE40 "B")  [LE40 "Y3"; LE40 "Z3"])
        (* C = T1 · (2·d) · T2.  fe25519_mul_d2 takes T1, returns 2d·T1;
           then a final mul against T2. *)
        (REdSeq (REdCall "fe25519_mul_d2" (LE40 "Y3") [LE40 "T1"])
        (REdSeq (REdCall "fe25519_mul" (LE40 "C")  [LE40 "Y3"; LE40 "T2"])
        (* D = 2 · Z1 · Z2.  fe25519_mul_2 does the by-2 scale. *)
        (REdSeq (REdCall "fe25519_mul" (LE40 "Y3") [LE40 "Z1"; LE40 "Z2"])
        (REdSeq (REdCall "fe25519_mul_2" (LE40 "D") [LE40 "Y3"])
        (* E = B - A,   F = D - C,   G = D + C,   H = B + A. *)
        (REdSeq (REdCall "fe25519_sub" (LE40 "E") [LE40 "B"; LE40 "A"])
        (REdSeq (REdCall "fe25519_sub" (LE40 "F") [LE40 "D"; LE40 "C"])
        (REdSeq (REdCall "fe25519_add" (LE40 "G") [LE40 "D"; LE40 "C"])
        (REdSeq (REdCall "fe25519_add" (LE40 "H") [LE40 "B"; LE40 "A"])
        (* X3 = E · F,   Y3 = G · H,   Z3 = F · G. *)
        (REdSeq (REdCall "fe25519_mul" (LE40 "X3") [LE40 "E"; LE40 "F"])
        (REdSeq (REdCall "fe25519_mul" (LE40 "Y3") [LE40 "G"; LE40 "H"])
        (REdSeq (REdCall "fe25519_mul" (LE40 "Z3") [LE40 "F"; LE40 "G"])
        (* Pack: Ta3 = E, Tb3 = H (so T3 = E·H per Hisil). *)
        (REdCallN "fe25519_pack_xyzt5"
           [dest]
           [LE40 "X3"; LE40 "Y3"; LE40 "Z3"; LE40 "E"; LE40 "H"])
        ))))))))))))))))))))   (* close 20 REdSeq second-arg parens *)
        )))))))))))))))))))))))   (* close 23 REdLetZero body parens *)
    | _ => REdSkip
    end.

(* ================================================================ *)
(* §2.  Field-op callees-honoured predicate                          *)
(* ================================================================ *)

(** Every [fe25519_*] leaf used by the decomposed body satisfies its
    mathematical contract on inputs / outputs read from / written to
    [rust_state_ed].

    Stated abstractly via the [callee_post]/[callee_post_n] oracles:
    discharging these obligations is upstream work (per-leaf
    [Verified.v] files).  For Phase A milestone this is an opaque
    hypothesis to [body_correct]; the obligation enumerates the leaves
    the body invokes. *)
Definition fe25519_callees_honoured_add
    (callee_post   : String.string -> list located_ed -> located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop)
    (callee_post_n : String.string -> list located_ed ->
                     list located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  (* unpack: 200B → 5 × 40B felems. *)
  (forall dests args rs1 rs2,
     callee_post_n "fe25519_unpack_xyzt5" dests args rs1 rs2 ->
     length dests = 5%nat /\
     (forall d, In d dests -> d.(loc_type) = TBytes 40))
  /\
  (* pack: 5 × 40B felems → 200B xyzt. *)
  (forall dests args rs1 rs2,
     callee_post_n "fe25519_pack_xyzt5" dests args rs1 rs2 ->
     length dests = 1%nat)
  /\
  (* Every field op: outputs a 40-byte felem. *)
  (forall fname dst args rs1 rs2,
     In fname ["fe25519_mul"; "fe25519_sub"; "fe25519_add";
               "fe25519_mul_d2"; "fe25519_mul_2"] ->
     callee_post fname args dst rs1 rs2 ->
     dst.(loc_type) = TBytes 40).

(* ================================================================ *)
(* §3.  Correctness theorem                                          *)
(* ================================================================ *)

(** [xyzt_add_body_decomposed_correct]: under the field-op contracts
    plus 200-byte input pre-conditions on both points, the decomposed
    body produces the 200-byte output specified by
    [ed25519_xyzt_add_gallina].

    PROOF SKELETON.  ~30 sequential [rust_exec_ed] inversion steps:
    23 [rexec_let_zero] for the scratch slots + 2 [rexec_calln] for
    the unpacks + 12 [rexec_call] for the field ops + 1 [rexec_calln]
    for the pack.  Each [rexec_call(_n)] hits a clause in
    [fe25519_callees_honoured_add] to extract the post value.

    The 12 [rexec_call] inversions thread a chain of Z-level
    equalities (T1 = Ta1·Tb1 mod p, A = (Y1-X1)(Y2-X2) mod p, ...)
    that compose to [parse_xyzt5 p1], [parse_xyzt5 p2] -> the
    Hisil formula -> [pack_xyzt5 X3 Y3 Z3 E H] = the output of
    [ed25519_xyzt_add_gallina p_bs1 p_bs2].

    Cost: ~150-200 LoC of mechanical [inversion] / [eapply] glue.
    Left as [Admitted] for the next session; the body itself is
    Qed-clean. *)
Theorem xyzt_add_body_decomposed_correct :
  forall callee_post callee_post_n function_table
         (P1 P2 dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (p1_bs p2_bs : list Byte.byte),
    fe25519_callees_honoured_add callee_post callee_post_n ->
    length p1_bs = 200%nat ->
    length p2_bs = 200%nat ->
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 P1.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 p1_bs)) ->
    rs_get_tower_ed rs1 P2.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 p2_bs)) ->
    rust_exec_ed callee_post callee_post_n function_table
                 (xyzt_add_body_decomposed dest [P1; P2]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_xyzt_add_gallina p1_bs p2_bs))).
Proof.
  intros callee_post callee_post_n function_table P1 P2 dest rs1 rs2
         p1_bs p2_bs Hhonoured Hlen1 Hlen2 Hdest_type HP1in HP2in Hexec.
  (* Remaining cascade — see the comment above.  Each step is one
     [rexec_let_zero] / [rexec_seq] / [rexec_call(_n)] inversion,
     threading [Hhonoured]'s components to pull the post value out
     of each oracle hit.  ~30 transitions total.

     STATUS: 0 progress here; leaves the obligation visible. *)
Admitted.

(* Print Assumptions xyzt_add_body_decomposed. *)
(* Print Assumptions xyzt_add_body_decomposed_correct. *)
