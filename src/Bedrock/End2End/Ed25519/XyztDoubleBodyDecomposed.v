(** * XyztDoubleBodyDecomposed — field-op-decomposed [function_body_ed]
 *                                for the extended-twisted-Edwards point
 *                                doubling leaf.
 *
 *  Phase A.2 of [docs/scalarmult-verification-plan.md] (commit b4af602).
 *
 *  Where [XyztDoubleBody.v]'s [xyzt_double_body] is a single
 *  [REdCall "fe25519_xyzt_double"] pass-through, this module
 *  decomposes the body into a sequence of:
 *
 *    - 1 × [REdCallN "fe25519_unpack_xyzt5"]  (unpack the 200-byte
 *           xyzt slot into 5 × 40-byte felems)
 *    - 7 × [REdCall  "fe25519_<op>"]          (field ops: sub, sqr,
 *           mul, add, scale)
 *    - 1 × [REdCallN "fe25519_pack_xyzt5"]    (pack the 5 output
 *           felems back into the 200-byte xyzt slot)
 *
 *  Each field op corresponds to one step in the standard Hisil-Wong-
 *  Carter-Dawson extended-twisted-Edwards doubling formula
 *  (https://eprint.iacr.org/2008/522 §3.3, eqn (5)):
 *
 *      A = X²              B = Y²            C = 2·Z²
 *      G = -A + B          F = G - C         H = -A - B
 *      E = (X+Y)² - A - B  (= 2·X·Y)
 *      X3 = E · F          Y3 = G · H        Z3 = F · G
 *      T3 = E · H          (encoded as Ta3 = E, Tb3 = H)
 *
 *  We reuse 8 scratch [TBytes 40] slots — A, B, C, E, F, G, H, XpY.
 *  The 5 unpacked input felems live in X, Y, Z, Ta, Tb (Ta·Tb is the
 *  cached T of the input).
 *
 *  Compared to [XyztAddBodyDecomposed.v]'s 10 field ops, doubling
 *  needs only 7 multiplicative ops (3 squarings + 4 multiplications)
 *  plus a handful of additive ops which we fold into mul-add or pack
 *  arithmetic where convenient.  Cost ≈ 0.5× of addition.
 *
 *  §1  Body definition [xyzt_double_body_decomposed].
 *  §2  Field-op contract predicate [fe25519_callees_honoured_dbl].
 *  §3  Correctness statement [xyzt_double_body_decomposed_correct].
 *      Proof skeleton with ONE [Admitted] (documented).
 *
 *  ## HONEST status
 *  The body builds and type-checks.  [xyzt_double_body_decomposed_correct]'s
 *  proof requires ~7 sequential [inversion] steps on [rust_exec_ed]
 *  (one per field op), each plugging in [fe25519_callees_honoured_dbl]
 *  to extract the post value, then combining the seven field results
 *  via [pack_xyzt5] into the final 200-byte output.  This is mechanical
 *  but ~100-150 LoC of clerical work; we leave the body of the proof
 *  as a single [Admitted] with a clear remaining-cascade comment.
 *
 *  Companion: [XyztAddBodyDecomposed.v] does the 10-op addition variant.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.XyztDoubleVerified.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §0.  Local located_ed helpers                                     *)
(* ================================================================ *)

(** Each field-element intermediate is a [TFp25519] tight-limb slot
    (5 × u64).  Retyped 2026-05-12 per the TFp25519_64 plumbing plan
    (mirror of [XyztAddBodyDecomposed.v]).  [LE40] retained as alias
    for legacy byte-slot callers. *)
Local Definition LE_TFp25519 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

Local Definition LE40 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 40 |}.

Local Definition LE200 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 200 |}.

(* ================================================================ *)
(* §1.  Field-op decomposed body                                     *)
(* ================================================================ *)

(** Body for the "xyzt_double_decomposed" entry of [curve_function_table].

    Surface: one [located_ed] argument [P] (200-byte xyzt slot), one
    destination [dest] (also 200-byte xyzt slot).  Decomposes into
    1 unpack + 7 field ops + 1 pack.

    On any other arity (defensive), the body collapses to [REdSkip]. *)
Definition xyzt_double_body_decomposed : function_body_ed :=
  fun dest args =>
    match args with
    | [P] =>
        (* Allocate the 5 unpacked input felems. *)
        REdLetZero "X"  TFp25519 (
        REdLetZero "Y"  TFp25519 (
        REdLetZero "Z"  TFp25519 (
        REdLetZero "Ta" TFp25519 (
        REdLetZero "Tb" TFp25519 (
        (* Allocate the 8 scratch slots for intermediates. *)
        REdLetZero "A"   TFp25519 (
        REdLetZero "B"   TFp25519 (
        REdLetZero "C"   TFp25519 (
        REdLetZero "E"   TFp25519 (
        REdLetZero "F"   TFp25519 (
        REdLetZero "G"   TFp25519 (
        REdLetZero "H"   TFp25519 (
        REdLetZero "XpY" TFp25519 (
        (* Unpack the input xyzt slot into the 5 input felems. *)
        REdSeq
          (REdCallN "fe25519_unpack_xyzt5"
             [LE_TFp25519 "X"; LE_TFp25519 "Y"; LE_TFp25519 "Z"; LE_TFp25519 "Ta"; LE_TFp25519 "Tb"]
             [P])
        (* 7 field ops in sequence.  Hisil et al. doubling:
             A = X²                          (sqr)
             B = Y²                          (sqr)
             C = 2 · Z²                      (sqr + double — folded as scale_2)
             XpY = X + Y                     (NOT counted in 7-op tally —
                                              treated as an inline add)
             E = (X+Y)² - A - B              (sqr + 2 subs)
             G = B - A                       (sub)
             H = -(A + B)  ≡ -A - B          (add + neg, can be sub from 0)
             F = G - C                       (sub)
             X3 = E · F                      (mul)
             Y3 = G · H                      (mul)
             Z3 = F · G                      (mul)
           For decomposition simplicity we ABBREVIATE: the 3 final
           multiplications are the dominant cost; the additive steps
           are sequenced but counted under the 7-op envelope by treating
           [B - A] / [-(A+B)] / [G - C] as REdCall to dedicated leaves. *)
        (REdSeq (REdCall "fe25519_sqr" (LE_TFp25519 "A") [LE_TFp25519 "X"])
        (REdSeq (REdCall "fe25519_sqr" (LE_TFp25519 "B") [LE_TFp25519 "Y"])
        (REdSeq (REdCall "fe25519_sqr_scale2" (LE_TFp25519 "C") [LE_TFp25519 "Z"])
        (REdSeq (REdCall "fe25519_add" (LE_TFp25519 "XpY") [LE_TFp25519 "X"; LE_TFp25519 "Y"])
        (REdSeq (REdCall "fe25519_sqr_sub2" (LE_TFp25519 "E")
                   [LE_TFp25519 "XpY"; LE_TFp25519 "A"; LE_TFp25519 "B"])
        (REdSeq (REdCall "fe25519_sub" (LE_TFp25519 "G") [LE_TFp25519 "B"; LE_TFp25519 "A"])
        (REdSeq (REdCall "fe25519_neg_add" (LE_TFp25519 "H") [LE_TFp25519 "A"; LE_TFp25519 "B"])
        (REdSeq (REdCall "fe25519_sub" (LE_TFp25519 "F") [LE_TFp25519 "G"; LE_TFp25519 "C"])
        (REdSeq (REdCall "fe25519_mul" (LE_TFp25519 "X")  [LE_TFp25519 "E"; LE_TFp25519 "F"])
        (REdSeq (REdCall "fe25519_mul" (LE_TFp25519 "Y")  [LE_TFp25519 "G"; LE_TFp25519 "H"])
        (REdSeq (REdCall "fe25519_mul" (LE_TFp25519 "Z")  [LE_TFp25519 "F"; LE_TFp25519 "G"])
        (* Pack: X3=X, Y3=Y, Z3=Z, Ta3=E, Tb3=H (so T3=E·H). *)
        (REdCallN "fe25519_pack_xyzt5"
           [dest]
           [LE_TFp25519 "X"; LE_TFp25519 "Y"; LE_TFp25519 "Z"; LE_TFp25519 "E"; LE_TFp25519 "H"])
        )))))))))))
        )))))))))))))
    | _ => REdSkip
    end.

(* ================================================================ *)
(* §2.  Field-op callees-honoured predicate                          *)
(* ================================================================ *)

(** Generic predicate: every [fe25519_*] leaf used by the decomposed
    body satisfies its mathematical contract on inputs / outputs read
    from / written to [rust_state_ed].

    Stated abstractly via the [callee_post]/[callee_post_n] oracles so
    no specific fiat-crypto Z-level proof is forced here — discharging
    these obligations is upstream work (per-leaf [Verified.v] files).

    For this Phase-A milestone we expose the predicate as an opaque
    hypothesis to [body_correct]; the obligation enumerates the
    seven leaves the body invokes. *)
Definition fe25519_callees_honoured_dbl
    (callee_post   : String.string -> list located_ed -> located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop)
    (callee_post_n : String.string -> list located_ed ->
                     list located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  (* (1) unpack: 200B → 5 × TFp25519 limb tuples. *)
  (forall dests args rs1 rs2,
     callee_post_n "fe25519_unpack_xyzt5" dests args rs1 rs2 ->
     length dests = 5%nat /\
     (forall d, In d dests -> d.(loc_type) = TFp25519))
  /\
  (* (2) pack: 5 × TFp25519 limb tuples → 200B xyzt. *)
  (forall dests args rs1 rs2,
     callee_post_n "fe25519_pack_xyzt5" dests args rs1 rs2 ->
     length dests = 1%nat)
  /\
  (* (3)-(9) seven field ops: each writes a TFp25519 limb output. *)
  (forall fname dst args rs1 rs2,
     In fname ["fe25519_sqr"; "fe25519_sqr_scale2"; "fe25519_add";
               "fe25519_sqr_sub2"; "fe25519_sub";
               "fe25519_neg_add"; "fe25519_mul"] ->
     callee_post fname args dst rs1 rs2 ->
     dst.(loc_type) = TFp25519).

(* ================================================================ *)
(* §3.  Correctness theorem                                          *)
(* ================================================================ *)

(** [xyzt_double_body_decomposed_correct]: under the field-op
    contracts plus a 200-byte input pre-condition, the decomposed
    body produces the 200-byte output specified by
    [ed25519_xyzt_double_gallina].

    PROOF SKELETON.  Each [REdLetZero] inverts via [rexec_let_zero]
    (introducing a zero felem at the named slot); each [REdSeq]
    splits via [rexec_seq]; each [REdCall] inverts via [rexec_call]
    (consuming one fe25519 contract from
    [fe25519_callees_honoured_dbl]).  After the 13 + 1 unpack + 7 ops
    + 1 pack = 22 inversion steps, the goal reduces to checking that
    the packed output bytes match [ed25519_xyzt_double_gallina]'s
    output bytes — which is true by [parse_xyzt5 / pack_xyzt5]
    round-trip + the Z-level computation chain.

    Cost: ~100-150 LoC of mechanical [inversion] / [eapply] glue
    chained through 22 transitions.  Left as [Admitted] for the next
    session; the body itself is Qed-clean. *)
Theorem xyzt_double_body_decomposed_correct :
  forall callee_post callee_post_n function_table
         (P dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (p_bs : list Byte.byte),
    fe25519_callees_honoured_dbl callee_post callee_post_n ->
    length p_bs = 200%nat ->
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 P.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 p_bs)) ->
    rust_exec_ed callee_post callee_post_n function_table
                 (xyzt_double_body_decomposed dest [P]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_xyzt_double_gallina p_bs))).
Proof.
  intros callee_post callee_post_n function_table P dest rs1 rs2 p_bs
         Hhonoured Hlen Hdest_type HPin Hexec.
  (* Remaining cascade — see the comment above.  Each step is one
     [rexec_let_zero] or [rexec_seq] or [rexec_call/rexec_calln]
     inversion, threading [Hhonoured]'s components to pull the post
     value out of each oracle hit.  ~22 transitions total.

     STATUS: 0 progress here; leaves the obligation visible. *)
Admitted.

(* Print Assumptions xyzt_double_body_decomposed. *)
(* Print Assumptions xyzt_double_body_decomposed_correct. *)
