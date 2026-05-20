(** * Fe25519InvertBodyV2 — divstep-based fe25519_invert (skeleton)
 *
 *  Adapts Bernstein–Chen–Harrison–Huang–Maxwell–Wang–Wuille–Yang,
 *  "Accelerating and verifying constant-time modular inversion",
 *  EUROCRYPT 2026 (doi:10.1007/978-3-032-25336-1_21).  Inverter 2X
 *  variant: saturated 4×u64 throughout, 10 outer iterations of 59
 *  divsteps each, δ₀ = 1/2.
 *
 *  Skeleton status: AST wiring is in place.  Three numeric leaves are
 *  external [REdCall] / [REdCallN] — their bodies are TODO, written
 *  either in safe Rust (slower, easier to verify) or as inline-asm
 *  wrappers around Harrison's s2n-bignum [bignum_inv_p25519].  See
 *  §2 for the contracts.
 *
 *  Replaces the 254-square + 11-multiplication Fermat chain in
 *  [Fe25519InvertBody.v] (~9000 cyc Skylake) with the paper's
 *  Inverter 2X (~4054 cyc Skylake, Table 1.2.1) — about 2.2× faster.
 *
 *  Bound: paper Theorem 1 with b = 256, δ₀ = 1/2:
 *      ⌈(9437·256 + 1)/4096⌉ = 590 divsteps   = 10 × 59
 *
 *  Type discipline: this body operates entirely on [TFp25519_64]
 *  (saturated 4×u64).  Call-sites that hold radix-2^51 [TFp25519]
 *  need a thin conversion wrapper — deferred until first benchmark
 *  to keep the skeleton minimal.
 *
 *  Correctness proof is not in this file.  When the leaves are
 *  pinned down, the spec to prove is the existing
 *  [Fe25519InvertCorrect.fe25519_invert_correct] statement —
 *  output is [a^(p-2) mod p] (= the inverse, or 0 on p|a).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Helpers                                                       *)
(* ================================================================ *)

Definition LFp64 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519_64 |}.

Definition LU64 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TU64 |}.

Fixpoint seqN (l : list rust_cmd_ed) : rust_cmd_ed :=
  match l with
  | [] => REdSkip
  | [c] => c
  | c :: cs => REdSeq c (seqN cs)
  end.

(* ================================================================ *)
(* §2. External-leaf contracts (TODO: implement)                     *)
(* ================================================================ *)
(*
 *  Three numeric leaves are called by this body.  All Fp25519_64
 *  arguments are 4×u64 saturated little-endian.
 *
 *  ─────────────────────────────────────────────────────────────────
 *  safegcd_init     [F; G; V; R; m] := (p, a, 0, 1, 0)
 *  ─────────────────────────────────────────────────────────────────
 *      REdCallN "safegcd_init"
 *               [F; G; V; R; m]            (5 outputs)
 *               [a]                        (1 input: Fp25519_64)
 *      F ← p = 2^255 - 19           (saturated 4×u64)
 *      G ← a                        (verbatim copy of input)
 *      V ← 0                        (additive identity)
 *      R ← 1                        (multiplicative identity)
 *      m ← 0                        (encodes δ₀ = 1/2 via 2δ-1 = 0;
 *                                    see paper §2.2 for the
 *                                    "δ ≥ 0 / 1-δ / 1+δ" mutation)
 *
 *  ─────────────────────────────────────────────────────────────────
 *  safegcd_step59   one outer iteration: 59 divsteps + matrix apply
 *  ─────────────────────────────────────────────────────────────────
 *      REdCallN "safegcd_step59"
 *               [F'; G'; V'; R'; m']       (5 outputs)
 *               [F;  G;  V;  R;  m]        (5 inputs)
 *      Performs 59 divsteps on the bottom limb of (F, G), assembling
 *      the implicit 2×2 word transition matrix (uu, vv, qq, rr) with
 *      |uu|,|vv|,|qq|,|rr| ≤ 2⁵⁹, then applies it to (F, G) and
 *      (V, R) with Montgomery-style squeeze modulo p:
 *          F' ← (uu·F + vv·G) / 2⁵⁹
 *          G' ← (qq·F + rr·G) / 2⁵⁹
 *          V' ← (uu·V + vv·R) mod p
 *          R' ← (qq·V + rr·R) mod p
 *      m' ← δ-state after 59 steps.
 *      Maps directly to the inner-loop body of Harrison's s2n-bignum
 *      [bignum_inv_p25519] (paper §6.3.2; arm64_bignum_inv_p25519.ml).
 *
 *  ─────────────────────────────────────────────────────────────────
 *  safegcd_finalize   sign-fix V; freeze modulo p
 *  ─────────────────────────────────────────────────────────────────
 *      REdCall "safegcd_finalize" out
 *              [V; F]                      (V, F : Fp25519_64)
 *      out ← if F < 0 (top bit of F[3]) then (p - V) mod p
 *            else V mod p,
 *      normalised into {0, …, p-1}.  After 590 divsteps with
 *      0 ≤ G ≤ F ≤ 2²⁵⁵, the paper guarantees G = 0 and F = ±1, so
 *      the sign of F determines whether V or -V is the inverse.
 *
 *  ─────────────────────────────────────────────────────────────────
 *  Plus two trivial 4×u64 copy leaves used as scratch-back moves:
 *      fe25519_64_copy   dst ← src        (32 bytes)
 *      u64_copy          dst ← src        (8 bytes)
 *  Both are pure memcpy; the existing Ed25519 stack already has
 *  fe25519_copy at the radix-2^51 layer.
 *)

(* ================================================================ *)
(* §3. One outer iteration                                           *)
(* ================================================================ *)

(** Outer-loop body.  Borrow check forbids in-place writes via
    [REdCallN dests args] when [dests ∩ args ≠ ∅], so we route the
    step output through *_new scratch slots and copy back.  Mirrors
    the [sqrN] pattern from [Fe25519InvertBody.v]. *)
Definition step59_outer_body : rust_cmd_ed :=
  REdSeq
    (REdCallN "safegcd_step59"
              [LFp64 "F_new"; LFp64 "G_new"; LFp64 "V_new"; LFp64 "R_new"; LU64 "m_new"]
              [LFp64 "F";     LFp64 "G";     LFp64 "V";     LFp64 "R";     LU64 "m"])
    (seqN
      [ REdCall "fe25519_64_copy" (LFp64 "F") [LFp64 "F_new"]
      ; REdCall "fe25519_64_copy" (LFp64 "G") [LFp64 "G_new"]
      ; REdCall "fe25519_64_copy" (LFp64 "V") [LFp64 "V_new"]
      ; REdCall "fe25519_64_copy" (LFp64 "R") [LFp64 "R_new"]
      ; REdCall "u64_copy"        (LU64 "m") [LU64 "m_new"]
      ]).

(* ================================================================ *)
(* §4. Top-level body                                                *)
(* ================================================================ *)

(** [fe25519_invert_v2_body dest [a_loc]]
 *
 *  Input  [a_loc] : TFp25519_64
 *  Output [dest]  : TFp25519_64 (= a^{-1} mod p, or 0 on p|a)
 *
 *  Slot layout (10 local slots):
 *      F, G, V, R           : TFp25519_64   running state
 *      F_new, G_new,
 *      V_new, R_new         : TFp25519_64   per-iteration scratch
 *      m, m_new             : TU64          δ-state + scratch
 *)
Definition fe25519_invert_v2_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc] =>
        REdLetZero "F"     TFp25519_64 (
        REdLetZero "G"     TFp25519_64 (
        REdLetZero "V"     TFp25519_64 (
        REdLetZero "R"     TFp25519_64 (
        REdLetZero "F_new" TFp25519_64 (
        REdLetZero "G_new" TFp25519_64 (
        REdLetZero "V_new" TFp25519_64 (
        REdLetZero "R_new" TFp25519_64 (
        REdLetZero "m"     TU64        (
        REdLetZero "m_new" TU64        (
          seqN
            [ (* §A. Initialise state from input a. *)
              REdCallN "safegcd_init"
                [LFp64 "F"; LFp64 "G"; LFp64 "V"; LFp64 "R"; LU64 "m"]
                [a_loc]
              (* §B. Ten outer iterations × 59 divsteps = 590 divsteps.
                    Sufficient by paper Theorem 1 for b = 256, δ₀ = 1/2. *)
            ; REdFor "_iter" 10 step59_outer_body
              (* §C. Sign-fix V and freeze modulo p. *)
            ; REdCall "safegcd_finalize" dest [LFp64 "V"; LFp64 "F"]
            ]
        ))))))))))
    | _ => REdSkip
    end.
