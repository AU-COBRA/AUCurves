(** * Fe25519InvertBody — rust_cmd_ed AST for fe25519_invert
 *
 *  Computes `out := a^(p-2) mod p`, `p = 2^255 - 19`, via the standard
 *  254-square + 11-multiplication addition chain (Bernstein / dalek /
 *  libjade-equivalent recipe).  Mirrors the Lean authoring at
 *  [CatCrypt/Crypto/Jasmin/Examples/Fe25519Invert.lean].
 *
 *  Phase 2 of "extend the IR": hand-code a verified addition chain in
 *  rust_cmd_ed so the emitted Rust is covered by the verified emitter
 *  discipline ([RustCmdToRustSimulates.v]'s headline lemma plus the
 *  single named axiom [RustcExec_correct]).
 *
 *  Leaves (declared external — [REdCall]; their semantics is supplied
 *  by the caller's [callee_post] oracle):
 *    - fe25519_sqr  : (out a   : TFp25519) → unit
 *    - fe25519_mul  : (out a b : TFp25519) → unit
 *    - fe25519_copy : (out a   : TFp25519) → unit
 *
 *  The borrow checker (call_aliases_ed) requires dest ∉ args; we use a
 *  scratch [TFp25519] slot for the repeated-squaring inner loop and copy
 *  back to the named accumulator each iteration.
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
(* §1.  Helpers                                                      *)
(* ================================================================ *)

(** Construct a TFp25519 [located_ed] from a variable name. *)
Definition LFp (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

(** [REdCall "fe25519_sqr" dst [src]] — dst := src^2. *)
Definition sqr_call (dst src : String.string) : rust_cmd_ed :=
  REdCall "fe25519_sqr" (LFp dst) [LFp src].

(** [REdCall "fe25519_mul" dst [a; b]] — dst := a · b. *)
Definition mul_call (dst a b : String.string) : rust_cmd_ed :=
  REdCall "fe25519_mul" (LFp dst) [LFp a; LFp b].

(** [REdCall "fe25519_copy" dst [src]] — dst := src. *)
Definition copy_call (dst src : String.string) : rust_cmd_ed :=
  REdCall "fe25519_copy" (LFp dst) [LFp src].

(** [n] squarings of [acc] (in place), via the bounded for-loop.
    Uses a separate [scratch] slot to avoid the alias
    [fe25519_sqr(&mut tmp, &tmp)] which the borrow checker rejects.
    Body each iteration:
        scratch := acc^2
        acc     := scratch          (verified copy leaf)
    After [n] iterations, [acc] holds the n-th iterated square. *)
Definition sqrN (n : nat) (acc scratch : String.string) : rust_cmd_ed :=
  REdFor "_i" n
    (REdSeq
      (sqr_call scratch acc)
      (copy_call acc scratch)).

(** Sequence a list of commands left-to-right. *)
Fixpoint seqN (l : list rust_cmd_ed) : rust_cmd_ed :=
  match l with
  | [] => REdSkip
  | [c] => c
  | c :: cs => REdSeq c (seqN cs)
  end.

(* ================================================================ *)
(* §2.  fe25519_invert body                                          *)
(* ================================================================ *)

(** The classical addition chain (matches dalek's Fe51::invert):

      z2     = a^2                                  -- 1 sqr
      t      = z2^4                                 -- 2 sqr
      z9     = t · a                                -- 1 mul
      z11    = z9 · z2                              -- 1 mul
      t      = z11^2                                -- 1 sqr
      z2_5_0 = t · z9                               -- 1 mul     [a^31]
      t      = z2_5_0^32                            -- 5 sqr
      z2_10_0= t · z2_5_0                           -- 1 mul     [a^(2^10-1)]
      t      = z2_10_0^1024                         -- 10 sqr
      z2_20_0= t · z2_10_0                          -- 1 mul     [a^(2^20-1)]
      t      = z2_20_0^(2^20)                       -- 20 sqr
      z2_40_0= t · z2_20_0                          -- 1 mul     [a^(2^40-1)]
      t      = z2_40_0^(2^10)                       -- 10 sqr
      z2_50_0= t · z2_10_0                          -- 1 mul     [a^(2^50-1)]
      t      = z2_50_0^(2^50)                       -- 50 sqr
      z2_100_0=t · z2_50_0                          -- 1 mul     [a^(2^100-1)]
      t      = z2_100_0^(2^100)                     -- 100 sqr
      t2     = t · z2_100_0                         -- 1 mul     [a^(2^200-1)]
      t      = t2^(2^50)                            -- 50 sqr
      t3     = t · z2_50_0                          -- 1 mul     [a^(2^250-1)]
      t      = t3^32                                -- 5 sqr
      out    = t · z11                              -- 1 mul     [a^(p-2)]

    Total: 1+2+1+5+10+20+10+50+100+50+5 = 254 squarings, 11 multiplies. *)

Definition fe25519_invert_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc] =>
        (* Slot declarations — 13 fresh TFp25519 locals. *)
        REdLetZero "tmp"      TFp25519 (
        REdLetZero "scratch"  TFp25519 (
        REdLetZero "z2"       TFp25519 (
        REdLetZero "z9"       TFp25519 (
        REdLetZero "z11"      TFp25519 (
        REdLetZero "z2_5_0"   TFp25519 (
        REdLetZero "z2_10_0"  TFp25519 (
        REdLetZero "z2_20_0"  TFp25519 (
        REdLetZero "z2_40_0"  TFp25519 (
        REdLetZero "z2_50_0"  TFp25519 (
        REdLetZero "z2_100_0" TFp25519 (
        REdLetZero "t2"       TFp25519 (
        REdLetZero "t3"       TFp25519 (
        seqN
          [ (* z2 = a^2 *)
            REdCall "fe25519_sqr" (LFp "z2") [a_loc];
            (* tmp = z2^4 = a^8  (two squarings, ping-pong via scratch) *)
            sqr_call "tmp" "z2";
            sqr_call "scratch" "tmp";
            copy_call "tmp" "scratch";
            (* z9 = tmp · a *)
            REdCall "fe25519_mul" (LFp "z9") [LFp "tmp"; a_loc];
            (* z11 = z9 · z2 *)
            mul_call "z11" "z9" "z2";
            (* tmp = z11^2 *)
            sqr_call "tmp" "z11";
            (* z2_5_0 = tmp · z9 *)
            mul_call "z2_5_0" "tmp" "z9";
            (* tmp = z2_5_0^32  (5 squarings) *)
            sqr_call "tmp" "z2_5_0";
            sqrN 4 "tmp" "scratch";
            (* z2_10_0 = tmp · z2_5_0 *)
            mul_call "z2_10_0" "tmp" "z2_5_0";
            (* tmp = z2_10_0^1024  (10 squarings) *)
            sqr_call "tmp" "z2_10_0";
            sqrN 9 "tmp" "scratch";
            (* z2_20_0 = tmp · z2_10_0 *)
            mul_call "z2_20_0" "tmp" "z2_10_0";
            (* tmp = z2_20_0^(2^20)  (20 squarings) *)
            sqr_call "tmp" "z2_20_0";
            sqrN 19 "tmp" "scratch";
            (* z2_40_0 = tmp · z2_20_0 *)
            mul_call "z2_40_0" "tmp" "z2_20_0";
            (* tmp = z2_40_0^(2^10)  (10 squarings) *)
            sqr_call "tmp" "z2_40_0";
            sqrN 9 "tmp" "scratch";
            (* z2_50_0 = tmp · z2_10_0 *)
            mul_call "z2_50_0" "tmp" "z2_10_0";
            (* tmp = z2_50_0^(2^50)  (50 squarings) *)
            sqr_call "tmp" "z2_50_0";
            sqrN 49 "tmp" "scratch";
            (* z2_100_0 = tmp · z2_50_0 *)
            mul_call "z2_100_0" "tmp" "z2_50_0";
            (* tmp = z2_100_0^(2^100)  (100 squarings) *)
            sqr_call "tmp" "z2_100_0";
            sqrN 99 "tmp" "scratch";
            (* t2 = tmp · z2_100_0 *)
            mul_call "t2" "tmp" "z2_100_0";
            (* tmp = t2^(2^50)  (50 squarings) *)
            sqr_call "tmp" "t2";
            sqrN 49 "tmp" "scratch";
            (* t3 = tmp · z2_50_0 *)
            mul_call "t3" "tmp" "z2_50_0";
            (* tmp = t3^32  (5 squarings) *)
            sqr_call "tmp" "t3";
            sqrN 4 "tmp" "scratch";
            (* out = tmp · z11 *)
            REdCall "fe25519_mul" dest [LFp "tmp"; LFp "z11"]
          ]
        )))))))))))))
    | _ => REdSkip
    end.
