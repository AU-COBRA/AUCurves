(** * X25519 scalar clamping at u64 granularity.
 *
 * Replaces fiat-crypto's [clamp] which uses [store1]/[load1] (byte ops)
 * — our [tr_cmd] in [Core.v] doesn't carry [access_size] through the
 * translation, so the byte ops would become u64 ops and clobber
 * adjacent bytes.  This file writes clamp directly at u64 granularity:
 *
 *   u64[0] &= 0xFFFFFFFFFFFFFFF8   (clears bottom 3 bits of byte 0)
 *   u64[3] &= 0x7FFFFFFFFFFFFFFF   (clears top bit of byte 31)
 *   u64[3] |= 0x4000000000000000   (sets bit 6 of byte 31)
 *
 * Each step is written as explicit load-to-temp, op-on-register,
 * store-from-temp so jasminc's asmgen sees only [Lvar]-based [Cassgn]
 * instructions.
 *)

From Stdlib Require Import ZArith String List.
From Stdlib Require Import Lia.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Import Syntax Syntax.Coercions NotationsCustomEntry.
Import ListNotations.

(** u64-granular clamp for X25519 scalars (32 bytes = 4 u64 limbs).
    Equivalent to fiat-crypto's clamp by bit-for-bit analysis. *)
(** Constants (u64):
    - [Z.pow 2 64 - 8 = 18446744073709551608 = 0xFFFFFFFFFFFFFFF8]
    - [Z.pow 2 63 - 1 = 9223372036854775807  = 0x7FFFFFFFFFFFFFFF]
    - [Z.pow 2 62     = 4611686018427387904  = 0x4000000000000000] *)
Definition clamp_64 := func! (sk) {
  tmp0 = load(sk);
  tmp0 = tmp0 & $18446744073709551608;
  store(sk, tmp0);
  tmp1 = load(sk + $24);
  tmp1 = tmp1 & $9223372036854775807;
  tmp1 = tmp1 | $4611686018427387904;
  store(sk + $24, tmp1)
}.
