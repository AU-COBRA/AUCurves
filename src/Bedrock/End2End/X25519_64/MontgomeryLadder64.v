(** * X25519 Montgomery ladder — 64-bit, 5-limb.
 *
 * 64-bit counterpart of fiat-crypto's [Bedrock.End2End.X25519.MontgomeryLadder].
 * Uses [Field25519_64] (5-limb unsaturated Solinas on 64-bit words) instead of
 * [Field25519] (10-limb on 32-bit words).
 *
 * The generic ladder step, montladder, x25519 function definitions, and their
 * WP proofs are inherited from fiat-crypto's [Group.ScalarMult.*] and
 * [Group.AdditionChains].  This file only wires in the 64-bit field instances.
 *)

From Coq Require Import String List ZArith.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Spec.MontgomeryCurve.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Bedrock.Specs.Field.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import bedrock2.SepAutoArray.
Require Import bedrock2.ZnWords.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.AdditionChains.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
(* Use our u64-granular clamp (bedrock2's fiat-crypto clamp uses byte
   ops which our tr_cmd doesn't carry through to jasmin_cmd). *)
Require Import Bedrock.End2End.X25519_64.clamp_64.

(* Import our 64-bit field *)
Require Import Bedrock.End2End.X25519_64.Field25519_64.

Require Import coqutil.Macros.WithBaseName.

Local Open Scope string_scope.
Import ListNotations.

Local Existing Instance frep25519.
Local Existing Instance frep25519_ok.

Derive ladderstep SuchThat (ladderstep = ladderstep_body) As ladderstep_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Derive montladder SuchThat (montladder = montladder_body (Z.to_nat (Z.log2 Curve25519.order)))
       As montladder_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Require Import bedrock2.NotationsCustomEntry.

(** x25519: clamp in-place on the input scalar pointer, then ladder.
    For a production version we'd copy sk to a stack buffer first
    (via memmove), but for extraction this suffices. *)
Definition x25519 := func! (out, sk, pk) {
  clamp_64(sk);
  stackalloc 40 as U;
  fe25519_from_bytes(U, pk);
  stackalloc 40 as OUT;
  montladder(OUT, sk, U);
  fe25519_to_bytes(out, OUT)
}.

Definition x25519_base := func! (out, sk) {
  clamp_64(sk);
  stackalloc 40 as U;
  fe25519_from_word(U, $9);
  stackalloc 40 as OUT;
  montladder(OUT, sk, U);
  fe25519_to_bytes(out, OUT)
}.

(* ================================================================ *)
(* Function list for extraction                                      *)
(* ================================================================ *)

Definition felem_cswap := CSwap.felem_cswap(word:=BasicC64Semantics.word)(field_parameters:=field_parameters)(field_representaton:=field_representation n s c).
Definition fe25519_inv := fe25519_inv(word:=BasicC64Semantics.word)(field_parameters:=field_parameters).

Definition funcs :=
  &[,x25519; x25519_base;
    montladder;
    fe25519_to_bytes;
    fe25519_from_bytes;
    fe25519_from_word;
    felem_cswap;
    fe25519_copy;
    fe25519_inv;
    ladderstep;
    fe25519_mul;
    fe25519_add;
    fe25519_sub;
    fe25519_square;
    fe25519_scmula24;
    clamp_64 ].

(* ================================================================ *)
(* ToCString / ToJasmin extraction                                   *)
(* ================================================================ *)

Require Import bedrock2.ToCString.
Definition x25519_c_module := list_byte_of_string (ToCString.c_module funcs).

Require Import Bedrock.Jasmin.Core.
Definition x25519_jasmin_module := to_jasmin_sized 5 funcs.
