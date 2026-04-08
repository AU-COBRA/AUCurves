(* Transport proof sketch for secp256k1_mul_bignum_correct.

   This file demonstrates the proof approach interactively.
   It must be compiled FROM the fiat-crypto directory with:

     cd AUCurves/fiat-crypto
     eval $(opam env)
     coqc -Q src Crypto ../scripts/transport_proof_sketch.v

   This uses system-installed coqutil/bedrock2/coqprime (Rocq 9.0)
   plus the fiat-crypto src/ (compiled .vo files).

   Key insight: the proof just specializes Hspec with felem witnesses
   constructed from word lists, then the postcondition follows by
   computation (felem_to_list (exist _ ws pf) = ws). *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Secp256k1.Field256k1.

Import ListNotations.
Open Scope Z_scope.

Section Transport.
  Import BasicC64Semantics.
  Existing Instance Field256k1.field_parameters.
  Existing Instance Field256k1.frep256k1.

  Local Notation n := felem_size_in_words.

  (* Step 1: Understand what spec_of_BinOp gives us after unfolding *)
  (* Hspec : forall pout px py (x y : felem) (out : list byte) Rr tr mem,
       bounded_by bin_xbounds (felem_to_list x) /\
       bounded_by bin_ybounds (felem_to_list y) /\
       length out = felem_size_in_bytes /\
       (exists Rx, (FElem px x * Rx) mem) /\
       (exists Ry, (FElem py y * Ry) mem) /\
       (out$@pout * Rr) mem ->
       call functions mul tr mem [pout; px; py] (fun tr' mem' rets =>
         rets = nil /\ tr = tr' /\
         exists out : felem,
           feval (felem_to_list out) = bin_model ... /\
           bounded_by bin_outbounds (felem_to_list out) /\
           (FElem pout out * Rr) mem') *)

  (* Step 2: The transport specializes with:
     - x := exist _ wsx Hlenx  (felem from word list)
     - y := exist _ wsy Hleny
     - out := ??? (need bytes for the old output buffer)
     - Rr := Rout
     Then shows FElem px x = Bignum n px wsx (via FElem_iff_Bignum)
     and bounded_by tight_bounds wsx = valid (map unsigned wsx) (definitional) *)

  (* Step 3: The postcondition feval_to_list out unwraps to the word list
     and the decoding matches eval ∘ from_mont definitionally *)

  (* The main difficulty: constructing the byte buffer for the old output.
     Need: out : list byte of length felem_size_in_bytes such that
     (out$@pout * Rr) mem.
     From Bignum n pout wsold we get:
       array scalar (word.of_Z 8) pout wsold mem
     which by felem_to_bytearray gives:
       array ptsto (word.of_Z 1) pout (ws2bs 8 wsold) mem
     which by of_list_word_at gives:
       ((ws2bs 8 wsold)$@pout) mem
     So out := ws2bs 8 wsold works. *)

End Transport.
