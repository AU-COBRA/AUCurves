(** * The contracts of the BLS12-381 Fp leaves, as bedrock2 executions of their bodies.

    These are fiat-crypto's [spec_of_BinOp bin_add / bin_sub / bin_mul] and
    [spec_of_UnOp un_square] for [bls12_frep] (Bedrock.Field.Synthesis.Examples.bls12_prime),
    unfolded: felems as lists of 6 words, [bounded_by] as WordByWordMontgomery.valid, [feval] as
    the Montgomery evaluation, [Semantics.call] as [exec] of the body.  They are stated here,
    with no dependency on fiat-crypto's synthesis pipeline, because that pipeline cannot be
    loaded together with Jasmin's semantics (universe inconsistency through ITree);
    [BLS12LeafSpecsProof] proves each of them from fiat-crypto's correctness lemma, and the
    Jasmin side ([JasminBridge.Ast.BLS12LeafThms]) uses them as premises. *)
From Stdlib Require Import String List ZArith.
Import ListNotations.
Require Import coqutil.Word.Interface coqutil.Map.Interface coqutil.Map.OfListWord coqutil.Byte.
Require Import bedrock2.Syntax bedrock2.Semantics bedrock2.Map.Separation bedrock2.Array bedrock2.Scalars.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.Core Crypto.Arithmetic.UniformWeight Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.JasminAst.BLS12LeafBodies.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition bls12_p : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Definition bls12_p_pos : positive := Z.to_pos bls12_p.
(** -p^-1 mod 2^64, fiat-crypto's [WordByWordMontgomery.m' m 64]. *)
Definition bls12_mprime : Z := 0x89f3fffcfffcfffd.

(** fiat-crypto's [feval] and [bounded_by] of [bls12_frep]. *)
Definition eval_w (ws : list word) : F bls12_p_pos :=
  F.of_Z bls12_p_pos (Positional.eval (uweight 64) 6
    (WordByWordMontgomery.from_montgomerymod 64 6 bls12_p bls12_mprime (List.map word.unsigned ws))).
Definition valid_w (ws : list word) : Prop :=
  WordByWordMontgomery.valid 64 6 bls12_p (List.map word.unsigned ws).

Definition felem_at (p : word) (x : list word) : mem -> Prop := array scalar (word.of_Z 8) p x.

Definition params3 : list string := ["out0"; "in0"; "in1"].
Definition params2 : list string := ["out0"; "in0"].

Definition binop_pre (pout px py : word) (x y : list word) (out : list byte) (Rr : mem -> Prop)
    (m : mem) : Prop :=
  length x = 6%nat /\ length y = 6%nat /\ valid_w x /\ valid_w y /\ length out = 48%nat /\
  (exists Rx, sep (felem_at px x) Rx m) /\ (exists Ry, sep (felem_at py y) Ry m) /\
  sep (sepclause_of_map (map.of_list_word_at pout out)) Rr m.

Definition unop_pre (pout px : word) (x : list word) (out : list byte) (Rr : mem -> Prop)
    (m : mem) : Prop :=
  length x = 6%nat /\ valid_w x /\ length out = 48%nat /\
  (exists Rx, sep (felem_at px x) Rx m) /\
  sep (sepclause_of_map (map.of_list_word_at pout out)) Rr m.

Definition result_post (pout : word) (v : F bls12_p_pos) (Rr : mem -> Prop) (m' : mem) : Prop :=
  exists out' : list word, length out' = 6%nat /\ eval_w out' = v /\ valid_w out' /\
    sep (felem_at pout out') Rr m'.

(** Bridge propositions: the body runs, from the arguments bound to its parameters, to the
    postcondition of fiat-crypto's contract. *)
Definition binop_contract (body : cmd) (model : F bls12_p_pos -> F bls12_p_pos -> F bls12_p_pos) : Prop :=
  forall (pout px py : word) (x y : list word) (out : list byte) (Rr : mem -> Prop) (t : trace) (m : mem),
    binop_pre pout px py x y out Rr m ->
    exists (fenv : env) (l : locals), map.of_list_zip params3 [pout; px; py] = Some l /\
      exec fenv body t m l (fun t' m' _ => t' = t /\
        result_post pout (model (eval_w x) (eval_w y)) Rr m').

Definition unop_contract (body : cmd) (model : F bls12_p_pos -> F bls12_p_pos) : Prop :=
  forall (pout px : word) (x : list word) (out : list byte) (Rr : mem -> Prop) (t : trace) (m : mem),
    unop_pre pout px x out Rr m ->
    exists (fenv : env) (l : locals), map.of_list_zip params2 [pout; px] = Some l /\
      exec fenv body t m l (fun t' m' _ => t' = t /\ result_post pout (model (eval_w x)) Rr m').

Definition bls12_add_contract : Prop := binop_contract bls12_add_body F.add.
Definition bls12_sub_contract : Prop := binop_contract bls12_sub_body F.sub.
Definition bls12_mul_contract : Prop := binop_contract bls12_mul_body F.mul.
Definition bls12_square_contract : Prop := unop_contract bls12_square_body (fun x => F.pow x 2).
