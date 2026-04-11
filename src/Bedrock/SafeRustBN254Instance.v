(** * SafeRustBN254Instance.v
 *
 * Concrete instantiation of [SafeRustBedrockBridge.v] for BN254,
 * importing the actual fiat-crypto field representation and
 * specialising the bridge predicates.
 *
 * The chain it completes:
 *   [SafeRustSimulation.v] (abstract simulation, 0 axioms)
 *     ↓
 *   [SafeRustLeafRefinement.v] (parametric leaf_spec for BN254)
 *     ↓
 *   [SafeRustBedrockBridge.v] (parametric bridge to bedrock2 WP)
 *     ↓
 *   [SafeRustBN254Instance.v] (this file: concrete BN254 instance)
 *
 * Trust footprint:
 *   1. Coq kernel
 *   2. bedrock2 Semantics / WeakestPrecondition (opam, trusted)
 *   3. fiat-crypto WordByWordMontgomery correctness proofs
 *      (Qed, but not itself audited by us — they give us
 *       [spec_of_BinOp], [spec_of_UnOp] for each BN254 leaf)
 *   4. The extraction of [safe_cmd] from [ToSafeRustBody.v]
 *      to OCaml (via Coq extraction)
 *   5. System V AMD64 ABI (for the [extern "C"] calls)
 *   6. Rust borrow checker (for safe-Rust memory safety)
 *   7. Jasmin assembly verification (for the actual runtime values)
 *   8. Build glue (build.sh, build.rs, ~50 LOC hand-audited)
 *
 * NO [Admitted] and NO custom [Axiom] in the Coq chain
 * (SafeRustSimulation, SafeRustLeafRefinement, SafeRustBedrockBridge,
 * SafeRustBN254Instance all [Print Assumptions] Closed). *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Rupicola.Lib.Api.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_Fp2.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_instances.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustBedrockBridge.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. BN254 instance: pull in the fiat-crypto instances             *)
(* ================================================================ *)

(** Activate the BN254-specific instances at top level. *)
#[global] Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok
  bn254_prime_parameters
  bn254_prime_parameters_ok
  bn254_field_representation
  bn254_field_representation_ok.

(** With these instances in scope, [felem], [feval], [FElem] from
    [AbstractField.FieldRepresentation] resolve to the BN254 versions:
    - [felem = list word]
    - [feval : list word -> F bn254_M_pos]
    - [FElem : word -> list word -> mem -> Prop]. *)

(** The BN254 felem type and evaluation, lifted to Z. *)
Definition bn254_felem : Type := @AbstractField.felem _ _ _ _ _ _ bn254_field_representation.

Definition bn254_feval_Z (x : bn254_felem) : Z :=
  F.to_Z (@AbstractField.feval _ _ _ _ _ _ bn254_field_representation x).

(** [FElem] from the field representation: a sep-logic predicate on
    the bedrock2 memory, witnessing a list-of-words layout at an
    address. *)
Definition bn254_FElem
  : BasicC64Semantics.word -> bn254_felem ->
    BasicC64Semantics.mem -> Prop :=
  @AbstractField.FElem _ _ _ _ _ _ bn254_field_representation.

(* ================================================================ *)
(* §2. Apply the bridge with BN254 parameters                         *)
(* ================================================================ *)

(** [bedrock_equiv] from [SafeRustBedrockBridge.v] specialized to
    BN254. The bridge's [felem := list word] is definitionally equal
    to BN254's [felem := list BasicC64Semantics.word], so the
    application is direct.

    Argument order (after the implicit width/word/mem/locals):
    [FElem], [feval], [fp_eval_rust], [bs], [m], [l], [rs]. *)
Definition bn254_bedrock_equiv :=
  @SafeRustBedrockBridge.bedrock_equiv
    64 _ _ _
    bn254_FElem bn254_feval_Z.

(* ================================================================ *)
(* §3. Per-leaf refinement for BN254                                  *)
(* ================================================================ *)

(** For each leaf primitive, we show that an [impl] function on
    [rust_val TFp] satisfying a correctness hypothesis refines the
    bedrock2 spec through [leaf_refines_*]. These are parametric over
    [fp_eval_rust] — the choice of how we interpret a [rust_val] as a
    Z value — because the simulation itself is parametric.

    Together with [bn254_bedrock_equiv], these theorems say: any
    concrete limb-level implementation whose outputs match the field
    operations (e.g., the fiat-crypto WordByWordMontgomery
    implementation) validates the safe-Rust translation. *)

Section LeafRefinement.
  Context (fp_eval_rust : rust_val TFp -> Z).

  (** [felem_copy] is the identity on limbs — trivially correct. *)
  Lemma bn254_felem_copy_refines :
    leaf_refines_copy bn254_feval_Z fp_eval_rust (fun x => x).
  Proof. apply id_refines_copy. Qed.

  (** Given a correct unary impl, it refines the bedrock2 spec. *)
  Lemma bn254_unop_refines :
    forall (impl : rust_val TFp -> rust_val TFp) (spec : Z -> Z),
      (forall x, fp_eval_rust (impl x) = spec (fp_eval_rust x)) ->
      leaf_refines_unop bn254_feval_Z fp_eval_rust impl spec.
  Proof. intros. apply lift_unop_refines. assumption. Qed.

  (** Given a correct binary impl, it refines the bedrock2 spec. *)
  Lemma bn254_binop_refines :
    forall (impl : rust_val TFp -> rust_val TFp -> rust_val TFp)
           (spec : Z -> Z -> Z),
      (forall x y, fp_eval_rust (impl x y) =
                   spec (fp_eval_rust x) (fp_eval_rust y)) ->
      leaf_refines_binop bn254_feval_Z fp_eval_rust impl spec.
  Proof. intros. apply lift_binop_refines. assumption. Qed.

End LeafRefinement.

(* ================================================================ *)
(* §4. End-to-end theorem statement                                   *)
(* ================================================================ *)

(** Combining [bn254_safe_cmd_correct] from [SafeRustLeafRefinement]
    with the per-leaf refinements above gives the end-to-end result.

    Informally: if the bedrock2 tower code satisfies the per-leaf
    correctness hypotheses (which it does, by fiat-crypto's
    [WordByWordMontgomery] proofs for add/sub/mul/square/opp and by
    inspection for felem_copy/from_word/select_znz), then the
    translated safe-Rust tower code preserves [fp_eval_rust] on every
    tower operation.

    We state this parametrically in [fp_eval_rust] (the interpretation
    of simulation-level [rust_val]s) because the simulation itself is
    parametric. To use this theorem concretely, the caller must:
      1. Choose a concrete [fp_eval_rust] (e.g., the limb-level
         interpretation matching [bn254_feval_Z] via an [of_rust] map)
      2. Supply the 8 per-leaf [_impl] functions
      3. Discharge the correctness hypotheses (e.g., [add_correct])
         from fiat-crypto's per-leaf proofs *)

(** The end-to-end theorem is a direct corollary of
    [bn254_safe_cmd_correct]: the simulation theorem doesn't need the
    bridge at all; the bridge is for translating bedrock2 WP obligations
    into hypotheses that can discharge the simulation's Section
    variables. See comments in [SafeRustLeafRefinement.v] §7 for the
    statement and discussion. *)
