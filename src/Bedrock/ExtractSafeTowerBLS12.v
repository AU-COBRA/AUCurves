(** * Safe Rust tower extraction for BLS12-381 (6 limbs). *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.ToSafeRustBody.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(* NOTE: The Fp2 base ops (bls12_Fp2_add/sub/mul/sqr/felem_copy) are NOT
   part of bls12_all_pairing_funcs because bls12_Fp2.v only has their
   WP proofs, not their closed function definitions (unlike bn254_Fp2.v).
   They are provided as trivial Rust wrappers at the top of the generated
   bls12_safe_tower.rs file — each is just two Fp ops on c0/c1.
   See project_safe_rust_pairing_bugs.md for the full explanation. *)
Definition bls12_tower_funcs : list function_t :=
  Eval vm_compute in
    BLS12_Pairing.bls12_all_pairing_funcs.

(** Use OCaml extraction for BLS12 — the tower is too large for
    vm_compute's O(n²) string concatenation (stack overflow).
    Same approach as ExtractSafeRust.v for the unsafe path. *)
From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "src/Bedrock/bls12_rust_extracted"
  bls12_tower_funcs safe_rust_fn type_decls safe_rust_module callee_types.
