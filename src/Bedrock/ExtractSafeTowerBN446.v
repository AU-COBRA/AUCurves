(** * Safe Rust tower extraction for BN446 (7 limbs).
 *
 * Mirror of [ExtractSafeTowerBN256.v] / [ExtractSafeTowerBLS12.v].
 * bn446_Fp2.v has closed function bodies for the Fp2 base ops (same
 * pattern as BN254 / BN256), so we include them in [bn446_tower_funcs]
 * and let btranslate generate their safe-Rust bodies — no hand-written
 * Fp2 wrappers needed.
 *
 * Excluded from the dune build (runs Coq's [Extraction "..."] command);
 * invoke manually after BN446_Pairing.vo is up-to-date.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.ToSafeRustBody.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn446_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.bn446_Fp2.
Require Import Bedrock.Field.Synthesis.Examples.BN446_Pairing.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bn446_fp2_funcs : list function_t :=
  [ Fp2_felem_copy; Fp2_add; Fp2_sub; Fp2_mul; Fp2_sqr ].

Definition bn446_tower_funcs : list function_t :=
  Eval vm_compute in
    (bn446_fp2_funcs ++ BN446_Pairing.bn446_all_pairing_funcs).

From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "src/Bedrock/bn446_rust_extracted"
  bn446_tower_funcs safe_rust_fn type_decls safe_rust_module callee_types.
