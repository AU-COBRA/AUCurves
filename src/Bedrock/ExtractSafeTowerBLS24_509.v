(** * Safe Rust tower extraction for BLS24-509 (8 limbs).
 *
 * Mirror of [ExtractSafeTowerBN256.v] / [ExtractSafeTowerBLS12_377.v].
 * BLS24-509 has the (different) tower Fp → Fp2 → Fp4 → Fp8 → Fp24, and
 * the function list is already aggregated in
 * [BLS24_509_Extract.bls24_all_funcs], so we can reuse it directly
 * (it composes [bls24_fp_funcs ++ bls24_Fp2_funcs ++ bls24_Fp4_funcs ++
 * bls24_Fp8_funcs ++ bls24_Fp24_funcs ++ MillerLoop / FinalExp /
 * pairing entries] — see [BLS24_509_Extract.v]).
 *
 * Excluded from the dune build (runs Coq's [Extraction "..."] command);
 * invoke manually after [BLS24_509_Extract.vo] is up-to-date.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.ToSafeRustBody.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_Extract.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Reuse the aggregated function list from BLS24_509_Extract.v.
    This already covers the full Fp/Fp2/Fp4/Fp8/Fp24 tower + Miller
    loop + final exponentiation + pairing. *)
Definition bls24_tower_funcs : list function_t :=
  Eval vm_compute in BLS24_509_Extract.bls24_all_funcs.

(** OCaml extraction (vm_compute string concatenation is too slow for
    towers of this size — same constraint as BN256 / BLS12-377). *)
From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "bls24_509_rust_extracted"
  bls24_tower_funcs safe_rust_fn type_decls safe_rust_module callee_types.
