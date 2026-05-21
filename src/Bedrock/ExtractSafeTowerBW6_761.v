(** * Safe Rust tower extraction for BW6-761 (12 limbs).
 *
 * Mirror of [ExtractSafeTowerBLS24_509.v].  BW6-761 has the tower
 * Fp -> Fp3 -> Fp6 (a CUBIC first extension instead of BLS24's
 * Fp2-Fp4-Fp8-Fp24), and the function list is already aggregated
 * in [BW6_761_Extract.bw6_all_funcs] (base Fp + GenericCubic Fp3
 * + GenericQuadratic Fp6 + mul-by-nr helpers + Miller loop + final
 * exponentiation).
 *
 * Excluded from the dune build (runs Coq's [Extraction "..."] command);
 * invoke manually after [BW6_761_Extract.vo] is up-to-date.
 *
 * Note: [BW6_761_FrobConsts.v] currently ships placeholder Frobenius
 * constants for the final exponentiation, so the extracted tower
 * will not produce gnark-compatible pairing outputs until those are
 * replaced with the SageMath-computed values for the BW6-761 prime.
 *)

Require Import Stdlib.Strings.String.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List. Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.ToSafeRustBody.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Extract.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Aggregate the BW6-761 tower functions, excluding the base [Fp]
    ops because those are provided by the hand-written extern-shim
    leaf wrappers in [bw6_761_safe_tower_main.ml] / [bw6-761-safe-rust/
    src/lib.rs] (forwarding to fiat-rust).  Mirrors the BLS12-377 /
    BLS24-509 pattern: skip the first 6 entries ([bw6_fp_funcs]),
    keep the tower + helpers + Miller + FinalExp. *)
Definition bw6_tower_funcs : list function_t :=
  Eval vm_compute in
    List.skipn 6 BW6_761_Extract.bw6_all_funcs.

(** OCaml extraction (vm_compute string concatenation is too slow for
    towers of this size — same constraint as BN256 / BLS12-377 /
    BLS24-509). *)
From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

(** Tower-shape-aware variants from ToSafeRustBody.v.  Wrap once with
    [bw6_761_tower] so the OCaml driver doesn't have to thread the
    shape itself. *)
Definition bw6_761_type_decls (n : BinNums.Z) : String.string :=
  type_decls_ts bw6_761_tower n.
Definition bw6_761_safe_rust_fn (n : BinNums.Z) (ptypes : list String.string)
    (func : function_t) : String.string :=
  safe_rust_fn_ts bw6_761_tower n ptypes func.
Definition bw6_761_safe_rust_module (n : BinNums.Z)
    (funcs : list function_t) : String.string :=
  safe_rust_module_ts bw6_761_tower n funcs.
Definition bw6_761_callee_types (f : String.string) (nargs : nat)
    : list String.string :=
  callee_types_ts bw6_761_tower f nargs.

Extraction "bw6_761_rust_extracted"
  bw6_tower_funcs
  bw6_761_safe_rust_fn bw6_761_type_decls
  bw6_761_safe_rust_module bw6_761_callee_types
  safe_rust_fn type_decls safe_rust_module callee_types.
