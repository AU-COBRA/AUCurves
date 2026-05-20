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

(** Aggregate the BLS24-509 tower functions, excluding the base [Fp]
    ops because those are provided by the hand-written extern-C leaf
    wrappers in [bls24_509_safe_tower_main.ml] (compiled from Jasmin
    assembly).  Mirrors the BLS12-377 pattern (see
    [ExtractSafeTowerBLS12_377.v]: skip [fp_funcs], include Fp2/.../
    + MillerLoop + FinalExp).

    [bls24_fp_funcs] is the first 6 entries (add/sub/mul/square/opp/
    felem_copy of the base Fp ops); we [List.skipn 6] to drop them
    while still reusing the already-vm_computed [bls24_all_funcs]. *)
Definition bls24_tower_funcs : list function_t :=
  Eval vm_compute in
    List.skipn 6 BLS24_509_Extract.bls24_all_funcs.

(** OCaml extraction (vm_compute string concatenation is too slow for
    towers of this size — same constraint as BN256 / BLS12-377). *)
From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

(** Tower-shape-aware variants from ToSafeRustBody.v.  Wrap once with
    [bls24_509_tower] so the OCaml driver doesn't have to thread the
    shape itself. *)
Definition bls24_509_type_decls (n : BinNums.Z) : String.string :=
  type_decls_ts bls24_509_tower n.
Definition bls24_509_safe_rust_fn (n : BinNums.Z) (ptypes : list String.string)
    (func : function_t) : String.string :=
  safe_rust_fn_ts bls24_509_tower n ptypes func.
Definition bls24_509_safe_rust_module (n : BinNums.Z)
    (funcs : list function_t) : String.string :=
  safe_rust_module_ts bls24_509_tower n funcs.
Definition bls24_509_callee_types (f : String.string) (nargs : nat)
    : list String.string :=
  callee_types_ts bls24_509_tower f nargs.

Extraction "bls24_509_rust_extracted"
  bls24_tower_funcs
  bls24_509_safe_rust_fn bls24_509_type_decls
  bls24_509_safe_rust_module bls24_509_callee_types
  safe_rust_fn type_decls safe_rust_module callee_types.
