(** * Safe Rust tower extraction for BLS12-377 (6 limbs).
 *
 * Mirror of [ExtractSafeTowerBN256.v].  [bls12_377_Fp2.v] has *closed*
 * function bodies for the Fp2 base ops (like bn256_Fp2.v, unlike
 * bls12_Fp2.v), so we include them in [bls377_tower_funcs] and let
 * btranslate generate their safe-Rust bodies — no hand-written
 * wrappers needed.
 *
 * Excluded from the dune build (runs Coq's [Extraction "..."] command);
 * invoke manually after [BLS12_377_Pairing.vo] and [bls12_377_Fp2.vo]
 * are up-to-date.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.ToSafeRustBody.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_Fp2.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_Pairing.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Fp2 base ops (closed bodies).  bls12_377_Fp2.v does not define an
    Fp2_opp; we inline it here exactly as ExtractSafeTowerBN256.v does
    for BN256 — negate each Fp component at offset 0 and offset 48
    (6 limbs × 8 bytes = 48-byte stride). *)
Definition Fp2_opp_bls377 : function_t :=
  ("bls377_Fp2_opp", (["out"; "x"], []:list String.string,
    (Syntax.cmd.seq
      (Syntax.cmd.call [] "bls377_opp"
        [Syntax.expr.var "out"; Syntax.expr.var "x"])
      (Syntax.cmd.call [] "bls377_opp"
        [Syntax.expr.op Syntax.bopname.add (Syntax.expr.var "out") (Syntax.expr.literal (BinInt.Z.of_nat 48));
         Syntax.expr.op Syntax.bopname.add (Syntax.expr.var "x") (Syntax.expr.literal (BinInt.Z.of_nat 48))])))).

(** Fp2 base ops not already in bls377_all_pairing_funcs.  Pulled out
    of [bls12_377_Fp2.v]; same shape as the BN256 / BN254 lists. *)
Definition bls377_fp2_funcs : list function_t :=
  [ Fp2_felem_copy; Fp2_add; Fp2_sub; Fp2_mul; Fp2_sqr;
    Fp2_inv; Fp2_opp_bls377 ].

Definition bls377_tower_funcs : list function_t :=
  Eval vm_compute in
    (bls377_fp2_funcs ++ BLS12_377_Pairing.bls377_all_pairing_funcs).

(** OCaml extraction (vm_compute string concatenation is too slow for
    towers of this size — same constraint as BN256 / BLS12-381). *)
From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

(* Rocq 9 puts extracted files alongside the .v source by default; pass
   -output-directory at compile time if a different location is needed.
   We just emit the basename. *)
Extraction "bls12_377_rust_extracted"
  bls377_tower_funcs safe_rust_fn type_decls safe_rust_module callee_types.
