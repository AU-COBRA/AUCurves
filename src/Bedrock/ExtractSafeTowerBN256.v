(** * Safe Rust tower extraction for BN256 (5 limbs).
 *
 * Mirror of [ExtractSafeTowerBLS12.v].  bn256_Fp2.v has *closed*
 * function bodies for the Fp2 base ops (unlike bls12_Fp2.v), so we
 * include them in [bn256_tower_funcs] and let btranslate generate
 * their safe-Rust bodies — no hand-written wrappers needed.
 *
 * Excluded from the dune build (runs Coq's [Extraction "..."] command);
 * invoke manually after BN256_Pairing.vo is up-to-date.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.ToSafeRustBody.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn256_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.bn256_Fp2.
Require Import Bedrock.Field.Synthesis.Examples.BN256_Pairing.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Fp2 base ops (closed bodies, identical pattern to bn254). *)
(** Inline Fp2_opp: negate both Fp components.  bn256_Fp2.v doesn't
    define it (BN254's ExtractSafeRust.v uses the same workaround).
    Offset 32 = 4 limbs × 8 bytes for BN256. *)
Definition Fp2_opp_bn256 : function_t :=
  ("bn256_Fp2_opp", (["out"; "x"], []:list String.string,
    (Syntax.cmd.seq
      (Syntax.cmd.call [] "bn256_opp"
        [Syntax.expr.var "out"; Syntax.expr.var "x"])
      (Syntax.cmd.call [] "bn256_opp"
        [Syntax.expr.op Syntax.bopname.add (Syntax.expr.var "out") (Syntax.expr.literal (BinInt.Z.of_nat 32));
         Syntax.expr.op Syntax.bopname.add (Syntax.expr.var "x") (Syntax.expr.literal (BinInt.Z.of_nat 32))])))).

(** Fp2 base ops not already in bn256_all_pairing_funcs.
    (Fp2_mul_xi and Fp2_conjugate live in bn256_pairing_ops via Fp6/Fp12.) *)
Definition bn256_fp2_funcs : list function_t :=
  [ Fp2_felem_copy; Fp2_add; Fp2_sub; Fp2_mul; Fp2_sqr;
    Fp2_inv; Fp2_opp_bn256 ].

Definition bn256_tower_funcs : list function_t :=
  Eval vm_compute in
    (bn256_fp2_funcs ++ BN256_Pairing.bn256_all_pairing_funcs).

(** OCaml extraction (vm_compute string concatenation is too slow
    for towers of this size, same reason as BLS12). *)
From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "src/Bedrock/bn256_rust_extracted"
  bn256_tower_funcs safe_rust_fn type_decls safe_rust_module callee_types.
