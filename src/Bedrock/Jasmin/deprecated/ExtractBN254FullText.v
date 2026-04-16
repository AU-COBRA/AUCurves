(** * Full BN254 Jasmin extraction.
 *
 *    **STATUS (2026-04-14): TEXT PRETTY-PRINTER OUTPUT IS DEPRECATED.**
 *    The [bn254_full_jasmin] AST list this driver builds is still
 *    consumed by the verified AST pipeline, but the [pp_module] /
 *    [.jazz]-text output it emits is unverified and superseded.
 *    Verified path (parallel to BLS12 ast2ast_main.ml):
 *      - [bn254_full_jasmin] (this file)             — function-list AST
 *      - [bridge_simple_v2.ml]                       — extracted JasminBridgeReal
 *      - [bn254_ast2ast_main.ml] + [build_bn254_ast2ast.sh]
 *                                                    — 30-line OCaml glue
 *    A direct AST driver inside fiat-crypto cannot be written: combining
 *    [JasminBridgeReal] with any [bn254_prime] importer triggers a
 *    universe inconsistency on [Morphisms.Proper] (see
 *    [project_unipoly_rebuild.md]).  Hence the two-extraction +
 *    Obj.magic-cast pattern.  See [feedback_tojasmin_ast_path.md].
 *
 *    Combines:
 *      - base Fp ops    (bn254_add/sub/mul/square/select_znz/felem_copy)
 *      - base Fp2 ops   (Fp2_add/sub/mul/square/inv/felem_copy/zero/one)
 *      - pairing funcs  (Fp6, Fp12, line, frobenius, miller, final_exp, …)
 *      - optimized ops  (sparse fp12_mul_line, cyclotomic fp12_cyc_sqr)
 *
 *    Mirrors the structure of [ExtractBLS12Jasmin.v] but pulls in the
 *    full BN254 pairing function list from [BN254_Extract.v] instead of
 *    just the base Fp ops.
 *
 *    Build:
 *      make EXTERNAL_DEPENDENCIES=1 \
 *        src/Bedrock/Field/FieldExtensions/ExtractBN254FullJasmin.vo
 *
 *    Output:
 *      src/Bedrock/Field/FieldExtensions/bn254_full_jasmin_extracted.ml
 *)

From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
(* Deliberately NOT [ExtrOcamlZInt] — see ExtractBLS12Jasmin.v *)
From Stdlib Require Import ZArith String Ascii.
Require Import bedrock2.Syntax.

Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_Fp2.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN254_Pairing.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN254_OptimizedOps.

Require Import Bedrock.Jasmin.Core.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Same construction as [BN254_Extract.all_funcs], plus the optimized ops. *)
Definition bn254_fp_base_funcs : list function_t :=
  [ bn254_add; bn254_sub; bn254_mul; bn254_square;
    bn254_select_znz;
    ("bn254_felem_copy", bn254_felem_copy) ].

(** [Fp2_zero] and [Fp2_one] are intentionally omitted: they call
    [bn254_from_word], which is never synthesized in [bn254_prime.v].
    The pairing pipeline never uses them — initial constants live in
    Frobenius load helpers — so dropping them lets jasminc resolve all
    cross-function calls. *)
Definition bn254_fp2_base_funcs : list function_t :=
  [ Fp2_felem_copy; Fp2_add; Fp2_sub;
    Fp2_mul; Fp2_sqr; Fp2_inv ].

Definition bn254_full_funcs_raw : list function_t :=
  bn254_fp_base_funcs ++
  bn254_fp2_base_funcs ++
  BN254_Pairing.bn254_all_pairing_funcs ++
  bn254_opt_funcs.

(** [vm_compute] reduces all the [felem_size_in_bytes (F:=Fp_k)] typeclass
    projections to literal byte sizes — required so that [tr_cmd] sees
    real integers in [stackalloc] arguments and emits non-zero
    [stack u64[N]] declarations.  See ExtractBLS12Jasmin.v for the
    rationale. *)
Definition bn254_full_funcs : list function_t :=
  Eval vm_compute in bn254_full_funcs_raw.

(** BN254 field elements are 4 u64 limbs. *)
Definition bn254_full_field_size : Z := 4.

Definition bn254_full_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized bn254_full_field_size f))
             bn254_full_funcs.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "bn254_full_jasmin_extracted"
  bn254_full_jasmin
  bn254_full_field_size
  pp_func pp_module.
