(** * OCaml extraction of the BLS12-381 pairing function list together
 *    with [to_jasmin_sized] and the flatten pass.
 *
 *    **STATUS (2026-04-14): DEPRECATED — text-based extraction.**
 *    The verified replacement is [ExtractBLS12JasminAST.v], which
 *    uses [JasminBridgeReal.to_jasmin_cmd] (AST → AST) instead of
 *    the unverified [pp_module] pretty-printer.  See
 *    [feedback_tojasmin_ast_path.md].
 *
 *    This file deliberately AVOIDS [Eval vm_compute in c_module ...] —
 *    that idiom in BLS12_Extract.v / BLS24_509_Extract.v hits a stack
 *    overflow because of the O(n²) string concatenation in the
 *    pretty-printer.  Instead we extract the symbolic function list
 *    to OCaml and let the OCaml-level pretty-printer (using native
 *    strings) emit the .jazz text in linear time.
 *
 *    Build:
 *      make EXTERNAL_DEPENDENCIES=1 \
 *        src/Bedrock/Field/FieldExtensions/ExtractBLS12Jasmin.vo
 *
 *    Output:
 *      src/Bedrock/Field/FieldExtensions/bls12_jasmin_extracted.ml
 *)

From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
(* Deliberately NOT [ExtrOcamlZInt]: it maps Coq's [Z] to OCaml's
   63-bit [int], which silently overflows on the curve constants
   (2^64-sized field-modulus limbs and the [u64_max]-normalized
   negative literals).  Without that directive, [Z] is extracted as
   its [Z0 | Zpos | Zneg] inductive, and arithmetic stays exact. *)
From Stdlib Require Import ZArith String Ascii.
Require Import bedrock2.Syntax.

Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.FlattenStackalloc.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Same construction as [BLS12_Extract.all_funcs], but no [vm_compute]
    of [c_module] follows. *)

Definition bls12_fp_base_funcs : list function_t :=
  [ bls12_add; bls12_sub; bls12_mul; bls12_square;
    bls12_select_znz;
    ("bls12_felem_copy", bls12_felem_copy) ].

(** [vm_compute] is essential here.  Without it, function-tower size
    constants like [felem_size_in_bytes (F:=Fp2)] remain as opaque
    typeclass-projected calls in the extracted OCaml.  Those then
    extract to [int]-returning stubs that default to 0, which causes
    the Jasmin emitter to produce [stack u64[0]] declarations and a
    parse error in jasminc.  Forcing reduction here pins each
    [stackalloc] to a literal byte size.  This is much cheaper than
    [vm_compute]ing [c_module ...] (which is what BLS12_Extract.v
    does and what hits the O(n²) string-concat stack overflow). *)
Definition bls12_all_funcs_raw : list function_t :=
  bls12_fp_base_funcs ++ BLS12_Pairing.bls12_all_pairing_funcs.

Definition bls12_all_funcs : list function_t :=
  Eval vm_compute in bls12_all_funcs_raw.

(** BLS12-381 field elements are 6 u64 limbs. *)
Definition bls12_field_size : Z := 6.

(** Tower mul/sqr functions are the candidates for stackalloc flattening. *)
Definition bls12_flatten_targets : list String.string :=
  ["bls12_Fp2_mul"; "bls12_Fp2_square";
   "bls12_Fp6_mul"; "bls12_Fp6_square";
   "bls12_Fp12_mul"; "bls12_Fp12_square";
   "bls12_Fp12_inv";
   "bls12_Fp6_mul_by_v"; "bls12_Fp12_mul_by_w"].

Definition bls12_optimized_funcs : list function_t :=
  flatten_selected bls12_flatten_targets bls12_all_funcs.

(** Pre-translate to [jasmin_func] in Coq.  Doing the [tr_func] /
    [tr_cmd] pass here means the [JTstack] sizes are reduced to
    literal integers and the OCaml-side [Z.div]/[Z.add] (which under
    [ExtrOcamlZInt] still walk a binary positive representation
    instead of doing native int arithmetic) is bypassed entirely. *)
Definition bls12_all_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized bls12_field_size f))
             bls12_all_funcs.

Definition bls12_optimized_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized bls12_field_size f))
             bls12_optimized_funcs.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

(** [bls12_all_jasmin] / [bls12_optimized_jasmin] are fully [vm_compute]d:
    every reference to a typeclass-projected size constant has been
    reduced to a literal [Z], and the [tr_cmd] / [tr_func_sized] pass
    has already been applied.  Monolithic [Extraction] of these two
    values therefore does not transitively pull in [BLS12_Pairing]'s
    [Module Fp12.] (the source-level module structure that breaks
    [Separate Extraction] because of the [find]/[O]/[S] gaps in
    Coq's per-module emission for [Init.Datatypes] / Stdlib [List]).

    We also extract [pp_module] so the driver only has to do a final
    pretty-print + [string] -> [Bytes]. *)
Extraction "bls12_jasmin_extracted"
  bls12_all_jasmin bls12_optimized_jasmin
  bls12_field_size
  pp_func pp_module.
