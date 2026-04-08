(** * ExtractSafeRust: Extract safe Rust wrappers to .rs files.
 *
 * Uses Rocq's [Redirect] command to write the generated Rust code
 * to standalone files for inclusion in Rust crates.
 *
 * Two layers are emitted:
 *   - Outer SAFE wrapper module ([bls12_381_safe.rs], [bn254_safe.rs]):
 *     newtype field types + [extern "C"] declarations + safe [pub fn]
 *     wrappers using [&T] / [&mut T] references. Built from a manually
 *     curated [wrapper_spec] list — independent of any bedrock2 source.
 *
 *   - Inner UNSAFE module ([bn254_pairing_inner.rs]): bedrock2 →
 *     unsafe Rust translation of the actual function bodies, via
 *     [ToRustString.rust_module]. The [extern "C"] symbols in the
 *     outer wrapper resolve to these.
 *
 * Path B (rust + jasmin, no C) takes both: outer + inner from this
 * extraction, leaf Fp ops swapped out for jasmin assembly via build.rs.
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.
Require Import Bedrock.ToSafeRustString.
Require Import Bedrock.ToRustString.

(** Print BLS12-381 safe wrappers. *)
Redirect "bls12_381_safe.rs" Eval vm_compute in bls12_381_safe_rust.

(** Print BN254 safe wrappers. *)
Redirect "bn254_safe.rs" Eval vm_compute in bn254_safe_rust.

(* ================================================================ *)
(* Inner unsafe-Rust extraction (Path B)                              *)
(* ================================================================ *)

Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_felem_copy.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Just the leaf Fp ops: smallest unit that's worth extracting alone.
    These are pure, non-recursive, no [stackalloc], no calls — the
    simplest test of [rust_func] / [rust_module]. *)
Definition bn254_leaf_funcs : list function_t :=
  [ bn254_add; bn254_sub; bn254_mul; bn254_square;
    bn254_select_znz;
    ("bn254_felem_copy", bn254_felem_copy) ].

(** OCaml extraction of [rust_func] / [rust_prelude] and the function list.
    The Coq pretty-printer stack-overflows on bedrock2 bodies because of
    O(n²) string concatenation in [String.append]; piping the same
    [rust_func] through OCaml's native strings (via [Extraction]) emits
    the same text in linear time. Mirrors the [ExtractBLS12Jasmin.v]
    workaround for the Jasmin pretty-printer. *)
From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "src/Bedrock/bn254_rust_extracted"
  bn254_leaf_funcs rust_func rust_prelude.
