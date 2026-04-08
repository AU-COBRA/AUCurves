(** * ExtractSafeRust: Extract safe Rust wrappers to .rs files.
 *
 * Uses Rocq's [Redirect] command to write the generated Rust code
 * to standalone files for inclusion in Rust crates.
 *)

Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Bedrock.ToSafeRustString.

(** Print BLS12-381 safe wrappers. *)
Redirect "bls12_381_safe.rs" Eval vm_compute in bls12_381_safe_rust.

(** Print BN254 safe wrappers. *)
Redirect "bn254_safe.rs" Eval vm_compute in bn254_safe_rust.
