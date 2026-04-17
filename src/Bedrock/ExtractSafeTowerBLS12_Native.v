(** * Coq-level bit-exact extraction of BLS12 safe-Rust tower bodies.
 *
 * Companion to [ExtractSafeTowerBLS12.v] (which uses OCaml extraction
 * because vm_compute hits stack overflow on the larger BLS12 bodies).
 *
 * This file uses [native_compute] + [Redirect] to dump the *body
 * portion* of the BLS12 safe-Rust tower (i.e. the output of
 * [safe_rust_module 6 bls12_tower_funcs], without the [type_decls]
 * preamble or hand-added leaf wrappers).
 *
 * The output goes to [bls12_safe_tower_bodies_native.rs.out] and can
 * be byte-compared to the corresponding slice of the committed
 * [bls12-381-safe-rust/generated/bls12_safe_tower.rs] (i.e. everything
 * after the leaf wrapper block).  The driver-level bit-exact check is
 * in [scripts/check_bls12_extraction.sh].
 *
 * Excluded from the dune build (heavy native_compute); invoke
 * manually after [BLS12_Pairing.vo] is up-to-date.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.ToSafeRustBody.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bls12_tower_funcs : list function_t :=
  Eval native_compute in BLS12_Pairing.bls12_all_pairing_funcs.

Definition bls12_safe_tower_bodies : string :=
  Eval native_compute in safe_rust_module 6 bls12_tower_funcs.

Redirect "bls12_safe_tower_bodies_native.rs"
  Eval native_compute in bls12_safe_tower_bodies.
