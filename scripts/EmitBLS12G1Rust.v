(** Driver for scripts/emit_bls12_g1_rust.sh: prints
    [BLS12_G1ArenaRust.bls12_g1_rs] (the Rust text) to bls12_g1.out in
    the current directory.  Not part of the dune build (it writes a
    file); see the script. *)
Require Import Stdlib.Strings.String.
Require Import Bedrock.BLS12_G1ArenaRust.
Open Scope string_scope.
Set Printing Depth 1000000.
Set Printing Width 1000000.
Redirect "bls12_g1" Eval vm_compute in bls12_g1_rs.
