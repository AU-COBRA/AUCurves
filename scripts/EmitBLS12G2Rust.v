(** Driver for scripts/emit_bls12_g2_rust.sh: prints
    [BLS12_G2ArenaRust.bls12_g2_rs] (the Rust text) to bls12_g2.out in
    the current directory.  Not part of the dune build (it writes a
    file); see the script. *)
Require Import Stdlib.Strings.String.
Require Import Bedrock.BLS12_G2ArenaRust.
Open Scope string_scope.
Set Printing Depth 1000000.
Set Printing Width 1000000.
Redirect "bls12_g2" Eval vm_compute in bls12_g2_rs.
