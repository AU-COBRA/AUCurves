(** Driver for scripts/emit_bls12_tower_jasmin.sh: prints
    [ExtractBLS12TowerJasmin.bls12_tower_jazz_regptr] (the Jasmin text) to
    bls12_tower_regptr.out in the current directory.  Not part of the dune
    build (it writes a file); see the script. *)
Require Import Stdlib.Strings.String.
Require Import Bedrock.ExtractBLS12TowerJasmin.
Open Scope string_scope.
Set Printing Depth 1000000.
Set Printing Width 1000000.
Redirect "bls12_tower_regptr" Eval vm_compute in bls12_tower_jazz_regptr.
