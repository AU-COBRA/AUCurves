(** Driver for scripts/emit_bls12_group_jasmin.sh: prints
    [ExtractBLS12GroupJasmin.bls12_group_jazz_regptr] (the Jasmin text) to
    bls12_group_regptr.out in the current directory.  Not part of the dune
    build (it writes a file); see the script. *)
Require Import Stdlib.Strings.String.
Require Import Bedrock.ExtractBLS12GroupJasmin.
Open Scope string_scope.
Set Printing Depth 1000000.
Set Printing Width 1000000.
Redirect "bls12_group_regptr" Eval vm_compute in bls12_group_jazz_regptr.
