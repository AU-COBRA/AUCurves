(** Driver for scripts/emit_bls12_leaves_live.sh: prints
    [pp_module_live_b bls12_leaf_ct_budget ExtractBLS12LeavesLive.bls12_leaves_jasmin_ct]
    (the branch-free live-hint Fp leaves: [polish_func_adc], then
    [CtSelect.ct_func], hints at [bls12_leaf_ct_budget]) to bls12_leaves_live.out in the current
    directory.  Not part of the dune build (it writes a file); see the script. *)
Require Import Stdlib.Strings.String.
Require Import Bedrock.Jasmin.SpillLiveness.
Require Import Bedrock.Jasmin.ExtractBLS12LeavesLive.
Open Scope string_scope.
Set Printing Depth 1000000.
Set Printing Width 1000000.
Redirect "bls12_leaves_live" Eval vm_compute in pp_module_live_b bls12_leaf_ct_budget bls12_leaves_jasmin_ct.
