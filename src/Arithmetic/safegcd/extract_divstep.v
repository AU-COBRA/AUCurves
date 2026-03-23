(** Extract processDivstep to OCaml for fast checkpoint generation.

    The extracted OCaml code can compute intermediate states natively
    (seconds instead of hours), which are then serialized back as Coq
    terms and verified by native_compute in Coq.

    Usage:
      coqc -R . '' extract_divstep.v
      # Produces divstep_extracted.ml and divstep_extracted.mli
      # Then compile and run:
      ocamlfind ocamlopt -package zarith -linkpkg \
        divstep_extracted.ml checkpoint_driver.ml -o gen_checkpoints
      ./gen_checkpoints > checkpoints.v
*)

Require Import ZArith.
Require Import QArith.
Require Import divsteps_base.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlString.

(** Extract the key functions *)
Extraction "divstep_extracted" processDivstep state0 ZMap.is_empty.
