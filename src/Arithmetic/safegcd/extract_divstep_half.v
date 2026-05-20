(** Extract processDivstep_half + state0_half to OCaml for fast δ₀=1/2 cert
    generation.  Mirror of [extract_divstep.v] for the δ₀=1 framework. *)

Require Import ZArith.
Require Import QArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlString.

Extraction "divstep_extracted_half"
  processDivstep_half state0_half ZMap.is_empty.
