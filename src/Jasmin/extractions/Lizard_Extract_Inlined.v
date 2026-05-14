(** * OCaml extraction of Lizard extract as a single [jasmin_func].
 *
 *  Inverse-direction sibling of [Lizard_Inject_Inlined.v]: pipes
 *  [lizard_extract_rs] (End2End/Lizard/Extract_RustCmd.v) through the
 *  same chain.  Decode side of Lizard: 32B Ristretto → 16B plaintext.
 *
 *  Same structural simplicity as inject:
 *    - 2 stack-allocated buffers (xyzt_ex:200B, buf32_ex:32B)
 *    - 3 FFI calls (ristretto_decode_or_fail, edwards_to_elligator2,
 *                   lizard_unpack)
 *)

From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
From Stdlib Require Import ZArith String List.
Import ListNotations.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.InlineCallFn.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.End2End.Lizard.Extract_RustCmd.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition lizard_extract_ftab : function_table_ed := nil.

Definition lizard_extract_inlined_rs : rust_cmd_ed :=
  inline_callfn_n 4 lizard_extract_ftab lizard_extract_rs.

Definition lizard_extract_inlined_jcmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin lizard_extract_inlined_rs.

(** Params:
      [rist] : 32B Ristretto input
      [pt_out] : 16B plaintext output *)
Definition lizard_extract_inlined_func : jasmin_func :=
  polish_func_hoist {|
    jf_name := "lizard_extract";
    jf_params := [("rist", JTptr 4); ("pt_out", JTptr 2)];
    jf_locals := nil;
    jf_body := lizard_extract_inlined_jcmd;
  |}.

Definition lizard_extract_all_jasmin : list jasmin_func :=
  Eval vm_compute in [lizard_extract_inlined_func].

Definition lizard_extract_field_size : Z := 5.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "lizard_extract_jasmin_extracted"
  lizard_extract_all_jasmin lizard_extract_field_size
  pp_func pp_module.
