(** * ExtractXyztDoubleDecomposedJasmin: PoC extraction of the
 *    decomposed xyzt_double body to jasmin_cmd.
 *
 *  Step (b) of the Option C ladder in
 *  [docs/jasmin-extraction-progress.md].  This is the first decomposed
 *  body in the chain: validates that [REdLetZero] + [REdSeq] + [REdCall]
 *  + [REdCallN] all translate through the bedrock2 detour into a
 *  legible [jasmin_cmd] AST.
 *
 *  The body uses:
 *    - 13 × [REdLetZero  v (TBytes 40) body]      → [cmd.stackalloc] →
 *                                                    [JCdecl x (JTstack 5) ...]
 *    - 1  × [REdCallN "fe25519_unpack_xyzt5"]     → [cmd.call dests ...] →
 *                                                    [JCcall "..." (dests ++ args)]
 *    - 7  × [REdCall  "fe25519_<op>"]             → [cmd.call [] ...] →
 *                                                    [JCcall "..." (dest :: args)]
 *    - 1  × [REdCallN "fe25519_pack_xyzt5"]
 *    - many × [REdSeq] glue                        → [cmd.seq] →
 *                                                    [JCseq]
 *
 *  Notably, [REdSelect] / [REdFor] are NOT exercised by this body —
 *  they remain blockers for the scalarmult* bodies (step (c)).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.End2End.Ed25519.XyztDoubleBodyDecomposed.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Concrete instantiation                                        *)
(* ================================================================ *)

Definition xyzt_double_decomposed_jasmin_cmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin
    (xyzt_double_body_decomposed
       {| loc_var := "out"; loc_type := TBytes 200 |}
       [{| loc_var := "P"; loc_type := TBytes 200 |}]).

(** Force vm_compute so [Print] dumps the normalised AST. *)
Definition xyzt_double_decomposed_jasmin_cmd_normalised : jasmin_cmd :=
  Eval vm_compute in xyzt_double_decomposed_jasmin_cmd.

(* ================================================================ *)
(* §2. Pretty-printed Jasmin dump                                    *)
(* ================================================================ *)

Definition xyzt_double_decomposed_jazz : string :=
  pp_cmd "  " xyzt_double_decomposed_jasmin_cmd.

Definition xyzt_double_decomposed_jazz_normalised : string :=
  Eval vm_compute in xyzt_double_decomposed_jazz.

(** Side-car dumps for visual inspection. *)
Redirect "xyzt_double_decomposed_jasmin"
  Print xyzt_double_decomposed_jasmin_cmd_normalised.
Redirect "xyzt_double_decomposed_jazz"
  Print xyzt_double_decomposed_jazz_normalised.
