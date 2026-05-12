(** * ExtractXyztCopyJasmin: PoC extraction of xyzt_copy_body to jasmin_cmd
 *
 *  Demonstrates Option C of [docs/jasmin-extraction-plan.md]: pipe a
 *  [rust_cmd_ed] body through the verified composition
 *  [rust_cmd_ed_to_jasmin = tr_cmd ∘ to_bedrock_cmd] and inspect the
 *  resulting [jasmin_cmd] AST.
 *
 *  Target body: [xyzt_copy_body] (simplest leaf — single REdCall).
 *  Expected output shape: a single [JCcall "fe25519_xyzt_copy" [...]].
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.End2End.Ed25519.XyztCopyBody.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Concrete instantiation                                        *)
(* ================================================================ *)

(** Apply the [function_body_ed] HOF to dummy [located_ed] arguments
    to materialise a concrete [rust_cmd_ed]. *)
Definition xyzt_copy_concrete : rust_cmd_ed :=
  xyzt_copy_body
    {| loc_var := "dest"; loc_type := TBytes 200 |}
    [{| loc_var := "src"; loc_type := TBytes 200 |}].

(* ================================================================ *)
(* §2. Composition target                                            *)
(* ================================================================ *)

Definition xyzt_copy_jasmin_cmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin xyzt_copy_concrete.

(* ================================================================ *)
(* §3. Reduction check                                               *)
(* ================================================================ *)

(** Closed-form witness: extracting [xyzt_copy_body] through the
    composition yields exactly one [JCcall] node naming the leaf and
    listing dest then src. *)
Example xyzt_copy_jasmin_cmd_value :
  xyzt_copy_jasmin_cmd
    = JCcall "fe25519_xyzt_copy"
        [JEvar "dest"; JEvar "src"].
Proof. reflexivity. Qed.

(** Force vm_compute for visual inspection (does not write to disk
    by default — wrap in a Redirect in a separate, optional driver). *)
Definition xyzt_copy_jasmin_cmd_normalised : jasmin_cmd :=
  Eval vm_compute in xyzt_copy_jasmin_cmd.

(* ================================================================ *)
(* §4. Stretch: pretty-print to (deprecated, unverified) .jazz text  *)
(* ================================================================ *)

(** Use the [pp_cmd] pretty-printer to produce a [.jazz]-like text
    rendering of the body.  This is intended for visual inspection of
    the PoC, not for verified extraction — the pretty-printer is
    flagged DEPRECATED in [Jasmin/Core.v] in favour of the verified
    AST-based path through [JasminBridgeReal.to_jasmin_cmd].  We use
    it here only to confirm the composition produces a recognisable
    Jasmin-like call site. *)
Definition xyzt_copy_jazz_text : String.string :=
  pp_cmd "  " xyzt_copy_jasmin_cmd_normalised.

Definition xyzt_copy_jazz_text_normalised : String.string :=
  Eval vm_compute in xyzt_copy_jazz_text.

(** Dump the vm-computed AST and the (deprecated, unverified) Jazz
    pretty-print to side-car files; useful for visual inspection. *)
Redirect "xyzt_copy_jasmin" Print xyzt_copy_jasmin_cmd_normalised.
Redirect "xyzt_copy_jazz"   Print xyzt_copy_jazz_text_normalised.
