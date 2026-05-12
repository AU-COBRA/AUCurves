(** * ExtractXyztCopyRealJasmin: extract xyzt_copy through the
 *    `rust_cmd_ed_to_real_jasmin` composition.
 *
 *  Option C ladder step (d) — companion to
 *  [ExtractXyztCopyJasmin.v] but routed through
 *  [RustCmdEdToRealJasmin.RustCmdToReal] so the same body is ready
 *  to be re-extracted to the real [Jasmin.expr.cmd] AST as soon as
 *  the [JasminBridge] dune theory builds (currently blocked on a
 *  Jasmin/Rocq .vo version mismatch — see
 *  `docs/jasmin-extraction-progress.md`).
 *
 *  Today (with the [LocalJasmin] instance), the output is bit-identical
 *  to [ExtractXyztCopyJasmin.xyzt_copy_jasmin_cmd] — this is checked
 *  by [xyzt_copy_real_jasmin_equiv_local].  When the [RealJasmin]
 *  instance is wired in (`src/Jasmin/RealJasminInstance.v`), the same
 *  source compiles against [Jasmin.expr.cmd] and emits a real Jasmin
 *  AST — no edits needed to this file.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.RustCmdEdToRealJasmin.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.End2End.Ed25519.XyztCopyBody.
Require Import Bedrock.ExtractXyztCopyJasmin.   (* sanity-check anchor *)
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Concrete instantiation                                        *)
(* ================================================================ *)

Definition xyzt_copy_real_concrete : rust_cmd_ed :=
  xyzt_copy_body
    {| loc_var := "dest"; loc_type := TBytes 200 |}
    [{| loc_var := "src"; loc_type := TBytes 200 |}].

(* ================================================================ *)
(* §2. Composition target                                            *)
(* ================================================================ *)

(** Today this is `LocalJasmin.jasmin_cmd_T = jasmin_cmd`.
    Once [src/Jasmin/RealJasminInstance.v] lands, the same body is
    available with [RealJasmin.jasmin_cmd_T = Jasmin.expr.cmd] via
    [RealJasminChain.rust_cmd_ed_to_real_jasmin]. *)
Definition xyzt_copy_real_jasmin : LocalJasmin.jasmin_cmd_T :=
  LocalChain.rust_cmd_ed_to_real_jasmin xyzt_copy_real_concrete.

(* ================================================================ *)
(* §3. Reduction check                                               *)
(* ================================================================ *)

Example xyzt_copy_real_jasmin_value :
  xyzt_copy_real_jasmin
    = JCcall "fe25519_xyzt_copy"
        [JEvar "dest"; JEvar "src"].
Proof. reflexivity. Qed.

(** Cross-check: the [LocalJasmin] instance preserves
    [ExtractXyztCopyJasmin.xyzt_copy_jasmin_cmd] verbatim, so the
    [RealJasmin]-ready file is differential-test equivalent today. *)
Example xyzt_copy_real_jasmin_equiv_local :
  xyzt_copy_real_jasmin = xyzt_copy_jasmin_cmd.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §4. AST dump (sidecar file)                                       *)
(* ================================================================ *)

Definition xyzt_copy_real_jasmin_normalised : LocalJasmin.jasmin_cmd_T :=
  Eval vm_compute in xyzt_copy_real_jasmin.

Redirect "xyzt_copy_real_ast"
  Print xyzt_copy_real_jasmin_normalised.
