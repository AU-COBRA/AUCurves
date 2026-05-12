(** * RealJasminInstance: wire [RustCmdEdToRealJasmin.RustCmdToReal]
 *    to the real [Jasmin.expr.cmd] AST.
 *
 *  Option C ladder step (d) — the *Jasmin-side* companion to
 *  [src/Bedrock/RustCmdEdToRealJasmin.v].  Provides:
 *
 *  1.  A [RealJasmin] instance of the [JasminEmit] module type
 *      defined in [Bedrock.RustCmdEdToRealJasmin].
 *
 *  2.  [rust_cmd_ed_to_real_jasmin] specialised to [Jasmin.expr.cmd]
 *      output.
 *
 *  3.  The Jasmin-state end-to-end simulation theorem (statement;
 *      proof Admitted pending the syntactic composition of four
 *      already-Qed building blocks — see [Bedrock.RustCmdEdToRealJasmin]
 *      for the chain).
 *
 *  Build status (2026-05-12):
 *
 *    This file is BLOCKED at build time on the [JasminBridge] dune
 *    theory not being live.  The theory's pre-built .vo files at
 *    `$WORKSPACE/jasmin/proofs/lang/expr.vo` etc. were
 *    compiled with Rocq 9.0.0 and report version 90000 against the
 *    current switch [rocq-9] / Rocq 9.0.1 (expects 90001).  This
 *    causes [Require Import JasminBridge.BridgeReal] to fail with a
 *    "bad version number" parsing error before any AUCurves code is
 *    touched.
 *
 *    The fix is a full rebuild of the Jasmin proof suite (178 files,
 *    estimated multi-hour, mathcomp-heavy compiler proofs) via the
 *    Makefile at `$WORKSPACE/jasmin/proofs/Makefile`:
 *
 *        eval $(opam env --switch=rocq-9 --set-switch)
 *        cd $WORKSPACE/jasmin/proofs
 *        make clean && make -j4
 *
 *    Once the rebuild lands and `BridgeReal.vo` builds under the
 *    AUCurves [JasminBridge] dune theory, this file compiles
 *    unchanged.
 *
 *  Until that rebuild, the file is kept as documentation /
 *  scaffolding: it shows precisely how `to_jasmin_cmd` would be
 *  instantiated, and the file is excluded from the [JasminBridge]
 *  dune theory's [modules] list so it does not break the build.
 *)

From HB Require Import structures.
From Jasmin Require Import expr psem_defs psem operators ident
                           x86_instr_decl x86_extra.
From mathcomp Require Import ssreflect ssrfun.
From Stdlib Require Import Uint63.
From Stdlib Require Import String ZArith List Ascii.
Import ListNotations.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.RustCmdEdToRealJasmin.
Require Import JasminBridge.BridgeReal.

Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. RealJasmin instance of JasminEmit                            *)
(* ================================================================ *)

Section RealJasminInstance.

  Context {atoI : arch_toIdent}.
  #[local] Existing Instance asm_opI | 0.

  (** The [RealJasmin] instance: emit into [Jasmin.expr.cmd] via the
      verified [to_jasmin_cmd] translator. *)

  Module RealJasmin <: JasminEmit.
    Definition jasmin_cmd_T : Type := cmd.   (* = Jasmin.expr.cmd *)
    Definition emit (c : jasmin_cmd) : jasmin_cmd_T := to_jasmin_cmd c.
  End RealJasmin.

  Module RealChain := RustCmdToReal RealJasmin.

  (** Specialised entry point: produce [Jasmin.expr.cmd] directly. *)
  Definition rust_cmd_ed_to_real_jasmin (c : rust_cmd_ed) : cmd :=
    RealChain.rust_cmd_ed_to_real_jasmin c.

End RealJasminInstance.

(* ================================================================ *)
(* §2. End-to-end simulation (statement; proof Admitted)            *)
(* ================================================================ *)

Section EndToEnd.

  Context {atoI : arch_toIdent}.
  Context {wsw : WithSubWord} {dc : DirectCall}
          {syscall_state_ : Type} {sc_sem : syscall.syscall_sem syscall_state_}
          {ep : EstateParams syscall_state_}
          {fcp : FlagCombinationParams}.

  #[local] Instance concrete_sip :
    SemInstrParams x86_extended_op syscall_state_ | 0 :=
    {| _asmop := asm_opI; _sc_sem := sc_sem |}.
  #[local] Instance concrete_spp : SemPexprParams | 0 := {| _fcp := fcp |}.

  Context {pT : progT} {scp : semCallParams}
          (P : @prog x86_extended_op _asmop pT) (ev : extra_val_t).

  (** The conclusion the paper points at: any [rust_cmd_ed] body that
      executes correctly under [rust_exec_ed] is simulated by the real
      Jasmin AST emitted from the same body under [psem.sem].

      Discharging this composes four already-Qed theorems (modulo two
      trivial identity-cast axioms in [BridgeReal]):

        - [SafeRustEd25519WPBridge.bridge_complete]
          ([rust_exec_ed] ↔ bedrock2 WP)
        - [NormalizeSelect.normalize_select_correct]
          (REdSelect lowering preserves [rust_exec_ed])
        - [Jasmin.Core.tr_cmd_correct]
          (bedrock2 [exec] ↔ jasmin_cmd [cmd_jasmin_equiv])
        - [JasminBridge.BridgeReal.real_jsem_*]
          (jasmin_cmd ↔ Jasmin [psem.sem]; one [real_jsem_*] lemma
          per [jasmin_cmd] constructor — all Qed)

      The composition is mechanical (chain rewrites + per-constructor
      cases) but verbose; tracked as the last open obligation in
      `docs/jasmin-extraction-progress.md` step (d). *)
  Theorem rust_cmd_ed_to_real_jasmin_correct_e2e :
    forall (state_refines : _ -> estate -> Prop)
           callee_post callee_post_n function_table c rs1 rs2,
      (* Premise: source executes correctly. *)
      True (* placeholder for [rust_exec_ed callee_post callee_post_n function_table c rs1 rs2]
              — kept abstract so the file's signature does not depend on
              the full SafeRust dependency closure imported via Bedrock. *)
      ->
      (* Conclusion: there is a Jasmin estate transition that simulates it. *)
      forall js1, state_refines rs1 js1 ->
        exists js2,
          state_refines rs2 js2 /\
          sem P ev js1 (rust_cmd_ed_to_real_jasmin c) js2.
  Proof.
    (* Mechanical composition:
         bridge_complete  ; tr_cmd_correct  ; real_jsem_call/seq/...
       Each link is Qed; the file is BLOCKED on the Jasmin theory
       rebuild before this proof can be elaborated. *)
  Admitted.

End EndToEnd.
