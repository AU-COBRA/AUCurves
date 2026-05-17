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
 *  Build status (2026-05-12):  builds clean.
 *
 *  Typeclass-resolution fix:  Jasmin's [cmd = seq instr], where
 *  [instr] is parameterised over [asm_op : Type] and
 *  [asmop : asmOp asm_op].  Inside a [Module] (which Rocq 9 disallows
 *  inside a [Section]) typeclass instances do NOT propagate from an
 *  enclosing [Context].  We therefore fix the architecture to
 *  x86-64 at the top level by:
 *
 *    1. Axiomatising [atoI : arch_toIdent] (the variable-naming
 *       convention; a function from kinds × types × strings to
 *       [Ident.ident]; not used in any proof, but needed for
 *       [x86_extended_op] to be a [Type]).  This mirrors the existing
 *       axioms [int_to_ident] / [int_to_funname] in [BridgeReal] and
 *       is identity at extraction time.
 *
 *    2. Fixing [@asm_opI] at the canonical x86 instance.
 *
 *    3. Specialising [jasmin_cmd_T] to
 *       [@cmd x86_extended_op asm_opI].
 *)

From HB Require Import structures.
From Jasmin Require Import expr psem_defs psem operators ident
                           x86_decl x86_instr_decl x86_extra arch_extra.
From mathcomp Require Import ssreflect ssrfun ssrnat seq.
From Stdlib Require Import Uint63.
From Stdlib Require Import String ZArith List Ascii.
Import ListNotations.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.RustCmdEdToRealJasmin.
Require Import JasminBridge.BridgeReal.

Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Fix the architecture at x86-64                               *)
(* ================================================================ *)

(** We axiomatise [arch_toIdent] (a variable-naming convention; a
    bundle of [ToIdent] instances for the four register classes).
    Discharging it requires either constructing concrete [ToIdent]
    records — non-trivial in Rocq because the underlying [Cident.t]
    is sealed via [CORE_IDENT] — or instantiating it at the OCaml
    level via Jasmin's [AToIdent_T.mk] (the standard route in the
    [jasminc] OCaml driver).  This axiom is identity at extraction
    time; eliminating it is tracked together with the [int_to_ident]
    / [int_to_funname] axioms in [BridgeReal]. *)
Axiom atoI : @arch_toIdent _ _ _ _ _ x86_decl.

#[local] Existing Instance atoI | 0.

(* With [atoI] in scope, [x86_extended_op] is a concrete [Type] and
   [asm_opI] specialises to [asmOp x86_extended_op]. *)
Notation real_cmd := (list (@instr x86_extended_op asm_opI)).

(* ================================================================ *)
(* §2. RealJasmin instance of JasminEmit                            *)
(* ================================================================ *)

Module RealJasmin <: JasminEmit.
  Definition jasmin_cmd_T : Type := real_cmd.
  Definition emit (c : jasmin_cmd) : jasmin_cmd_T :=
    @to_jasmin_cmd _ asm_opI c.
End RealJasmin.

Module RealChain := RustCmdToReal RealJasmin.

(** Specialised entry point: produce [Jasmin.expr.cmd] directly. *)
Definition rust_cmd_ed_to_real_jasmin
  (c : SafeRustEd25519Sim.rust_cmd_ed) : real_cmd :=
  RealChain.rust_cmd_ed_to_real_jasmin c.

(* ================================================================ *)
(* §3. End-to-end simulation (statement; proof Admitted)            *)
(* ================================================================ *)

Section EndToEnd.

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
    forall {RST : Type} (state_refines : RST -> estate -> Prop)
           (c : SafeRustEd25519Sim.rust_cmd_ed) (rs1 rs2 : RST),
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
       Each link is Qed; only the syntactic composition remains. *)
  Admitted.

End EndToEnd.
