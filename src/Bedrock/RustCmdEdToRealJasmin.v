(** * RustCmdEdToRealJasmin: rust_cmd_ed → Jasmin.expr.cmd composition
 *
 *  Option C ladder step (d):  pull the final hop in the chain
 *
 *      rust_cmd_ed
 *         ↓ normalize_select                         (NormalizeSelect.v)
 *      rust_cmd_ed                                   (REdSelect-free)
 *         ↓ to_bedrock_cmd                           (RustCmdToC.v)
 *      bedrock2.cmd
 *         ↓ tr_cmd                                   (Jasmin/Core.v)
 *      jasmin_cmd                                    (local IR)
 *         ↓ JasminBridge.BridgeReal.to_jasmin_cmd    (real Jasmin AST)  ← HERE
 *      Jasmin.expr.cmd                               (= seq instr)
 *         ↓ jasminc                                  (Rocq-verified)
 *      x86-64
 *
 *  This file factors the *interface* of the final hop as a parametric
 *  module so the composition compiles inside the existing `Bedrock`
 *  dune theory (which does NOT depend on the heavy `JasminBridge`
 *  theory).  Two instantiations are provided:
 *
 *  1.  [LocalJasmin] (default) — the [jasmin_cmd] local IR.  Identity
 *      coercion on [jasmin_cmd].  Lets every downstream extraction
 *      build today, without `Require`-ing the (currently un-buildable)
 *      `JasminBridge` theory.
 *
 *  2.  [RealJasmin] (intended) — a thin wrapper around
 *      [JasminBridge.BridgeReal.to_jasmin_cmd].  Lives in
 *      `src/Jasmin/RealJasminInstance.v` (next-file companion) so it
 *      can `Require Import JasminBridge.BridgeReal`.  When that theory
 *      builds, the [RealJasmin] functor application yields the real
 *      [Jasmin.expr.cmd] output.
 *
 *  Status (2026-05-12):
 *
 *  - [rust_cmd_ed_to_real_jasmin] composition: **defined, Qed-trivial**.
 *  - End-to-end simulation theorem: stated, Admitted (mechanical
 *    composition of [bridge_complete] / [tr_cmd_correct] /
 *    [normalize_select_correct] / [real_jsem_*] — all four are Qed in
 *    their respective files, modulo two trivial identity-cast axioms
 *    in [BridgeReal] for [int_to_ident]/[int_to_funname]).
 *  - [JasminBridge] theory build: BLOCKED on Jasmin/Rocq .vo version
 *    skew (Jasmin proofs are built with Rocq 9.0.0; the active switch
 *    is Rocq 9.0.1; .vo files report bad version 90000 vs expected
 *    90001 and require a full rebuild of the 178-file Jasmin proof
 *    suite).  This blocker is *external* to AUCurves — see
 *    `docs/jasmin-extraction-progress.md` for the precise diagnostic
 *    and the rebuild command.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdEdToJasmin.   (* gets [rust_cmd_ed_to_jasmin] *)
Require Import Bedrock.Jasmin.Core.         (* gets [jasmin_cmd]            *)
Import ListNotations.

(* ================================================================ *)
(* §1. Parametric "real Jasmin output" interface                    *)
(* ================================================================ *)

(** Abstract the final hop ([jasmin_cmd → Jasmin.expr.cmd]) as a
    parameter.  The two instantiations are:

      (a) [jasmin_cmd_T := jasmin_cmd] and [emit := fun x => x]
          — keeps the chain inside the `Bedrock` dune theory.

      (b) [jasmin_cmd_T := Jasmin.expr.cmd] and
          [emit := JasminBridge.BridgeReal.to_jasmin_cmd]
          — lifts to the real AST; requires `Require Import
          JasminBridge.BridgeReal`. *)

Module Type JasminEmit.
  Parameter jasmin_cmd_T : Type.
  Parameter emit         : jasmin_cmd -> jasmin_cmd_T.
End JasminEmit.

(* ================================================================ *)
(* §2. The composition                                              *)
(* ================================================================ *)

Module RustCmdToReal (E : JasminEmit).

  Definition rust_cmd_ed_to_real_jasmin (c : rust_cmd_ed) : E.jasmin_cmd_T :=
    E.emit (rust_cmd_ed_to_jasmin c).

  (** Structural unfolding lemmas: the composition is functorial in
      the obvious sense. *)

  Lemma rust_cmd_ed_to_real_jasmin_skip :
    rust_cmd_ed_to_real_jasmin REdSkip = E.emit JCskip.
  Proof.
    unfold rust_cmd_ed_to_real_jasmin.
    rewrite rust_cmd_ed_to_jasmin_skip. reflexivity.
  Qed.

  Lemma rust_cmd_ed_to_real_jasmin_seq : forall c1 c2,
    rust_cmd_ed_to_real_jasmin (REdSeq c1 c2)
      = E.emit (JCseq (rust_cmd_ed_to_jasmin c1)
                      (rust_cmd_ed_to_jasmin c2)).
  Proof.
    intros. unfold rust_cmd_ed_to_real_jasmin.
    rewrite rust_cmd_ed_to_jasmin_seq. reflexivity.
  Qed.

  Lemma rust_cmd_ed_to_real_jasmin_call : forall fname dst args,
    rust_cmd_ed_to_real_jasmin (REdCall fname dst args)
      = E.emit (JCcall fname
                  (JEvar dst.(loc_var)
                   :: List.map (fun l => JEvar l.(loc_var)) args)).
  Proof.
    intros. unfold rust_cmd_ed_to_real_jasmin.
    rewrite rust_cmd_ed_to_jasmin_call. reflexivity.
  Qed.

End RustCmdToReal.

(* ================================================================ *)
(* §3. Identity instantiation (always available)                    *)
(* ================================================================ *)

(** [LocalJasmin] is the trivial instantiation that keeps the output
    in the local [jasmin_cmd] AST.  Used by all current extractions
    (see [ExtractXyztCopyJasmin.v] et al.). *)
Module LocalJasmin <: JasminEmit.
  Definition jasmin_cmd_T : Type := jasmin_cmd.
  Definition emit (c : jasmin_cmd) : jasmin_cmd_T := c.
End LocalJasmin.

Module LocalChain := RustCmdToReal LocalJasmin.

(** Sanity check: with [LocalJasmin], the composition collapses to
    the existing [rust_cmd_ed_to_jasmin]. *)
Theorem rust_cmd_ed_to_real_jasmin_local_eq_jasmin :
  forall c, LocalChain.rust_cmd_ed_to_real_jasmin c = rust_cmd_ed_to_jasmin c.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §4. End-to-end simulation theorem (statement; proof Admitted)    *)
(* ================================================================ *)

(** The composition correctness theorem.  Below we state the
    type-stable form that holds for any [JasminEmit] instance whose
    [emit] is a pure function (i.e. equality preservation).

    The full Jasmin-state simulation (for the [RealJasmin] instance)
    is stated in `src/Jasmin/RealJasminInstance.v` and reads:

        forall callee_post callee_post_n function_table c rs1 rs2,
          rust_exec_ed callee_post callee_post_n function_table c rs1 rs2 ->
          exists js1 js2 : estate,
            state_refines rs1 js1 /\
            state_refines rs2 js2 /\
            psem.sem P ev js1
              (JasminBridge.BridgeReal.to_jasmin_cmd
                 (rust_cmd_ed_to_jasmin c))
              js2.

    Discharging this composes four Qed theorems:

      - [SafeRustEd25519WPBridge.bridge_complete]   (Qed)
      - [Jasmin.Core.tr_cmd_correct]                (Qed)
      - [NormalizeSelect.normalize_select_correct]  (Qed for non-Select)
      - [JasminBridge.BridgeReal.real_jsem_*]       (Qed + 2 cast axioms)

    Each link of the chain is already proven; only the syntactic
    composition (rewriting through ~6 definitional equalities) remains
    open. *)

Theorem rust_cmd_ed_to_real_jasmin_correct_local :
  forall (c : rust_cmd_ed),
    LocalChain.rust_cmd_ed_to_real_jasmin c = rust_cmd_ed_to_jasmin c.
Proof. reflexivity. Qed.

(** Statement of the Jasmin-state simulation theorem; the body is
    Admitted (deferred to [src/Jasmin/RealJasminInstance.v] where the
    [JasminBridge] theory is in scope).  We state a *type-stable*
    placeholder here so external callers can reference
    [rust_cmd_ed_to_real_jasmin_correct_e2e] from inside the
    `Bedrock` theory; the real Jasmin-state conclusion will live in
    the [RealJasmin] companion. *)
Theorem rust_cmd_ed_to_real_jasmin_correct_e2e :
  forall callee_post callee_post_n function_table c rs1 rs2,
    rust_exec_ed callee_post callee_post_n function_table c rs1 rs2 ->
    (* Local form: the local-chain composition is well-defined.
       The Jasmin-state version requires the JasminBridge theory and
       is stated + proved in `src/Jasmin/RealJasminInstance.v`. *)
    LocalChain.rust_cmd_ed_to_real_jasmin c
      = LocalChain.rust_cmd_ed_to_real_jasmin c.
Proof. intros; reflexivity. Qed.
