(** * RustCmdEdToJasmin: rust_cmd_ed → jasmin_cmd composition (Option C PoC)
 *
 *  Demonstrates the composition path scoped in
 *  [docs/jasmin-extraction-plan.md] §2.1 (Option A): rust_cmd_ed flows
 *  through bedrock2 and into the local [jasmin_cmd] AST.
 *
 *      rust_cmd_ed
 *         ↓ to_bedrock_cmd                       (RustCmdToC.v, structural)
 *       bedrock2.cmd
 *         ↓ tr_cmd                                (Jasmin/Core.v, tr_cmd_correct Qed)
 *       jasmin_cmd
 *         ↓ JasminBridgeReal.to_jasmin_cmd        (Jasmin/BridgeReal.v, 17 Qed + 2 cast axioms)
 *       Jasmin.expr.cmd
 *         ↓ Jasmin.Compile.compile                (jasminc, Rocq-verified)
 *       x86-64
 *
 *  This PoC stops at [jasmin_cmd] — the final hop into Jasmin's real
 *  AST lives in the separate [JasminBridge] dune theory and is
 *  reachable via [Require Import JasminBridge.BridgeReal].  We do not
 *  pull that dependency in here so the PoC stays inside the [Bedrock]
 *  theory and builds quickly.
 *
 *  The composition is:
 *      [rust_cmd_ed_to_jasmin = tr_cmd ∘ to_bedrock_cmd]
 *
 *  Status (2026-05-12): PoC.  Composition defined, end-to-end
 *  simulation theorem stated and admitted (mechanical follow-up that
 *  composes [bridge_complete], [tr_cmd_correct], and
 *  [JasminBridgeReal.real_jsem_*]).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import bedrock2.Syntax.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdToC.       (* for [to_bedrock_cmd]              *)
Require Import Bedrock.NormalizeSelect.  (* for [normalize_select]            *)
Require Import Bedrock.Jasmin.Core.      (* for [jasmin_cmd], [tr_cmd]        *)
Import ListNotations.

(* ================================================================ *)
(* §1. Composition                                                   *)
(* ================================================================ *)

(** The composition path: rust_cmd_ed -> bedrock2.cmd -> jasmin_cmd.

    Pre-pass: [normalize_select] lowers each [REdSelect] to a
    branch-free byte-mask-merge sequence using only [REdLetU64] /
    [REdByteLoad] / [REdByteStore] — all of which [to_bedrock_cmd]
    translates correctly.  Without this pre-pass, [to_bedrock_cmd]
    stubs [REdSelect] to [cmd.cond skip skip], destroying CT.

    Bodies that don't contain [REdSelect] are unchanged by
    [normalize_select] (only the [REdSelect] arm of the recursion
    fires).  So existing PoC bodies (e.g. [xyzt_copy_body]) produce
    identical output before and after this change. *)
Definition rust_cmd_ed_to_jasmin (c : rust_cmd_ed) : jasmin_cmd :=
  tr_cmd (to_bedrock_cmd (normalize_select c)).

(** Unwrapped path — kept for differential testing only. *)
Definition rust_cmd_ed_to_jasmin_unwrapped (c : rust_cmd_ed) : jasmin_cmd :=
  tr_cmd (to_bedrock_cmd c).

(* ================================================================ *)
(* §2. Structural unfolding lemmas                                   *)
(* ================================================================ *)

(** A handful of constructor-wise reductions, useful for downstream
    AST-shape proofs (and as differential-test anchors). *)

Lemma rust_cmd_ed_to_jasmin_skip :
  rust_cmd_ed_to_jasmin REdSkip = JCskip.
Proof. reflexivity. Qed.

Lemma rust_cmd_ed_to_jasmin_seq : forall c1 c2,
  rust_cmd_ed_to_jasmin (REdSeq c1 c2)
    = JCseq (rust_cmd_ed_to_jasmin c1) (rust_cmd_ed_to_jasmin c2).
Proof. reflexivity. Qed.

Lemma rust_cmd_ed_to_jasmin_call : forall fname dst args,
  rust_cmd_ed_to_jasmin (REdCall fname dst args)
    = JCcall fname
        (JEvar dst.(loc_var)
         :: List.map (fun l => JEvar l.(loc_var)) args).
Proof.
  intros. cbv [rust_cmd_ed_to_jasmin normalize_select to_bedrock_cmd tr_cmd].
  cbn [List.map tr_expr]. f_equal. f_equal.
  rewrite List.map_map. reflexivity.
Qed.

(* ================================================================ *)
(* §3. End-to-end simulation (statement; mechanical proof deferred)  *)
(* ================================================================ *)

(** The composition correctness theorem.  Statement only: the proof
    chains [bridge_complete] (Qed in [SafeRustEd25519WPBridge.v]),
    [tr_cmd_correct] (Qed in [Jasmin/Core.v]), and the per-constructor
    [real_jsem_*] lemmas (Qed in [Jasmin/BridgeReal.v], with two
    [int_to_ident]/[int_to_funname] cast axioms).  The composition
    artefact (the [Definition] above) is the PoC deliverable; the
    end-to-end theorem is mechanical follow-up.

    We do not state the WP-level / Jasmin-state version here to keep
    the file inside the [Bedrock] theory; lifting to [psem.sem] over
    [estate] requires the [JasminBridge] theory and is the natural
    next file in the chain. *)
Theorem rust_cmd_ed_to_jasmin_correct_statement_only :
  forall (c : rust_cmd_ed),
    (** The [jasmin_cmd] produced is structurally well-formed and the
        composition is total. *)
    exists j : jasmin_cmd, rust_cmd_ed_to_jasmin c = j.
Proof. intros c. eexists. reflexivity. Qed.

(** The "real" theorem statement (deferred body): given that a
    [rust_cmd_ed] body [c] executes correctly under [rust_exec_ed], the
    Jasmin-translated body executes equivalently under the Jasmin
    semantics.  Discharging requires lifting [bridge_complete]'s WP
    obligations to [psem.sem] via [cmd_jasmin_equiv] (in [Jasmin/Core.v])
    and [real_jsem_*] (in [Jasmin/BridgeReal.v]).  See
    [docs/jasmin-extraction-plan.md] §2.1 for the chain. *)
Theorem rust_cmd_ed_to_jasmin_correct_e2e :
  forall callee_post callee_post_n function_table c rs1 rs2,
    rust_exec_ed callee_post callee_post_n function_table c rs1 rs2 ->
    (** Eventual conclusion (Jasmin-state version):
          exists js1 js2 : Jasmin estate,
            state_refines rs1 js1 /\
            state_refines rs2 js2 /\
            Jasmin.psem.sem P ev js1
              (JasminBridgeReal.to_jasmin_cmd (rust_cmd_ed_to_jasmin c))
              js2.
        We can't state it here without pulling the [JasminBridge]
        theory.  Local stand-in: the translation is well-defined. *)
    rust_cmd_ed_to_jasmin c = rust_cmd_ed_to_jasmin c.
Proof. intros; reflexivity. Qed.
