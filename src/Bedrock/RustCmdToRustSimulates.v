(** * RustCmdToRustSimulates: trust localization for [rs_func_emit].
 *
 * Rocq counterpart to Lean's
 * [CatCrypt.Crypto.Jasmin.JasminToRustEmitSimulates]: the named-axiom
 * design that isolates the "rustc + LLVM + CPU faithfully realize the
 * IR semantics" trust assumption to a single auditable statement.
 *
 * Status:
 *   - §1 [RustcExec] declared as an opaque relation (no defining eq).
 *   - §2 [RustcExec_correct] is the SOLE axiom of this file: it
 *     asserts that the emitted Rust string, when executed by
 *     rustc-compiled binary, agrees with [rust_exec_ed].
 *   - §3 [print_module_preserves_semantics] is a one-line consequence
 *     of the axiom; states the simulation in the form a downstream
 *     user actually needs.
 *   - §4 Per-constructor [rfl] lemmas document that [rs_emit] is a
 *     pure structural pattern-match (no semantic content beyond
 *     string concatenation) — the printer is audit-by-inspection.
 *
 * Compared to the previous status (an implicit [Admitted] inside
 * [rs_emit_correct] proofs scattered across consumers), the trust
 * assumption is now:
 *   - A SINGLE axiom statement (greppable as [RustcExec_correct])
 *   - With an explicit equivalence form (no hidden assumptions)
 *   - Independent of leaf instances (universally quantified over
 *     callee oracles + function tables)
 *
 * The axiom does NOT prove printer correctness — we have no formal
 * Rust source-level semantics in Rocq.  It LOCALIZES the trust gap:
 * any audit of the verification chain reduces to auditing one named
 * statement plus the (rfl-closed) reflectivity lemmas in §4.  Closing
 * the gap for real requires formalizing a Rust subset semantics
 * (RustBelt / Aeneas / MiniRust); that is independent future work.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdToC.   (* LF, join *)
Require Import Bedrock.RustCmdToRust.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1.  Opaque [RustcExec] relation                                  *)
(* ================================================================ *)

(** [RustcExec src rs1 rs2] holds when the Rust source string [src],
    after being compiled by rustc into a binary, executes from input
    state [rs1] to output state [rs2].

    No defining equation — this is intentionally a placeholder for the
    behavior of an external compiler + target CPU.  The only fact we
    will assert about it is the trust axiom in §2. *)
Parameter RustcExec :
  String.string ->     (* the emitted Rust function source *)
  rust_state_ed ->     (* input state (parameter bindings + tower slots) *)
  rust_state_ed ->     (* output state *)
  Prop.

(* ================================================================ *)
(* §2.  Trust axiom                                                  *)
(* ================================================================ *)

(** [RustcExec_correct]: the sole trust assumption of the printer
    chain.  Asserts that compiled-and-run Rust source agrees with our
    Rocq IR semantics [rust_exec_ed], for every callee oracle and
    function-table assignment.

    Why this is the right shape:
    - It quantifies over the IR's callee_post / callee_post_n oracles,
      so it holds against ANY interpretation of leaf-call semantics
      that the caller chooses (no coupling to a specific leaf set).
    - It is stated as an IFF, so it transports both directions:
      proofs upstream of [RustcExec] can conclude facts about
      [rust_exec_ed], and vice versa.

    What this does NOT claim:
    - It does NOT prove that rustc is bug-free.  It asserts a
      compatibility property — the same content as Lean's
      [RustcExec_correct] axiom, which has been the canonical leaf
      since [JasminToRustEmitSimulates.lean].
    - The axiom is unconditional on [rs_emit] producing well-formed
      Rust.  If the emitter ever produces a string that rustc rejects,
      [RustcExec] is vacuously empty and the equivalence collapses on
      both sides (rust_exec_ed for malformed IR is also empty under
      well-formedness constraints elsewhere in the chain). *)
Axiom RustcExec_correct :
  forall (callee_post :
            String.string -> list located_ed -> located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (sig : rs_func_sig) (body : rust_cmd_ed)
         (rs1 rs2 : rust_state_ed),
    RustcExec (rs_func_emit sig body) rs1 rs2
      <-> rust_exec_ed callee_post callee_post_n function_table body rs1 rs2.

(* ================================================================ *)
(* §3.  Headline lemma: print_module_preserves_semantics             *)
(* ================================================================ *)

(** The simulation theorem in the form a downstream consumer wants:
    given an IR program, the emitted Rust source executes equivalently.

    One-liner — its content IS the axiom above; this lemma exists so
    callers can [Require] the simulation result without [Require]ing
    the axiom directly, and so the proof tree shows the dependency on
    [RustcExec_correct] cleanly via [Print Assumptions]. *)
Theorem print_module_preserves_semantics
  (callee_post :
     String.string -> list located_ed -> located_ed ->
     rust_state_ed -> rust_state_ed -> Prop)
  (callee_post_n :
     String.string -> list located_ed -> list located_ed ->
     rust_state_ed -> rust_state_ed -> Prop)
  (function_table : function_table_ed)
  (sig : rs_func_sig) (body : rust_cmd_ed)
  (rs1 rs2 : rust_state_ed) :
  RustcExec (rs_func_emit sig body) rs1 rs2
    <-> rust_exec_ed callee_post callee_post_n function_table body rs1 rs2.
Proof.
  apply RustcExec_correct.
Qed.

(* ================================================================ *)
(* §4.  Per-constructor structural lemmas (printer is pure concat)   *)
(* ================================================================ *)

(** These lemmas state what [rs_emit] produces on each [rust_cmd_ed]
    constructor.  All are closed by [reflexivity] — the printer is a
    direct pattern-match that does no semantic transform.  Their
    purpose is documentation: an auditor checks the per-constructor
    output against the audit corpus (e.g., the emitted .rs files
    shipped with the crate) and verifies the printer hasn't drifted.

    These DO NOT prove semantic correctness; they prove the printer
    is the trivial syntax-directed map we audited.  The
    [RustcExec_correct] axiom carries the semantic content. *)

Lemma rs_emit_skip (indent : String.string) :
  rs_emit indent REdSkip = indent ++ "()".
Proof. reflexivity. Qed.

Lemma rs_emit_seq (indent : String.string) (c1 c2 : rust_cmd_ed) :
  rs_emit indent (REdSeq c1 c2) =
    rs_emit indent c1 ++ ";" ++ LF ++ rs_emit indent c2.
Proof. reflexivity. Qed.

Lemma rs_emit_scalar_set (indent : String.string) (v : String.string) (e : sexpr_ed) :
  rs_emit indent (REdScalarSet v e) =
    indent ++ rs_sanitize v ++ " = " ++ rs_sexpr e.
Proof. reflexivity. Qed.

Lemma rs_emit_if_nz (indent : String.string) (e : sexpr_ed) (c1 c2 : rust_cmd_ed) :
  rs_emit indent (REdIfNz e c1 c2) =
    indent ++ "if (" ++ rs_sexpr e ++ ") != 0 {" ++ LF ++
    rs_emit ("    " ++ indent) c1 ++ LF ++
    indent ++ "} else {" ++ LF ++
    rs_emit ("    " ++ indent) c2 ++ LF ++
    indent ++ "}".
Proof. reflexivity. Qed.

Lemma rs_emit_while_nz (indent : String.string) (e : sexpr_ed) (body : rust_cmd_ed) :
  rs_emit indent (REdWhileNz e body) =
    indent ++ "while (" ++ rs_sexpr e ++ ") != 0 {" ++ LF ++
    rs_emit ("    " ++ indent) body ++ LF ++
    indent ++ "}".
Proof. reflexivity. Qed.

Lemma rs_emit_block (indent : String.string) (body : rust_cmd_ed) :
  rs_emit indent (REdBlock body) =
    indent ++ "{" ++ LF ++
    rs_emit ("    " ++ indent) body ++ LF ++
    indent ++ "}".
Proof. reflexivity. Qed.

(** [rs_emit] emits a whole-array literal write as
    [loc.copy_from_slice(&[..])] rather than [loc = [..]], so that it
    works whether [loc] is a local [ [u8; N] ] or a reference parameter
    [&mut [u8; N] ]; a bare [=] type-errors on the latter.  See the
    comment on [REdSetBytes] in RustCmdToRust.v. *)
Lemma rs_emit_setbytes (indent : String.string)
                       (loc : located_ed) (bytes : list Z) :
  rs_emit indent (REdSetBytes loc bytes) =
    indent ++ rs_sanitize loc.(loc_var) ++ ".copy_from_slice(&[" ++
      join ", " (List.map (fun z => z_str z ++ "u8") bytes) ++ "])".
Proof. reflexivity. Qed.

Lemma rs_emit_arr_load (indent : String.string)
                       (dst src : located_ed) (idx_e : sexpr_ed) :
  rs_emit indent (REdArrLoad dst src idx_e) =
    indent ++ rs_sanitize dst.(loc_var) ++ " = " ++
      rs_sanitize src.(loc_var) ++ "[(" ++ rs_sexpr idx_e ++ ") as usize]".
Proof. reflexivity. Qed.

Lemma rs_emit_arr_store (indent : String.string)
                        (arr : located_ed) (idx_e : sexpr_ed)
                        (src : located_ed) :
  rs_emit indent (REdArrStore arr idx_e src) =
    indent ++ rs_sanitize arr.(loc_var) ++ "[(" ++ rs_sexpr idx_e ++
      ") as usize] = " ++ rs_sanitize src.(loc_var).
Proof. reflexivity. Qed.

(** The remaining cases ([REdLetZero], [REdLetU64], [REdCall],
    [REdByteStore], [REdByteLoad], [REdFor], [REdSelect], [REdCallN],
    [REdCallFn]) follow the same pattern: [reflexivity] discharges
    each as a direct unfolding of the [rs_emit] match.  They can be
    added on demand; the discipline is established by the §4 cases
    above.  Lean's [JasminToRustEmitSimulates.lean §1] discharges
    eleven such lemmas in the same shape. *)

(** [print_assumptions_check] — invoke [Print Assumptions
    print_module_preserves_semantics] to verify the only assumption is
    [RustcExec_correct] (and primitives from [Stdlib]).  This is the
    audit checkpoint: a single named axiom, no other admits, no
    universe issues. *)
