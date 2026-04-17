(** * X25519 Dettman multiplication: bedrock2 synthesis glue.
 *   EXPLORATORY — BLOCKED 2026-04-15.
 *
 * This file is a placeholder documenting an attempted but blocked approach
 * to closing the final 4 X25519 field operations in the bedrock2 → Jasmin
 * pipeline (fe25519_mul, fe25519_square, and their callers ladderstep,
 * montladder, x25519, x25519_base).
 *
 * ## Goal
 *
 * Wire fiat-crypto's [DettmanMultiplication.mul]/[.square] from
 * [PushButtonSynthesis/DettmanMultiplication.v] into the bedrock2
 * [computed_op] framework, producing [fe25519_mul_dettman] /
 * [fe25519_square_dettman] bedrock2 functions that could replace
 * UnsaturatedSolinas's [carry_mul]/[carry_square].
 *
 * ## Why
 *
 * Schoolbook UnsaturatedSolinas produces a 5×5 mul with ~20-36 live u64
 * partial sums at every midpoint — above jasminc's register-allocator
 * budget (~14 GPR).  Dettman's interleaved mul+reduce emits one output
 * limb at a time, shrinking the live cross-section to ~14-16.
 * Structural evidence: [fiat-crypto/fiat-bedrock2/src/secp256k1_dettman_64.c]
 * has the same n=5 structure and a tractable live profile at column
 * boundaries (x39, x76, x101, x132, x151).
 *
 * ## Blocker
 *
 * The [make_computed_op] tactic relies on [vm_compute; reflexivity] to
 * reduce the Pipeline.BoundsPipeline output to a normal-form [API.Expr].
 * For X25519-scale Dettman parameters (s=2^255, c=19, n=5, lw=51, lr=1),
 * this consumed >15 GB of RAM on a 14 GB machine and thrashed swap
 * indefinitely (killed after 5 minutes, process in state D with 16 GB
 * swap used).  [native_compute] exhibited the same memory footprint
 * because the underlying term is fundamentally huge — Pipeline's
 * interleaved partial-product reductions produce a term with very deep
 * nested lets that vm/native compute cannot share-collapse.
 *
 * The analogous UnsaturatedSolinas case [fe25519_ops] compiles in ~5
 * minutes, peaking at ~2 GB; the schoolbook shape is smaller and more
 * share-friendly than Dettman's interleaved form.
 *
 * ## Typeclass-resolution findings
 *
 * Resolved issues (before hitting the memory blocker):
 * - [DettmanMultiplication.mul] in [PushButtonSynthesis] takes
 *   machine_wordsize POSITIONALLY, not named.
 * - [machine_wordsize] has type [machine_wordsize_opt] (a class alias
 *   for [Z]); passing [64] alone triggers a nat/Z coercion error, the
 *   working form is [(64%Z : machine_wordsize_opt)].
 * - [list_binop_insizes], [list_binop_outsizes], [list_binop_inlengths]
 *   from [Signature.v] are reusable generically (not specific to
 *   UnsaturatedSolinas).
 *
 * ## Escape hatches (for a future session)
 *
 * 1. **Hand-write Dettman mulmod for X25519 directly** as a bedrock2
 *    [func!] for the n=5, lw=51 case, with an equivalence proof to
 *    [DettmanMultiplication.mulmod] via [eval_mulmod].
 *    ~300 lines code + ~150 lines proof.
 * 2. **Run the Pipeline via extracted OCaml**: fiat-crypto's
 *    [bedrock2_dettman_multiplication] CLI already produces the bedrock2
 *    AST for secp256k1.  Parameterize it for X25519, serialize the
 *    output, deserialize into Rocq.  Loses the Rocq-level Pipeline
 *    invocation but keeps the eventual [to_jasmin_cmd] verification.
 * 3. **Build on a machine with 32+ GB RAM**.  Not attempted.
 *
 * ## Correctness (if (1) or (3) are pursued)
 *
 * The field-level theorems [fe25519_mul_dettman_correct] would reduce
 * to [DettmanMultiplication.mul_correct] (already Qed in
 * [fiat-crypto/src/PushButtonSynthesis/DettmanMultiplication.v]) combined
 * with the generic [list_binop_correct] in
 * [Bedrock/Field/Synthesis/New/Signature.v].  No new soundness work is
 * required.
 *)

(** This file intentionally contains no definitions.  Re-enable when one
    of the escape hatches above is in scope. *)
From Stdlib Require Import String.
