(** * CurveBodies — aggregator for the 6 curve-leaf
 *                  [function_body_ed] forwarders.
 *
 *  Deliverable beyond per-leaf verification (Phases 3-5): exposes a
 *  single [function_table_ed] constant [curve_function_table] that
 *  the framework's [REdCallFn] dispatch can consume.  Future runtime
 *  extraction (sign / verify implemented as [REdCallFn] sites
 *  resolving against this table) reads from here.
 *
 *  All seven entries are framework-level forwarders to their
 *  corresponding "fe25519_*" external leaves.  The companion
 *  per-leaf [body_correct] theorems (in the *Body.v files) discharge
 *  the framework dispatch obligation under the assumption that the
 *  external leaves honour their [callee_post] contracts.
 *
 *  Granular field-op decomposition of each body is multi-month
 *  future work; this file is the framework hook that lets that work
 *  be slotted in piecewise without touching anything else.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.XyztAddBody.
Require Import Bedrock.End2End.Ed25519.XyztDoubleBody.
Require Import Bedrock.End2End.Ed25519.XyztAddBodyDecomposed.
Require Import Bedrock.End2End.Ed25519.XyztDoubleBodyDecomposed.
Require Import Bedrock.End2End.Ed25519.XyztCopyBody.
Require Import Bedrock.End2End.Ed25519.ScalarmultBody.
Require Import Bedrock.End2End.Ed25519.ScalarmultBodyDecomposed.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseBody.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseBodyDecomposed.
Require Import Bedrock.End2End.Ed25519.DecompressBody.
Require Import Bedrock.End2End.Ed25519.CalculateKeyPairBody.
Import ListNotations.
Local Open Scope string_scope.

(** Function-table entry-point names used by [REdCallFn] lookups.
    These match the strings passed in [REdCallFn fname dest args]
    inside any future verified-helper bodies.

    The "*_decomposed" entries (Phase A of
    [docs/scalarmult-verification-plan.md]) sit alongside the trivial
    pass-throughs.  Sites can pick either name when emitting their
    [REdCallFn] — the pass-through stays the live default while the
    decomposed variants' [body_correct] proofs are completed. *)
Definition curve_function_table : function_table_ed :=
  [("xyzt_add",              xyzt_add_body);
   ("xyzt_add_decomposed",   xyzt_add_body_decomposed);
   ("xyzt_double",           xyzt_double_body);
   ("xyzt_double_decomposed", xyzt_double_body_decomposed);
   ("xyzt_copy",             xyzt_copy_body);
   ("scalarmult",            scalarmult_body);
   ("scalarmult_decomposed", scalarmult_body_decomposed);
   ("scalarmult_base",       scalarmult_base_body);
   ("scalarmult_base_decomposed", scalarmult_base_body_decomposed);
   ("decompress_R",          decompress_R_body);
   ("decompress_A",          decompress_A_body);
   ("calculate_key_pair_a",  calculate_key_pair_a_body);
   ("calculate_key_pair_A",  calculate_key_pair_A_body)].

(** Sanity check: the table now has 13 entries (Phase A added the
    [xyzt_*_decomposed] pair, Phase B added [xyzt_copy] and
    [scalarmult_decomposed], Phase C added
    [scalarmult_base_decomposed] on top of the original 10). *)
Lemma curve_function_table_size :
  length curve_function_table = 13%nat.
Proof. reflexivity. Qed.

(* Print Assumptions curve_function_table. *)
