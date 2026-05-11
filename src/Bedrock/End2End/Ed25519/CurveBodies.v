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
Require Import Bedrock.End2End.Ed25519.ScalarmultBody.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseBody.
Require Import Bedrock.End2End.Ed25519.DecompressBody.
Require Import Bedrock.End2End.Ed25519.CalculateKeyPairBody.
Import ListNotations.
Local Open Scope string_scope.

(** Function-table entry-point names used by [REdCallFn] lookups.
    These match the strings passed in [REdCallFn fname dest args]
    inside any future verified-helper bodies. *)
Definition curve_function_table : function_table_ed :=
  [("xyzt_add",             xyzt_add_body);
   ("xyzt_double",          xyzt_double_body);
   ("scalarmult",           scalarmult_body);
   ("scalarmult_base",      scalarmult_base_body);
   ("decompress_R",         decompress_R_body);
   ("decompress_A",         decompress_A_body);
   ("calculate_key_pair_a", calculate_key_pair_a_body);
   ("calculate_key_pair_A", calculate_key_pair_A_body)].

(** Sanity check: the table has the expected 8 entries (7 distinct
    bodies — decompress contributes two). *)
Lemma curve_function_table_size :
  length curve_function_table = 8%nat.
Proof. reflexivity. Qed.

(* Print Assumptions curve_function_table. *)
