(** * Heavy imports + 64-bit instances for EdwardsXYZT64.v.
 *
 * Extracted to a separate file so [EdwardsXYZT64.v] (the content file
 * that we iterate on) loads quickly via MCP — PET caches this loader's
 * .vo across sessions. Without the split, MCP's 600s file-load
 * timeout fires on the heavy fiat-crypto + bedrock2 + EdwardsXYZT
 * import chain.
 *
 * This file should be stable; iteration happens in EdwardsXYZT64.v. *)

From Stdlib Require Export String List ZArith Lia.
Require Export coqutil.Map.OfListWord.
Require Export coqutil.Map.Interface.
Require Export Crypto.Spec.ModularArithmetic.
Require Export Crypto.Spec.Curve25519.
Require Export Crypto.Spec.CompleteEdwardsCurve.
From coqutil.Tactics Require Export Tactics.
Require Export Crypto.Util.Tactics.DestructHead.

(* bedrock2 stack. *)
Require Export bedrock2.Array.
Require Export bedrock2.bottom_up_simpl.
Require Export bedrock2.Map.Separation.
Require Export bedrock2.Map.SeparationLogic.
Require Export bedrock2.ProgramLogic.
Require Export bedrock2.SepAutoArray.
Require Export bedrock2.Scalars.
Require Export bedrock2.Semantics.
Require Export bedrock2.Syntax.
Require Export bedrock2.WeakestPrecondition.
Require Export bedrock2.WeakestPreconditionProperties.
Require Export bedrock2.NotationsCustomEntry.
Require Export bedrock2.ZnWords.
Require Export bedrock2.Loops.

(* 64-bit word + memory instances. *)
Require Export coqutil.Word.Interface.
Require Export coqutil.Word.Naive.
Require Export bedrock2.BasicC64Semantics.
Require Export coqutil.Word.Bitwidth64.
Require Export coqutil.Byte.

(* Curves + Edwards XYZT abstract algebra. *)
Require Export Crypto.Curves.Edwards.XYZT.Basic.
Require Export Crypto.Curves.Edwards.XYZT.Precomputed.
Require Export Crypto.Curves.Edwards.XYZT.Readdition.
Require Export Crypto.Bedrock.Specs.Field.

(* 64-bit Field25519 representation (heaviest single import). *)
Require Export Bedrock.End2End.X25519_64.Field25519_64.

(* Upstream bedrock2 Edwards XYZT atoms (3.8MB .vo).
   Use Require (not Export) so its Local instances don't conflict
   with our 64-bit ones; we still get qualified access via
   `Crypto.Bedrock.End2End.X25519.EdwardsXYZT.<name>`. *)
Require Crypto.Bedrock.End2End.X25519.EdwardsXYZT.

(* 64-bit instances re-exported. *)
#[export] Existing Instances
  BasicC64Semantics.word
  BasicC64Semantics.wordok
  Bitwidth64.BW64
  BasicC64Semantics.mem
  BasicC64Semantics.mapok.

#[export] Existing Instance field_parameters.
#[export] Existing Instance frep25519.
#[export] Existing Instance frep25519_ok.

(* Coercions/notations from bedrock2.WeakestPrecondition. *)
Export WeakestPrecondition.

(* Re-export the abstract Curve25519 field instances so downstream
   doesn't have to import Curve25519 + Crypto.Spec.* directly. *)
#[export] Existing Instance Curve25519.field.
#[export] Existing Instance Curve25519.char_ge_3.
