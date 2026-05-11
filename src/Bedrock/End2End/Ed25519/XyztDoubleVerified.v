(** * XyztDoubleVerified — Gallina point doubling for the
 *                         200-byte projective xyzt encoding.
 *
 * Used by [ScalarmultVerified.v] for the double-and-add loop.  This is
 * NOT an axiom (no upstream Parameter declared it) — purely a helper.
 *
 * Implementation: delegate to [ed25519_xyzt_add_gallina P P].  Edwards
 * curves have unified group laws (no exceptional case for doubling),
 * so this is mathematically correct.  An optimized implementation
 * would use the cheaper dedicated doubling formulas (Hisil et al. §3.3,
 * ~7 multiplications instead of ~10), but we don't need that here:
 * the spec is treated abstractly downstream.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Local Open Scope Z_scope.

Definition ed25519_xyzt_double_gallina (p : list Byte.byte) : list Byte.byte :=
  ed25519_xyzt_add_spec p p.

Lemma ed25519_xyzt_double_gallina_length :
  forall p, length (ed25519_xyzt_double_gallina p) = 200%nat.
Proof. intros p. cbv [ed25519_xyzt_double_gallina]. apply ed25519_xyzt_add_spec_len. Qed.
