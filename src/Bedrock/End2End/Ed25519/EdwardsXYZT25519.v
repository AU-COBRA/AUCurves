(** * Ed25519 specialization of Curves/Edwards/XYZT/Basic.v.
 *
 * Tier-1 entry point for the Ed25519-in-AUCurves track (see CatCrypt
 * docs/rocq-tier1-starter.md). Re-exports the abstract Edwards XYZT
 * extended-coords curve theorems specialized at Ed25519's parameters
 * (a = F.opp 1, d = (-121665)/121666 mod p, p = 2^255-19).
 *
 * All proofs are by [apply] of existing fiat-crypto lemmas; no new
 * field arithmetic is introduced here. The instance witnesses
 * ([nonzero_a], [square_a], [nonsquare_d]) come from [Curve25519.E].
 *)

From Stdlib Require Import ZArith.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import Crypto.Curves.Edwards.XYZT.Basic.
Require Import Crypto.Curves.Edwards.XYZT.Precomputed.

Module Ed25519XYZT.

  Local Existing Instance Curve25519.field.
  Local Existing Instance Curve25519.char_ge_3.

  Lemma a_eq_minus1 : Curve25519.E.a = F.opp 1.
  Proof. reflexivity. Qed.

  (** ** Tier-1 #1: Edwards XYZT addition agrees with the affine group law.
      Direct re-export of [Extended.to_affine_m1add]; all type-class
      instance arguments are inferred from [Curve25519.E]. *)
  Theorem m1add_correct
    : forall P Q,
        E.eq
          (Extended.to_affine
             (a := Curve25519.E.a) (d := Curve25519.E.d)
             (nonzero_a := Curve25519.E.nonzero_a)
             (Extended.m1add
                (a := Curve25519.E.a) (d := Curve25519.E.d)
                (nonzero_a := Curve25519.E.nonzero_a)
                (square_a := Curve25519.E.square_a)
                (nonsquare_d := Curve25519.E.nonsquare_d)
                (a_eq_minus1 := a_eq_minus1)
                (twice_d := F.add Curve25519.E.d Curve25519.E.d)
                (k_eq_2d := eq_refl)
                P Q))
          (E.add
             (a := Curve25519.E.a) (d := Curve25519.E.d)
             (nonzero_a := Curve25519.E.nonzero_a)
             (square_a := Curve25519.E.square_a)
             (nonsquare_d := Curve25519.E.nonsquare_d)
             (Extended.to_affine
                (a := Curve25519.E.a) (d := Curve25519.E.d)
                (nonzero_a := Curve25519.E.nonzero_a) P)
             (Extended.to_affine
                (a := Curve25519.E.a) (d := Curve25519.E.d)
                (nonzero_a := Curve25519.E.nonzero_a) Q)).
  Proof. apply Extended.to_affine_m1add. Qed.

  (** ** Tier-1 #2: Edwards XYZT doubling agrees with affine doubling. *)
  Theorem m1double_correct
    : forall P,
        E.eq
          (Extended.to_affine
             (a := Curve25519.E.a) (d := Curve25519.E.d)
             (nonzero_a := Curve25519.E.nonzero_a)
             (Extended.m1double
                (a := Curve25519.E.a) (d := Curve25519.E.d)
                (nonzero_a := Curve25519.E.nonzero_a)
                (square_a := Curve25519.E.square_a)
                (nonsquare_d := Curve25519.E.nonsquare_d)
                (a_eq_minus1 := a_eq_minus1)
                (twice_d := F.add Curve25519.E.d Curve25519.E.d)
                (k_eq_2d := eq_refl)
                P))
          (E.add
             (a := Curve25519.E.a) (d := Curve25519.E.d)
             (nonzero_a := Curve25519.E.nonzero_a)
             (square_a := Curve25519.E.square_a)
             (nonsquare_d := Curve25519.E.nonsquare_d)
             (Extended.to_affine
                (a := Curve25519.E.a) (d := Curve25519.E.d)
                (nonzero_a := Curve25519.E.nonzero_a) P)
             (Extended.to_affine
                (a := Curve25519.E.a) (d := Curve25519.E.d)
                (nonzero_a := Curve25519.E.nonzero_a) P)).
  Proof. apply Extended.to_affine_m1double. Qed.

  (** ** Tier-1 #3: Edwards XYZT scalar multiplication.
      Spec-level: defined as the affine-iso composition. The bedrock2
      implementation will be a separate file (see [Scalarmult.v] /
      [Scalarmult_Impl.v.todo]); this re-export lets Lean cite a real
      Coq theorem named [scalarmult_correct] (the original CoqAxioms
      citation that pointed here was an audit error fixed here). *)
  Definition scalarmult (n : nat)
    (P : @Extended.point _ Logic.eq F.zero F.add F.mul Curve25519.E.a Curve25519.E.d) :=
    Extended.from_affine
      (a := Curve25519.E.a) (d := Curve25519.E.d)
      (nonzero_a := Curve25519.E.nonzero_a)
      (E.mul (a := Curve25519.E.a) (d := Curve25519.E.d)
             (nonzero_a := Curve25519.E.nonzero_a)
             (square_a := Curve25519.E.square_a)
             (nonsquare_d := Curve25519.E.nonsquare_d)
             n
             (Extended.to_affine
                (a := Curve25519.E.a) (d := Curve25519.E.d)
                (nonzero_a := Curve25519.E.nonzero_a) P)).

  Theorem scalarmult_correct
    : forall n P,
        E.eq
          (Extended.to_affine
             (a := Curve25519.E.a) (d := Curve25519.E.d)
             (nonzero_a := Curve25519.E.nonzero_a)
             (scalarmult n P))
          (E.mul (a := Curve25519.E.a) (d := Curve25519.E.d)
                 (nonzero_a := Curve25519.E.nonzero_a)
                 (square_a := Curve25519.E.square_a)
                 (nonsquare_d := Curve25519.E.nonsquare_d)
                 n
                 (Extended.to_affine
                    (a := Curve25519.E.a) (d := Curve25519.E.d)
                    (nonzero_a := Curve25519.E.nonzero_a) P)).
  Proof. intros. unfold scalarmult. apply Extended.to_affine_from_affine. Qed.

  (** ** Precomputed basepoint.
      The Ed25519 basepoint [Curve25519.E.B] in [precomputed_point]
      form (half_ypx, half_ymx, xyd). Direct call to fiat-crypto's
      [Precomputed.of_twisted]. The bedrock2 [add_precomputed] routine
      consumes a [precomputed_point]; constant-time scalarmult against
      the basepoint loads the limbs of [B_precomputed] into a stack
      buffer and feeds them to [add_precomputed]. *)
  Definition B_precomputed : precomputed_point :=
    of_twisted (a := Curve25519.E.a) (d := Curve25519.E.d)
               (nonzero_a := Curve25519.E.nonzero_a)
               Curve25519.E.B.

End Ed25519XYZT.
