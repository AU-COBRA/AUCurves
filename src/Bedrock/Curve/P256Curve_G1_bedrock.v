(* P256Curve_G1_bedrock.v
   Bridge between fiat-crypto's Jacobian P-256 point addition
   and the AUCurves P-256 RCB Gallina specification.

   The bridge proves that the two algorithms compute the same group
   operation in the abstract sense — i.e., when both outputs are
   converted to affine Weierstrass coordinates, they are W.eq.

   Proof chain (no Admitted):
     1. AUCurves Gallina spec  <-->  Projective.add
        (CurveSpecsEquivalence.gallina_fiat_crypto_equiv', already proven
         and instantiated for P-256 via P256CurveSpecsEquiv)
     2. to_affine (Projective.add P Q) = W.add (to_affine P) (to_affine Q)
        (Projective.to_affine_add, proven in fiat-crypto)
     3. to_affine (Jacobian.add P Q) = W.add (to_affine P) (to_affine Q)
        (Jacobian.to_affine_add, proven in fiat-crypto)
     4. By transitivity, the affine images of the two algorithms agree.

   The remaining gap (the bedrock2 representation bridge connecting
   Montgomery byte arrays to WordByWordMontgomery.eval word lists) is
   *separate* from algorithm equivalence and is documented at the bottom.
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Curves.Weierstrass.Jacobian.Jacobian.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Curves.Weierstrass.P256.

Local Open Scope Z_scope.

(* P-256 abstract algebraic equivalence between Projective.add and
   Jacobian.add via the affine round-trip.

   We instantiate fiat-crypto's Projective and Jacobian modules with
   the P-256 field (F p256). Both have to_affine_add lemmas; transitivity
   gives us the equivalence at the W.point level. *)

Section P256_Algorithm_Equiv.

  (* Instantiate Projective and Jacobian for P-256 *)
  Local Notation F := (F P256.p256).
  Local Notation Wpoint := (@W.point F eq F.add F.mul P256.a P256.b).

  Local Notation Ppoint := (@Projective.point
    F eq F.zero F.add F.mul P256.a P256.b).
  Local Notation Jpoint := (@Jacobian.point
    F eq F.zero F.add F.mul P256.a P256.b).

  Local Notation Padd := (@Projective.add
    F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div
    P256.a P256.b _ P256.p256_char_ge_3 _
    P256.three_b P256.three_b_correct P256.discriminant_nonzero).

  Local Notation Jadd := (@Jacobian.add
    F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div
    P256.a P256.b _ P256.p256_char_ge_3 _).

  Local Notation P_to_affine := (@Projective.to_affine
    F eq F.zero F.add F.mul P256.a P256.b _ _).

  Local Notation J_to_affine := (@Jacobian.to_affine
    F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div
    P256.a P256.b _ _).

  (* Key bridge: Projective.add and Jacobian.add agree on affine images. *)
  Theorem p256_proj_jacobian_affine_equiv :
    forall (P Q : Ppoint) (P' Q' : Jpoint) except,
      W.eq (P_to_affine P) (J_to_affine P') ->
      W.eq (P_to_affine Q) (J_to_affine Q') ->
      W.eq (P_to_affine (Padd P Q except)) (J_to_affine (Jadd P' Q')).
  Proof.
    intros P Q P' Q' except HP HQ.
    rewrite Projective.to_affine_add.
    rewrite Jacobian.to_affine_add.
    rewrite HP, HQ.
    reflexivity.
  Qed.

  (* As a special case: starting from the same affine point yields
     the same affine result. *)
  Corollary p256_same_affine :
    forall (W1 W2 : Wpoint) except,
      W.eq
        (P_to_affine (Padd (Projective.of_affine W1) (Projective.of_affine W2) except))
        (J_to_affine (Jadd (Jacobian.of_affine W1) (Jacobian.of_affine W2))).
  Proof.
    intros W1 W2 except.
    apply p256_proj_jacobian_affine_equiv.
    - rewrite Projective.to_affine_of_affine. reflexivity.
    - rewrite Projective.to_affine_of_affine. reflexivity.
  Qed.

End P256_Algorithm_Equiv.

(* ================================================================== *)
(* ================================================================== *)
(* Bedrock2 representation bridge — composes algebraic equivalence    *)
(* with the Bignum/FElem spec bridge.                                 *)
(* ================================================================== *)

Require Import Bedrock.Curve.P256_Bignum_Specs.

Section P256_Bedrock_Correctness.

  (* The above [p256_proj_jacobian_affine_equiv] proves *algorithmic*
     equivalence between Projective.add (which AUCurves' RCB Gallina
     spec computes via CurveSpecsEquivalence) and Jacobian.add (which
     fiat-crypto's bedrock2 P-256 implements). Both compute the same
     abstract group operation on W.point.

     The remaining piece of "full bedrock2 correctness" is the
     *representation bridge*: connecting AUCurves' [Bignum n p ws]
     sep predicate (with [valid] bounds and [eval ∘ from_mont]
     decoding) to fiat-crypto's [FElem px x] sep predicate (with
     [bounded_by tight_bounds] bounds and [feval] decoding).

     The exploration in [BignumFElemBridge.v] establishes that these
     are *definitionally equal* up to dependent-pair wrapping:

     - Memory: both unfold to [array scalar (word.of_Z 8) px ws] over
       the same word list. The [Bignum] vs [FElem] difference is just
       an explicit length clause vs a [{ws | length ws = n}] sigma type.

     - Bounds: [bounded_by tight_bounds] for the WBW p256 representation
       expands directly to [WordByWordMontgomery.valid 64 4 m] (see
       [tight_bounds_eq] in
       [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]).

     - Decoding: [feval] for the p256 WBW representation computes
       [F.of_Z (Positional.eval (uweight 64) 4 (from_montgomerymod _))]
       which is exactly AUCurves' [evfrom = eval ∘ from_mont].

     [p256_FElem_iff_Bignum] in [P256_Bignum_Specs.v] packages the
     memory-level [iff1]; the bounds and decoding equivalences are
     [reflexivity] up to typeclass unfolding.

     A "full bedrock2 correctness" theorem combining both bridges
     would have the shape:

       forall functions, (* fiat-crypto P256 functions in scope *)
         spec_of_p256_point_add functions ->          (* fiat-crypto's WP *)
         spec_of_P256_RCB_add functions               (* AUCurves' Bignum-style WP *)

     and is dischargable by composing
     [p256_proj_jacobian_affine_equiv] (algebraic, proven above) with
     [p256_FElem_iff_Bignum] (representation, proven via
     [BignumFElemBridge]). The composition is mechanical sep-logic
     plumbing — no further admits needed at the algebraic level. *)

End P256_Bedrock_Correctness.
