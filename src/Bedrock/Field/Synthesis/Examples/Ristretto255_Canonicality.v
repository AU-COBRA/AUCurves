(** * Ristretto255_Canonicality — Phase B.2 + Phase B.4 derived theorems.
 *
 *  Two theorems, both derived from already-stated lemmas in
 *  [Ristretto255_RoundTrip] without introducing new admits in their
 *  proofs:
 *
 *  - Phase B.2: [ristretto_decode_canonical] — every ristretto-equivalence
 *    class has at most one valid byte encoding.  Factors through
 *    [ristretto_decode_encode_roundtrip] + [canonical_rep_selection].
 *
 *  - Phase B.4: [ristretto_quotient_add] (def) and
 *    [ristretto_encode_add_commute] — the byte-level group operation
 *    induced by decoding, adding via the Edwards law, and re-encoding,
 *    commutes with the encoder.
 *
 *  Two new lemmas at the Edwards-algebra layer are stated but left
 *  Admitted with full proof strategies in their docstrings:
 *
 *    - [ristretto_equiv_sym]        symmetry of the equivalence
 *                                   (P - Q = -(Q - P), Edwards negation)
 *    - [ristretto_equiv_add_compat] E[4] is normal in E (closure of E[4]
 *                                   under E.add plus commutativity)
 *
 *  These are CRISPLY Edwards-algebra (not Ristretto-specific) and do
 *  NOT overlap with the [canonical_rep_case_*] admits in
 *  [Ristretto255_RoundTrip.v] (which handle the Hamburg-flip selection
 *  of canonical representatives).
 *
 *  This file lives separate from [Ristretto255_RoundTrip.v] so the
 *  algebraic-content agent working on [canonical_rep_case_*] and this
 *  derived layer can be edited without merge conflicts.
 *
 *  Companion files:
 *    - [Ristretto255_Encode.v]      (Phase A.1)
 *    - [Ristretto255_Decode.v]      (Phase A.2)
 *    - [Ristretto255_RoundTrip.v]   (Phase B.1 + algebraic admits)
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Decode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_RoundTrip.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).

(* Field tactic + group machinery for the Edwards-algebra admits below
   (same setup as Ristretto255_TorsionCases.v; [fsatz] times out on the
   concrete value of [Curve25519.E.d], so the stdlib [field] tactic with
   [E.d]/[SQRT_M1] kept opaque is used instead). *)
Local Existing Instance Curve25519.field.
Local Existing Instance Curve25519.char_ge_3.

Add Field _curve25519_field_canon :
  (Algebra.Field.field_theory_for_stdlib_tactic(T:=F (2^255-19)%positive))
  (morphism (F.ring_morph (2^255-19)%positive),
   constants [F.is_constant],
   div (F.morph_div_theory (2^255-19)%positive),
   power_tac (F.power_theory (2^255-19)%positive) [F.is_pow_constant]).

(* ========================================================================
   Section 1: Edwards-equivalence algebraic helpers.

   Two lemmas about [ristretto_equiv] that follow from standard Edwards
   group theory.  They are Admitted with proof strategies; the
   downstream B.2 / B.4 theorems factor through them.

   These are CRISPLY DIFFERENT from the algebraic admits in
   [Ristretto255_RoundTrip.v] — those concern the encoder's canonical-
   representative selection (a Hamburg-flip / Jacobi-quartic story).
   These two concern the group structure of [E[4]] inside [E] alone
   (closure + symmetry), and are dischargeable by direct Edwards
   group calculation (no encoder pipeline involved).
   ======================================================================== *)

(** ** [ristretto_equiv_sym] — equivalence is symmetric.

    P ~ Q iff (P - Q) ∈ E[4].  Symmetry requires (Q - P) = -(P - Q),
    and E[4] closed under negation:
      -(0, 1)        = (0, 1)         in E[4]
      -(0, -1)       = (0, -1)        in E[4]  (Edwards: -(x, y) = (-x, y))
      Wait: Edwards opp is (-x, y), so -(0, 1) = (0, 1), -(0, -1) = (0, -1),
      -(SQRT_M1, 0)  = (-SQRT_M1, 0)  in E[4]
      -(-SQRT_M1, 0) = (SQRT_M1, 0)   in E[4]
    All four cases land in E[4]; hence symmetric.

    PROOF (~30 LoC Edwards calculation):
      - case analysis on the 4-torsion class.
      - for each, compute [sub_affine Q P] = -(sub_affine P Q) and check
        it lies in the same set.
*)
(** ** [ristretto_equiv_refl] — equivalence is reflexive: P - P = O = (0,1) ∈ E[4].
    Worked at the typed-Edwards-group level (P + (-P) = E.zero by [right_inverse]),
    whose coordinates are (0,1) — the identity case of [is_4torsion_affine]. *)
Lemma ristretto_equiv_refl : forall P : Curve25519.E.point, ristretto_equiv P P.
Proof.
  intros P.
  pose (Popp := @AffineProofs.E.opp _ _ _ _ F.opp F.add F.sub F.mul _ _
    Curve25519.field _ Curve25519.E.a Curve25519.E.d Curve25519.E.nonzero_a P).
  pose (D := Curve25519.E.add P Popp).
  assert (Hcoord : E.coordinates D
    = (sub_affine_x (point_coords P) (point_coords P),
       sub_affine_y (point_coords P) (point_coords P)))
    by (destruct P as [[x y] Hoc]; reflexivity).
  pose proof (@AffineProofs.E.edwards_curve_commutative_group _ _ _ _
    F.opp F.add F.sub F.mul _ _ Curve25519.field Curve25519.char_ge_3 _
    Curve25519.E.a Curve25519.E.d Curve25519.E.nonzero_a Curve25519.E.square_a
    Curve25519.E.nonsquare_d) as Hgrp.
  destruct Hgrp as [Hgrp_group _].
  assert (HD0 : (D = Curve25519.E.zero)%E)
    by (subst D Popp; apply right_inverse).
  unfold ristretto_equiv. rewrite sub_affine_eq_pair. left.
  unfold CompleteEdwardsCurve.E.eq in HD0. rewrite Hcoord in HD0.
  destruct HD0 as [Hx Hy]. split; assumption.
Qed.

Lemma ristretto_equiv_sym :
  forall P Q : Curve25519.E.point,
    ristretto_equiv P Q -> ristretto_equiv Q P.
Proof.
  (* TODO: 4-way case analysis on [is_4torsion_affine].  Each case is a
     ~5-line Edwards negation calculation. *)
Admitted.

(** ** [ristretto_equiv_add_compat] — equivalence respects Edwards addition.

    E[4] is normal in E.  Since E is abelian, every subgroup is normal,
    and the quotient inherits a group operation.

    PROOF (~50 LoC Edwards calculation):
      1. By [ristretto_equiv], (P - P') and (Q - Q') are both in E[4].
      2. (P + Q) - (P' + Q') = (P - P') + (Q - Q') by Edwards commutativity
         and associativity.
      3. Sum of two 4-torsion elements is a 4-torsion element (E[4] is
         a finite group of size 4 under E.add; closure is a 4x4 table).
      4. Hence (P + Q) - (P' + Q') ∈ E[4], i.e. equivalent.
*)
Lemma ristretto_equiv_add_compat :
  forall P P' Q Q' : Curve25519.E.point,
    ristretto_equiv P P' ->
    ristretto_equiv Q Q' ->
    ristretto_equiv (Curve25519.E.add P Q) (Curve25519.E.add P' Q').
Proof.
  (* TODO: see strategy in docstring above. *)
Admitted.

(* ========================================================================
   Section 2: Phase B.2 — Canonicality.

   Statement: every ristretto-equivalence class has at most one canonical
   byte encoding.  More precisely: if [bs1] and [bs2] both decode to
   ristretto-equivalent points, then [bs1 = bs2].

   Proof structure (no new admits beyond Section 1):

     1.  From [Hdec1]/[Hdec2] and [decode_some_implies_canonical], extract
         that both [bs1] and [bs2] are 32-byte strings.
     2.  Apply [ristretto_decode_encode_roundtrip] to each, obtaining
         [bs_i = ristretto_encode_bytes (to_extended (point_coords P_i))].
     3.  Apply [canonical_rep_selection] under the hypothesis
         [ristretto_equiv P Q] to conclude the two encodings agree.
     4.  Chain the three equalities to close the goal.

   The two dependencies on Section 1 ([ristretto_equiv_sym], etc.) are
   confined to the derived iff corollary; the main canonicality
   theorem uses ONLY [decode_some_implies_canonical] (Qed),
   [ristretto_decode_encode_roundtrip] (admitted, B.1) and
   [canonical_rep_selection] (admitted, A.3).
   ======================================================================== *)

(** ** [ristretto_decode_canonical] — Phase B.2 main theorem.

    Two byte strings that decode to ristretto-equivalent points are
    bit-for-bit identical.  This is what licenses the use of byte
    equality as the underlying equality in security-protocol byte-level
    accounting. *)
Theorem ristretto_decode_canonical :
  forall (oc : OnCurveObligation) (bs1 bs2 : list Byte.byte)
         (P Q : Curve25519.E.point),
    ristretto_decode_bytes oc bs1 = Some P ->
    ristretto_decode_bytes oc bs2 = Some Q ->
    ristretto_equiv P Q ->
    bs1 = bs2.
Proof.
  intros oc bs1 bs2 P Q Hdec1 Hdec2 Hequiv.
  pose proof (decode_some_implies_canonical oc bs1 P Hdec1) as [Hlen1 _].
  pose proof (decode_some_implies_canonical oc bs2 Q Hdec2) as [Hlen2 _].
  pose proof (ristretto_decode_encode_roundtrip oc bs1 Hlen1 P Hdec1) as Hrt1.
  pose proof (ristretto_decode_encode_roundtrip oc bs2 Hlen2 Q Hdec2) as Hrt2.
  rewrite <- Hrt1, <- Hrt2.
  apply canonical_rep_selection. exact Hequiv.
Qed.

(** ** Corollary: a decoded value is determined by the byte string
       (trivial: [Some] injection). *)
Theorem ristretto_decode_function_modulo_equiv :
  forall (oc : OnCurveObligation) (bs : list Byte.byte) (P Q : Curve25519.E.point),
    ristretto_decode_bytes oc bs = Some P ->
    ristretto_decode_bytes oc bs = Some Q ->
    P = Q.
Proof.
  intros oc bs P Q HP HQ.
  rewrite HP in HQ. inversion HQ. reflexivity.
Qed.

(* ========================================================================
   Section 3: Phase B.4 — Group-law commutation.

   The byte-level group operation [ristretto_quotient_add] is defined
   structurally as "decode, add via [Curve25519.E.add], encode".  The
   commutation theorem [ristretto_encode_add_commute] follows from
   [canonical_rep_selection] applied to the encoder-decoder round-trip:

     encode(P + Q)
       = encode(decode(encode(P)) + decode(encode(Q)))     [by B.1]
       = quotient_add(encode(P), encode(Q))               [by def]

   The intermediate step uses [canonical_rep_selection] composed with
   [ristretto_equiv_add_compat] (Section 1) to argue that "P + Q" and
   "decode(encode P) + decode(encode Q)" land in the same ristretto
   coset, hence encode to identical byte strings.
   ======================================================================== *)

(** ** [ristretto_quotient_add] — the byte-level group operation.

    Decodes two byte strings, performs Edwards addition on the resulting
    typed points, and re-encodes.  On any decode failure, returns the
    encoding of the identity point [E.zero] (the "bad point" fallback).
*)
Definition ristretto_zero_bytes : list Byte.byte :=
  ristretto_encode_bytes (to_extended (point_coords Curve25519.E.zero)).

Definition ristretto_quotient_add
  (oc : OnCurveObligation)
  (bs1 bs2 : list Byte.byte) : list Byte.byte :=
  match ristretto_decode_bytes oc bs1, ristretto_decode_bytes oc bs2 with
  | Some P, Some Q =>
      ristretto_encode_bytes (to_extended (point_coords (Curve25519.E.add P Q)))
  | _, _ => ristretto_zero_bytes
  end.

(** ** Length invariant of the quotient operation.  Every match branch
    produces a [ristretto_encode_bytes]-image, hence length 32. *)
Lemma ristretto_quotient_add_length :
  forall oc bs1 bs2,
    length (ristretto_quotient_add oc bs1 bs2) = 32%nat.
Proof.
  intros oc bs1 bs2.
  unfold ristretto_quotient_add, ristretto_zero_bytes.
  destruct (ristretto_decode_bytes oc bs1);
    destruct (ristretto_decode_bytes oc bs2);
    apply ristretto_encode_bytes_length.
Qed.

(** ** [ristretto_encode_add_commute] — Phase B.4 main theorem.

    The encoder is a group homomorphism from [(E, +)] to the byte-level
    group [(bytes, ristretto_quotient_add oc)], modulo the ristretto
    quotient.

    Proof structure:
      1. Decode [encode P] gives some [P' ~ P] (by B.1 encode-decode
         round-trip; requires the [on_main_subgroup] guard).
      2. Decode [encode Q] gives some [Q' ~ Q].
      3. By [ristretto_equiv_add_compat]: [P + Q ~ P' + Q'].
      4. By [canonical_rep_selection]: [encode (P + Q) = encode (P' + Q')].
      5. Chain definitions.
*)
Theorem ristretto_encode_add_commute :
  forall (oc : OnCurveObligation) (P Q : Curve25519.E.point),
    on_main_subgroup P -> on_main_subgroup Q ->
    ristretto_quotient_add oc
      (ristretto_encode_bytes (to_extended (point_coords P)))
      (ristretto_encode_bytes (to_extended (point_coords Q)))
    = ristretto_encode_bytes (to_extended (point_coords (Curve25519.E.add P Q))).
Proof.
  intros oc P Q HmP HmQ.
  unfold ristretto_quotient_add.
  destruct (ristretto_encode_decode_roundtrip oc P HmP) as [P' [HdecP HeqP]].
  destruct (ristretto_encode_decode_roundtrip oc Q HmQ) as [Q' [HdecQ HeqQ]].
  rewrite HdecP, HdecQ.
  symmetry.
  apply canonical_rep_selection.
  apply ristretto_equiv_add_compat; assumption.
Qed.

(** ** Special case: encoding the identity element.

    The identity [E.zero] encodes to [ristretto_zero_bytes].  This is by
    definition and doesn't require any admits. *)
Lemma ristretto_encode_zero :
  ristretto_zero_bytes
  = ristretto_encode_bytes (to_extended (point_coords Curve25519.E.zero)).
Proof. reflexivity. Qed.

(* ========================================================================
   Section 4: Combined statements.

   Convenience theorems for downstream callers (e.g. zkgroup-hax) that
   want a single iff or a clean shape.
   ======================================================================== *)

(** ** Decoder is injective on its image, modulo equivalence.

    Combined statement: two byte strings encode the same ristretto coset
    iff they are equal.  This is exactly the requirement for using byte
    equality as ristretto equality, which is what dalek's [Eq] on
    [RistrettoPoint] amounts to.

    Uses [ristretto_equiv_sym] for the reflexive case of the [<-]
    direction (when bs1 = bs2 we have P = Q and need to construct
    [ristretto_equiv P P]). *)
Theorem ristretto_decode_byte_eq_iff_equiv :
  forall (oc : OnCurveObligation) (bs1 bs2 : list Byte.byte)
         (P Q : Curve25519.E.point),
    ristretto_decode_bytes oc bs1 = Some P ->
    ristretto_decode_bytes oc bs2 = Some Q ->
    (bs1 = bs2 -> ristretto_equiv P Q) /\
    (ristretto_equiv P Q -> bs1 = bs2).
Proof.
  intros oc bs1 bs2 P Q HdecP HdecQ.
  split.
  - intros Heq. subst bs2.
    rewrite HdecP in HdecQ. inversion HdecQ; subst Q.
    (* [ristretto_equiv P P] now discharged by [ristretto_equiv_refl]
       (P - P = O = (0,1) ∈ E[4], via the typed Edwards group). *)
    apply ristretto_equiv_refl.
  - intro Hequiv. eapply ristretto_decode_canonical; eauto.
Qed.

(** ** One-direction version (no new admits): equivalence implies
    bytes equal.  This is the direction security proofs actually use:
    "two points in the same coset have identical encodings". *)
Theorem ristretto_decode_byte_eq_of_equiv :
  forall (oc : OnCurveObligation) (bs1 bs2 : list Byte.byte)
         (P Q : Curve25519.E.point),
    ristretto_decode_bytes oc bs1 = Some P ->
    ristretto_decode_bytes oc bs2 = Some Q ->
    ristretto_equiv P Q ->
    bs1 = bs2.
Proof. exact ristretto_decode_canonical. Qed.

(** ** Length preservation of the quotient operation. *)
Theorem ristretto_quotient_add_length_invariant :
  forall oc bs1 bs2,
    length (ristretto_quotient_add oc bs1 bs2) = 32%nat.
Proof. apply ristretto_quotient_add_length. Qed.

(* ========================================================================
   Phase B.2 + B.4 deliverables summary:

   QED (depends only on already-stated lemmas in Ristretto255_RoundTrip.v):
     - ristretto_decode_canonical            (B.2 main theorem)
     - ristretto_decode_function_modulo_equiv
     - ristretto_quotient_add_length
     - ristretto_encode_zero                 (definitional)
     - ristretto_decode_byte_eq_of_equiv     (one-direction iff)
     - ristretto_encode_add_commute          (B.4 main theorem, depends on
                                              Section 1's add_compat admit)
     - ristretto_quotient_add_length_invariant

   ADMITTED (new Edwards-algebra content, NOT subsumed by RoundTrip.v):
     - ristretto_equiv_sym                   (~30 LoC: Edwards negation)
     - ristretto_equiv_add_compat            (~50 LoC: E[4] normality)
     - ristretto_decode_byte_eq_iff_equiv    (one branch — uses unstated
                                              refl, intentionally left as
                                              the natural iff form)

   Each admit comes with a concrete Edwards-group proof strategy
   documented in its docstring, dischargeable by any future agent doing
   pure Edwards calculation (independent of the canonical-rep / Hamburg-
   flip story in [Ristretto255_RoundTrip.v]).
   ======================================================================== *)
