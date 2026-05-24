(** Development scratch for the ristretto injectivity residual
    (encode_decode_equiv).  Strengthened with the on-curve hypothesis on
    pP (REQUIRED: an off-curve pP whose encoding decodes would give a
    false E[4] conclusion).  Imports the built RoundTrip.vo. *)

From Stdlib Require Import ZArith NArith.
From Stdlib Require Import micromega.Lia Bool.Bool.
From Stdlib Require Import Init.Byte Lists.List.
Require Import coqutil.Byte coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Decode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_RoundTrip.
Require Bedrock.Field.Synthesis.Examples.Ristretto255_Sqrt.
Require Bedrock.Field.Synthesis.Examples.Ristretto255_CaseScratch.
Import ListNotations.
Local Open Scope F_scope.
Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).
Local Existing Instance Curve25519.field.
Local Existing Instance Curve25519.char_ge_3.
Add Field _f : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F (2^255-19)%positive))
  (morphism (F.ring_morph (2^255-19)%positive), constants [F.is_constant],
   div (F.morph_div_theory (2^255-19)%positive),
   power_tac (F.power_theory (2^255-19)%positive) [F.is_pow_constant]).

(* a = -1 in Curve25519. *)
Local Lemma HaQ : Curve25519.E.a = F.opp Fone.
Proof. unfold Curve25519.E.a. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

(* a/b = c whenever a = c*b and b<>0. *)
Local Lemma div_eq : forall (a b c : Fp), b <> Fzero -> a = (c * b)%F -> (a / b)%F = c.
Proof. intros a b c Hb Ha. rewrite Ha. field. exact Hb. Qed.

(* ===================== STEP 1 reduction (pure field algebra) =====================
   If the Edwards difference numerators/denominators of (x,y) and (x',y') satisfy one
   of the four polynomial systems below (with both sub_affine denominators nonzero),
   then sub_affine (x,y) (x',y') is one of the four 4-torsion points. *)
Local Lemma step1_reduction : forall (x y x' y' : Fp),
  (Fone + Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  (Fone - Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  (   ((x * y' - y * x' = Fzero) /\ (y * y' - x * x' = Fone + Curve25519.E.d * x * x' * y * y'))
   \/ ((x * y' - y * x' = Fzero) /\ (y * y' - x * x' = F.opp (Fone + Curve25519.E.d * x * x' * y * y')))
   \/ ((y * y' - x * x' = Fzero) /\ (x * y' - y * x' = SQRT_M1 * (Fone - Curve25519.E.d * x * x' * y * y')))
   \/ ((y * y' - x * x' = Fzero) /\ (x * y' - y * x' = F.opp SQRT_M1 * (Fone - Curve25519.E.d * x * x' * y * y'))))%F ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hdx Hdy Hcases.
  rewrite sub_affine_eq_pair. unfold is_4torsion_affine, sub_affine_x, sub_affine_y, opp_affine.
  rewrite HaQ.
  destruct Hcases as [[Ha Hb]|[[Ha Hb]|[[Ha Hb]|[Ha Hb]]]];
  [ left | right; left | right; right; left | right; right; right ];
  split.
  - apply (div_eq _ _ Fzero Hdx). transitivity (x * y' - y * x'); [ ring | rewrite Ha; ring ].
  - apply (div_eq _ _ Fone Hdy). transitivity (y * y' - x * x'); [ ring | rewrite Hb; ring ].
  - apply (div_eq _ _ Fzero Hdx). transitivity (x * y' - y * x'); [ ring | rewrite Ha; ring ].
  - apply (div_eq _ _ (F.opp Fone) Hdy). transitivity (y * y' - x * x'); [ ring | rewrite Hb; ring ].
  - apply (div_eq _ _ SQRT_M1 Hdx). transitivity (x * y' - y * x'); [ ring | rewrite Hb; ring ].
  - apply (div_eq _ _ Fzero Hdy). transitivity (y * y' - x * x'); [ ring | rewrite Ha; ring ].
  - apply (div_eq _ _ (F.opp SQRT_M1) Hdx). transitivity (x * y' - y * x'); [ ring | rewrite Hb; ring ].
  - apply (div_eq _ _ Fzero Hdy). transitivity (y * y' - x * x'); [ ring | rewrite Ha; ring ].
Qed.

(* ===================== STEP 2 partial: principal-branch y-determination =====================
   In the encoder's non-rotate / non-flip / was_square branch, the encoded s satisfies
   s^2 = (invsqrtE * x*y * (1-y))^2 with the sqrt invariant (1+y)(1-y)(xy)^2 invsqrtE^2 = 1.
   Combined with the decoder relation s^2 (1+y') = 1-y', this forces y = y' (sign-free).
   This is the cleanest piece of the encoder inversion and is reused by the principal
   (identity, system (i)) torsion case. *)
Local Lemma yeq_noflip : forall (s x y y' invsqrtE : Fp),
  (s * s * (Fone + y') = Fone - y')%F ->
  (Fone + s * s <> Fzero)%F ->
  (s * s = invsqrtE * (x * y) * (Fone - y) * (invsqrtE * (x * y) * (Fone - y)))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)) * (invsqrtE * invsqrtE) = Fone)%F ->
  (Fone - y <> Fzero)%F ->
  y = y'.
Proof.
  intros s x y y' invsqrtE Hs2y' Hu2nz Hs2enc Hinv H1y.
  assert (Hs2y : (s * s * (Fone + y) = Fone - y)%F).
  { apply (Ristretto255_Sqrt.mul_cancel_l (Fone - y) _ _ H1y).
    transitivity ((Fone + y) * (Fone - y) * (x * y * (x * y)) * (invsqrtE * invsqrtE) * ((Fone - y) * (Fone - y)))%F.
    - rewrite Hs2enc. ring.
    - rewrite Hinv. ring. }
  apply (Ristretto255_Sqrt.mul_cancel_l (Fone + s * s) _ _ Hu2nz).
  transitivity (Fone - s * s).
  - replace ((Fone + s * s) * y)%F with (y + (s * s * (Fone + y)) - s * s)%F by ring.
    rewrite Hs2y. ring.
  - replace ((Fone + s * s) * y')%F with (y' + (s * s * (Fone + y')) - s * s)%F by ring.
    rewrite Hs2y'. ring.
Qed.

(* ============================================================================
   STATUS (ristretto255 injectivity residual / Decaf cofactor theorem).

   DONE (Qed, 0 axioms):
     * [step1_reduction] — the full STEP-1 reduction: any of the four
       polynomial systems (with the two sub_affine denominators nonzero)
       implies [is_4torsion_affine (sub_affine (x,y) (x',y'))].  Pure field
       algebra; covers all four torsion points (0,1),(0,-1),(SQRT_M1,0),
       (-SQRT_M1,0).  REUSABLE.
     * [div_eq], [HaQ] — supporting field/curve facts.
     * [yeq_noflip] — STEP-2 principal-branch y-determination (sign-free):
       the encoder's non-rotate/non-flip/was_square branch pins y = y'.

   The verified proof skeleton for [encode_decode_equiv'] (all steps below
   were machine-checked interactively and re-establish on each session) is:

       intros x y x' y' Hoc Hdec.
       pose proof (encode_decode_same_s (x, y) (x', y') Hdec) as Hsame.
       set (s := ristretto_encode (to_extended (x, y))) in *.
       unfold ristretto_encode_bytes, ristretto_encode_bytes_of_F in Hdec.
       fold s in Hdec.
       pose proof (decoded_self_characterization s x' y' Hdec) as Hchar.
       cbv zeta in Hchar.
       destruct Hchar as (Hnegs & Hynz & Hu2nz & Hvnz & Hyvu2 & Hxv2v & Hxneg & Hoc_Q).
       (* decoder profile in hand: y'*(1+s^2)=1-s^2, x'^2*v=4s^2, both on curve,
          is_negative s=false, is_negative x'=false, y'<>0 *)
       assert (Hs2y' : s*s*(1+y') = 1-y') ... (* Qed, derived from Hyvu2 *)
       assert (Hsdef : s = ristretto_encode_aux x y 1 (x*y)) by reflexivity.
       unfold ristretto_encode_aux in Hsdef.
       set (Aenc := (1+y)*(1-y)*(x*y*(x*y))) in *.
       destruct (sqrt_ratio_m1 1 Aenc) as [wsenc invsqrtE] eqn:Hsrenc.
       set (zarg := x*y*(invsqrtE*((1+y)*(1-y))*(invsqrtE*(x*y))*(x*y))) in *.
       destruct (is_negative zarg) eqn:Hrot.   (* rotate vs not *)
       (* each rotate branch further splits on the inner flip [is_negative(X'*zarg)]
          and on wsenc via sqrt_ratio_m1_correct *)

   REMAINING GAP (the genuine Decaf cofactor content, ~250-400 LoC):
   From the encoder case-split above, produce one of [step1_reduction]'s four
   polynomial systems.  Per branch:
     - non-rotate, non-flip, was_square : y = y' (have [yeq_noflip]); then
       sign-pinning [is_negative x'=false] + the encoder flip-condition forces
       x = x' (NOT -x'), giving system (i) [identity, (0,1)].
     - non-rotate, flip               : y = -y'  -> system (ii) [(0,-1)].
     - rotate (both flips)            : (x,y) is the order-4 translate
       (SQRT_M1*y', SQRT_M1*x') resp. its negation, using
       INVSQRT_A_MINUS_D^2*(a-d)=1 -> systems (iii)/(iv).
   The Decaf key is that exactly ONE of [Aenc] / [rotated arg] is a square
   (SQRT_M1 is a quadratic non-residue: see local_SQRT_M1_nonsquare in
   Ristretto255_RoundTrip), which is what makes [rotate] well-defined and pins
   the active branch; the [s=0] degenerate case (-> identity coset) and the
   x-sign pinning are the most delicate sub-steps.  Also requires the two
   sub_affine denominators (Edwards completeness, d a non-square) nonzero to
   feed [step1_reduction].
   ============================================================================ *)
Lemma encode_decode_equiv' : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ristretto_decode_coords (ristretto_encode_bytes (to_extended (x, y))) = Some (x', y') ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
Admitted.
