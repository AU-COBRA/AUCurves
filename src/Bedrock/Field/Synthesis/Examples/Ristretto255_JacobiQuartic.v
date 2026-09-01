(** * Ristretto255 — the Jacobi quartic [J = E / E[4]] and membership.

    This file is the entry point for closing [encode_decode_equiv] (the
    sole remaining admit of the Ristretto255 round-trip cluster) via the
    Decaf/Ristretto Jacobi-quartic correspondence, rather than the
    per-leaf inversion of [Ristretto255_Inj.main_inversion] (which is
    provably stuck on the [M = SQRT_M1] branch, where the decoder
    [x']-coordinate is not a rational function of [(x, y)]).

    The key object is the quartic [J(Curve25519)] cut out by

       on_jq s x  :=  x^2 * v(s) = 4 * s^2,

    where [v s = -(d * (1 - s^2)^2) - (1 + s^2)^2], i.e. (expanded)

       v s = -(d + 1) * (1 + s^4) + 2 * (d - 1) * s^2     ([jq_v_expanded]).

    The encoder [E -> Fp, P |-> s] is the [s]-coordinate of the image of
    [P] under [E -> J]; its fibers are exactly the [E[4]]-cosets.  Working
    at the [s]/JQ level keeps everything rational in [s] (the encode
    output): [x] enters only as [x^2 = 4 s^2 / v], so the irrational-[x']
    obstruction never arises.

    [jq_v] is, by construction, definitionally the decoder's [v] from
    [Ristretto255_RoundTrip.decoded_self_characterization]; hence the
    decoder's output already lies on [J] ([decoder_on_jq], for free).
    The remaining work is the encoder-side membership ([M1]) and the
    coset separation ([M3]).  See [writeup/RISTRETTO_JACOBI_QUARTIC_PLAN.md].
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Algebra.IntegralDomain.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Decode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_RoundTrip.
Require Bedrock.Field.Synthesis.Examples.Ristretto255_Sqrt.
Require Bedrock.Field.Synthesis.Examples.Ristretto255_CaseScratch.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).
Local Open Scope F_scope.
Local Existing Instance Curve25519.field.
Local Existing Instance Curve25519.char_ge_3.
Add Field _f : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F (2^255-19)%positive))
  (morphism (F.ring_morph (2^255-19)%positive), constants [F.is_constant],
   div (F.morph_div_theory (2^255-19)%positive),
   power_tac (F.power_theory (2^255-19)%positive) [F.is_pow_constant]).

(* ========================================================================
   M0 — the Jacobi-quartic object and decoder-side membership.
   ======================================================================== *)

(** [jq_v s] — the quartic coefficient, definitionally equal to the
    decoder's [v] in [decoded_self_characterization]. *)
Definition jq_v (s : Fp) : Fp :=
  (F.opp (Curve25519.E.d * ((Fone - s*s) * (Fone - s*s))) - (Fone + s*s) * (Fone + s*s))%F.

(** [on_jq s x] — the point [(s, x)] lies on the Jacobi quartic [J]. *)
Definition on_jq (s x : Fp) : Prop :=
  (x * x * jq_v s = F.of_Z _ 4 * (s * s))%F.

(** The expanded quartic form: [v s = -(d+1)(1+s^4) + 2(d-1)s^2]. *)
Lemma jq_v_expanded : forall s : Fp,
  jq_v s = (F.opp (Curve25519.E.d + Fone) * (Fone + s*s*s*s)
            + (Fone + Fone) * (Curve25519.E.d - Fone) * (s*s))%F.
Proof. intro s. unfold jq_v. ring. Qed.

(** [4 <> 0] in [Fp]. *)
Lemma four_nz : (F.of_Z (2^255-19) 4) <> Fzero.
Proof. Decidable.vm_decide. Qed.

(** [d + 1 <> 0] in [Fp] (the leading coefficient [-(d+1)] of the [s^4]
    term is nonzero). *)
Lemma dp1_nz : (Curve25519.E.d + Fone)%F <> Fzero.
Proof. Decidable.vm_decide. Qed.

(** [d - 1 <> 0] in [Fp]. *)
Lemma dm1_nz : (Curve25519.E.d - Fone)%F <> Fzero.
Proof. Decidable.vm_decide. Qed.

(** [SQRT_M1] is a NON-square in [Fp].  Euler: [SQRT_M1^((p-1)/2) = (SQRT_M1^2)^((p-1)/4)
    = (-1)^(2^253 - 5) = -1 <> 1].  Decided by [PrimeFieldTheorems.F.Decidable_square] (the
    same mechanism as [Curve25519.E.nonsquare_d]).  Lynchpin for the decode-success
    [was_square] bridge: if the decoder's sqrt argument is a square, the [sqrt_ratio_m1]
    branch cannot be the [SQRT_M1]-twist (else [SQRT_M1] would itself be a square). *)
Lemma SQRT_M1_nonsquare : forall x : Fp, (x * x)%F <> SQRT_M1.
Proof.
  assert (Hns : ~ (exists y : Fp, (y * y)%F = SQRT_M1)).
  { pose (Hdec := @PrimeFieldTheorems.F.Decidable_square (2^255 - 19)%positive
                  prime_p ltac:(Decidable.vm_decide) SQRT_M1).
    Decidable.vm_decide. }
  intros x Hx. apply Hns. exists x. exact Hx.
Qed.

(** From JQ membership with x <> 0, the quartic coefficient [jq_v s] (= the decoder's [v])
    is a SQUARE, namely [(2 s / x)^2].  (From [on_jq]: [x^2 * jq_v s = 4 s^2].) *)
Lemma jq_v_is_square : forall s x : Fp, on_jq s x -> x <> Fzero ->
  exists w : Fp, jq_v s = (w * w)%F.
Proof.
  intros s x Hjq Hx. unfold on_jq in Hjq.
  assert (Hxx : (x * x)%F <> Fzero)
    by (intro H; destruct (Ristretto255_Sqrt.mul_zero_factor _ _ H); apply Hx; assumption).
  exists (F.of_Z _ 2 * s / x)%F.
  apply (Ristretto255_Sqrt.mul_cancel_l (x * x)%F _ _ Hxx).
  rewrite Hjq. field. exact Hx.
Qed.

(** DECODE-SUCCESS [was_square] BRIDGE.  The decoder's sqrt argument is
    [den = v * u2^2 = jq_v s * (1 + s^2)^2] (its [v] is exactly [jq_v s]).  When [(s,x)] is
    on the Jacobi quartic with [x <> 0], [jq_v s] is a square ([jq_v_is_square]), hence so is
    [den]; therefore [sqrt_ratio_m1 Fone den] reports [was_square = true] — otherwise
    [den * r^2 = SQRT_M1] would make [SQRT_M1] a square, contradicting [SQRT_M1_nonsquare].
    This is the converse of [decoder_on_jq]'s direction and the crux of decode-success. *)
Lemma den_was_square : forall s x : Fp,
  on_jq s x -> x <> Fzero ->
  (jq_v s * ((Fone + s*s) * (Fone + s*s)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone (jq_v s * ((Fone + s*s) * (Fone + s*s)))) = true.
Proof.
  intros s x Hjq Hx Hden.
  destruct (jq_v_is_square s x Hjq Hx) as [w Hw].
  pose proof (sqrt_ratio_m1_correct Fone
                (jq_v s * ((Fone + s*s) * (Fone + s*s)))%F Hden) as Hc.
  destruct (sqrt_ratio_m1 Fone (jq_v s * ((Fone + s*s) * (Fone + s*s)))%F) as [ws r] eqn:E.
  cbn [fst]. destruct Hc as [[ [Hws _] | [Hwsf Hr] ] Hrneg].
  - exact Hws.
  - exfalso. apply (SQRT_M1_nonsquare (w * (Fone + s*s) * r)%F).
    transitivity ((jq_v s * ((Fone + s*s) * (Fone + s*s))) * r * r)%F.
    + rewrite Hw. ring.
    + rewrite Hr. ring.
Qed.

(** ** Decoder-side membership (free).

    Every coordinate pair returned by the decoder lies on [J]: this is
    exactly the [x'^2 * v = 4 s^2] conjunct of
    [decoded_self_characterization]. *)
Lemma decoder_on_jq : forall (s x' y' : Fp),
  ristretto_decode_coords (le_split 32 (F.to_Z s)) = Some (x', y') ->
  on_jq s x'.
Proof.
  intros s x' y' Hdec.
  pose proof (decoded_self_characterization s x' y' Hdec) as D.
  cbv zeta in D.
  destruct D as (Hnegs & Hynz & Hu2nz & Hvnz & Hyvu2 & Hq & Hxneg & HocQ).
  unfold on_jq, jq_v.
  exact Hq.
Qed.

(* ========================================================================
   M1 — encoder-side membership (IN PROGRESS).

   Target (disjunctive, since the encoder's X' = if rotate then SQRT_M1*y
   else x):

     encoder_on_jq : on_curve (x,y) -> u1*u2^2 <> 0 ->
       let s := ristretto_encode_aux x y Fone (x*y) in
       on_jq s x  \/  on_jq s (y * SQRT_M1).

   The encoder splits on rotate := is_negative(x*y * invsqrt^2*u1*u2^2)
   and a flip := is_negative(X' * invsqrt^2*u1*u2^2); `sqrt_ratio_m1_correct`
   gives the invariant  V*invsqrt^2 ∈ {Fone, SQRT_M1}  (V := u1*u2^2),
   i.e. ws=true => V*invsqrt^2 = Fone,  ws=false => = SQRT_M1.

   The CORE algebra (proven below for the principal non-rotate ws=true,
   flip=false leaf): with V*invsqrt^2 = Fone one gets (1+y)*s^2 = (1-y),
   hence (1+y)(1-s^2)=2y and (1+y)(1+s^2)=2, and `on_jq s x` collapses to
   the on-curve equation  x^2*(1+d*y^2) = y^2-1.

   CRUX (open): the non-rotate, ws=false leaf makes BOTH disjuncts false
   (on_jq s x would force x^2*y*(d+1)=0).  So the encoder must satisfy
   ws=false => rotate (for on-curve points) — Ristretto's cofactor-8
   rotate absorbing the non-square branch.  This rot<->ws correlation is
   the remaining content of M1 and must be PROVEN (not assumed).
   ======================================================================== *)

(** Principal leaf: non-rotate, [V*w^2 = Fone] (ws=true), flip=false
    (so the encoder's [Y' = y] and [s = abs(w * x*y * (1 - y))]).
    [on_jq s x] reduces to the on-curve equation.  This validates the
    full algebraic template (abs square, the sqrt invariant, the
    [(1+y)^2] cancellation, and the on-curve reduction). *)
Lemma encoder_on_jq_core_nonrot : forall (x y w : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (((Fone + y) * (Fone - y) * (x * y * (x * y))) * (w * w))%F = Fone ->
  (Fone + y) <> Fzero ->
  on_jq (abs (w * (x*y) * (Fone - y))) x.
Proof.
  intros x y w Hoc Hw H1ynz.
  assert (HaQ : Curve25519.E.a = F.opp Fone)
    by (unfold Curve25519.E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  assert (Habs_sq : forall z:Fp, (abs z * abs z = z * z)%F)
    by (intro z; unfold abs; destruct (is_negative z); ring).
  set (s := abs (w * (x*y) * (Fone - y))) in *.
  assert (Hs2 : ((Fone + y) * (s * s))%F = (Fone - y)%F)
    by (unfold s; rewrite Habs_sq;
        transitivity ((((Fone + y) * (Fone - y) * (x * y * (x * y))) * (w * w)) * (Fone - y))%F;
        [ ring | rewrite Hw; ring ]).
  assert (Hms : ((Fone + y) * (Fone - s*s))%F = ((Fone+Fone) * y)%F)
    by (transitivity ((Fone+y) - (Fone+y)*(s*s))%F; [ ring | rewrite Hs2; ring ]).
  assert (Hps : ((Fone + y) * (Fone + s*s))%F = (Fone+Fone)%F)
    by (transitivity ((Fone+y) + (Fone+y)*(s*s))%F; [ ring | rewrite Hs2; ring ]).
  assert (H1y2nz : ((Fone+y)*(Fone+y))%F <> Fzero)
    by (intro Hk; destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hk) as [H|H]; exact (H1ynz H)).
  assert (Hdxy : (Curve25519.E.d*(x*x)*(y*y))%F = (y*y - x*x - Fone)%F)
    by (rewrite HaQ in Hoc;
        transitivity (Fone + Curve25519.E.d*(x*x)*(y*y) - Fone)%F; [ ring | rewrite <- Hoc; ring ]).
  assert (H4 : F.of_Z (2^255-19) 4 = ((Fone+Fone)*(Fone+Fone))%F) by ring.
  unfold on_jq. rewrite H4.
  apply (Ristretto255_CaseScratch.mul_cancel_l ((Fone+y)*(Fone+y)) _ _ H1y2nz).
  unfold jq_v.
  transitivity (x*x*(F.opp(Curve25519.E.d*(((Fone+y)*(Fone-s*s))*((Fone+y)*(Fone-s*s)))) - ((Fone+y)*(Fone+s*s))*((Fone+y)*(Fone+s*s))))%F;
    [ ring | ].
  rewrite Hms, Hps.
  transitivity ((Fone+Fone)*(Fone+Fone)*((Fone+y)*(s*s))*(Fone+y))%F;
    [ | ring ].
  rewrite Hs2.
  transitivity (F.opp((Fone+Fone)*(Fone+Fone)*(Curve25519.E.d*(x*x)*(y*y))) - (Fone+Fone)*(Fone+Fone)*(x*x))%F;
    [ ring | ].
  rewrite Hdxy. ring.
Qed.

(** Non-rotate, flip=true leaf ([Y' = -y], [s = abs(w*x*y*(1+y))]).  Same
    template, [(1-y)*s^2 = (1+y)]; collapses to the on-curve equation. *)
Lemma encoder_on_jq_core_nonrot_flip : forall (x y w : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (((Fone + y) * (Fone - y) * (x * y * (x * y))) * (w * w))%F = Fone ->
  (Fone - y) <> Fzero ->
  on_jq (abs (w * (x*y) * (Fone + y))) x.
Proof.
  intros x y w Hoc Hw H1ynz.
  assert (HaQ : Curve25519.E.a = F.opp Fone)
    by (unfold Curve25519.E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  assert (Habs_sq : forall z:Fp, (abs z * abs z = z * z)%F)
    by (intro z; unfold abs; destruct (is_negative z); ring).
  set (s := abs (w * (x*y) * (Fone + y))) in *.
  assert (Hs2 : ((Fone - y) * (s * s))%F = (Fone + y)%F)
    by (unfold s; rewrite Habs_sq;
        transitivity ((((Fone + y) * (Fone - y) * (x * y * (x * y))) * (w * w)) * (Fone + y))%F;
        [ ring | rewrite Hw; ring ]).
  assert (Hms : ((Fone - y) * (Fone - s*s))%F = (F.opp (Fone+Fone) * y)%F)
    by (transitivity ((Fone-y) - (Fone-y)*(s*s))%F; [ ring | rewrite Hs2; ring ]).
  assert (Hps : ((Fone - y) * (Fone + s*s))%F = (Fone+Fone)%F)
    by (transitivity ((Fone-y) + (Fone-y)*(s*s))%F; [ ring | rewrite Hs2; ring ]).
  assert (H1y2nz : ((Fone-y)*(Fone-y))%F <> Fzero)
    by (intro Hk; destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hk) as [H|H]; exact (H1ynz H)).
  assert (Hdxy : (Curve25519.E.d*(x*x)*(y*y))%F = (y*y - x*x - Fone)%F)
    by (rewrite HaQ in Hoc;
        transitivity (Fone + Curve25519.E.d*(x*x)*(y*y) - Fone)%F; [ ring | rewrite <- Hoc; ring ]).
  assert (H4 : F.of_Z (2^255-19) 4 = ((Fone+Fone)*(Fone+Fone))%F) by ring.
  unfold on_jq. rewrite H4.
  apply (Ristretto255_CaseScratch.mul_cancel_l ((Fone-y)*(Fone-y)) _ _ H1y2nz).
  unfold jq_v.
  transitivity (x*x*(F.opp(Curve25519.E.d*(((Fone-y)*(Fone-s*s))*((Fone-y)*(Fone-s*s)))) - ((Fone-y)*(Fone+s*s))*((Fone-y)*(Fone+s*s))))%F;
    [ ring | ].
  rewrite Hms, Hps.
  transitivity ((Fone+Fone)*(Fone+Fone)*((Fone-y)*(s*s))*(Fone-y))%F;
    [ | ring ].
  rewrite Hs2.
  transitivity (F.opp((Fone+Fone)*(Fone+Fone)*(Curve25519.E.d*(x*x)*(y*y))) - (Fone+Fone)*(Fone+Fone)*(x*x))%F;
    [ ring | ].
  rewrite Hdxy. ring.
Qed.

(** Rotate, flip=false leaf ([X' = SQRT_M1*y], [Y' = SQRT_M1*x],
    [den_inv = w*u1*INVSQRT_A_MINUS_D], [s = abs(w*u1*IAD*(1 - x*SQRT_M1))]);
    concludes [on_jq s (y*SQRT_M1)].

    This is the leaf carrying genuine [SQRT_M1] algebra (the [(1 - x*SQRT_M1)]
    factor).  After the same template reduces it to a polynomial residual,
    the [SQRT_M1]/[E.d] CONSTANTS are abstracted to opaque variables
    ([set]+[clearbody]) so that [nsatz] works over a small symbolic ring
    instead of choking on the huge concrete constants; [nsatz] then finds the
    certificate (residual [~ (1 = 0)] discharged by [discriminate]).  Uses
    [INVSQRT_A_MINUS_D^2 * (a - d) = 1] (the [K2] defining relation). *)
Lemma encoder_on_jq_core_rot : forall (x y w : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (((Fone + y) * (Fone - y) * (x * y * (x * y))) * (w * w))%F = Fone ->
  x <> Fzero -> y <> Fzero ->
  on_jq (abs (w * ((Fone + y) * (Fone - y)) * INVSQRT_A_MINUS_D * (Fone - x * SQRT_M1))) (y * SQRT_M1).
Proof.
  intros x y w Hoc Hw Hxnz Hynz.
  assert (HaQ : Curve25519.E.a = F.opp Fone)
    by (unfold Curve25519.E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  assert (Habs_sq : forall z:Fp, (abs z * abs z = z * z)%F)
    by (intro z; unfold abs; destruct (is_negative z); ring).
  assert (HSqi : (SQRT_M1 * SQRT_M1)%F = F.opp Fone) by (exact Ristretto255_CaseScratch.SQRT_M1_sq).
  assert (K2 : (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (Curve25519.E.a - Curve25519.E.d))%F = Fone)
    by (unfold INVSQRT_A_MINUS_D, Curve25519.E.a, Curve25519.E.d;
        apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  set (s := abs (w * ((Fone + y) * (Fone - y)) * INVSQRT_A_MINUS_D * (Fone - x * SQRT_M1))) in *.
  assert (Hrs : ((Curve25519.E.a - Curve25519.E.d) * (x*x) * (y*y) * (s*s))%F
              = ((Fone+y)*(Fone-y) * ((Fone - x*SQRT_M1)*(Fone - x*SQRT_M1)))%F)
    by (unfold s; rewrite Habs_sq;
        transitivity ((INVSQRT_A_MINUS_D*INVSQRT_A_MINUS_D*(Curve25519.E.a-Curve25519.E.d))
                      * (((Fone+y)*(Fone-y)*(x*y*(x*y)))*(w*w))
                      * ((Fone+y)*(Fone-y))
                      * ((Fone - x*SQRT_M1)*(Fone - x*SQRT_M1)))%F;
        [ ring | rewrite K2, Hw; ring ]).
  set (K := ((Curve25519.E.a - Curve25519.E.d) * (x*x) * (y*y))%F) in *.
  assert (HKnz : K <> Fzero)
    by (unfold K; intro Hk;
        destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hk) as [H|Hy];
        [ destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ H) as [Had|Hxx];
          [ revert Had; Decidable.vm_decide
          | destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hxx) as [Hx|Hx]; exact (Hxnz Hx) ]
        | destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hy) as [Hy'|Hy']; exact (Hynz Hy') ]).
  assert (HK2nz : (K*K)%F <> Fzero)
    by (intro Hk; destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hk) as [H|H]; exact (HKnz H)).
  assert (Hms_r : (K * (Fone - s*s))%F = (K - (Fone+y)*(Fone-y)*((Fone-x*SQRT_M1)*(Fone-x*SQRT_M1)))%F)
    by (transitivity (K - K*(s*s))%F; [ ring | rewrite Hrs; ring ]).
  assert (Hps_r : (K * (Fone + s*s))%F = (K + (Fone+y)*(Fone-y)*((Fone-x*SQRT_M1)*(Fone-x*SQRT_M1)))%F)
    by (transitivity (K + K*(s*s))%F; [ ring | rewrite Hrs; ring ]).
  assert (Hyi : ((y*SQRT_M1)*(y*SQRT_M1))%F = F.opp (y*y))
    by (transitivity ((SQRT_M1*SQRT_M1)*(y*y))%F; [ ring | rewrite HSqi; ring ]).
  assert (H4 : F.of_Z (2^255-19) 4 = ((Fone+Fone)*(Fone+Fone))%F) by ring.
  unfold on_jq. rewrite Hyi, H4.
  apply (Ristretto255_CaseScratch.mul_cancel_l (K*K) _ _ HK2nz).
  unfold jq_v.
  transitivity (F.opp(y*y) * (F.opp(Curve25519.E.d*((K*(Fone-s*s))*(K*(Fone-s*s)))) - (K*(Fone+s*s))*(K*(Fone+s*s))))%F;
    [ ring | ].
  rewrite Hms_r, Hps_r.
  transitivity ((Fone+Fone)*(Fone+Fone)*(K*(s*s))*K)%F;
    [ | ring ].
  rewrite Hrs.
  unfold K. rewrite HaQ in Hoc |- *.
  clear Hrs Hms_r Hps_r Hyi H4 K2 Hw Habs_sq HKnz HK2nz Hxnz Hynz s HaQ.
  set (i := SQRT_M1) in *. set (dd := Curve25519.E.d) in *. clearbody i dd.
  nsatz. discriminate.
Qed.

(** Rotate, flip=true leaf ([Y' = -SQRT_M1*x], [s = abs(w*u1*IAD*(1 + x*SQRT_M1))]);
    the sign-flipped mirror of [encoder_on_jq_core_rot]. *)
Lemma encoder_on_jq_core_rot_flip : forall (x y w : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (((Fone + y) * (Fone - y) * (x * y * (x * y))) * (w * w))%F = Fone ->
  x <> Fzero -> y <> Fzero ->
  on_jq (abs (w * ((Fone + y) * (Fone - y)) * INVSQRT_A_MINUS_D * (Fone + x * SQRT_M1))) (y * SQRT_M1).
Proof.
  intros x y w Hoc Hw Hxnz Hynz.
  assert (HaQ : Curve25519.E.a = F.opp Fone)
    by (unfold Curve25519.E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  assert (Habs_sq : forall z:Fp, (abs z * abs z = z * z)%F)
    by (intro z; unfold abs; destruct (is_negative z); ring).
  assert (HSqi : (SQRT_M1 * SQRT_M1)%F = F.opp Fone) by (exact Ristretto255_CaseScratch.SQRT_M1_sq).
  assert (K2 : (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (Curve25519.E.a - Curve25519.E.d))%F = Fone)
    by (unfold INVSQRT_A_MINUS_D, Curve25519.E.a, Curve25519.E.d;
        apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  set (s := abs (w * ((Fone + y) * (Fone - y)) * INVSQRT_A_MINUS_D * (Fone + x * SQRT_M1))) in *.
  assert (Hrs : ((Curve25519.E.a - Curve25519.E.d) * (x*x) * (y*y) * (s*s))%F
              = ((Fone+y)*(Fone-y) * ((Fone + x*SQRT_M1)*(Fone + x*SQRT_M1)))%F)
    by (unfold s; rewrite Habs_sq;
        transitivity ((INVSQRT_A_MINUS_D*INVSQRT_A_MINUS_D*(Curve25519.E.a-Curve25519.E.d))
                      * (((Fone+y)*(Fone-y)*(x*y*(x*y)))*(w*w))
                      * ((Fone+y)*(Fone-y))
                      * ((Fone + x*SQRT_M1)*(Fone + x*SQRT_M1)))%F;
        [ ring | rewrite K2, Hw; ring ]).
  set (K := ((Curve25519.E.a - Curve25519.E.d) * (x*x) * (y*y))%F) in *.
  assert (HKnz : K <> Fzero)
    by (unfold K; intro Hk;
        destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hk) as [H|Hy];
        [ destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ H) as [Had|Hxx];
          [ revert Had; Decidable.vm_decide
          | destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hxx) as [Hx|Hx]; exact (Hxnz Hx) ]
        | destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hy) as [Hy'|Hy']; exact (Hynz Hy') ]).
  assert (HK2nz : (K*K)%F <> Fzero)
    by (intro Hk; destruct (Ristretto255_CaseScratch.mul_zero_factor _ _ Hk) as [H|H]; exact (HKnz H)).
  assert (Hms_r : (K * (Fone - s*s))%F = (K - (Fone+y)*(Fone-y)*((Fone+x*SQRT_M1)*(Fone+x*SQRT_M1)))%F)
    by (transitivity (K - K*(s*s))%F; [ ring | rewrite Hrs; ring ]).
  assert (Hps_r : (K * (Fone + s*s))%F = (K + (Fone+y)*(Fone-y)*((Fone+x*SQRT_M1)*(Fone+x*SQRT_M1)))%F)
    by (transitivity (K + K*(s*s))%F; [ ring | rewrite Hrs; ring ]).
  assert (Hyi : ((y*SQRT_M1)*(y*SQRT_M1))%F = F.opp (y*y))
    by (transitivity ((SQRT_M1*SQRT_M1)*(y*y))%F; [ ring | rewrite HSqi; ring ]).
  assert (H4 : F.of_Z (2^255-19) 4 = ((Fone+Fone)*(Fone+Fone))%F) by ring.
  unfold on_jq. rewrite Hyi, H4.
  apply (Ristretto255_CaseScratch.mul_cancel_l (K*K) _ _ HK2nz).
  unfold jq_v.
  transitivity (F.opp(y*y) * (F.opp(Curve25519.E.d*((K*(Fone-s*s))*(K*(Fone-s*s)))) - (K*(Fone+s*s))*(K*(Fone+s*s))))%F;
    [ ring | ].
  rewrite Hms_r, Hps_r.
  transitivity ((Fone+Fone)*(Fone+Fone)*(K*(s*s))*K)%F;
    [ | ring ].
  rewrite Hrs.
  unfold K. rewrite HaQ in Hoc |- *.
  clear Hrs Hms_r Hps_r Hyi H4 K2 Hw Habs_sq HKnz HK2nz Hxnz Hynz s HaQ.
  set (i := SQRT_M1) in *. set (dd := Curve25519.E.d) in *. clearbody i dd.
  nsatz. discriminate.
Qed.

(** ** Encoder lands on the Jacobi quartic (disjunctive membership).

    For an on-curve [(x,y)] with [u1*u2^2 <> 0], WHEN the encoder's
    [sqrt_ratio_m1] reports a square ([fst ... = true], i.e. [c = Fone]),
    the encoder output [s := ristretto_encode_aux x y 1 (x*y)] satisfies
    [on_jq s x] OR [on_jq s (y*SQRT_M1)] — the encoder's rotated x-coordinate
    [X' = if rotate then SQRT_M1*y else x] is a JQ x-coordinate over [s].

    Proof: unfold the encoder, peel [sqrt_ratio_m1] (the [ws=true] branch of
    [sqrt_ratio_m1_correct] gives the invariant [u1*u2^2 * invsqrt^2 = Fone]),
    then dispatch the four rotate/flip leaves.  The [ws=true] (square)
    hypothesis is exactly what decode-success supplies downstream; for [ws=false]
    the disjunction is genuinely false (the encoder's [s] lands on [J] at a
    different x), so the square condition is necessary, not incidental. *)
Lemma encoder_on_jq : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F) = true ->
  on_jq (ristretto_encode_aux x y Fone (x*y)) x
  \/ on_jq (ristretto_encode_aux x y Fone (x*y)) (y * SQRT_M1).
Proof.
  intros x y Hoc HVnz Hws.
  assert (Hx : x <> Fzero) by (intro H; apply HVnz; rewrite H; ring).
  assert (Hy : y <> Fzero) by (intro H; apply HVnz; rewrite H; ring).
  assert (H1py : (Fone + y)%F <> Fzero) by (intro H; apply HVnz; rewrite H; ring).
  assert (H1my : (Fone - y)%F <> Fzero) by (intro H; apply HVnz; rewrite H; ring).
  unfold ristretto_encode_aux.
  destruct (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F) as [ws invsqrt] eqn:Hsr.
  simpl in Hws. subst ws.
  pose proof (sqrt_ratio_m1_correct Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F HVnz) as Hinv.
  rewrite Hsr in Hinv.
  destruct Hinv as [Hdisj Hrneg].
  assert (Hw : (((Fone + y) * (Fone - y) * (x * y * (x * y))) * (invsqrt * invsqrt))%F = Fone)
    by (destruct Hdisj as [[_ Heq]|[Hbad _]];
        [ transitivity ((Fone + y) * (Fone - y) * (x * y * (x * y)) * invsqrt * invsqrt)%F; [ ring | exact Heq ]
        | discriminate ]).
  set (zi := (invsqrt * ((Fone + y) * (Fone - y)) * (invsqrt * (x * y)) * (x * y))%F) in *.
  destruct (is_negative (x * y * zi)%F) eqn:Hrot;
  [ destruct (is_negative (y * SQRT_M1 * zi)%F) eqn:Hflip;
    [ right; replace (Fone - F.opp (x * SQRT_M1))%F with (Fone + x * SQRT_M1)%F by ring;
      apply (encoder_on_jq_core_rot_flip x y invsqrt Hoc Hw Hx Hy)
    | right; apply (encoder_on_jq_core_rot x y invsqrt Hoc Hw Hx Hy) ]
  | destruct (is_negative (x * zi)%F) eqn:Hflip;
    [ left; replace (Fone - F.opp y)%F with (Fone + y)%F by ring;
      apply (encoder_on_jq_core_nonrot_flip x y invsqrt Hoc Hw H1my)
    | left; apply (encoder_on_jq_core_nonrot x y invsqrt Hoc Hw H1py) ] ].
Qed.

(* ========================================================================
   M3 — coset separation (the injectivity crux).  IN PROGRESS.
   ======================================================================== *)

(** The JQ fiber over [s] is a single [x]-square: any two on-[J] points over
    the same [s] have equal [x^2].  This is the rational-in-[s] core that
    dodges the irrational-[x'] obstruction (x enters only as [x^2]). *)
Lemma jq_x_sq_eq : forall (s X X' : Fp),
  on_jq s X -> on_jq s X' -> jq_v s <> Fzero -> (X * X = X' * X')%F.
Proof.
  intros s X X' HX HX' Hv.
  unfold on_jq in HX, HX'.
  apply (Ristretto255_CaseScratch.mul_cancel_l (jq_v s) _ _ Hv).
  transitivity (X * X * jq_v s)%F; [ ring | ].
  rewrite HX, <- HX'. ring.
Qed.

(** ===== B: encoder→decoder [was_square] assembly =====

    Combines [encoder_on_jq] (gives [on_jq s x ∨ on_jq s (y·SQRT_M1)] from on-curve
    + arg≠0 + ws=true) with [den_was_square] (gives [fst sqrt_ratio_m1 = true] from
    [on_jq] + witness≠0 + den≠0).  This is the clean [was_square] step for
    [decode_encode_success]: takes the four encoder-side hypotheses (matching
    [encoder_on_jq]) plus den≠0, returns the decoder's [was_square=true].  The
    den≠0 obligation is deferred to the caller (it depends on s = encoder output
    and rules out s=±SQRT_M1; provable but not needed in this lemma). *)
Lemma encoder_decoder_was_square : forall (x y : Fp),
  (Curve25519.E.a * (x*x) + y*y = Fone + Curve25519.E.d * (x*x) * (y*y))%F ->
  ((Fone + y) * (Fone - y) * (x*y*(x*y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x*y*(x*y)))) = true ->
  let s := ristretto_encode_aux x y Fone (x*y) in
  (jq_v s * ((Fone + s*s) * (Fone + s*s)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone (jq_v s * ((Fone + s*s) * (Fone + s*s)))) = true.
Proof.
  intros x y Hoc Harg Hws s Hden.
  assert (Hx : x <> Fzero) by (intro H; apply Harg; rewrite H; ring).
  assert (Hy : y <> Fzero) by (intro H; apply Harg; rewrite H; ring).
  assert (HSnz : SQRT_M1 <> Fzero) by (apply Ristretto255_Sqrt.SQRT_M1_nz).
  assert (Hys : (y * SQRT_M1)%F <> Fzero).
  { intro H. destruct (Ristretto255_Sqrt.mul_zero_factor _ _ H);
      [ apply Hy | apply HSnz ]; assumption. }
  destruct (encoder_on_jq x y Hoc Harg Hws) as [Hjq | Hjq].
  - exact (den_was_square s x Hjq Hx Hden).
  - exact (den_was_square s (y * SQRT_M1)%F Hjq Hys Hden).
Qed.

(** ===== B: decoder y-coord characterisation =====

    When [was_square = true], [sqrt_ratio_m1 Fone den] gives [iv] with [den·iv²=1].
    Specialising [den := jq_v(s)·(1+s²)²], the decoder's y-coord
        [y_dec := (1-s²)·(iv·(iv·(1+s²))·jq_v(s))]
    satisfies the clean relation [y_dec · (1+s²) = 1 - s²].  This reduces the
    [y_dec ≠ 0] sign predicate (B's remaining gap) to [s ≠ ±1] (assuming
    [(1+s²) ≠ 0], itself reducing to [s ≠ ±SQRT_M1]). *)
Lemma decoder_y_recovered_eq : forall (s iv : Fp),
  (jq_v s * ((Fone + s*s) * (Fone + s*s)) * (iv * iv) = Fone)%F ->
  ((Fone - s*s) * (iv * (iv * (Fone + s*s)) * jq_v s) * (Fone + s*s)
   = Fone - s*s)%F.
Proof.
  intros s iv Hinv.
  transitivity ((Fone - s*s) * (jq_v s * ((Fone + s*s) * (Fone + s*s)) * (iv * iv)))%F.
  - ring.
  - rewrite Hinv. ring.
Qed.

(** ===== A: Decaf squareness via doubling (CONCRETE PATH, replaces chi_hom approach) =====

    Key derived identity (uses curve eq for P, a = -1):
        [(1 - y_P^2)(1 + x_P^2) = -(d+1) · x_P^2 · y_P^2]    -- [doubling_chi_numerator]
    Combined with the Edwards doubling formula
        [(1 - y_{2P}^2) · D^2 = 4(1 - y_P^2)(1 + x_P^2)]     (D = 1 - d·x_P^2·y_P^2)
    this gives
        [(1 - y_{2P}^2) · D^2 = 4·(-(d+1))·x_P^2·y_P^2]
    so [chi(2P) = [1 - y_{2P}^2] = [-(d+1)]] (since [4·x_P^2·y_P^2/D^2] is a square).

    For Curve25519, [-(d+1)] is a CONCRETE SQUARE mod p, verified by [vm_decide]
    in 4s via [F.Decidable_square] ([neg_d_plus_one_is_square]).  Hence [chi(2P) = 1]
    with explicit witness [2·x_P·y_P·ε/D] where [ε² = -(d+1)].

    [⟨B⟩] has odd order [ℓ]; every [P = nB ∈ ⟨B⟩] equals [2Q] for [Q = ((ℓ+1)/2)·n·B ∈ ⟨B⟩]
    (since [2·(ℓ+1)/2·nB = (ℓ+1)·nB = ℓ·nB + nB = 0 + nB = nB]).  Hence [chi(P) = chi(2Q) = 1]
    for all [P ∈ ⟨B⟩] (modulo edge cases [Q = identity ⟺ P = identity], handled by the
    [s = 0] degenerate case of B).  This gives [main_subgroup_valid] without the
    full 2-descent homomorphism witness.

    Remaining A wiring:
      - [chi_doubling_witness] (algebraic, ~10 LoC): combine [doubling_chi_numerator]
        + [neg_d_plus_one_is_square]'s [ε] + the doubling [y_{2P}^2] formula to give
        an explicit [w] with [(1-y_{2P}^2)·D = 2·x_P·y_P·ε] (or similar shape).
      - [2-surjectivity on ⟨B⟩]: [∀n, ∃m, nB = 2·mB] with [m := ((ℓ+1)/2)·n mod ℓ].
        Standard; needs the group-theoretic order of [B] (= [ℓ]).
      - [chi-to-ws bridge]: [chi(P) = 1 ⟹ ws_P = true], via the curve identity
        [1 - y_P^2 = -x_P^2·(1 + d·y_P^2)] + [sqrt_ratio_m1_correct] + the same
        [SQRT_M1_nonsquare] machinery as [den_was_square] (mirror of B's bridge). *)

Lemma neg_d_plus_one_is_square :
  exists eps : Fp, (eps * eps)%F = F.opp (Curve25519.E.d + Fone).
Proof.
  pose (Hdec := @PrimeFieldTheorems.F.Decidable_square (2^255 - 19)%positive
                  prime_p ltac:(Decidable.vm_decide)
                  (F.opp (Curve25519.E.d + Fone))).
  Decidable.vm_decide.
Qed.

(** 0-form (avoids [nsatz] over [F.opp]): the linear combination of LHS-RHS with
    the curve-eq's LHS-RHS multiplied by [F.opp Fone] is identically zero. *)
Lemma doubling_chi_numerator : forall (xP yP : Fp),
  (Curve25519.E.a * (xP*xP) + yP*yP
   = Fone + Curve25519.E.d * (xP*xP) * (yP*yP))%F ->
  ((Fone - yP*yP) * (Fone + xP*xP)
   + (Curve25519.E.d + Fone) * (xP*xP) * (yP*yP) = Fzero)%F.
Proof.
  intros xP yP Hoc.
  unfold Curve25519.E.a in Hoc.
  (* Hoc has [F.opp 1] (notation-asymmetric with [Fone]); rewrite [<- Hoc]
     against the [Fone + d·x²·y²] subterm (which IS in Hoc's RHS in [Fone] form). *)
  assert (Hzero :
    (Fone + Curve25519.E.d * (xP*xP) * (yP*yP) - yP*yP + xP*xP = Fzero)%F)
    by (rewrite <- Hoc; ring).
  transitivity (Fone + Curve25519.E.d * (xP*xP) * (yP*yP) - yP*yP + xP*xP)%F.
  - ring.
  - exact Hzero.
Qed.

(** ===== A: explicit witness for [chi(2P) = 1] (the key composition) =====

    The numerator [D² - (yP²+xP²)²] of [(1 - y_{2P}²)] is a SQUARE with explicit
    witness [2·ε·xP·yP] (where [ε² = -(d+1)]).  Composes:
      - [doubling_chi_numerator]: [(1-yP²)(1+xP²) = -(d+1)·xP²·yP²] mod curve.
      - [neg_d_plus_one_is_square]: [-(d+1) is a square] with witness [ε].
      - The Edwards-doubling [F1·F2 = 4(1-y_P²)(1+x_P²)] identity, inlined via
        [rewrite Hd] (substitutes [d·xP²·yP² → yP²-xP²-1] from the curve eq,
        making the [D² - (yP²+xP²)²] difference a pure ring identity in [xP, yP]).

    Since [D²] is itself a square, this gives [(1 - y_{2P}²) is a square] —
    i.e. [chi(2P) = 1] (the 2-descent kernel inclusion [2E(Fp) ⊆ ker χ]),
    with an EXPLICIT witness, no `nsatz` and no opaque 2-descent multiplicativity.

    Combined with [⟨B⟩] odd-order [⟹] every [P ∈ ⟨B⟩] is [2Q] for some [Q ∈ ⟨B⟩],
    this gives [main_subgroup_valid] modulo the [ws]-bridge (mirror of [B]'s
    [den_was_square]) — all mechanical from here. *)
Lemma chi_doubling_witness : forall (xP yP : Fp),
  (Curve25519.E.a * (xP*xP) + yP*yP
   = Fone + Curve25519.E.d * (xP*xP) * (yP*yP))%F ->
  exists w : Fp,
    ((Fone - Curve25519.E.d*(xP*xP)*(yP*yP))
       * (Fone - Curve25519.E.d*(xP*xP)*(yP*yP))
     - (yP*yP + xP*xP) * (yP*yP + xP*xP)
     = w * w)%F.
Proof.
  intros xP yP Hoc.
  destruct neg_d_plus_one_is_square as [eps Heps].
  exists (F.of_Z _ 2 * eps * xP * yP)%F.
  unfold Curve25519.E.a in Hoc.
  assert (Hd : (Curve25519.E.d * (xP*xP) * (yP*yP) = yP*yP - xP*xP - Fone)%F).
  { transitivity (Fone + Curve25519.E.d * (xP*xP) * (yP*yP) - Fone)%F.
    - ring.
    - rewrite <- Hoc. ring. }
  assert (Hxy : (eps*eps * (xP*xP) * (yP*yP)
                 = (Fone - yP*yP) * (Fone + xP*xP))%F).
  { replace (eps*eps * (xP*xP) * (yP*yP))%F
      with (eps*eps * (xP*xP * (yP*yP)))%F by ring.
    rewrite Heps.
    replace (F.opp (Curve25519.E.d + Fone) * (xP*xP * (yP*yP)))%F
      with (F.opp (Curve25519.E.d * (xP*xP) * (yP*yP)
                   + xP*xP * (yP*yP)))%F by ring.
    rewrite Hd. ring. }
  rewrite Hd.
  transitivity (F.of_Z _ 4 * ((Fone - yP*yP) * (Fone + xP*xP)))%F.
  - ring.
  - replace ((F.of_Z _ 2 * eps * xP * yP) * (F.of_Z _ 2 * eps * xP * yP))%F
      with (F.of_Z _ 4 * (eps*eps * (xP*xP) * (yP*yP)))%F by ring.
    rewrite Hxy. ring.
Qed.

(** B corollary: the decoder's [y_dec = 0] ⟹ [s² = 1] (= [s = ±1]).
    Direct from [decoder_y_recovered_eq]: [y_dec · (1+s²) = 1 - s²], so
    [y_dec = 0] ⟹ [1 - s² = 0] ⟹ [s² = 1].  Reduces B's [y_dec ≠ 0]
    obligation to the simpler [s² ≠ 1] (= [s ≠ ±1]). *)
Lemma decoder_y_zero_to_s_sq : forall (s iv : Fp),
  (jq_v s * ((Fone + s*s) * (Fone + s*s)) * (iv * iv) = Fone)%F ->
  ((Fone - s*s) * (iv * (iv * (Fone + s*s)) * jq_v s))%F = Fzero ->
  (s * s = Fone)%F.
Proof.
  intros s iv Hinv Hy0.
  pose proof (decoder_y_recovered_eq s iv Hinv) as Hyeq.
  rewrite Hy0 in Hyeq.
  assert (Hy : (Fone - s*s = Fzero)%F) by (rewrite <- Hyeq; ring).
  assert (Heq : (Fone = s*s)%F).
  { transitivity (Fone - s*s + s*s)%F.
    - ring.
    - rewrite Hy. ring. }
  symmetry. exact Heq.
Qed.

(** ===== A: chi-to-ws bridge (mirror of [den_was_square]) =====
    If [1 - y_P^2 = w^2] for some [w] (i.e. [chi(P) = 1]) and the encoder
    [sqrt_ratio_m1] argument is nonzero, then [ws_P = true].  The argument
    [(1+y)(1-y)(xy)^2 = (1-y^2)(xy)^2 = (w·xy)^2] is a square, so
    [sqrt_ratio_m1] enters the [ws=true] branch (else [SQRT_M1] would be a
    square, contradicting [SQRT_M1_nonsquare]). *)
Lemma chi_to_ws : forall (x y : Fp),
  ((Fone + y) * (Fone - y) * (x*y*(x*y)))%F <> Fzero ->
  (exists w : Fp, (Fone - y*y = w * w)%F) ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x*y*(x*y)))) = true.
Proof.
  intros x y Harg [w Hw].
  pose proof (sqrt_ratio_m1_correct Fone _ Harg) as Hsr.
  destruct (sqrt_ratio_m1 Fone _) as [ws r] eqn:E.
  cbn [fst]. destruct Hsr as [[ [Hws _] | [Hwsf Hrf] ] Hrneg].
  - exact Hws.
  - exfalso.
    apply (SQRT_M1_nonsquare (w * (x*y) * r)).
    transitivity ((Fone + y) * (Fone - y) * (x*y*(x*y)) * r * r)%F.
    + transitivity ((Fone - y*y) * (x*y*(x*y)) * r * r)%F.
      * rewrite Hw. ring.
      * ring.
    + rewrite Hrf. ring.
Qed.

(** B helper: [abs z]^2 = z^2 (the sign choice vanishes under squaring). *)
Lemma abs_sq : forall (z : Fp),
  (Ristretto255_Encode.abs z * Ristretto255_Encode.abs z = z * z)%F.
Proof.
  intros z. unfold Ristretto255_Encode.abs.
  destruct (is_negative z); ring.
Qed.

(** B: decoder x-coord-squared characterisation (analog of [decoder_y_recovered_eq]).
    [x_dec^2 * jq_v(s) = (2s)^2].  Uses [abs_sq] (sign drops on squaring) plus the
    [was_square] invariant [den * iv^2 = 1] to simplify [x_dec^2 * jq_v(s)] to [(2s)^2]. *)
Lemma decoder_x_sq_recovered_eq : forall (s iv : Fp),
  (jq_v s * ((Fone + s*s) * (Fone + s*s)) * (iv * iv) = Fone)%F ->
  (Ristretto255_Encode.abs (F.of_Z p 2 * s * (iv * (Fone + s*s)))
   * Ristretto255_Encode.abs (F.of_Z p 2 * s * (iv * (Fone + s*s)))
   * jq_v s
   = F.of_Z p 2 * s * (F.of_Z p 2 * s))%F.
Proof.
  intros s iv Hinv.
  rewrite abs_sq.
  transitivity ((F.of_Z p 2 * s * (F.of_Z p 2 * s)) *
                (jq_v s * ((Fone + s*s) * (Fone + s*s)) * (iv * iv)))%F.
  - ring.
  - rewrite Hinv. ring.
Qed.

(** B: decoder t-coord-squared characterisation.  Composing [decoder_x_sq_recovered_eq] +
    [decoder_y_recovered_eq] gives [t² · jq_v(s) · (1+s²)² = (2s·(1-s²))²], where
    [t = x_dec · y_dec].  All decoder coordinates now have closed-form characterisations. *)
Lemma decoder_t_sq_recovered_eq : forall (s iv : Fp),
  (jq_v s * ((Fone + s*s) * (Fone + s*s)) * (iv * iv) = Fone)%F ->
  ((Ristretto255_Encode.abs (F.of_Z p 2 * s * (iv * (Fone + s*s)))
    * ((Fone - s*s) * (iv * (iv * (Fone + s*s)) * jq_v s)))
   * (Ristretto255_Encode.abs (F.of_Z p 2 * s * (iv * (Fone + s*s)))
      * ((Fone - s*s) * (iv * (iv * (Fone + s*s)) * jq_v s)))
   * jq_v s * ((Fone + s*s) * (Fone + s*s))
   = (F.of_Z p 2 * s * (Fone - s*s)) * (F.of_Z p 2 * s * (Fone - s*s)))%F.
Proof.
  intros s iv Hinv.
  pose proof (decoder_x_sq_recovered_eq s iv Hinv) as Hx.
  pose proof (decoder_y_recovered_eq s iv Hinv) as Hy.
  transitivity ((Ristretto255_Encode.abs (F.of_Z p 2 * s * (iv * (Fone + s*s)))
                 * Ristretto255_Encode.abs (F.of_Z p 2 * s * (iv * (Fone + s*s)))
                 * jq_v s)
                * (((Fone - s*s) * (iv * (iv * (Fone + s*s)) * jq_v s))
                   * (Fone + s*s)
                 * (((Fone - s*s) * (iv * (iv * (Fone + s*s)) * jq_v s))
                    * (Fone + s*s))))%F.
  - ring.
  - rewrite Hx, Hy. ring.
Qed.

(** ===== A: division-step composition — [chi_doubling_witness] in [(1 - y_{2P}²) is a square] form =====

    The Edwards doubling [y_{2P} = (yP²+xP²)/D] where [D = 1 - d·xP²·yP²].
    Combining [chi_doubling_witness]'s numerator-form witness with the division by [D²]
    gives the [chi_to_ws]-ready form [∃w', 1 - y_{2P}² = w'·w'] with witness [w' = w/D].

    Trick: after [field_simplify] both sides are [poly/denom], split with [f_equal2]
    into numerator equality + denominator equality; numerator equality closes via
    [rewrite <- Hw; ring] (where Hw has been [ring_simplify]'d to match the [^]-normal form). *)
Lemma chi_doubling_chi_eq : forall (xP yP : Fp),
  (Curve25519.E.a * (xP*xP) + yP*yP = Fone + Curve25519.E.d * (xP*xP) * (yP*yP))%F ->
  (Fone - Curve25519.E.d*(xP*xP)*(yP*yP))%F <> Fzero ->
  exists w : Fp,
    (Fone - ((yP*yP + xP*xP) / (Fone - Curve25519.E.d*(xP*xP)*(yP*yP)))
            * ((yP*yP + xP*xP) / (Fone - Curve25519.E.d*(xP*xP)*(yP*yP)))
     = w * w)%F.
Proof.
  intros xP yP Hoc HD.
  destruct (chi_doubling_witness xP yP Hoc) as [w Hw].
  exists (w / (Fone - Curve25519.E.d*(xP*xP)*(yP*yP)))%F.
  ring_simplify in Hw.
  field_simplify; try exact HD.
  apply f_equal2; [ | reflexivity ].
  rewrite <- Hw. ring.
Qed.

(** ===== A: FULL COMPOSITION — [ws_{2P} = true] for the Edwards-doubled point =====

    Composes [chi_doubling_chi_eq] (the [(1 - y_{2P}²) is a square] form) with
    [chi_to_ws] (the chi-to-ws bridge).  Gives: for [P] on-curve with [D ≠ 0]
    and the encoder argument for [2P] nonzero, [ws_{2P} = true].  This is the
    full Decaf squareness statement on the [2P] image — A's main theorem
    modulo [⟨B⟩ ⊆ 2·E(Fp)] ([2]-surjectivity, the remaining group-theory glue). *)
Lemma chi_doubling_to_ws_2P : forall (xP yP : Fp),
  (Curve25519.E.a * (xP*xP) + yP*yP
   = Fone + Curve25519.E.d * (xP*xP) * (yP*yP))%F ->
  (Fone - Curve25519.E.d*(xP*xP)*(yP*yP))%F <> Fzero ->
  forall (xR : Fp),
    let yR := ((yP*yP + xP*xP) / (Fone - Curve25519.E.d*(xP*xP)*(yP*yP)))%F in
    ((Fone + yR) * (Fone - yR) * (xR*yR*(xR*yR)))%F <> Fzero ->
    fst (sqrt_ratio_m1 Fone ((Fone + yR) * (Fone - yR) * (xR*yR*(xR*yR)))) = true.
Proof.
  intros xP yP Hoc HD xR yR Harg.
  apply chi_to_ws; [ exact Harg | ].
  unfold yR.
  apply chi_doubling_chi_eq; assumption.
Qed.

(** ===== B: arg=0 degenerate case (s = encode(P) = 0 for E[4]-torsion P) =====

    The encoder's [arg = (1+y)(1-y)(xy)²] is zero precisely for E[4]-torsion P
    (identity (0,1), order-2 (0,-1), order-4 (±SQRT_M1, 0)).  For these, the
    encoder returns s = 0, and the decoder of s = 0 returns the identity (0, 1).

    [decoder_zero_was_square] computes the sqrt_ratio at s = 0: the argument is
    [jq_v(0)·(1+0)² = -(d+1)], which is a square (by [neg_d_plus_one_is_square]).
    So [was_square = true] at s = 0 — the decoder enters its main branch. *)
Lemma jq_v_at_zero : jq_v Fzero = F.opp (Curve25519.E.d + Fone).
Proof. unfold jq_v. ring. Qed.

Lemma decoder_zero_was_square :
  fst (sqrt_ratio_m1 Fone (F.opp (Curve25519.E.d + Fone))) = true.
Proof.
  pose proof neg_d_plus_one_is_square as [eps Heps].
  pose proof dp1_nz as Hdp1.
  assert (Hnz : F.opp (Curve25519.E.d + Fone) <> Fzero).
  { intro H. apply Hdp1.
    transitivity (F.opp (F.opp (Curve25519.E.d + Fone)))%F.
    - ring.
    - rewrite H. ring. }
  pose proof (sqrt_ratio_m1_correct Fone _ Hnz) as Hsr.
  destruct (sqrt_ratio_m1 Fone (F.opp (Curve25519.E.d + Fone))) as [ws r] eqn:E.
  cbn [fst]. destruct Hsr as [[ [Hws _] | [Hwsf Hr] ] _].
  - exact Hws.
  - exfalso.
    apply (SQRT_M1_nonsquare (eps * r)).
    transitivity (F.opp (Curve25519.E.d + Fone) * r * r)%F.
    + rewrite <- Heps. ring.
    + rewrite Hr. ring.
Qed.

(** At s=0, the decoder's recovered y-coord equals [Fone] (given the was_square
    invariant [-(d+1)·iv² = Fone]).  Combined with [decoder_x_at_zero] (x_dec = 0),
    this gives the decoder's full output at s=0: (Fzero, Fone) — the identity. *)
Lemma decoder_y_at_zero : forall (iv : Fp),
  (F.opp (Curve25519.E.d + Fone) * (iv * iv) = Fone)%F ->
  ((Fone - Fzero*Fzero) * (iv * (iv * (Fone + Fzero*Fzero)) * jq_v Fzero) = Fone)%F.
Proof.
  intros iv Hinv.
  rewrite jq_v_at_zero.
  transitivity ((F.opp (Curve25519.E.d + Fone)) * (iv * iv))%F.
  - ring.
  - exact Hinv.
Qed.

Lemma decoder_x_at_zero : forall (iv : Fp),
  Ristretto255_Encode.abs (F.of_Z p 2 * Fzero * (iv * (Fone + Fzero*Fzero))) = Fzero.
Proof.
  intros iv.
  replace (F.of_Z p 2 * Fzero * (iv * (Fone + Fzero*Fzero)))%F
    with (Fzero : Fp) by ring.
  unfold Ristretto255_Encode.abs.
  rewrite Ristretto255_CaseScratch.is_negative_zero. reflexivity.
Qed.

(** ===== B: arg=0 degenerate case CLOSED — decoder of 32 zero-bytes returns identity =====

    Full proof composing the arg=0 helpers: [le_split_F_round_trip] (bytes→s=0),
    [is_negative_zero] (skip the [is_negative s] guard), [decoder_zero_was_square]
    (ws=true so we enter the [Some] branch), [decoder_x_at_zero] + [decoder_y_at_zero]
    (compute the recovered coords as [(Fzero, Fone) = identity]).  This is the full
    B [decode_encode_success] resolved for the degenerate input. *)
Lemma decoder_zero_returns_identity :
  ristretto_decode_coords (le_split 32 0%Z) = Some ((Fzero : Fp), Fone).
Proof.
  unfold ristretto_decode_coords.
  replace (0%Z) with (F.to_Z (Fzero : Fp)) by reflexivity.
  rewrite le_split_F_round_trip.
  rewrite Ristretto255_CaseScratch.is_negative_zero.
  pose proof decoder_zero_was_square as Hws.
  assert (Hnz : F.opp (Curve25519.E.d + Fone) <> Fzero).
  { intro H. pose proof dp1_nz as Hdp1. apply Hdp1.
    transitivity (F.opp (F.opp (Curve25519.E.d + Fone)))%F;
      [ring | rewrite H; ring]. }
  match goal with
  | |- context [sqrt_ratio_m1 Fone ?A] =>
      replace A with (F.opp (Curve25519.E.d + Fone))%F
        by (rewrite <- jq_v_at_zero; unfold jq_v; ring)
  end.
  pose proof (sqrt_ratio_m1_correct Fone _ Hnz) as Hsr.
  destruct (sqrt_ratio_m1 Fone (F.opp (Curve25519.E.d + Fone))) as [ws r] eqn:E.
  cbn [fst] in Hws. subst ws.
  destruct Hsr as [[ [_ Hsq] | [Hwsf _] ] _]; [ | discriminate ].
  assert (Hinv : (F.opp (Curve25519.E.d + Fone) * (r * r) = Fone)%F).
  { transitivity (F.opp (Curve25519.E.d + Fone) * r * r)%F;
      [ring | exact Hsq]. }
  cbn [negb orb].
  match goal with
  | |- context [F.opp (Curve25519.E.d * ?A) - ?B] =>
      replace (F.opp (Curve25519.E.d * A) - B)%F with (jq_v Fzero)
        by (unfold jq_v; ring)
  end.
  rewrite decoder_x_at_zero.
  rewrite (decoder_y_at_zero r Hinv).
  replace (Fzero * Fone)%F with (Fzero : Fp) by ring.
  rewrite Ristretto255_CaseScratch.is_negative_zero.
  cbn [orb].
  reflexivity.
Qed.

(** ===== A: FINAL REDUCTION — main_subgroup_valid reduced to [2]-surjectivity =====

    Given P with coords (xP, yP), if yP is the y-coord of [2Q] for some on-curve Q
    (with D ≠ 0 for the doubling), then ws_P = true (and hence P satisfies
    [valid_ristretto_input]).  This is the final A theorem: A's main_subgroup_valid
    reduces to showing that every prime-order-subgroup point lies in [2·E(Fp)]
    (= the image of [E(Fp)] under doubling) — the [2]-surjectivity on ⟨B⟩
    that ℓ odd makes a clean group-theoretic fact (every nB = 2·((ℓ+1)/2·n·B)).

    Coords-form statement avoids E.point plumbing — the caller (Inj/Canonicality)
    can specialise once the group-level [2]-surjectivity is established. *)
Lemma chi_doubling_main_subgroup :
  forall (xP yP : Fp),
  (Curve25519.E.a * (xP*xP) + yP*yP
   = Fone + Curve25519.E.d * (xP*xP) * (yP*yP))%F ->
  (exists (xQ yQ : Fp),
    (Curve25519.E.a * (xQ*xQ) + yQ*yQ
     = Fone + Curve25519.E.d * (xQ*xQ) * (yQ*yQ))%F /\
    (Fone - Curve25519.E.d*(xQ*xQ)*(yQ*yQ))%F <> Fzero /\
    yP = ((yQ*yQ + xQ*xQ) / (Fone - Curve25519.E.d*(xQ*xQ)*(yQ*yQ)))%F) ->
  ((Fone + yP) * (Fone - yP) * (xP*yP*(xP*yP)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + yP) * (Fone - yP) * (xP*yP*(xP*yP)))) = true.
Proof.
  intros xP yP HoP [xQ [yQ [HoQ [HD HyP_eq]]]] Harg.
  rewrite HyP_eq.
  rewrite HyP_eq in Harg.
  apply (chi_doubling_to_ws_2P xQ yQ HoQ HD xP).
  exact Harg.
Qed.

(** ===== B: encoder structural fact — [z_inv = 1] for valid input =====

    Inside [ristretto_encode_aux x y Fone (xy)] for valid input (ws=true):
      [den1 := invsqrt · (1-y²)]
      [den2 := invsqrt · xy]
      [z_inv := den1 · den2 · T = invsqrt² · (1-y²) · (xy)² · 1]
    which equals [Fone] by the [was_square=true] invariant
    [invsqrt² · ((1-y²)(xy)²) = Fone].

    Consequence: encoder rotate guard = [is_negative (T · z_inv) = is_negative xy].
    Y'-flip guard = [is_negative (X' · z_inv) = is_negative X'].
    This is the algebraic kernel for B's sign-condition analysis ([is_negative t = false]):
    knowing rotate/flip in closed form lets us trace the canonical-representative pick
    leaf-by-leaf and show the decoded [t = x_dec · y_dec] is sign-correct.  *)
Lemma encoder_z_inv_eq_one : forall (x y iv : Fp),
  (iv * iv * ((Fone - y*y) * (x*y * (x*y))) = Fone)%F ->
  (iv * (Fone - y*y) * (iv * (x*y)) * (x*y) = Fone)%F.
Proof.
  intros x y iv Hinv.
  transitivity (iv * iv * ((Fone - y*y) * (x*y * (x*y))))%F.
  - ring.
  - exact Hinv.
Qed.
