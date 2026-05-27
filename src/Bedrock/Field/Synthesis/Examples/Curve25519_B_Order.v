(** * [Curve25519_B_Order] — computational verification that [ℓ·B = E.zero].
 *
 *   Proves [B] has order [ℓ = 2^252 + 277423...] (the prime-order subgroup
 *   generator) by direct computation of [ℓ·B] in projective Edwards XYZT
 *   coordinates, verified via [Decidable.vm_decide].
 *
 *   ## Why XYZT projective + [Decidable.vm_decide]?
 *
 *   - [vm_compute] on affine Edwards add EXPOSES [F.div = F.inv = F.pow],
 *     whose [Pos.iter] structure normalises to a term tree that the kernel
 *     cannot inject in reasonable time (RC-22 in [reference_slow_proofs_fiat]).
 *   - XYZT (Hisil-Carter-Dawson-Wong) projective add formulas have NO
 *     division — pure F.mul/F.add/F.sub.  By choosing [Z = 5] for B we
 *     embed [y_B = 4/5] without ever calling F.div.
 *   - Plain [vm_compute; reflexivity] still times out on F sigma-type
 *     normalisation, but [Decidable.vm_decide] evaluates the [Decidable
 *     (F.eq …)] instance entirely on the underlying [Z]-values, sidestepping
 *     the F-injection bottleneck.
 *
 *   ## Result
 *
 *   Total kernel-check: ~92s for the full conjunction (X=0, T=0, Y=Z) at
 *   the 252-bit scalar [ℓ].  Each component is ~22s individually.
 *
 *   ## Outstanding bridge
 *
 *   This lemma establishes [Edwards_xyzt_smult_pos ℓ B_xyzt] is the XYZT
 *   projective identity.  To consume it as [Curve25519.E.mul ℓ Curve25519.E.B
 *   = Curve25519.E.zero] (or its [Nat.iter]-form [nB ℓ = E.zero]) one
 *   additionally needs:
 *
 *     1. [edwards_xyzt_to_affine : XYZT-point → E.point] respects [add].
 *     2. [Edwards_xyzt_smult_pos n P ≡ scalarmult_ref (Z.pos n) (affine P)]
 *        via induction on [positive]'s binary structure + add-homomorphism.
 *     3. Coordinate-form [B_xyzt] = projective representation of
 *        [Curve25519.E.B].
 *
 *   These are mechanical (~50 LoC each) using fiat-crypto's
 *   [Crypto.Curves.Edwards.XYZT.Basic].
 *)

From Stdlib Require Import ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

Local Notation FF := (F p).
Local Notation Fzero := (F.zero : FF).
Local Notation Fone  := (F.one : FF).

(** Projective Edwards XYZT add (Hisil-Carter-Dawson-Wong, division-free).
    Uses explicit [fst]/[snd] projections — bare tuple patterns autogenerate
    intermediate binders named [p] which shadow the prime [p] in scope. *)
Definition edwards_xyzt_add25519 (P Q : FF * FF * FF * FF) : FF * FF * FF * FF :=
  let X1 := fst (fst (fst P)) in
  let Y1 := snd (fst (fst P)) in
  let Z1 := snd (fst P) in
  let T1 := snd P in
  let X2 := fst (fst (fst Q)) in
  let Y2 := snd (fst (fst Q)) in
  let Z2 := snd (fst Q) in
  let T2 := snd Q in
  let A := (Y1 - X1) * (Y2 - X2) in
  let B := (Y1 + X1) * (Y2 + X2) in
  let C := (F.of_Z _ 2 * Curve25519.E.d) * T1 * T2 in
  let D := F.of_Z _ 2 * Z1 * Z2 in
  let E := B - A in
  let Ff := D - C in
  let G := D + C in
  let H := B + A in
  (E * Ff, G * H, Ff * G, E * H).

(** Binary log-depth scalar mult on XYZT-projective Curve25519 Edwards. *)
Fixpoint Edwards_xyzt_smult_pos (n : positive) (P : FF * FF * FF * FF)
  : FF * FF * FF * FF :=
  match n with
  | xH => P
  | xO n' => let Q := Edwards_xyzt_smult_pos n' P in edwards_xyzt_add25519 Q Q
  | xI n' => let Q := Edwards_xyzt_smult_pos n' P in
             edwards_xyzt_add25519 (edwards_xyzt_add25519 Q Q) P
  end.

(** Curve25519's base point [B] in XYZT projective representation, with
    [Z = 5] chosen so [y_B = 4/5] becomes [Y/Z = 4/5] WITHOUT calling F.div. *)
Definition B_xyzt : FF * FF * FF * FF :=
  let xB := F.of_Z _ 15112221349535400772501151409588531511454012693041857206046113283949847762202 in
  (F.of_Z _ 5 * xB, F.of_Z _ 4, F.of_Z _ 5, F.of_Z _ 4 * xB).

(** The Curve25519 prime order, as a positive literal. *)
Definition l_pos : positive :=
  7237005577332262213973186563042994240857116359379907606001950938285454250989.

(** Sanity: [l_pos = Spec.Curve25519.l]. *)
Lemma l_pos_eq_spec : (Z.pos l_pos = Z.pos Spec.Curve25519.l)%Z.
Proof. reflexivity. Qed.

(** ===== Main computational fact =====

    [ℓ·B] in XYZT is the projective identity [(0, c, c, 0)]: all three
    invariants [X=0], [T=0], [Y=Z] hold.  By [Decidable.vm_decide] in ~92s.
*)
(** Native-compiled decision (faster than [vm_cast] for the 252-doubling
    computation): [apply dec_bool; native_cast_no_check (eq_refl true)],
    mirroring [Spec.Curve25519.prime_p]'s use of [native_cast_no_check]. *)
Local Ltac native_decide_eq :=
  apply Decidable.dec_bool; native_cast_no_check (eq_refl true).

Lemma lB_is_xyzt_identity :
  let lB := Edwards_xyzt_smult_pos l_pos B_xyzt in
  fst (fst (fst lB)) = Fzero            (* X = 0 *)
  /\ snd lB = Fzero                      (* T = 0 *)
  /\ snd (fst lB) = snd (fst (fst lB)).  (* Y = Z *)
Proof.
  cbv zeta. split; [ | split ]; native_decide_eq.
Qed.
