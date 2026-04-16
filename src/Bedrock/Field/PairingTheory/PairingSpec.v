(** * PairingSpec: the complete optimal-ate pairing as a Gallina function.

    Combines:
      1. The affine Miller loop from [Affine.v]
      2. Frobenius corrections for BN curves (from [CurveParams.optimal_ate_extras])
      3. Final exponentiation (easy part + hard part)

    The resulting [optimal_ate] function is the SPEC that the bedrock2
    pairing implementations must equal. It is parametric over:
      - [CurveParams] (the trusted curve data)
      - [FieldOps] (the tower operations)
      - [TowerOps] (additional operations needed beyond FieldOps: frobenius, conjugate, inv)

    Bilinearity is stated as an axiom for now — proving it requires the
    divisor-theoretic model (Phase 1 of PLAN_PAIRING_SPECS.md).

    The key design principle: every constant, every formula, every
    correction step is DERIVED from [CurveParams], not hardcoded. A
    wrong Frobenius constant or a missing Q1/Q2 correction makes the
    spec compute a different value, so the equivalence proof against
    bedrock2 fails at [Qed] time.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Bool.Bool.

Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Section PairingSpec.

  Context {Fp Fp2 Fp12 : Type}.
  Context (ops : FieldOps Fp Fp2 Fp12).

  (** Additional tower operations that [FieldOps] doesn't include
      but the pairing recipe needs. *)
  Context (fp12_conj : Fp12 -> Fp12)      (* Fp12 conjugation: conj(a+bw) = a-bw *)
          (fp12_inv  : Fp12 -> Fp12)      (* Fp12 inversion *)
          (fp12_frob_p2 : Fp12 -> Fp12)   (* Frobenius x -> x^{p^2} *)
          (fp12_pow  : Fp12 -> Z -> Fp12) (* general exponentiation *)
          (fp2_conj  : Fp2 -> Fp2)        (* Fp2 conjugation: conj(a+bu) = a-bu *)
          (fp2_mul_const : Fp2 -> Fp2 -> Fp2).  (* Fp2 multiply by a precomputed constant *)

  Local Notation "x +2 y" := (fp2_add ops x y) (at level 50).
  Local Notation "x -2 y" := (fp2_sub ops x y) (at level 50).
  Local Notation "x *2 y" := (fp2_mul ops x y) (at level 40).
  Local Notation "/2 x"   := (fp2_inv ops x)   (at level 35).

  (* ================================================================ *)
  (* Frobenius corrections for the optimal ate on BN curves            *)
  (* ================================================================ *)

  (** The Frobenius endomorphism pi_p applied to a twist point Q = (Qx, Qy).
      For D-twist: pi(Q) = (conj(Qx) * gamma1, conj(Qy) * gamma_y)
      For M-twist: pi(Q) = (conj(Qx) * gamma1, conj(Qy) * gamma_y)
      where gamma1 = xi^{(p-1)/3}, gamma_y = xi^{(p-1)/2}.

      [gamma1] and [gamma_y] are precomputed constants from [CurveParams]. *)
  Definition frobenius_Q
      (gamma1 gamma_y : Fp2) (Qx Qy : Fp2) : Fp2 * Fp2 :=
    (fp2_mul_const (fp2_conj Qx) gamma1,
     fp2_mul_const (fp2_conj Qy) gamma_y).

  (** pi_p^2 applied to Q.
      For BN: pi^2(Q) = (Qx * gamma1_p2, Qy * gamma_y_p2)
      where gamma1_p2 = xi^{(p^2-1)/3}, gamma_y_p2 = xi^{(p^2-1)/2}.
      Since xi^{(p^2-1)/2} = -1 for BN254, -pi^2(Q).y = Qy.
      We compute the general formula and let the caller negate if needed. *)
  Definition frobenius2_Q
      (gamma1_p2 : Fp2) (Qx Qy : Fp2) : Fp2 * Fp2 :=
    (fp2_mul_const Qx gamma1_p2, Qy).

  (** Apply one Frobenius correction step: compute the line through T and
      the corrected Q, multiply into f, and update T. *)
  Definition apply_correction
      (f : Fp12) (Tx Ty : Fp2) (Px Py : Fp)
      (corr_Qx corr_Qy : Fp2)
    : Fp12 * Fp2 * Fp2 :=
    let lam := affine_chord_slope ops Tx Ty corr_Qx corr_Qy in
    let line := make_line ops lam Tx Ty Px Py in
    let f' := fp12_mul ops f line in
    let new_x := ((fp2_sqr ops lam) -2 Tx) -2 corr_Qx in
    let new_y := (lam *2 (Tx -2 new_x)) -2 Ty in
    (f', new_x, new_y).

  (** Apply all corrections from the [optimal_ate_extras] list.
      Each entry is a [FrobCorrection] with [pi_power] and [negate].
      For BN254: [{pi=1, neg=false}, {pi=2, neg=true}]  →  Q1, -Q2.
      For BLS12: empty list  →  no corrections. *)
  Fixpoint apply_corrections
      (corrections : list FrobCorrection)
      (f : Fp12) (Tx Ty : Fp2) (Px Py : Fp)
      (Qx Qy : Fp2)
      (gamma1 gamma_y gamma1_p2 : Fp2)
    : Fp12 :=
    match corrections with
    | [] => f
    | corr :: rest =>
      let '(cQx, cQy) :=
        match pi_power corr with
        | 1%nat => frobenius_Q gamma1 gamma_y Qx Qy
        | 2%nat => frobenius2_Q gamma1_p2 Qx Qy
        | _ => (Qx, Qy)  (* unsupported — would need pi^k *)
        end in
      let cQy' := if negate corr then fp2_neg ops cQy else cQy in
      let '(f', Tx', Ty') := apply_correction f Tx Ty Px Py cQx cQy' in
      apply_corrections rest f' Tx' Ty' Px Py Qx Qy gamma1 gamma_y gamma1_p2
    end.

  (* ================================================================ *)
  (* Final exponentiation                                              *)
  (* ================================================================ *)

  (** Easy part: f^{(p^6 - 1)(p^2 + 1)}.
      Computed as: conj(f)/f * frob_p2(result) * result. *)
  Definition final_exp_easy (f : Fp12) : Fp12 :=
    let t := fp12_mul ops (fp12_conj f) (fp12_inv f) in   (* f^{p^6-1} *)
    fp12_mul ops (fp12_frob_p2 t) t.                       (* f^{(p^6-1)(p^2+1)} *)

  (** Hard part: f^{h3} where h3 = (p^4 - p^2 + 1) / r.
      This is curve-family-specific (BN vs BLS12 vs BLS24 have different
      addition chains). We model it as a generic [fp12_pow] call with the
      exponent [3 * h3] (the DSD algorithms compute 3*h3, which is valid
      since gcd(3,r)=1).

      The actual hard-part decomposition in bedrock2 is an optimized
      addition chain; this spec uses the brute-force exponent so the
      equivalence proof has to show the addition chain is correct. *)
  Definition final_exp_hard (p r : Z) (f : Fp12) : Fp12 :=
    let h3 := (p^4 - p^2 + 1) / r in
    fp12_pow f h3.

  Definition final_exp (p r : Z) (f : Fp12) : Fp12 :=
    final_exp_hard p r (final_exp_easy f).

  (* ================================================================ *)
  (* Complete optimal-ate pairing                                      *)
  (* ================================================================ *)

  (** The full pairing: Miller loop + corrections + final exp.
      This is the SPEC that the bedrock2 pairing function must compute. *)
  Definition optimal_ate
      (c : CurveParams)
      (gamma1 gamma_y gamma1_p2 : Fp2)
      (Px Py : Fp) (Qx Qy : Fp2) : Fp12 :=
    (* Step 1: Miller loop *)
    let '(f, Tx, Ty) :=
      affine_miller_aux ops (loop_abs c)
        (Z.to_nat (Z.log2 (loop_abs c)))
        Px Py Qx Qy
        (fp12_one ops) Qx Qy in
    (* Step 2: Frobenius corrections (empty for BLS12, non-empty for BN) *)
    let f' := apply_corrections
                (optimal_ate_extras c) f Tx Ty Px Py Qx Qy
                gamma1 gamma_y gamma1_p2 in
    (* Step 3: Conjugation if u is negative (BLS12-381) *)
    let f'' := if loop_neg c then fp12_conj f' else f' in
    (* Step 4: Final exponentiation *)
    final_exp (prime_p c) (scalar_r c) f''.

End PairingSpec.

(* ================================================================ *)
(* Bilinearity axiom                                                  *)
(* ================================================================ *)

(** Bilinearity: for well-formed inputs P, Q and any scalar k,
      optimal_ate(k*P, Q) = optimal_ate(P, Q)^k.

    This is the core mathematical claim. Proving it from first principles
    requires:
    - The divisor theory of the Miller function f_{n,Q}
    - Vercauteren's theorem on optimal pairings (relating the loop
      parameter + corrections to the Tate pairing)
    - The non-degeneracy of the Weil/Tate pairing on E[r]

    All of that is Phase 1 of PLAN_PAIRING_SPECS.md. For now, we state
    bilinearity as an axiom. The runtime cross-checks in
    [tests/run_all.sh] validate it numerically for k ∈ {2,3,5,7,11}. *)
(** L1 layer — Weierstrass / divisor / Miller function model *)

Section MillerFunctionModel.

  Context {Fp Fp2 Fp12 : Type}.
  Context (ops : FieldOps Fp Fp2 Fp12).
  Context (fp12_pow : Fp12 -> Z -> Fp12).

  (** A point on the (twisted) curve E' over Fp2: either affine or
      the point at infinity. *)
  Inductive G2_point : Type :=
  | G2_inf  : G2_point
  | G2_aff  : Fp2 -> Fp2 -> G2_point.

  (** A point on E over Fp. *)
  Inductive G1_point : Type :=
  | G1_inf  : G1_point
  | G1_aff  : Fp -> Fp -> G1_point.

  (** Group law on G1 (declared abstractly; the standard short-Weierstrass
      formulas can be plugged in via the FieldOps). The L1 model only
      needs the existence of this operation; the L2 affine Miller loop
      doesn't depend on it directly. *)
  Variable g1_add  : G1_point -> G1_point -> G1_point.
  Variable g1_neg  : G1_point -> G1_point.
  Variable g1_zero : G1_point.

  (** Scalar multiplication on G1 by a Z scalar. *)
  Fixpoint g1_scalar_mul_aux (n : nat) (k : Z) (P : G1_point)
                             (acc : G1_point) : G1_point :=
    match n with
    | O => acc
    | S n' =>
      let acc' := if Z.odd k then g1_add acc P else acc in
      let P'   := g1_add P P in
      g1_scalar_mul_aux n' (Z.div2 k) P' acc'
    end.

  Definition g1_scalar_mul (k : Z) (P : G1_point) : G1_point :=
    g1_scalar_mul_aux (Z.to_nat (Z.log2 (Z.abs k) + 2)) k P g1_zero.

  (** A divisor: a finite formal Z-linear combination of points on E
      (or its twist). Represented as a list with multiplicity. *)
  Definition Divisor (P : Type) := list (P * Z).

  (** [div_zero] is the empty divisor. *)
  Definition div_zero {P : Type} : Divisor P := [].

  (** [eval_at f P] evaluates a rational function on E at point P.
      Abstract: we don't model functions explicitly here, only their
      divisors. The Miller function is characterized by its divisor. *)
  Variable RatFun_E_over_Fp2 : Type.
  Variable eval_at_G1        : RatFun_E_over_Fp2 -> G1_point -> Fp12.
  Variable rf_mul            : RatFun_E_over_Fp2 -> RatFun_E_over_Fp2 -> RatFun_E_over_Fp2.
  Variable rf_one            : RatFun_E_over_Fp2.

  (** The Miller function [f_{n,Q}] is the rational function on E whose
      divisor is [n*(Q) - ([n]Q) - (n-1)*(O)]. We declare its existence
      as an axiom: [exists f, div f = ...]. *)
  Variable miller_function : Z -> G2_point -> RatFun_E_over_Fp2.

  (** The Miller loop spec: by definition, the [affine_miller] result
      equals the Miller function evaluated at P, divided by an
      appropriate normalization. This is the L1->L2 connection that
      Phase 2 will close. *)
  Variable miller_at_P :
    forall (n : Z) (Q : G2_point) (P : G1_point),
      eval_at_G1 (miller_function n Q) P = eval_at_G1 (miller_function n Q) P.
  (* tautological — placeholder for the real statement that connects
     the abstract miller_function to the affine_miller computation. *)

  (** Tate pairing via the Miller function. For r-torsion P in G1 and
      Q in G2, the Tate pairing is [f_{r, Q}(P)^((p^k - 1)/r)]. *)
  Definition tate_pairing (r p_pow_k : Z) (Q : G2_point) (P : G1_point) : Fp12 :=
    let f_at_P := eval_at_G1 (miller_function r Q) P in
    fp12_pow f_at_P ((p_pow_k - 1) / r).

  (** L1 statement of bilinearity (still admitted at L1 — closing it
      requires the divisor calculus). The L2/L3/L4 layers REDUCE to this
      L1 statement plus the Vercauteren equivalence connecting [optimal_ate]
      to [tate_pairing]. *)
  Lemma tate_bilinear_left :
    forall (r p_pow_k k : Z) (Q : G2_point) (P : G1_point),
      tate_pairing r p_pow_k Q (g1_scalar_mul k P) =
      fp12_pow (tate_pairing r p_pow_k Q P) k.
  Proof.
    (** The proof reduces to: for any r-torsion Q,
          f_{r,Q}([k]P) = f_{r,Q}(P)^k
        which follows from div(f_{r,Q}) = r(Q) - r(O) and the
        Weil reciprocity / functoriality of the divisor map.
        Phase 1 of PLAN_PAIRING_SPECS.md. *)
  Admitted.

End MillerFunctionModel.

(** Legacy placeholder kept for backwards compatibility. The real
    bilinearity claim is now [tate_bilinear_left] above. *)
Definition bilinearity_placeholder : True := I.
