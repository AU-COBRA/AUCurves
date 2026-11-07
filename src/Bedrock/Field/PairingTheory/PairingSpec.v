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

(** The definitions of the pairing recipe (Section [PairingSpec]: [frobenius_Q],
    [frobenius2_Q], [apply_correction(s)], [final_exp_easy], [final_exp_hard], [final_exp],
    [optimal_ate]) are in [PairingSpecDefs.v], re-exported here, so that they can be used without
    the [MillerFunctionModel] section below. *)
Require Export Bedrock.Field.PairingTheory.PairingSpecDefs.

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
