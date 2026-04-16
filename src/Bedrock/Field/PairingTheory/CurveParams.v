(** * CurveParams: trusted mathematical data for one pairing-friendly curve.

    This file is the SINGLE-SOURCE-OF-TRUTH for everything about a curve
    that the rest of the pairing pipeline can depend on:

      - the base prime [p] and scalar order [r];
      - the Weierstrass coefficients [a], [b] of E/Fp;
      - the embedding degree [k];
      - the tower nonresidue [xi = xi_re + xi_im * u] in Fp2 = Fp[u]/(u^2 - beta);
      - the twist convention (D or M);
      - the optimal-ate loop parameter [|L|] (always positive; sign in [L_neg]);
      - the family-specific list of post-loop Frobenius corrections (Q1, nQ2, ...).

    Every concrete curve gets one [Definition <curve>_params : CurveParams := ...]
    in [PairingTheory/Curves/<curve>_params.v]. The bedrock2 [<curve>_Pairing.v]
    must NOT introduce any new literal constants outside this file: every
    Frobenius constant, every loop bit, every Q1/Q2 formula must be derivable
    from the [CurveParams] instance.

    The eventual L4 equivalence theorem
        [feval out = OptimalAte.run params P Q]
    is then trivially curve-generic because [params] is just a record value.

    NOTE: this file is structurally minimal — only the data, no algorithms,
    no instances of fiat-crypto's [FieldRepresentation], no bedrock2 imports.
    The purpose is to make the trusted boundary visible at one location and
    auditable in 100 lines. Algorithms live in [PairingTheory/Affine.v] etc.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.

Local Open Scope Z_scope.

(** Twist convention: BN curves are conventionally D-twist (E': y^2 = x^3 + b/xi),
    BLS12-381 is M-twist (E': y^2 = x^3 + b*xi). The choice changes both the
    twist isomorphism direction and the line-function basis layout. *)
Inductive TwistKind : Set :=
| Dtwist  (** y^2 = x^3 + b/xi *)
| Mtwist  (** y^2 = x^3 + b*xi *)
.

(** A single Frobenius correction step at the end of the optimal-ate Miller
    loop. [pi_power] is which power of the curve Frobenius is applied to Q,
    and [negate] is whether to negate after (BN curves use +pi(Q) and
    -pi^2(Q); BLS12 has none of these). The list lives in [optimal_ate_extras]
    below. *)
Record FrobCorrection : Set := {
  pi_power : nat;     (** 1 = pi_p,  2 = pi_p^2,  ... *)
  negate   : bool;    (** if [true], use -pi^k(Q) instead of pi^k(Q) *)
}.

(** The trusted core record. *)
Record CurveParams : Type := {
  (** Base field. *)
  prime_p : Z;
  (** Subgroup (scalar) order. *)
  scalar_r : Z;

  (** Weierstrass coefficients of E/Fp:  y^2 = x^3 + curve_a*x + curve_b. *)
  curve_a : Z;
  curve_b : Z;

  (** Embedding degree (k = 12 for BN, BLS12; k = 24 for BLS24; k = 6 for BW6). *)
  embedding_degree : nat;

  (** Quadratic nonresidue beta defining Fp2 = Fp[u]/(u^2 - beta).
      For BN254, BLS12-381 etc this is [-1] (so u^2 = -1). *)
  fp2_beta : Z;

  (** Cubic nonresidue [xi = xi_re + xi_im * u] in Fp2 defining
      Fp6 = Fp2[v]/(v^3 - xi). *)
  xi_re : Z;
  xi_im : Z;

  (** Twist convention. *)
  twist : TwistKind;

  (** Optimal-ate loop parameter. We store the absolute value
      [loop_abs] separately from the sign so the Miller loop body
      can iterate over [loop_abs] and the wrapper handles the
      conjugate-if-negative step. *)
  loop_abs : Z;
  loop_neg : bool;

  (** Frobenius corrections appended to the Miller loop output, in
      application order. For BN: [{| pi_power := 1; negate := false |};
      {| pi_power := 2; negate := true |}]. For BLS12: empty list. *)
  optimal_ate_extras : list FrobCorrection;
}.

(** A few smart constructors / helper lemmas. *)

Definition signed_loop (c : CurveParams) : Z :=
  if c.(loop_neg) then - c.(loop_abs) else c.(loop_abs).

Definition is_BN_family (c : CurveParams) : bool :=
  match c.(optimal_ate_extras) with
  | [] => false
  | _ :: _ => true
  end.

(** Sanity: the loop parameter is positive when given. *)
Definition loop_abs_positive (c : CurveParams) : Prop :=
  0 < c.(loop_abs).

(** A coarse well-formedness predicate. The full mathematical
    well-formedness (curve has [r]-torsion, embedding degree is correct,
    xi is a non-cube and non-square in Fp2, etc.) is left to per-curve
    proof obligations in the Curves/ subdirectory. *)
Record CurveParams_wf (c : CurveParams) : Prop := {
  wf_p_prime    : 2 < c.(prime_p);
  wf_r_positive : 0 < c.(scalar_r);
  wf_loop_pos   : loop_abs_positive c;
}.
