(** * PairingSpecDefs: the optimal-ate pairing recipe, without the Miller-function model.

    The definitions of [PairingSpec.v] ([frobenius_Q], [frobenius2_Q], [apply_correction(s)],
    [final_exp_easy], [final_exp_hard], [final_exp], [optimal_ate]), moved here verbatim so that
    they can be imported without the [MillerFunctionModel] section of [PairingSpec.v] (whose
    [tate_bilinear_left] is [Admitted]).  [PairingSpec.v] re-exports this file.

    The definitions live in a module [PairingSpec], exported, so that both the unqualified names
    and the qualified names [PairingSpec.optimal_ate] etc. used by the importers of
    [PairingSpec.v] resolve as before.  See [PairingSpec.v] for the documentation of each
    definition.  No [Admitted], no [Axiom].
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Bool.Bool.

Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Module PairingSpec.

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

  (** The negated square Frobenius -pi_p^2(Q).
      For BN: pi^2(Q) = (Qx * gamma1_p2, Qy * gamma_y_p2)
      where gamma1_p2 = xi^{(p^2-1)/3}, gamma_y_p2 = xi^{(p^2-1)/2}.
      Since xi is a non-square in Fp2, xi^{(p^2-1)/2} = -1, so pi^2(Q) = (Qx * gamma1_p2, -Qy)
      and this function, which returns (Qx * gamma1_p2, Qy), computes -pi^2(Q), the point of
      the second optimal-ate correction line on BN curves.  The BN params therefore use
      [{| pi_power := 2; negate := false |}]; [negate := true] would give pi^2(Q). *)
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
      For BN254, BN256, BN446: [{pi=1, neg=false}, {pi=2, neg=false}]  →  Q1 = pi(Q), then
      [frobenius2_Q] = -pi^2(Q) (see above), i.e. the lines through pi(Q) and -pi^2(Q).
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

End PairingSpec.

Export PairingSpec.
