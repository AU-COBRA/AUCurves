(** * Algebraic correctness specifications for BLS12 pairing.

    Defines the target theorems connecting bedrock2 implementations
    to the Gallina pairing model in Theory.BLS12Pairing.Pairing.

    These are SPECIFICATIONS ONLY — no proofs yet.

    Post-Section signatures (from About):
      miller_loop p P Q
      final_exponentiation p gamma1_p2 gamma2_p2 coeff_p2_c1 f
      final_exponentiation_dsd p g1 g2 g1p2 g2p2 cc1 cp2c1 f
      pairing p gamma1_p2 gamma2_p2 coeff_p2_c1 P Q
*)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Theory.BLS12Pairing.Pairing.

Local Open Scope Z_scope.

Section Correctness.

  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := ((Fp * Fp)%type).
  Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
  Local Notation Fp12 := ((Fp6 * Fp6)%type).

  (* ================================================================ *)
  (** ** Fp2 feval correctness                                        *)
  (* ================================================================ *)

  (** Each Fp2 operation's feval equation.
      These follow from Fp-level synthesis + algebraic identity. *)

  Definition Fp2_mul_feval (feval : Fp2 -> Fp2) (result a b : Fp2) : Prop :=
    feval result = fp2_mul p (feval a) (feval b).

  Definition Fp2_add_feval (feval : Fp2 -> Fp2) (result a b : Fp2) : Prop :=
    feval result = fp2_add p (feval a) (feval b).

  Definition Fp2_sub_feval (feval : Fp2 -> Fp2) (result a b : Fp2) : Prop :=
    feval result = fp2_sub p (feval a) (feval b).

  Definition Fp2_sqr_feval (feval : Fp2 -> Fp2) (result a : Fp2) : Prop :=
    feval result = fp2_sqr p (feval a).

  Definition Fp2_inv_feval (feval : Fp2 -> Fp2) (result a : Fp2) : Prop :=
    feval result = fp2_inv p (feval a).

  Definition Fp2_conjugate_feval (feval : Fp2 -> Fp2) (result a : Fp2) : Prop :=
    feval result = fp2_conjugate p (feval a).

  Definition Fp2_mul_xi_feval (feval : Fp2 -> Fp2) (result a : Fp2) : Prop :=
    feval result = fp2_mul_xi p (feval a).

  (* ================================================================ *)
  (** ** Fp12 feval correctness                                       *)
  (* ================================================================ *)

  Definition Fp12_mul_feval (feval : Fp12 -> Fp12) (result a b : Fp12) : Prop :=
    feval result = fp12_mul p (feval a) (feval b).

  Definition Fp12_sqr_feval (feval : Fp12 -> Fp12) (result a : Fp12) : Prop :=
    feval result = fp12_sqr p (feval a).

  Definition Fp12_conjugate_feval (feval : Fp12 -> Fp12) (result a : Fp12) : Prop :=
    feval result = fp12_conjugate p (feval a).

  (* ================================================================ *)
  (** ** Miller loop correctness                                      *)
  (* ================================================================ *)

  (** The loop output equals the Gallina miller_loop. *)
  Definition miller_loop_correct (result : Fp12)
    (px py : Fp) (qx qy : Fp2) : Prop :=
    result = miller_loop p
      (mk_g1_affine p px py false)
      (mk_g2_affine p qx qy false).

  (* ================================================================ *)
  (** ** Final exponentiation correctness                             *)
  (* ================================================================ *)

  Variable gamma1_p2 gamma2_p2 coeff_p2_c1 : Fp2.

  Definition final_exp_correct (result input : Fp12) : Prop :=
    result = final_exponentiation p gamma1_p2 gamma2_p2 coeff_p2_c1 input.

  (* DSD variant uses all 6 Frobenius constants *)
  Variable gamma1 gamma2 coeff_c1 : Fp2.

  Definition final_exp_dsd_correct (result input : Fp12) : Prop :=
    result = final_exponentiation_dsd p
      gamma1 gamma2 gamma1_p2 gamma2_p2 coeff_c1 coeff_p2_c1 input.

  (* ================================================================ *)
  (** ** Top-level pairing correctness                                *)
  (* ================================================================ *)

  Definition pairing_correct (result : Fp12)
    (px py : Fp) (qx qy : Fp2) : Prop :=
    result = pairing p gamma1_p2 gamma2_p2 coeff_p2_c1
      (mk_g1_affine p px py false)
      (mk_g2_affine p qx qy false).

  (* ================================================================ *)
  (** ** Strengthened WP specs (combining memory + feval)              *)
  (* ================================================================ *)

  (** The strengthened spec for miller_loop adds feval to the postcondition:

      ensures tr' mem' :=
        tr = tr' /\ exists out,
          Fp12_bounded Fp12_loose out /\
          miller_loop_correct (feval_fp12 out) (feval_fp px) (feval_fp py)
                              (feval_fp2 qx) (feval_fp2 qy) /\
          (FElem_Fp12 pout out ⋆ ...) mem'

      This is strictly stronger than the current black-box spec. *)

End Correctness.
