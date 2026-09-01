(** * Final exponentiation and pairing feval correctness.
 *
 *  Proves that the bedrock2 final exponentiation (using Fp12.v operations)
 *  equals the Pairing.v Gallina model, and composes with the Miller loop
 *  bridge to get a top-level pairing correctness theorem.
 *
 *  Proof strategy:
 *    - For each Fp12 operation (conjugate, inv, mul, frobenius_p2),
 *      the Fp12Feval bridge gives Fp12.op = Pairing.op.
 *    - For fp12_pow_bits_aux (binary exponentiation), we prove by induction
 *      on the bit list that substituting the bridged sqr/mul gives the same
 *      result.
 *    - The final exponentiation is a straight-line composition; rewrite
 *      each step via the bridge.
 *    - The top-level pairing = final_exp . miller_loop follows by
 *      composing the two theorems.
 *
 *  Performance notes:
 *    - All Fp6/Fp12/Pairing-level operations are Local Opaque.
 *    - h3_exp, h3_width, Z_to_bits, final_exponentiation, pairing, and
 *      miller_loop are all opaque to prevent the 1268-bit exponent from
 *      exploding during reflexivity/Qed.
 *    - The pow_bits_aux_feval induction proof uses abstract to keep Qed fast.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp6.
Require Import Theory.BLS12Pairing.Fp12.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Fp12Feval.

Local Open Scope Z_scope.

(* Prevent term explosion by making Fp6-level operations opaque. *)
Local Opaque Fp6.fp6_add Fp6.fp6_sub Fp6.fp6_neg Fp6.fp6_mul
  Fp6.fp6_sqr Fp6.fp6_mul_by_v Fp6.fp6_inv Fp6.fp6_mul_fp2
  Fp6.fp6_frobenius Fp6.fp6_frobenius_p2.
Local Opaque Pairing.fp6_add Pairing.fp6_sub Pairing.fp6_neg Pairing.fp6_mul
  Pairing.fp6_sqr Pairing.fp6_mul_by_v Pairing.fp6_inv Pairing.fp6_mul_fp2
  Pairing.fp6_frobenius Pairing.fp6_frobenius_p2.

(* Also make Fp12-level operations opaque to control rewriting. *)
Local Opaque Fp12.fp12_mul Fp12.fp12_sqr Fp12.fp12_add Fp12.fp12_sub
  Fp12.fp12_neg Fp12.fp12_conjugate Fp12.fp12_inv
  Fp12.fp12_frobenius Fp12.fp12_frobenius_p2.
Local Opaque Pairing.fp12_mul Pairing.fp12_sqr Pairing.fp12_add
  Pairing.fp12_sub Pairing.fp12_neg Pairing.fp12_conjugate Pairing.fp12_inv
  Pairing.fp12_frobenius Pairing.fp12_frobenius_p2.

(* Keep the 63-element bit list opaque to prevent proof term explosion
   during the pairing composition. *)
Local Opaque Pairing.bls_x_bits.

(* Make the 1268-bit exponent and bit-conversion opaque to prevent
   reflexivity/Qed from expanding them. The proofs that need to unfold
   fp12_pow_Z/final_exponentiation do so explicitly before these are
   sealed by the section's local opaque declarations below. *)
Local Opaque Pairing.h3_exp Pairing.h3_width Pairing.Z_to_bits.

(* ================================================================ *)
(** ** Complete pairing feval: final exp + miller loop bridge        *)
(* ================================================================ *)

Section PairingFeval.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6' := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12' := (Fp6' * Fp6')%type.

  Let beta : Fp := F.of_Z p (-1).
  Let xi_re : Fp := @F.one p.
  Let xi_im : Fp := @F.one p.

  (* Frobenius constants for frobenius_p2 *)
  Variable fg1_p2 fg2_p2 : Fp2.
  Variable w_frob_p2_c1 : Fp2.

  (* Fp6 bridge hypotheses *)
  Hypothesis fp6_add_bridge : forall a b : Fp6',
    Fp6.fp6_add p a b = Pairing.fp6_add p a b.
  Hypothesis fp6_sub_bridge : forall a b : Fp6',
    Fp6.fp6_sub p a b = Pairing.fp6_sub p a b.
  Hypothesis fp6_neg_bridge : forall a : Fp6',
    Fp6.fp6_neg p a = Pairing.fp6_neg p a.
  Hypothesis fp6_mul_bridge : forall a b : Fp6',
    Fp6.fp6_mul p beta xi_re xi_im a b = Pairing.fp6_mul p a b.
  Hypothesis fp6_mul_by_v_bridge : forall a : Fp6',
    Fp6.fp6_mul_by_v p beta xi_re xi_im a = Pairing.fp6_mul_by_v p a.
  Hypothesis fp6_sqr_bridge : forall a : Fp6',
    Fp6.fp6_sqr p beta xi_re xi_im a = Pairing.fp6_sqr p a.
  Hypothesis pairing_fp6_mul_self_bridge : forall a : Fp6',
    Pairing.fp6_mul p a a = Pairing.fp6_sqr p a.
  Hypothesis fp6_karatsuba_cross_bridge : forall a b : Fp6',
    Pairing.fp6_sub p
      (Pairing.fp6_sub p
        (Pairing.fp6_mul p (Pairing.fp6_add p a b) (Pairing.fp6_add p a b))
        (Pairing.fp6_mul p a a))
      (Pairing.fp6_mul p b b) =
    Pairing.fp6_add p (Pairing.fp6_mul p a b) (Pairing.fp6_mul p a b).
  Hypothesis fp6_frobenius_p2_bridge : forall a : Fp6',
    Fp6.fp6_frobenius_p2 p beta fg1_p2 fg2_p2 a =
    Pairing.fp6_frobenius_p2 p fg1_p2 fg2_p2 a.
  Hypothesis fp6_mul_fp2_bridge : forall (a : Fp6') (s : Fp2),
    Fp6.fp6_mul_fp2 p beta a s = Pairing.fp6_mul_fp2 p a s.
  Hypothesis fp6_inv_bridge : forall a : Fp6',
    Fp6.fp6_inv p beta xi_re xi_im a = Pairing.fp6_inv p a.

  (* ================================================================ *)
  (** ** Derived Fp12 bridge lemmas                                    *)
  (* ================================================================ *)

  Local Lemma sqr_eq : forall a : Fp12',
    Fp12.fp12_sqr p beta xi_re xi_im a = Pairing.fp12_sqr p a.
  Proof. apply fp12_sqr_eq; assumption. Qed.

  Local Lemma mul_eq : forall a b : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im a b = Pairing.fp12_mul p a b.
  Proof. apply fp12_mul_eq; assumption. Qed.

  Local Lemma conjugate_eq : forall a : Fp12',
    Fp12.fp12_conjugate p a = Pairing.fp12_conjugate p a.
  Proof. apply fp12_conjugate_eq; assumption. Qed.

  Local Lemma inv_eq : forall a : Fp12',
    Fp12.fp12_inv p beta xi_re xi_im a = Pairing.fp12_inv p a.
  Proof. apply fp12_inv_eq; assumption. Qed.

  Local Lemma frobenius_p2_eq' : forall a : Fp12',
    Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 a =
    Pairing.fp12_frobenius_p2 p fg1_p2 fg2_p2 w_frob_p2_c1 a.
  Proof. apply fp12_frobenius_p2_eq; assumption. Qed.

  (* ================================================================ *)
  (** ** Part 1: Binary exponentiation feval                          *)
  (* ================================================================ *)

  (** Bedrock2 version of fp12_pow_bits_aux: uses Fp12.v sqr and mul. *)
  Fixpoint bedrock2_pow_bits_aux (base : Fp12') (bits : list bool)
    (acc : Fp12') (started : bool) : Fp12' :=
    match bits with
    | [] => acc
    | b :: rest =>
      let acc' := if started then Fp12.fp12_sqr p beta xi_re xi_im acc
                  else acc in
      if b then
        let acc'' := if started
                     then Fp12.fp12_mul p beta xi_re xi_im acc' base
                     else base in
        bedrock2_pow_bits_aux base rest acc'' true
      else
        bedrock2_pow_bits_aux base rest acc' started
    end.

  (** The bedrock2 pow_bits_aux equals the Pairing.v version.
      Use abstract to hide each inductive step from Qed. *)
  Lemma pow_bits_aux_feval : forall bits base acc started,
    bedrock2_pow_bits_aux base bits acc started =
    Pairing.fp12_pow_bits_aux p base bits acc started.
  Proof.
    induction bits as [|b bs IH]; intros base acc started.
    - abstract reflexivity.
    - simpl bedrock2_pow_bits_aux. simpl Pairing.fp12_pow_bits_aux.
      rewrite sqr_eq, mul_eq. destruct b; apply IH.
  Qed.

  Definition bedrock2_pow_Z (base : Fp12') (exp : Z) (width : nat) : Fp12' :=
    bedrock2_pow_bits_aux base (Pairing.Z_to_bits width exp)
      (Fp12.fp12_one p) false.

  Lemma pow_Z_feval : forall base exp width,
    bedrock2_pow_Z base exp width = Pairing.fp12_pow_Z p base exp width.
  Proof.
    intros. unfold bedrock2_pow_Z, Pairing.fp12_pow_Z, Pairing.fp12_pow_bits.
    f_equal. apply pow_bits_aux_feval.
  Qed.

  (* ================================================================ *)
  (** ** Part 2: Final exponentiation feval                           *)
  (* ================================================================ *)

  (** Bedrock2 final exponentiation: uses Fp12.v operations. *)
  Definition bedrock2_final_exp (f : Fp12') : Fp12' :=
    let f_conj := Fp12.fp12_conjugate p f in
    let f_inv := Fp12.fp12_inv p beta xi_re xi_im f in
    let result := Fp12.fp12_mul p beta xi_re xi_im f_conj f_inv in
    let result_p2 := Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2
                       w_frob_p2_c1 result in
    let result' := Fp12.fp12_mul p beta xi_re xi_im result_p2 result in
    bedrock2_pow_Z result' Pairing.h3_exp Pairing.h3_width.

  Theorem final_exp_feval_correct : forall f : Fp12',
    bedrock2_final_exp f =
    Pairing.final_exponentiation p fg1_p2 fg2_p2 w_frob_p2_c1 f.
  Proof.
    intro f.
    unfold bedrock2_final_exp, Pairing.final_exponentiation.
    rewrite conjugate_eq, inv_eq, mul_eq.
    rewrite frobenius_p2_eq', mul_eq.
    apply pow_Z_feval.
  Qed.

  (* ================================================================ *)
  (** ** Part 3: Miller loop bridge (bedrock2 fold = Pairing.miller_loop) *)
  (* ================================================================ *)

  Lemma bedrock2_miller_loop_eq :
    forall (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      fst (fold_left
        (bedrock2_miller_step p
           (Pairing.g2_x p Q) (Pairing.g2_y p Q)
           (Pairing.g1_x p P) (Pairing.g1_y p P))
        Pairing.bls_x_bits
        (Fp12.fp12_one p, (Pairing.g2_x p Q, Pairing.g2_y p Q))) =
      Pairing.miller_loop p P Q.
  Proof.
    intros P Q Hp Hq.
    unfold Pairing.miller_loop.
    rewrite Hp, Hq. simpl orb.
    apply (miller_loop_feval_correct p); assumption.
  Qed.

  (* ================================================================ *)
  (** ** Part 4: Top-level pairing feval                              *)
  (* ================================================================ *)

  (** Bedrock2 pairing: miller loop + final exponentiation. *)
  Definition bedrock2_pairing (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p)
    : Fp12' :=
    let f := fst (fold_left
      (bedrock2_miller_step p
         (Pairing.g2_x p Q) (Pairing.g2_y p Q)
         (Pairing.g1_x p P) (Pairing.g1_y p P))
      Pairing.bls_x_bits
      (Fp12.fp12_one p, (Pairing.g2_x p Q, Pairing.g2_y p Q))) in
    bedrock2_final_exp f.

  Theorem pairing_feval_correct :
    forall (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      bedrock2_pairing P Q =
      Pairing.pairing p fg1_p2 fg2_p2 w_frob_p2_c1 P Q.
  Proof.
    intros P Q Hp Hq.
    unfold bedrock2_pairing, Pairing.pairing.
    rewrite final_exp_feval_correct.
    f_equal.
    apply bedrock2_miller_loop_eq; assumption.
  Qed.

End PairingFeval.
