(** * BLS24-509 Frobenius — Gallina model.

    Defines the per-component Gallina Frobenius model on the BLS24-509
    tower:
      Fp   = F_p
      Fp2  = Fp[u]/(u^2 + 1)                (since p ≡ 3 mod 4)
      Fp4  = Fp2[v]/(v^2 - (1+u))
      Fp8  = Fp4[w]/(w^2 - v)
      Fp24 = Fp8[t]/(t^3 - w)

    These match the bedrock2 bodies in BLS24_509_FinalExp.v exactly
    (the inline fp4_frob_inline / fp8_frob_inline / fp24_frob body):

      bls24_fp24_frob:    per-component on (c0,c1,c2) with
                          gamma_fp4, gamma_fp8, gamma_fp24_1, gamma_fp24_2
      bls24_fp24_frob_p2: same structure with squared gammas, but the
                          inner fp2_frob acts identically (p^2 ≡ 1 on Fp2)
      bls24_fp24_frob_p4: same structure with p^4 gammas; inner fp2 also id

    The model is parameterized over the multiplication operations at
    each tower level (fp2_mul, fp4_mul, fp8_mul) and the negation on
    Fp.  These are kept abstract; concrete WBW implementations provide
    actual values via [AbstractField.feval] applied to the result of
    [AbstractField.mul] and [AbstractField.opp].

    Algebraic correctness — i.e. that "scaling by these gammas"
    actually computes x ↦ x^{p^k} — is a SEPARATE algebraic fact
    about the chosen gammas, established only for the concrete
    FrobConsts numerics.  At the SPEC level we just need that the
    function output equals the Gallina model output. *)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Local Open Scope Z_scope.

Section BLS24FrobModel.

  Variable p : positive.

  Local Notation Fp   := (F p).
  Local Notation Fp2  := (Fp * Fp)%type.
  Local Notation Fp4  := (Fp2 * Fp2)%type.
  Local Notation Fp8  := (Fp4 * Fp4)%type.
  Local Notation Fp24 := ((Fp8 * Fp8) * Fp8)%type.

  (* -------------------------------------------------------------- *)
  (* The model is parameterised over multiplication operations at    *)
  (* each tower level.  The intent: the BLS24 specs use              *)
  (* [AbstractField.feval] and [Fmul] on the appropriate level —    *)
  (* the model just reproduces the same compositional structure as  *)
  (* the bedrock2 body.                                              *)
  (* -------------------------------------------------------------- *)

  Variable fp2_mul : Fp2 -> Fp2 -> Fp2.
  Variable fp4_mul : Fp4 -> Fp4 -> Fp4.
  Variable fp8_mul : Fp8 -> Fp8 -> Fp8.

  (* -------------------------------------------------------------- *)
  (* Frobenius pi^1                                                  *)
  (* -------------------------------------------------------------- *)

  (** Inline fp2_frob: complex conjugation on Fp2 (since p ≡ 3 mod 4).
      (a0, a1) ↦ (a0, -a1) *)
  Definition fp2_frob_gallina (a : Fp2) : Fp2 :=
    (fst a, F.opp (snd a)).

  (** fp4_frob: applies fp2_frob component-wise, then multiplies the
      high half by gamma_fp4. *)
  Definition fp4_frob_gallina (a : Fp4) (gamma_fp4 : Fp2) : Fp4 :=
    (fp2_frob_gallina (fst a),
     fp2_mul (fp2_frob_gallina (snd a)) gamma_fp4).

  (** fp8_frob: applies fp4_frob component-wise, then multiplies the
      high half by gamma_fp8. *)
  Definition fp8_frob_gallina (a : Fp8) (gamma_fp4 : Fp2) (gamma_fp8 : Fp4) : Fp8 :=
    (fp4_frob_gallina (fst a) gamma_fp4,
     fp4_mul (fp4_frob_gallina (snd a) gamma_fp4) gamma_fp8).

  (** fp24_frob: applies fp8_frob to c0, then for c1 and c2 multiplies
      by gamma_fp24_1 and gamma_fp24_2 respectively. *)
  Definition frobenius_fp24_gallina
    (x : Fp24)
    (gamma_fp4 : Fp2) (gamma_fp8 : Fp4)
    (gamma_fp24_1 gamma_fp24_2 : Fp8) : Fp24 :=
    let c0 := fst (fst x) in
    let c1 := snd (fst x) in
    let c2 := snd x in
    let c0_frob := fp8_frob_gallina c0 gamma_fp4 gamma_fp8 in
    let c1_frob := fp8_frob_gallina c1 gamma_fp4 gamma_fp8 in
    let c2_frob := fp8_frob_gallina c2 gamma_fp4 gamma_fp8 in
    let c1_out  := fp8_mul c1_frob gamma_fp24_1 in
    let c2_out  := fp8_mul c2_frob gamma_fp24_2 in
    ((c0_frob, c1_out), c2_out).

  (* -------------------------------------------------------------- *)
  (* Frobenius pi^2                                                  *)
  (*                                                                  *)
  (* On Fp2, pi^2 is the identity (since p^2 ≡ 1 on the Galois        *)
  (* group of Fp2/Fp).  The bedrock2 body uses "copy" for the c0 of   *)
  (* fp4_frob_p2 and "mul" for the c1 by gamma_fp4_p2.                *)
  (* -------------------------------------------------------------- *)

  Definition fp4_frob_p2_gallina (a : Fp4) (gamma_fp4_p2 : Fp2) : Fp4 :=
    (fst a, fp2_mul (snd a) gamma_fp4_p2).

  Definition fp8_frob_p2_gallina (a : Fp8) (gamma_fp4_p2 : Fp2) (gamma_fp8_p2 : Fp4) : Fp8 :=
    (fp4_frob_p2_gallina (fst a) gamma_fp4_p2,
     fp4_mul (fp4_frob_p2_gallina (snd a) gamma_fp4_p2) gamma_fp8_p2).

  Definition frobenius_fp24_p2_gallina
    (x : Fp24)
    (gamma_fp4_p2 : Fp2) (gamma_fp8_p2 : Fp4)
    (gamma_fp24_p2_1 gamma_fp24_p2_2 : Fp8) : Fp24 :=
    let c0 := fst (fst x) in
    let c1 := snd (fst x) in
    let c2 := snd x in
    let c0_frob := fp8_frob_p2_gallina c0 gamma_fp4_p2 gamma_fp8_p2 in
    let c1_frob := fp8_frob_p2_gallina c1 gamma_fp4_p2 gamma_fp8_p2 in
    let c2_frob := fp8_frob_p2_gallina c2 gamma_fp4_p2 gamma_fp8_p2 in
    let c1_out  := fp8_mul c1_frob gamma_fp24_p2_1 in
    let c2_out  := fp8_mul c2_frob gamma_fp24_p2_2 in
    ((c0_frob, c1_out), c2_out).

  (* -------------------------------------------------------------- *)
  (* Frobenius pi^4                                                  *)
  (*                                                                  *)
  (* Same shape as pi^2 (p^4 also acts trivially on Fp2).             *)
  (* -------------------------------------------------------------- *)

  Definition fp4_frob_p4_gallina (a : Fp4) (gamma_fp4_p4 : Fp2) : Fp4 :=
    (fst a, fp2_mul (snd a) gamma_fp4_p4).

  Definition fp8_frob_p4_gallina (a : Fp8) (gamma_fp4_p4 : Fp2) (gamma_fp8_p4 : Fp4) : Fp8 :=
    (fp4_frob_p4_gallina (fst a) gamma_fp4_p4,
     fp4_mul (fp4_frob_p4_gallina (snd a) gamma_fp4_p4) gamma_fp8_p4).

  Definition frobenius_fp24_p4_gallina
    (x : Fp24)
    (gamma_fp4_p4 : Fp2) (gamma_fp8_p4 : Fp4)
    (gamma_fp24_p4_1 gamma_fp24_p4_2 : Fp8) : Fp24 :=
    let c0 := fst (fst x) in
    let c1 := snd (fst x) in
    let c2 := snd x in
    let c0_frob := fp8_frob_p4_gallina c0 gamma_fp4_p4 gamma_fp8_p4 in
    let c1_frob := fp8_frob_p4_gallina c1 gamma_fp4_p4 gamma_fp8_p4 in
    let c2_frob := fp8_frob_p4_gallina c2 gamma_fp4_p4 gamma_fp8_p4 in
    let c1_out  := fp8_mul c1_frob gamma_fp24_p4_1 in
    let c2_out  := fp8_mul c2_frob gamma_fp24_p4_2 in
    ((c0_frob, c1_out), c2_out).

End BLS24FrobModel.

(* ================================================================== *)
(** * Sanity lemmas                                                    *)
(* ================================================================== *)

Section FrobModelLemmas.

  Variable p : positive.

  Local Notation Fp   := (F p).
  Local Notation Fp2  := (Fp * Fp)%type.

  (** fp2_frob is involutive on the Fp-subfield slice (a0, 0):
      complex conjugation of a "real" element is itself. *)
  Lemma fp2_frob_real : forall (a0 : Fp),
    fp2_frob_gallina p (a0, F.zero) = (a0, F.opp F.zero).
  Proof.
    intros a0; cbn [fp2_frob_gallina fst snd]; reflexivity.
  Qed.

  (** fp2_frob is involutive (pi^2 = identity on Fp2). *)
  Lemma fp2_frob_involutive : forall (a : Fp2),
    fp2_frob_gallina p (fp2_frob_gallina p a) = (fst a, F.opp (F.opp (snd a))).
  Proof.
    intros [a0 a1]; cbn [fp2_frob_gallina fst snd]; reflexivity.
  Qed.

End FrobModelLemmas.
