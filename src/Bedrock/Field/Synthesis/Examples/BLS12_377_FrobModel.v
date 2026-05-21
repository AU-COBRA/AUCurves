(** * BLS12-377 Frobenius — Gallina model.

    Defines the per-component Gallina Frobenius model on the BLS12-377
    tower:
      Fp   = F_p
      Fp2  = Fp[u]/(u^2 - beta)               (beta = -5 in BLS12-377)
      Fp6  = Fp2[v]/(v^3 - xi)                (xi = (0, 1) i.e. u)
      Fp12 = Fp6[w]/(w^2 - v)

    This file mirrors the [Local Definition fp12_frobenius_p2_model] in
    [Crypto.Bedrock.Field.FieldExtensions.PairingFieldOps], lifted to a
    non-local definition so the BLS12-377 DSD spec can reference it.

    Algebraic-correctness of the BLS12-377 [bls377_Fp12_frobenius_p2]
    body is established by the library lemma
    [PairingFieldOps.Fp12_frobenius_p2_ok], proved against the same
    Gallina model.  The model here is a re-export.

    NOTE: this model intentionally uses the AbstractField [Fmul]
    operations at each tower level, so the algebraic equation is
    typeclass-polymorphic over the chosen Fp2/Fp6 representation. *)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Local Open Scope Z_scope.

Section BLS12_377FrobModel.

  Variable p : positive.

  Local Notation Fp   := (F p).
  Local Notation Fp2  := (Fp * Fp)%type.
  Local Notation Fp6  := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  (* Model is parameterised over the tower multiplications and over
     fp6_mul_fp2 (multiply Fp6 by an Fp2 scalar). *)
  Variable fp2_mul     : Fp2  -> Fp2 -> Fp2.
  Variable fp6_mul_fp2 : Fp6  -> Fp2 -> Fp6.

  (* -------------------------------------------------------------- *)
  (* Fp2 conjugation                                                 *)
  (* -------------------------------------------------------------- *)

  Definition fp2_conj_gallina (x : Fp2) : Fp2 := (fst x, F.opp (snd x)).

  (* -------------------------------------------------------------- *)
  (* Fp6 Frobenius pi:                                               *)
  (*   (c0, c1, c2) ↦ (fp2_conj c0, gamma1 * fp2_conj c1, gamma2 * fp2_conj c2) *)
  (* -------------------------------------------------------------- *)

  Definition fp6_frobenius_gallina (gamma1 gamma2 : Fp2) (x : Fp6) : Fp6 :=
    let '(c0, c1, c2) := x in
    (fp2_conj_gallina c0,
     fp2_mul (fp2_conj_gallina c1) gamma1,
     fp2_mul (fp2_conj_gallina c2) gamma2).

  (* -------------------------------------------------------------- *)
  (* Fp6 Frobenius pi^2:                                             *)
  (*   (c0, c1, c2) ↦ (c0, gamma1_p2 * c1, gamma2_p2 * c2)            *)
  (*   (No inner Fp2-conjugation since p^2 acts trivially on Fp2.)  *)
  (* -------------------------------------------------------------- *)

  Definition fp6_frobenius_p2_gallina (gamma1_p2 gamma2_p2 : Fp2) (x : Fp6) : Fp6 :=
    let '(c0, c1, c2) := x in
    (c0, fp2_mul c1 gamma1_p2, fp2_mul c2 gamma2_p2).

  (* -------------------------------------------------------------- *)
  (* Fp12 Frobenius pi:                                              *)
  (*   (c0, c1) ↦ (fp6_frobenius c0, w_frob_c1 * fp6_frobenius c1)   *)
  (* -------------------------------------------------------------- *)

  Definition fp12_frobenius_gallina
    (gamma1 gamma2 : Fp2) (w_frob_c1 : Fp2) (x : Fp12) : Fp12 :=
    let c0 := fst x in let c1 := snd x in
    (fp6_frobenius_gallina gamma1 gamma2 c0,
     fp6_mul_fp2 (fp6_frobenius_gallina gamma1 gamma2 c1) w_frob_c1).

  (* -------------------------------------------------------------- *)
  (* Fp12 Frobenius pi^2:                                            *)
  (*   (c0, c1) ↦ (fp6_frobenius_p2 c0, w_frob_p2_c1 * fp6_frobenius_p2 c1) *)
  (* -------------------------------------------------------------- *)

  Definition fp12_frobenius_p2_gallina
    (gamma1_p2 gamma2_p2 : Fp2) (w_frob_p2_c1 : Fp2) (x : Fp12) : Fp12 :=
    let c0 := fst x in let c1 := snd x in
    (fp6_frobenius_p2_gallina gamma1_p2 gamma2_p2 c0,
     fp6_mul_fp2 (fp6_frobenius_p2_gallina gamma1_p2 gamma2_p2 c1) w_frob_p2_c1).

End BLS12_377FrobModel.

(* ================================================================== *)
(** * Sanity lemmas                                                    *)
(* ================================================================== *)

Section FrobModelLemmas.

  Variable p : positive.
  Local Notation Fp  := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.

  (** Fp2 conjugation is involutive. *)
  Lemma fp2_conj_involutive : forall (x : Fp2),
    fp2_conj_gallina p (fp2_conj_gallina p x) = (fst x, F.opp (F.opp (snd x))).
  Proof.
    intros [x0 x1]; cbn [fp2_conj_gallina fst snd]; reflexivity.
  Qed.

End FrobModelLemmas.
