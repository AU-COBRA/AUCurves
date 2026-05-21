(** * BW6-761 Frobenius — Gallina model.

    Defines the per-component Gallina Frobenius model on the BW6-761
    Fp6 = Fp3[w]/(w^2 - zeta), Fp3 = Fp[zeta]/(zeta^3 + 4) tower.
    These match the bedrock2 bodies in BW6_761_FinalExp.v exactly:

      bw6_fp6_frob:    per-component scaling by (alpha, alpha^2,
                       sa, sa*alpha, sa*alpha^2)
      bw6_fp6_frob_p2: per-component scaling by the SQUARES of the
                       above gammas
      bw6_fp6_frob_p3: copy c0; mul c1 components by -1 mod p

    The model is parameterized over the gamma SCALAR values (not the
    full Fp3 felems), so each spec can quantify over arbitrary
    pre-computed gammas; the FrobConsts file pins those down to the
    concrete BW6-761 numerics.

    Algebraic correctness — i.e. that "scaling by these gammas"
    actually computes [x -> x^p] — is a SEPARATE algebraic fact
    about the chosen gammas, established only for the concrete
    FrobConsts numerics.  At the SPEC level we just need that the
    function output equals the Gallina model output.

    Naming convention:
      [frobenius_fp6_gallina x gfp3 gfp6] takes
        - [x   : Fp6] the input
        - [gfp3 : Fp3] the Fp3 blob holding (_, alpha, alpha^2)
                       (the 0th slot is unused; we model it as the
                       Fp value of the 0th slot but ignore in the
                       computation)
        - [gfp6 : Fp3] the Fp3 blob holding (sa, sa*alpha, sa*alpha^2)
      and returns the new Fp6 value computed component-wise.
*)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Local Open Scope Z_scope.

Section BW6FrobModel.

  Variable p : positive.

  Local Notation Fp  := (F p).
  Local Notation Fp3 := ((Fp * Fp) * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  (* -------------------------------------------------------------- *)
  (* Selectors                                                      *)
  (* -------------------------------------------------------------- *)

  Definition fp3_a0 (a : Fp3) : Fp := fst (fst a).
  Definition fp3_a1 (a : Fp3) : Fp := snd (fst a).
  Definition fp3_a2 (a : Fp3) : Fp := snd a.

  Definition fp3_mk (a0 a1 a2 : Fp) : Fp3 := ((a0, a1), a2).

  Definition fp6_c0 (x : Fp6) : Fp3 := fst x.
  Definition fp6_c1 (x : Fp6) : Fp3 := snd x.

  Definition fp6_mk (c0 c1 : Fp3) : Fp6 := (c0, c1).

  (* -------------------------------------------------------------- *)
  (* Frobenius pi (degree 1)                                         *)
  (*                                                                 *)
  (* gfp3 holds (_, alpha, alpha^2):                                 *)
  (*   out.c0 = (a0, a1 * gfp3.c1, a2 * gfp3.c2)                     *)
  (* gfp6 holds (sa, sa*alpha, sa*alpha^2):                          *)
  (*   out.c1 = (b0 * gfp6.c0, b1 * gfp6.c1, b2 * gfp6.c2)           *)
  (* -------------------------------------------------------------- *)

  Definition frobenius_fp3_c0_gallina (a : Fp3) (g : Fp3) : Fp3 :=
    fp3_mk (fp3_a0 a)
           (F.mul (fp3_a1 a) (fp3_a1 g))
           (F.mul (fp3_a2 a) (fp3_a2 g)).

  Definition frobenius_fp3_c1_gallina (b : Fp3) (g : Fp3) : Fp3 :=
    fp3_mk (F.mul (fp3_a0 b) (fp3_a0 g))
           (F.mul (fp3_a1 b) (fp3_a1 g))
           (F.mul (fp3_a2 b) (fp3_a2 g)).

  Definition frobenius_fp6_gallina (x : Fp6) (gfp3 gfp6 : Fp3) : Fp6 :=
    fp6_mk (frobenius_fp3_c0_gallina (fp6_c0 x) gfp3)
           (frobenius_fp3_c1_gallina (fp6_c1 x) gfp6).

  (* -------------------------------------------------------------- *)
  (* Frobenius pi^2 — same shape; the caller passes squared gammas. *)
  (* -------------------------------------------------------------- *)

  Definition frobenius_fp6_p2_gallina (x : Fp6) (gfp3_p2 gfp6_p2 : Fp3) : Fp6 :=
    frobenius_fp6_gallina x gfp3_p2 gfp6_p2.

  (* -------------------------------------------------------------- *)
  (* Frobenius pi^3                                                  *)
  (*                                                                 *)
  (* pi^3 acts trivially on Fp3, then pi^3(w) = -w in Fp6.            *)
  (* The bedrock2 body uses [gamma_fp6_p3.c0 = -1 mod p] and          *)
  (* multiplies each Fp slot of c1 by that single scalar.             *)
  (* Other slots of [gamma_fp6_p3] are ignored, so we model with      *)
  (* a SINGLE Fp parameter [g] (= gamma_fp6_p3.c0).                   *)
  (* -------------------------------------------------------------- *)

  Definition frobenius_fp6_p3_gallina (x : Fp6) (g : Fp) : Fp6 :=
    let c1 := fp6_c1 x in
    fp6_mk (fp6_c0 x)
           (fp3_mk (F.mul (fp3_a0 c1) g)
                   (F.mul (fp3_a1 c1) g)
                   (F.mul (fp3_a2 c1) g)).

End BW6FrobModel.

(* ================================================================== *)
(** * Sanity lemmas                                                    *)
(* ================================================================== *)

Section FrobModelLemmas.

  Variable p : positive.

  Local Notation Fp  := (F p).
  Local Notation Fp3 := ((Fp * Fp) * Fp)%type.

  (** [frobenius_fp6_p2_gallina] is definitionally [frobenius_fp6_gallina]. *)
  Lemma frobenius_fp6_p2_unfold : forall x gfp3_p2 gfp6_p2,
    frobenius_fp6_p2_gallina p x gfp3_p2 gfp6_p2 =
    frobenius_fp6_gallina p x gfp3_p2 gfp6_p2.
  Proof. reflexivity. Qed.

  (** Pi^3 with g = -1 (mod p): c1 ↦ -c1, c0 unchanged. *)
  Lemma frobenius_fp6_p3_neg1 : forall (c0 c1 : Fp3),
    let g_neg1 : Fp := F.opp (@F.one p) in
    frobenius_fp6_p3_gallina p (c0, c1) g_neg1 =
    (c0, ((F.mul (fp3_a0 p c1) g_neg1,
           F.mul (fp3_a1 p c1) g_neg1),
          F.mul (fp3_a2 p c1) g_neg1)).
  Proof.
    intros c0 c1; cbn; reflexivity.
  Qed.

End FrobModelLemmas.
