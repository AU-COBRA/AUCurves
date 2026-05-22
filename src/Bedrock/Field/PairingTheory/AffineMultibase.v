(** * AffineMultibase.v — Gallina reference model for BW6-761's 5-symbol
    optimal-ate Miller loop.

    BW6-761 (Brezing-Weng, k=6) has embedding degree 6 and uses an
    *optimal-ate* Miller loop with a non-trivial 2-NAF scalar split:

         a₀ + λ a₁

    where each per-iteration digit

         j_i = L1[i] * 3 + L0[i]   ∈ {-3, -1, 0, 1, 3}

    is dispatched over a 5-symbol alphabet (cases ±4, ±2 do not occur,
    given the static [LoopCounter]/[LoopCounter1] tables in gnark).
    See gnark-crypto's `ecc/bw6-761/pairing.go` (function `MillerLoop`).

    The digit-3 / digit-(-3) accumulation needs an extra "pre-computed"
    G2 point — gnark uses ±φ(Q) (the GLV image obtained by multiplying
    Qx by `thirdRootOneG1`).  For this abstract Gallina model the extra
    point is left as a parameter (caller passes the BW6-specific
    precomputed point), so the model is reusable for any 5-symbol
    optimal-ate construction.

    This is Step 1 of Phase 2: pure Gallina + Qed lemmas, no bedrock2.
    It mirrors the structure of [Affine.v]'s binary [affine_miller_aux]
    but generalises the per-iteration switch from {0,1} to {-3,-1,0,1,3}.

    Final adjustment.  After the main loop, gnark runs i=0 separately
    with j = -3 using `lineCompute` (line-only, no point addition,
    since the next iteration would discard the new T anyway).  We model
    this with [affine_miller_5symbol_final_adjustment].

    Top-level: [affine_miller_optimal_ate] = main loop ∘ final adjust.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Bedrock.Field.PairingTheory.Affine.

Local Open Scope Z_scope.

Section AffineMultibase.

  Context {Fp Fp2 Fp12 : Type}.
  Context (ops : FieldOps Fp Fp2 Fp12).

  Local Notation "x +2 y" := (fp2_add  ops x y) (at level 50).
  Local Notation "x -2 y" := (fp2_sub  ops x y) (at level 50).
  Local Notation "x *2 y" := (fp2_mul  ops x y) (at level 40).
  Local Notation "/2 x"   := (fp2_inv  ops x)   (at level 35).

  (** ** Per-iteration step alias: line-only (no point update).

      Used by the BW6 final adjustment: at i=0 we evaluate the line
      through T at ±φ(Q) but do not commit the point addition because
      no further iteration consumes T.  Reuses [affine_chord_slope]
      and [make_line]. *)
  Definition line_only_step
      (f : Fp12) (Tx Ty Qx Qy : Fp2) (Px Py : Fp) : Fp12 :=
    let lam := affine_chord_slope ops Tx Ty Qx Qy in
    let line := make_line ops lam Tx Ty Px Py in
    fp12_mul ops f line.

  (** ** 5-symbol dispatcher.

      Given a digit [j ∈ {-3,-1,0,1,3}] and a quadruple of precomputed
      G2 points (Q, -Q, φQ, -φQ for BW6, but kept abstract here):
        j =  0 : doubling only (no addition)
        j = +1 : double + add Q
        j = -1 : double + add (-Q)
        j = +3 : double + add φ(Q)
        j = -3 : double + add (-φ(Q))
      Any other [j] falls through to the [j=0] case (treated as a no-op
      add), matching gnark's static guarantee that ±4, ±2 do not occur.

      Returns the iteration's (f', T'x, T'y). *)
  Definition multibase_iter_step
      (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
      (Px Py : Fp)
      (j : Z) (f : Fp12) (Tx Ty : Fp2)
    : Fp12 * Fp2 * Fp2 :=
    let '(f1, Tx1, Ty1) := double_step ops f Tx Ty Px Py in
    match j with
    | 0  => (f1, Tx1, Ty1)
    | 1  => add_step ops f1 Tx1 Ty1 Qx Qy Px Py
    | -1 => add_step ops f1 Tx1 Ty1 QxNeg QyNeg Px Py
    | 3  => add_step ops f1 Tx1 Ty1 PhiQx PhiQy Px Py
    | -3 => add_step ops f1 Tx1 Ty1 PhiQxNeg PhiQyNeg Px Py
    | _  => (f1, Tx1, Ty1)   (* unreachable for valid BW6 alphabet *)
    end.

  (** ** Main 5-symbol Miller loop body.

      Processes indices [i-1], [i-2], …, [0] of the alphabet
      [alphabet : nat -> Z].  Mirrors [affine_miller_aux] but with a
      5-symbol switch.

      Loop invariant (informal): after [n - i] iterations,
        f  = ∏_{k=n-1..i} l_{j_k}(P) · square accumulation
        T  = (∑_{k≥i} j_k 2^?) Q                         *)
  Fixpoint affine_miller_5symbol_aux
      (alphabet : nat -> Z) (i : nat)
      (Px Py : Fp) (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
      (f : Fp12) (Tx Ty : Fp2)
    : Fp12 * Fp2 * Fp2 :=
    match i with
    | O => (f, Tx, Ty)
    | S i' =>
      let '(f', Tx', Ty') :=
        multibase_iter_step
          Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
          Px Py
          (alphabet i') f Tx Ty
      in
      affine_miller_5symbol_aux alphabet i' Px Py
        Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
        f' Tx' Ty'
    end.

  (** ** Main-loop entry point.

      Initialised with [f := 1] and [T := Q]; the topmost digit is
      consumed by that initialisation.  [n_iters] is the number of
      digits to process — for BW6-761 this is 188 (i.e. the loop runs
      i = 187, …, 1 in gnark's notation, then a final-adjust step for
      i = 0). *)
  Definition affine_miller_5symbol
      (n_iters : nat) (alphabet : nat -> Z)
      (Px Py : Fp) (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
    : Fp12 * Fp2 * Fp2 :=
    affine_miller_5symbol_aux
      alphabet n_iters Px Py
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      (fp12_one ops) Qx Qy.

  (** ** Final-adjustment step (BW6-specific).

      At i = 0 gnark runs:
        - one [doubleStep]
        - one [lineCompute] through T and (-φQ)
        - combines the two lines via [Mul014By014] + [MulBy01245]
      Importantly NO point addition is committed (T is dropped).

      We model this as: double the running [f] and absorb both lines.
      The exact basis-level multiplication choice (`MulBy014` vs
      `Mul014By014` + `MulBy01245`) is a Fp12-mul optimisation that does
      not affect the value, so we just use [fp12_mul] twice. *)
  Definition affine_miller_5symbol_final_adjustment
      (f : Fp12) (Tx Ty : Fp2)
      (Px Py : Fp)
      (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
    : Fp12 :=
    let '(f1, Tx1, Ty1) := double_step ops f Tx Ty Px Py in
    (* For j = -3 at i=0: line through T1 at -φQ, no point update. *)
    line_only_step f1 Tx1 Ty1 PhiQxNeg PhiQyNeg Px Py.

  (** ** Top-level: main loop ∘ final adjustment.

      [n_iters] is the number of "switch" iterations (187 for BW6-761);
      the final-adjust step handles the i=0 iteration separately. *)
  Definition affine_miller_optimal_ate
      (n_iters : nat) (alphabet : nat -> Z)
      (Px Py : Fp) (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
    : Fp12 :=
    let '(f, Tx, Ty) :=
      affine_miller_5symbol n_iters alphabet Px Py
        Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
    in
    affine_miller_5symbol_final_adjustment
      f Tx Ty Px Py
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg.

End AffineMultibase.

(** ** Sanity lemmas (alphabet correctness + dispatcher behaviour). *)

(** Helper: the digit assembly [L1 * 3 + L0] over the trit alphabet
    [{-1,0,1}], with the sparseness constraint [L1 = 0 \/ L0 = 0]
    (i.e. at most one of the two trits is non-zero in any iteration),
    lands in the 5-symbol alphabet [{-3,-1,0,1,3}].

    This sparseness is exactly the static invariant maintained by
    gnark's [LoopCounter]/[LoopCounter1] tables, which ensures the
    cases ±4 and ±2 never arise (see the `default: return errors` arm
    in `MillerLoop`). *)
Lemma alphabet_in_range :
  forall (l1 l0 : Z),
    (l1 = -1 \/ l1 = 0 \/ l1 = 1) ->
    (l0 = -1 \/ l0 = 0 \/ l0 = 1) ->
    (l1 = 0 \/ l0 = 0) ->
    let j := l1 * 3 + l0 in
    j = -3 \/ j = -1 \/ j = 0 \/ j = 1 \/ j = 3.
Proof.
  intros l1 l0 Hl1 Hl0 Hsparse; cbv zeta.
  destruct Hsparse as [-> | ->].
  - (* l1 = 0 *)
    destruct Hl0 as [-> | [-> | ->]]; cbn; auto.
  - (* l0 = 0 *)
    destruct Hl1 as [-> | [-> | ->]]; cbn; auto.
Qed.

(** Helper: under the same sparseness constraint, the cases ±4 and ±2
    cannot arise. *)
Lemma alphabet_excludes_even :
  forall (l1 l0 : Z),
    (l1 = -1 \/ l1 = 0 \/ l1 = 1) ->
    (l0 = -1 \/ l0 = 0 \/ l0 = 1) ->
    (l1 = 0 \/ l0 = 0) ->
    let j := l1 * 3 + l0 in
    j <> -4 /\ j <> -2 /\ j <> 2 /\ j <> 4.
Proof.
  intros l1 l0 Hl1 Hl0 Hsparse; cbv zeta.
  destruct Hsparse as [-> | ->].
  - destruct Hl0 as [-> | [-> | ->]]; cbn; repeat split; discriminate.
  - destruct Hl1 as [-> | [-> | ->]]; cbn; repeat split; discriminate.
Qed.

(** Dispatcher consistency: at [j = 0] the dispatcher is precisely the
    bare doubling step.  This is the lemma that nails down the "no
    addition" semantics of the zero digit (and proves it definitionally
    — no symbolic evaluation needed). *)
Lemma multibase_iter_step_j0 :
  forall {Fp Fp2 Fp12} (ops : FieldOps Fp Fp2 Fp12)
         (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
         (Px Py : Fp) (f : Fp12) (Tx Ty : Fp2),
    multibase_iter_step ops
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      Px Py 0 f Tx Ty
    = double_step ops f Tx Ty Px Py.
Proof.
  intros; cbv [multibase_iter_step].
  destruct (double_step ops f Tx Ty Px Py) as [[? ?] ?]; reflexivity.
Qed.

(** Dispatcher consistency at [j = 1]: doubling then adding [Q]. *)
Lemma multibase_iter_step_j1 :
  forall {Fp Fp2 Fp12} (ops : FieldOps Fp Fp2 Fp12)
         (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
         (Px Py : Fp) (f : Fp12) (Tx Ty : Fp2),
    multibase_iter_step ops
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      Px Py 1 f Tx Ty
    = let '(f1, Tx1, Ty1) := double_step ops f Tx Ty Px Py in
      add_step ops f1 Tx1 Ty1 Qx Qy Px Py.
Proof. reflexivity. Qed.

(** Dispatcher consistency at [j = -1]: doubling then adding [-Q]. *)
Lemma multibase_iter_step_jm1 :
  forall {Fp Fp2 Fp12} (ops : FieldOps Fp Fp2 Fp12)
         (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
         (Px Py : Fp) (f : Fp12) (Tx Ty : Fp2),
    multibase_iter_step ops
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      Px Py (-1) f Tx Ty
    = let '(f1, Tx1, Ty1) := double_step ops f Tx Ty Px Py in
      add_step ops f1 Tx1 Ty1 QxNeg QyNeg Px Py.
Proof. reflexivity. Qed.

(** Dispatcher consistency at [j = 3]: doubling then adding [φQ]. *)
Lemma multibase_iter_step_j3 :
  forall {Fp Fp2 Fp12} (ops : FieldOps Fp Fp2 Fp12)
         (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
         (Px Py : Fp) (f : Fp12) (Tx Ty : Fp2),
    multibase_iter_step ops
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      Px Py 3 f Tx Ty
    = let '(f1, Tx1, Ty1) := double_step ops f Tx Ty Px Py in
      add_step ops f1 Tx1 Ty1 PhiQx PhiQy Px Py.
Proof. reflexivity. Qed.

(** Dispatcher consistency at [j = -3]: doubling then adding [-φQ]. *)
Lemma multibase_iter_step_jm3 :
  forall {Fp Fp2 Fp12} (ops : FieldOps Fp Fp2 Fp12)
         (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
         (Px Py : Fp) (f : Fp12) (Tx Ty : Fp2),
    multibase_iter_step ops
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      Px Py (-3) f Tx Ty
    = let '(f1, Tx1, Ty1) := double_step ops f Tx Ty Px Py in
      add_step ops f1 Tx1 Ty1 PhiQxNeg PhiQyNeg Px Py.
Proof. reflexivity. Qed.

(** ** Connection to the binary affine model.

    When the alphabet is restricted to [{0, 1}] (i.e. the trit-1 part is
    always 0 and only the [Q] / no-add cases fire), the 5-symbol loop
    reduces to the binary [affine_miller_aux] from [Affine.v] driven by
    the alphabet's digit-bit pattern.

    The statement: for any alphabet [α : nat -> Z] taking values in
    [{0,1}], the 5-symbol auxiliary equals the binary auxiliary with
    [n] reconstructed bit-by-bit so that [Z.testbit n i = (α i =? 1)].

    Rather than carry the bit-pattern construction, we state the
    structural identity per iteration directly. *)
Lemma multibase_iter_step_binary_eq :
  forall {Fp Fp2 Fp12} (ops : FieldOps Fp Fp2 Fp12)
         (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
         (Px Py : Fp) (f : Fp12) (Tx Ty : Fp2) (b : bool),
    multibase_iter_step ops
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      Px Py (if b then 1 else 0) f Tx Ty
    = let '(f1, Tx1, Ty1) := double_step ops f Tx Ty Px Py in
      if b then add_step ops f1 Tx1 Ty1 Qx Qy Px Py
           else (f1, Tx1, Ty1).
Proof.
  intros; destruct b; cbv [multibase_iter_step];
    destruct (double_step ops f Tx Ty Px Py) as [[? ?] ?]; reflexivity.
Qed.

(** Per-iteration reduction to the binary case.  Together with
    [affine_miller_aux]'s definition this gives a structural reduction
    of [affine_miller_5symbol_aux] to [affine_miller_aux] when the
    alphabet matches [Z.testbit n]. *)
Lemma affine_miller_5symbol_aux_binary_eq :
  forall {Fp Fp2 Fp12} (ops : FieldOps Fp Fp2 Fp12)
         (n : Z) (i : nat)
         (Px Py : Fp) (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
         (f : Fp12) (Tx Ty : Fp2),
    affine_miller_5symbol_aux ops
      (fun k => if Z.testbit n (Z.of_nat k) then 1 else 0)
      i Px Py
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      f Tx Ty
    = affine_miller_aux ops n i Px Py Qx Qy f Tx Ty.
Proof.
  intros Fp Fp2 Fp12 ops n i.
  induction i as [| i' IH]; intros Px Py Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg f Tx Ty.
  - reflexivity.
  - cbn [affine_miller_5symbol_aux affine_miller_aux].
    rewrite multibase_iter_step_binary_eq.
    destruct (double_step ops f Tx Ty Px Py) as [[f1 Tx1] Ty1].
    destruct (Z.testbit n (Z.of_nat i'));
      cbn; apply IH.
Qed.

(** Connection lemma at top level: with a [{0,1}] alphabet, the
    5-symbol main loop equals the binary [affine_miller] applied to the
    Z whose bits read off the alphabet. *)
Lemma affine_miller_5symbol_extends_binary :
  forall {Fp Fp2 Fp12} (ops : FieldOps Fp Fp2 Fp12)
         (n : Z) (n_iters : nat)
         (Px Py : Fp) (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2),
    n_iters = Z.to_nat (Z.log2 n) ->
    fst (fst
      (affine_miller_5symbol ops n_iters
        (fun k => if Z.testbit n (Z.of_nat k) then 1 else 0)
        Px Py Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg))
    = affine_miller ops n Px Py Qx Qy.
Proof.
  intros Fp Fp2 Fp12 ops n n_iters Px Py
         Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg Hiter.
  cbv [affine_miller_5symbol affine_miller].
  rewrite Hiter.
  rewrite affine_miller_5symbol_aux_binary_eq.
  destruct (affine_miller_aux ops n (Z.to_nat (Z.log2 n)) Px Py Qx Qy
              (fp12_one ops) Qx Qy) as [[? ?] ?]; reflexivity.
Qed.

(** ** Precomputation sanity check.

    Sanity property of the [multibase_iter_step] dispatcher under the
    digit-3 branch: with [j = 3], the iteration is precisely "double
    then add the precomputed digit-3 point [PhiQ]".  This is the
    symbolic-composition claim that justifies materialising the
    digit-3 target via a single [add_step] at iteration time.

    Note: this is *not* the curve-arithmetic claim "3Q = (3·Qx, 3·Qy)"
    (which is false on an elliptic curve); the digit-3 point used by
    BW6's optimal-ate is [φ(Q)] (the GLV image), not 3·Q.  The lemma
    pins down the dispatcher structure; the caller is responsible for
    passing the correct precomputed point. *)
Lemma multibase_iter_step_precompute_3 :
  forall {Fp Fp2 Fp12} (ops : FieldOps Fp Fp2 Fp12)
         (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2)
         (Px Py : Fp) (f : Fp12) (Tx Ty : Fp2),
    multibase_iter_step ops
      Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
      Px Py 3 f Tx Ty
    = (let '(f1, Tx1, Ty1) := double_step ops f Tx Ty Px Py in
       add_step ops f1 Tx1 Ty1 PhiQx PhiQy Px Py).
Proof. reflexivity. Qed.
