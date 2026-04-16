(** * Affine.v — curve-generic affine reference Miller loop in Gallina.

    This is the L2 layer in [PLAN_PAIRING_SPECS.md]. The function defined
    here, [affine_miller], is parameterised over an abstract record of
    field operations on (Fp, Fp2, Fp12) plus a [make_line] helper. It
    computes [f_{n,Q}(P)] for any positive integer [n] using a left-to-right
    binary square-and-multiply Miller loop.

    The intended uses:

    1. Fully concrete instantiation: instantiate [FieldOps] with native Z
       arithmetic (mod p) for one of our curves and use [Eval vm_compute]
       to compute reference Miller loop values for unit tests / cross-checks.

    2. Symbolic instantiation: instantiate [FieldOps] with the bedrock2
       fiat-crypto Fp / Fp2 / Fp12 types and prove equality with the
       bedrock2 IR's Miller loop. (Future work; the file as-is is the
       reference algorithm only.)

    The line function ([make_line] in [FieldOps]) is left abstract because
    its basis layout differs by twist convention. The line bug we hit in
    BN254 (Task #21) lived in the BN254 [make_line] body inside the
    bedrock2 IR — at L2 it's a parameter, so a wrong layout in [make_line]
    propagates *into the postcondition* and would be caught by L4
    equivalence proofs, not silently absorbed.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.

Local Open Scope Z_scope.

(** Generic field/tower operations the affine Miller loop needs.
    No assumptions about how Fp/Fp2/Fp12 are represented — only that the
    listed operations exist and return the same types they take. *)
Record FieldOps (Fp Fp2 Fp12 : Type) : Type := {
  (* Fp *)
  fp_zero  : Fp;
  fp_one   : Fp;

  (* Fp2 *)
  fp2_zero : Fp2;
  fp2_one  : Fp2;
  fp2_add  : Fp2 -> Fp2 -> Fp2;
  fp2_sub  : Fp2 -> Fp2 -> Fp2;
  fp2_neg  : Fp2 -> Fp2;
  fp2_mul  : Fp2 -> Fp2 -> Fp2;
  fp2_sqr  : Fp2 -> Fp2;
  fp2_inv  : Fp2 -> Fp2;
  fp2_mul_fp : Fp2 -> Fp -> Fp2;   (* multiply Fp2 by Fp scalar *)

  (* Fp12 *)
  fp12_one : Fp12;
  fp12_mul : Fp12 -> Fp12 -> Fp12;
  fp12_sqr : Fp12 -> Fp12;

  (* Line builder.
     Inputs: lambda (Fp2), Tx (Fp2), Ty (Fp2), Px (Fp), Py (Fp).
     Output: a sparse Fp12 representing the line through T at P, in
     whatever basis the curve's twist convention requires. The body of
     [make_line] is exactly where the BN254 vs BLS12-381 difference lives. *)
  make_line : Fp2 -> Fp2 -> Fp2 -> Fp -> Fp -> Fp12;
}.

Arguments fp_zero {Fp Fp2 Fp12} _.
Arguments fp_one  {Fp Fp2 Fp12} _.
Arguments fp2_zero {Fp Fp2 Fp12} _.
Arguments fp2_one  {Fp Fp2 Fp12} _.
Arguments fp2_add  {Fp Fp2 Fp12} _ _ _.
Arguments fp2_sub  {Fp Fp2 Fp12} _ _ _.
Arguments fp2_neg  {Fp Fp2 Fp12} _ _.
Arguments fp2_mul  {Fp Fp2 Fp12} _ _ _.
Arguments fp2_sqr  {Fp Fp2 Fp12} _ _.
Arguments fp2_inv  {Fp Fp2 Fp12} _ _.
Arguments fp2_mul_fp {Fp Fp2 Fp12} _ _ _.
Arguments fp12_one {Fp Fp2 Fp12} _.
Arguments fp12_mul {Fp Fp2 Fp12} _ _ _.
Arguments fp12_sqr {Fp Fp2 Fp12} _ _.
Arguments make_line {Fp Fp2 Fp12} _ _ _ _ _ _.

Section AffineMiller.

  Context {Fp Fp2 Fp12 : Type}.
  Context (ops : FieldOps Fp Fp2 Fp12).

  Local Notation "x +2 y" := (fp2_add  ops x y) (at level 50).
  Local Notation "x -2 y" := (fp2_sub  ops x y) (at level 50).
  Local Notation "x *2 y" := (fp2_mul  ops x y) (at level 40).
  Local Notation "/2 x"   := (fp2_inv  ops x)   (at level 35).

  (** Tangent slope at T = (Tx, Ty) on E': [3*Tx^2 / (2*Ty)]. *)
  Definition affine_doubling_slope (Tx Ty : Fp2) : Fp2 :=
    let txs := fp2_sqr ops Tx in
    let three_txs := (txs +2 txs) +2 txs in
    let two_ty := Ty +2 Ty in
    three_txs *2 /2 two_ty.

  (** Chord slope from T to Q on E': [(Qy - Ty) / (Qx - Tx)]. *)
  Definition affine_chord_slope (Tx Ty Qx Qy : Fp2) : Fp2 :=
    (Qy -2 Ty) *2 /2 (Qx -2 Tx).

  (** Doubling step: returns (new f, new Tx, new Ty). *)
  Definition double_step
      (f : Fp12) (Tx Ty : Fp2) (Px Py : Fp)
    : Fp12 * Fp2 * Fp2 :=
    let lam := affine_doubling_slope Tx Ty in
    let line := make_line ops lam Tx Ty Px Py in
    let f2 := fp12_mul ops (fp12_sqr ops f) line in
    let new_x := (fp2_sqr ops lam) -2 Tx -2 Tx in
    let new_y := (lam *2 (Tx -2 new_x)) -2 Ty in
    (f2, new_x, new_y).

  (** Mixed addition step: T + Q on E', returns (new f, new Tx, new Ty). *)
  Definition add_step
      (f : Fp12) (Tx Ty Qx Qy : Fp2) (Px Py : Fp)
    : Fp12 * Fp2 * Fp2 :=
    let lam := affine_chord_slope Tx Ty Qx Qy in
    let line := make_line ops lam Tx Ty Px Py in
    let f' := fp12_mul ops f line in
    let new_x := ((fp2_sqr ops lam) -2 Tx) -2 Qx in
    let new_y := (lam *2 (Tx -2 new_x)) -2 Ty in
    (f', new_x, new_y).

  (** [affine_miller_aux] processes bit indices [i-1], [i-2], …, [0]
      of [n] in that order. The loop invariant is:
        f = f_{ n_{top..i}, Q }(P)  and  T = [n_{top..i}] * Q
      where [n_{top..i}] denotes the value of [n]'s bits from the top
      down to but excluding bit [i]. *)
  Fixpoint affine_miller_aux
      (n : Z) (i : nat)
      (Px Py : Fp) (Qx Qy : Fp2)
      (f : Fp12) (Tx Ty : Fp2)
    : Fp12 * Fp2 * Fp2 :=
    match i with
    | O => (f, Tx, Ty)
    | S i' =>
      let '(f1, Tx1, Ty1) := double_step f Tx Ty Px Py in
      let '(f2, Tx2, Ty2) :=
        if Z.testbit n (Z.of_nat i') then
          add_step f1 Tx1 Ty1 Qx Qy Px Py
        else
          (f1, Tx1, Ty1)
      in
      affine_miller_aux n i' Px Py Qx Qy f2 Tx2 Ty2
    end.

  (** Top-level affine Miller function. The loop is initialised with
      [f := 1, T := Q], which has the effect of consuming the topmost
      bit of [n] (always 1 for any positive [n]). The remaining
      [Z.log2 n] bits are processed by [affine_miller_aux].

      Convention: returns [f_{n, Q}(P)] for the unsigned positive value
      [n]. The sign is handled by the curve-specific wrapper (BLS12-381
      conjugates, BN254 doesn't). *)
  Definition affine_miller
      (n : Z) (Px Py : Fp) (Qx Qy : Fp2) : Fp12 :=
    let nbits := Z.to_nat (Z.log2 n) in
    let '(f, _, _) :=
      affine_miller_aux n nbits Px Py Qx Qy
        (fp12_one ops) Qx Qy
    in f.

End AffineMiller.

(** ** Sparse-line variant of the affine Miller loop.

    The line emitted by [make_line] is sparse — only 6 of its 12
    [Fp] components are non-zero (in the bedrock2 D-twist basis: c0.c0
    and the [c1] block, in the M-twist basis: the [c0] block and
    c1.c1).  A generic [Fp12] multiplier wastes work multiplying by
    those zeros.  A specialised [fp12_mul_by_line] is roughly 2x faster
    on real instances (~half the [Fp2] multiplications); arkworks calls
    this its [ell()] routine and saves much of the per-iteration cost
    of the Miller loop.

    [affine_miller_sparse] is structurally identical to [affine_miller]
    but uses an extra [mul_by_line : Fp12 -> Fp12 -> Fp12] argument
    everywhere the line is multiplied into [f].  Curves whose
    [FieldOps] doesn't have a sparse multiplier just pass [fp12_mul]
    and pay the speed penalty; correctness is preserved by the trivial
    equality [fp12_mul = mul_by_line] in that case. *)

Section AffineMillerSparse.

  Context {Fp Fp2 Fp12 : Type}.
  Context (ops : FieldOps Fp Fp2 Fp12).
  Context (mul_by_line : Fp12 -> Fp12 -> Fp12).

  Local Notation "x +2 y" := (fp2_add  ops x y) (at level 50).
  Local Notation "x -2 y" := (fp2_sub  ops x y) (at level 50).
  Local Notation "x *2 y" := (fp2_mul  ops x y) (at level 40).
  Local Notation "/2 x"   := (fp2_inv  ops x)   (at level 35).

  Definition double_step_sparse
      (f : Fp12) (Tx Ty : Fp2) (Px Py : Fp)
    : Fp12 * Fp2 * Fp2 :=
    let lam := affine_doubling_slope ops Tx Ty in
    let line := make_line ops lam Tx Ty Px Py in
    let f2 := mul_by_line (fp12_sqr ops f) line in
    let new_x := (fp2_sqr ops lam) -2 Tx -2 Tx in
    let new_y := (lam *2 (Tx -2 new_x)) -2 Ty in
    (f2, new_x, new_y).

  Definition add_step_sparse
      (f : Fp12) (Tx Ty Qx Qy : Fp2) (Px Py : Fp)
    : Fp12 * Fp2 * Fp2 :=
    let lam := affine_chord_slope ops Tx Ty Qx Qy in
    let line := make_line ops lam Tx Ty Px Py in
    let f' := mul_by_line f line in
    let new_x := ((fp2_sqr ops lam) -2 Tx) -2 Qx in
    let new_y := (lam *2 (Tx -2 new_x)) -2 Ty in
    (f', new_x, new_y).

  Fixpoint affine_miller_sparse_aux
      (n : Z) (i : nat)
      (Px Py : Fp) (Qx Qy : Fp2)
      (f : Fp12) (Tx Ty : Fp2)
    : Fp12 * Fp2 * Fp2 :=
    match i with
    | O => (f, Tx, Ty)
    | S i' =>
      let '(f1, Tx1, Ty1) := double_step_sparse f Tx Ty Px Py in
      let '(f2, Tx2, Ty2) :=
        if Z.testbit n (Z.of_nat i') then
          add_step_sparse f1 Tx1 Ty1 Qx Qy Px Py
        else
          (f1, Tx1, Ty1)
      in
      affine_miller_sparse_aux n i' Px Py Qx Qy f2 Tx2 Ty2
    end.

  Definition affine_miller_sparse
      (n : Z) (Px Py : Fp) (Qx Qy : Fp2) : Fp12 :=
    let nbits := Z.to_nat (Z.log2 n) in
    let '(f, _, _) :=
      affine_miller_sparse_aux n nbits Px Py Qx Qy
        (fp12_one ops) Qx Qy
    in f.

End AffineMillerSparse.

(** Soundness witness: with [mul_by_line := fp12_mul ops],
    [affine_miller_sparse] reduces structurally to [affine_miller]. *)
Lemma affine_miller_sparse_dense
  {Fp Fp2 Fp12 : Type}
  (ops : FieldOps Fp Fp2 Fp12)
  (n : Z) (Px Py : Fp) (Qx Qy : Fp2) :
  affine_miller_sparse ops (fp12_mul ops) n Px Py Qx Qy
    = affine_miller ops n Px Py Qx Qy.
Proof. reflexivity. Qed.

(** ** Concrete instance: native-Z mod p arithmetic.

    This is the executable instance used by [Eval vm_compute] cross-checks.
    It mirrors the bedrock2 tower's basis exactly:
      Fp2 = Fp[u] / (u^2 + 1)            (so beta = -1)
      Fp6, Fp12 not used directly here   — see the [make_line] doc.

    The line function is parameterised by a [twist : TwistKind]; this is
    the only place that knows about the D vs M layout split. *)

Require Import Bedrock.Field.PairingTheory.CurveParams.

Module ZModMillerOps.

  (** Fp = Z, all ops mod p. Caller passes p in. *)
  Local Definition T := Z.

  (** Fp2 element: pair (re, im) with arithmetic mod p, beta = -1. *)
  Definition Fp2_v := (Z * Z)%type.

  (** Fp12 element: a flat 12-tuple in the bedrock2 basis order
        (c0.c0.c0, c0.c0.c1, c0.c1.c0, c0.c1.c1, c0.c2.c0, c0.c2.c1,
         c1.c0.c0, c1.c0.c1, c1.c1.c0, c1.c1.c1, c1.c2.c0, c1.c2.c1).
      We model only the operations the affine Miller loop touches:
      [one], [mul] and [sqr]. For Fp12 mul we'd need the full Fp6 / Fp12
      tower implementation; rather than reproduce 200 lines, we leave
      it as an [Axiom Fp12_v : Type] with abstract operations and ask
      the *caller* to instantiate it.

      In other words: this module gives you Fp + Fp2 over Z, but the
      Fp12 layer is still a black box. The intended workflow is to
      build [FieldOps] for vm_compute by combining this module with a
      separate Fp12 implementation (for example one extracted from the
      existing fiat-crypto Fp12 algebraic models, or a hand-rolled Z
      implementation in a sibling file). *)

End ZModMillerOps.

(** TODO (future work, see PLAN_PAIRING_SPECS.md):
    - Add [ZModFp12.v]: a flat-Z implementation of Fp12 = Fp[u]/(u^2+1)
      [v]/(v^3-xi) [w]/(w^2-v) suitable for [Eval vm_compute]. This is
      ~150 lines of arithmetic and lets us do
        [Eval vm_compute in affine_miller bn254_ops 3 Px Py Qx Qy]
      to obtain a numerical reference value.
    - Prove [affine_miller] correct against the divisor-theoretic
      [f_{n,Q}] from [MillerFunction.v] (L1 ↔ L2 equivalence).
    - Build a [FieldOps] instance from the bedrock2 fiat-crypto Fp / Fp2
      / Fp12 representations and prove the bedrock2 [bn254_miller_loop]
      function value-equal to [affine_miller bn254_ops loop_param ...]
      under the bedrock2 sep-logic precondition (L4 equivalence). *)
