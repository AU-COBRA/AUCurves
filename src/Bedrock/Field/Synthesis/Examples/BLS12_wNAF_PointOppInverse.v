(** * Point-opposition inverse for the RCB complete addition formula.

    Task (C) from BLS12_wNAF_GLV_Instance.v: discharge the
    [point_opp_inverse] hypothesis for the concrete curve_add defined
    by [ladderstep_gallina] (Renes-Costello-Batina complete addition
    for short Weierstrass y^2 = x^3 + b).

    ** Key finding: **
    [ladderstep_gallina three_b X X Y (opp Y) Z Z] produces
    [(0, Yout, 0)] where [Yout] depends on the input point, NOT
    the constant [(0, 1, 0)].  In particular,

      Yout = (Y^2 - 3*b*Z^2) * (-(Y^2) - 3*b*Z^2) + 3*X^2 * (3*b * 2*X*Z)

    which simplifies to  Y^4 - 9*b^2*Z^4 + 18*b*X^3*Z.

    Since Zout = 0, the output [(0, Yout, 0)] IS projectively
    equivalent to [(0, 1, 0)] (both represent the point at infinity),
    but they are NOT Leibniz-equal.

    ** Consequences for the proof chain: **
    The [point_opp_inverse] axiom in BLS12_wNAF_HornerAlgebra.v
    requires Leibniz equality [curve_add P (point_opp P) = (0, 1, 0)].
    This is NOT satisfiable when [curve_add] is literally
    [ladderstep_gallina].  Two resolutions:

    (1) Define [curve_add] as [ladderstep_gallina] post-composed with
        a normalization step that maps [(X, Y, 0)] to [(0, 1, 0)].
        Then [point_opp_inverse] holds, but [curve_add_zero_r] and
        [curve_add_zero_l] also need re-verification (they DO hold
        because the identity input (0,1,0) has Z2=0, but the OUTPUT
        of curve_add(P, id) also has non-trivial coordinates that need
        normalization — see discussion below).

    (2) Refactor HornerAlgebra to use projective equivalence instead
        of Leibniz equality.  This is more principled but requires
        changing the entire proof chain.

    ** What this file proves: **
    We prove the core field identities:
    - [rcb_add_opp_Xout_zero]: the X-coordinate of the output is 0
    - [rcb_add_opp_Zout_zero]: the Z-coordinate of the output is 0
    - [rcb_add_opp_result]: the output is [(0, Yout, 0)] for explicit [Yout]

    These are proved using the [ring] tactic on F_p.

    We also define the normalizing wrapper and prove
    [point_opp_inverse_norm] for it. *)

From Stdlib Require Import ZArith Lia Znumtheory.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.ModularArithmetic.

Local Open Scope F_scope.

Section RCB_PointOppInverse.

  Context {p : positive} {prime_p : prime p}.

  Local Notation F := (F p).
  Local Notation Fzero := (@F.zero p).
  Local Notation Fone := (@F.one p).

  (** Register ring for the [ring] tactic. *)
  Add Ring Fp_ring : (F.ring_theory p)
    (morphism (F.ring_morph p),
     constants [F.is_constant],
     div (F.morph_div_theory p),
     power_tac (F.power_theory p) [F.is_pow_constant]).

  (** The b-parameter of the curve y^2 = x^3 + b.
      [three_b] = 3*b is the precomputed constant used by ladderstep. *)
  Variable three_b : F.

  (** ** Pure algebraic definition of the RCB complete addition formula.

      This is exactly [ladderstep_gallina] from CurveAdd.v with all
      [let/n], [stack], and [nlet] reduced (they are all identity
      functions). Arguments: (X1, X2, Y1, Y2, Z1, Z2). *)

  Definition rcb_add (X1 X2 Y1 Y2 Z1 Z2 : F) : F * F * F :=
    let t0 := X1 * X2 in
    let t1 := Y1 * Y2 in
    let t2 := Z1 * Z2 in
    let t3 := (X1 + Y1) * (X2 + Y2) in
    let t4 := t0 + t1 in
    let t3 := t3 - t4 in
    let t4 := (X1 + Z1) * (X2 + Z2) in
    let t5 := t0 + t2 in
    let t4 := t4 - t5 in
    let t5 := (Y1 + Z1) * (Y2 + Z2) in
    let Xout_0 := t1 + t2 in
    let t5 := t5 - Xout_0 in
    let Zout_0 := three_b * t2 in
    let Xout_1 := t1 - Zout_0 in
    let Zout_1 := Zout_0 + t1 in
    let Yout_0 := Xout_1 * Zout_1 in
    let t1' := t0 + t0 + t0 in (* 3 * t0 *)
    let t4' := three_b * t4 in
    let t0' := t1' * t4' in
    let Yout := Yout_0 + t0' in
    let t0'' := t5 * t4' in
    let Xout := t3 * Xout_1 - t0'' in
    let t0''' := t3 * t1' in
    let Zout := t5 * Zout_1 + t0''' in
    (Xout, Yout, Zout).

  (** ** Core lemmas: addition with negated point gives Z=0 output. *)

  (** When we add P = (X, Y, Z) to its negation -P = (X, -Y, Z),
      the X-output of the RCB formula is zero. *)
  Lemma rcb_add_opp_Xout_zero : forall Xc Yc Zc,
    fst (fst (rcb_add Xc Xc Yc (F.opp Yc) Zc Zc)) = Fzero.
  Proof.
    intros Xc Yc Zc. unfold rcb_add; cbv [fst snd].
    (* After unfolding, the X-output contains a factor [t3] and [t5]
       which are both zero when X1=X2, Y2=-Y1, Z1=Z2.

       t3 = (X+Y)*(X+(-Y)) - (X*X + Y*(-Y))
          = (X^2 - Y^2) - (X^2 - Y^2) = 0
       t5 = (Y+Z)*((-Y)+Z) - (Y*(-Y) + Z*Z)
          = (Z^2 - Y^2) - (-Y^2 + Z^2) = 0

       Xout = t3 * Xout_1 - t5 * t4', and both terms have a zero factor. *)
    ring.
  Qed.

  (** When we add P to -P, the Z-output of the RCB formula is zero. *)
  Lemma rcb_add_opp_Zout_zero : forall Xc Yc Zc,
    snd (rcb_add Xc Xc Yc (F.opp Yc) Zc Zc) = Fzero.
  Proof.
    intros Xc Yc Zc. unfold rcb_add; cbv [fst snd].
    (* Zout = t5 * Zout_1 + t3 * t1', and both t3=0 and t5=0. *)
    ring.
  Qed.

  (** The full output: X=0, Z=0, and Y is some specific expression. *)
  Lemma rcb_add_opp_result : forall Xc Yc Zc,
    exists Yout,
    rcb_add Xc Xc Yc (F.opp Yc) Zc Zc = (Fzero, Yout, Fzero).
  Proof.
    intros Xc Yc Zc.
    pose proof (rcb_add_opp_Xout_zero Xc Yc Zc) as HX.
    pose proof (rcb_add_opp_Zout_zero Xc Yc Zc) as HZ.
    destruct (rcb_add Xc Xc Yc (F.opp Yc) Zc Zc) as [[Xo Yo] Zo].
    simpl in HX, HZ. subst Xo Zo.
    exists Yo. reflexivity.
  Qed.

  (** ** Normalizing wrapper.

      To obtain Leibniz-equal identity [(0, 1, 0)], we define a wrapper
      that normalizes outputs with Z=0 to the canonical identity.
      In practice, this would be implemented as a conditional move
      (cmov/csel) after curve_add. *)

  Definition rcb_add_norm (X1 X2 Y1 Y2 Z1 Z2 : F) : F * F * F :=
    let '(Xo, Yo, Zo) := rcb_add X1 X2 Y1 Y2 Z1 Z2 in
    if F.eq_dec Zo Fzero then (Fzero, Fone, Fzero) else (Xo, Yo, Zo).

  (** The normalizing wrapper satisfies point_opp_inverse exactly. *)
  Lemma point_opp_inverse_norm : forall Xc Yc Zc,
    rcb_add_norm Xc Xc Yc (F.opp Yc) Zc Zc = (Fzero, Fone, Fzero).
  Proof.
    intros Xc Yc Zc. unfold rcb_add_norm.
    destruct (rcb_add_opp_result Xc Yc Zc) as [Yout Heq].
    rewrite Heq.
    destruct (F.eq_dec Fzero Fzero) as [_|Habs]; [reflexivity|].
    exfalso; apply Habs; reflexivity.
  Qed.

  (** ** Verification that rcb_add matches ladderstep_gallina.

      The definition [rcb_add] above is the algebraic core of
      [ladderstep_gallina] from CurveAdd.v. Specifically, after
      unfolding [nlet] (which is [fun vars val body => body val])
      and [stack] (which is [fun a => a]), the two definitions
      are definitionally equal up to the P2.pair / (,) distinction:

        ladderstep_gallina three_b X1 X2 Y1 Y2 Z1 Z2
        = \< fst (fst (rcb_add X1 X2 Y1 Y2 Z1 Z2)),
             snd (fst (rcb_add X1 X2 Y1 Y2 Z1 Z2)),
             snd (rcb_add X1 X2 Y1 Y2 Z1 Z2) \>

      This equivalence is straightforward but requires importing
      Rupicola (for P2.pair, nlet, stack) and instantiating the
      bedrock2 context variables (width, BW, word, mem,
      field_parameters, field_representation).  We omit the formal
      proof here to keep this file lightweight. *)

  (** ** Analysis of identity inputs.

      For the abstract proof chain to work, [curve_add_zero_r] must
      also hold: [curve_add P (0,1,0) = P].

      With [rcb_add_norm], adding (X,Y,Z) to (0,1,0):
        rcb_add X 0 Y 1 Z 0 = (X*Y, Y^2, Y*Z)
      which is projectively equivalent to (X,Y,Z) (scaled by Y).
      But [Y*Z] is generally nonzero, so normalization does NOT fire,
      and the result [(X*Y, Y^2, Y*Z)] is NOT Leibniz-equal to [(X,Y,Z)].

      This means [rcb_add_norm] does NOT satisfy [curve_add_zero_r]
      either.  The full resolution requires projective equivalence
      throughout the proof chain, OR a more sophisticated normalization
      that divides by the appropriate scalar. *)

  (** Demonstrate identity-right failure: rcb_add P (0,1,0) != P *)
  Lemma rcb_add_identity_right : forall Xc Yc Zc,
    rcb_add Xc Fzero Yc Fone Zc Fzero = (Xc * Yc, Yc * Yc, Yc * Zc).
  Proof.
    intros Xc Yc Zc. unfold rcb_add. f_equal. { f_equal; ring. } ring.
  Qed.

  (** But the output IS projectively equivalent to (X, Y, Z): all
      coordinates are scaled by Y.  This is the correct mathematical
      statement. *)

  (** ** Alternative resolution: weaken point_opp_inverse.

      Instead of requiring [curve_add P (negate P) = (0, 1, 0)],
      the HornerAlgebra could require only that the Z-output is zero:

        [snd (curve_add P (negate P)) = 0]

      combined with a separate lemma that the scmul loop PRESERVES
      Leibniz equality with (0,1,0) for the accumulator:

        If acc = (0,1,0) and we apply curve_add acc Q, then
        curve_add (0,1,0) Q = (Q_X * Q_Y, Q_Y^2, Q_Y * Q_Z)

      which is projectively Q, and subsequent curve_adds compose
      correctly up to projective equivalence.

      This approach would require a projective-equivalence version
      of the entire HornerAlgebra. *)

End RCB_PointOppInverse.
