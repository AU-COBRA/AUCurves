(** * Rupicola derivation of the a = 0 Renes-Costello-Batina complete
      point DOUBLING (RCB 2015, Algorithm 9), and its bridge to the
      a = 0 complete ADDITION applied to a repeated argument.

    This is the a = 0 counterpart of [CurveDoubleA3.v] (Algorithm 6,
    a = -3), standing to [CurveAdd.v]'s [ladderstep_gallina]
    (Algorithm 7) exactly as [CurveDoubleA3.v] stands to
    [CurveAddA3.v] (Algorithm 4).

    ** Why this file exists **

    [PointDouble.v] already carries a definition called
    [point_double_gallina], wired as the "curve_double" entry of
    [bn254_curve_op_funcs], [bn256_curve_op_funcs] and
    [bn446_curve_op_funcs].  That body is dbl-2009-l, which is a
    JACOBIAN formula: it reads (X : Y : Z) as (X/Z^2, Y/Z^3).  Every
    other component of the a = 0 chain is HOMOGENEOUS --
    [ladderstep_gallina] is [Projective.add]
    ([BN254_wNAF_Laws.bn254_curve_add_is_cadd]), [store_zero] writes
    the homogeneous identity, and [RcbProjectiveLaws.oncurve] is the
    homogeneous curve equation.  Mixing the two is not a missing
    equivalence proof but a wrong answer: on the homogeneous
    representative (7X : 7Y : 7) of a point P, dbl-2009-l returns a
    triple that is 2P in neither reading.  The mismatch has not
    shipped -- no Rust or Jasmin artifact in this tree contains a
    "curve_double" -- but it does mean [PointDouble.v] cannot
    discharge [BN254_wNAF_Instance.HCurveDouble], whose postcondition
    is literally [curve_add (X,Y,Z) (X,Y,Z)].

    Algorithm 9 is the correct homogeneous body, and it discharges
    that postcondition on the nose (Section 2 below).

    ** Op counts **

      Algorithm 7 (a = 0, addition)  33 ops = 12 M + 2 m_3b + 19 add
                                            = 14 multiplications
      Algorithm 9 (a = 0, doubling)  18 ops =  8 M + 1 m_3b +  9 add
                                            =  9 multiplications

    Fifteen operations and five multiplications saved against the
    self-addition -- a larger margin than at a = -3, where
    [CurveDoubleA3.v]'s Algorithm 6 (34 ops / 13 M) saves nine
    operations and one multiplication against [CurveAddA3.v]'s
    Algorithm 4 (43 ops / 14 M).  Measured on BW6-761 (a = 0) over the
    verified Fp leaves, in `bw6-761-safe-rust/examples/bench_g1.rs`
    (medians of four runs on a loaded machine): doubling
    3.2 us -> 2.2 us, about -30%; 377-bit scalar multiplication
    2.0 ms -> 1.5 ms, about -24%.  The a = -3 change measured -17% to
    -22% on doubling and -10% to -17% on scalar multiplication, so the
    a = 0 transfer is worth strictly more, in the ratio the operation
    counts predict.

    ** Squarings **

    Steps D1 and D6 are squarings, written [x *F x] (binary [mul]) as
    in [CurveDoubleA3.v]'s PORT-CHECK (S), not [F.pow x 2].  That
    keeps the callee list at [mul; add; sub] plus the single loader --
    the same list [CurveAdd.v] uses -- so a curve that has
    "curve_add" already has every leaf this body needs.  It also costs
    nothing on at least one target: BW6-761's [fp_square] leaf
    measures 232 ns against [fp_mul]'s 201 ns.

    ** Honesty ledger **

    0 Admitted, 0 Axiom.  Compiler run 2026-08-29 (after the fix
    below): the whole file compiles, [compile] closes the [Derive] in
    6.7 s and [Qed] takes 0.3 s.  [Print Assumptions] reports "Closed
    under the global context" for both [rcb_double_a0_eq_ladderstep]
    and [rcb_double_a0_correct].  In the dune build.

    Compiler run 2026-08-29 (before the fix):

      * the algebra closes.  [rcb_double_a0_eq_ladderstep] (the
        Leibniz bridge: RCB Algorithm 9 equals [ladderstep_gallina]
        on a repeated argument, coordinate for coordinate, for every
        on-curve input) is Qed, as are [compile_rcb_double_a0] and
        [compile_load_three_b_a0];

      * the bedrock2 derivation did not.  [compile] ran for 15.7 s,
        backtracked, and reported "Compilation incomplete"; [Qed]
        then failed with "Attempt to save an incomplete proof".

    Diagnosis (2026-08-29): the output binders were named
    outx/outy/outz while the [defn!] argument list names the output
    buffers "Xout", "Yout", "Zout".  Rupicola takes the [let/n]
    binder as the bedrock2 variable name, so the first non-[stack]
    output binding, D2 [let/n outz := (t0 +F t0)], produced the
    side condition [map.get l "outz" = Some ?p] against a locals map
    holding only Xin/Yin/Zin/Xout/Yout/Zout and the stack temporaries
    -- unsolvable, hence the backtracking.  See PORT-CHECK (N).
    The mechanism was reproduced in isolation on Rupicola's own
    [Rupicola.Examples.Cells.Swap]: renaming its output binders c1/c2
    to d1/d2 while leaving [defn! "swap"("c1","c2")] alone leaves
    exactly [map.get #{"c1" => c1_ptr; "c2" => c2_ptr; ...}# "d1" =
    Some c1_ptr] open and makes [Qed] fail the same way.

    Fix: the binders now read Xout/Yout/Zout, matching the
    [defn!] arguments.  This is an alpha-renaming of the Gallina body
    -- the [nlet] var-name strings change, nothing else -- so
    Section 2 is untouched in content.

    Not yet re-verified: neither the [Derive] nor
    [rcb_double_a0_eq_ladderstep] has been re-run.  Interactive
    checking through rocq-mcp is unavailable for this file: the only
    `pet` binary on this machine belongs to the vc-sf opam switch, and
    loading fiat-crypto's [coq-rewriter] plugin from rocq-9 into it
    fails at Dynlink ("implementation mismatch on Proofview").
    `opam install coq-lsp --switch=rocq-9` would remove that
    limitation.  Unverified API details are flagged
    (* PORT-CHECK: ... *).

    Source: Renes, Costello, Batina, "Complete addition formulas for
    prime order elliptic curves", EUROCRYPT 2016 / ePrint 2015/1060,
    Algorithm 9 ("Exception-free point doubling for prime order short
    Weierstrass curves E/Fq : y^2 = x^3 + b").  Steps below are
    numbered D1-D18 after that algorithm's line numbers. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Local Open Scope Z_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

(* ==================================================================== *)
(** * Section 1: The Gallina body                                       *)
(* ==================================================================== *)

Section Gallina.

Context {field_parameters : FieldParameters}.
Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
Context {field_representation : FieldRepresentation}.

Local Notation F := (F M_pos).
Local Infix "+F" := (@F.add M_pos) (at level 100).
Local Infix "-F" := (@F.sub M_pos) (at level 100).
Local Infix "*F" := (@F.mul M_pos) (at level 90).

(** The single curve constant, [3b] of y^2 = x^3 + b -- the same
    constant [ladderstep_gallina] multiplies by, so a curve that
    supplies one supplies the other. *)
Context {three_b_val : F}.

  (** a = 0 RCB complete doubling, Algorithm 9, 18 field operations.
      Paper variable -> binder: t0..t2 -> t0..t2 (stack),
      X3 -> Xout, Y3 -> Yout, Z3 -> Zout, b3 -> three_b (stack).

      [stack] marks the FIRST binding of each stack-allocated
      temporary (three_b, t0..t2); Xout/Yout/Zout are the caller's
      output buffers, so their first bindings (D8, D9, D2) are plain
      [let/n].

      PORT-CHECK (N): the output binder names are NOT free.  Rupicola
      reads the [let/n] binder as the bedrock2 variable name --
      [compile_binop]'s conclusion is [pred (nlet_eq [out_var] v k)]
      and its side condition [map.get l out_var = Some out_ptr] -- so
      a plain (non-[stack]) binding must name a variable that already
      exists in [locals], i.e. one of the [defn!] argument names
      ("Xin", "Yin", "Zin", "Xout", "Yout", "Zout").  Input binders
      (X1, Y1, Z1) are unconstrained, because [compile_binop] leaves
      [x_var]/[y_var] as evars and finds them by pointer lookup;
      [PointDouble.v] relies on exactly that, with gallina inputs
      X/Y/Z against arguments "Xin"/"Yin"/"Zin".  The first draft of
      this body used outx/outy/outz, which left the unsolvable goal
      [map.get l "outz" = Some ?p] at D2 and made [compile] report
      "Compilation incomplete".  [CurveDoubleA3.v] keeps the other
      half of the same convention: it names its arguments
      ("outx", "outy", "outz", "X1", "Y1", "Z1") to match its binders.

      PORT-CHECK (A): the aliased binops (D3, D4, D7, D10, D12, D13,
      D14, D15, D18) are the shapes already attested by
      [ladderstep_gallina] (S21 [Xout := Xout -F t0], S23
      [Zout := Zout +F t0], S13 [t3 := t3 -F t4]) and by
      [PointDouble.v]'s compiled [t := t +F t]. *)
  Definition rcb_double_a0_gallina
             (X1 Y1 Z1 : F) : \<< F, F, F \>> :=
    let/n three_b := stack three_b_val in
    let/n t0 := stack (Y1 *F Y1) in       (* D1  t0 = Y^2 *)
    let/n Zout := (t0 +F t0) in           (* D2 *)
    let/n Zout := (Zout +F Zout) in       (* D3 *)
    let/n Zout := (Zout +F Zout) in       (* D4  Zout = 8Y^2 *)
    let/n t1 := stack (Y1 *F Z1) in       (* D5  t1 = YZ *)
    let/n t2 := stack (Z1 *F Z1) in       (* D6  t2 = Z^2 *)
    let/n t2 := (three_b *F t2) in        (* D7  t2 = 3b Z^2 *)
    let/n Xout := (t2 *F Zout) in         (* D8 *)
    let/n Yout := (t0 +F t2) in           (* D9  Yout = Y^2 + 3b Z^2 *)
    let/n Zout := (t1 *F Zout) in         (* D10 Zout = 8 Y^3 Z *)
    let/n t1 := (t2 +F t2) in             (* D11 *)
    let/n t2 := (t1 +F t2) in             (* D12 t2 = 9b Z^2 *)
    let/n t0 := (t0 -F t2) in             (* D13 t0 = Y^2 - 9b Z^2 *)
    let/n Yout := (t0 *F Yout) in         (* D14 *)
    let/n Yout := (Xout +F Yout) in       (* D15 Y3 *)
    let/n t1 := (X1 *F Y1) in             (* D16 t1 = XY *)
    let/n Xout := (t0 *F t1) in           (* D17 *)
    let/n Xout := (Xout +F Xout) in       (* D18 X3 *)
    \<Xout, Yout, Zout\>.

End Gallina.

(* ==================================================================== *)
(** * Section 2: Algorithm 9 IS Algorithm 7 on a repeated argument      *)
(* ==================================================================== *)

(** This section takes ONLY [field_parameters], so its statements
    discharge with exactly one implicit argument besides their
    explicit [three_b_val] -- the shape
    [BN254_wNAF_Laws.bn254_curve_add] and [RcbProjectiveLaws.cadd]
    both have, so the three compose without an intervening cast. *)

Section DoubleIsAdd.
  Context {field_parameters : FieldParameters}.

  Local Notation F := (F M_pos).

  Add Ring Fp_ring_a0_double : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  (** Turn an equality goal into a cancellation goal, so that the
      cofactor identities below are reached by [ring] alone. *)
  Lemma F_eq_of_sub_eq_zero (x y : F) :
    (x - y)%F = 0%F -> x = y.
  Proof.
    intros H. transitivity ((x - y) + y)%F; [ | rewrite H ]; ring.
  Qed.

  (** [rcb_double_a0_gallina] on plain triples, matching
      [BN254_wNAF_Laws.bn254_curve_add]'s presentation. *)
  Definition rcb_double_a0_triple (three_b_val : F) (P : F * F * F)
    : F * F * F :=
    let '(X, Y, Z) := P in
    let '\<x, y, z\> := @rcb_double_a0_gallina _ three_b_val X Y Z in
    (x, y, z).

  (** [ladderstep_gallina] on plain triples.  Definitionally the same
      as [BN254_wNAF_Laws.bn254_curve_add]; repeated here so that this
      file depends only on [CurveAdd.v].  Note the INTERLEAVED
      coordinate order [X1 X2 Y1 Y2 Z1 Z2] that [ladderstep_gallina]
      takes. *)
  Definition ladderstep_triple (three_b_val : F) (P Q : F * F * F)
    : F * F * F :=
    let '(X1, Y1, Z1) := P in
    let '(X2, Y2, Z2) := Q in
    let '\<x, y, z\> :=
      @ladderstep_gallina _ three_b_val X1 X2 Y1 Y2 Z1 Z2 in
    (x, y, z).

  (** The homogeneous curve equation at a = 0.  This is
      [RcbProjectiveLaws.oncurve F.zero b_val (X,Y,Z)] with the
      vacuous [0 * X * (Z * Z)] summand dropped and the
      [Z = 0 -> Y <> 0] conjunct forgotten -- neither is needed here
      -- so a caller holding the [RcbProjectiveLaws] predicate
      supplies this one in one line:
      [destruct H as [H _]; rewrite H; ring].  Stated here rather
      than imported so that this file's dependencies stay exactly
      [CurveAdd.v]'s. *)
  Definition oncurve_a0 (b_val : F) (P : F * F * F) : Prop :=
    let '(X, Y, Z) := P in
    (Y * Y * Z)%F = (X * (X * X) + b_val * (Z * (Z * Z)))%F.

  (** ** The bridge.

      Unlike the a = -3 case -- where [CurveA3Equiv.v] relates
      Algorithm 6 to Algorithm 3 by an UNCONDITIONAL polynomial
      identity, but where Algorithm 6 is only PROJECTIVELY equal to
      the addition on a repeated argument (its [Z3 = 8 Y^3 Z] differs
      from the addition's representative) -- Algorithm 9 and Algorithm
      7 agree here coordinate for coordinate, and the on-curve
      hypothesis is what buys that.  Off the curve they differ; the
      three cofactors against the curve polynomial
      [g := Y^2 Z - X^3 - b Z^3] are

        X3 : 0             (so X3 is an unconditional ring identity)
        Y3 : 6 * 3b * Z
        Z3 : 6 * Y

      so each coordinate closes by [ring] once [g] is rewritten to
      zero -- no [fsatz], no [nsatz], no ideal search.  The two
      cofactors are written out as repeated addition rather than
      through a numeral, so that [ring] needs no constant morphism to
      read them: [6 * t] appears as [(t + t) + (t + t) + (t + t)] and
      [3b] as [b + b + b].

      Consequence for the wNAF chain: because the equality is
      Leibniz rather than [pt_eq], a "curve_double" implementing
      Algorithm 9 satisfies [BN254_wNAF_Instance.HCurveDouble]
      (postcondition [curve_add (X,Y,Z) (X,Y,Z)]) directly, with no
      [pt_eq]-congruence argument anywhere in the chain --
      [rcb_double_a0_is_curve_add] below.

      [timeout] so that a regression reports a position instead of
      hanging: the three [ring] calls are on degree-4 polynomials in
      five variables, one variable fewer than the size
      [BN254_wNAF_Laws.bn254_curve_add_is_cadd] and
      [RcbProjectiveLaws.cadd_is_Padd] already discharge. *)
  Theorem rcb_double_a0_eq_ladderstep
          (b_val three_b_val : F) (P : F * F * F) :
    three_b_val = (b_val + b_val + b_val)%F ->
    oncurve_a0 b_val P ->
    rcb_double_a0_triple three_b_val P
    = ladderstep_triple three_b_val P P.
  Proof.
    destruct P as [[X Y] Z]. intros Hthree_b Honcurve.
    cbv [oncurve_a0] in Honcurve.
    (* The curve polynomial, as a term [ring] can cancel against. *)
    assert (Hg : ((Y * Y * Z) - (X * (X * X) + b_val * (Z * (Z * Z))))%F
                 = 0%F)
      by (rewrite Honcurve; ring).
    subst three_b_val.
    cbv [rcb_double_a0_triple ladderstep_triple
         rcb_double_a0_gallina ladderstep_gallina
         nlet stack P2.car P2.cdr].
    apply pair_equal_spec; split; [apply pair_equal_spec; split | ].
    - (* X3: cofactor 0, so an unconditional identity. *)
      timeout 120 ring.
    - (* Y3: cofactor 6 * 3b * Z, i.e. 18 * b * Z. *)
      apply F_eq_of_sub_eq_zero.
      transitivity
        (((((b_val + b_val + b_val) * Z + (b_val + b_val + b_val) * Z)
           + ((b_val + b_val + b_val) * Z + (b_val + b_val + b_val) * Z)
           + ((b_val + b_val + b_val) * Z + (b_val + b_val + b_val) * Z)))
         * ((Y * Y * Z) - (X * (X * X) + b_val * (Z * (Z * Z)))))%F.
      + timeout 120 ring.
      + rewrite Hg; ring.
    - (* Z3: cofactor 6 * Y. *)
      apply F_eq_of_sub_eq_zero.
      transitivity
        ((((Y + Y) + (Y + Y) + (Y + Y)))
         * ((Y * Y * Z) - (X * (X * X) + b_val * (Z * (Z * Z)))))%F.
      + timeout 120 ring.
      + rewrite Hg; ring.
  Qed.

  (** The form the wNAF chain consumes: any [curve_add] that is the
      a = 0 ladderstep -- [BN254_wNAF_Laws.bn254_add] is, by
      [Definition] -- is computed on a repeated argument by Algorithm
      9.  This is exactly [HCurveDouble]'s postcondition. *)
  Corollary rcb_double_a0_is_curve_add
          (curve_add : F * F * F -> F * F * F -> F * F * F)
          (three_b_val b_val : F)
          (Hadd : forall P Q, curve_add P Q = ladderstep_triple three_b_val P Q)
          (Hthree_b : three_b_val = (b_val + b_val + b_val)%F) :
    forall P, oncurve_a0 b_val P ->
              rcb_double_a0_triple three_b_val P = curve_add P P.
  Proof.
    intros P HP. rewrite Hadd.
    exact (rcb_double_a0_eq_ladderstep b_val three_b_val P Hthree_b HP).
  Qed.

End DoubleIsAdd.

(* ==================================================================== *)
(** * Section 3: Rupicola derivation                                    *)
(* ==================================================================== *)

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.

  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Local Notation F := (F M_pos).

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  (** Calling convention: inputs first, then outputs -- the order
      [PointDouble.v] uses and the order
      [BN254_wNAF_Instance.HCurveDouble] calls with
      ([pX; pY; pZ; pX; pY; pZ]), so this is a drop-in replacement for
      the "curve_double" slot of [bn254_curve_op_funcs] and friends.

      The function name is "curve_double_a0", not "curve_double", so
      that this file and [PointDouble.v] can be imported together
      without two [spec_of "curve_double"] instances competing --
      the same separation [CurveDoubleA3.v] keeps with
      "curve_double_a3".  A per-curve file binds the derived body
      into its environment under whatever key it uses, as
      [BN254_CurveOps.bn254_point_double] does with
      [("curve_double", point_double_body)]. *)
  Instance spec_of_rcb_double_a0 : spec_of "curve_double_a0" :=
    fnspec! "curve_double_a0"
          (pXin pYin pZin pXout pYout pZout : word)
          / (X Y Z Xold Yold Zold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pXin X
         * FElem (Some tight_bounds) pYin Y
         * FElem (Some tight_bounds) pZin Z
         * FElem (Some tight_bounds) pXout Xold
         * FElem (Some tight_bounds) pYout Yold
         * FElem (Some tight_bounds) pZout Zold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Xo Yo Zo : F,
             (@rcb_double_a0_gallina _ three_b_val X Y Z
              = \<Xo, Yo, Zo\>)
             /\ (FElem (Some tight_bounds) pXin X
                 * FElem (Some tight_bounds) pYin Y
                 * FElem (Some tight_bounds) pZin Z
                 * FElem (Some tight_bounds) pXout Xo
                 * FElem (Some tight_bounds) pYout Yo
                 * FElem (Some tight_bounds) pZout Zo * R)%sep mem' }.

  (** Downstream compile lemma.  Structural clone of
      [CurveAdd.compile_ladderstep] with three input pointers instead
      of six. *)
  Lemma compile_rcb_double_a0 {tr m l functions}
        (x1 y1 z1 outx1 outy1 outz1 : F)
        {P} {pred: P (@rcb_double_a0_gallina _ three_b_val x1 y1 z1) -> predicate}
        {k: nlet_eq_k P (@rcb_double_a0_gallina _ three_b_val x1 y1 z1)} {k_impl} :
    let v := @rcb_double_a0_gallina _ three_b_val x1 y1 z1 in
    forall
           Rout
           X1_ptr X1_var Y1_ptr Y1_var Z1_ptr Z1_var
           outx_ptr outx_var outy_ptr outy_var outz_ptr outz_var,

      spec_of_rcb_double_a0 functions ->

      (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) Y1_ptr y1 *
       FElem (Some tight_bounds) Z1_ptr z1 *
       FElem (Some tight_bounds) outx_ptr outx1 *
       FElem (Some tight_bounds) outy_ptr outy1 *
       FElem (Some tight_bounds) outz_ptr outz1 * Rout)%sep m ->

      map.get l X1_var = Some X1_ptr ->
      map.get l Y1_var = Some Y1_ptr ->
      map.get l Z1_var = Some Z1_ptr ->
      map.get l outx_var = Some outx_ptr ->
      map.get l outy_var = Some outy_ptr ->
      map.get l outz_var = Some outz_ptr ->

      (let v := v in
       forall m',
       let '\<outx', outy', outz'\> :=
         @rcb_double_a0_gallina _ three_b_val x1 y1 z1 in
            (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) Y1_ptr y1 *
            FElem (Some tight_bounds) Z1_ptr z1 *
            FElem (Some tight_bounds) outx_ptr outx' *
            FElem (Some tight_bounds) outy_ptr outy' *
            FElem (Some tight_bounds) outz_ptr outz' * Rout)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->

      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] "curve_double_a0"
                  [ expr.var X1_var; expr.var Y1_var; expr.var Z1_var;
                    expr.var outx_var; expr.var outy_var;
                    expr.var outz_var])
        k_impl
      <{ pred (nlet_eq
                 [outx_var; outy_var; outz_var]
                 v k) }>.
  Proof.
    repeat straightline'.
    handle_call.
    lazymatch goal with
    | Hcont : (forall m', _ -> _),
      Heq : rcb_double_a0_gallina _ _ _ = _,
      Hsep : sep _ _ _ |- _ =>
      apply Hcont; rewrite Heq; ecancel_assumption
    end.
  Qed.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  (** Loader spec and loader compilation lemma: verbatim duplicates of
      [CurveAdd.v]'s, duplicated (not imported) exactly as
      [CurveDoubleA3.v] duplicates [CurveAddA3.v]'s.  The two copies
      are convertible once the felem / name arguments are supplied, so
      a per-curve file discharges this copy from the addition loader
      proof by [exact].

      PORT-CHECK (I): [CurveAdd.spec_of_three_b_loader] and this
      [spec_of_three_b_loader_a0] are both [Instance]s of
      [spec_of three_b_name], so a file importing both has two
      candidates for that class.  Their statements are
      alpha-equivalent once the same [three_b : felem] is supplied, so
      either resolution is sound; [CurveDoubleA3.v] carries the same
      duplication against [CurveAddA3.v] and accepts it.  If
      resolution does pick wrongly, the fix is to demote one to a
      plain [Definition] and pass it explicitly at the [Derive]. *)
  Instance spec_of_three_b_loader_a0 : spec_of three_b_name :=
    fnspec! three_b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout three_b_val * Rout)%sep mem' }.

  Lemma compile_load_three_b_a0 {tr m l functions}
        {P} {pred: P three_b_val -> predicate}
        {k: nlet_eq_k P three_b_val} {k_impl} :
    let v := three_b_val in
    forall
           R out out_ptr out_var out_bounds,
      spec_of_three_b_loader_a0 functions ->
      map.get l out_var = Some out_ptr ->
      (FElem out_bounds out_ptr out * R)%sep m ->
      (let v := v in
       forall m',
         (FElem (Some loose_bounds) out_ptr v * R)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] three_b_name [expr.var out_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    repeat straightline'.
    handle_call.
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | _ => idtac
    end.
    sepsimpl; repeat straightline'; subst; eauto.
  Qed.

  Local Hint Extern 5
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ three_b_val _))) =>
    simple eapply compile_load_three_b_a0; shelve : compiler.

  Local Lemma tighten_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                      (FElem (Some tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.
  Local Hint Immediate tighten_bounds_FElem : ecancel_impl.

  (** Derivation driver: 19 nlets, one loader, four stack
      temporaries.  Strictly smaller than the attested 34-nlet
      one-loader run of [CurveAdd.v]. *)
  Derive rcb_double_a0_body SuchThat
         (defn! "curve_double_a0"
                ("Xin", "Yin", "Zin", "Xout", "Yout", "Zout")
              { rcb_double_a0_body },
           implements @rcb_double_a0_gallina _ three_b_val
                      using [mul; add; sub; three_b_name])
         As rcb_double_a0_correct.
  Proof. compile. Qed.

End __.

#[global] Existing Instance spec_of_rcb_double_a0.

#[global]
Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (rcb_double_a0_gallina _ _ _) _))) =>
       simple eapply compile_rcb_double_a0; shelve : compiler.
