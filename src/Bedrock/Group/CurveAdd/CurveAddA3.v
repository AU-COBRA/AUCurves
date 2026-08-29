(** * Rupicola derivation of the a = -3 Renes-Costello-Batina
      complete point addition (RCB 2015, Algorithm 4).

    Structural clone of [CurveAddGeneralA.v] (the compiled general-a
    ADDITION derivation, Algorithm 1): same section layout, same
    loader-spec / loader-compilation-lemma pattern, same
    [Derive ... compile] driver.  Two differences:

    - ONE stack-loaded curve constant instead of two.  Algorithm 4
      multiplies by [b] (not by [3b]) and never multiplies by [a],
      because a = -3 is realised by the additions of lines 20-22,
      26-34.  So the derivation carries a single [b_val] / [b_name]
      loader where the general-a file carries [three_b_val] and
      [a_val].

    - The chain is LONGER in [let/n] steps and SHORTER in
      multiplications:

        Algorithm 1 (general a)   40 ops = 12 M + 3 m_a + 2 m_3b + 23 add
                                         = 17 multiplications, 23 add/sub
        Algorithm 4 (a = -3)      43 ops = 12 M + 2 m_b        + 29 add
                                         = 14 multiplications, 29 add/sub

      Three field multiplications are traded for six field additions,
      and one stack temporary is saved (t0..t4 here, t0..t5 there;
      plus one constant buffer instead of two, so six stack
      allocations against eight).  That trade is the whole point:
      a word-by-word-Montgomery multiplication at four or six limbs
      costs several times a modular addition.

    Source: Renes, Costello, Batina, "Complete addition formulas for
    prime order elliptic curves", EUROCRYPT 2016 / ePrint 2015/1060,
    Algorithm 4 ("Complete, projective point addition for prime order
    short Weierstrass curves E/Fq : y^2 = x^3 - 3x + b"), also the EFD
    entry add-2015-rcb.  Steps below are numbered A1-A43 after that
    algorithm's line numbers.  Every NIST prime curve (P-224, P-256,
    P-384, P-521) has a = -3.  Curves with a = 0 (BLS12, BN, Pallas,
    Vesta, secp256k1) are served by Algorithm 7 instead, which is
    already derived in [CurveAdd.v]; this file is the missing third
    case.

    Algorithm 4 is EQUAL to Algorithm 1 at (a, 3b) := (-3, 3b) as a
    polynomial identity in F[X1,Y1,Z1,X2,Y2,Z2,b] -- no on-curve
    hypothesis is used.  That equality is [CurveA3Equiv.v], and it is
    what carries the [RcbProjectiveLaws] group laws, the Bignum
    bridges and the wNAF instances over to this body unchanged.

    Honesty ledger (this file): 0 Admitted, 0 Axiom.  Nothing here was
    executed by a compiler at authoring time; the file is a static
    clone of an attested one, and every unverified API detail is
    flagged (* PORT-CHECK: ... *). *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Local Open Scope Z_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section Gallina.

Context {field_parameters : FieldParameters}.
Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
Context {field_representation : FieldRepresentation}.

Local Notation F := (F M_pos).
Local Infix "+F" := (@F.add M_pos) (at level 100).
Local Infix "-F" := (@F.sub M_pos) (at level 100).
Local Infix "*F" := (@F.mul M_pos) (at level 90).

(** The single curve constant: b of y^2 = x^3 - 3x + b.

    PORT-CHECK (B): the general-a derivation is parameterised by 3b;
    Algorithm 4 needs b itself.  The per-curve instantiation therefore
    encodes a NEW Montgomery constant (the limbs of b), not a reuse of
    [pXXX_three_b_mont].  [MontgomeryCurveSpecs.three_b_mont_list] is
    a generic encoder (partition then to_montgomerymod), so
    [three_b_mont_list m bw n m' b] produces those limbs. *)
Context {b_val : F}.

  (** a = -3 RCB complete addition, Algorithm 4, 43 field operations.

      Step markers A1-A43 are the line numbers of Algorithm 4 (RCB
      2015).  Paper variable -> binder: t0..t4 -> t0..t4 (stack),
      X3 -> outx, Y3 -> outy, Z3 -> outz, b -> b_const (stack).

      [stack] marks the FIRST binding of each stack-allocated
      temporary (b_const, t0..t4), exactly as in
      [rcb_add_general_gallina]; outx/outy/outz are the caller's
      output buffers, so their first bindings (A10, A15, A19) are
      plain [let/n].

      PORT-CHECK (A): five steps have dest = one or both operands
      (A21 outz := outx+outx, A22 outx := outx+outz, A30, A31, and the
      in-place updates A28/A29/A34/A38/A40/A43).  Full aliasing is
      admissible for [compile_binop] (Compilation2.v), which takes the
      x-, y- and out-FElem facts as three separate hypotheses on the
      same memory; the attested cases are S21/S23/S34/S37/S40 of
      [rcb_add_general_gallina] and [t := t +F t] in PointDouble.v. *)
  Definition rcb_add_a3_gallina
             (X1 Y1 Z1 X2 Y2 Z2 : F) : \<< F, F, F \>> :=
    let/n b_const := stack b_val in
    let/n t0 := stack (X1 *F X2) in       (* A1  t0 = X1X2 *)
    let/n t1 := stack (Y1 *F Y2) in       (* A2  t1 = Y1Y2 *)
    let/n t2 := stack (Z1 *F Z2) in       (* A3  t2 = Z1Z2 *)
    let/n t3 := stack (X1 +F Y1) in       (* A4 *)
    let/n t4 := stack (X2 +F Y2) in       (* A5 *)
    let/n t3 := (t3 *F t4) in             (* A6 *)
    let/n t4 := (t0 +F t1) in             (* A7 *)
    let/n t3 := (t3 -F t4) in             (* A8  t3 = X1Y2 + Y1X2 *)
    let/n t4 := (Y1 +F Z1) in             (* A9 *)
    let/n outx := (Y2 +F Z2) in           (* A10 *)
    let/n t4 := (t4 *F outx) in           (* A11 *)
    let/n outx := (t1 +F t2) in           (* A12 *)
    let/n t4 := (t4 -F outx) in           (* A13 t4 = Y1Z2 + Z1Y2 *)
    let/n outx := (X1 +F Z1) in           (* A14 *)
    let/n outy := (X2 +F Z2) in           (* A15 *)
    let/n outx := (outx *F outy) in       (* A16 *)
    let/n outy := (t0 +F t2) in           (* A17 *)
    let/n outy := (outx -F outy) in       (* A18 outy = X1Z2 + Z1X2 *)
    let/n outz := (b_const *F t2) in      (* A19 outz = b*Z1Z2 *)
    let/n outx := (outy -F outz) in       (* A20 *)
    let/n outz := (outx +F outx) in       (* A21 *)
    let/n outx := (outx +F outz) in       (* A22 outx = 3(xz - b*zz) *)
    let/n outz := (t1 -F outx) in         (* A23 outz = yy - 3(xz-b*zz) *)
    let/n outx := (t1 +F outx) in         (* A24 outx = yy + 3(xz-b*zz) *)
    let/n outy := (b_const *F outy) in    (* A25 outy = b*xz *)
    let/n t1 := (t2 +F t2) in             (* A26 *)
    let/n t2 := (t1 +F t2) in             (* A27 t2 = 3*zz *)
    let/n outy := (outy -F t2) in         (* A28 *)
    let/n outy := (outy -F t0) in         (* A29 outy = b*xz - 3zz - xx *)
    let/n t1 := (outy +F outy) in         (* A30 *)
    let/n outy := (t1 +F outy) in         (* A31 outy = 3(b*xz - 3zz - xx) *)
    let/n t1 := (t0 +F t0) in             (* A32 *)
    let/n t0 := (t1 +F t0) in             (* A33 t0 = 3*xx *)
    let/n t0 := (t0 -F t2) in             (* A34 t0 = 3xx - 3zz *)
    let/n t1 := (t4 *F outy) in           (* A35 *)
    let/n t2 := (t0 *F outy) in           (* A36 *)
    let/n outy := (outx *F outz) in       (* A37 *)
    let/n outy := (outy +F t2) in         (* A38 Y3 *)
    let/n outx := (t3 *F outx) in         (* A39 *)
    let/n outx := (outx -F t1) in         (* A40 X3 *)
    let/n outz := (t4 *F outz) in         (* A41 *)
    let/n t1 := (t3 *F t0) in             (* A42 *)
    let/n outz := (outz +F t1) in         (* A43 Z3 *)
    \<outx, outy, outz\>.

End Gallina.

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

  (** The single curve-constant felem and the name of its bedrock2
      loader function.  Context order (Hbounds_eq, b_const, b_name,
      Hb_bounds, then the derivation) mirrors CurveAddGeneralA.v with
      the [a_const] block deleted, so the section-discharged argument
      order of [rcb_add_a3_correct] is
        Hbounds_eq b_const b_name marker functions ... *)
  Context (b_const : felem).
  Context (b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) b_const).

  Local Definition b_val : F := feval (proj1_sig b_const).

  (** Calling convention: outputs first, then P1, then P2 — the ABI of
      [rcb_add_general_correct] and of the hand-written
      [P256_G1_add], so that the two bodies are interchangeable at the
      call site. *)
  Instance spec_of_rcb_add_a3 : spec_of "curve_add_a3" :=
    fnspec! "curve_add_a3"
          (poutx pouty poutz pX1 pY1 pZ1 pX2 pY2 pZ2 : word)
          / (X1 Y1 Z1 X2 Y2 Z2 outxold outyold outzold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pX1 X1
         * FElem (Some tight_bounds) pY1 Y1
         * FElem (Some tight_bounds) pZ1 Z1
         * FElem (Some tight_bounds) pX2 X2
         * FElem (Some tight_bounds) pY2 Y2
         * FElem (Some tight_bounds) pZ2 Z2
         * FElem (Some tight_bounds) poutx outxold
         * FElem (Some tight_bounds) pouty outyold
         * FElem (Some tight_bounds) poutz outzold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists outx outy outz (* output values *)
                  : F ,
                  (@rcb_add_a3_gallina _ b_val X1 Y1 Z1 X2 Y2 Z2
           = \<outx, outy, outz\>)
          /\ (FElem (Some tight_bounds) pX1 X1
                * FElem (Some tight_bounds) pY1 Y1
                * FElem (Some tight_bounds) pZ1 Z1
                * FElem (Some tight_bounds) pX2 X2
                * FElem (Some tight_bounds) pY2 Y2
                * FElem (Some tight_bounds) pZ2 Z2
                * FElem (Some tight_bounds) poutx outx
                * FElem (Some tight_bounds) pouty outy
                * FElem (Some tight_bounds) poutz outz * R)%sep mem'}.

  (** Downstream compile lemma: lets a later Rupicola derivation call
      "curve_add_a3" as a single [nlet_eq] step.  Clone of
      [compile_rcb_add_general]. *)
  Lemma compile_rcb_add_a3 {tr m l functions}
        (x1 y1 z1 x2 y2 z2 outx1 outy1 outz1 : F)
        {P} {pred: P (@rcb_add_a3_gallina _ b_val x1 y1 z1 x2 y2 z2) -> predicate}
        {k: nlet_eq_k P (@rcb_add_a3_gallina _ b_val x1 y1 z1 x2 y2 z2)} {k_impl} :
    let v := @rcb_add_a3_gallina _ b_val x1 y1 z1 x2 y2 z2 in
    forall
           Rout
           X1_ptr X1_var Y1_ptr Y1_var Z1_ptr Z1_var
           X2_ptr X2_var Y2_ptr Y2_var Z2_ptr Z2_var
           outx_ptr outx_var outy_ptr outy_var outz_ptr outz_var,

      spec_of_rcb_add_a3 functions ->

      (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) Y1_ptr y1 *
       FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) X2_ptr x2 *
       FElem (Some tight_bounds) Y2_ptr y2 * FElem (Some tight_bounds) Z2_ptr z2 *
       FElem (Some tight_bounds) outx_ptr outx1 *
       FElem (Some tight_bounds) outy_ptr outy1 * FElem (Some tight_bounds) outz_ptr outz1 * Rout)%sep m ->

      map.get l X1_var = Some X1_ptr ->
      map.get l Y1_var = Some Y1_ptr ->
      map.get l Z1_var = Some Z1_ptr ->
      map.get l X2_var = Some X2_ptr ->
      map.get l Y2_var = Some Y2_ptr ->
      map.get l Z2_var = Some Z2_ptr ->
      map.get l outx_var = Some outx_ptr ->
      map.get l outy_var = Some outy_ptr ->
      map.get l outz_var = Some outz_ptr ->

      (let v := v in
       forall (* output values *) m',
       let '\<outx', outy', outz'\> := @rcb_add_a3_gallina _ b_val x1 y1 z1 x2 y2 z2 in
            (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) Y1_ptr y1 *
            FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) X2_ptr x2 *
            FElem (Some tight_bounds) Y2_ptr y2 * FElem (Some tight_bounds) Z2_ptr z2 *
            FElem (Some tight_bounds) outx_ptr outx' *
            FElem (Some tight_bounds) outy_ptr outy' * FElem (Some tight_bounds) outz_ptr outz' * Rout)%sep m' ->
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
        (cmd.call [] "curve_add_a3"
                  [ expr.var outx_var; expr.var outy_var;
                  expr.var outz_var;
                  expr.var X1_var; expr.var Y1_var; expr.var Z1_var;
                  expr.var X2_var; expr.var Y2_var; expr.var Z2_var])
        k_impl
      <{ pred (nlet_eq
                 [outx_var; outy_var; outz_var]
                 v k) }>.
  Proof.
    (* Proof script cloned verbatim from compile_rcb_add_general
       (Qed on 2026-08-28); only the name in the match pattern
       changes. *)
    repeat straightline'.
    handle_call.
    lazymatch goal with
    | Hcont : (forall m', _ -> _),
      Heq : rcb_add_a3_gallina _ _ _ _ _ _ = _,
      Hsep : sep _ _ _ |- _ =>
      apply Hcont; rewrite Heq; ecancel_assumption
    end.
  Qed.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  (** Spec for the b constant loader function.  Same fnspec as
      [CurveAddGeneralA.spec_of_three_b_loader] with [three_b_val]
      replaced by [b_val]; the P-256 loader proof
      (CurveAddGeneralA_P256_Loaders.v) transfers verbatim. *)
  Instance spec_of_b_loader : spec_of b_name :=
    fnspec! b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout b_val * Rout)%sep mem' }.

  (* Compilation lemma for loading the b constant *)
  Lemma compile_load_b {tr m l functions}
        {P} {pred: P b_val -> predicate}
        {k: nlet_eq_k P b_val} {k_impl} :
    let v := b_val in
    forall
           R out out_ptr out_var out_bounds,
      spec_of_b_loader functions ->
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
        (cmd.call [] b_name [expr.var out_var])
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
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ b_val _))) =>
    simple eapply compile_load_b; shelve : compiler.

  (* Bounds tightening: since loose_bounds = tight_bounds, we can go
     loose→tight (reverse of relax_bounds_FElem). Needed because add
     produces loose_bounds but sub/mul expect tight_bounds inputs. *)
  Local Lemma tighten_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                      (FElem (Some tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.
  Local Hint Immediate tighten_bounds_FElem : ecancel_impl.

  (** Derivation driver, cloned from CurveAddGeneralA.v (attested on a
      42-nlet chain with TWO loaders in one [compile] run).  This chain
      has 44 nlets and ONE loader.
      PORT-CHECK (D): the chain is two [let/n] longer than the
      attested one and the only new shapes are the aliased binops of
      PORT-CHECK (A), all of which occur in the attested chain too.
      If [compile] stalls, apply the MSM helper-extraction pattern
      (split the chain at A18/A24) before concluding the approach
      fails. *)
  Derive rcb_add_a3_body in
         (defn! "curve_add_a3"
                ("outx", "outy", "outz", "X1", "Y1", "Z1", "X2", "Y2", "Z2")
              { rcb_add_a3_body },
           implements @rcb_add_a3_gallina _ b_val
                      using [mul; add; sub; b_name])
         as rcb_add_a3_correct.
  Proof. compile. Qed.

End __.

#[global] Existing Instance spec_of_rcb_add_a3.

#[global]
Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (rcb_add_a3_gallina _ _ _ _ _ _) _))) =>
       simple eapply compile_rcb_add_a3; shelve : compiler.

(** * Instantiation plan (per curve)

    Identical to the plan of CurveAddGeneralA.v except that ONE
    constant is needed instead of two, and it is [b] rather than [3b]:

      Definition pXXX_b_mont := Eval vm_compute in
        MontgomeryCurveSpecs.three_b_mont_list m bw n m' pXXX_b.

    ([three_b_mont_list] is the generic "encode this Z as n Montgomery
    limbs" function of MontgomeryCurveSpecs.v:53 — partition then
    to_montgomerymod — so passing [b] gives the limbs of [b].)  Then a
    "pXXX_b" loader function storing those limbs, its
    [spec_of_b_loader] proof (the script of
    CurveAddGeneralA_P256_Loaders.v, with [three_b] replaced by [b]),
    and

      Definition pXXX_curve_add_a3_func := rcb_add_a3_body "pXXX_b".

    See CurveA3_P256.v.  P-521 is not covered (unsaturated-Solinas
    representation, so [Hbounds_eq : loose_bounds = tight_bounds]
    fails), exactly as for the general-a derivation. *)
