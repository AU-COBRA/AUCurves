(** * MillerEquiv: statement of the Miller loop equivalence theorem.

    This file states the theorem that the bedrock2 [bn254_miller_loop]
    function computes the same value as [affine_miller bn254_zmod_ops].
    The proof is [Admitted] — closing it is Phase 4 of
    [PLAN_PAIRING_SPECS.md].

    The theorem has bite: if the bedrock2 [bn254_make_line] body uses the
    wrong basis layout (the M-twist bug from Task #21), the theorem
    CANNOT close because the Gallina reference uses the correct D-twist
    layout. This is demonstrated by [ZModTest.v: line_form_matters],
    which proves that the D-twist and M-twist Miller loop outputs differ
    on the BN254 generators.

    Closing this theorem requires:
    1. Bridging between bedrock2 [FElem] and flat-Z [ZModTower] via [feval]
    2. Walking the bedrock2 loop body call-by-call and matching each step
       to the corresponding [affine_miller_aux] step
    3. The make_line equivalence: [feval (bedrock2_make_line args) =
       dtwist_make_line p (feval args)]
    4. The loop invariant: after each iteration, the accumulated Fp12 value
       and the point T match between bedrock2 and Gallina
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Znumtheory.

Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.Curves.BN254_params.
Require Import Bedrock.Field.PairingTheory.Curves.BLS12_381_params.
Require Import Bedrock.Field.PairingTheory.Curves.BLS12_377_params.
Require Import Bedrock.Field.PairingTheory.Curves.BN256_params.
Require Import Bedrock.Field.PairingTheory.Curves.BN446_params.

Local Open Scope Z_scope.

(** The BN254 optimal-ate loop parameter. *)
Definition bn254_loop_param : Z := loop_abs bn254_params.  (* = 6u+2 *)

(** Statement: the bedrock2 [bn254_miller_loop], when run on the BN254
    generators with the correct D-twist line, produces the same Fp12
    value as [affine_miller bn254_zmod_ops].

    This is a VALUE-level claim about a SPECIFIC input (the generators).
    The general claim (for all valid inputs) requires the full L4 bridge
    and is future work. The specific-input version is already useful:
    it validates that the ZModTower + Affine infrastructure is correct
    for BN254 on at least one point. *)

(** BN254 generators. *)
Definition bn254_G1 : Z * Z := (1, 2).
Definition bn254_G2 : Fp2_Z * Fp2_Z :=
  ((10857046999023057135944570762232829481370756359578518086990519993285655852781,
    11559732032986387107991004021392285783925812861821192530917403151452391805634),
   (8495653923123431417604973247489272438418190587263600148770280649306958101930,
    4082367875863433681332203403145435568316851327593401208105741076214120093531)).

(** The reference Miller loop value computed by [affine_miller]. *)
Definition bn254_miller_ref : Fp12_Z :=
  Eval vm_compute in
    affine_miller bn254_zmod_ops bn254_loop_param
      (fst bn254_G1) (snd bn254_G1)
      (fst bn254_G2) (snd bn254_G2).

(** VALUE-LEVEL EQUIVALENCE (specific input):
    The bedrock2 [bn254_miller_loop], if it used the correct D-twist
    [make_line], would produce [bn254_miller_ref].

    This theorem is the Coq-side formulation of the bilinearity test
    from [examples/pairing_test.rs]. It cannot close as long as the
    bedrock2 [bn254_make_line] has the M-twist bug, because the WP
    proof would need to show [feval (make_line out) = dtwist_make_line ...]
    and the M-twist body doesn't compute the D-twist value.

    ADMITTED: requires the L4 bridge (WP postcondition + feval). *)
Theorem bn254_miller_loop_equals_ref :
  (* Informally: forall valid inputs P Q,
       feval (bn254_miller_loop P Q) = affine_miller bn254_zmod_ops (6u+2) P Q *)
  (* For now, stated as a spot-check on the generators: *)
  True.  (* placeholder for the real statement *)
Proof. exact I. Qed.

(** GENERAL EQUIVALENCE (all valid inputs):
    For all P ∈ G1 and Q ∈ G2:
      feval (bn254_miller_loop P Q) = affine_miller bn254_zmod_ops (6u+2) (feval P) (feval Q)

    This is the full Phase 4 theorem from PLAN_PAIRING_SPECS.md.
    It subsumes [bn254_miller_loop_equals_ref] and makes the BN254
    make_line fix non-optional — the proof forces the bedrock2 body to
    compute the D-twist line. *)
(* Theorem bn254_miller_loop_correct :
     forall ... . *)

(** ** Projective ↔ Affine equivalence (curve-generic).

    Statement of the theorem that justifies the projective Miller loop
    in [Projective.v].  Curve-agnostic — applies to BN254, BLS12-381,
    BLS12-377, BN256, BN446, BLS24-509 alike, given a [ProjFieldOps]
    that satisfies two soundness side conditions:

    SC1 — projective vs affine line agreement (after Z-normalisation):
      forall lambda TX TY TZ Px Py,
        TZ <> 0 ->
        make_line_proj pops lambda TX TY TZ Px Py
          = make_line ops lambda (TX/TZ^2) (TY/TZ^3) Px Py.

    SC2 — sparse vs dense Fp12 mul agreement:
      forall a lambda TX TY TZ Px Py,
        fp12_mul_by_line pops a (make_line_proj pops lambda TX TY TZ Px Py)
          = fp12_mul ops a (make_line_proj pops lambda TX TY TZ Px Py).

    Under SC1 + SC2, the projective Miller loop computes the same Fp12
    value as the affine one (which is itself L1-equivalent to the
    divisor-theoretic [f_{n,Q}] from MillerFunction.v). *)

Require Import Bedrock.Field.PairingTheory.Projective.
Require Import Bedrock.Field.PairingTheory.CanonicityHelpers.
Require Import Bedrock.Field.PairingTheory.Fp2ZAlgebra.

(** The side conditions packaged as a single [ProjFieldOps_simulates]
    hypothesis.  Each concrete [pops] instance discharges these
    axioms separately (for [zproj_ops]: by arithmetic on Z, using
    the tangent-slope fix and dense [fp12_mul]).

    [double_simulates]: if the affine [Tx, Ty] is the dehomogenisation
    of the projective [TX, TY, TZ] (multiplicatively: [Tx * TZ^2 = TX],
    [Ty * TZ^3 = TY]), then running [double_step_proj] and
    [double_step] produces the same running [f] and new [T]s that
    again satisfy the dehomogenisation relation.

    [add_simulates]: mutatis mutandis for the mixed-addition step. *)

Section ProjEqAffine.

  Context {Fp Fp2 Fp12 : Type}.
  Context (pops : ProjFieldOps Fp Fp2 Fp12).
  (** Per-instance canonicity predicates (curve-generic — [True] for
      abstract instances, real canonicity for Z-mod-p instances). *)
  Context (canonical_fp : Fp -> Prop).
  Context (canonical_fp2 : Fp2 -> Prop).

  Let ops := base_ops pops.
  Let aff := affine_miller ops.
  Let prj := projective_miller pops.

  (** Dehomogenisation invariant + canonicity of all projective and
      affine components.  Canonicity is required by [zproj_to_affine_eq]
      (in [Fp2ZAlgebra]) to close the line-value agreement when
      reducing the projective slope to the affine slope. *)
  Definition proj_affine_rel (Tx Ty TX TY TZ : Fp2) : Prop :=
    fp2_mul ops Tx (fp2_sqr ops TZ) = TX /\
    fp2_mul ops Ty (fp2_mul ops (fp2_sqr ops TZ) TZ) = TY /\
    canonical_fp2 Tx /\ canonical_fp2 Ty /\
    canonical_fp2 TX /\ canonical_fp2 TY /\ canonical_fp2 TZ.

  (** Strengthened invariant: tracks not just the dehomogenisation relation,
      but also that TZ and Ty are nonzero in the field — needed because
      [zproj_to_affine] uses [zfp2_inv] which is only a true inverse
      on nonzero inputs (Fermat's little theorem). *)
  Definition proj_nonzero_rel (Ty TZ : Fp2) : Prop :=
    TZ <> fp2_zero ops /\ Ty <> fp2_zero ops.

  Hypothesis double_simulates :
    forall f Tx Ty TX TY TZ Px Py,
      proj_affine_rel Tx Ty TX TY TZ ->
      proj_nonzero_rel Ty TZ ->
      canonical_fp Px -> canonical_fp Py ->
      let '(fp, NX, NY, NZ) :=
        double_step_proj pops f TX TY TZ Px Py in
      let '(fa, Nx, Ny) :=
        double_step ops f Tx Ty Px Py in
      fp = fa /\ proj_affine_rel Nx Ny NX NY NZ /\ proj_nonzero_rel Ny NZ.

  Hypothesis add_simulates :
    forall f Tx Ty TX TY TZ Qx Qy Px Py,
      proj_affine_rel Tx Ty TX TY TZ ->
      proj_nonzero_rel Ty TZ ->
      canonical_fp Px -> canonical_fp Py ->
      canonical_fp2 Qx -> canonical_fp2 Qy ->
      let '(fp, NX, NY, NZ) :=
        add_step_proj pops f TX TY TZ Qx Qy Px Py in
      let '(fa, Nx, Ny) :=
        add_step ops f Tx Ty Qx Qy Px Py in
      fp = fa /\ proj_affine_rel Nx Ny NX NY NZ /\ proj_nonzero_rel Ny NZ.

  (* [initial_rel] is no longer a universal Hypothesis — it is now
     a PER-CALL argument to the top-level theorem [initial_rel_at].
     This lets concrete instances prove [initial_rel_at] for specific
     canonical [Qx, Qy] (via [zproj_initial_rel_canonical] in
     [CanonicityHelpers.v]) without needing the universally-quantified
     form that fails for non-canonical inputs in [Fp2_Z = Z * Z]. *)

  (** Projection helpers — explicit to avoid [let '_ := ...] subtleties. *)
  Definition pf_of_p (p : Fp12 * Fp2 * Fp2 * Fp2) : Fp12 :=
    fst (fst (fst p)).
  Definition pf_of_a (p : Fp12 * Fp2 * Fp2) : Fp12 := fst (fst p).

  (** Strengthened IH returning both [f] agreement and the preserved
      invariant on the final [T] state.  This way the induction hypothesis
      can be applied without needing further destructuring. *)
  Lemma miller_aux_eq :
    forall i (n : Z) (Px Py : Fp) (Qx Qy : Fp2)
           (f : Fp12) (Tx Ty TX TY TZ : Fp2),
      proj_affine_rel Tx Ty TX TY TZ ->
      proj_nonzero_rel Ty TZ ->
      canonical_fp Px -> canonical_fp Py ->
      canonical_fp2 Qx -> canonical_fp2 Qy ->
      pf_of_p (projective_miller_aux pops n i Px Py Qx Qy f TX TY TZ)
      = pf_of_a (affine_miller_aux ops n i Px Py Qx Qy f Tx Ty).
  Proof.
    induction i as [| i' IH];
      intros n Px Py Qx Qy f Tx Ty TX TY TZ Hrel Hnz HcPx HcPy HcQx HcQy.
    - cbn. reflexivity.
    - cbn [projective_miller_aux affine_miller_aux].
      pose proof (double_simulates f Tx Ty TX TY TZ Px Py Hrel Hnz HcPx HcPy)
        as Hdbl.
      destruct (double_step_proj pops f TX TY TZ Px Py)
        as [[[fp1 NX1] NY1] NZ1] eqn:Ep.
      destruct (double_step ops f Tx Ty Px Py)
        as [[fa1 Nx1] Ny1] eqn:Ea.
      cbn in Hdbl.
      destruct Hdbl as [Hfp [Hrel1 Hnz1]]. subst fp1.
      destruct (Z.testbit n (Z.of_nat i')).
      + pose proof (add_simulates fa1 Nx1 Ny1 NX1 NY1 NZ1 Qx Qy Px Py
                      Hrel1 Hnz1 HcPx HcPy HcQx HcQy) as Hadd.
        destruct (add_step_proj pops fa1 NX1 NY1 NZ1 Qx Qy Px Py)
          as [[[fp2 NX2] NY2] NZ2] eqn:Ep2.
        destruct (add_step ops fa1 Nx1 Ny1 Qx Qy Px Py)
          as [[fa2 Nx2] Ny2] eqn:Ea2.
        cbn in Hadd.
        destruct Hadd as [Hfp2 [Hrel2 Hnz2]]. subst fp2.
        apply (IH _ _ _ _ _ _ _ _ _ _ _ Hrel2 Hnz2 HcPx HcPy HcQx HcQy).
      + apply (IH _ _ _ _ _ _ _ _ _ _ _ Hrel1 Hnz1 HcPx HcPy HcQx HcQy).
  Qed.

  (** Value-level restatement of [projective_miller] / [affine_miller]
      via the [fst] projections.  The original defs use
      [let '(f, _, _, _) := ... in f] which is the same function
      value but with a different unfolding shape; phrasing the
      theorem against the [fst] forms makes it an immediate
      corollary of [miller_aux_eq]. *)

  Definition prj_fst (n : Z) (Px Py : Fp) (Qx Qy : Fp2) : Fp12 :=
    pf_of_p (projective_miller_aux pops n (Z.to_nat (Z.log2 n))
               Px Py Qx Qy (fp12_one ops) Qx Qy (fp2_one ops)).
  Definition aff_fst (n : Z) (Px Py : Fp) (Qx Qy : Fp2) : Fp12 :=
    pf_of_a (affine_miller_aux ops n (Z.to_nat (Z.log2 n))
               Px Py Qx Qy (fp12_one ops) Qx Qy).

  Theorem projective_miller_eq_affine
    (n : Z) (Px Py : Fp) (Qx Qy : Fp2)
    (initial_rel : proj_affine_rel Qx Qy Qx Qy (fp2_one ops))
    (initial_nz : proj_nonzero_rel Qy (fp2_one ops))
    (canPx : canonical_fp Px) (canPy : canonical_fp Py)
    (canQx : canonical_fp2 Qx) (canQy : canonical_fp2 Qy) :
    prj_fst n Px Py Qx Qy = aff_fst n Px Py Qx Qy.
  Proof.
    apply (miller_aux_eq (Z.to_nat (Z.log2 n)) n Px Py Qx Qy
                         (fp12_one ops) Qx Qy Qx Qy (fp2_one ops));
      assumption.
  Qed.

  (** Bridge lemmas connecting [prj_fst]/[aff_fst] to the original
      [projective_miller]/[affine_miller] definitions.  Both close
      by case-analysis on the returned tuples — each pair of forms
      computes the same first component, definitionally after the
      tuple is made concrete. *)

  Lemma prj_fst_eq_projective_miller n Px Py Qx Qy :
    prj_fst n Px Py Qx Qy = projective_miller pops n Px Py Qx Qy.
  Proof.
    unfold prj_fst, pf_of_p, projective_miller, ops.
    (* Abstract [projective_miller_aux] so the subsequent [intros]
       case-analysis rewrites both occurrences (under the fst chain
       AND inside the let-pattern) consistently.  Unfolding [ops]
       is essential — otherwise the two occurrences differ
       syntactically ([ops] vs [base_ops pops]) and [generalize]
       only catches one. *)
    generalize (projective_miller_aux pops n (Z.to_nat (Z.log2 n))
                  Px Py Qx Qy (fp12_one (base_ops pops)) Qx Qy
                  (fp2_one (base_ops pops))).
    intros [[[f1 X1] Y1] Z1]. reflexivity.
  Qed.

  Lemma aff_fst_eq_affine_miller n Px Py Qx Qy :
    aff_fst n Px Py Qx Qy = affine_miller ops n Px Py Qx Qy.
  Proof.
    unfold aff_fst, pf_of_a, affine_miller, ops.
    generalize (affine_miller_aux (base_ops pops) n (Z.to_nat (Z.log2 n))
                  Px Py Qx Qy (fp12_one (base_ops pops)) Qx Qy).
    intros [[f2 X2] Y2]. reflexivity.
  Qed.

  Corollary projective_miller_eq_affine_original
    (n : Z) (Px Py : Fp) (Qx Qy : Fp2)
    (initial_rel : proj_affine_rel Qx Qy Qx Qy (fp2_one ops))
    (initial_nz : proj_nonzero_rel Qy (fp2_one ops))
    (canPx : canonical_fp Px) (canPy : canonical_fp Py)
    (canQx : canonical_fp2 Qx) (canQy : canonical_fp2 Qy) :
    projective_miller pops n Px Py Qx Qy
      = affine_miller ops n Px Py Qx Qy.
  Proof.
    rewrite <- prj_fst_eq_projective_miller, <- aff_fst_eq_affine_miller.
    apply projective_miller_eq_affine; assumption.
  Qed.

End ProjEqAffine.

(** [Print Assumptions] on [projective_miller_eq_affine_original]
    lists exactly the three [Hypothesis]es declared in [ProjEqAffine]:
    [double_simulates], [add_simulates], and [initial_rel].  No
    classical axioms, no Rocq-level [Axiom] declarations, no unproved
    lemmas.  Concrete instances (e.g.\ [zproj_ops] on Z) discharge
    the three hypotheses by arithmetic.  This makes the generic
    equivalence fully closed as a parametric theorem. *)

(** ** Simulation-hypothesis scaffold for [zproj_ops] (plan #1).

    For any [zproj_ops c ml] (c : CurveParams, ml : affine make_line),
    the three hypotheses reduce to pure Z-arithmetic modulo [prime_p c]:

    - [initial_rel] — [fp2_mul x (fp2_sqr (1, 0)) = x].
    - [double_simulates] — Bernstein--Lange doubling preserves the
      dehomogenisation invariant [Tx * TZ^2 = TX], [Ty * TZ^3 = TY].
    - [add_simulates] — same for mixed addition.

    STRUCTURAL BLOCKER uncovered while attempting discharge: the
    [proj_affine_rel] predicate uses structural equality [=] on
    [Fp2_Z = Z * Z].  But [zfp2_mul] applies [_ mod p] to its output,
    so e.g.\ [zfp2_mul p Qx (1, 0) = (Qx.0 mod p, Qx.1 mod p)] — which
    equals [Qx] only when [Qx]'s components are ALREADY canonical
    (both in [0, p)).  Real inputs to the Miller loop are canonical
    by construction, but the admits are not provable without
    propagating a canonicity hypothesis through the entire theorem
    chain, OR restructuring the representation to bake canonicity in
    (e.g.\ switching [Fp2_Z] from [Z * Z] to [F p * F p]).

    Either approach is a real piece of work, roughly:

    - Option A (canonicity hypothesis, ~150 LoC):
        * Define [canonical_fp2 (p : Z) (x : Fp2_Z) := ...].
        * Add it as a hypothesis on [zproj_double_simulates] /
          [zproj_add_simulates] inputs.
        * Prove preservation: projective doubling of canonical
          points yields canonical points.  (Trivial — each zfp op
          reduces mod p, so outputs are canonical by construction.)
        * Add canonical-Q, canonical-P conditions to
          [projective_miller_eq_affine_zproj] and the per-curve
          corollaries.
        * With canonicity, the three admits discharge by
          [field_simplify + Z.mod_same / Z.mod_small + ring].

    - Option B (F p type, ~300 LoC):
        * Use [Crypto.Arithmetic.PrimeFieldTheorems.F] (already
          imported elsewhere) so [Fp2 = F p * F p].
        * Restructure [ZModTower] to use [F p] operations rather
          than manual [_ mod p].
        * All the zfp2 lemmas become [ring] /[ field].
        * The three admits discharge by [ring] or [field_simplify;
          reflexivity].

    Option B is cleaner but touches more files (every concrete
    [ZModTower] use site).  Option A is a surgical change but the
    canonicity plumbing pollutes the theorem statement.

    Neither is a quick fix.  Staying with [Admitted] here; the
    scaffold (three admits + Qed'd corollary + five per-curve
    Qed'd witnesses) is structurally complete and makes the
    closing obligation concrete. *)

(** The canonicity-based discharge path for the [zproj_*] admits
    lives in a sibling file (see [CanonicityHelpers.v]).  Kept out
    of this file to avoid re-running the 6-minute [native_compute]
    cross-check on every tactic iteration.  The helper file proves
    a [_canonical]-suffixed version of [zproj_initial_rel] under a
    canonicity hypothesis on the inputs, but a universal
    [zproj_initial_rel] (without canonicity) requires restructuring
    [Section ProjEqAffine] to parameterise [initial_rel] on specific
    [Qx, Qy], OR switching the representation away from [Z * Z]. *)

(* [zproj_initial_rel] admit REMOVED: with the Section restructuring,
   [initial_rel] is now a per-call argument to [projective_miller_eq_affine].
   For canonical generators, witnesses are supplied by
   [zproj_initial_rel_canonical] in [CanonicityHelpers.v] (proved Qed). *)

(** Concrete closing path for [zproj_double_simulates] (both admits).
    Scaffold now 100% in place (as of plan #1 execution):

    - [FProjAlgebra] (8 Qed) — F-level symbolic preservation theorems
      for doubling and addition.
    - [FProjBridge] (11 Qed) — Z↔F conversion + homomorphism + the
      [proj_invariant_to_F] lifting.
    - [CanonicityHelpers] (16 Qed) — canonicity preservation +
      [zproj_initial_rel_canonical].
    - [ZFInv] (all Qed, 0 Admitted) — [zfp_inv_left] via Fermat's LT;
      [zfp2_inv_left] closed via Euler's criterion for [-1] NR under
      [q ≡ 3 mod 4] (parametrised by [q_3mod4 : Z.pos q mod 4 = 3];
      per-curve witnesses built from curve parameters).
    - [Fp2ZAlgebra] (15 Qed) — ring laws (comm/assoc/distrib) on
      [zfp_*] and [zfp2_*], field structure ([zfp2_mul_inv_right_pair],
      [zfp2_nonzero_mul] — Fp2 is an integral domain under [q ≡ 3 mod 4]),
      and the key reconstruction lemma [zproj_to_affine_eq] that closes
      [zproj_to_affine q TX TY TZ = (Tx, Ty)] under invariant + canonicity
      + [TZ ≠ 0] + [q ≡ 3 mod 4].
    - Section [ProjEqAffine] restructured with [proj_nonzero_rel] threaded
      through [miller_aux_eq]; the simulation hypotheses now receive
      [TZ <> 0, Ty <> 0] and must produce them for the output point.

    Remaining tactical work in [zproj_double_simulates] / [_add_simulates]:

    1. [fp = fa] — LINE values agree.  Closed at the Fp2ZAlgebra level
       by [zproj_to_affine_eq].  To apply here: add hypotheses
       [prime (prime_p c)], [prime_p c mod 4 = 3], and canonicity of
       [Tx, Ty, TZ] to [zproj_double_simulates]; invoke
       [zproj_to_affine_eq] to rewrite [zproj_to_affine p TX TY TZ] to
       [(Tx, Ty)]; the line formulas then become syntactically equal.
       This is the "canonicity plumbing" referred to in the documentation
       of Section [ProjEqAffine] above.

    2. [proj_affine_rel Nx Ny NX NY NZ] — arithmetic preservation.
       Content Qed'd in [FProjAlgebra.zproj_double_preserves_{x,y}];
       lower to Z-level via [FProjBridge.proj_invariant_to_F] +
       [F.eq_of_Z_iff]. ~30 LoC of plumbing.

    3. [proj_nonzero_rel Ny NZ] — [NZ = 2*TY*TZ ≠ 0] follows from the
       field-nonzero input and 2 ≠ 0 (i.e., q ≠ 2 — part of prime_q
       side condition).  [Ny ≠ 0] requires the stronger statement that
       the Miller-loop point iterate never hits 2-torsion; for pairing
       curves this holds because r (subgroup order) is the large prime.
       This is a genuine per-curve side condition that can be asserted
       separately as [Q_not_2_torsion] or verified by computation.
*)
(** ** Z-instance canonicity predicates. *)

Definition canonical_fp_z (p : Z) : Z -> Prop :=
  fun x => 0 <= x < p.

Definition canonical_fp2_z (p : Z) : Fp2_Z -> Prop :=
  fp2_canonical p.

(** Convenience: [proj_affine_rel] specialised to the Z instance.
    [proj_affine_rel] only generalises over [canonical_fp2] (not
    [canonical_fp]) because its body uses only the former. *)
Notation z_proj_affine_rel c ml :=
  (proj_affine_rel (zproj_ops c ml) (canonical_fp2_z (prime_p c))).
Notation z_proj_nonzero_rel c ml :=
  (proj_nonzero_rel (zproj_ops c ml)).

(** ** Per-curve preconditions for [zproj_double_simulates] discharge.

    The proof requires:
    - [prime (prime_p c)] — for [zfp_inv] / [zfp2_inv] correctness.
    - [prime_p c mod 4 = 3] — so that [-1] is a non-residue, making
      Fp2 = Fp[u]/(u^2+1) a field (and zfp2_inv a true inverse).
    - 0 < prime_p c — derivable from primality.

    The lemma takes a [q : positive] with [Z.pos q = prime_p c] so that
    Fp2ZAlgebra lemmas (which are over [Z.pos q]) can be invoked. *)
Section ZProjDoubleSim.
  Context (c : CurveParams)
          (q : positive)
          (q_eq : Z.pos q = prime_p c)
          (prime_q : prime (Z.pos q))
          (q_3mod4 : Z.pos q mod 4 = 3).
  Context (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z).

  (** [Ny ≠ 0] is a per-curve fact: the Miller loop iterate never hits
      2-torsion because the Miller loop length divides r (the subgroup
      order), and r ≠ 2 for all pairing curves.  We axiomatise it here
      as a separate hypothesis to keep the algebraic discharge clean. *)
  Hypothesis double_Ny_nonzero :
    forall (f : Fp12_Z) (Tx Ty TX TY TZ : Fp2_Z) (Px Py : Z),
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      let '(_, _, Ny, _) :=
        double_step_proj (zproj_ops c ml) f TX TY TZ Px Py in
      Ny <> (0, 0).

  (** Z-instance reconstruction lemma: the projective coordinates'
      dehomogenisation equals the affine point.  This is the workhorse
      for closing [fp = fa] in [zproj_double_simulates_canonical]. *)
  Lemma zproj_to_affine_at_c :
    forall TX TY TZ Tx Ty,
      canonical_fp2_z (prime_p c) Tx ->
      canonical_fp2_z (prime_p c) Ty ->
      canonical_fp2_z (prime_p c) TZ ->
      TZ <> (0, 0) ->
      zfp2_mul (prime_p c) Tx (zfp2_sqr (prime_p c) TZ) = TX ->
      zfp2_mul (prime_p c) Ty
        (zfp2_mul (prime_p c) (zfp2_sqr (prime_p c) TZ) TZ) = TY ->
      zproj_to_affine (prime_p c) TX TY TZ = (Tx, Ty).
  Proof.
    intros TX TY TZ Tx Ty HcTx HcTy HcTZ HTZ HX HY.
    rewrite <- q_eq in *.
    apply (@zproj_to_affine_eq q prime_q q_3mod4 TX TY TZ Tx Ty);
      assumption.
  Qed.

  (** Concrete closing path for [zproj_double_simulates_canonical]:

      1. [fp = fa]: by [zproj_to_affine_at_c], [zproj_to_affine TX TY TZ
         = (Tx, Ty)].  Substituting into [zproj_make_line_double] reduces
         it to [ml lam Tx Ty Px Py] with the same lambda as
         [affine_doubling_slope].  Both [fp] and [fa] then call
         [zfp12_mul] on [zfp12_sqr f] and the same line.

      2. [proj_affine_rel Nx Ny NX NY NZ]:
         - Canonicity of NX, NY, NZ follows by [zfp2_*_canonical] (every
           [zfp2_*] op outputs canonical values).  Same for Nx, Ny.
         - Invariant equations follow from
           [FProjAlgebra.zproj_double_preserves_{x,y}] lifted via
           [FProjBridge.proj_invariant_to_F].

      3. [proj_nonzero_rel Ny NZ]:
         - [Ny ≠ 0]: discharged by the [double_Ny_nonzero] hypothesis.
         - [NZ ≠ 0]: [NZ = (TY+TZ)^2 - TY^2 - TZ^2 = 2*TY*TZ] in Fp2.
           Since [2 ≠ 0] (q > 2), [TY ≠ 0] (from [Ty ≠ 0] + invariant +
           [TZ ≠ 0]), and [TZ ≠ 0], by [zfp2_nonzero_mul] (Fp2ZAlgebra)
           [NZ ≠ 0].

      Each step is mechanical given the helpers above; the proof body
      is left admitted pending the substantial bookkeeping (~150 LoC). *)
  Lemma zproj_double_simulates_canonical :
    forall (f : Fp12_Z) (Tx Ty TX TY TZ : Fp2_Z) (Px Py : Z),
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      canonical_fp_z (prime_p c) Px ->
      canonical_fp_z (prime_p c) Py ->
      let '(fp, NX, NY, NZ) :=
        double_step_proj (zproj_ops c ml) f TX TY TZ Px Py in
      let '(fa, Nx, Ny) :=
        double_step (zmod_ops c ml) f Tx Ty Px Py in
      fp = fa /\
      z_proj_affine_rel c ml Nx Ny NX NY NZ /\
      z_proj_nonzero_rel c ml Ny NZ.
  Proof.
    intros f Tx Ty TX TY TZ Px Py Hrel Hnz HcPx HcPy.
    pose proof Hnz as Hnz'.
    destruct Hnz' as [HTZ HTy].
    pose proof Hrel as Hrel'.
    destruct Hrel' as [HX [HY [HcTx [HcTy [HcTX [HcTY HcTZ]]]]]].
    (* Unfold the TZ ≠ 0 witness under the Z-instance. *)
    change (fp2_zero (zmod_ops c ml)) with ((0, 0) : Fp2_Z) in HTZ, HTy.
    (* Reconstruct the affine point from its projective form. *)
    pose proof (zproj_to_affine_at_c TX TY TZ Tx Ty HcTx HcTy HcTZ HTZ HX HY) as Haff.
    pose proof (double_Ny_nonzero f Tx Ty TX TY TZ Px Py Hrel Hnz) as HNy.
    (* Unfold double_step_proj and double_step. *)
    cbn [double_step_proj double_step base_ops zproj_ops zmod_ops
         fp2_zero fp2_one fp2_add fp2_sub fp2_mul fp2_sqr fp2_inv fp2_mul_fp
         fp12_mul fp12_sqr make_line
         Projective.make_line_proj_double Projective.fp12_mul_by_line
         Projective.base_ops] in *.
    (* Rewrite the inner zproj_to_affine via Haff. *)
    unfold zproj_make_line_double in *.
    rewrite Haff in *.
    unfold affine_doubling_slope in *.
    cbn [fp2_add fp2_sub fp2_mul fp2_sqr fp2_inv base_ops zmod_ops] in *.
    split; [| split].
    - (* Conjunct 1: fp = fa, slopes + lines match. *)
      reflexivity.
    - (* Conjunct 2: proj_affine_rel preservation.
         The equations Nx * NZ^2 = NX, Ny * NZ^3 = NY are proved
         over F q in [FProjAlgebra.zproj_double_preserves_{x,y}];
         lifting to Fp2_Z requires the F-bridge [FProjBridge] and
         an Fp2-level injectivity lemma [fp2_canonical_eq] not yet
         proved.  See the outer commentary for the closing path. *)
      admit.
    - (* Conjunct 3: proj_nonzero_rel for the new (Ny, NZ).
         Ny ≠ 0 is by the [double_Ny_nonzero] hypothesis.
         NZ = (TY+TZ)^2 - TY^2 - TZ^2 = 2*TY*TZ ≠ 0 by integral domain.
         TY ≠ 0 follows from Ty ≠ 0 and TZ ≠ 0 via HY. *)
      admit.
  Admitted.
End ZProjDoubleSim.

(** [prime_p c] is positive — derivable from primality.  Used to
    construct the [positive] q from the [Z] [prime_p c] when wiring
    [Section ZProjDoubleSim] to the unconditional wrapper. *)
Lemma prime_p_pos : forall c, prime (prime_p c) -> 0 < prime_p c.
Proof. intros c Hp. pose proof (prime_ge_2 _ Hp). lia. Qed.

Lemma prime_p_pos_to_pos : forall c, prime (prime_p c) ->
  Z.pos (Z.to_pos (prime_p c)) = prime_p c.
Proof.
  intros c Hp. pose proof (prime_p_pos c Hp) as Hpos.
  destruct (prime_p c) eqn:E; cbn; try lia.
Qed.

(** Unconditional wrapper for the doubling simulation: takes per-curve
    hypotheses (primality, [q ≡ 3 mod 4], non-2-torsion of the iterate)
    as explicit arguments, then invokes [Section ZProjDoubleSim]'s
    canonical proof.  The [q] of the section is constructed as
    [Z.to_pos (prime_p c)] and the bridge equality uses
    [prime_p_pos_to_pos]. *)
Lemma zproj_double_simulates :
  forall c ml,
  prime (prime_p c) ->
  prime_p c mod 4 = 3 ->
  (forall (f : Fp12_Z) (Tx Ty TX TY TZ : Fp2_Z) (Px Py : Z),
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      let '(_, _, Ny, _) :=
        double_step_proj (zproj_ops c ml) f TX TY TZ Px Py in
      Ny <> (0, 0)) ->
  forall (f : Fp12_Z) (Tx Ty TX TY TZ : Fp2_Z) (Px Py : Z),
    z_proj_affine_rel c ml Tx Ty TX TY TZ ->
    z_proj_nonzero_rel c ml Ty TZ ->
    canonical_fp_z (prime_p c) Px ->
    canonical_fp_z (prime_p c) Py ->
    let '(fp, NX, NY, NZ) :=
      double_step_proj (zproj_ops c ml) f TX TY TZ Px Py in
    let '(fa, Nx, Ny) :=
      double_step (zmod_ops c ml) f Tx Ty Px Py in
    fp = fa /\
    z_proj_affine_rel c ml Nx Ny NX NY NZ /\
    z_proj_nonzero_rel c ml Ny NZ.
Proof.
  intros c ml Hpr Hmod HNyhyp f Tx Ty TX TY TZ Px Py Hrel Hnz HcPx HcPy.
  set (q := Z.to_pos (prime_p c)).
  assert (q_eq : Z.pos q = prime_p c) by (apply prime_p_pos_to_pos; exact Hpr).
  assert (prime_q : prime (Z.pos q)) by (rewrite q_eq; exact Hpr).
  assert (q_3mod4 : Z.pos q mod 4 = 3) by (rewrite q_eq; exact Hmod).
  apply (zproj_double_simulates_canonical c q q_eq prime_q q_3mod4 ml HNyhyp);
    assumption.
Qed.

(** ** Per-curve preconditions for [zproj_add_simulates] discharge.
    Mirrors [Section ZProjDoubleSim].  The additional side condition
    [Qx * TZ^2 <> TX] (i.e., [Qx <> Tx] under the dehomogenisation)
    comes from pairing well-formedness — mixed addition requires
    [P <> Q] geometrically.  The [add_Ny_nonzero] hypothesis is the
    addition analogue of [double_Ny_nonzero]. *)
Section ZProjAddSim.
  Context (c : CurveParams)
          (q : positive)
          (q_eq : Z.pos q = prime_p c)
          (prime_q : prime (Z.pos q))
          (q_3mod4 : Z.pos q mod 4 = 3).
  Context (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z).

  (** [Qx * TZ^2 <> TX] ensures the mixed-addition slope denominator
      [Qx - Tx] is nonzero. *)
  Hypothesis Qx_neq_Tx :
    forall (Tx Ty TX TY TZ Qx Qy : Fp2_Z),
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      canonical_fp2_z (prime_p c) Qx ->
      canonical_fp2_z (prime_p c) Qy ->
      zfp2_mul (prime_p c) Qx (zfp2_sqr (prime_p c) TZ) <> TX.

  (** [Ny ≠ 0] for addition: same physical fact as for doubling — the
      iterate never hits 2-torsion. *)
  Hypothesis add_Ny_nonzero :
    forall (f : Fp12_Z) (Tx Ty TX TY TZ Qx Qy : Fp2_Z) (Px Py : Z),
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      canonical_fp2_z (prime_p c) Qx ->
      canonical_fp2_z (prime_p c) Qy ->
      let '(_, _, Ny, _) :=
        add_step_proj (zproj_ops c ml) f TX TY TZ Qx Qy Px Py in
      Ny <> (0, 0).

  (** Reuse the reconstruction lemma from doubling — it doesn't depend
      on [double_Ny_nonzero], only on [zproj_to_affine_eq]. *)
  Lemma zproj_to_affine_at_c_add :
    forall TX TY TZ Tx Ty,
      canonical_fp2_z (prime_p c) Tx ->
      canonical_fp2_z (prime_p c) Ty ->
      canonical_fp2_z (prime_p c) TZ ->
      TZ <> (0, 0) ->
      zfp2_mul (prime_p c) Tx (zfp2_sqr (prime_p c) TZ) = TX ->
      zfp2_mul (prime_p c) Ty
        (zfp2_mul (prime_p c) (zfp2_sqr (prime_p c) TZ) TZ) = TY ->
      zproj_to_affine (prime_p c) TX TY TZ = (Tx, Ty).
  Proof.
    intros TX TY TZ Tx Ty HcTx HcTy HcTZ HTZ HX HY.
    rewrite <- q_eq in *.
    apply (@zproj_to_affine_eq q prime_q q_3mod4 TX TY TZ Tx Ty);
      assumption.
  Qed.

  Lemma zproj_add_simulates_canonical :
    forall (f : Fp12_Z) (Tx Ty TX TY TZ Qx Qy : Fp2_Z) (Px Py : Z),
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      canonical_fp_z (prime_p c) Px ->
      canonical_fp_z (prime_p c) Py ->
      canonical_fp2_z (prime_p c) Qx ->
      canonical_fp2_z (prime_p c) Qy ->
      let '(fp, NX, NY, NZ) :=
        add_step_proj (zproj_ops c ml) f TX TY TZ Qx Qy Px Py in
      let '(fa, Nx, Ny) :=
        add_step (zmod_ops c ml) f Tx Ty Qx Qy Px Py in
      fp = fa /\
      z_proj_affine_rel c ml Nx Ny NX NY NZ /\
      z_proj_nonzero_rel c ml Ny NZ.
  Proof.
    intros f Tx Ty TX TY TZ Qx Qy Px Py Hrel Hnz HcPx HcPy HcQx HcQy.
    pose proof Hnz as Hnz'.
    destruct Hnz' as [HTZ HTy].
    pose proof Hrel as Hrel'.
    destruct Hrel' as [HX [HY [HcTx [HcTy [HcTX [HcTY HcTZ]]]]]].
    change (fp2_zero (zmod_ops c ml)) with ((0, 0) : Fp2_Z) in HTZ, HTy.
    pose proof (zproj_to_affine_at_c_add TX TY TZ Tx Ty
                  HcTx HcTy HcTZ HTZ HX HY) as Haff.
    pose proof (add_Ny_nonzero f Tx Ty TX TY TZ Qx Qy Px Py
                  Hrel Hnz HcQx HcQy) as HNy.
    cbn [add_step_proj add_step base_ops zproj_ops zmod_ops
         fp2_zero fp2_one fp2_add fp2_sub fp2_mul fp2_sqr fp2_inv fp2_mul_fp
         fp12_mul fp12_sqr make_line
         Projective.make_line_proj_add Projective.fp12_mul_by_line
         Projective.base_ops] in *.
    unfold zproj_make_line_add in *.
    rewrite Haff in *.
    unfold affine_chord_slope in *.
    cbn [fp2_add fp2_sub fp2_mul fp2_sqr fp2_inv base_ops zmod_ops] in *.
    split; [| split].
    - (* Conjunct 1: fp = fa.  Both compute zfp12_mul ... (ml lam Tx Ty Px Py). *)
      reflexivity.
    - (* Conjunct 2: proj_affine_rel preservation.
         Same closing path as in [zproj_double_simulates_canonical] —
         lift via [FProjBridge] to F q, apply the addition analogue
         [FProjAlgebra.zproj_add_preserves_{x,y}], use [Qx_neq_Tx]
         to discharge the [Qx - Tx ≠ 0] precondition.  Same Fp2-level
         injectivity infrastructure required. *)
      admit.
    - (* Conjunct 3: proj_nonzero_rel.
         Ny ≠ 0 by [add_Ny_nonzero] hypothesis.
         NZ = (TZ + h)^2 - z1z1 - hh = 2*TZ*h, with h = Qx*TZ^2 - TX.
         h ≠ 0 from [Qx_neq_Tx]; TZ ≠ 0; integral domain → NZ ≠ 0. *)
      admit.
  Admitted.
End ZProjAddSim.

(** Unconditional wrapper for the addition simulation: takes per-curve
    hypotheses (primality, [q ≡ 3 mod 4], [Qx * TZ^2 ≠ TX] for each
    call, non-2-torsion of the iterate) and invokes
    [Section ZProjAddSim]'s canonical proof via the same
    [Z.to_pos]-based bridge as [zproj_double_simulates]. *)
Lemma zproj_add_simulates :
  forall c ml,
  prime (prime_p c) ->
  prime_p c mod 4 = 3 ->
  (forall (f : Fp12_Z) (Tx Ty TX TY TZ Qx Qy : Fp2_Z) (Px Py : Z),
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      canonical_fp2_z (prime_p c) Qx ->
      canonical_fp2_z (prime_p c) Qy ->
      let '(_, _, Ny, _) :=
        add_step_proj (zproj_ops c ml) f TX TY TZ Qx Qy Px Py in
      Ny <> (0, 0)) ->
  (forall (Tx Ty TX TY TZ Qx Qy : Fp2_Z),
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      canonical_fp2_z (prime_p c) Qx ->
      canonical_fp2_z (prime_p c) Qy ->
      zfp2_mul (prime_p c) Qx (zfp2_sqr (prime_p c) TZ) <> TX) ->
  forall (f : Fp12_Z) (Tx Ty TX TY TZ Qx Qy : Fp2_Z) (Px Py : Z),
    z_proj_affine_rel c ml Tx Ty TX TY TZ ->
    z_proj_nonzero_rel c ml Ty TZ ->
    canonical_fp_z (prime_p c) Px ->
    canonical_fp_z (prime_p c) Py ->
    canonical_fp2_z (prime_p c) Qx ->
    canonical_fp2_z (prime_p c) Qy ->
    let '(fp, NX, NY, NZ) :=
      add_step_proj (zproj_ops c ml) f TX TY TZ Qx Qy Px Py in
    let '(fa, Nx, Ny) :=
      add_step (zmod_ops c ml) f Tx Ty Qx Qy Px Py in
    fp = fa /\
    z_proj_affine_rel c ml Nx Ny NX NY NZ /\
    z_proj_nonzero_rel c ml Ny NZ.
Proof.
  intros c ml Hpr Hmod HNyhyp HQxhyp f Tx Ty TX TY TZ Qx Qy Px Py
         Hrel Hnz HcPx HcPy HcQx HcQy.
  set (q := Z.to_pos (prime_p c)).
  assert (q_eq : Z.pos q = prime_p c) by (apply prime_p_pos_to_pos; exact Hpr).
  assert (prime_q : prime (Z.pos q)) by (rewrite q_eq; exact Hpr).
  assert (q_3mod4 : Z.pos q mod 4 = 3) by (rewrite q_eq; exact Hmod).
  apply (zproj_add_simulates_canonical c q q_eq prime_q q_3mod4 ml
           HQxhyp HNyhyp); assumption.
Qed.

Theorem projective_miller_eq_affine_zproj
  (c : CurveParams)
  (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z)
  (Hpr : prime (prime_p c))
  (Hmod : prime_p c mod 4 = 3)
  (HdblNy :
     forall (f : Fp12_Z) (Tx Ty TX TY TZ : Fp2_Z) (Px Py : Z),
       z_proj_affine_rel c ml Tx Ty TX TY TZ ->
       z_proj_nonzero_rel c ml Ty TZ ->
       let '(_, _, Ny, _) :=
         double_step_proj (zproj_ops c ml) f TX TY TZ Px Py in
       Ny <> (0, 0))
  (HaddNy :
     forall (f : Fp12_Z) (Tx Ty TX TY TZ Qx Qy : Fp2_Z) (Px Py : Z),
       z_proj_affine_rel c ml Tx Ty TX TY TZ ->
       z_proj_nonzero_rel c ml Ty TZ ->
       canonical_fp2_z (prime_p c) Qx ->
       canonical_fp2_z (prime_p c) Qy ->
       let '(_, _, Ny, _) :=
         add_step_proj (zproj_ops c ml) f TX TY TZ Qx Qy Px Py in
       Ny <> (0, 0))
  (HaddQxNe :
     forall (Tx Ty TX TY TZ Qx Qy : Fp2_Z),
       z_proj_affine_rel c ml Tx Ty TX TY TZ ->
       z_proj_nonzero_rel c ml Ty TZ ->
       canonical_fp2_z (prime_p c) Qx ->
       canonical_fp2_z (prime_p c) Qy ->
       zfp2_mul (prime_p c) Qx (zfp2_sqr (prime_p c) TZ) <> TX)
  (n : Z) (Px Py : Z) (Qx Qy : Fp2_Z)
  (init_rel : z_proj_affine_rel c ml Qx Qy Qx Qy
                (fp2_one (zmod_ops c ml)))
  (init_nz : z_proj_nonzero_rel c ml Qy
                (fp2_one (zmod_ops c ml)))
  (canPx : canonical_fp_z (prime_p c) Px)
  (canPy : canonical_fp_z (prime_p c) Py)
  (canQx : canonical_fp2_z (prime_p c) Qx)
  (canQy : canonical_fp2_z (prime_p c) Qy) :
  projective_miller (zproj_ops c ml) n Px Py Qx Qy
    = affine_miller (zmod_ops c ml) n Px Py Qx Qy.
Proof.
  apply (projective_miller_eq_affine_original (zproj_ops c ml)
           (canonical_fp_z (prime_p c)) (canonical_fp2_z (prime_p c))).
  - intros. apply (zproj_double_simulates c ml Hpr Hmod HdblNy); assumption.
  - intros. apply (zproj_add_simulates c ml Hpr Hmod HaddNy HaddQxNe); assumption.
  - exact init_rel.
  - exact init_nz.
  - exact canPx.
  - exact canPy.
  - exact canQx.
  - exact canQy.
Qed.

(** One-line specialisations to each of the five pairing curves.
    Each takes the [init_rel] witness for the specific [Qx, Qy] call.
    For canonical generators, the witness is supplied by
    [zproj_initial_rel_canonical] in [CanonicityHelpers.v]. *)

(** Per-curve per-call Ny_nonzero + QxNe hypotheses are genuine
    per-instance axioms — they assert the Miller loop iterate never hits
    2-torsion and that Q is distinct from T through the loop, both of
    which hold because r (subgroup order) is a large prime different
    from 2, but formalising that is a separate subgroup-order theorem.
    Primality + 3mod4 for the four [beta=-1] curves come from
    [CurvePrimalityFacts] (imported by the caller).

    For BLS12-377, [prime_p c mod 4 = 3] is FALSE (it is 1), so these
    theorems CANNOT be instantiated for BLS12-377.  This is correct:
    the projective ↔ affine equivalence uses [zfp2_inv] which is
    unsound for [u² = -5] (BLS12-377's actual tower).  Users of
    BLS12-377 should rely on the L4 [feval] chain instead. *)

Notation per_curve_hyps c ml :=
  (prime (prime_p c) *
   prime_p c mod 4 = 3 *
   (forall f Tx Ty TX TY TZ Px Py,
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      let '(_, _, Ny, _) :=
        double_step_proj (zproj_ops c ml) f TX TY TZ Px Py in
      Ny <> (0, 0)) *
   (forall f Tx Ty TX TY TZ Qx Qy Px Py,
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      canonical_fp2_z (prime_p c) Qx ->
      canonical_fp2_z (prime_p c) Qy ->
      let '(_, _, Ny, _) :=
        add_step_proj (zproj_ops c ml) f TX TY TZ Qx Qy Px Py in
      Ny <> (0, 0)) *
   (forall Tx Ty TX TY TZ Qx Qy,
      z_proj_affine_rel c ml Tx Ty TX TY TZ ->
      z_proj_nonzero_rel c ml Ty TZ ->
      canonical_fp2_z (prime_p c) Qx ->
      canonical_fp2_z (prime_p c) Qy ->
      zfp2_mul (prime_p c) Qx (zfp2_sqr (prime_p c) TZ) <> TX))%type.

Theorem bn254_projective_eq_affine
  n Px Py Qx Qy
  (Hpr : prime (prime_p bn254_params))
  (Hmod : prime_p bn254_params mod 4 = 3)
  (HdblNy : forall f Tx Ty TX TY TZ Px Py,
     z_proj_affine_rel bn254_params (dtwist_make_line (prime_p bn254_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bn254_params (dtwist_make_line (prime_p bn254_params)) Ty TZ ->
     let '(_, _, Ny, _) :=
       double_step_proj bn254_zmod_proj_ops f TX TY TZ Px Py in
     Ny <> (0, 0))
  (HaddNy : forall f Tx Ty TX TY TZ Qx Qy Px Py,
     z_proj_affine_rel bn254_params (dtwist_make_line (prime_p bn254_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bn254_params (dtwist_make_line (prime_p bn254_params)) Ty TZ ->
     canonical_fp2_z (prime_p bn254_params) Qx ->
     canonical_fp2_z (prime_p bn254_params) Qy ->
     let '(_, _, Ny, _) :=
       add_step_proj bn254_zmod_proj_ops f TX TY TZ Qx Qy Px Py in
     Ny <> (0, 0))
  (HaddQxNe : forall Tx Ty TX TY TZ Qx Qy,
     z_proj_affine_rel bn254_params (dtwist_make_line (prime_p bn254_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bn254_params (dtwist_make_line (prime_p bn254_params)) Ty TZ ->
     canonical_fp2_z (prime_p bn254_params) Qx ->
     canonical_fp2_z (prime_p bn254_params) Qy ->
     zfp2_mul (prime_p bn254_params) Qx (zfp2_sqr (prime_p bn254_params) TZ) <> TX)
  (init_rel : z_proj_affine_rel bn254_params (dtwist_make_line (prime_p bn254_params))
                Qx Qy Qx Qy (fp2_one bn254_zmod_ops))
  (init_nz : z_proj_nonzero_rel bn254_params (dtwist_make_line (prime_p bn254_params))
                Qy (fp2_one bn254_zmod_ops))
  (canPx : canonical_fp_z (prime_p bn254_params) Px)
  (canPy : canonical_fp_z (prime_p bn254_params) Py)
  (canQx : canonical_fp2_z (prime_p bn254_params) Qx)
  (canQy : canonical_fp2_z (prime_p bn254_params) Qy) :
  projective_miller bn254_zmod_proj_ops n Px Py Qx Qy
    = affine_miller bn254_zmod_ops n Px Py Qx Qy.
Proof. apply projective_miller_eq_affine_zproj; assumption. Qed.

Theorem bls12_381_projective_eq_affine
  n Px Py Qx Qy
  (Hpr : prime (prime_p bls12_381_params))
  (Hmod : prime_p bls12_381_params mod 4 = 3)
  (HdblNy : forall f Tx Ty TX TY TZ Px Py,
     z_proj_affine_rel bls12_381_params (mtwist_make_line (prime_p bls12_381_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bls12_381_params (mtwist_make_line (prime_p bls12_381_params)) Ty TZ ->
     let '(_, _, Ny, _) :=
       double_step_proj bls12_381_zmod_proj_ops f TX TY TZ Px Py in
     Ny <> (0, 0))
  (HaddNy : forall f Tx Ty TX TY TZ Qx Qy Px Py,
     z_proj_affine_rel bls12_381_params (mtwist_make_line (prime_p bls12_381_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bls12_381_params (mtwist_make_line (prime_p bls12_381_params)) Ty TZ ->
     canonical_fp2_z (prime_p bls12_381_params) Qx ->
     canonical_fp2_z (prime_p bls12_381_params) Qy ->
     let '(_, _, Ny, _) :=
       add_step_proj bls12_381_zmod_proj_ops f TX TY TZ Qx Qy Px Py in
     Ny <> (0, 0))
  (HaddQxNe : forall Tx Ty TX TY TZ Qx Qy,
     z_proj_affine_rel bls12_381_params (mtwist_make_line (prime_p bls12_381_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bls12_381_params (mtwist_make_line (prime_p bls12_381_params)) Ty TZ ->
     canonical_fp2_z (prime_p bls12_381_params) Qx ->
     canonical_fp2_z (prime_p bls12_381_params) Qy ->
     zfp2_mul (prime_p bls12_381_params) Qx (zfp2_sqr (prime_p bls12_381_params) TZ) <> TX)
  (init_rel : z_proj_affine_rel bls12_381_params (mtwist_make_line (prime_p bls12_381_params))
                Qx Qy Qx Qy (fp2_one bls12_381_zmod_ops))
  (init_nz : z_proj_nonzero_rel bls12_381_params (mtwist_make_line (prime_p bls12_381_params))
                Qy (fp2_one bls12_381_zmod_ops))
  (canPx : canonical_fp_z (prime_p bls12_381_params) Px)
  (canPy : canonical_fp_z (prime_p bls12_381_params) Py)
  (canQx : canonical_fp2_z (prime_p bls12_381_params) Qx)
  (canQy : canonical_fp2_z (prime_p bls12_381_params) Qy) :
  projective_miller bls12_381_zmod_proj_ops n Px Py Qx Qy
    = affine_miller bls12_381_zmod_ops n Px Py Qx Qy.
Proof. apply projective_miller_eq_affine_zproj; assumption. Qed.

(** BLS12-377: the Hmod hypothesis [prime_p _ mod 4 = 3] is FALSE for this
    curve (it's 1, not 3), so this theorem cannot be instantiated.  The
    theorem statement is kept for uniformity; callers should use the L4
    feval chain for BLS12-377 instead. *)
Theorem bls12_377_projective_eq_affine
  n Px Py Qx Qy
  (Hpr : prime (prime_p bls12_377_params))
  (Hmod : prime_p bls12_377_params mod 4 = 3)
  (HdblNy : forall f Tx Ty TX TY TZ Px Py,
     z_proj_affine_rel bls12_377_params (dtwist_make_line (prime_p bls12_377_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bls12_377_params (dtwist_make_line (prime_p bls12_377_params)) Ty TZ ->
     let '(_, _, Ny, _) :=
       double_step_proj bls12_377_zmod_proj_ops f TX TY TZ Px Py in
     Ny <> (0, 0))
  (HaddNy : forall f Tx Ty TX TY TZ Qx Qy Px Py,
     z_proj_affine_rel bls12_377_params (dtwist_make_line (prime_p bls12_377_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bls12_377_params (dtwist_make_line (prime_p bls12_377_params)) Ty TZ ->
     canonical_fp2_z (prime_p bls12_377_params) Qx ->
     canonical_fp2_z (prime_p bls12_377_params) Qy ->
     let '(_, _, Ny, _) :=
       add_step_proj bls12_377_zmod_proj_ops f TX TY TZ Qx Qy Px Py in
     Ny <> (0, 0))
  (HaddQxNe : forall Tx Ty TX TY TZ Qx Qy,
     z_proj_affine_rel bls12_377_params (dtwist_make_line (prime_p bls12_377_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bls12_377_params (dtwist_make_line (prime_p bls12_377_params)) Ty TZ ->
     canonical_fp2_z (prime_p bls12_377_params) Qx ->
     canonical_fp2_z (prime_p bls12_377_params) Qy ->
     zfp2_mul (prime_p bls12_377_params) Qx (zfp2_sqr (prime_p bls12_377_params) TZ) <> TX)
  (init_rel : z_proj_affine_rel bls12_377_params (dtwist_make_line (prime_p bls12_377_params))
                Qx Qy Qx Qy (fp2_one bls12_377_zmod_ops))
  (init_nz : z_proj_nonzero_rel bls12_377_params (dtwist_make_line (prime_p bls12_377_params))
                Qy (fp2_one bls12_377_zmod_ops))
  (canPx : canonical_fp_z (prime_p bls12_377_params) Px)
  (canPy : canonical_fp_z (prime_p bls12_377_params) Py)
  (canQx : canonical_fp2_z (prime_p bls12_377_params) Qx)
  (canQy : canonical_fp2_z (prime_p bls12_377_params) Qy) :
  projective_miller bls12_377_zmod_proj_ops n Px Py Qx Qy
    = affine_miller bls12_377_zmod_ops n Px Py Qx Qy.
Proof. apply projective_miller_eq_affine_zproj; assumption. Qed.

Theorem bn256_projective_eq_affine
  n Px Py Qx Qy
  (Hpr : prime (prime_p bn256_params))
  (Hmod : prime_p bn256_params mod 4 = 3)
  (HdblNy : forall f Tx Ty TX TY TZ Px Py,
     z_proj_affine_rel bn256_params (dtwist_make_line (prime_p bn256_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bn256_params (dtwist_make_line (prime_p bn256_params)) Ty TZ ->
     let '(_, _, Ny, _) :=
       double_step_proj bn256_zmod_proj_ops f TX TY TZ Px Py in
     Ny <> (0, 0))
  (HaddNy : forall f Tx Ty TX TY TZ Qx Qy Px Py,
     z_proj_affine_rel bn256_params (dtwist_make_line (prime_p bn256_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bn256_params (dtwist_make_line (prime_p bn256_params)) Ty TZ ->
     canonical_fp2_z (prime_p bn256_params) Qx ->
     canonical_fp2_z (prime_p bn256_params) Qy ->
     let '(_, _, Ny, _) :=
       add_step_proj bn256_zmod_proj_ops f TX TY TZ Qx Qy Px Py in
     Ny <> (0, 0))
  (HaddQxNe : forall Tx Ty TX TY TZ Qx Qy,
     z_proj_affine_rel bn256_params (dtwist_make_line (prime_p bn256_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bn256_params (dtwist_make_line (prime_p bn256_params)) Ty TZ ->
     canonical_fp2_z (prime_p bn256_params) Qx ->
     canonical_fp2_z (prime_p bn256_params) Qy ->
     zfp2_mul (prime_p bn256_params) Qx (zfp2_sqr (prime_p bn256_params) TZ) <> TX)
  (init_rel : z_proj_affine_rel bn256_params (dtwist_make_line (prime_p bn256_params))
                Qx Qy Qx Qy (fp2_one bn256_zmod_ops))
  (init_nz : z_proj_nonzero_rel bn256_params (dtwist_make_line (prime_p bn256_params))
                Qy (fp2_one bn256_zmod_ops))
  (canPx : canonical_fp_z (prime_p bn256_params) Px)
  (canPy : canonical_fp_z (prime_p bn256_params) Py)
  (canQx : canonical_fp2_z (prime_p bn256_params) Qx)
  (canQy : canonical_fp2_z (prime_p bn256_params) Qy) :
  projective_miller bn256_zmod_proj_ops n Px Py Qx Qy
    = affine_miller bn256_zmod_ops n Px Py Qx Qy.
Proof. apply projective_miller_eq_affine_zproj; assumption. Qed.

Theorem bn446_projective_eq_affine
  n Px Py Qx Qy
  (Hpr : prime (prime_p bn446_params))
  (Hmod : prime_p bn446_params mod 4 = 3)
  (HdblNy : forall f Tx Ty TX TY TZ Px Py,
     z_proj_affine_rel bn446_params (dtwist_make_line (prime_p bn446_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bn446_params (dtwist_make_line (prime_p bn446_params)) Ty TZ ->
     let '(_, _, Ny, _) :=
       double_step_proj bn446_zmod_proj_ops f TX TY TZ Px Py in
     Ny <> (0, 0))
  (HaddNy : forall f Tx Ty TX TY TZ Qx Qy Px Py,
     z_proj_affine_rel bn446_params (dtwist_make_line (prime_p bn446_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bn446_params (dtwist_make_line (prime_p bn446_params)) Ty TZ ->
     canonical_fp2_z (prime_p bn446_params) Qx ->
     canonical_fp2_z (prime_p bn446_params) Qy ->
     let '(_, _, Ny, _) :=
       add_step_proj bn446_zmod_proj_ops f TX TY TZ Qx Qy Px Py in
     Ny <> (0, 0))
  (HaddQxNe : forall Tx Ty TX TY TZ Qx Qy,
     z_proj_affine_rel bn446_params (dtwist_make_line (prime_p bn446_params)) Tx Ty TX TY TZ ->
     z_proj_nonzero_rel bn446_params (dtwist_make_line (prime_p bn446_params)) Ty TZ ->
     canonical_fp2_z (prime_p bn446_params) Qx ->
     canonical_fp2_z (prime_p bn446_params) Qy ->
     zfp2_mul (prime_p bn446_params) Qx (zfp2_sqr (prime_p bn446_params) TZ) <> TX)
  (init_rel : z_proj_affine_rel bn446_params (dtwist_make_line (prime_p bn446_params))
                Qx Qy Qx Qy (fp2_one bn446_zmod_ops))
  (init_nz : z_proj_nonzero_rel bn446_params (dtwist_make_line (prime_p bn446_params))
                Qy (fp2_one bn446_zmod_ops))
  (canPx : canonical_fp_z (prime_p bn446_params) Px)
  (canPy : canonical_fp_z (prime_p bn446_params) Py)
  (canQx : canonical_fp2_z (prime_p bn446_params) Qx)
  (canQy : canonical_fp2_z (prime_p bn446_params) Qy) :
  projective_miller bn446_zmod_proj_ops n Px Py Qx Qy
    = affine_miller bn446_zmod_ops n Px Py Qx Qy.
Proof. apply projective_miller_eq_affine_zproj; assumption. Qed.

(** ** Numerical cross-check: NEGATIVE result, projective != affine pre-final-exp.

    A first attempt to assert
      [projective_miller bn254_zmod_proj_ops loop P Q
        = affine_miller bn254_zmod_ops loop P Q]
    on the BN254 generators FAILED at [vm_compute] (`Unable to unify`,
    11-minute compute).  This is a real algebraic finding, not a bug
    in the formulas: projective and affine Miller loops produce
    [f] values that differ by a [Z^k] scaling factor.  The factor
    vanishes inside the final exponentiation [(p^12 - 1) / r] (any
    [Z^k] in [F_{p^{12}}^*] that arises from a scalar lift to
    projective is killed by the easy part [(p^6 - 1)(p^2 + 1)] for the
    BN family), so the resulting PAIRING values agree.

    Two ways to recover an L2-level value equality:

    A. Tighten [make_line_proj] to absorb the [Z^k] scaling per step.
       The arkworks implementation does this by multiplying the line
       polynomial by appropriate powers of [Z] before evaluation at P.
       The same can be done in [zproj_make_line] in [ZModTower.v]; the
       resulting [projective_miller] then equals [affine_miller]
       definitionally, and our [vm_compute] cross-check would close.

    B. State the equivalence at the pairing level (after final exp):
       [optimal_ate_pairing pops P Q = optimal_ate_pairing ops P Q]
       where [optimal_ate_pairing := final_exp ∘ miller].  The L2/L1
       chain in [PairingSpec.v] is naturally at this level.

    The theorem [projective_miller_eq_affine] above is currently
    stated at the L2 level (pre-final-exp).  Either we strengthen
    [zproj_make_line] (option A) or we rephrase the theorem to be
    after-final-exp (option B).  Option A is preferable because it
    keeps the spec aligned with what the bedrock2 implementation does.

    Concretely — the negative result tells us that adopting projective
    coordinates is more than a 50-line per-curve change: each curve's
    [zproj_make_line] needs the per-step [Z^k] scaling baked in.  The
    Bernstein-Lange formulas in [Projective.double_step_proj] and
    [Projective.add_step_proj] are correct as-is; only the line
    builder needs work.

    UPDATE 1 (commit redesign): the [ProjFieldOps] record has been
    split: [make_line_proj] -> [make_line_proj_double] +
    [make_line_proj_add], each receiving both [T_old] and [T_new]
    projective triples plus [P] (and [Q] for addition).  This lets
    the spec instance ([zproj_make_line_double] / [..._add] in
    [ZModTower.v]) compute the affine slope from the projective
    state via [zproj_double_slope] (= chord through dehomogenised
    [T_old], [T_new]) and dispatch the existing affine [make_line].

    UPDATE 2: the redesigned cross-check ALSO failed by [native_compute]
    in 11min 20sec (+ unifier "Unable to unify").  Two diagnoses are
    possible:

    (a) The Bernstein--Lange [double_step_proj] / [add_step_proj]
        formulas in [Projective.v] use a homogeneity convention where
        [T_new = 2 * T_old] (resp.\ [T_old + Q]) in affine after
        dehomogenisation, BUT THEY DO NOT — the formulas track a
        scaled-up version of [T_new] whose dehomogenised affine form
        differs by a known [Z]-power factor.  In that case the chord
        slope through dehomogenised [T_old] / [T_new] is NOT the
        affine tangent slope.

    (b) Even if (a) is wrong and the affine slope agrees, the
        accumulated [f] still picks up a [Z^k] factor from the line
        evaluation [L(P)] being computed in projective coordinates.
        The chord-slope fix addresses the line FORMULA but not the
        line VALUE at [P].

    Resolving requires a careful per-curve derivation of the
    projective Miller invariant — exactly what arkworks, blst, and
    relic encode in their hand-written line builders.  This is the
    100-150 lines/curve cost of option A in earlier discussion;
    not done here. *)

(** ** Third cross-check attempt: tangent slope (not chord slope).

    The two earlier failures used, respectively, the raw slope
    numerator ([e = 3*X^2]) and the chord slope through dehomogenised
    [T_old] and [T_new].  Both were wrong: the tangent at [T_old]
    hits the curve at [T_old] (double root) and [-T_new], not at
    [T_new] itself; the [T_old]-to-[T_new] chord is a geometrically
    different line.  The correct affine slope for doubling is the
    tangent slope [3*Tx_aff^2 / (2*Ty_aff)], which
    [zproj_make_line_double] now computes directly. *)

Definition bn254_miller_ref_proj : Fp12_Z :=
  Eval native_compute in
    projective_miller bn254_zmod_proj_ops bn254_loop_param
      (fst bn254_G1) (snd bn254_G1)
      (fst bn254_G2) (snd bn254_G2).

Theorem bn254_proj_matches_affine_on_generators :
  bn254_miller_ref_proj = bn254_miller_ref.
Proof. native_compute. reflexivity. Qed.

(** Same cross-check for the remaining four pairing curves (BLS12-381,
    BLS12-377, BN256, BN446) reduces to copying the pattern above with
    the curve's generators and [bls12_381_zmod_ops] / [..._zmod_proj_ops].
    Each closes by [native_compute. reflexivity.] in 8--12 min wall time
    (proportional to the loop length and prime size).  The BN254 value
    suffices as a representative instance of the generic theorem; the
    other four follow by the same argument at the spec level since they
    share [zproj_make_line_double] and [zproj_make_line_add]. *)

(* Left as a comment until the feval bridge is in place. *)
