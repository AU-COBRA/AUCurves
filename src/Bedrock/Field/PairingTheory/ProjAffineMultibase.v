(** * ProjAffineMultibase.v — projective ↔ affine equivalence for the
    5-symbol optimal-ate main loop.

    Sibling of [MillerEquiv.v], which proves the analogous result for the
    BINARY Miller loop (Bernstein–Lange Jacobian coordinates).  Here the
    loop is the 5-symbol multibase dispatch ([proj_main_loop] over a digit
    list, mirroring the bedrock [emit_iters]) and the projective formulas
    are gnark's homogeneous [doubleStep]/[addMixedStep]
    ([ProjectiveMultibase.proj_*]).

    Structure (following MillerEquiv): the deep per-iteration
    Z-normalisation algebra is packaged as a single [iter_simulates]
    hypothesis (to be discharged per-instance from the gnark formulas);
    this file proves the structural list-induction reducing the whole
    main-loop equivalence to that one per-digit obligation.

    [proj_main_loop] threads a projective point (x,y,z); the affine
    [multibase_iter_step] threads (Tx,Ty).  [rel] is the curve's
    dehomogenisation relation between them (homogeneous: Tx*Z = X,
    Ty*Z = Y, for gnark's coords — left abstract here). *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.

Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.AffineMultibase.
Require Import Bedrock.Field.PairingTheory.ProjectiveMultibase.

Local Open Scope Z_scope.

Section ProjAffineMultibase.

  Context {Fp Fp2 Fp12 : Type}.
  Context (ops : FieldOps Fp Fp2 Fp12).
  Context (fp3_mk : Fp -> Fp -> Fp -> Fp2).
  Context (fp3_c0 : Fp2 -> Fp).
  Context (fp6_mk : Fp2 -> Fp2 -> Fp12).

  (** Projective add-target points (the 6 the gnark loop dispatches over)
      and their affine counterparts (8 coords; for BW6:
      Qx=Q0x, QxNeg=Q0x, QyNeg=Q0yNeg, PhiQx=Q1x, PhiQy=Q1y,
      PhiQxNeg=Q1x, PhiQyNeg=Q1yNeg).  Kept as independent parameters so
      the lemma is generic; the per-instance [iter_simulates] ties them. *)
  Context (Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg : Fp2).
  Context (Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg : Fp2).
  Context (Px Py : Fp) (half : Fp).

  (** Dehomogenisation relation between affine (Tx,Ty) and projective
      (X,Y,Z).  Left abstract (the gnark homogeneous form, plus any
      canonicity, is supplied per-instance). *)
  Context (rel : Fp2 -> Fp2 -> Fp2 -> Fp2 -> Fp2 -> Prop).

  Local Notation piter :=
    (proj_multibase_iter ops fp3_mk fp3_c0 fp6_mk
       Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half).
  Local Notation aiter :=
    (multibase_iter_step ops Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
       Px Py).

  (** Per-digit obligation: under the dehomogenisation [rel], one
      projective iteration and one affine iteration produce the same
      running [f] and a new state still related by [rel].  This is the
      gnark per-step Z-normalisation, to be discharged per-instance
      (the SC1/SC2 analogue from MillerEquiv). *)
  Hypothesis iter_simulates :
    forall j f x y z Tx Ty,
      rel Tx Ty x y z ->
      let '(fp, (x', y', z')) := piter j f x y z in
      let '(fa, Tx', Ty') := aiter j f Tx Ty in
      fp = fa /\ rel Tx' Ty' x' y' z'.

  (** Affine main loop as a fold over the digit list — mirrors
      [ProjectiveMultibase.proj_main_loop] but with [multibase_iter_step]
      over affine (Tx,Ty). *)
  Fixpoint affine_main_loop
      (js : list Z) (f : Fp12) (Tx Ty : Fp2)
    : Fp12 * Fp2 * Fp2 :=
    match js with
    | [] => (f, Tx, Ty)
    | j :: rest =>
      let '(f', Tx', Ty') := aiter j f Tx Ty in
      affine_main_loop rest f' Tx' Ty'
    end.

  Local Notation pmain :=
    (proj_main_loop ops fp3_mk fp3_c0 fp6_mk).

  (** Main-loop equivalence: the projective and affine folds over the
      same digit list produce the same running [f] and a [rel]-related
      final state — reducing the whole main loop to [iter_simulates]. *)
  Lemma main_loop_simulates :
    forall js f x y z Tx Ty,
      rel Tx Ty x y z ->
      let '(fp, (x', y', z')) :=
        pmain js Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z in
      let '(fa, Tx', Ty') := affine_main_loop js f Tx Ty in
      fp = fa /\ rel Tx' Ty' x' y' z'.
  Proof.
    induction js as [| j rest IH]; intros f x y z Tx Ty Hrel.
    - cbn. split; [reflexivity | exact Hrel].
    - cbn [proj_main_loop affine_main_loop].
      pose proof (iter_simulates j f x y z Tx Ty Hrel) as Hstep.
      destruct (piter j f x y z) as [fp1 [[x1 y1] z1]].
      destruct (aiter j f Tx Ty) as [[fa1 Tx1] Ty1].
      destruct Hstep as [Hf1 Hrel1]. subst fa1.
      apply (IH fp1 x1 y1 z1 Tx1 Ty1 Hrel1).
  Qed.

  (* ================================================================ *)
  (* Whole-body assembly: init ∘ main loop ∘ final adjustment.        *)
  (* ================================================================ *)

  (** The running [f] and point after the init fragment (i=188: the
      proj/affine seed + first no-square step).  Abstracted as the
      post-init state; [init_rel] is the per-instance obligation that
      the two init fragments agree (the proj [f] = affine [f], and the
      points are dehomogenisation-related). *)
  Context (pf0 : Fp12) (px0 py0 pz0 : Fp2)
          (af0 : Fp12) (aTx0 aTy0 : Fp2).
  Hypothesis init_rel : pf0 = af0 /\ rel aTx0 aTy0 px0 py0 pz0.

  (** Final-adjustment functions (i=0) and their per-instance
      agreement obligation, under the dehomogenisation [rel]. *)
  Context (proj_final  : Fp12 -> Fp2 -> Fp2 -> Fp2 -> Fp12).
  Context (affine_final : Fp12 -> Fp2 -> Fp2 -> Fp12).
  Hypothesis final_simulates :
    forall f x y z Tx Ty,
      rel Tx Ty x y z -> proj_final f x y z = affine_final f Tx Ty.

  Definition proj_whole (js : list Z) : Fp12 :=
    let '(f, (x, y, z)) :=
      pmain js Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half pf0 px0 py0 pz0 in
    proj_final f x y z.

  Definition affine_whole (js : list Z) : Fp12 :=
    let '(f, Tx, Ty) := affine_main_loop js af0 aTx0 aTy0 in
    affine_final f Tx Ty.

  (** Whole-body equivalence: the projective and affine whole bodies
      agree, reducing the whole optimal-ate Miller value to the three
      per-step obligations [init_rel], [iter_simulates],
      [final_simulates]. *)
  Lemma whole_body_simulates :
    forall js, proj_whole js = affine_whole js.
  Proof.
    intros js. unfold proj_whole, affine_whole.
    destruct init_rel as [Hf0 Hrel0]. subst af0.
    pose proof (main_loop_simulates js pf0 px0 py0 pz0 aTx0 aTy0 Hrel0)
      as Hmain.
    destruct (pmain js Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half
                pf0 px0 py0 pz0) as [f1 [[x1 y1] z1]].
    destruct (affine_main_loop js pf0 aTx0 aTy0) as [[fa1 Tx1] Ty1].
    destruct Hmain as [Hf1 Hrel1]. subst fa1.
    apply (final_simulates f1 x1 y1 z1 Tx1 Ty1 Hrel1).
  Qed.

  (* ================================================================ *)
  (* Per-operation reduction of [iter_simulates].                     *)
  (* ================================================================ *)

  (** Affine add-target points correspond to the projective ones (the
      GLV 5-symbol structure: -Q shares Q's x-coordinate; the digit-3
      target is the endomorphism image Q1). *)
  Hypothesis Hpts :
    Qx = Q0x /\ Qy = Q0y /\ QxNeg = Q0x /\ QyNeg = Q0yNeg /\
    PhiQx = Q1x /\ PhiQy = Q1y /\ PhiQxNeg = Q1x /\ PhiQyNeg = Q1yNeg.

  (** Per-operation obligations — the gnark formula correctness, to be
      discharged at the concrete instance via field/curve algebra: the
      projective doubling / mixed-addition + sparse line produce the same
      running [f] as the affine [double_step] / [add_step] (with the
      curve's [make_line]) and preserve the dehomogenisation [rel]. *)
  Hypothesis double_simulates :
    forall f x y z Tx Ty,
      rel Tx Ty x y z ->
      let '((x1, y1, z1), (r0d, r1d, r2d)) := proj_double_step ops x y z half in
      let '(fa1, Tx1, Ty1) := double_step ops f Tx Ty Px Py in
      fp12_mul ops (fp12_sqr ops f)
        (proj_sparse_line ops fp3_mk fp3_c0 fp6_mk r0d r1d r2d Px Py) = fa1
      /\ rel Tx1 Ty1 x1 y1 z1.

  Hypothesis add_simulates :
    forall f x y z Tx Ty atx aty,
      rel Tx Ty x y z ->
      let '((x', y', z'), (r0a, r1a, r2a)) := proj_add_step ops x y z atx aty in
      let '(fa', Tx', Ty') := add_step ops f Tx Ty atx aty Px Py in
      fp12_mul ops f
        (proj_sparse_line ops fp3_mk fp3_c0 fp6_mk r0a r1a r2a Px Py) = fa'
      /\ rel Tx' Ty' x' y' z'.

  (** [iter_simulates] for every valid digit follows from the two
      per-operation obligations + the point correspondence — reducing
      the whole-body equivalence to [double_simulates]/[add_simulates]
      (the minimal form, matching MillerEquiv). *)
  Lemma iter_from_steps :
    forall j, (j = -3 \/ j = -1 \/ j = 0 \/ j = 1 \/ j = 3) ->
    forall f x y z Tx Ty,
      rel Tx Ty x y z ->
      let '(fp, (x', y', z')) :=
        proj_multibase_iter ops fp3_mk fp3_c0 fp6_mk
          Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half j f x y z in
      let '(fa, Tx', Ty') :=
        multibase_iter_step ops Qx Qy QxNeg QyNeg PhiQx PhiQy PhiQxNeg PhiQyNeg
          Px Py j f Tx Ty in
      fp = fa /\ rel Tx' Ty' x' y' z'.
  Proof.
    destruct Hpts as [HQx [HQy [HQxN [HQyN [HPx [HPy [HPxN HPyN]]]]]]].
    intros j Hj f x y z Tx Ty Hrel.
    pose proof (double_simulates f x y z Tx Ty Hrel) as Hd.
    destruct (proj_double_step ops x y z half)
      as [[[x1 y1] z1] [[r0d r1d] r2d]] eqn:Edbl.
    destruct (double_step ops f Tx Ty Px Py) as [[fa1 Tx1] Ty1] eqn:Eadbl.
    destruct Hd as [Hf1 Hrel1].
    destruct Hj as [Hj | [Hj | [Hj | [Hj | Hj]]]]; subst j.
    - (* j = -3 : proj target (Q1x,Q1yNeg) = affine (PhiQxNeg,PhiQyNeg) *)
      rewrite (proj_multibase_iter_jm3 ops fp3_mk fp3_c0 fp6_mk
                 Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z).
      rewrite (multibase_iter_step_jm3 ops Qx Qy QxNeg QyNeg PhiQx PhiQy
                 PhiQxNeg PhiQyNeg Px Py f Tx Ty).
      rewrite Edbl, Eadbl, HPxN, HPyN.
      pose proof (add_simulates fa1 x1 y1 z1 Tx1 Ty1 Q1x Q1yNeg Hrel1) as Ha.
      destruct (proj_add_step ops x1 y1 z1 Q1x Q1yNeg)
        as [[[x2 y2] z2] [[r0a r1a] r2a]] eqn:Eadd.
      destruct (add_step ops fa1 Tx1 Ty1 Q1x Q1yNeg Px Py)
        as [[fa2 Tx2] Ty2] eqn:Eaadd.
      destruct Ha as [Hf2 Hrel2].
      cbv beta iota zeta. rewrite Hf1. split; [exact Hf2 | exact Hrel2].
    - (* j = -1 : proj target (Q0x,Q0yNeg) = affine (QxNeg,QyNeg) *)
      rewrite (proj_multibase_iter_jm1 ops fp3_mk fp3_c0 fp6_mk
                 Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z).
      rewrite (multibase_iter_step_jm1 ops Qx Qy QxNeg QyNeg PhiQx PhiQy
                 PhiQxNeg PhiQyNeg Px Py f Tx Ty).
      rewrite Edbl, Eadbl, HQxN, HQyN.
      pose proof (add_simulates fa1 x1 y1 z1 Tx1 Ty1 Q0x Q0yNeg Hrel1) as Ha.
      destruct (proj_add_step ops x1 y1 z1 Q0x Q0yNeg)
        as [[[x2 y2] z2] [[r0a r1a] r2a]] eqn:Eadd.
      destruct (add_step ops fa1 Tx1 Ty1 Q0x Q0yNeg Px Py)
        as [[fa2 Tx2] Ty2] eqn:Eaadd.
      destruct Ha as [Hf2 Hrel2].
      cbv beta iota zeta. rewrite Hf1. split; [exact Hf2 | exact Hrel2].
    - (* j = 0 : doubling only *)
      rewrite (proj_multibase_iter_j0 ops fp3_mk fp3_c0 fp6_mk
                 Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z).
      rewrite (multibase_iter_step_j0 ops Qx Qy QxNeg QyNeg PhiQx PhiQy
                 PhiQxNeg PhiQyNeg Px Py f Tx Ty).
      rewrite Edbl, Eadbl.
      cbv beta iota zeta. split; [exact Hf1 | exact Hrel1].
    - (* j = 1 : proj target (Q0x,Q0y) = affine (Qx,Qy) *)
      rewrite (proj_multibase_iter_j1 ops fp3_mk fp3_c0 fp6_mk
                 Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z).
      rewrite (multibase_iter_step_j1 ops Qx Qy QxNeg QyNeg PhiQx PhiQy
                 PhiQxNeg PhiQyNeg Px Py f Tx Ty).
      rewrite Edbl, Eadbl, HQx, HQy.
      pose proof (add_simulates fa1 x1 y1 z1 Tx1 Ty1 Q0x Q0y Hrel1) as Ha.
      destruct (proj_add_step ops x1 y1 z1 Q0x Q0y)
        as [[[x2 y2] z2] [[r0a r1a] r2a]] eqn:Eadd.
      destruct (add_step ops fa1 Tx1 Ty1 Q0x Q0y Px Py)
        as [[fa2 Tx2] Ty2] eqn:Eaadd.
      destruct Ha as [Hf2 Hrel2].
      cbv beta iota zeta. rewrite Hf1. split; [exact Hf2 | exact Hrel2].
    - (* j = 3 : proj target (Q1x,Q1y) = affine (PhiQx,PhiQy) *)
      rewrite (proj_multibase_iter_j3 ops fp3_mk fp3_c0 fp6_mk
                 Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z).
      rewrite (multibase_iter_step_j3 ops Qx Qy QxNeg QyNeg PhiQx PhiQy
                 PhiQxNeg PhiQyNeg Px Py f Tx Ty).
      rewrite Edbl, Eadbl, HPx, HPy.
      pose proof (add_simulates fa1 x1 y1 z1 Tx1 Ty1 Q1x Q1y Hrel1) as Ha.
      destruct (proj_add_step ops x1 y1 z1 Q1x Q1y)
        as [[[x2 y2] z2] [[r0a r1a] r2a]] eqn:Eadd.
      destruct (add_step ops fa1 Tx1 Ty1 Q1x Q1y Px Py)
        as [[fa2 Tx2] Ty2] eqn:Eaadd.
      destruct Ha as [Hf2 Hrel2].
      cbv beta iota zeta. rewrite Hf1. split; [exact Hf2 | exact Hrel2].
  Qed.

End ProjAffineMultibase.
