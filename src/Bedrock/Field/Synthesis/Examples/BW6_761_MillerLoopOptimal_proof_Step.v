(** * BW6-761 Optimal-Ate Miller Loop — Step sub-lemma.

    Per-iteration invariant preservation: for each
    [v ∈ {1,...,187}] the unrolled body fragment
    [miller_iter_body (bw6_alphabet v)] takes the invariant from
    measure [v] to measure [v - 1].

    Closing this requires walking the per-iteration WP through:
      - 1 × fp6_sqr (f := f²)
      - 1 × g2_double_step (T := 2T, line coeffs r0d/r1d/r2d)
      - 1 × sparse_line_eval (line_d := sparse(r0d, r1d, r2d, P))
      - 1 × fp6_mul (f := f × line_d)
    and, when [bw6_alphabet v ≠ 0] (a non-zero NAF digit), also:
      - 1 × g2_add_step against the appropriate (q0/q0Neg/q1/q1Neg)
      - 1 × sparse_line_eval (line_a)
      - 1 × fp6_mul (f := f × line_a)
    and then deriving the projective-model transition
    [proj_running … fv Tx Ty Tz] -> [proj_running … fv' Tx' Ty' Tz']
    where [(fv',(Tx',Ty',Tz')) = bw6_proj_multibase_iter j …], via the
    [proj_multibase_iter_j0] / [_j1] / [_jm1] / [_j3] / [_jm3]
    dispatchers in [ProjectiveMultibase].

    Build note.  This file's cold-build time (~11 min) is dominated
    by loading [Rupicola.Lib.Api] (which transitively pulls in the
    Rupicola sub-files plus the bedrock2 weakest-precondition
    machinery), not by the [AffineMultibase] Gallina model (a
    384-LoC reference theory).  A Module-Type refactor over
    [AffineMultibase] therefore cannot reduce the build budget: it
    only abstracts the small Gallina component, while the heavy
    bedrock2/Rupicola chain is still required for [fnspec!] in the
    strengthened spec and for [WeakestPrecondition.cmd] here.  This
    file is consequently build-excluded in [src/Bedrock/dune].

    Statement now retargeted to the projective model (the callee
    specs in [BW6_761_MillerLoopOptimal] have been strengthened to
    value-postconditions relating outputs to [bw6_proj_double_step]
    etc., and [proj_running] carries the explicit Gallina state).
    All chained buffers are [loose]-bounded (the gnark step formulas
    end in mul/sub, and [sparse_line] / the init f-assignment yield
    loose), so only the forward [relax] (tight ⊆ loose) is needed.
    The proof is the per-call WP walk; under interactive development. *)

Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoopOptimal_proof_Common.

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoopOptimal.
Require Import Bedrock.Field.PairingTheory.ProjectiveMultibase.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_ProjOps.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BW6_761_MillerLoopOptimal_Step.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Existing Instances
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp_repr
    bw6_Fp_repr_ok
    bw6_Fp_names
    bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok bw6_Fp3_names
    bw6_Fp6_params bw6_Fp6_repr bw6_Fp6_repr_ok bw6_Fp6_names.

  Local Notation Fp  := (F PrimeField.M_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  Local Notation Fp_felem  := (@AbstractField.felem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_felem := (@AbstractField.felem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_felem := (@AbstractField.felem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_feval  := (@AbstractField.feval _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_feval := (@AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_feval := (@AbstractField.feval _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  (** Variable-name → buffer-address bindings the body reads.  The
      void [cmd.call]s in [miller_iter_body] never reassign locals, so
      this is invariant across iterations: the main theorem establishes
      it once after the stackallocs and threads it (with [l' = li] in
      the step postcondition) through the digit-list induction over
      [emit_iters].  [out] is excluded — it is read only by the final
      [fp6_copy], not by [miller_iter_body]. *)
  Definition step_locals
    (l : locals)
    (a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
     a_line_d a_line_a
     p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half : word) : Prop :=
    map.get l "f" = Some a_f /\
    map.get l "qx" = Some a_qx /\
    map.get l "qy" = Some a_qy /\
    map.get l "qz" = Some a_qz /\
    map.get l "r0d" = Some a_r0d /\
    map.get l "r1d" = Some a_r1d /\
    map.get l "r2d" = Some a_r2d /\
    map.get l "r0a" = Some a_r0a /\
    map.get l "r1a" = Some a_r1a /\
    map.get l "r2a" = Some a_r2a /\
    map.get l "line_d" = Some a_line_d /\
    map.get l "line_a" = Some a_line_a /\
    map.get l "p_x" = Some p_px /\
    map.get l "p_y" = Some p_py /\
    map.get l "q0x" = Some p_q0x /\
    map.get l "q0y" = Some p_q0y /\
    map.get l "q1x" = Some p_q1x /\
    map.get l "q1y" = Some p_q1y /\
    map.get l "q0ny" = Some p_q0ny /\
    map.get l "q1ny" = Some p_q1ny /\
    map.get l "half_fp" = Some p_half.

  (** Resolve [dexprs] for a [cmd.call]'s argument list: each
      [expr.var] is looked up via the [step_locals] [map.get] facts in
      context ([eassumption]). *)
  Local Ltac dexprs_fast :=
    cbv [dexprs WeakestPrecondition.list_map WeakestPrecondition.list_map_body
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first [ exact eq_refl | eexists; split; [ eassumption | ] ]).

  (** Per-iteration invariant preservation (projective model).

      One [miller_iter_body j] advances [proj_running] by exactly one
      [bw6_proj_multibase_iter j], leaving locals unchanged.  Holds for
      ALL [j] (not just the NAF digits {-3,-1,0,1,3}): the bedrock
      [match j] and the model [match j] share the same default
      ([q0x,q0y]), so any out-of-alphabet digit agrees on both sides.

      The callee specs the body actually calls are taken as hypotheses:
        - [g2_double_step], [sparse_line_eval], [fp6_sqr], [fp6_mul]
          (always, for [f := f² · line_double]);
        - [g2_add_step] additionally when [j <> 0]
          (for [f := f · line_add]).
      [g2_line_compute] is NOT needed here — it appears only in
      [miller_iter_final] (the i=0 step), handled separately. *)
  Lemma miller_loop_body_step_opt :
    forall functions
      (Hdbl    : spec_of_bw6_761_g2_double_step functions)
      (Hadd    : spec_of_bw6_761_g2_add_step functions)
      (Hsparse : spec_of_bw6_761_sparse_line_eval functions)
      (HFp6mul : spec_of_BinOp bin_mul (field_representation:=bw6_Fp6_repr) functions)
      (HFp6sqr : spec_of_UnOp un_square (field_representation:=bw6_Fp6_repr) functions),
    forall a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
           a_line_d a_line_a
           pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half
           (old_out : Fp6_felem) (p_x p_y : Fp_felem)
           (q0x q0y q1x q1y q0ny q1ny : Fp3_felem) (half : Fp_felem)
           (Rr : mem -> Prop) (tr : Semantics.trace)
           (j : Z) (fv : Fp6) (Tx Ty Tz : Fp3)
           (ti : Semantics.trace) (mi : mem) (li : locals),
      (j = 0%Z \/ j = 1%Z \/ j = (-1)%Z \/ j = 3%Z \/ j = (-3)%Z) ->
      step_locals li a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
        a_line_d a_line_a p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half ->
      proj_running
        a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
        a_line_d a_line_a
        pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half
        old_out p_x p_y q0x q0y q1x q1y q0ny q1ny half Rr tr
        fv Tx Ty Tz ti mi li ->
      WeakestPrecondition.cmd functions
        (miller_iter_body j) ti mi li
        (fun t' m' l' =>
          l' = li /\
          (let '(fv', (Tx', Ty', Tz')) :=
             bw6_proj_multibase_iter
               (Fp3_feval q0x) (Fp3_feval q0y) (Fp3_feval q0ny)
               (Fp3_feval q1x) (Fp3_feval q1y) (Fp3_feval q1ny)
               (Fp_feval p_x) (Fp_feval p_y) (Fp_feval half)
               j fv Tx Ty Tz in
           proj_running
             a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a
             a_line_d a_line_a
             pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half
             old_out p_x p_y q0x q0y q1x q1y q0ny q1ny half Rr tr
             fv' Tx' Ty' Tz' t' m' l')).
  Proof.
    intros functions Hdbl Hadd Hsparse Hmul Hsqr.
    intros a_f a_qx a_qy a_qz a_r0d a_r1d a_r2d a_r0a a_r1a a_r2a a_line_d a_line_a
           pout p_px p_py p_q0x p_q0y p_q1x p_q1y p_q0ny p_q1ny p_half
           old_out p_x p_y q0x q0y q1x q1y q0ny q1ny half Rr tr j fv Tx Ty Tz ti mi li
           Hj Hloc Hrun.
    unfold proj_running in Hrun.
    destruct Hrun as (Htr & Hbpx & Hbpy & Hbhalf & Hbq0x & Hbq0y & Hbq1x & Hbq1y
      & Hbq0ny & Hbq1ny & f_val & qx_val & qy_val & qz_val & r0d_val & r1d_val & r2d_val
      & r0a_val & r1a_val & r2a_val & line_d_val & line_a_val
      & Hbf & Hbqx & Hbqy & Hbqz & Hef & Heqx & Heqy & Heqz & Hsep).
    unfold step_locals in Hloc.
    destruct Hloc as (Lf & Lqx & Lqy & Lqz & Lr0d & Lr1d & Lr2d & Lr0a & Lr1a & Lr2a
      & Lld & Lla & Lpx & Lpy & Lq0x & Lq0y & Lq1x & Lq1y & Lq0ny & Lq1ny & Lhalf).
    subst ti.
    destruct (Z.eqb j 0) eqn:Hj0.
    { (* ===================== j = 0 ===================== *)
      apply Z.eqb_eq in Hj0; subst j.
      cbv [miller_iter_body]. cbv [cmd_seq_list BW6_761_MillerLoop.cmd_seq_list].
      change (0 =? 0)%Z with true; cbv iota.
      (* call 1: f := f^2 *)
      repeat straightline.
      eexists. split. 1: dexprs_fast.
      eapply Semantics.weaken_call.
      { eapply Hsqr. split; [exact Hbf|].
        split; [eexists; SeparationLogic.ecancel_assumption_impl|].
        SeparationLogic.ecancel_assumption_impl. }
      cbv beta. intros t1 m1 rets1 Hpost1.
      destruct Hpost1 as (-> & <- & f1v & Hfe1 & Hb1 & Hs1).
      eexists. split. 1: reflexivity.
      (* call 2: g2_double_step *)
      repeat straightline.
      eexists. split. 1: dexprs_fast.
      eapply Semantics.weaken_call.
      { eapply Hdbl. split;[exact Hbqx|]. split;[exact Hbqy|]. split;[exact Hbqz|].
        split;[exact Hbhalf|]. SeparationLogic.ecancel_assumption_impl. }
      cbv beta. intros t2 m2 rets2 Hpost2.
      destruct Hpost2 as (-> & <- & x2v & y2v & z2v & r0v & r1v & r2v
        & Hbx2 & Hby2 & Hbz2 & Hbr0 & Hbr1 & Hbr2 & Hs2 & Hval2).
      eexists. split. 1: reflexivity.
      (* call 3: sparse_line_eval -> line_d *)
      repeat straightline.
      eexists. split. 1: dexprs_fast.
      eapply Semantics.weaken_call.
      { eapply Hsparse. split;[exact Hbr0|]. split;[exact Hbr1|]. split;[exact Hbr2|].
        split;[exact Hbpx|]. split;[exact Hbpy|]. SeparationLogic.ecancel_assumption_impl. }
      cbv beta. intros t3 m3 rets3 Hpost3.
      destruct Hpost3 as (-> & <- & ld2 & Hbld2 & Hs3 & Hvld).
      eexists. split. 1: reflexivity.
      (* call 4: f := f * line_d *)
      repeat straightline.
      eexists. split. 1: dexprs_fast.
      eapply Semantics.weaken_call.
      { eapply Hmul.
        split; [ apply (@AbstractField.relax_bounds _ _ _ _ _ _ bw6_Fp6_repr bw6_Fp6_repr_ok _ Hb1) |].
        split; [ exact Hbld2 |].
        split; [eexists; SeparationLogic.ecancel_assumption_impl|].
        split; [eexists; SeparationLogic.ecancel_assumption_impl|].
        SeparationLogic.ecancel_assumption_impl. }
      cbv beta. intros t4 m4 rets4 Hpost4.
      destruct Hpost4 as (-> & <- & f2v & Hfe2 & Hb2 & Hs4).
      (* reassembly: state matches bw6_proj_multibase_iter ... 0 *)
      exists li. split; [reflexivity|]. split; [reflexivity|].
      cbv [bw6_proj_multibase_iter]. rewrite proj_multibase_iter_j0.
      unfold bw6_proj_double_step in Hval2.
      rewrite <- Heqx, <- Heqy, <- Heqz.
      destruct (proj_double_step bw6_proj_ops (Fp3_feval qx_val) (Fp3_feval qy_val)
        (Fp3_feval qz_val) (Fp_feval half)) as [[[x1 y1] z1] [[r0d r1d] r2d]] eqn:HD.
      destruct Hval2 as (Hx1 & Hy1 & Hz1 & Hr0 & Hr1 & Hr2).
      cbv beta zeta iota.
      unfold proj_running.
      split; [reflexivity|].
      split; [exact Hbpx|]. split; [exact Hbpy|]. split; [exact Hbhalf|].
      split; [exact Hbq0x|]. split; [exact Hbq0y|]. split; [exact Hbq1x|].
      split; [exact Hbq1y|]. split; [exact Hbq0ny|]. split; [exact Hbq1ny|].
      exists f2v, x2v, y2v, z2v, r0v, r1v, r2v, r0a_val, r1a_val, r2a_val, ld2, line_a_val.
      split; [ apply (@AbstractField.relax_bounds _ _ _ _ _ _ bw6_Fp6_repr bw6_Fp6_repr_ok _ Hb2) |].
      split; [exact Hbx2|]. split; [exact Hby2|]. split; [exact Hbz2|].
      split.
      2:{ split; [exact Hx1|]. split; [exact Hy1|]. split; [exact Hz1|].
          SeparationLogic.ecancel_assumption_impl. }
      rewrite Hfe2, Hfe1, Hef, Hvld, Hr0, Hr1, Hr2.
      cbv [bw6_proj_sparse_line bin_model bin_mul un_model un_square
           Affine.fp12_mul Affine.fp12_sqr bw6_proj_ops].
      unfold AbstractField.Fsquare. reflexivity. }
    (* ===================== j <> 0 : digits 1, -1, 3, -3 ===================== *)
    (* Each is the j=0 walk (square; double; sparse_d; mul_d) followed by the
       add branch (g2_add_step against the j-selected affine target; sparse_a;
       mul_a), with the running state matched via proj_multibase_iter_j{1,m1,
       3,m3}.  Same per-call discharge pattern as j=0; deferred. *)
    apply Z.eqb_neq in Hj0.
    destruct Hj as [Hj|[Hj|[Hj|[Hj|Hj]]]];
      [ congruence
      | subst j; admit
      | subst j; admit
      | subst j; admit
      | subst j; admit ].
  Admitted.

End BW6_761_MillerLoopOptimal_Step.
