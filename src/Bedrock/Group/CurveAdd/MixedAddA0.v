(** * Complete mixed addition for a = 0 (Renes-Costello-Batina 2015, Algorithm 8), in place.

    [madd_a0_gallina X1 Y1 Z1 X2 Y2] adds the projective point (X1 : Y1 : Z1) and the affine
    point (X2, Y2), i.e. (X2 : Y2 : 1), on y^2 = x^3 + b with 3b = [three_b_val]: Algorithm 8 of
    Renes, Costello and Batina, "Complete addition formulas for prime order elliptic curves"
    (2015), step for step, 11 multiplications, 2 multiplications by 3b and 13 additions or
    subtractions (Algorithm 7, [CurveAdd.ladderstep_gallina], takes 12, 2 and 19).

    The intermediate values of X3, Y3, Z3 are kept in stack temporaries, and the outputs Xout,
    Yout, Zout are each written once, with the final value, after the last read of X1, Y1, Z1
    (step 14), and never read; so the same command adds the affine point in place (outputs =
    the buffers of X1, Y1, Z1: bucket += point) or into separate buffers.

    - [madd_a0_eq_ladderstep] (Section 2): at Z2 = 1 the result is, coordinate for coordinate
      (Leibniz), that of [ladderstep_gallina]; so every property of Algorithm 7 carries over
      ([madd_a0_triple_eq] in triple form; [BLS12_MSM_MixedAdd] uses it to keep the MSM's
      contract [g1_add_spec = ladderstep_triple], whose group law is [RcbProjectiveLaws]).
    - [madd_a0_cmd] / [madd_a0_cmd_ok] (Section 3): the bedrock2 command, derived by Rupicola
      (callees: the field mul / add / sub and the 3b loader of [CurveAdd.ladderstep_body]) in
      any locals map that binds the eight pointer variables, so that a function can inline it
      ([BLS12_MSM_MixedAdd.msm_curve_add_mixed] does), with the outputs in place;
      [madd_a0_cmd_sep_ok]: the same derivation with separate output buffers, and
      [madd_a0_cmd_sep_eq]: both derivations give the same command.

    Everything is Qed; no Admitted, no Axiom. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Local Open Scope Z_scope.

(* ==================================================================== *)
(** * Section 1: the Gallina program                                    *)
(* ==================================================================== *)

Section Gallina.
  Context {field_parameters : FieldParameters}.

  Local Notation F := (F M_pos).
  Local Infix "+F" := (@F.add M_pos) (at level 100).
  Local Infix "-F" := (@F.sub M_pos) (at level 100).
  Local Infix "*F" := (@F.mul M_pos) (at level 90).

  Context {three_b_val : F}.

  (** Algorithm 8, step for step (step numbers of the paper).  The intermediate values of
      X3, Y3, Z3 live in stack temporaries ([t2] / [t5], [y3], [z3]; [t5] first holds 3b, dead
      after step 17); [Xout], [Yout], [Zout] are each written once, with the final value
      (steps 20, 23, 26), after the last read of X1, Y1, Z1 (step 14), and never read.  So the
      same command is correct whether or not the outputs are the buffers of X1, Y1, Z1
      (Section 4 derives it for both). *)
  Definition madd_a0_gallina (X1 Y1 Z1 X2 Y2 : F) : \<< F, F, F \>> :=
    let/n t5 := stack three_b_val in
    let/n t0 := stack (X1 *F X2) in          (*  1 *)
    let/n t1 := stack (Y1 *F Y2) in          (*  2 *)
    let/n t3 := stack (X2 +F Y2) in          (*  3 *)
    let/n t4 := stack (X1 +F Y1) in          (*  4 *)
    let/n t3 := (t3 *F t4) in                (*  5 *)
    let/n t4 := (t0 +F t1) in                (*  6 *)
    let/n t3 := (t3 -F t4) in                (*  7 *)
    let/n t4 := (Y2 *F Z1) in                (*  8 *)
    let/n t4 := (t4 +F Y1) in                (*  9 *)
    let/n y3 := stack (X2 *F Z1) in          (* 10 *)
    let/n y3 := (y3 +F X1) in                (* 11 *)
    let/n t2 := stack (t0 +F t0) in          (* 12: X3 in t2 *)
    let/n t0 := (t2 +F t0) in                (* 13 *)
    let/n t2 := (t5 *F Z1) in                (* 14 *)
    let/n z3 := stack (t1 +F t2) in          (* 15 *)
    let/n t1 := (t1 -F t2) in                (* 16 *)
    let/n y3 := (t5 *F y3) in                (* 17 *)
    let/n t5 := (t4 *F y3) in                (* 18: X3 in t5 *)
    let/n t2 := (t3 *F t1) in                (* 19 *)
    let/n Xout := (t2 -F t5) in              (* 20 *)
    let/n y3 := (y3 *F t0) in                (* 21 *)
    let/n t1 := (t1 *F z3) in                (* 22 *)
    let/n Yout := (t1 +F y3) in              (* 23 *)
    let/n t0 := (t0 *F t3) in                (* 24 *)
    let/n z3 := (z3 *F t4) in                (* 25 *)
    let/n Zout := (z3 +F t0) in              (* 26 *)
    \<Xout, Yout, Zout\>.
End Gallina.

(* ==================================================================== *)
(** * Section 2: Algorithm 8 is Algorithm 7 at Z2 = 1                   *)
(* ==================================================================== *)

Section MixedIsAdd.
  Context {field_parameters : FieldParameters}.

  Local Notation F := (F M_pos).

  Add Ring Fp_ring_a0_mixed : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  (** Leibniz, for any field and any 3b: both are the same three polynomials (RCB 2015, the
      a = 0 formulas of their Section 3) once Z2 = 1. *)
  Theorem madd_a0_eq_ladderstep (three_b_val X1 Y1 Z1 X2 Y2 : F) :
    @madd_a0_gallina _ three_b_val X1 Y1 Z1 X2 Y2
    = @ladderstep_gallina _ three_b_val X1 X2 Y1 Y2 Z1 1%F.
  Proof.
    cbv [madd_a0_gallina ladderstep_gallina nlet stack].
    f_equal; [ | f_equal ]; ring.
  Qed.

  (** Triple form. *)
  Definition madd_a0_triple (three_b_val : F) (P : F * F * F) (Q : F * F) : F * F * F :=
    let '(X1, Y1, Z1) := P in
    let '(X2, Y2) := Q in
    let '\<x, y, z\> := @madd_a0_gallina _ three_b_val X1 Y1 Z1 X2 Y2 in
    (x, y, z).

  Corollary madd_a0_triple_eq (three_b_val : F) (P : F * F * F) (X2 Y2 : F) :
    madd_a0_triple three_b_val P (X2, Y2) = ladderstep_triple three_b_val P (X2, Y2, 1%F).
  Proof.
    destruct P as [[X1 Y1] Z1].
    cbv [madd_a0_triple ladderstep_triple]. rewrite madd_a0_eq_ladderstep. reflexivity.
  Qed.
End MixedIsAdd.

(* ==================================================================== *)
(** * Section 3: Rupicola derivation of the command                     *)
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


  Local Definition three_b_val : F := feval (proj1_sig three_b).

  (** The 3b loader, as [CurveAdd.spec_of_three_b_loader] (its compile lemma there is local). *)
  #[local] Instance spec_of_three_b_loader_madd : spec_of three_b_name | 0 :=
    fnspec! three_b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout three_b_val * Rout)%sep mem' }.

  Lemma compile_load_three_b_madd {tr m l functions}
        {P} {pred: P three_b_val -> predicate}
        {k: nlet_eq_k P three_b_val} {k_impl} :
    let v := three_b_val in
    forall
           R out out_ptr out_var out_bounds,
      spec_of_three_b_loader_madd functions ->
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
    simple eapply compile_load_three_b_madd; shelve : compiler.

  Local Lemma tighten_bounds_FElem_madd x_ptr x
    : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                      (FElem (Some tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.
  Local Hint Immediate tighten_bounds_FElem_madd : ecancel_impl.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  Local Ltac solve_map_get_put :=
    lazymatch goal with
    | |- map.get _ _ = Some _ =>
        solve [ repeat first [ simple apply map.get_put_same
                             | rewrite map.get_put_diff by congruence ] ]
    end.

  (** The postcondition, in the form Rupicola's function setup produces (no return values;
      the final locals are not constrained). *)
  Definition madd_a0_pred (tr : Semantics.trace) (Q : mem -> Prop)
    : \<< F, F, F \>> -> Semantics.trace -> mem -> locals -> Prop :=
    fun p =>
      wp_bind_retvars []
        (fun (rets : list word) (tr' : Semantics.trace) (mem' : mem) (_ : locals) =>
           rets = [] /\ tr = tr' /\
           exists X3 Y3 Z3 : F, p = \<X3, Y3, Z3\> /\ Q mem').

  Local Ltac finish_madd :=
    cbv [madd_a0_pred wp_bind_retvars]; exists []; split; [ reflexivity | ];
    split; [ reflexivity | ]; split; [ reflexivity | ];
    do 3 eexists; split; [ reflexivity | ];
    rewrite Hbounds_eq in *; ecancel_assumption.

  (** In place: [Xout], [Yout], [Zout] hold the pointers of [X1], [Y1], [Z1].  The locals are
      any map in which the eight names are bound as shown (output names below input names, so
      that Rupicola reads the inputs through [X1], [Y1], [Z1]). *)
  Derive madd_a0_cmd SuchThat
    (forall functions : Semantics.env,
       spec_of_BinOp bin_mul functions -> spec_of_BinOp bin_add functions ->
       spec_of_BinOp bin_sub functions -> spec_of_three_b_loader_madd functions ->
       forall (pX1 pY1 pZ1 pX2 pY2 : word) (X1 Y1 Z1 X2 Y2 : F) (R : mem -> Prop)
              (tr : Semantics.trace) (mem0 : mem) (l0 : locals),
       (FElem (Some tight_bounds) pX1 X1
        * FElem (Some tight_bounds) pY1 Y1
        * FElem (Some tight_bounds) pZ1 Z1
        * FElem (Some tight_bounds) pX2 X2
        * FElem (Some tight_bounds) pY2 Y2 * R)%sep mem0 ->
       <{ Trace := tr; Memory := mem0;
          Locals := map.put (map.put (map.put (map.put (map.put (map.put (map.put (map.put l0
                      "Xout" pX1) "Yout" pY1) "Zout" pZ1)
                      "X1" pX1) "Y1" pY1) "Z1" pZ1) "X2" pX2) "Y2" pY2;
          Functions := functions }>
       madd_a0_cmd
       <{ madd_a0_pred tr
            (fun m' => exists X3 Y3 Z3 : F,
               @madd_a0_gallina _ three_b_val X1 Y1 Z1 X2 Y2 = \<X3, Y3, Z3\> /\
               (FElem (Some tight_bounds) pX1 X3
                * FElem (Some tight_bounds) pY1 Y3
                * FElem (Some tight_bounds) pZ1 Z3
                * FElem (Some tight_bounds) pX2 X2
                * FElem (Some tight_bounds) pY2 Y2 * R)%sep m')
            (@madd_a0_gallina _ three_b_val X1 Y1 Z1 X2 Y2) }>)
    As madd_a0_cmd_ok.
  Proof.
    intros. subst madd_a0_cmd. unfold madd_a0_gallina at 2.
    repeat repeat (first [ compile_step | solve_map_get_put ]).
    cbv [madd_a0_pred wp_bind_retvars]. exists []. split; [ reflexivity | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    do 3 eexists. split; [ reflexivity | ].
    do 3 eexists. split; [ reflexivity | ].
    rewrite Hbounds_eq in *. ecancel_assumption.
  Qed.

  (** Separate outputs (unconstrained buffers), as [RcbAnyOut.spec_of_ladderstep_anyout]. *)
  Derive madd_a0_cmd_sep SuchThat
    (forall functions : Semantics.env,
       spec_of_BinOp bin_mul functions -> spec_of_BinOp bin_add functions ->
       spec_of_BinOp bin_sub functions -> spec_of_three_b_loader_madd functions ->
       forall (pX1 pY1 pZ1 pX2 pY2 pXo pYo pZo : word) (X1 Y1 Z1 X2 Y2 Xo Yo Zo : F)
              (R : mem -> Prop) (tr : Semantics.trace) (mem0 : mem) (l0 : locals),
       (FElem (Some tight_bounds) pX1 X1
        * FElem (Some tight_bounds) pY1 Y1
        * FElem (Some tight_bounds) pZ1 Z1
        * FElem (Some tight_bounds) pX2 X2
        * FElem (Some tight_bounds) pY2 Y2
        * FElem None pXo Xo * FElem None pYo Yo * FElem None pZo Zo * R)%sep mem0 ->
       <{ Trace := tr; Memory := mem0;
          Locals := map.put (map.put (map.put (map.put (map.put (map.put (map.put (map.put l0
                      "Xout" pXo) "Yout" pYo) "Zout" pZo)
                      "X1" pX1) "Y1" pY1) "Z1" pZ1) "X2" pX2) "Y2" pY2;
          Functions := functions }>
       madd_a0_cmd_sep
       <{ madd_a0_pred tr
            (fun m' => exists X3 Y3 Z3 : F,
               @madd_a0_gallina _ three_b_val X1 Y1 Z1 X2 Y2 = \<X3, Y3, Z3\> /\
               (FElem (Some tight_bounds) pX1 X1
                * FElem (Some tight_bounds) pY1 Y1
                * FElem (Some tight_bounds) pZ1 Z1
                * FElem (Some tight_bounds) pX2 X2
                * FElem (Some tight_bounds) pY2 Y2
                * FElem (Some tight_bounds) pXo X3
                * FElem (Some tight_bounds) pYo Y3
                * FElem (Some tight_bounds) pZo Z3 * R)%sep m')
            (@madd_a0_gallina _ three_b_val X1 Y1 Z1 X2 Y2) }>)
    As madd_a0_cmd_sep_ok.
  Proof.
    intros. subst madd_a0_cmd_sep. unfold madd_a0_gallina at 2.
    repeat repeat (first [ compile_step | solve_map_get_put ]).
    cbv [madd_a0_pred wp_bind_retvars]. exists []. split; [ reflexivity | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    do 3 eexists. split; [ reflexivity | ].
    do 3 eexists. split; [ reflexivity | ].
    rewrite Hbounds_eq in *. ecancel_assumption.
  Qed.

  (** The two derivations give the same command. *)
  Lemma madd_a0_cmd_sep_eq : madd_a0_cmd_sep = madd_a0_cmd.
  Proof. reflexivity. Qed.
End __.
