Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
(* Require Import Crypto.Bedrock.Specs.Field. *)
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
Local Notation "x ^F2" := (@F.mul M_pos x x) (at level 90).

Context {three_b_val : F}.

  Definition ladderstep_gallina
             (X1 X2 Y1 Y2 Z1 Z2 : F) : \<< F, F, F \>> :=
    let/n three_b := stack three_b_val in
    let/n t0 := stack (X1 *F X2) in
    let/n t1 := stack (Y1 *F Y2) in
    let/n t2 := stack (Z1 *F Z2) in
    let/n t3 := stack (X1 +F Y1) in
    let/n t4 := stack (X2 +F Y2) in
    let/n t3 := (t3 *F t4) in
    let/n t4 := (t0 +F t1) in
    let/n t3 := (t3 -F t4) in
    let/n t4 := (X1 +F Z1) in
    let/n t5 := stack (X2 +F Z2) in
    let/n t4 := (t4 *F t5) in
    let/n t5 := (t0 +F t2) in
    let/n t4 := (t4 -F t5) in
    let/n t5 := (Y1 +F Z1) in
    let/n Xout := (Y2 +F Z2) in
    let/n t5 := (t5 *F Xout) in
    let/n Xout:= (t1 +F t2) in
    let/n t5 := (t5 -F Xout) in
    let/n Zout := (three_b *F t2) in
    let/n Xout := (t1 -F Zout) in
    let/n Zout := (Zout +F t1) in
    let/n Yout := (Xout *F Zout) in
    let/n t1 := (t0 +F t0) in
    let/n t1 := (t1 +F t0) in
    let/n t4 := (three_b *F t4) in
    let/n t0 := (t1 *F t4) in
    let/n Yout := (Yout +F t0) in
    let/n t0 := (t5 *F t4) in
    let/n Xout := (t3 *F Xout) in
    let/n Xout := (Xout -F t0) in
    let/n t0 := (t3 *F t1) in
    let/n Zout := (t5 *F Zout) in
    let/n Zout := (Zout +F t0) in
    \<Xout, Yout, Zout\>.
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
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  Instance spec_of_ladderstep : spec_of "curve_add" :=
    fnspec! "curve_add"
          (pX1 pX2 pY1 pY2 pZ1 pZ2 pXout pYout pZout : word)
          / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pX1 X1
         * FElem (Some tight_bounds) pX2 X2
         * FElem (Some tight_bounds) pY1 Y1
         * FElem (Some tight_bounds) pY2 Y2
         * FElem (Some tight_bounds) pZ1 Z1
         * FElem (Some tight_bounds) pZ2 Z2
         * FElem (Some tight_bounds) pXout Xoutold
         * FElem (Some tight_bounds) pYout Youtold
         * FElem (Some tight_bounds) pZout Zoutold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Xout Yout Zout (* output values *)
                  : F ,
                  (@ladderstep_gallina _ three_b_val X1 X2 Y1 Y2 Z1 Z2
           = \<Xout, Yout, Zout\>)
          /\ (FElem (Some tight_bounds) pX1 X1
                * FElem (Some tight_bounds) pX2 X2
                * FElem (Some tight_bounds) pY1 Y1
                * FElem (Some tight_bounds) pY2 Y2
                * FElem (Some tight_bounds) pZ1 Z1
                * FElem (Some tight_bounds) pZ2 Z2
                * FElem (Some tight_bounds) pXout Xout
                * FElem (Some tight_bounds) pYout Yout
                * FElem (Some tight_bounds) pZout Zout * R)%sep mem'}.

  Lemma compile_ladderstep {tr m l functions}
        (x1 x2 y1 y2 z1 z2 xout1 yout1 zout1 : F)
        {P} {pred: P (@ladderstep_gallina _ three_b_val x1 x2 y1 y2 z1 z2) -> predicate}
        {k: nlet_eq_k P (@ladderstep_gallina _ three_b_val x1 x2 y1 y2 z1 z2)} {k_impl} :
    let v := @ladderstep_gallina _ three_b_val x1 x2 y1 y2 z1 z2 in
    forall
           Rout
           X1_ptr X1_var X2_ptr X2_var Y1_ptr Y1_var Y2_ptr Y2_var
           Z1_ptr Z1_var Z2_ptr Z2_var Xout_ptr Xout_var Yout_ptr Yout_var Zout_ptr Zout_var,

      spec_of_ladderstep functions ->

      (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) X2_ptr x2 *
       FElem (Some tight_bounds) Y1_ptr y1 * FElem (Some tight_bounds) Y2_ptr y2 *
       FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) Z2_ptr z2 *
       FElem (Some tight_bounds) Xout_ptr xout1 *
       FElem (Some tight_bounds) Yout_ptr yout1 * FElem (Some tight_bounds) Zout_ptr zout1 * Rout)%sep m ->

      map.get l X1_var = Some X1_ptr ->
      map.get l X2_var = Some X2_ptr ->
      map.get l Y1_var = Some Y1_ptr ->
      map.get l Y2_var = Some Y2_ptr ->
      map.get l Z1_var = Some Z1_ptr ->
      map.get l Z2_var = Some Z2_ptr ->
      map.get l Xout_var = Some Xout_ptr ->
      map.get l Yout_var = Some Yout_ptr ->
      map.get l Zout_var = Some Zout_ptr ->

      (let v := v in
       forall (* output values *) m',
       let '\<Xout', Yout', Zout'\> := @ladderstep_gallina _ three_b_val x1 x2 y1 y2 z1 z2 in
            (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) X2_ptr x2 *
            FElem (Some tight_bounds) Y1_ptr y1 * FElem (Some tight_bounds) Y2_ptr y2 *
            FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) Z2_ptr z2 *
            FElem (Some tight_bounds) Xout_ptr Xout' *
            FElem (Some tight_bounds) Yout_ptr Yout' * FElem (Some tight_bounds) Zout_ptr Zout' * Rout)%sep m' ->
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
        (cmd.call [] "curve_add"
                  [ expr.var X1_var; expr.var X2_var;
                  expr.var Y1_var; expr.var Y2_var;
                  expr.var Z1_var; expr.var Z2_var;
                  expr.var Xout_var; expr.var Yout_var;
                  expr.var Zout_var])
        k_impl
      <{ pred (nlet_eq
                 [Xout_var; Yout_var; Zout_var]
                 v k) }>.
  Proof.
    repeat straightline'.
    handle_call.
    lazymatch goal with
    | Hcont : (forall m', _ -> _),
      Heq : ladderstep_gallina _ _ _ _ _ _ = _,
      Hsep : sep _ _ _ |- _ =>
      apply Hcont; rewrite Heq; ecancel_assumption
    end.
  Qed.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  (* Spec for the three_b constant loader function *)
  Instance spec_of_three_b_loader : spec_of three_b_name :=
    fnspec! three_b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout three_b_val * Rout)%sep mem' }.

  (* Compilation lemma for loading the three_b constant *)
  Lemma compile_load_three_b {tr m l functions}
        {P} {pred: P three_b_val -> predicate}
        {k: nlet_eq_k P three_b_val} {k_impl} :
    let v := three_b_val in
    forall
           R out out_ptr out_var out_bounds,
      spec_of_three_b_loader functions ->
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
    simple eapply compile_load_three_b; shelve : compiler.

  (* Bounds tightening: since loose_bounds = tight_bounds, we can go
     loose→tight (reverse of relax_bounds_FElem). Needed because add
     produces loose_bounds but sub/mul expect tight_bounds inputs. *)
  Local Lemma tighten_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                      (FElem (Some tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.
  Local Hint Immediate tighten_bounds_FElem : ecancel_impl.

  Derive ladderstep_body SuchThat
         (defn! "curve_add"
                ("X1", "X2", "Y1", "Y2", "Z1", "Z2", "Xout", "Yout", "Zout")
              { ladderstep_body },
           implements @ladderstep_gallina _ three_b_val
                      using [mul; add; sub; three_b_name])
         As ladderstep_correct.
  Proof. compile. Qed.

End __.

#[global] Existing Instance spec_of_ladderstep.

#[global]
Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (ladderstep_gallina _ _ _ _ _ _) _))) =>
       simple eapply compile_ladderstep; shelve : compiler.
