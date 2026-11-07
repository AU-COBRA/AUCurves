(** * The Granger-Scott cyclotomic squaring of Fp12, derived by Rupicola over an arbitrary
      field ([Bedrock.Specs.AbstractField]) standing for Fp2.

    [af_cyc_sqr_gallina mulxi x0 .. x5] is the in-place [let/n] chain of
    [Theory.BLS12Pairing.CyclotomicGS.cyc_sqr6] over [AbstractField.Fadd/Fsub/Fmul] and a
    unary [mulxi] (multiplication by the non-residue xi): the six Fp2 coefficients of an
    Fp12 element in memory order (c0.c0, c0.c1, c0.c2, c1.c0, c1.c1, c1.c2), three Fp4
    squarings (nine squarings of the field), the outputs written over the inputs after the
    last read of each.  [af_cyc_sqr_body] is derived from it with the AbstractField compile
    lemmas of [Compilation2_Fp2] and [compile_af_mulxi] below ([af_cyc_sqr_correct], Qed);
    it calls exactly [AbstractField.mul] (squarings: [square]), [add], [sub] and [mulxi_name].

    Instantiated at the BLS12-381 Fp2 representation with [mulxi_name = "bls12_Fp2_mul_xi"]
    in [BLS12_Pairing.bls12_Fp12_cyclotomic_square].  Everything here is Qed. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Bedrock.Specs.AbstractField.
Require Bedrock.Field.FieldExtensions.Compilation2_Fp2.
Local Open Scope Z_scope.

Section Gallina.
  Context {F : Type} {field_parameters : AbstractField.FieldParameters F}.
  Context (mulxi : F -> F).

  Local Infix "+F" := AbstractField.Fadd (at level 100).
  Local Infix "-F" := AbstractField.Fsub (at level 100).
  Local Infix "*F" := AbstractField.Fmul (at level 90).

  (** g0 = (x0, x4), g1 = (x3, x2), g2 = (x1, x5);  t^2 = xi. *)
  Definition af_cyc_sqr_gallina (x0 x1 x2 x3 x4 x5 : F) : \<< F, F, F, F, F, F \>> :=
    (* g0^2 = (t0, t2) *)
    let/n t0 := stack (x0 *F x0) in
    let/n t1 := stack (x4 *F x4) in
    let/n t2 := stack (x0 +F x4) in
    let/n t2 := (t2 *F t2) in
    let/n t2 := (t2 -F t0) in
    let/n t2 := (t2 -F t1) in
    let/n t1 := mulxi t1 in
    let/n t0 := (t0 +F t1) in
    (* g1^2 = (t3, t5) *)
    let/n t3 := stack (x3 *F x3) in
    let/n t4 := stack (x2 *F x2) in
    let/n t5 := stack (x3 +F x2) in
    let/n t5 := (t5 *F t5) in
    let/n t5 := (t5 -F t3) in
    let/n t5 := (t5 -F t4) in
    let/n t4 := mulxi t4 in
    let/n t3 := (t3 +F t4) in
    (* g2^2 = (t1, t6) *)
    let/n t1 := (x1 *F x1) in
    let/n t4 := (x5 *F x5) in
    let/n t6 := stack (x1 +F x5) in
    let/n t6 := (t6 *F t6) in
    let/n t6 := (t6 -F t1) in
    let/n t6 := (t6 -F t4) in
    let/n t4 := mulxi t4 in
    let/n t1 := (t1 +F t4) in
    (* new g0 = 3 g0^2 - 2 conj g0 *)
    let/n x0 := (t0 -F x0) in
    let/n x0 := (x0 +F x0) in
    let/n x0 := (x0 +F t0) in
    let/n x4 := (t2 +F x4) in
    let/n x4 := (x4 +F x4) in
    let/n x4 := (x4 +F t2) in
    (* new g2 = 3 g1^2 - 2 conj g2 *)
    let/n x1 := (t3 -F x1) in
    let/n x1 := (x1 +F x1) in
    let/n x1 := (x1 +F t3) in
    let/n x5 := (t5 +F x5) in
    let/n x5 := (x5 +F x5) in
    let/n x5 := (x5 +F t5) in
    (* new g1 = 3 t g2^2 + 2 conj g1 *)
    let/n t6 := mulxi t6 in
    let/n x3 := (t6 +F x3) in
    let/n x3 := (x3 +F x3) in
    let/n x3 := (x3 +F t6) in
    let/n x2 := (t1 -F x2) in
    let/n x2 := (x2 +F x2) in
    let/n x2 := (x2 +F t1) in
    \<x0, x1, x2, x3, x4, x5\>.
End Gallina.

Section Derive.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type}
          {field_parameters : AbstractField.FieldParameters F}
          {field_representation : AbstractField.FieldRepresentation}
          {field_representation_ok : AbstractField.FieldRepresentation_ok}.

  Local Notation AFElem := Compilation2_Fp2.AFElem.

  (** ** Stack temporaries *)

  #[local, refine]
  Instance afelem_alloc_cyc : Allocable (AFElem None) :=
    {| size_in_bytes := AbstractField.felem_size_in_bytes;
       size_in_bytes_mod := AbstractField.felem_size_in_bytes_mod |}.
  Proof.
    - intros px x m0 H.
      unfold AFElem in H. destruct H as [ws H].
      apply sep_emp_l in H. destruct H as [_ H].
      apply (proj2 (AbstractField.FElem_from_bytes px m0)).
      exists ws. exact H.
    - intros px m0 H.
      apply (proj1 (AbstractField.FElem_from_bytes px m0)) in H.
      destruct H as [ws H].
      exists (AbstractField.feval ws). unfold AFElem. exists ws.
      apply sep_emp_l. split; [ split; [ reflexivity | exact I ] | exact H ].
  Defined.

  Context (Hbounds_eq : AbstractField.loose_bounds = AbstractField.tight_bounds).
  Context (mulxi : F -> F) (mulxi_name : string).

  Local Lemma tighten_bounds_AFElem_cyc x_ptr x
    : Lift1Prop.impl1 (AFElem (Some AbstractField.loose_bounds) x_ptr x)
                      (AFElem (Some AbstractField.tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.

  (** ** Callee contracts *)

  #[local] Instance spec_of_af_mul_cyc : spec_of AbstractField.mul :=
    AbstractField.binop_spec AbstractField.bin_mul.
  #[local] Instance spec_of_af_add_cyc : spec_of AbstractField.add :=
    AbstractField.binop_spec AbstractField.bin_add.
  #[local] Instance spec_of_af_sub_cyc : spec_of AbstractField.sub :=
    AbstractField.binop_spec AbstractField.bin_sub.
  #[local] Instance spec_of_af_square_cyc : spec_of AbstractField.square :=
    AbstractField.unop_spec AbstractField.un_square.

  (** Multiplication by xi: tight input, loose output (the bounds of
      [CubicFieldExtensions.spec_of_Fp2_mul_xi]). *)
  #[local] Instance un_mulxi : AbstractField.UnOp mulxi_name :=
    {| AbstractField.un_model := mulxi;
       AbstractField.un_xbounds := AbstractField.tight_bounds;
       AbstractField.un_outbounds := AbstractField.loose_bounds |}.

  #[local] Instance spec_of_af_mulxi : spec_of mulxi_name := AbstractField.unop_spec un_mulxi.

  Lemma compile_af_mulxi
        (tr : Semantics.trace) (m : mem) (l : locals) (functions : Semantics.env)
        (x : F) :
    let v := mulxi x in
    forall P (pred : P v -> predicate) (k : nlet_eq_k P v) k_impl
           Rin Rout out x_ptr x_var out_ptr out_var out_bounds,
      AbstractField.unop_spec un_mulxi functions ->
      map.get l out_var = Some out_ptr ->
      (AFElem out_bounds out_ptr out * Rout)%sep m ->
      (AFElem (Some AbstractField.tight_bounds) x_ptr x * Rin)%sep m ->
      map.get l x_var = Some x_ptr ->
      (let v := v in forall m',
         sep (AFElem (Some AbstractField.loose_bounds) out_ptr v) Rout m' ->
         (<{ Trace := tr; Memory := m'; Locals := l; Functions := functions }>
          k_impl <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      cmd.seq (cmd.call [] mulxi_name [expr.var out_var; expr.var x_var])
              k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using ext_spec_ok locals_ok mem_ok word_ok field_representation_ok.
    intro v; intros ? ? ? ? ? ? ? ? ? ? ? ?
           Hspec ? ? ? ? Hcont;
    repeat straightline'; unfold AFElem in *; sepsimpl;
    repeat match goal with H : AbstractField.feval _ = ?x |- _ => is_var x; subst x end;
    try match goal with v' := _ : F |- _ => subst v' end;
    unfold AbstractField.unop_spec in Hspec;
    eapply Semantics.weaken_call;
    [ match goal with
      | Hbx : AbstractField.bounded_by _ ?wx,
        Hsx : (AbstractField.FElem ?px ?wx * _)%sep ?mem0,
        Hso : (AbstractField.FElem ?po ?wo * ?Rr)%sep ?mem0
        |- Semantics.call _ _ ?tr0 ?mem0 _ _ =>
        eapply (Hspec po px wo wx Rr tr0 mem0);
        split; [exact Hbx |];
        split; [eexists; exact Hsx |]; exact Hso
      end
    | cbv beta;
      let t := fresh "t" in let m' := fresh "m" in let rets := fresh "rets" in
      let out' := fresh "out" in let Hfev := fresh "Hfev" in
      let Hbnd := fresh "Hbnd" in let Hsep := fresh "Hsep" in
      intros t m' rets [? [? [out' [Hfev [Hbnd Hsep]]]]]; subst;
      cbv [map.putmany_of_list_zip un_mulxi
           AbstractField.un_model AbstractField.un_outbounds] in *;
      eexists; split; [exact eq_refl |];
      apply Hcont;
      eapply Proper_sep_impl1; [| exact (fun a b => b) | exact Hsep];
      let m0 := fresh "m" in let Hf0 := fresh "Hf" in
      intros m0 Hf0; exists out'; exists map.empty, m0;
      split; [apply Properties.map.split_empty_l; reflexivity |];
      split; [| exact Hf0]; split; [exact eq_refl |]; split; eassumption ].
  Qed.

  (** Hints: squaring before multiplication (more specific pattern), mul/add/sub, mulxi. *)
  Local Hint Extern 6
    (WeakestPrecondition.cmd _ _ _ _ _
      (_ (nlet_eq _ (@AbstractField.Fmul _ _ ?x ?x) _))) =>
    simple eapply Compilation2_Fp2.compile_af_square; shelve : compiler.
  Local Hint Extern 7
    (WeakestPrecondition.cmd _ _ _ _ _
      (_ (nlet_eq _ (@AbstractField.Fmul _ _ _ _) _))) =>
    simple eapply Compilation2_Fp2.compile_af_mul; shelve : compiler.
  Local Hint Extern 7
    (WeakestPrecondition.cmd _ _ _ _ _
      (_ (nlet_eq _ (@AbstractField.Fadd _ _ _ _) _))) =>
    simple eapply Compilation2_Fp2.compile_af_add; shelve : compiler.
  Local Hint Extern 7
    (WeakestPrecondition.cmd _ _ _ _ _
      (_ (nlet_eq _ (@AbstractField.Fsub _ _ _ _) _))) =>
    simple eapply Compilation2_Fp2.compile_af_sub; shelve : compiler.
  Local Hint Extern 5
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (mulxi _) _))) =>
    simple eapply compile_af_mulxi; shelve : compiler.
  Local Hint Immediate Compilation2_Fp2.relax_bounds_AFElem : ecancel_impl.
  Local Hint Immediate Compilation2_Fp2.drop_bounds_AFElem : ecancel_impl.
  Local Hint Immediate tighten_bounds_AFElem_cyc : ecancel_impl.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  (** ** The in-place squaring *)

  #[local] Instance spec_of_af_cyc_sqr : spec_of "bls12_Fp12_cyclotomic_square" :=
    fnspec! "bls12_Fp12_cyclotomic_square"
          (p0 p1 p2 p3 p4 p5 : word) / (x0 x1 x2 x3 x4 x5 : F) R,
    { requires tr mem :=
        (AFElem (Some AbstractField.tight_bounds) p0 x0
         * AFElem (Some AbstractField.tight_bounds) p1 x1
         * AFElem (Some AbstractField.tight_bounds) p2 x2
         * AFElem (Some AbstractField.tight_bounds) p3 x3
         * AFElem (Some AbstractField.tight_bounds) p4 x4
         * AFElem (Some AbstractField.tight_bounds) p5 x5 * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists y0 y1 y2 y3 y4 y5 : F,
          (af_cyc_sqr_gallina mulxi x0 x1 x2 x3 x4 x5 = \<y0, y1, y2, y3, y4, y5\>)
          /\ (AFElem (Some AbstractField.tight_bounds) p0 y0
              * AFElem (Some AbstractField.tight_bounds) p1 y1
              * AFElem (Some AbstractField.tight_bounds) p2 y2
              * AFElem (Some AbstractField.tight_bounds) p3 y3
              * AFElem (Some AbstractField.tight_bounds) p4 y4
              * AFElem (Some AbstractField.tight_bounds) p5 y5 * R)%sep mem' }.

  Derive af_cyc_sqr_body SuchThat
         (defn! "bls12_Fp12_cyclotomic_square" ("x0", "x1", "x2", "x3", "x4", "x5")
              { af_cyc_sqr_body },
           implements (af_cyc_sqr_gallina mulxi)
                      using [AbstractField.mul; AbstractField.add; AbstractField.sub;
                             AbstractField.square; mulxi_name])
         As af_cyc_sqr_correct.
  Proof. compile. Qed.

End Derive.
