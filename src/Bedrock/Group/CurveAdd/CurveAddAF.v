(** * The a = 0 complete projective group law (RCB 2015, Algorithms 7 and 9)
      derived by Rupicola over an ARBITRARY field ([Bedrock.Specs.AbstractField]).

    [CurveAdd.v] and [PointDoubleA0.v] derive the same two bodies over the
    prime-field interface [Crypto.Bedrock.Specs.Field], whose field is
    [F M_pos]; they cannot be instantiated at Fp2.  This file repeats the
    two [let/n] chains verbatim over [AbstractField.Fadd/Fsub/Fmul] and
    derives them with the AbstractField compile lemmas of
    [FieldExtensions.Compilation2_Fp2] ([compile_af_mul/add/sub]).
    Instantiated at [bls12_Fp2] it gives the BLS12-381 G2 addition and
    doubling ([BLS12_G2_Closed.v]).

    Differences from the prime-field derivations:
    - the output buffers are [AFElem None] in the precondition (any bytes),
      so the bodies are directly usable with fresh or stale outputs (the
      G1 chain needed [RcbAnyOut.v] for that);
    - [three_b_val : F] is a Context; the loader contract states it;
    - an [Allocable] instance for [AFElem None] (stack temporaries), from
      [AbstractField.FElem_from_bytes];
    - only the mul/add/sub compile hints are registered (not the square
      or copy hints of [Compilation2_Fp2]), so the bodies call exactly
      [AbstractField.mul], [add], [sub] and the loader.

    Everything here is Qed. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Bedrock.Specs.AbstractField.
Require Bedrock.Field.FieldExtensions.Compilation2_Fp2.
Local Open Scope Z_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section Gallina.
  Context {F : Type} {field_parameters : AbstractField.FieldParameters F}.

  Local Infix "+F" := AbstractField.Fadd (at level 100).
  Local Infix "-F" := AbstractField.Fsub (at level 100).
  Local Infix "*F" := AbstractField.Fmul (at level 90).

  Context {three_b_val : F}.

  (** RCB 2015 Algorithm 7, [CurveAdd.ladderstep_gallina] letter for letter. *)
  Definition af_add_gallina
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

  (** RCB 2015 Algorithm 9, [PointDoubleA0.rcb_double_a0_gallina] letter for letter. *)
  Definition af_double_gallina
             (X1 Y1 Z1 : F) : \<< F, F, F \>> :=
    let/n three_b := stack three_b_val in
    let/n t0 := stack (Y1 *F Y1) in
    let/n Zout := (t0 +F t0) in
    let/n Zout := (Zout +F Zout) in
    let/n Zout := (Zout +F Zout) in
    let/n t1 := stack (Y1 *F Z1) in
    let/n t2 := stack (Z1 *F Z1) in
    let/n t2 := (three_b *F t2) in
    let/n Xout := (t2 *F Zout) in
    let/n Yout := (t0 +F t2) in
    let/n Zout := (t1 *F Zout) in
    let/n t1 := (t2 +F t2) in
    let/n t2 := (t1 +F t2) in
    let/n t0 := (t0 -F t2) in
    let/n Yout := (t0 *F Yout) in
    let/n Yout := (Xout +F Yout) in
    let/n t1 := (X1 *F Y1) in
    let/n Xout := (t0 *F t1) in
    let/n Xout := (Xout +F Xout) in
    \<Xout, Yout, Zout\>.
  (** In-place variants, for callers that overwrite their accumulator.
      Algorithm 7 writes its outputs only after the last read of the
      first point, so binding the outputs to the names of the first
      input (X1, Y1, Z1) is the same chain.  Algorithm 9 reads Y*Z, Z*Z
      and X*Y after its first output write; here they are computed into
      stack temporaries first (t3 holds X*Y).  Both chains are equal to
      the out-of-place ones ([af_add_ip_eq], [af_double_ip_eq]). *)
  Definition af_add_ip_gallina
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
    let/n X1 := (Y2 +F Z2) in
    let/n t5 := (t5 *F X1) in
    let/n X1 := (t1 +F t2) in
    let/n t5 := (t5 -F X1) in
    let/n Z1 := (three_b *F t2) in
    let/n X1 := (t1 -F Z1) in
    let/n Z1 := (Z1 +F t1) in
    let/n Y1 := (X1 *F Z1) in
    let/n t1 := (t0 +F t0) in
    let/n t1 := (t1 +F t0) in
    let/n t4 := (three_b *F t4) in
    let/n t0 := (t1 *F t4) in
    let/n Y1 := (Y1 +F t0) in
    let/n t0 := (t5 *F t4) in
    let/n X1 := (t3 *F X1) in
    let/n X1 := (X1 -F t0) in
    let/n t0 := (t3 *F t1) in
    let/n Z1 := (t5 *F Z1) in
    let/n Z1 := (Z1 +F t0) in
    \<X1, Y1, Z1\>.

  Definition af_double_ip_gallina
             (X1 Y1 Z1 : F) : \<< F, F, F \>> :=
    let/n three_b := stack three_b_val in
    let/n t0 := stack (Y1 *F Y1) in
    let/n t1 := stack (Y1 *F Z1) in
    let/n t2 := stack (Z1 *F Z1) in
    let/n t3 := stack (X1 *F Y1) in
    let/n Z1 := (t0 +F t0) in
    let/n Z1 := (Z1 +F Z1) in
    let/n Z1 := (Z1 +F Z1) in
    let/n t2 := (three_b *F t2) in
    let/n X1 := (t2 *F Z1) in
    let/n Y1 := (t0 +F t2) in
    let/n Z1 := (t1 *F Z1) in
    let/n t1 := (t2 +F t2) in
    let/n t2 := (t1 +F t2) in
    let/n t0 := (t0 -F t2) in
    let/n Y1 := (t0 *F Y1) in
    let/n Y1 := (X1 +F Y1) in
    let/n X1 := (t0 *F t3) in
    let/n X1 := (X1 +F X1) in
    \<X1, Y1, Z1\>.

  Lemma af_add_ip_eq X1 X2 Y1 Y2 Z1 Z2 :
    af_add_ip_gallina X1 X2 Y1 Y2 Z1 Z2 = af_add_gallina X1 X2 Y1 Y2 Z1 Z2.
  Proof. reflexivity. Qed.

  Lemma af_double_ip_eq X1 Y1 Z1 :
    af_double_ip_gallina X1 Y1 Z1 = af_double_gallina X1 Y1 Z1.
  Proof. cbv [af_double_ip_gallina af_double_gallina nlet stack]. reflexivity. Qed.
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

  #[refine]
  Instance afelem_alloc : Allocable (AFElem None) :=
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
  Context (three_b_val : F).
  Context (three_b_name : string).

  Local Lemma tighten_bounds_AFElem x_ptr x
    : Lift1Prop.impl1 (AFElem (Some AbstractField.loose_bounds) x_ptr x)
                      (AFElem (Some AbstractField.tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.

  (** ** Callee contracts *)

  Instance spec_of_af_mul : spec_of AbstractField.mul :=
    AbstractField.binop_spec AbstractField.bin_mul.
  Instance spec_of_af_add : spec_of AbstractField.add :=
    AbstractField.binop_spec AbstractField.bin_add.
  Instance spec_of_af_sub : spec_of AbstractField.sub :=
    AbstractField.binop_spec AbstractField.bin_sub.

  Instance spec_of_af_three_b : spec_of three_b_name :=
    fnspec! three_b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (AFElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (AFElem (Some AbstractField.loose_bounds) pout three_b_val * Rout)%sep mem' }.

  Lemma compile_af_load_three_b {tr m l functions}
        {P} {pred: P three_b_val -> predicate}
        {k: nlet_eq_k P three_b_val} {k_impl} :
    let v := three_b_val in
    forall R out out_ptr out_var,
      spec_of_af_three_b functions ->
      map.get l out_var = Some out_ptr ->
      (AFElem None out_ptr out * R)%sep m ->
      (let v := v in
       forall m',
         (AFElem (Some AbstractField.loose_bounds) out_ptr v * R)%sep m' ->
         (<{ Trace := tr; Memory := m'; Locals := l; Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      cmd.seq (cmd.call [] three_b_name [expr.var out_var]) k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    intros v R out out_ptr out_var Hspec Hget Hm Hk.
    repeat straightline'.
    eapply Semantics.weaken_call; [ exact (Hspec out_ptr out R tr m Hm) | ].
    cbv beta. intros tr' m' rets [Hrets [Htr Hm']]. subst.
    cbv [map.putmany_of_list_zip]. eexists; split; [ reflexivity | ].
    apply Hk. exact Hm'.
  Qed.

  (** Mul/add/sub/loader hints, and the bounds implications for [ecancel]. *)
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
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ three_b_val _))) =>
    simple eapply compile_af_load_three_b; shelve : compiler.
  Local Hint Immediate Compilation2_Fp2.relax_bounds_AFElem : ecancel_impl.
  Local Hint Immediate Compilation2_Fp2.drop_bounds_AFElem : ecancel_impl.
  Local Hint Immediate tighten_bounds_AFElem : ecancel_impl.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  (** ** Addition *)

  Instance spec_of_af_curve_add : spec_of "g2_curve_add" :=
    fnspec! "g2_curve_add"
          (pX1 pX2 pY1 pY2 pZ1 pZ2 pXout pYout pZout : word)
          / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) R,
    { requires tr mem :=
        (AFElem (Some AbstractField.tight_bounds) pX1 X1
         * AFElem (Some AbstractField.tight_bounds) pX2 X2
         * AFElem (Some AbstractField.tight_bounds) pY1 Y1
         * AFElem (Some AbstractField.tight_bounds) pY2 Y2
         * AFElem (Some AbstractField.tight_bounds) pZ1 Z1
         * AFElem (Some AbstractField.tight_bounds) pZ2 Z2
         * AFElem None pXout Xoutold
         * AFElem None pYout Youtold
         * AFElem None pZout Zoutold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Xout Yout Zout : F,
          (@af_add_gallina _ _ three_b_val X1 X2 Y1 Y2 Z1 Z2
           = \<Xout, Yout, Zout\>)
          /\ (AFElem (Some AbstractField.tight_bounds) pX1 X1
              * AFElem (Some AbstractField.tight_bounds) pX2 X2
              * AFElem (Some AbstractField.tight_bounds) pY1 Y1
              * AFElem (Some AbstractField.tight_bounds) pY2 Y2
              * AFElem (Some AbstractField.tight_bounds) pZ1 Z1
              * AFElem (Some AbstractField.tight_bounds) pZ2 Z2
              * AFElem (Some AbstractField.tight_bounds) pXout Xout
              * AFElem (Some AbstractField.tight_bounds) pYout Yout
              * AFElem (Some AbstractField.tight_bounds) pZout Zout * R)%sep mem'}.

  Derive af_curve_add_body SuchThat
         (defn! "g2_curve_add"
                ("X1", "X2", "Y1", "Y2", "Z1", "Z2", "Xout", "Yout", "Zout")
              { af_curve_add_body },
           implements @af_add_gallina _ _ three_b_val
                      using [AbstractField.mul; AbstractField.add; AbstractField.sub; three_b_name])
         As af_curve_add_correct.
  Proof. compile. Qed.

  (** ** Doubling *)

  Instance spec_of_af_curve_double : spec_of "g2_curve_double" :=
    fnspec! "g2_curve_double"
          (pXin pYin pZin pXout pYout pZout : word)
          / (X Y Z Xold Yold Zold : F) R,
    { requires tr mem :=
        (AFElem (Some AbstractField.tight_bounds) pXin X
         * AFElem (Some AbstractField.tight_bounds) pYin Y
         * AFElem (Some AbstractField.tight_bounds) pZin Z
         * AFElem None pXout Xold
         * AFElem None pYout Yold
         * AFElem None pZout Zold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Xo Yo Zo : F,
             (@af_double_gallina _ _ three_b_val X Y Z = \<Xo, Yo, Zo\>)
             /\ (AFElem (Some AbstractField.tight_bounds) pXin X
                 * AFElem (Some AbstractField.tight_bounds) pYin Y
                 * AFElem (Some AbstractField.tight_bounds) pZin Z
                 * AFElem (Some AbstractField.tight_bounds) pXout Xo
                 * AFElem (Some AbstractField.tight_bounds) pYout Yo
                 * AFElem (Some AbstractField.tight_bounds) pZout Zo * R)%sep mem' }.

  Derive af_curve_double_body SuchThat
         (defn! "g2_curve_double"
                ("Xin", "Yin", "Zin", "Xout", "Yout", "Zout")
              { af_curve_double_body },
           implements @af_double_gallina _ _ three_b_val
                      using [AbstractField.mul; AbstractField.add; AbstractField.sub; three_b_name])
         As af_curve_double_correct.
  Proof. compile. Qed.

  (** ** In-place addition and doubling (outputs overwrite the first point) *)

  Instance spec_of_af_curve_add_ip : spec_of "g2_curve_add_ip" :=
    fnspec! "g2_curve_add_ip"
          (pX1 pX2 pY1 pY2 pZ1 pZ2 : word) / (X1 X2 Y1 Y2 Z1 Z2 : F) R,
    { requires tr mem :=
        (AFElem (Some AbstractField.tight_bounds) pX1 X1
         * AFElem (Some AbstractField.tight_bounds) pX2 X2
         * AFElem (Some AbstractField.tight_bounds) pY1 Y1
         * AFElem (Some AbstractField.tight_bounds) pY2 Y2
         * AFElem (Some AbstractField.tight_bounds) pZ1 Z1
         * AFElem (Some AbstractField.tight_bounds) pZ2 Z2 * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Xo Yo Zo : F,
          (@af_add_ip_gallina _ _ three_b_val X1 X2 Y1 Y2 Z1 Z2 = \<Xo, Yo, Zo\>)
          /\ (AFElem (Some AbstractField.tight_bounds) pX1 Xo
              * AFElem (Some AbstractField.tight_bounds) pX2 X2
              * AFElem (Some AbstractField.tight_bounds) pY1 Yo
              * AFElem (Some AbstractField.tight_bounds) pY2 Y2
              * AFElem (Some AbstractField.tight_bounds) pZ1 Zo
              * AFElem (Some AbstractField.tight_bounds) pZ2 Z2 * R)%sep mem'}.

  Derive af_curve_add_ip_body SuchThat
         (defn! "g2_curve_add_ip" ("X1", "X2", "Y1", "Y2", "Z1", "Z2")
              { af_curve_add_ip_body },
           implements @af_add_ip_gallina _ _ three_b_val
                      using [AbstractField.mul; AbstractField.add; AbstractField.sub; three_b_name])
         As af_curve_add_ip_correct.
  Proof. compile. Qed.

  Instance spec_of_af_curve_double_ip : spec_of "g2_curve_double_ip" :=
    fnspec! "g2_curve_double_ip" (pX pY pZ : word) / (X Y Z : F) R,
    { requires tr mem :=
        (AFElem (Some AbstractField.tight_bounds) pX X
         * AFElem (Some AbstractField.tight_bounds) pY Y
         * AFElem (Some AbstractField.tight_bounds) pZ Z * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Xo Yo Zo : F,
             (@af_double_ip_gallina _ _ three_b_val X Y Z = \<Xo, Yo, Zo\>)
             /\ (AFElem (Some AbstractField.tight_bounds) pX Xo
                 * AFElem (Some AbstractField.tight_bounds) pY Yo
                 * AFElem (Some AbstractField.tight_bounds) pZ Zo * R)%sep mem' }.

  Derive af_curve_double_ip_body SuchThat
         (defn! "g2_curve_double_ip" ("X1", "Y1", "Z1")
              { af_curve_double_ip_body },
           implements @af_double_ip_gallina _ _ three_b_val
                      using [AbstractField.mul; AbstractField.add; AbstractField.sub; three_b_name])
         As af_curve_double_ip_correct.
  Proof. compile. Qed.

End Derive.
