(** * Compilation hints for AbstractField operations.

    Analogous to [Crypto.Bedrock.Field.Interface.Compilation2] but for
    the [AbstractField] layer used by Fp2/Fp6/Fp12 proofs.

    Provides:
    - [AFElem]: AbstractField.FElem wrapped with optional bounds
    - [compile_af_mul/add/sub/square/felem_copy]: compile lemmas
    - Hint registrations in the [compiler] database *)

Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.

Local Open Scope Z_scope.
Import bedrock2.Memory.

Section Compile.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}
          {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}
          {locals_ok : map.ok locals}
          {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type}
          {field_parameters : AbstractField.FieldParameters F}
          {field_representation : AbstractField.FieldRepresentation}
          {field_representation_ok : AbstractField.FieldRepresentation_ok}.

  Definition AFElem (mbounds : option AbstractField.bounds)
             (ptr : word) (v : F) : mem -> Prop :=
    Lift1Prop.ex1 (fun ws : AbstractField.felem =>
      (emp (AbstractField.feval ws = v /\
            match mbounds with
            | Some b => AbstractField.bounded_by b ws
            | None => True
            end)
       * AbstractField.FElem ptr ws)%sep).

  Lemma drop_bounds_AFElem ptr v bounds
    : Lift1Prop.impl1 (AFElem bounds ptr v) (AFElem None ptr v).
  Proof using mem_ok word_ok.
    unfold AFElem, Lift1Prop.impl1; intros m0 H.
    destruct H as [ws [m1 [m2 [Hsplit [[Heq [Heval Hbnd]] Hfe]]]]].
    exists ws, m1, m2. split; [exact Hsplit |]. split; [| exact Hfe].
    split; [exact Heq |]. split; [exact Heval | exact I].
  Qed.

  Lemma relax_bounds_AFElem ptr v
    : Lift1Prop.impl1 (AFElem (Some AbstractField.tight_bounds) ptr v)
                       (AFElem (Some AbstractField.loose_bounds) ptr v).
  Proof using field_representation_ok mem_ok word_ok.
    unfold AFElem, Lift1Prop.impl1; intros m0 H.
    destruct H as [ws [m1 [m2 [Hsplit [[Heq [Heval Hbnd]] Hfe]]]]].
    exists ws, m1, m2. split; [exact Hsplit |]. split; [| exact Hfe].
    split; [exact Heq |]. split; [exact Heval |].
    exact (AbstractField.relax_bounds _ Hbnd).
  Qed.

  Lemma compile_af_mul
        (tr : Semantics.trace) (m : mem) (l : locals) (functions : Semantics.env)
        (x y : F) :
    let v := AbstractField.Fmul x y in
    forall P (pred : P v -> predicate) (k : nlet_eq_k P v) k_impl
           Rx Ry Rout out x_ptr x_var y_ptr y_var out_ptr out_var bound_out,
      AbstractField.binop_spec AbstractField.bin_mul functions ->
      map.get l out_var = Some out_ptr ->
      (AFElem bound_out out_ptr out * Rout)%sep m ->
      (AFElem (Some AbstractField.loose_bounds) x_ptr x * Rx)%sep m ->
      (AFElem (Some AbstractField.loose_bounds) y_ptr y * Ry)%sep m ->
      map.get l x_var = Some x_ptr ->
      map.get l y_var = Some y_ptr ->
      (let v := v in forall m',
         sep (AFElem (Some AbstractField.tight_bounds) out_ptr v) Rout m' ->
         (<{ Trace := tr; Memory := m'; Locals := l; Functions := functions }>
          k_impl <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      cmd.seq (cmd.call [] AbstractField.mul [expr.var out_var; expr.var x_var; expr.var y_var])
              k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using ext_spec_ok locals_ok mem_ok word_ok field_representation_ok.
    intro v; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?
           Hspec ? ? ? ? ? ? Hcont;
    repeat straightline'; unfold AFElem in *; sepsimpl;
    repeat match goal with H : AbstractField.feval _ = ?x |- _ => is_var x; subst x end;
    try match goal with v' := _ : F |- _ => subst v' end;
    unfold AbstractField.binop_spec in Hspec;
    eapply Semantics.weaken_call;
    [ match goal with
      | Hbx : AbstractField.bounded_by _ ?wx, Hby : AbstractField.bounded_by _ ?wy,
        Hsx : (AbstractField.FElem ?px ?wx * _)%sep ?mem0,
        Hsy : (AbstractField.FElem ?py ?wy * _)%sep ?mem0,
        Hso : (AbstractField.FElem ?po ?wo * ?Rr)%sep ?mem0
        |- Semantics.call _ _ ?tr0 ?mem0 _ _ =>
        eapply (Hspec po px py wo wx wy Rr tr0 mem0);
        split; [exact Hbx |]; split; [exact Hby |];
        split; [eexists; exact Hsx |]; split; [eexists; exact Hsy |]; exact Hso
      end
    | cbv beta;
      let t := fresh "t" in let m' := fresh "m" in let rets := fresh "rets" in
      let out' := fresh "out" in let Hfev := fresh "Hfev" in
      let Hbnd := fresh "Hbnd" in let Hsep := fresh "Hsep" in
      intros t m' rets [? [? [out' [Hfev [Hbnd Hsep]]]]]; subst;
      cbv [map.putmany_of_list_zip
           AbstractField.bin_mul AbstractField.bin_model AbstractField.bin_outbounds] in *;
      eexists; split; [exact eq_refl |];
      apply Hcont;
      eapply Proper_sep_impl1; [| exact (fun a b => b) | exact Hsep];
      let m0 := fresh "m" in let Hf0 := fresh "Hf" in
      intros m0 Hf0; exists out'; exists map.empty, m0;
      split; [apply Properties.map.split_empty_l; reflexivity |];
      split; [| exact Hf0]; split; [exact eq_refl |]; split; eassumption ].
  Qed.

  Lemma compile_af_add
        (tr : Semantics.trace) (m : mem) (l : locals) (functions : Semantics.env)
        (x y : F) :
    let v := AbstractField.Fadd x y in
    forall P (pred : P v -> predicate) (k : nlet_eq_k P v) k_impl
           Rx Ry Rout out x_ptr x_var y_ptr y_var out_ptr out_var bound_out,
      AbstractField.binop_spec AbstractField.bin_add functions ->
      map.get l out_var = Some out_ptr ->
      (AFElem bound_out out_ptr out * Rout)%sep m ->
      (AFElem (Some AbstractField.tight_bounds) x_ptr x * Rx)%sep m ->
      (AFElem (Some AbstractField.tight_bounds) y_ptr y * Ry)%sep m ->
      map.get l x_var = Some x_ptr ->
      map.get l y_var = Some y_ptr ->
      (let v := v in forall m',
         sep (AFElem (Some AbstractField.loose_bounds) out_ptr v) Rout m' ->
         (<{ Trace := tr; Memory := m'; Locals := l; Functions := functions }>
          k_impl <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      cmd.seq (cmd.call [] AbstractField.add [expr.var out_var; expr.var x_var; expr.var y_var])
              k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using ext_spec_ok locals_ok mem_ok word_ok field_representation_ok.
    intro v; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?
           Hspec ? ? ? ? ? ? Hcont;
    repeat straightline'; unfold AFElem in *; sepsimpl;
    repeat match goal with H : AbstractField.feval _ = ?x |- _ => is_var x; subst x end;
    try match goal with v' := _ : F |- _ => subst v' end;
    unfold AbstractField.binop_spec in Hspec;
    eapply Semantics.weaken_call;
    [ match goal with
      | Hbx : AbstractField.bounded_by _ ?wx, Hby : AbstractField.bounded_by _ ?wy,
        Hsx : (AbstractField.FElem ?px ?wx * _)%sep ?mem0,
        Hsy : (AbstractField.FElem ?py ?wy * _)%sep ?mem0,
        Hso : (AbstractField.FElem ?po ?wo * ?Rr)%sep ?mem0
        |- Semantics.call _ _ ?tr0 ?mem0 _ _ =>
        eapply (Hspec po px py wo wx wy Rr tr0 mem0);
        split; [exact Hbx |]; split; [exact Hby |];
        split; [eexists; exact Hsx |]; split; [eexists; exact Hsy |]; exact Hso
      end
    | cbv beta;
      let t := fresh "t" in let m' := fresh "m" in let rets := fresh "rets" in
      let out' := fresh "out" in let Hfev := fresh "Hfev" in
      let Hbnd := fresh "Hbnd" in let Hsep := fresh "Hsep" in
      intros t m' rets [? [? [out' [Hfev [Hbnd Hsep]]]]]; subst;
      cbv [map.putmany_of_list_zip
           AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub
           AbstractField.bin_model AbstractField.bin_outbounds] in *;
      eexists; split; [exact eq_refl |];
      apply Hcont;
      eapply Proper_sep_impl1; [| exact (fun a b => b) | exact Hsep];
      let m0 := fresh "m" in let Hf0 := fresh "Hf" in
      intros m0 Hf0; exists out'; exists map.empty, m0;
      split; [apply Properties.map.split_empty_l; reflexivity |];
      split; [| exact Hf0]; split; [exact eq_refl |]; split; eassumption ].
  Qed.

  Lemma compile_af_sub
        (tr : Semantics.trace) (m : mem) (l : locals) (functions : Semantics.env)
        (x y : F) :
    let v := AbstractField.Fsub x y in
    forall P (pred : P v -> predicate) (k : nlet_eq_k P v) k_impl
           Rx Ry Rout out x_ptr x_var y_ptr y_var out_ptr out_var bound_out,
      AbstractField.binop_spec AbstractField.bin_sub functions ->
      map.get l out_var = Some out_ptr ->
      (AFElem bound_out out_ptr out * Rout)%sep m ->
      (AFElem (Some AbstractField.tight_bounds) x_ptr x * Rx)%sep m ->
      (AFElem (Some AbstractField.tight_bounds) y_ptr y * Ry)%sep m ->
      map.get l x_var = Some x_ptr ->
      map.get l y_var = Some y_ptr ->
      (let v := v in forall m',
         sep (AFElem (Some AbstractField.loose_bounds) out_ptr v) Rout m' ->
         (<{ Trace := tr; Memory := m'; Locals := l; Functions := functions }>
          k_impl <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      cmd.seq (cmd.call [] AbstractField.sub [expr.var out_var; expr.var x_var; expr.var y_var])
              k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using ext_spec_ok locals_ok mem_ok word_ok field_representation_ok.
    intro v; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?
           Hspec ? ? ? ? ? ? Hcont;
    repeat straightline'; unfold AFElem in *; sepsimpl;
    repeat match goal with H : AbstractField.feval _ = ?x |- _ => is_var x; subst x end;
    try match goal with v' := _ : F |- _ => subst v' end;
    unfold AbstractField.binop_spec in Hspec;
    eapply Semantics.weaken_call;
    [ match goal with
      | Hbx : AbstractField.bounded_by _ ?wx, Hby : AbstractField.bounded_by _ ?wy,
        Hsx : (AbstractField.FElem ?px ?wx * _)%sep ?mem0,
        Hsy : (AbstractField.FElem ?py ?wy * _)%sep ?mem0,
        Hso : (AbstractField.FElem ?po ?wo * ?Rr)%sep ?mem0
        |- Semantics.call _ _ ?tr0 ?mem0 _ _ =>
        eapply (Hspec po px py wo wx wy Rr tr0 mem0);
        split; [exact Hbx |]; split; [exact Hby |];
        split; [eexists; exact Hsx |]; split; [eexists; exact Hsy |]; exact Hso
      end
    | cbv beta;
      let t := fresh "t" in let m' := fresh "m" in let rets := fresh "rets" in
      let out' := fresh "out" in let Hfev := fresh "Hfev" in
      let Hbnd := fresh "Hbnd" in let Hsep := fresh "Hsep" in
      intros t m' rets [? [? [out' [Hfev [Hbnd Hsep]]]]]; subst;
      cbv [map.putmany_of_list_zip
           AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub
           AbstractField.bin_model AbstractField.bin_outbounds] in *;
      eexists; split; [exact eq_refl |];
      apply Hcont;
      eapply Proper_sep_impl1; [| exact (fun a b => b) | exact Hsep];
      let m0 := fresh "m" in let Hf0 := fresh "Hf" in
      intros m0 Hf0; exists out'; exists map.empty, m0;
      split; [apply Properties.map.split_empty_l; reflexivity |];
      split; [| exact Hf0]; split; [exact eq_refl |]; split; eassumption ].
  Qed.

  Lemma compile_af_square
        (tr : Semantics.trace) (m : mem) (l : locals) (functions : Semantics.env)
        (x : F) :
    let v := AbstractField.Fmul x x in
    forall P (pred : P v -> predicate) (k : nlet_eq_k P v) k_impl
           Rin Rout out x_ptr x_var out_ptr out_var out_bounds,
      AbstractField.unop_spec AbstractField.un_square functions ->
      map.get l out_var = Some out_ptr ->
      (AFElem out_bounds out_ptr out * Rout)%sep m ->
      (AFElem (Some AbstractField.loose_bounds) x_ptr x * Rin)%sep m ->
      map.get l x_var = Some x_ptr ->
      (let v := v in forall m',
         sep (AFElem (Some AbstractField.tight_bounds) out_ptr v) Rout m' ->
         (<{ Trace := tr; Memory := m'; Locals := l; Functions := functions }>
          k_impl <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      cmd.seq (cmd.call [] AbstractField.square [expr.var out_var; expr.var x_var])
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
      cbv [map.putmany_of_list_zip
           AbstractField.un_square AbstractField.Fsquare
           AbstractField.un_model AbstractField.un_outbounds] in *;
      eexists; split; [exact eq_refl |];
      apply Hcont;
      eapply Proper_sep_impl1; [| exact (fun a b => b) | exact Hsep];
      let m0 := fresh "m" in let Hf0 := fresh "Hf" in
      intros m0 Hf0; exists out'; exists map.empty, m0;
      split; [apply Properties.map.split_empty_l; reflexivity |];
      split; [| exact Hf0]; split; [exact eq_refl |]; split; eassumption ].
  Qed.

  Lemma compile_af_felem_copy
        (tr : Semantics.trace) (m : mem) (l : locals) (functions : Semantics.env)
        (x : F) :
    let v := x in
    forall P (pred : P v -> predicate) (k : nlet_eq_k P v) k_impl
           R x_ptr x_var out out_ptr out_var x_bound out_bound,
      AbstractField.spec_of_felem_copy functions ->
      map.get l out_var = Some out_ptr ->
      (AFElem x_bound x_ptr x * AFElem out_bound out_ptr out * R)%sep m ->
      map.get l x_var = Some x_ptr ->
      (let v := v in forall m',
         (AFElem x_bound x_ptr x * AFElem x_bound out_ptr x * R)%sep m' ->
         (<{ Trace := tr; Memory := m'; Locals := l; Functions := functions }>
          k_impl <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      cmd.seq (cmd.call [] AbstractField.felem_copy [expr.var out_var; expr.var x_var])
              k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof using ext_spec_ok locals_ok mem_ok word_ok field_representation_ok.
    intro v; intros ? ? ? ? ? ? ? ? ? ? ? ?
           Hspec Hget_out Hmem Hget_x Hcont.
    repeat straightline'.
    unfold AFElem in *; sepsimpl.
    repeat match goal with
    | H : AbstractField.feval _ = ?x |- _ => is_var x; subst x
    end.
    try match goal with v' := _ : F |- _ => subst v' end.
    eapply Semantics.weaken_call.
    { eapply Hspec; split; [ | ecancel_assumption ]; ecancel_assumption. }
    intros ? ? ? [? [? ?]]; subst.
    cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |].
    apply Hcont.
    extract_ex1_and_emp_in_goal.
    all: try ecancel_assumption.
    all: eauto.
    split; [ecancel_assumption |].
    split; (split; [reflexivity | assumption]).
  Qed.

End Compile.

(** Hint registrations for the [compiler] database. *)

#[export] Hint Extern 7
  (WeakestPrecondition.cmd _ _ _ _ _
    (_ (nlet_eq _ (@AbstractField.Fmul _ _ _ _) _))) =>
  simple eapply compile_af_mul; shelve : compiler.

#[export] Hint Extern 7
  (WeakestPrecondition.cmd _ _ _ _ _
    (_ (nlet_eq _ (@AbstractField.Fadd _ _ _ _) _))) =>
  simple eapply compile_af_add; shelve : compiler.

#[export] Hint Extern 7
  (WeakestPrecondition.cmd _ _ _ _ _
    (_ (nlet_eq _ (@AbstractField.Fsub _ _ _ _) _))) =>
  simple eapply compile_af_sub; shelve : compiler.

#[export] Hint Extern 6
  (WeakestPrecondition.cmd _ _ _ _ _
    (_ (nlet_eq _ (@AbstractField.Fmul _ _ ?x ?x) _))) =>
  simple eapply compile_af_square; shelve : compiler.

#[export] Hint Extern 9
  (WeakestPrecondition.cmd _ _ _ _ _
    (_ (nlet_eq _ ?v _))) =>
  is_var v; simple eapply compile_af_felem_copy; shelve : compiler.

#[export] Hint Immediate relax_bounds_AFElem : ecancel_impl.
#[export] Hint Immediate drop_bounds_AFElem : ecancel_impl.
