(** * BLS12_GLV_Prog — the bedrock2 GLV Shamir loop, program order, no algebraic premises.

    [BLS12_GLV_ScalarMultBedrock.glv_shamir_func] (unchanged, imported) is
    proved here against callee contracts that name two arbitrary Gallina
    functions [add] and [dbl] for the aliased addition and the in-place
    doubling, with no law about them.  The output is the program-order
    Gallina value [glv_prog_output add dbl k1 k2 P Phi]: 129 LSB-first
    iterations of
       out := add out (if bit_i k1 then P else O);
       out := add out (if bit_i k2 then Phi else O);
       P := dbl P;  Phi := dbl Phi
    from out = O = (0 : 1 : 0).  The proof is the one of
    [BLS12_GLV_ScalarMultBedrock.glv_shamir_ok] with the invariant
    restated in program order, and two callee contracts replaced:
    - the conditional move is an in-place contract [CmovInplaceOK]
      (aux := if c = 0 then aux else Q; output aliased with the first
      input, as in the program), in place of [spec_of_group_cmov_alt]
      whose only implementation is not proved;
    - ["store_zero"] by the [StoreZero3OK] shape of [BLS12_MSM].
    The functional correctness (k1 P + k2 Phi up to pt_eq on the RCB
    formulas) is in [BLS12_GLV_Functional]. *)

From Stdlib Require Import ZArith Lia.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import bedrock2.Loops.
Require Import bedrock2.NotationsCustomEntry.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_ScalarMultBedrock.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** ** The program-order Gallina function *)
Section ProgOrder.
  Context {G : Type} (idp : G) (add : G -> G -> G) (dbl : G -> G).

  Definition glv_step (k1 k2 : Z) (i : nat) (s : G * G * G) : G * G * G :=
    let '(out, p, q) := s in
    let out1 := add out (if Z.testbit k1 (Z.of_nat i) then p else idp) in
    let out2 := add out1 (if Z.testbit k2 (Z.of_nat i) then q else idp) in
    (out2, dbl p, dbl q).

  Fixpoint glv_state (k1 k2 : Z) (p q : G) (n : nat) : G * G * G :=
    match n with
    | O => (idp, p, q)
    | S n' => glv_step k1 k2 n' (glv_state k1 k2 p q n')
    end.

  Definition glv_prog_output (k1 k2 : Z) (p q : G) : G :=
    fst (fst (glv_state k1 k2 p q 129)).
End ProgOrder.

Section GLV_Prog_Generic.
  Context {width : Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
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
          {field_representation_ok : FieldRepresentation_ok}
          {group_cmov_alt : string}
          {store_zero : string}.

  Local Notation F := (F M_pos).
  Local Notation Fzero := (F.of_Z M_pos 0).
  Local Notation Fone := (F.of_Z M_pos 1).

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (curve_add_name : string).
  Context (curve_double_name : string).

  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Context (cmov_name : string).
  Context (add : F * F * F -> F * F * F -> F * F * F).
  Context (dbl : F * F * F -> F * F * F).

  Let glv_scalar_words : nat := 2.
  Let glv_iterations : Z := 129.

  Local Notation eval_bignum n x :=
    (Positional.eval (uweight width) n (List.map word.unsigned x)).

  (** Two-word [shift_scalar]: the low bit into [pc], the bignum shifted right by one. *)
  Local Instance spec_of_shift_scalar : spec_of "shift_scalar" :=
    fnspec! "shift_scalar"
          (pc px : word)
          / c x R,
    { requires tr mem :=
        (Bignum.Bignum glv_scalar_words px x ⋆ scalar pc c ⋆ R) mem;
      ensures tr' mem' :=
        exists c' x',
          tr = tr'
          /\ eval_bignum glv_scalar_words x / 2 = eval_bignum glv_scalar_words x'
          /\ eval_bignum glv_scalar_words x mod 2 = word.unsigned c'
          /\ ((Bignum.Bignum glv_scalar_words px x' ⋆ scalar pc c' ⋆ R) mem')}.

  Local Notation idp := (Fzero, Fone, Fzero).

  (** The program, as defined (and printed) in [BLS12_GLV_ScalarMultBedrock]. *)
  Definition glv_prog : function_t :=
    glv_shamir_func (group_cmov_alt := cmov_name) curve_add_name curve_double_name.

  (** In-place conditional move, the shape of the program's two calls
      [cmov(aux, aux, Q, cond)]: aux := if c = 0 then aux else Q. *)
  Definition CmovInplaceOK (functions : Semantics.env) : Prop :=
    forall (pX pY pZ pX2 pY2 pZ2 pc : word) (X Y Z X2 Y2 Z2 : F) (c : word) R tr m,
      (FElem (Some tight_bounds) pX X ⋆ FElem (Some tight_bounds) pY Y
       ⋆ FElem (Some tight_bounds) pZ Z ⋆ FElem (Some tight_bounds) pX2 X2
       ⋆ FElem (Some tight_bounds) pY2 Y2 ⋆ FElem (Some tight_bounds) pZ2 Z2
       ⋆ scalar pc c ⋆ R) m ->
      Semantics.call functions cmov_name tr m
        [pX; pY; pZ; pX; pY; pZ; pX2; pY2; pZ2; pc]
        (fun tr' m' rets => rets = [] /\ (tr = tr' /\
           let '(X', Y', Z') := (if word.eqb c (word.of_Z 0) then (X, Y, Z) else (X2, Y2, Z2)) in
           (FElem (Some tight_bounds) pX X' ⋆ FElem (Some tight_bounds) pY Y'
            ⋆ FElem (Some tight_bounds) pZ Z' ⋆ FElem (Some tight_bounds) pX2 X2
            ⋆ FElem (Some tight_bounds) pY2 Y2 ⋆ FElem (Some tight_bounds) pZ2 Z2
            ⋆ scalar pc c ⋆ R) m')).

  (** ["store_zero"]: the [BLS12_MSM.StoreZero3OK] shape. *)
  Definition StoreZeroOK (functions : Semantics.env) : Prop :=
    forall (pX pY pZ : word) (Xv Yv Zv : F) R tr m,
      (FElem None pX Xv ⋆ FElem None pY Yv ⋆ FElem None pZ Zv ⋆ R) m ->
      Semantics.call functions "store_zero" tr m [pX; pY; pZ]
        (fun tr' m' rets => rets = [] /\ (tr = tr' /\
           (FElem (Some tight_bounds) pX Fzero ⋆ FElem (Some tight_bounds) pY Fone
            ⋆ FElem (Some tight_bounds) pZ Fzero ⋆ R) m')).

  (** Aliased addition [add(out, Q, out)] (as [BLS12_MSM.CurveAddAliasedOK]). *)
  Definition AddAliasedOK (functions : Semantics.env) : Prop :=
    forall pXo pX2 pYo pY2 pZo pZ2 (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
      (FElem (Some tight_bounds) pXo X ⋆ FElem (Some tight_bounds) pX2 X2'
       ⋆ FElem (Some tight_bounds) pYo Y ⋆ FElem (Some tight_bounds) pY2 Y2'
       ⋆ FElem (Some tight_bounds) pZo Z ⋆ FElem (Some tight_bounds) pZ2 Z2'
       ⋆ R0) m0 ->
      Semantics.call functions curve_add_name tr0 m0
        [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
        (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
           let '(Xo', Yo', Zo') := add (X, Y, Z) (X2', Y2', Z2') in
           (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pX2 X2'
            ⋆ FElem (Some tight_bounds) pYo Yo' ⋆ FElem (Some tight_bounds) pY2 Y2'
            ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pZ2 Z2'
            ⋆ R0) m')).

  (** In-place doubling (as [BLS12_MSM.CurveDoubleInplaceOK]). *)
  Definition DoubleInplaceOK (functions : Semantics.env) : Prop :=
    forall pX pY pZ (X Y Z : F) R0 tr0 m0,
      (FElem (Some tight_bounds) pX X ⋆ FElem (Some tight_bounds) pY Y
       ⋆ FElem (Some tight_bounds) pZ Z ⋆ R0) m0 ->
      Semantics.call functions curve_double_name tr0 m0
        [pX; pY; pZ; pX; pY; pZ]
        (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
           let '(Xo, Yo, Zo) := dbl (X, Y, Z) in
           (FElem (Some tight_bounds) pX Xo ⋆ FElem (Some tight_bounds) pY Yo
            ⋆ FElem (Some tight_bounds) pZ Zo ⋆ R0) m')).

  Local Notation eval n x := (Positional.eval (uweight width) n (List.map word.unsigned x)).

  Local Lemma eval_nonneg_2 (x : list word) : 0 <= eval 2 x.
  Proof.
    unfold Positional.eval, Positional.to_associational, Associational.eval.
    destruct x as [|w0 [|w1 rest]]; simpl;
    unfold uweight, ModOps.weight; simpl;
    try (pose proof (word.unsigned_range w0));
    try (pose proof (word.unsigned_range w1));
    try (assert (0 < 2 ^ width) by (apply Z.pow_pos_nonneg; lia));
    try nia; lia.
  Qed.

  Definition spec_of_glv_prog (functions : Semantics.env) : Prop :=
    forall (pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2 : word)
           (Outx Outy Outz Px Py Pz Phix Phiy Phiz : F)
           (k1_words k2_words : list word) R tr mem,
      0 <= eval glv_scalar_words k1_words < 2 ^ glv_iterations ->
      0 <= eval glv_scalar_words k2_words < 2 ^ glv_iterations ->
      (FElem (Some tight_bounds) pOutx Outx
       * FElem (Some tight_bounds) pOuty Outy
       * FElem (Some tight_bounds) pOutz Outz
       * FElem (Some tight_bounds) pPx Px
       * FElem (Some tight_bounds) pPy Py
       * FElem (Some tight_bounds) pPz Pz
       * FElem (Some tight_bounds) pPhix Phix
       * FElem (Some tight_bounds) pPhiy Phiy
       * FElem (Some tight_bounds) pPhiz Phiz
       * Bignum.Bignum glv_scalar_words pk1 k1_words
       * Bignum.Bignum glv_scalar_words pk2 k2_words
       * R)%sep mem ->
      WeakestPrecondition.call functions "bls12_glv_shamir" tr mem
        [pOutx; pOuty; pOutz; pPx; pPy; pPz; pPhix; pPhiy; pPhiz; pk1; pk2]
        (fun tr' mem' rets => rets = [] /\
          tr = tr'
          /\ exists Outxnew Outynew Outznew Pxnew Pynew Pznew Phixnew Phiynew Phiznew : F,
             exists k1new k2new : list word,
               (Outxnew, Outynew, Outznew) =
                 glv_prog_output idp add dbl
                   (eval glv_scalar_words k1_words) (eval glv_scalar_words k2_words)
                   (Px, Py, Pz) (Phix, Phiy, Phiz)
               /\ (FElem (Some tight_bounds) pOutx Outxnew
                  * FElem (Some tight_bounds) pOuty Outynew
                  * FElem (Some tight_bounds) pOutz Outznew
                  * FElem (Some tight_bounds) pPx Pxnew
                  * FElem (Some tight_bounds) pPy Pynew
                  * FElem (Some tight_bounds) pPz Pznew
                  * FElem (Some tight_bounds) pPhix Phixnew
                  * FElem (Some tight_bounds) pPhiy Phiynew
                  * FElem (Some tight_bounds) pPhiz Phiznew
                  * Bignum.Bignum glv_scalar_words pk1 k1new
                  * Bignum.Bignum glv_scalar_words pk2 k2new
                  * R)%sep mem').


  Definition glv_loop_inv
    (pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz : word)
    (pk1 pk2 : word) (a_auxx a_auxy a_auxz a_cond1 a_cond2 a_iter : word)
    (Px_init Py_init Pz_init Phix_init Phiy_init Phiz_init : F)
    (k1_init k2_init : Z)
    (R : mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\
    exists (Outx Outy Outz Px Py Pz Phix Phiy Phiz
            Auxx Auxy Auxz : F)
           (k1_words k2_words : list word)
           (c1 c2 : word) (iter_word : word),
      let iter := (129 - Z.of_nat v)%Z in
      (* Scalar invariants *)
      eval glv_scalar_words k1_words = Z.shiftr k1_init iter
      /\ eval glv_scalar_words k2_words = Z.shiftr k2_init iter
      (* Accumulator invariant *)
      /\ (Outx, Outy, Outz) = fst (fst (glv_state idp add dbl k1_init k2_init
             (Px_init, Py_init, Pz_init) (Phix_init, Phiy_init, Phiz_init) (Z.to_nat iter)))
      /\ (Px, Py, Pz) = snd (fst (glv_state idp add dbl k1_init k2_init
             (Px_init, Py_init, Pz_init) (Phix_init, Phiy_init, Phiz_init) (Z.to_nat iter)))
      /\ (Phix, Phiy, Phiz) = snd (glv_state idp add dbl k1_init k2_init
             (Px_init, Py_init, Pz_init) (Phix_init, Phiy_init, Phiz_init) (Z.to_nat iter))
      (* Memory layout — grouped into Point3 triples to reduce sep conjuncts *)
      /\ (Point3 (Some tight_bounds) pOutx pOuty pOutz Outx Outy Outz
         * Point3 (Some tight_bounds) pPx pPy pPz Px Py Pz
         * Point3 (Some tight_bounds) pPhix pPhiy pPhiz Phix Phiy Phiz
         * Point3 None a_auxx a_auxy a_auxz Auxx Auxy Auxz
         * Bignum.Bignum glv_scalar_words pk1 k1_words
         * Bignum.Bignum glv_scalar_words pk2 k2_words
         * scalar a_cond1 c1
         * scalar a_cond2 c2
         * scalar a_iter iter_word
         * R)%sep m
      (* Locals bindings *)
      /\ map.get l "outx" = Some pOutx
      /\ map.get l "outy" = Some pOuty
      /\ map.get l "outz" = Some pOutz
      /\ map.get l "px" = Some pPx
      /\ map.get l "py" = Some pPy
      /\ map.get l "pz" = Some pPz
      /\ map.get l "phix" = Some pPhix
      /\ map.get l "phiy" = Some pPhiy
      /\ map.get l "phiz" = Some pPhiz
      /\ map.get l "pk1" = Some pk1
      /\ map.get l "pk2" = Some pk2
      /\ map.get l "auxx" = Some a_auxx
      /\ map.get l "auxy" = Some a_auxy
      /\ map.get l "auxz" = Some a_auxz
      /\ map.get l "cond1" = Some a_cond1
      /\ map.get l "cond2" = Some a_cond2
      /\ map.get l "iter" = Some a_iter
      /\ word.unsigned iter_word = iter
      (* Measure: v counts down from 129 to 0 *)
      /\ v = Z.to_nat (glv_iterations - iter).

  Opaque felem_size_in_bytes.
  Opaque Memory.bytes_per_word.
  Opaque glv_scalar_words.
  Opaque glv_iterations.
  (** * Section 5: Correctness lemma                                    *)
  (* ================================================================== *)

  (** Resolve map.get on abstract locals using hypotheses *)
  Local Ltac resolve_map_get :=
    match goal with
    | |- map.get (map.put ?m ?k ?v) ?k' = Some ?e =>
      first
      [ unify k k';
        rewrite map.get_put_same; exact eq_refl
      | rewrite map.get_put_diff by congruence;
        resolve_map_get ]
    | |- map.get ?m ?k = Some ?e =>
      first
      [ assumption
      | match goal with
        | H : map.get m k = Some _ |- _ => exact H
        end ]
    end.

  (** Evaluate dexprs with abstract locals *)
  Local Ltac eval_dexprs_abstract :=
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | eexists; split; [resolve_map_get |]
      | eexists; split; [exact eq_refl |]
      ]).

  (** Process cmd.seq/set with abstract locals *)
  Local Ltac glv_straightline :=
    match goal with
    | |- WeakestPrecondition.cmd _ (cmd.seq _ _) _ _ _ _ =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body]
    | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |]
    | |- WeakestPrecondition.cmd _ cmd.skip _ _ _ ?post =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body]
    end.

  (** The WP proof for the GLV Shamir function.

      PROOF STRATEGY:
      1. Function entry: start_func, process 6 stackallocs
         (3 felem + 3 word-sized), convert anybytes to FElem/scalar.
      2. Initialization: process store_zero(outx,outy,outz) call,
         then store iter=0.
      3. While loop: apply Loops.while_localsmap with glv_loop_inv.
      4. Loop body: 11 calls per iteration.
      5. Post-loop: stack deallocation + postcondition.

      Callee specs are taken as hypotheses since this is in a
      generic section.  The function body uses:
        "store_zero"    -- literal string
        "shift_scalar"  -- literal string
        group_cmov_alt  -- section variable
        curve_add_name  -- section variable *)

  Lemma word_eqb0_b2z (x : word) (b : bool) :
    word.unsigned x = Z.b2z b -> word.eqb x (word.of_Z 0) = negb b.
  Proof.
    intros Hx. rewrite word.unsigned_eqb, word.unsigned_of_Z_0, Hx.
    destruct b; reflexivity.
  Qed.

  Lemma glv_prog_ok :
    forall functions
      (EnvContains : map.get functions "bls12_glv_shamir" = Some (snd glv_prog))
      (HStoreZero : StoreZeroOK functions)
      (HShiftScalar : spec_of_shift_scalar functions)
      (HCmovInplace : CmovInplaceOK functions)
      (HCurveAddInplace : AddAliasedOK functions)
      (HCurveDouble : DoubleInplaceOK functions),
    spec_of_glv_prog functions.
  Proof.
    intros.
    unfold spec_of_glv_prog.
    intros pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
           Outx Outy Outz Px Py Pz Phix Phiy Phiz
           k1_words k2_words R tr mem0 Hk1_bound Hk2_bound Hsep.

    (* === Phase 1: Function entry === *)
    eapply WeakestPreconditionProperties.start_func;
      [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold glv_prog, glv_shamir_func. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* === Phase 2: Process 6 stackallocs === *)
    (* Stackalloc 1: auxx (felem-sized) *)
    repeat straightline.
    split. { apply felem_size_in_bytes_mod. }
    intros a_auxx mStack_auxx mComb_auxx Hany_auxx Hsplit_auxx.
    repeat straightline.

    (* Stackalloc 2: auxy (felem-sized) *)
    split. { apply felem_size_in_bytes_mod. }
    intros a_auxy mStack_auxy mComb_auxy Hany_auxy Hsplit_auxy.
    repeat straightline.

    (* Stackalloc 3: auxz (felem-sized) *)
    split. { apply felem_size_in_bytes_mod. }
    intros a_auxz mStack_auxz mComb_auxz Hany_auxz Hsplit_auxz.
    repeat straightline.

    (* Stackalloc 4: cond1 (word-sized) *)
    split. { apply Z_mod_same_full. }
    intros a_cond1 mStack_cond1 mComb_cond1 Hany_cond1 Hsplit_cond1.
    repeat straightline.

    (* Stackalloc 5: cond2 (word-sized) *)
    split. { apply Z_mod_same_full. }
    intros a_cond2 mStack_cond2 mComb_cond2 Hany_cond2 Hsplit_cond2.
    repeat straightline.

    (* Stackalloc 6: iter (word-sized) *)
    split. { apply Z_mod_same_full. }
    intros a_iter mStack_iter mComb_iter Hany_iter Hsplit_iter.

    (* Convert felem anybytes to FElem None using P_from_bytes from felem_alloc.
       P_from_bytes : forall px, impl1 (anybytes px sz) (ex1 (FElem None px))
       i.e., forall px m, anybytes px sz m -> exists x, FElem None px x m *)
    pose proof (P_from_bytes a_auxx mStack_auxx Hany_auxx)
      as [Auxx_init Hfe_auxx].
    pose proof (P_from_bytes a_auxy mStack_auxy Hany_auxy)
      as [Auxy_init Hfe_auxy].
    pose proof (P_from_bytes a_auxz mStack_auxz Hany_auxz)
      as [Auxz_init Hfe_auxz].

    (* Convert word-sized anybytes to scalars *)
    apply anybytes_to_scalar in Hany_cond1 as [c1_init Hsc_cond1].
    apply anybytes_to_scalar in Hany_cond2 as [c2_init Hsc_cond2].
    apply anybytes_to_scalar in Hany_iter as [iter_init Hsc_iter].

    (* === Phase 3: Process store_zero initialization ===

       The goal is a WP for:
         cmd.seq (cmd.call "store_zero" [outx; outy; outz])
           (cmd.seq (cmd.store iter 0) (cmd.while ...))
       followed by 6 stack deallocations.

       The memory mComb_iter contains:
       - Original inputs (FElem tight for out/p/phi, Bignum for k1/k2, R)
         embedded in the map.split chain from stackallocs
       - Stack FElems (FElem None for auxx/auxy/auxz)
       - Stack scalars (scalar for cond1/cond2/iter)

       We process the store_zero call:
       1. cmd.seq → expose the call
       2. dexprs for arguments [outx; outy; outz]
       3. weaken_call with HStoreZero
       4. Precondition: need FElem None, have FElem (Some tight_bounds)
          → use drop_bounds_FElem to weaken
       5. Postcondition: FElem tight with Fzero/Fone/Fzero (identity)

       Then process store(iter, 0) via straightline.

       Then apply Loops.while_localsmap with glv_loop_inv.

       === Phase 4: while_localsmap application ===
       Apply with:
       - measure v0 := 129 (nat)
       - lt := Nat.lt, well_founded := lt_wf
       - invariant := glv_loop_inv with initial P/phi/k1/k2 values

       Initial invariant (v0=129, iter=0):
       - k1/k2 unchanged (shiftr by 0 = identity)
       - out = identity = curve_add (scmul 0 P) (scmul 0 phi)
       - P = P_init = scmul (2^0) P_init
       - phi = phi_init = scmul (2^0) phi_init

       === Phase 5: Loop body (11 function calls/iteration) ===
       For measure v, the body processes:
       a. store iter = iter + 1
       b. shift_scalar(cond1, pk1): extract k1's low bit, shift k1
       c. shift_scalar(cond2, pk2): extract k2's low bit, shift k2
       d. store_zero(aux) + group_cmov_alt(aux,aux,P,cond1):
          aux = cond1 ? P : O
       e. curve_add(out, aux, out): out += aux
       f. store_zero(aux) + group_cmov_alt(aux,aux,phi,cond2):
          aux = cond2 ? phi : O
       g. curve_add(out, aux, out): out += aux
       h. curve_add(P, P, P): P = 2*P
       i. curve_add(phi, phi, phi): phi = 2*phi

       Each call: glv_straightline + unfold cmd.call + dexprs_abstract
       + weaken_call + sep manipulation. (~300 lines total)

       Invariant preservation: Z arithmetic for scalar decomposition
       (k_init mod 2^(iter+1) decomposition) + scmul_glv properties.

       === Phase 6: Post-loop ===
       After 129 iterations: out = [k1]P + [k2]phi.
       6 stack deallocations (FElem→anybytes, scalar→anybytes).
       Final postcondition: existentials + sep.
       (~100 lines following MillerLoop.v lines 1701-1800) *)

    (* === Tactic: gcall processes one function call end-to-end === *)
    (* Modeled on WPTactics.wp_call + BLS12_377 MillerLoop mcall.
       Handles binop (curve_add), custom fnspec (store_zero, cmov_alt),
       and shift_scalar specs. Avoids repeat straightline. *)
    (* Custom postcall: beta-reduce before matching (fixes abstract locals) *)
    Local Ltac glv_postcall :=
      let t := fresh "t" in let m := fresh "m" in let rets := fresh "rets" in
      let H := fresh "Hpost" in
      intros t m rets H;
      cbv beta in H;
      lazymatch type of H with
      | ?A /\ ?B =>
        let Hrets := fresh "Hrets" in let Hrest := fresh "Hrest" in
        destruct H as [Hrets Hrest];
        subst rets;
        lazymatch type of Hrest with
        | ?C /\ ?D =>
          let Htr := fresh "Htr" in let Hrem := fresh "Hrem" in
          destruct Hrest as [Htr Hrem];
          first [ symmetry in Htr; subst t | subst t | idtac ];
          cbv [map.putmany_of_list_zip];
          (try (eexists; split; [ exact eq_refl | ]))
        | _ =>
          first [ subst t | idtac ];
          cbv [map.putmany_of_list_zip];
          (try (eexists; split; [ exact eq_refl | ]))
        end
      end.

    (* Fast cancel for impl1: match syntactically unifiable non-evar
       conjuncts. Standard cancel_step only handles iff1, not impl1.
       ecancel_step_by_implication can't match equal pairs either
       (it relies on ecancel_impl hints which don't include reflexivity). *)
    Local Ltac cancel_impl_step :=
      let RHS := lazymatch goal with
                 | |- Lift1Prop.impl1 (seps _) (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (idtac; let y := rdelta_var y in is_evar y);
      let LHS := lazymatch goal with
                 | |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
      let i := find_syntactic_unify_deltavar LHS y in
      cancel_seps_at_indices_by_implication i j;
      [exact (impl1_refl _)|].

    (* ecancel with fast impl1 syntactic pre-pass *)
    Local Ltac ecancel_fast :=
      cancel;
      lazymatch goal with
      | |- Lift1Prop.impl1 _ _ =>
        repeat cancel_impl_step;
        repeat ecancel_step_by_implication;
        cbv [seps]; exact impl1_refl
      | |- Lift1Prop.iff1 _ _ =>
        ecancel_steps_at O;
        ecancel_done
      end.

    (* ecancel_assumption using the fast impl1 path.
       Copies the hypothesis first (like ecancel_assumption_with_copy)
       so multi-sep specs (e.g., cmov_alt) can reuse it.
       Handles let-match bindings from curve_add postconditions
       (let '(X,Y,Z) := curve_add ... in sep) by destructing the pair. *)
    Local Ltac ecancel_assumption_fast :=
      multimatch goal with
      | |- ?PG ?m1 =>
        multimatch goal with
        | H: _ ?m2 |- _ =>
          syntactic_unify_deltavar m1 m2;
          let H' := fresh "Hcopy" in
          pose proof H as H';
          cbv beta iota zeta in H';
          lazymatch type of H' with
          | (_ * _)%sep _ =>
            refine (Morphisms.subrelation_refl
                      Lift1Prop.impl1 _ _ _ _ H');
            clear H';
            ecancel_fast
          end
        end
      end.

    Local Ltac gcall spec :=
      try glv_straightline;
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |];
      eapply Semantics.weaken_call;
      [ let H := fresh "Hcall" in pose proof spec as H; eapply H;
        first
        [ wp_binop_precond solve_bounds_auto
        | wp_unop_precond solve_bounds_auto
        | split; ecancel_assumption_fast
        | ecancel_assumption_fast
        | repeat (first
            [ solve_bounds_auto
            | ecancel_assumption_fast
            | split ])
        ]
      | glv_postcall ];
      (* Destruct postcondition existentials *)
      repeat match goal with
      | H : exists _, _ |- _ => destruct H
      end;
      repeat match goal with
      | H : _ /\ _ |- _ =>
          lazymatch type of H with
          | _ = _ /\ _ => destruct H
          | _ /\ _ => destruct H
          end
      end;
      try match goal with
      | H : ?tr = ?t |- _ => first [ subst t | subst tr | idtac ]
      end.

    (* === Phase 3: Process store_zero call + store iter=0 === *)
    (* Process let/d and peel cmd.seq for the store_zero call *)
    cbv [dlet.dlet]. set (l4 := map.put l3 "iter" a_iter).
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    (* Call store_zero. The sep is fragmented across map.split chains.
       Reassemble into a single sep on mComb_iter, then use ecancel_assumption_impl
       which handles FElem (Some tight) -> FElem None via drop_bounds_FElem hint. *)
    destruct Hsplit_auxx as [Heq_auxx Hd_auxx].
    destruct Hsplit_auxy as [Heq_auxy Hd_auxy].
    destruct Hsplit_auxz as [Heq_auxz Hd_auxz].
    destruct Hsplit_cond1 as [Heq_cond1 Hd_cond1].
    destruct Hsplit_cond2 as [Heq_cond2 Hd_cond2].
    destruct Hsplit_iter as [Heq_iter Hd_iter].
    subst mComb_iter mComb_cond2 mComb_cond1 mComb_auxz mComb_auxy mComb_auxx.
    (* Build combined sep using sep_from_put/sep witnesses *)
    assert (HsepAll :
      (FElem (Some tight_bounds) pOutx Outx
       ⋆ FElem (Some tight_bounds) pOuty Outy
       ⋆ FElem (Some tight_bounds) pOutz Outz
       ⋆ FElem (Some tight_bounds) pPx Px
       ⋆ FElem (Some tight_bounds) pPy Py
       ⋆ FElem (Some tight_bounds) pPz Pz
       ⋆ FElem (Some tight_bounds) pPhix Phix
       ⋆ FElem (Some tight_bounds) pPhiy Phiy
       ⋆ FElem (Some tight_bounds) pPhiz Phiz
       ⋆ Bignum glv_scalar_words pk1 k1_words
       ⋆ Bignum glv_scalar_words pk2 k2_words
       ⋆ R
       ⋆ Compilation2.FElem None a_auxx Auxx_init
       ⋆ Compilation2.FElem None a_auxy Auxy_init
       ⋆ Compilation2.FElem None a_auxz Auxz_init
       ⋆ scalar a_cond1 c1_init
       ⋆ scalar a_cond2 c2_init
       ⋆ scalar a_iter iter_init)
      (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy) mStack_auxz) mStack_cond1) mStack_cond2) mStack_iter)).
    { (* Each putmany step: (P * Q)(putmany m1 m2) from P m1 and Q m2 and disjoint m1 m2 *)
      (* iter *)
      exists (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy) mStack_auxz) mStack_cond1) mStack_cond2), mStack_iter.
      split. { split; [reflexivity | exact Hd_iter]. }
      split; [| exact Hsc_iter].
      (* cond2 *)
      exists (map.putmany (map.putmany (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy) mStack_auxz) mStack_cond1), mStack_cond2.
      split. { split; [reflexivity | exact Hd_cond2]. }
      split; [| exact Hsc_cond2].
      (* cond1 *)
      exists (map.putmany (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy) mStack_auxz), mStack_cond1.
      split. { split; [reflexivity | exact Hd_cond1]. }
      split; [| exact Hsc_cond1].
      (* auxz *)
      exists (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy), mStack_auxz.
      split. { split; [reflexivity | exact Hd_auxz]. }
      split; [| exact Hfe_auxz].
      (* auxy *)
      exists (map.putmany mem0 mStack_auxx), mStack_auxy.
      split. { split; [reflexivity | exact Hd_auxy]. }
      split; [| exact Hfe_auxy].
      (* auxx *)
      exists mem0, mStack_auxx.
      split. { split; [reflexivity | exact Hd_auxx]. }
      split; [ecancel_assumption | exact Hfe_auxx]. }

    exists [pOutx; pOuty; pOutz]. split.
    { cbv [dexprs list_map list_map_body WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
      repeat (first [exact eq_refl | eexists; split; [subst l4 l3 l2 l1 l0 l; resolve_map_get |]]). }
    eapply Semantics.weaken_call.
    1: { eapply HStoreZero. ecancel_assumption_impl. }
    (* Manual postcall processing (wp_postcall_auto can't match this shape) *)
    intros t'0 m'0 rets0 [Hrets0 [Htr0 Hsep0]].
    subst rets0. symmetry in Htr0. subst t'0.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    (* store iter = 0: resolve DEXPR + memory store manually *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists. split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
           WeakestPrecondition.expr_body WeakestPrecondition.get dlet.dlet].
      eexists. split; [subst l4; rewrite map.get_put_same; exact eq_refl
                       | exact eq_refl]. }
    letexists. split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
           WeakestPrecondition.expr_body WeakestPrecondition.literal dlet.dlet].
      exact eq_refl. }
    eapply store_word_of_sep.
    { pose proof Hsep0 as H'. ecancel_assumption. }
    intros m_store Hsep_store.

    (* === Phase 4: Apply Loops.while_localsmap === *)

    eapply Loops.while_localsmap
      with (v0 := 129%nat)
           (lt := Nat.lt)
           (invariant := glv_loop_inv
                    pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz
                    pk1 pk2 a_auxx a_auxy a_auxz a_cond1 a_cond2 a_iter
                    Px Py Pz Phix Phiy Phiz
                    (eval glv_scalar_words k1_words) (eval glv_scalar_words k2_words)
                    R tr).

    (* Well-foundedness *)
    { exact lt_wf. }

    (* Initial invariant (v0 = 129, iter = 0) *)
    { unfold glv_loop_inv.
      split; [reflexivity |].
      (* After store_zero: outx=Fzero, outy=Fone, outz=Fzero (identity).
         After store iter=0: iter_word = word.of_Z 0.
         k1/k2 unchanged, P/phi unchanged, aux/cond unchanged.

         Provide existential witnesses: the current values of all fields.
         Identity point: (Fzero, Fone, Fzero)
         P unchanged: (Px, Py, Pz)
         phi unchanged: (Phix, Phiy, Phiz)
         aux: initial values from P_from_bytes
         k1/k2: unchanged from input
         cond1/cond2: initial from anybytes_to_scalar
         iter_word: word.of_Z 0 (from the store we just did)

         Scalar invariants at iter=0:
         - Z.shiftr k1_init 0 = k1_init = eval k1_words  (OK)
         - Z.shiftr k2_init 0 = k2_init = eval k2_words  (OK)
         - k1_init mod 2^0 = 0, so scmul_glv 0 P = identity  (OK)
         - k2_init mod 2^0 = 0, so scmul_glv 0 phi = identity  (OK)
         - curve_add identity identity = identity  (need id properties)
         - 2^0 = 1, scmul_glv 1 P = curve_add P identity = P  (OK)

         The sep and locals follow from the current state after
         store_zero + store iter. *)
      (* Witnesses: identity output, unchanged P/phi/aux/k/cond, iter=0 *)
      exists Fzero, Fone, Fzero, Px, Py, Pz, Phix, Phiy, Phiz,
             Auxx_init, Auxy_init, Auxz_init,
             k1_words, k2_words, c1_init, c2_init, (word.of_Z 0).
      cbv [glv_iterations]. cbv beta.
      (* Scalar: Z.shiftr k 0 = k *)
      rewrite !Z.shiftr_0_r.
      (* State after 0 iterations: (O, P, Phi) *)
      change (Z.to_nat (129 - Z.of_nat 129)) with 0%nat.
      cbn [glv_state fst snd].
      subst a v.
      repeat split; try reflexivity.
      (* Sep: change Compilation2.FElem to FElem, unfold Point3 for ecancel *)
      all: try (change Compilation2.FElem with FElem in Hsep_store;
                unfold Point3; ecancel_assumption).
      (* Locals *)
      all: try (subst l4 l3 l2 l1 l0 l; resolve_map_get).
      (* iter word value *)
      all: try (change (Z.of_nat 129) with 129%Z;
                rewrite word.unsigned_of_Z; cbv; reflexivity). }

    (* Loop body + post-loop: Loops.while_localsmap generates 2 subgoals:
       1. Loop body: forall vi, invariant vi -> exists br,
            expr ... br /\
            (br <> 0 -> body; exists vi', invariant vi' /\ vi' < vi) /\
            (br = 0  -> postcondition)
       2. (already handled by well_founded + initial invariant above)

       Actually, while_localsmap generates 3 subgoals:
       a. well_founded (done above)
       b. initial invariant (done above)
       c. forall v t m l, invariant v t m l ->
            exists br, expr ... br /\
            (br <> 0 -> loop body WP) /\
            (br = 0  -> post-loop WP)

       So we have ONE subgoal here combining body and post-loop. *)
    { intros vi ti mi li Hinv.
      unfold glv_loop_inv in Hinv.
      destruct Hinv as [Htr_i Hinv_body].
      destruct Hinv_body as [Outx_i [Outy_i [Outz_i [Px_i [Py_i [Pz_i
        [Phix_i [Phiy_i [Phiz_i [Auxx_i [Auxy_i [Auxz_i
        [k1w_i [k2w_i [c1_i [c2_i [iw_i
        Hinv_conj]]]]]]]]]]]]]]]]].
      subst ti.

      (* Destruct all conjuncts from the invariant *)
      destruct Hinv_conj as
        [Hk1_i [Hk2_i [Hout_i [Hp_i [Hphi_i
        [Hsep_i
        [Hl_outx [Hl_outy [Hl_outz
        [Hl_px [Hl_py [Hl_pz
        [Hl_phix [Hl_phiy [Hl_phiz
        [Hl_pk1 [Hl_pk2
        [Hl_auxx [Hl_auxy [Hl_auxz
        [Hl_cond1 [Hl_cond2 [Hl_iter
        [Hiter_val Hv_eq]]]]]]]]]]]]]]]]]]]]]]]].

      (* Evaluate branch condition:
         expr.op bopname.ltu
           (expr.load access_size.word (expr.var "iter"))
           (expr.literal glv_iterations)
         This loads the iter counter from memory, compares with 129.
         Result is word.b2w (word.ltu iter_word (word.of_Z 129)). *)

      (* The branch value is computed from memory (load from a_iter).
         We need to provide the value and show the expression evaluates to it.
         From Hsep_i: (scalar a_iter iw_i ⋆ ...) mi
         From Hiter_val: word.unsigned iw_i = 129 - Z.of_nat vi *)

      (* Provide branch value: word encoding of (iter < 129) *)
      exists (word.b2w (word.ltu iw_i (word.of_Z 129))).
      split.
      { (* Evaluate branch expression:
           expr.op bopname.ltu (expr.load access_size.word (expr.var "iter")) (expr.literal glv_iterations)
           The load reads iw_i from scalar a_iter, then compares with 129. *)
        cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.load dlet.dlet].
        rewrite Hl_iter.
        (* Need to show: load from (scalar a_iter iw_i) yields iw_i *)
        eexists. split. { exact eq_refl. }
        eexists. split.
        { eapply load_word_of_sep. ecancel_assumption. }
        cbv [Semantics.interp_binop literal dlet.dlet word.b2w Z.b2z].
        destruct (word.ltu iw_i (word.of_Z 129)); exact eq_refl. }

      split.
      { (* TRUE branch: iter < 129, i.e. vi > 0 *)
        intro Hne.

        (* Process store: iter = iter + 1 *)
        glv_straightline.  (* cmd.seq — peel to expose store + rest *)
        (* cmd.store iter (iter+1): manual resolution for abstract locals *)
        straightline. straightline.
        exists a_iter. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.get dlet.dlet].
          eexists. split; [exact Hl_iter | exact eq_refl]. }
        (* Evaluate load(iter) + 1, then store *)
        eexists. split.
        { (* DEXPR: load(iter) + 1 *)
          eexists. split. { exact Hl_iter. }
          eexists. split. { eapply load_word_of_sep. ecancel_assumption. }
          cbv [Semantics.interp_binop].
          exact eq_refl. }
        eapply store_word_of_sep. { ecancel_assumption. }
        intros m_iter Hsep_iter.

        (* Flatten right-associated sep from store_word_of_sep.
           Build a flat sep hypothesis via ecancel from Hsep_i + the iter store. *)
        (* Hsep_iter from store_word_of_sep is right-assoc with scalar a_iter at front.
           Don't flatten — just keep it and let gcall_explicit use the slow cancel path
           for the first call, then impl1_refl for subsequent same-order calls. *)

        (* === Loop body: 10 function calls + invariant restoration === *)

        (* Memory optimization: clear all stale stackalloc/init hypotheses.
           After the while loop setup, only the loop invariant's sep (Hsep_i
           destructed into Hk1_i..Hv_eq) and the iter store (Hsep_iter → m_iter)
           matter. Everything from Phase 1-3 is dead weight. *)
        (* Aggressive cleanup: keep only what the 10 gcalls need. *)
        clear - functions HStoreZero HShiftScalar HCmovInplace
                HCurveAddInplace HCurveDouble
                pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
                a_auxx a_auxy a_auxz a_cond1 a_cond2 a_iter
                vi li
                Outx_i Outy_i Outz_i Px_i Py_i Pz_i
                Phix_i Phiy_i Phiz_i
                Auxx_i Auxy_i Auxz_i k1w_i k2w_i c1_i c2_i iw_i
                Hk1_i Hk2_i Hout_i Hp_i Hphi_i
                Hl_outx Hl_outy Hl_outz Hl_px Hl_py Hl_pz
                Hl_phix Hl_phiy Hl_phiz Hl_pk1 Hl_pk2
                Hl_auxx Hl_auxy Hl_auxz Hl_cond1 Hl_cond2 Hl_iter
                Hiter_val Hv_eq Hne
                m_iter mi Hsep_iter Hsep_i
                Px Py Pz Phix Phiy Phiz R tr
                mem_ok word_ok locals_ok env_ok ext_spec_ok.

        (* Memory optimization: clear stale sep hypotheses after each call.
           Each gcall produces a fresh sep on new memory; old seps are dead weight. *)
        Local Ltac clear_stale_seps :=
          lazymatch goal with
          | |- WeakestPrecondition.cmd _ _ _ ?mcur _ _ =>
            repeat match goal with
            | H : _ ?m |- _ =>
              lazymatch type of H with
              | context[Separation.sep] =>
                lazymatch m with mcur => fail | _ => clear H end
              | context[FElem] =>
                lazymatch m with mcur => fail | _ => clear H end
              end
            end
          | _ => idtac
          end.

        (* Flatten right-associated sep hypotheses to left-associated *)
        Local Ltac flatten_seps :=
          repeat match goal with
          | H : (_ ⋆ _) ?m |- _ =>
            lazymatch type of H with
            | Separation.sep _ (Separation.sep _ _) _ =>
              apply sep_assoc in H
            end
          end.

        Local Ltac gcall_clean spec :=
          gcall spec;
          try lazymatch goal with
          | |- WeakestPrecondition.cmd _ _ _ _ _ _ => idtac
          end.

        (* Tactic for calls with explicit spec args *)
        Local Ltac gcall_explicit spec pc px c x :=
          try glv_straightline;
          unfold1_cmd_goal; cbv beta match delta [cmd_body];
          letexists; split; [solve [eval_dexprs_abstract] |];
          eapply Semantics.weaken_call;
          [ pose proof (spec pc px c x) as HS; eapply HS;
            ecancel_assumption_fast
          | glv_postcall ];
          repeat match goal with
          | H : exists _, _ |- _ => destruct H
          end;
          repeat match goal with
          | H : _ /\ _ |- _ =>
              lazymatch type of H with
              | _ = _ /\ _ => destruct H
              | _ /\ _ => destruct H
              end
          end;
          try match goal with
          | H : ?tr = ?t |- _ => first [ subst t | subst tr | idtac ]
          end;
          idtac.

        (* Name the results of add / dbl / cmov in the call postconditions:
           [Hop : (x, y, z) = op ...], the sep hypothesis then mentions x y z. *)
        Local Ltac destr_ops :=
          repeat match goal with
          | H : context[add (?a, ?b, ?c) (?d, ?e, ?ff)] |- _ =>
            lazymatch type of H with @eq _ _ _ => fail | _ => idtac end;
            let r := fresh "ca" in let Heq := fresh "Hop" in
            remember (add (a, b, c) (d, e, ff)) as r eqn:Heq in H;
            destruct r as [[? ?] ?]
          | H : context[dbl (?a, ?b, ?c)] |- _ =>
            lazymatch type of H with @eq _ _ _ => fail | _ => idtac end;
            let r := fresh "cd" in let Heq := fresh "Hop" in
            remember (dbl (a, b, c)) as r eqn:Heq in H;
            destruct r as [[? ?] ?]
          | H : context[if word.eqb ?c ?z then ?A else ?B] |- _ =>
            lazymatch type of H with @eq _ _ _ => fail | _ => idtac end;
            let r := fresh "cm" in let Heq := fresh "Hop" in
            remember (if word.eqb c z then A else B) as r eqn:Heq in H;
            destruct r as [[? ?] ?]
          end.

        (* === Process all 10 loop body calls === *)

        (* Flatten the right-associated sep from store_word_of_sep and
           unfold Point3 so that ecancel can match individual FElems.
           This is critical for resolving frame evars during gcall. *)
        unfold Point3 in Hsep_iter.
        flatten_seps.

        (* Call 1: shift_scalar(cond1, pk1) *)
        gcall_explicit HShiftScalar a_cond1 pk1 c1_i k1w_i.
        (* Call 2: shift_scalar(cond2, pk2) *)
        gcall_explicit HShiftScalar a_cond2 pk2 c2_i k2w_i.
        (* Call 3: store_zero(aux) *)
        gcall_clean HStoreZero.
        (* Call 4: cmov_alt(aux, aux, P, cond1) *)
        gcall HCmovInplace.
        destr_ops.
        (* Call 5: curve_add(out, aux, out) *)
        gcall_clean HCurveAddInplace.
        (* Destruct curve_add let-bindings BEFORE call 6:
           1) puts result variables in scope for evar resolution
           2) preserves equations for algebraic goals *)
        destr_ops.
        (* Call 6: store_zero(aux) *)
        gcall_clean HStoreZero.
        (* Call 7: cmov_alt(aux, aux, phi, cond2) *)
        gcall HCmovInplace.
        destr_ops.
        (* Call 8: curve_add(out, aux, out) *)
        gcall_clean HCurveAddInplace.
        (* Destruct curve_add let-bindings before calls 9-10 *)
        destr_ops.
        (* Call 9: curve_add(P, P, P) — P = 2P *)
        gcall_clean HCurveDouble.
        (* Destruct curve_add let-binding before call 10 *)
        destr_ops.
        (* Call 10: curve_add(phi, phi, phi) — phi = 2*phi *)
        gcall_clean HCurveDouble.

        (* === Loop invariant restoration === *)
        destr_ops.
        exists (vi - 1)%nat. unfold Markers.split.
        assert (Hvi_gt0 : (vi > 0)%nat).
        { rewrite (@word.unsigned_b2w _ _ word_ok) in Hne.
          pose proof (@word.unsigned_ltu _ _ word_ok iw_i (word.of_Z 129)) as Hltu.
          destruct (word.ltu iw_i (word.of_Z 129)) eqn:Eb;
            [| exfalso; apply Hne; cbn; reflexivity].
          symmetry in Hltu; apply Z.ltb_lt in Hltu.
          rewrite Hiter_val, word.unsigned_of_Z in Hltu.
          unfold word.wrap in Hltu.
          destruct (width_cases) as [Hw|Hw]; rewrite Hw in Hltu;
            (change (129 mod 2 ^ 32) with 129 in Hltu
             || change (129 mod 2 ^ 64) with 129 in Hltu); lia. }
        split.
        2: { lia. }
        unfold glv_loop_inv. subst. split. { reflexivity. }
        exists f8, f9, f10, f11, f12, f13, f14, f15, f16, f5, f6, f7.
        exists x0, x2, x, x1, (word.add iw_i (word.of_Z 1)).
        (* the state after one more iteration *)
        pose proof (word.unsigned_range iw_i) as Hiw_range.
        assert (Hn : Z.to_nat (129 - Z.of_nat (vi - 1))
                     = S (Z.to_nat (129 - Z.of_nat vi))) by lia.
        rewrite Hn. cbn [glv_state].
        assert (Hb1 : word.eqb x (word.of_Z 0)
                      = negb (Z.testbit (eval glv_scalar_words k1_words)
                                (Z.of_nat (Z.to_nat (129 - Z.of_nat vi))))).
        { apply word_eqb0_b2z. rewrite <- H1, Hk1_i, Z2Nat.id by lia.
          apply Z_shiftr_mod2_b2z; [exact (eval_nonneg_2 _) | lia]. }
        assert (Hb2 : word.eqb x1 (word.of_Z 0)
                      = negb (Z.testbit (eval glv_scalar_words k2_words)
                                (Z.of_nat (Z.to_nat (129 - Z.of_nat vi))))).
        { apply word_eqb0_b2z. rewrite <- H5, Hk2_i, Z2Nat.id by lia.
          apply Z_shiftr_mod2_b2z; [exact (eval_nonneg_2 _) | lia]. }
        rewrite Hb1 in Hop. rewrite Hb2 in Hop1.
        destruct (glv_state idp add dbl (eval glv_scalar_words k1_words)
                    (eval glv_scalar_words k2_words) (Px, Py, Pz) (Phix, Phiy, Phiz)
                    (Z.to_nat (129 - Z.of_nat vi))) as [[o pp] qq].
        cbn [fst snd] in Hout_i, Hp_i, Hphi_i. subst o pp qq.
        cbv [glv_step]. cbn [fst snd].
        rewrite Hop2, Hop0, Hop1, Hop, Hop3, Hop4.
        assert (Hif : forall (b : bool) (A B : F * F * F),
                   (if negb b then A else B) = (if b then B else A))
          by (intros [|] ? ?; reflexivity).
        rewrite !Hif.
        repeat split.
        (* Sep *)
        all: try match goal with |- (_ ⋆ _) ?m =>
          unfold Point3;
          ecancel_assumption_fast
        end.
        (* Locals *)
        all: try resolve_map_get.
        all: try (rewrite (Nat2Z.inj_sub vi 1) by lia;
                  change (Z.of_nat 1) with 1%Z).
        (* Scalar shifts *)
        all: try (
          transitivity (Z.shiftr (eval glv_scalar_words k1_words) ((129 - Z.of_nat vi) + 1));
          [rewrite <- H0, Hk1_i;
           apply (shiftr_from_div2 _ _ (129 - Z.of_nat vi));
           [pose proof (word.unsigned_range iw_i); lia | reflexivity]
          | replace ((129 - Z.of_nat vi) + 1) with (129 - (Z.of_nat vi - 1)) by lia;
            reflexivity]).
        all: try (
          transitivity (Z.shiftr (eval glv_scalar_words k2_words) ((129 - Z.of_nat vi) + 1));
          [rewrite <- H4, Hk2_i;
           apply (shiftr_from_div2 _ _ (129 - Z.of_nat vi));
           [pose proof (word.unsigned_range iw_i); lia | reflexivity]
          | replace ((129 - Z.of_nat vi) + 1) with (129 - (Z.of_nat vi - 1)) by lia;
            reflexivity]).
        (* Word arithmetic *)
        all: try (rewrite word.unsigned_add; rewrite Hiter_val;
                  rewrite word.unsigned_of_Z_1; unfold word.wrap;
                  destruct (width_cases) as [Hw|Hw]; rewrite Hw;
                  change (1 mod 2 ^ 32) with 1; change (1 mod 2 ^ 64) with 1;
                  rewrite Z.mod_small by
                    (pose proof (word.unsigned_range iw_i); lia);
                  pose proof (word.unsigned_range iw_i); lia).
        (* Nat arithmetic *)
        all: try (
          cbv [glv_iterations];
          replace (Z.of_nat vi - 1) with (Z.of_nat (vi - 1)) by
            (rewrite Nat2Z.inj_sub by lia; change (Z.of_nat 1) with 1%Z; ring);
          replace (129 - (129 - Z.of_nat (vi - 1))) with (Z.of_nat (vi - 1)) by
            (pose proof (word.unsigned_range iw_i); lia);
          rewrite Nat2Z.id; reflexivity). }

      { (* FALSE branch: iter >= 129, i.e. vi = 0 *)
        intro Hcond.
        (* The while condition is false: NOT (iter < 129), so iter >= 129.
           From Hiter_val: word.unsigned iw_i = 129 - Z.of_nat vi.
           From Hcond: word.unsigned (word.b2w (word.ltu ...)) = 0.
           This means NOT (iw_i < 129), so iw_i >= 129.
           Combined with iter = 129 - Z.of_nat vi, we get vi = 0.

           Post-loop goal: WP for 6 stack deallocations, then postcondition.
           After the while loop, there's no more code in the function body
           (the while is the last statement before the stack deallocs).

           The stack deallocs are automatic from the stackalloc construct:
           they require providing anybytes for each stack buffer.

           We need to convert:
           - FElem None a_auxx/y/z → anybytes (via FElem_to_bytes)
           - scalar a_cond1/2 → anybytes (via scalar_to_anybytes)
           - scalar a_iter → anybytes (via scalar_to_anybytes)

           Then provide the final postcondition existentials. *)

        (* vi = 0 means iter = 129, all bits processed *)

        (* --- Dealloc level 1: iter (word-sized scalar → anybytes) --- *)
        eassert (Hiter_sep : (_ ⋆ scalar a_iter _) mi).
        { pose proof Hsep_i as H'. ecancel_assumption. }
        destruct Hiter_sep as [m_rest_iter [m_stk_iter [[Heq_iter' Hd_iter'] [Hrest_iter Hstk_iter]]]].
        eapply scalar_to_anybytes in Hstk_iter.
        exists m_rest_iter, m_stk_iter.
        split. { exact Hstk_iter. }
        split. { split; [exact Heq_iter' | exact Hd_iter']. }

        (* --- Dealloc level 2: cond2 (word-sized scalar → anybytes) --- *)
        eassert (Hcond2_sep : (_ ⋆ scalar a_cond2 _) m_rest_iter).
        { pose proof Hrest_iter as H'. ecancel_assumption. }
        destruct Hcond2_sep as [m_rest_cond2 [m_stk_cond2 [[Heq_cond2' Hd_cond2'] [Hrest_cond2 Hstk_cond2]]]].
        eapply scalar_to_anybytes in Hstk_cond2.
        exists m_rest_cond2, m_stk_cond2.
        split. { exact Hstk_cond2. }
        split. { split; [exact Heq_cond2' | exact Hd_cond2']. }

        (* --- Dealloc level 3: cond1 (word-sized scalar → anybytes) --- *)
        eassert (Hcond1_sep : (_ ⋆ scalar a_cond1 _) m_rest_cond2).
        { pose proof Hrest_cond2 as H'. ecancel_assumption. }
        destruct Hcond1_sep as [m_rest_cond1 [m_stk_cond1 [[Heq_cond1' Hd_cond1'] [Hrest_cond1 Hstk_cond1]]]].
        eapply scalar_to_anybytes in Hstk_cond1.
        exists m_rest_cond1, m_stk_cond1.
        split. { exact Hstk_cond1. }
        split. { split; [exact Heq_cond1' | exact Hd_cond1']. }

        (* --- Dealloc level 4: auxz (felem-sized FElem None → anybytes) --- *)
        eassert (Hauxz_sep : (_ ⋆ FElem None a_auxz _) m_rest_cond1).
        { change Compilation2.FElem with FElem in Hrest_cond1.
          unfold Point3 in Hrest_cond1.
          pose proof Hrest_cond1 as H'. ecancel_assumption. }
        destruct Hauxz_sep as [m_rest_auxz [m_stk_auxz [[Heq_auxz' Hd_auxz'] [Hrest_auxz Hstk_auxz]]]].
        exists m_rest_auxz, m_stk_auxz.
        split. { exact (P_to_bytes a_auxz _ m_stk_auxz Hstk_auxz). }
        split. { split; [exact Heq_auxz' | exact Hd_auxz']. }

        (* --- Dealloc level 5: auxy (felem-sized FElem None → anybytes) --- *)
        eassert (Hauxy_sep : (_ ⋆ FElem None a_auxy _) m_rest_auxz).
        { change Compilation2.FElem with FElem in Hrest_auxz.
          unfold Point3 in Hrest_auxz.
          pose proof Hrest_auxz as H'. ecancel_assumption. }
        destruct Hauxy_sep as [m_rest_auxy [m_stk_auxy [[Heq_auxy' Hd_auxy'] [Hrest_auxy Hstk_auxy]]]].
        exists m_rest_auxy, m_stk_auxy.
        split. { exact (P_to_bytes a_auxy _ m_stk_auxy Hstk_auxy). }
        split. { split; [exact Heq_auxy' | exact Hd_auxy']. }

        (* --- Dealloc level 6: auxx (felem-sized FElem None → anybytes) --- *)
        eassert (Hauxx_sep : (_ ⋆ FElem None a_auxx _) m_rest_auxy).
        { change Compilation2.FElem with FElem in Hrest_auxy.
          unfold Point3 in Hrest_auxy.
          pose proof Hrest_auxy as H'. ecancel_assumption. }
        destruct Hauxx_sep as [m_rest_auxx [m_stk_auxx' [[Heq_auxx' Hd_auxx'] [Hrest_auxx Hstk_auxx]]]].
        exists m_rest_auxx, m_stk_auxx'.
        split. { exact (P_to_bytes a_auxx _ m_stk_auxx' Hstk_auxx). }
        split. { split; [exact Heq_auxx' | exact Hd_auxx']. }

        (* --- Final postcondition --- *)
        cbv [list_map list_map_body].
        split. { exact eq_refl. }
        split. { exact eq_refl. }
        (* Provide existential witnesses for output values *)
        exists Outx_i, Outy_i, Outz_i,
               Px_i, Py_i, Pz_i,
               Phix_i, Phiy_i, Phiz_i.
        exists k1w_i, k2w_i.
        split.
        { (* Accumulator equation: out = [k1]P + [k2]phi(P) *)
          (* Step 1: derive vi = 0 from the false branch condition *)
          rewrite (@word.unsigned_b2w _ _ word_ok) in Hcond.
          assert (Hltu_false : word.ltu iw_i (word.of_Z 129) = false).
          { destruct (word.ltu iw_i (word.of_Z 129));
            [cbn in Hcond; lia | reflexivity]. }
          pose proof (@word.unsigned_ltu _ _ word_ok iw_i (word.of_Z 129)) as Hltu_eq.
          rewrite Hltu_false in Hltu_eq. symmetry in Hltu_eq.
          apply Z.ltb_ge in Hltu_eq.
          rewrite Hiter_val, word.unsigned_of_Z in Hltu_eq.
          cbv [glv_iterations] in Hltu_eq.
          unfold word.wrap in Hltu_eq.
          destruct (width_cases) as [Hw|Hw]; rewrite Hw in Hltu_eq;
            (change (129 mod 2 ^ 32) with 129 in Hltu_eq
             || change (129 mod 2 ^ 64) with 129 in Hltu_eq);
            assert (Hvi0 : vi = 0%nat) by (pose proof Znat.Nat2Z.is_nonneg vi; lia);
            subst vi;
            change (Z.to_nat (129 - Z.of_nat 0)) with 129%nat in Hout_i;
            exact Hout_i. }
        (* Sep: the remaining memory satisfies the postcondition *)
        change Compilation2.FElem with FElem in Hrest_auxx.
        unfold Point3 in Hrest_auxx.
        ecancel_assumption. } }
  Qed.


End GLV_Prog_Generic.
