Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.CurveAddAlt.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.BignumShift.
Require Import Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

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
          {field_representation_ok : FieldRepresentation_ok}
          {group_cmov : string}
          {store_zero : string}.
  Context {scalar_words : nat}.

  Local Notation F := (F M_pos).
  Local Notation Fzero := (F.of_Z M_pos 0).
  Local Notation Fone := (F.of_Z M_pos 1).

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (curve_add_name : string).

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  (* this should all be generalized: F * F * F should be a generic group etc. *)
  Context
    {n_init : Z}
      {Px_init Py_init Pz_init : F}
      {curve_add : (F * F * F) -> (F * F * F) -> (F * F * F)}
      {curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R}
      {curve_add_zero_l : forall P, curve_add (Fzero, Fone, Fzero) P = P}
      {curve_add_zero_r : forall P, curve_add P (Fzero, Fone, Fzero) = P}.

  Fixpoint scmul (n : nat)  : F * F * F -> F * F * F :=
    fun (P : F * F * F) =>
      let X := (fst (fst P) ) in
      let Y := (snd (fst P)) in
      let Z := (snd P) in
      match n with
      | O => (Fzero, Fone, Fzero)
      | S m => curve_add (X, Y, Z) (scmul m (X, Y, Z))
      end.

  Lemma scmul_add n m : forall x y z,
      scmul (n + m) (x, y, z) = curve_add (scmul n (x, y, z)) (scmul m (x, y, z)).
  Proof.
    intros.
    induction n.
    - simpl. rewrite curve_add_zero_l. reflexivity.
    - simpl. rewrite IHn. rewrite curve_add_assoc. reflexivity.
  Qed.

  Context
    {curve_add_spec : forall x y z a b c n m k,
        @CurveAdd.ladderstep_gallina _ three_b_val x a y b z c = \<n, m, k\> ->
        (n, m, k) = curve_add (x, y, z) (a, b, c)}.

  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

  Instance spec_of_loop_body : spec_of "loop_body" :=
    fnspec! "loop_body"
          (pPx pPy pPz pOutx pOuty pOutz pPauxx pPauxy pPauxz pn pc : word)
          / (Px Py Pz Outx Outy Outz Pauxx Pauxy Pauxz Px_init Py_init Pz_init : F) (iter : nat) (n_init : Z) (n : list word) (c : word) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pPx Px
         * FElem (Some tight_bounds) pPy Py
         * FElem (Some tight_bounds) pPz Pz
         * FElem (Some tight_bounds) pOutx Outx
         * FElem (Some tight_bounds) pOuty Outy
         * FElem (Some tight_bounds) pOutz Outz
         * FElem None pPauxx Pauxx
         * FElem None pPauxy Pauxy
         * FElem None pPauxz Pauxz
         * Bignum.Bignum scalar_words pn n
         * scalar pc c
         * R)%sep mem
         /\ (Positional.eval (uweight width) scalar_words (List.map word.unsigned n)) = Z.shiftr n_init (Z.of_nat iter)
         /\ (Outx, Outy, Outz) = scmul (Z.to_nat (n_init mod (2 ^ (Z.of_nat iter))))%Z (Px_init, Py_init, Pz_init)
         /\ (Px, Py, Pz) = scmul  (2 ^ iter) (Px_init, Py_init, Pz_init)
         ;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Pxnew Pynew Pznew Outxnew Outynew Outznew Pauxxnew Pauxynew Pauxznew
                  : F,
           exists nnew : list word,
           exists cnew : word,
            (Positional.eval (uweight width) scalar_words (List.map word.unsigned nnew)) = Z.shiftr n_init (Z.of_nat (iter + 1))
            /\ (Outxnew, Outynew, Outznew) = scmul  (Z.to_nat (n_init mod (2 ^ (Z.of_nat (iter + 1)))))%Z (Px_init, Py_init, Pz_init)
            /\ (Pxnew, Pynew, Pznew) = scmul  (2 ^ (iter + 1)) (Px_init, Py_init, Pz_init)
          /\ (FElem (Some tight_bounds) pPx Pxnew
                * FElem (Some tight_bounds) pPy Pynew
                * FElem (Some tight_bounds) pPz Pznew
                * FElem (Some tight_bounds) pOutx Outxnew
                * FElem (Some tight_bounds) pOuty Outynew
                * FElem (Some tight_bounds) pOutz Outznew
                * FElem (Some tight_bounds) pPauxx Pauxxnew
                * FElem (Some tight_bounds) pPauxy Pauxynew
                * FElem (Some tight_bounds) pPauxz Pauxznew
                * Bignum.Bignum scalar_words pn nnew
                * scalar pc cnew
                * R)%sep mem'}.

  Definition loop_body_func : function_t :=
    ("loop_body", (["px"; "py"; "pz"; "outx"; "outy"; "outz"; "pauxx"; "pauxy"; "pauxz"; "pn"; "pc"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] ("store_zero") [expr.var ("pauxx"); expr.var ("pauxy"); expr.var ("pauxz")]);
      coq:(cmd.call [] ("shift_scalar") [expr.var ("pc"); expr.var ("pn")]);
      coq:(cmd.call [] ("group_cmov_alt") [expr.var ("pauxx"); expr.var ("pauxy"); expr.var ("pauxz"); expr.var ("pauxx"); expr.var ("pauxy"); expr.var ("pauxz"); expr.var ("px"); expr.var ("py"); expr.var ("pz"); expr.var("pc")]);
      coq:(cmd.call [] (curve_add_name)
             [expr.var ("outx");
              expr.var ("pauxx");
              expr.var ("outy");
              expr.var ("pauxy");
              expr.var ("outz");
              expr.var ("pauxz");
              expr.var ("outx");
              expr.var ("outy");
              expr.var ("outz")]);
      coq:(cmd.call [] (curve_add_name)
             [expr.var ("px");
              expr.var ("px");
              expr.var ("py");
              expr.var ("py");
              expr.var ("pz");
              expr.var ("pz");
              expr.var ("px");
              expr.var ("py");
              expr.var ("pz")])
    ))).

  Lemma loop_body_ok : program_logic_goal_for_function! loop_body_func.
  Proof. exact I. Qed.

End __.
