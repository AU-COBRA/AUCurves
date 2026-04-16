Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.LoopBody.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
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

(* MaxBounds lemmas — pure math, no field deps *)
Lemma max_bounds_map_max_range w n : @MaxBounds.max_bounds w n = List.map Some (List.repeat (@MaxBounds.max_range w) n).
Proof. rewrite ListUtil.map_repeat. reflexivity. Qed.

Lemma eval_max_range_lower w n :
  (0 <= w) ->
  Positional.eval (uweight w) n (List.map ZRange.lower (List.repeat (@MaxBounds.max_range w) n)) = 0.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite Positional.eval_cons.
    rewrite uweight_eval_shift.
    3, 4: now rewrite map_length, repeat_length.
    2: assumption.
    rewrite uweight_0, IHn.
    lia.
Qed.

Lemma eval_max_range_upper w n :
  0 <= w ->
   Positional.eval (uweight w) n (List.map ZRange.upper (List.repeat (@MaxBounds.max_range w) n)) = 2 ^ (w * Z.of_nat n) - 1.
Proof.
  induction n; intros.
  - simpl.
    rewrite Z.mul_0_r.
    rewrite Positional.eval_nil.
    reflexivity.
  -
    rewrite Nat2Z.inj_succ.
    remember (Z.of_nat n). simpl.
    rewrite Positional.eval_cons.
    rewrite uweight_eval_shift.
    3, 4: now rewrite map_length, repeat_length.
    2: auto.
    rewrite uweight_1, uweight_0, IHn; auto.
    rewrite Z.mul_succ_r.
    rewrite Z.pow_add_r.
    nia.
    nia.
    nia.
Qed.

Section __.
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
          {group_cmov : string}
          {store_zero : string}.

  Local Notation F := (F M_pos).
  Local Notation Fzero := (F.of_Z M_pos 0).
  Local Notation Fone := (F.of_Z M_pos 1).

  Context {curve_add : (F * F * F) -> (F * F * F) -> (F * F * F)}.
  Context {group_prop1 : forall x y z, curve_add (x, y, z) (Fzero, Fone, Fzero) = (x, y, z)}.

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context {scalar_words : nat}.

  Definition scalar_bits := (width * Z.of_nat scalar_words).

  Context {scalar_words_ok1 : scalar_bits < 2 ^ width}.

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  Instance spec_of_scalar_mult : spec_of "scalar_mult" :=
    fnspec! "scalar_mult"
      (pPx pPy pPz pOutx pOuty pOutz pn : word)
      / (Px Py Pz Outx Outy Outz : F) (n : list word) R,
      { requires tr mem :=
          (FElem (Some tight_bounds) pPx Px
           * FElem (Some tight_bounds) pPy Py
           * FElem (Some tight_bounds) pPz Pz
           * FElem (Some tight_bounds) pOutx Outx
           * FElem (Some tight_bounds) pOuty Outy
           * FElem (Some tight_bounds) pOutz Outz
           * Bignum.Bignum scalar_words pn n
           * R)%sep mem
      ;
        ensures tr' mem' :=
          tr = tr'
          /\ exists Pxnew Pynew Pznew Outxnew Outynew Outznew
            : F,
          exists nnew : list word,
            (Outxnew, Outynew, Outznew) = (@LoopBody.scmul _ curve_add) (Z.to_nat (Positional.eval (uweight width) scalar_words (List.map word.unsigned n))) (Px, Py, Pz)
            /\ (FElem (Some tight_bounds) pPx Pxnew
               * FElem (Some tight_bounds) pPy Pynew
               * FElem (Some tight_bounds) pPz Pznew
               * FElem (Some tight_bounds) pOutx Outxnew
               * FElem (Some tight_bounds) pOuty Outynew
               * FElem (Some tight_bounds) pOutz Outznew
               * Bignum.Bignum scalar_words pn nnew
               * R)%sep mem'}.

  Require Import Crypto.COperationSpecifications.

  Lemma max_bounds_words : forall (x : list word) n, length x = n -> list_Z_bounded_by (@MaxBounds.max_bounds width n) (List.map word.unsigned x).
  Proof.
      intros. generalize dependent x.
      induction n; intros.
          - destruct x; try discriminate. simpl. cbv. auto.
          - destruct x; try discriminate. simpl.
            eapply Util.list_Z_bounded_by_cons. split.
            2: {
                simpl in IHn. eapply IHn. auto.
            }
            apply Expr.is_bounded_by_bool_width_range.
            eauto.
            pose proof Properties.word.unsigned_range. auto.
  Qed.

  Definition scalar_mult_func : function_t :=
      ("scalar_mult", (["px"; "py"; "pz"; "outx"; "outy"; "outz"; "pn"], []:list String.string, bedrock_func_body:(
      stackalloc felem_size_in_bytes as pauxx;
      stackalloc felem_size_in_bytes as pauxy;
      stackalloc felem_size_in_bytes as pauxz;
      stackalloc (Memory.bytes_per_word width) as cond;
      stackalloc (Memory.bytes_per_word width) as iter;
      coq:(cmd.call [] "store_zero" [expr.var "outx"; expr.var "outy"; expr.var "outz"]);
      coq:(cmd.store access_size.word (expr.var "iter") (expr.literal 0));
      while (coq:( expr.op bopname.ltu (expr.load access_size.word (expr.var "iter")) scalar_bits )){
          coq:(cmd.store access_size.word (expr.var "iter") (expr.op bopname.add (expr.load access_size.word "iter") (expr.literal 1)));
          coq:(cmd.call [] "loop_body"
                 [expr.var "px"; expr.var "py"; expr.var "pz"; expr.var "outx"; expr.var "outy"; expr.var "outz"; expr.var "pauxx"; expr.var "pauxy"; expr.var "pauxz"; expr.var "pn"; expr.var "cond" ])
      }
      ))).

  Opaque felem_size_in_bytes.
  Opaque scalar_words.
  Opaque scalar_bits.
  Opaque Memory.bytes_per_word.
  Opaque Z.of_nat.

  Lemma scalar_mult_ok : program_logic_goal_for_function! scalar_mult_func.
  Proof. exact I. Qed.

End __.
