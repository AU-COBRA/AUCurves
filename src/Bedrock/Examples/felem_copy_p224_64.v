Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Bedrock.Field.felem_copy.
Require Import Coq.Lists.List.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.SeparationLogic.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import coqutil.Word.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Bedrock.Util.Tactics.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Bedrock.Util.Bignum.
(* Require Import bedrock2.NotationsCustomEntry. *)

Local Open Scope string_scope.
Import Syntax.Coercions.
Import ListNotations.

(*Parameters to be changed: we require an instance of parameters and parameters_ok, as well as a a string to be appended to function name.
    lastly, the parameter num_limbs specify the number of words in a Bignum representation of the fiel elements to be copied.*)
Existing Instances Defaults64.default_parameters Defaults64.default_parameters_ok.
Definition aff := "_p224_64".
Definition num_limbs := 4%nat.


(*Rest of file should not be changed.*)
Definition felem_copy_m : Syntax.func := (felem_copy aff num_limbs).

Instance spec_of_felem_copy_m: spec_of felem_copy_m :=
fun functions : list (string * (list string * list string * Syntax.cmd)) =>
    forall (welem : list Interface.word.rep)
    (pout pelem: Interface.word.rep)
    (wold_out: list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (R Relem P : Interface.map.rep -> Prop),
    ( (fun m => (Bignum num_limbs pelem welem * Relem)%sep m /\ P m) * (Bignum num_limbs pout wold_out) * R)%sep m0 ->
    WeakestPrecondition.call functions (append "felem_copy" aff) t m0
    ([pout; pelem])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    ((P * (Bignum num_limbs pout welem) * R)%sep m')).

Notation N aw := (word.add (word.of_Z word_size_in_bytes) aw).

Theorem felem_copy_m_ok : program_logic_goal_for_function! felem_copy_m.
Proof.
    repeat straightline.

    (*Packing all assumption into single separation hypothesis for copying bytes.*)
    remember (Bignum num_limbs pelem welem) as Q.
    remember (Bignum num_limbs pout wold_out * R)%sep as newR.
    eassert (H0 : ( _ * newR)%sep _) by (subst newR; ecancel_assumption); clear H.
    apply sep_and_l_fwd in H0. destruct H0 as [H H0]. subst newR.

    assert (Ha : a = pout) by (subst a; normalize_words; auto).
    eassert (nval : num_limbs = _) by (cbv [num_limbs]; auto with zarith).

    (*Rephrasing Bignun to Scalar for copying bytes*)
    Bignum_to_Scalars num_limbs wold_out nval.
    eassert ((Bignum num_limbs pout _ * (P * R)%sep)%sep m0) by (apply sep_comm; clear H H1 H2; ecancel_assumption).
    apply Bignum_manyScalars_R in H3; sepsimpl_hyps; clear H3;
    rewrite nval in H4; repeat rewrite many_Scalars_next in H4; rewrite many_Scalars_nil in H4.

    clear H1 H H0. subst Q.
    Bignum_to_Scalars num_limbs welem nval. clear H H2.
    subst a.

    rename H0 into H;
    rename H4 into H0.
    repeat copy_word H H0.

    (* copy_word H H0. *)
    repeat split; auto.

    lazymatch goal with 
    | |- (_ * (Bignum _ _ ?list) * _)%sep _ => remember list as l end.

    (*Postcondition*)
    unfold Bignum.
    eassert ( (P * (emp (Datatypes.length l = num_limbs) * _))%sep m) by (subst l; sepsimpl; auto; ecancel_assumption).
    subst l; unfold Array.array; normalize_words; normalize_words_in H0; clear H H0; normalize_words_in H1; ecancel_assumption.
Qed.

(*Output to terminal:*)

(* Require Import bedrock2.ToCString bedrock2.Bytedump.
Definition felem_copy_func := c_module (felem_copy_m :: nil).
Eval compute in felem_copy_func. *)