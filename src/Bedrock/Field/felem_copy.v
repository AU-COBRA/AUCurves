Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.NotationsCustomEntry.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import bedrock2.Syntax.
Require Import Coq.micromega.Lia.
Require Import Bedrock.Util.Bignum.
Require Import Bedrock.Util.Word.
Require Import Bedrock.Util.Tactics.
Require Import Bedrock.Util.SeparationLogic.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import coqutil.Word.Interface.
Require Import Bedrock.Util.Word.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.

Local Open Scope string_scope.
Import Syntax.Coercions.
Import ListNotations.
Local Open Scope Z_scope.

Section felemcopy.
    Context (m : Z)
            (affix : string)
            (m_big : 0 < m)
            (num_limbs : nat)
            {p : Types.parameters}
            (bw_big : 0 < word_size_in_bytes).

    Notation num_bytes := word_size_in_bytes.
    
    Definition bw : Z := num_bytes * 8.
    Import access_size.
    Import bopname.

    Local Definition store_this (pout : Syntax.expr) pin n0 : cmd :=
    cmd.store access_size.word (expr.op add pout (expr.literal (n0 * num_bytes))) (expr.load access_size.word (expr.op add pin (expr.literal (n0 * num_bytes)))).

    Local Coercion Z.of_nat : nat >-> Z.

    Fixpoint copy_words (n nz : nat) pout pin : cmd :=
        match n with
        | O => cmd.skip
        | S (n0) => (cmd.seq (store_this pout pin nz) (copy_words n0 (S(nz)) pout pin) )
        end.

    Definition felem_copy : Syntax.func :=
    let out := "out" in
    let elem := "elem" in
    (append "felem_copy" affix, ([out; elem], [], (copy_words num_limbs O out elem))).

    Local Open Scope string_scope.
    Local Infix "*" := sep : sep_scope.
    Delimit Scope sep_scope with sep.
    Local Notation function_t := ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
    Local Notation functions_t := (list function_t).
End felemcopy.

Ltac normalize_words := repeat (try rewrite word_add_0; try rewrite (next_word')).
Ltac normalize_words_in H := repeat (rewrite next_word' in H; try rewrite word_add_0 in H).

Ltac subst_this_a := lazymatch goal with
| |- exists v : _ , _ /\ store access_size.word _ ?thisa _ _ => subst thisa
| _ => fail
end.

Ltac copy_word H1 H2 := eexists; split;
[ repeat straightline; try (eexists; split; [
    lazymatch goal with
    | [ |- Memory.load access_size.word _ (word.add _ ?v) = _] => subst v; normalize_words; repeat straightline
    end
    | eauto]) |];
    lazymatch goal with
    | [ |- WeakestPrecondition.store access_size.word _ ?a _ _] =>
    eapply store_word_of_sep_2;
    [ try subst a; normalize_words; clear H1; ecancel_assumption
    | try subst a; normalize_words; clear H2; ecancel_assumption| ]
    | _ => fail
    end; clear H1 H2;  do 6 straightline; try (straightline; subst_this_a); repeat straightline.