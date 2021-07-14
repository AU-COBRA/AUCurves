Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Memory.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Bedrock.Util.Util.
Require Import Bedrock.Util.Bignum.
Require Import coqutil.Word.Interface.
Require Import bedrock2.ProgramLogic.

Notation msplit := Interface.map.split.

Ltac cleanup_hyp H m :=
repeat apply (sep_assoc_proj1 m) in H; apply (sep_assoc_proj2 m) in H; rewrite <- Bignum_eq in H.

Ltac get_list_from_length l :=
(repeat (destruct l; [discriminate| ])); destruct l; [| discriminate].

(*get rid of nval argument*)
Ltac Bignum_to_Scalars n l nval := let Hsep := (fresh "Hsep") in
  eassert (Hsep : (Bignum n _ l * _)%sep _) by ecancel_assumption;
  apply Bignum_manyScalars_R in Hsep; sepsimpl_hyps; get_list_from_length l;
  lazymatch goal with
  | [H : (many_Scalars n _ _ * _)%sep _ |- _] => 
    rewrite nval in H; repeat rewrite many_Scalars_next in H;
    rewrite many_Scalars_nil in H; try rewrite <- nval in H
  | _ => fail
  end.

  (*Stackallocation leaves a number of hypothesis in the context, each pertaining to some fragment of the memory.
    these tactics collects these hyptohesis into a single one*)
  Ltac defrag_in_context' n Hold := lazymatch goal with
    | [
      |- exists _ _,
        (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
          let Ha := (fresh "Ha") in
          let m := fresh "m" in
          let Htemp := fresh "Htemp" in
          let Htemp' := fresh "Htemp'" in
          let mStack := fresh "mStack" in
          eassert (Ha : ((Bignum n addr _) * _)%sep mem) by ecancel_assumption; clear Hold;
          destruct Ha as [mStack [m [ Htemp [Htemp' ]]]];
          exists m; exists mStack; split; [ eapply (Bignum_anybytes n); [cbv; auto|]; eassumption; cbv; reflexivity | split; [apply Properties.map.split_comm; auto| clear Htemp Htemp']]
          end.
              
Ltac defrag_in_context n :=
  match goal with 
    | [ H : _ ?mem |- exists _ _, _ /\ msplit ?mem _ _ /\ _ ] => defrag_in_context' n H
  end.