(** * BLS12-381: the base-field functions called by the tower that the extraction does not list.

    - [bls12_opp]: fiat-crypto synthesis ([opp_op] of [bls12_prime.bls12_ops]), with the
      fiat-crypto [spec_of_UnOp un_opp].
    - [bls12_from_word]: stores the word and five zero limbs, then converts to the Montgomery
      domain in place with [bls12_to_mont]; fiat-crypto [spec_of_from_word].
    These functions are not added to [BLS12_Pairing.bls12_all_pairing_funcs]; the generated
    C/Rust code is unchanged.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Func.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Crypto.Arithmetic.WordByWordMontgomery.
Require Import Rupicola.Lib.Api.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok
  bls12_field_parameters bls12_frep bls12_frep_ok.

Local Notation functions_contain functions f :=
  (Interface.map.get functions (fst f) = Some (snd f)).

Module WBW := Crypto.Arithmetic.WordByWordMontgomery.WordByWordMontgomery.

(** ** Arithmetic of the limbs [w, 0, 0, 0, 0, 0] *)

Definition limbs_of_word (w : @Interface.word.rep 64 (Naive.word 64)) : list (@Interface.word.rep 64 (Naive.word 64)) :=
  [w; word.of_Z 0; word.of_Z 0; word.of_Z 0; word.of_Z 0; word.of_Z 0].

Lemma to_mont_limbs (w : @Interface.word.rep 64 (Naive.word 64)) :
  to_mont_model (Field.feval (limbs_of_word w)) = F.of_Z _ (word.unsigned w)
  /\ Field.bounded_by Field.tight_bounds (limbs_of_word w).
Proof.
  cbv [to_mont_model Field.feval Field.bounded_by Field.tight_bounds bls12_frep WordByWordMontgomery.field_representation Signature.field_representation Representation.frep Representation.eval_words list_in_bounds eval_trans limbs_of_word].
  cbn [ListDef.map].
  change (word.unsigned (word.of_Z 0)) with 0.
  change (WordByWordMontgomery.n m 64) with 6%nat.
  change (Z.of_nat felem_size_in_words) with 6.
  pose proof (word.unsigned_range w) as Hw.
  change (2 ^ 64) with 18446744073709551616 in Hw.
  set (z := word.unsigned w) in *.
  assert (Hm : 18446744073709551616 < m) by (vm_compute; reflexivity).
  assert (Hev : WordByWordMontgomery.WordByWordMontgomery.eval 64 (n:=6) [z; 0; 0; 0; 0; 0] = z).
  { cbv [WordByWordMontgomery.WordByWordMontgomery.eval Core.Positional.eval Core.Positional.to_associational Core.Associational.eval ListDef.map seq List.combine fold_right fst snd].
    rewrite !Z.mul_0_r, !Z.add_0_r. rewrite UniformWeight.uweight_0. lia. }
  assert (Hval : WordByWordMontgomery.WordByWordMontgomery.valid 64 6 m [z; 0; 0; 0; 0; 0]).
  { split.
    - cbv [WordByWordMontgomery.WordByWordMontgomery.small]. rewrite Hev.
      cbv [Partition.Partition.partition ListDef.map seq].
      repeat match goal with |- context[UniformWeight.uweight 64 ?k] =>
        let v := eval vm_compute in (UniformWeight.uweight 64 k) in
        change (UniformWeight.uweight 64 k) with v end.
      rewrite !(Z.mod_small z) by lia. rewrite Z.div_1_r.
      rewrite !(Z.div_small z) by lia. reflexivity.
    - rewrite Hev. lia. }
  split; [|exact Hval].
  destruct (WordByWordMontgomery.WordByWordMontgomery.from_montgomerymod_correct 64 6 m
    (PushButtonSynthesis.WordByWordMontgomery.r' m 64) (WordByWordMontgomery.m' m 64))
    with (v := [z; 0; 0; 0; 0; 0]) as [He _];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia | vm_compute; reflexivity
    | discriminate | vm_compute; reflexivity | exact Hval | ].
  rewrite Hev in He. cbv [WordByWordMontgomery.WordByWordMontgomery.eval] in He.
  rewrite <- F.of_Z_mul. apply F.eq_of_Z_iff.
  change (word.unsigned w) with z.
  change (OrdersEx.Z_as_DT.pos M_pos) with m.
  rewrite <- Zmult_mod_idemp_l, He, Zmult_mod_idemp_l.
  rewrite <- Z.mul_assoc, <- Zmult_mod_idemp_r.
  lazymatch goal with
  | |- (z * ?e) mod m = _ => replace e with 1 by (vm_compute; reflexivity)
  end.
  rewrite Z.mul_1_r. reflexivity.
Qed.

(** ** [bls12_opp] *)

Local Ltac epair :=
  lazymatch goal with
  | f := _ : string * Syntax.func |- _ =>
    let p := open_constr:((_, _)) in
    unify f p;
    subst f
  end.

Local Ltac felem_size_fast :=
  lazymatch goal with
  | |- (@felem_size_in_bytes _ _ _ _ _ ?fr <= 2 ^ _)%Z =>
    exact (@felem_size_ok _ _ _ _ _ _ bls12_frep_ok)
  end.

Existing Instance bls12_ops.

Derive bls12_opp
       SuchThat (forall functions,
                    functions_contain functions bls12_opp ->
                    spec_of_UnOp un_opp (field_representation:=bls12_frep) functions)
       As bls12_opp_correct.
Proof.
  epair.
  eapply opp_func_correct.
  all: try lazymatch goal with
           | |- _ = b2_func ?op => assert_fails (has_evar op); vm_compute; reflexivity
           end.
  all: lazymatch goal with
       | |- _ = @ErrorT.Success ?ErrT unit tt =>
         abstract (vm_cast_no_check (@eq_refl _ (@ErrorT.Success ErrT unit tt)))
       | |- Func.valid_func _ =>
         eapply Func.valid_func_bool_iff;
         abstract vm_cast_no_check (eq_refl true)
       | |- (_ = _)%Z => vm_compute; reflexivity
       | |- (felem_size_in_bytes <= 2 ^ _)%Z => felem_size_fast
       | _ => idtac
       end.
Qed.

(** ** [bls12_from_word] *)

Definition bls12_from_word : string * Syntax.func :=
  ("bls12_from_word", (["out"; "w"], (nil : list string), bedrock_func_body:(
    coq:(cmd.store access_size.word (expr.var "out") (expr.var "w"));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal 8)) (expr.literal 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal 16)) (expr.literal 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal 24)) (expr.literal 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal 32)) (expr.literal 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal 40)) (expr.literal 0));
    coq:(cmd.call [] "bls12_to_mont" [expr.var "out"; expr.var "out"])
  ))).

Lemma bls12_from_word_correct functions :
  functions_contain functions bls12_from_word ->
  functions_contain functions bls12_to_mont ->
  spec_of_from_word (field_representation:=bls12_frep) functions.
Proof.
intros E_fw E_tm.
cbv [spec_of_from_word].
intros pout x out R tr m0 [Hsep Hlen].
seprewrite_in (felem_from_bytes pout out Hlen) Hsep.
unfold FElem in Hsep.
change (Memory.bytes_per_word 64) with 8 in Hsep.
set (ys := proj1_sig (bs2felem out)) in Hsep.
assert (Hyslen : length ys = 6%nat) by (subst ys; destruct (bs2felem out); assumption).
clearbody ys.
destruct ys as [| y0 [| y1 [| y2 [| y3 [| y4 [| y5 []]]]]]]; try discriminate.
clear Hyslen.
cbn [array] in Hsep.
repeat match type of Hsep with
| context[word.add (word.add ?base (word.of_Z ?a)) (word.of_Z ?b)] =>
  let c := eval cbv in (a + b)%Z in
  replace (word.add (word.add base (word.of_Z a)) (word.of_Z b))
    with (word.add base (word.of_Z c)) in Hsep by ring
end.
eapply start_func; [exact E_fw | clear E_fw].
cbv match beta delta [WeakestPrecondition.func bls12_from_word snd].
eexists; split; [exact eq_refl|].
repeat straightline.
subst a a0 a1 a2 a3 args.
pose (X := exist (fun l => length l = felem_size_in_words) [x; v; v0; v1; v2; v3] eq_refl : felem).
assert (HX : (FElem pout X * R)%sep m5).
{ unfold FElem; cbv [X proj1_sig].
  change (Memory.bytes_per_word 64) with 8.
  cbn [array].
  repeat match goal with
  | |- context[word.add (word.add ?base (word.of_Z ?a)) (word.of_Z ?b)] =>
    let c := eval cbv in (a + b)%Z in
    replace (word.add (word.add base (word.of_Z a)) (word.of_Z b))
      with (word.add base (word.of_Z c)) by ring
  end.
  pose proof (proj2 (sep_emp_True_r _ m5) H4) as H4'.
  ecancel_assumption. }
pose proof HX as HXb.
seprewrite_in (felem_to_bytes pout X) HXb.
destruct (to_mont_limbs x) as [Hval Hbnd].
eapply WeakestPreconditionProperties.Proper_call;
  [ | exact (bls12_to_mont_correct functions E_tm pout pout X _ R tr m5
               (conj Hbnd (conj (ws2bs_felem_length X) (conj (ex_intro _ R HX) HXb)))) ].
intros t m6 rets (Hrets & Ht & out' & Hv & Hb & Hs). subst rets.
eexists; split; [reflexivity|].
cbn [list_map]. split; [reflexivity|]. split; [exact Ht|].
exists out'. split; [|split].
- rewrite Hv. exact Hval.
- exact Hb.
- exact Hs.
Qed.
