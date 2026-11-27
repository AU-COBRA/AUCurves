(** * secp256k1 wNAF scalar multiplication and RCB addition on a concrete function table.

    [Secp256k1_wNAF_Instance.secp256k1_wnaf_single_full] and
    [CurveAddGeneralA_Secp256k1.secp256k1_curve_add_general_full] take two premises on the
    function environment: the table ([secp256k1_wnaf_table_ok]: the derived addition, its
    two constant loaders, the wrappers of NistWnafWrappers.v, felem_copy) and the field
    leaf specs ([secp256k1_wnaf_leaf_specs]: mul, add, sub, opp, from_word).  This file
    discharges both for the concrete environment [secp256k1_wnaf_env]:

      - mul, add, sub, opp, felem_copy, to_mont: fiat-crypto's synthesized functions of
        [Crypto.Bedrock.Secp256k1.Field256k1] with their correctness lemmas;
      - from_word: [secp256k1_from_word] below (store the word in the low limb, zero the
        others, convert to the Montgomery domain with "secp256k1_to_mont"), proved here
        (the four-limb version of [BLS12_FpExtra.bls12_from_word]);
      - the group-level functions: the bodies of [Secp256k1_wNAF_Instance.v].

    Main statements, with no premise on the environment:
      [secp256k1_wnaf_env_table_ok], [secp256k1_wnaf_env_leaf_specs];
      [secp256k1_wnaf_single_closed]  the wNAF driver computes [k * P] up to projective
                                      equality (as [secp256k1_wnaf_single_full]);
      [secp256k1_curve_add_general_closed]  "curve_add_general" meets its spec.

    Honesty ledger (this file): 0 Admitted, 0 Axiom. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Specs.Field.
Require Crypto.Arithmetic.WordByWordMontgomery.
Require Import Rupicola.Lib.Api.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Bedrock.Secp256k1.Field256k1.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Group.CurveAdd.WNAFTable.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_Secp256k1.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Require Import Bedrock.Group.ScalarMult.Secp256k1_wNAF_Instance.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok
  Field256k1.field_parameters secp256k1_field_parameters_ok
  Field256k1.frep256k1 Field256k1.frep256k1_ok.

Local Notation functions_contain functions f :=
  (Interface.map.get functions (fst f) = Some (snd f)).

Local Notation function_t := (String.string * Syntax.func)%type.

(** ** [secp256k1_from_word] *)

Definition limbs_of_word (w : @Interface.word.rep 64 (Naive.word 64))
  : list (@Interface.word.rep 64 (Naive.word 64)) :=
  [w; word.of_Z 0; word.of_Z 0; word.of_Z 0].

Lemma to_mont_limbs (w : @Interface.word.rep 64 (Naive.word 64)) :
  to_mont_model (Field.feval (limbs_of_word w)) = F.of_Z _ (word.unsigned w)
  /\ Field.bounded_by Field.tight_bounds (limbs_of_word w).
Proof.
  cbv [to_mont_model Field.feval Field.bounded_by Field.tight_bounds Field256k1.frep256k1
       WordByWordMontgomery.field_representation Signature.field_representation
       Representation.frep Representation.eval_words list_in_bounds eval_trans limbs_of_word].
  cbn [ListDef.map].
  change (word.unsigned (word.of_Z 0)) with 0.
  change (WordByWordMontgomery.n Field256k1.m 64) with 4%nat.
  change (Z.of_nat felem_size_in_words) with 4.
  pose proof (word.unsigned_range w) as Hw.
  change (2 ^ 64) with 18446744073709551616 in Hw.
  set (z := word.unsigned w) in *.
  assert (Hm : 18446744073709551616 < Field256k1.m) by (vm_compute; reflexivity).
  assert (Hev : WordByWordMontgomery.WordByWordMontgomery.eval 64 (n:=4) [z; 0; 0; 0] = z).
  { cbv [WordByWordMontgomery.WordByWordMontgomery.eval Core.Positional.eval
         Core.Positional.to_associational Core.Associational.eval ListDef.map seq
         List.combine fold_right fst snd].
    rewrite !Z.mul_0_r, !Z.add_0_r. rewrite UniformWeight.uweight_0. lia. }
  assert (Hval : WordByWordMontgomery.WordByWordMontgomery.valid 64 4 Field256k1.m [z; 0; 0; 0]).
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
  destruct (WordByWordMontgomery.WordByWordMontgomery.from_montgomerymod_correct 64 4
    Field256k1.m (PushButtonSynthesis.WordByWordMontgomery.r' Field256k1.m 64)
    (WordByWordMontgomery.m' Field256k1.m 64))
    with (v := [z; 0; 0; 0]) as [He _];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia | vm_compute; reflexivity
    | discriminate | vm_compute; reflexivity | exact Hval | ].
  rewrite Hev in He. cbv [WordByWordMontgomery.WordByWordMontgomery.eval] in He.
  rewrite <- F.of_Z_mul. apply F.eq_of_Z_iff.
  change (word.unsigned w) with z.
  change (OrdersEx.Z_as_DT.pos M_pos) with Field256k1.m.
  rewrite <- Zmult_mod_idemp_l, He, Zmult_mod_idemp_l.
  rewrite <- Z.mul_assoc, <- Zmult_mod_idemp_r.
  lazymatch goal with
  | |- (z * ?e) mod Field256k1.m = _ => replace e with 1 by (vm_compute; reflexivity)
  end.
  rewrite Z.mul_1_r. reflexivity.
Qed.

Definition secp256k1_from_word : string * Syntax.func :=
  ("secp256k1_from_word", (["out"; "w"], (nil : list string), bedrock_func_body:(
    coq:(cmd.store access_size.word (expr.var "out") (expr.var "w"));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal 8)) (expr.literal 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal 16)) (expr.literal 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal 24)) (expr.literal 0));
    coq:(cmd.call [] "secp256k1_to_mont" [expr.var "out"; expr.var "out"])
  ))).

Lemma secp256k1_from_word_correct functions :
  functions_contain functions secp256k1_from_word ->
  functions_contain functions Field256k1.secp256k1_to_mont ->
  spec_of_from_word (field_representation:=Field256k1.frep256k1) functions.
Proof.
intros E_fw E_tm.
cbv [spec_of_from_word].
intros pout x out R tr m0 [Hsep Hlen].
seprewrite_in (felem_from_bytes pout out Hlen) Hsep.
unfold FElem in Hsep.
change (Memory.bytes_per_word 64) with 8 in Hsep.
set (ys := proj1_sig (bs2felem out)) in Hsep.
assert (Hyslen : length ys = 4%nat) by (subst ys; destruct (bs2felem out); assumption).
clearbody ys.
destruct ys as [| y0 [| y1 [| y2 [| y3 []]]]]; try discriminate.
clear Hyslen.
cbn [array] in Hsep.
repeat match type of Hsep with
| context[word.add (word.add ?base (word.of_Z ?a)) (word.of_Z ?b)] =>
  let c := eval cbv in (a + b)%Z in
  replace (word.add (word.add base (word.of_Z a)) (word.of_Z b))
    with (word.add base (word.of_Z c)) in Hsep by ring
end.
eapply start_func; [exact E_fw | clear E_fw].
cbv match beta delta [WeakestPrecondition.func secp256k1_from_word snd].
eexists; split; [exact eq_refl|].
repeat straightline.
subst a a0 a1 args.
pose (X := exist (fun l => length l = felem_size_in_words) [x; v; v0; v1] eq_refl : felem).
assert (HX : (FElem pout X * R)%sep m3).
{ unfold FElem; cbv [X proj1_sig].
  change (Memory.bytes_per_word 64) with 8.
  cbn [array].
  repeat match goal with
  | |- context[word.add (word.add ?base (word.of_Z ?a)) (word.of_Z ?b)] =>
    let c := eval cbv in (a + b)%Z in
    replace (word.add (word.add base (word.of_Z a)) (word.of_Z b))
      with (word.add base (word.of_Z c)) by ring
  end.
  pose proof (proj2 (sep_emp_True_r _ m3) H2) as H2'.
  ecancel_assumption. }
pose proof HX as HXb.
seprewrite_in (felem_to_bytes pout X) HXb.
destruct (to_mont_limbs x) as [Hval Hbnd].
eapply WeakestPreconditionProperties.Proper_call;
  [ | exact (Field256k1.secp256k1_to_mont_correct functions E_tm pout pout X _ R tr m3
               (conj Hbnd (conj (ws2bs_felem_length X) (conj (ex_intro _ R HX) HXb)))) ].
intros t m6 rets (Hrets & Ht & out' & Hv & Hb & Hs). subst rets.
eexists; split; [reflexivity|].
cbn [list_map]. split; [reflexivity|]. split; [exact Ht|].
exists out'. split; [|split].
- rewrite Hv. exact Hval.
- exact Hb.
- exact Hs.
Qed.

(** ** The environment *)

Definition secp256k1_wnaf_funcs : list function_t :=
  [ ("curve_add_general", secp256k1_curve_add_general_func);
    ("secp256k1_three_b", secp256k1_three_b_func);
    ("secp256k1_a_const", secp256k1_a_const_func);
    ("curve_add", snd secp256k1_curve_add_inplace_func);
    ("curve_double", snd secp256k1_curve_double_func);
    ("store_zero", snd secp256k1_store_zero_func);
    ("opp_inplace", snd secp256k1_opp_inplace_func);
    Field256k1.secp256k1_felem_copy;
    Field256k1.secp256k1_mul;
    Field256k1.secp256k1_add;
    Field256k1.secp256k1_sub;
    Field256k1.secp256k1_opp;
    secp256k1_from_word;
    Field256k1.secp256k1_to_mont;
    secp256k1_wnaf_single_func ].

Definition secp256k1_wnaf_env : Semantics.env := map.of_list secp256k1_wnaf_funcs.

Definition first_binding (l : list function_t) (k : string) : option Syntax.func :=
  option_map snd (List.find (fun p => String.eqb (fst p) k) l).

Lemma get_of_list_find (l : list function_t) (k : string) :
  map.get (map.of_list l : Semantics.env) k = first_binding l k.
Proof.
  unfold first_binding.
  induction l as [| [k0 v0] l IH]; cbn [map.of_list List.find fst].
  - rewrite map.get_empty. reflexivity.
  - rewrite map.get_put_dec. destruct (String.eqb k0 k); [reflexivity | exact IH].
Qed.

(** One conversion per name: [List.find] only compares names. *)
Local Ltac env_get := rewrite get_of_list_find; exact eq_refl.

Lemma secp256k1_wnaf_env_table_ok : secp256k1_wnaf_table_ok secp256k1_wnaf_env.
Proof.
  cbv [secp256k1_wnaf_table_ok secp256k1_wnaf_env].
  repeat split; env_get.
Qed.

Lemma env_mul : functions_contain secp256k1_wnaf_env Field256k1.secp256k1_mul.
Proof. cbv [secp256k1_wnaf_env]. env_get. Qed.
Lemma env_add : functions_contain secp256k1_wnaf_env Field256k1.secp256k1_add.
Proof. cbv [secp256k1_wnaf_env]. env_get. Qed.
Lemma env_sub : functions_contain secp256k1_wnaf_env Field256k1.secp256k1_sub.
Proof. cbv [secp256k1_wnaf_env]. env_get. Qed.
Lemma env_opp : functions_contain secp256k1_wnaf_env Field256k1.secp256k1_opp.
Proof. cbv [secp256k1_wnaf_env]. env_get. Qed.
Lemma env_from_word : functions_contain secp256k1_wnaf_env secp256k1_from_word.
Proof. cbv [secp256k1_wnaf_env]. env_get. Qed.
Lemma env_to_mont : functions_contain secp256k1_wnaf_env Field256k1.secp256k1_to_mont.
Proof. cbv [secp256k1_wnaf_env]. env_get. Qed.

Lemma secp256k1_wnaf_env_leaf_specs : secp256k1_wnaf_leaf_specs secp256k1_wnaf_env.
Proof.
  cbv [secp256k1_wnaf_leaf_specs]. repeat split.
  - exact (Field256k1.secp256k1_mul_correct _ env_mul).
  - exact (Field256k1.secp256k1_add_correct _ env_add).
  - exact (Field256k1.secp256k1_sub_correct _ env_sub).
  - exact (Field256k1.secp256k1_opp_correct _ env_opp).
  - exact (secp256k1_from_word_correct _ env_from_word env_to_mont).
Qed.

(** ** The closed statements *)

Theorem secp256k1_curve_add_general_closed :
  spec_of_rcb_add_general secp256k1_three_b_felem secp256k1_a_felem secp256k1_wnaf_env.
Proof.
  exact (secp256k1_rcb_add_general_spec _ secp256k1_wnaf_env_table_ok
           secp256k1_wnaf_env_leaf_specs).
Qed.

Theorem secp256k1_wnaf_single_closed :
  forall k, 0 <= k < 2 ^ 256 ->
  forall Px Py Pz table_entries,
    secp256k1_oncurve (Px,Py,Pz) ->
    secp256k1_table_ok Px Py Pz table_entries ->
  forall pOx pOy pOz pAx pAy pAz pT pDK
    (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F M_pos)
    (Rinner : BasicC64Semantics.mem -> Prop) tr m l,
  map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
  map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
  map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
  map.get l "table_P" = Some pT ->
  map.get l "digits_k" = Some pDK ->
  (Compilation2.FElem (Some tight_bounds) pOx Ox0
   ⋆ Compilation2.FElem (Some tight_bounds) pOy Oy0
   ⋆ Compilation2.FElem (Some tight_bounds) pOz Oz0
   ⋆ (Compilation2.FElem (Some tight_bounds) pAx Ax0
      ⋆ Compilation2.FElem (Some tight_bounds) pAy Ay0
      ⋆ Compilation2.FElem (Some tight_bounds) pAz Az0)
   ⋆ DigitArray pDK (secp256k1_digits k) ⋆ Table4 pT table_entries
   ⋆ Rinner) m ->
  WeakestPrecondition.cmd secp256k1_wnaf_env
    (snd (snd secp256k1_wnaf_single_func))
    tr m l
    (fun t m' l' =>
      exists Rx Ry Rz Ax' Ay' Az',
      secp256k1_oncurve (Rx,Ry,Rz)
      /\ secp256k1_pt_eq (Rx,Ry,Rz) (secp256k1_scmul (Z.to_nat k) (Px,Py,Pz))
      /\ (Compilation2.FElem (Some tight_bounds) pOx Rx
          ⋆ Compilation2.FElem (Some tight_bounds) pOy Ry
          ⋆ Compilation2.FElem (Some tight_bounds) pOz Rz
          ⋆ (Compilation2.FElem (Some tight_bounds) pAx Ax'
             ⋆ Compilation2.FElem (Some tight_bounds) pAy Ay'
             ⋆ Compilation2.FElem (Some tight_bounds) pAz Az')
          ⋆ DigitArray pDK (secp256k1_digits k) ⋆ Table4 pT table_entries
          ⋆ Rinner) m').
Proof.
  exact (secp256k1_wnaf_single_full secp256k1_wnaf_env secp256k1_wnaf_env_table_ok
           secp256k1_wnaf_env_leaf_specs).
Qed.
