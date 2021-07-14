Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery. 
Local Open Scope Z_scope.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Local Open Scope string_scope.
Import ListNotations.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.Syntax.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import bedrock2.Semantics.
Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.ReifiedOperation.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Local Open Scope Z_scope.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.Spec.MxDH.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Translation.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import bedrock2.Semantics.
Require Import Theory.Fields.QuadraticFieldExtensions.
Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.
Require Import Bedrock.Field.bls12prime.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import coqutil.Map.Properties.
Require Import bedrock2.Lift1Prop.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Bedrock.Util.Word.
Require Import SOSReduction.
Require Import Bedrock.Util.Util.
Require Import Bedrock.Util.Bignum.
Require Import Bedrock.Util.Tactics.
Require Import Bedrock.Util.SeparationLogic.

Local Open Scope Z_scope.

(*Parameters to be changed: specify prime and import reification from cache.*)
    Require Import Bedrock.Examples.felem_copy_64.
    Local Definition felem_suffix := felem_copy_64.aff.
    Local Notation m := bls12prime.m.
    Local Definition prefix := "bls12_"%string. (* placed before function names *)
    Local Notation a := (0 mod m).
    Local Notation b := (4 mod m).

    Existing Instances Defaults64.default_parameters Defaults64.default_parameters_ok bls12_bedrock2_funcs
    bls12_bedrock2_specs bls12_bedrock2_correctness.

(*  We instantiate specs of all imported bedrock2 functions.
    This needs to be done for typeclass inference to work properly.*)

  Instance spec_of_reified_mul :
  spec_of (append prefix "mul") := spec_of_mul.

  Instance spec_of_reified_square :
  spec_of (append prefix "square") := spec_of_square.

  Instance spec_of_reified_add :
  spec_of (append prefix "add") := spec_of_add.

  Instance spec_of_reified_sub :
  spec_of (append prefix "sub") := spec_of_sub.

  Instance spec_of_reified_opp :
  spec_of (append prefix "opp") := spec_of_opp.

  Instance spec_of_reified_to_montgomery :
  spec_of (append prefix "to_montgomery") := spec_of_to_montgomery.

  Instance spec_of_reified_from_montgomery :
  spec_of (append prefix "from_montgomery") := spec_of_from_montgomery.

  Instance spec_of_reified_nonzero :
  spec_of (append prefix "nonzero") := spec_of_nonzero.

  Instance spec_of_reified_selectznz :
  spec_of (append prefix "selectznz") := spec_of_selectznz.

  Instance spec_of_reified_to_bytes :
  spec_of (append prefix "to_bytes") := spec_of_to_bytes.

  Instance spec_of_reified_from_bytes :
  spec_of (append prefix "from_bytes") := spec_of_from_bytes.
(*Instantiation done.*)

(*Initializing parameters; do not touch*)
Local Notation bw := width.
Local Notation m' := (@WordByWordMontgomery.m' m bw).
Notation n := (WordByWordMontgomery.n m (@width semantics)).
Local Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
Local Notation valid := (@WordByWordMontgomery.valid bw n m).
Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
Local Notation thisword := (@word semantics).
Local Definition valid_words w := valid (List.map (@Interface.word.unsigned width thisword) w).
Local Definition map_words := List.map (@Interface.word.unsigned width thisword).
Local Notation r := (WordByWordMontgomery.r bw).
Local Notation r' := (WordByWordMontgomery.r' m bw).
Local Definition num_bytes := Eval compute in (Z.of_nat (((Z.to_nat bw * n) / 8)%nat)).
Local Notation three_b := (3 * b mod m).
Local Notation uw := (uweight bw).
Notation three_b_list := (MontgomeryCurveSpecs.three_b_list bw n three_b).
Definition three_b_mont := Eval vm_compute in (MontgomeryCurveSpecs.three_b_mont_list m bw n m' three_b).

(*Lemmas of correctness of parameters to be used for montgomery arithmetic.*)
Lemma a_small : a = a mod m.
Proof. auto. Qed.

Lemma three_b_small : three_b = three_b mod m.
Proof. auto. Qed.

Lemma r'_correct : (2 ^ bw * r') mod m = 1.
Proof. auto with zarith. Qed.

Lemma m'_correct : (m * m') mod 2 ^ bw = -1 mod 2 ^ bw.
Proof. auto with zarith. Qed.

Lemma bw_big : 0 < bw.
Proof. cbv; auto. Qed.

Lemma m_big : 1 < m.
Proof. cbv; auto. Qed.

Lemma n_nz : n <> 0%nat.
Proof. cbv; discriminate. Qed.

Lemma m_small : m < (2 ^ bw) ^ Z.of_nat n.
Proof. cbv; auto. Qed.

Lemma m_big' : 1 < m.
Proof. cbv; auto. Qed.

Lemma n_small : Z.of_nat n < 2 ^ bw.
Proof. cbv. auto. Qed.

Ltac wbw_conds :=
  repeat first [ progress apply r'_correct
               | progress apply m'_correct
               | progress apply bw_big
               | progress apply m_big
               | progress apply n_nz
               | progress apply m_small
               | progress apply m'_correct
               | progress apply m'_correct ].

Local Notation from_mont_correct := (@from_mont_correct m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
Local Notation valid_mod := (valid_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
Local Notation mont_add := (mont_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
Local Notation mont_sub := (mont_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
Local Notation mont_mul := (mont_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
Local Notation valid_valid'_equiv := (valid_valid'_equiv m bw n n_nz m_big).
Local Notation evfrom_mod := (evfrom_mod' m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
Local Notation eval_from_mont_inj := (eval_from_mont_inj m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
Local Notation mont_zero := (mont_zero m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
Local Notation toZ_ofZ_eq := (toZ_ofZ_eq n n_nz n_small m).

Lemma num_bytes_correct : num_bytes = Z.of_nat (n * Z.to_nat word_size_in_bytes).
Proof. cbv; auto. Qed.


Lemma three_b_mont_correct : three_b_mont = (WordByWordMontgomery.to_montgomerymod bw n m m' three_b_list).
Proof. vm_compute (WordByWordMontgomery.to_montgomerymod bw n m m' three_b_list). reflexivity. Qed.

Lemma three_b_valid: valid three_b_list.
Proof.
  apply three_b_list_valid; cbv; auto. intros; discriminate.
Qed.

Lemma three_b_mont_valid : valid three_b_mont.
Proof.
  unfold three_b_mont. cbv; repeat split; auto; intros; discriminate.
Qed.

Lemma a_mont_zero : (a_mont m bw n r' m' a a_small
    r'_correct m'_correct bw_big n_nz m_small m_big) = mont_zero.
  Proof.
    apply mont_enc_irr. simpl. cbv [a_mont_list]. apply f_equal. cbv [a_list].
    assert (a = 0) by (cbv; reflexivity). rewrite H. cbv. auto.
  Qed.

(*Some notation*)
Notation my_mul := (my_mul m).
Notation my_add := (my_add m).
Notation my_sub := (my_sub m).

Local Infix "*'" := my_mul (at level 70).
Local Infix "+'" := my_add (at level 80).
Local Infix "-'" := my_sub (at level 80).

Local Notation evfrom x := (eval (from_mont x)).

(*Gallina specs
  Note that we use 2 different specs; one is more general and proven correct in Fiats library.
  The other is correct only when the parameter a is 0; which is the case here.
  Their equivalence is shown below.*)
Definition BLS12_add_Gallina_spec :=
    BLS12_add_Gallina_spec m bw n m' a three_b.

Definition BLS12_add_Gallina_spec_a_0 X1 Y1 Z1 X2 Y2 Z2 outx outy outz :=
  let X1 := evfrom X1 in
  let Y1 := evfrom Y1 in
  let Z1 := evfrom Z1 in
  let X2 := evfrom X2 in
  let Y2 := evfrom Y2 in
  let Z2 := evfrom Z2 in
  let t0 := X1*'X2 in
  let t1 := Y1*'Y2 in
  let t2 := Z1*'Z2 in
  let t3 := X1+'Y1 in
  let t4 := X2+'Y2 in
  let t3 := t3*'t4 in
  let t4 := t0+'t1 in
  let t3 := t3-'t4 in
  let t4 := X1+'Z1 in
  let t5 := X2+'Z2 in
  let t4 := t4*'t5 in
  let t5 := t0+'t2 in
  let t4 := t4-'t5 in
  let t5 := Y1+'Z1 in
  let X3 := Y2+'Z2 in
  let t5 := t5*'X3 in
  let X3 := t1+'t2 in
  let t5 := t5-'X3 in
  let Z3 := eval three_b_list *'t2 in
  let X3 := t1-'Z3 in
  let Z3 := t1+'Z3 in
  let Y3 := X3*'Z3 in
  let t1 := t0+'t0 in
  let t1 := t1+'t0 in
  let t4 := eval three_b_list *'t4 in
  let t0 := t1*'t4 in
  let Y3 := Y3+'t0 in
  let t0 := t5*'t4 in
  let X3 := t3*'X3 in
  let X3 := X3-'t0 in
  let t0 := t3*'t1 in
  let Z3 := t5*'Z3 in
  let Z3 := Z3+'t0 in
  ( eval (from_mont (outx)), eval (from_mont ( outy)), eval (from_mont(outz))) = (X3, Y3, Z3).

Lemma add_specs_equiv : forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz, 
  BLS12_add_Gallina_spec X1 X2 Y1 Y2 Z1 Z2 outx outy outz 
  <-> BLS12_add_Gallina_spec_a_0 X1 X2 Y1 Y2 Z1 Z2 outx outy outz.
Proof.
  intros X1 X2 Y1 Y2 Z1 Z2 outx outy outz.
  unfold BLS12_add_Gallina_spec, MontgomeryCurveSpecs.BLS12_add_Gallina_spec.
  unfold BLS12_add_Gallina_spec_a_0.
  assert (H0 : eval (a_list bw n a) = 0) by auto. rewrite H0.

  remember (evfrom X1) as x1.
  remember (evfrom X2) as x2.
  remember (evfrom Y1) as y1.
  remember (evfrom Y2) as y2.
  remember (evfrom Z1) as z1.
  remember (evfrom Z2) as z2.
  remember (eval three_b_list) as tb.
  unfold my_mul, my_add, my_sub.
  pull_Zmod.

  split; (intros H; rewrite H; apply pair_equal_spec; split; [apply pair_equal_spec; split| ]; apply (f_equal (fun y => y mod m)); ring).
Qed.

(*Bedrock2 Function Definition*)
Definition BLS12_add : Syntax.func :=
    let outx := "outx" in
    let outy := "outy" in
    let outz := "outz" in

    let X1 := "X1" in
    let Y1 := "Y1" in
    let Z1 := "Z1" in

    let X2 := "X2" in
    let Y2 := "Y2" in
    let Z2 := "Z2" in

    let t0 := "t0" in
    let t1 := "t1" in
    let t2 := "t2" in
    let t3 := "t3" in
    let t4 := "t4" in
    let t5 := "t5" in
    let three_b := "three_b" in
    let add := (append prefix "add") in
    let mul := (append prefix "mul") in
    let sub := (append prefix "sub") in  
    ("BLS12_add", (
      [outx; outy; outz; X1; Y1; Z1; X2; Y2; Z2], [],
      bedrock_func_body:(
      stackalloc num_bytes as three_b{
        stackalloc num_bytes as t0 {
          stackalloc num_bytes as t1 {
            stackalloc num_bytes as t2 {
              stackalloc num_bytes as t3 {
                stackalloc num_bytes as t4 {
                  stackalloc num_bytes as t5 {
                      store(three_b, (coq:(nth 0 three_b_mont 0)));
                      store(three_b + coq:(8), coq:(nth 1 three_b_mont 0));
                      store(three_b + coq:(16), coq:(nth 2 three_b_mont 0));
                      store(three_b + coq:(24), coq:(nth 3 three_b_mont 0));
                      store(three_b + coq:(32), coq:(nth 4 three_b_mont 0));
                      store(three_b + coq:(40), coq:(nth 5 three_b_mont 0));
                      mul (t0, X1, X2);
                      mul (t1, Y1, Y2);
                      mul (t2, Z1, Z2);
                      add (t3, X1, Y1);
                      add (t4, X2, Y2);
                      mul (t3, t3, t4);
                      add (t4, t0, t1);
                      sub (t3, t3, t4);
                      add (t4, X1, Z1);
                      add (t5, X2, Z2);
                      mul (t4, t4, t5);
                      add (t5, t0, t2);
                      sub (t4, t4, t5);
                      add (t5, Y1, Z1);
                      add (outx, Y2, Z2);
                      mul (t5, t5, outx);
                      add (outx, t1, t2);
                      sub (t5, t5, outx);
                      mul (outz, three_b, t2);
                      sub (outx, t1, outz);
                      add (outz, outz, t1);
                      mul (outy, outx, outz);
                      add (t1, t0, t0);
                      add (t1, t1, t0);
                      mul (t4, three_b, t4);
                      mul (t0, t1, t4);
                      add (outy, outy, t0);
                      mul (t0, t5, t4);
                      mul (outx, t3, outx);
                      sub (outx, outx, t0);
                      mul (t0, t3, t1);
                      mul (outz, t5, outz);
                      add (outz, outz, t0)
                  }
                }
              }
            }
          }
        }
      }
      )
    )).

Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.
Local Notation toZ x := (List.map Interface.word.unsigned x).

(*Bedrock2 function Spec*)
Instance spec_of_BLS12_add: spec_of BLS12_add :=
fun functions : list (string * (list string * list string * cmd)) =>
    forall (wX1 wY1 wZ1 wX2 wY2 wZ2 : list Interface.word.rep)
    (pX1 pY1 pZ1 pX2 pY2 pZ2  poutx pouty poutz: Interface.word.rep)
    (wold_outx wold_outy wold_outz: list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (Rout : Interface.map.rep -> Prop),
    valid (List.map Interface.word.unsigned wX1) /\
    valid (List.map Interface.word.unsigned wY1) /\
    valid (List.map Interface.word.unsigned wZ1) /\
    valid (List.map Interface.word.unsigned wX2) /\
    valid (List.map Interface.word.unsigned wY2) /\
    valid (List.map Interface.word.unsigned wZ2) ->
    ((Bignum n pX1 wX1) *
    (Bignum n pX2 wX2) *
    (Bignum n pY1 wY1) *
    (Bignum n pY2 wY2) *
    (Bignum n pZ1 wZ1) *
    (Bignum n pZ2 wZ2) *
    (Bignum n poutx wold_outx) * (Bignum n pouty wold_outy) * (Bignum n poutz wold_outz) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "BLS12_add") t m0
    ([poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutx wouty woutz : list Interface.word.rep) Rout,
        (
                (BLS12_add_Gallina_spec (toZ wX1) (toZ wY1) (toZ wZ1) (toZ wX2) (toZ wY2) 
                (toZ wZ2) (toZ woutx) (toZ wouty) (toZ woutz)/\
                valid (List.map Interface.word.unsigned woutx) /\
                valid (List.map Interface.word.unsigned wouty) /\
                valid (List.map Interface.word.unsigned woutz)) /\
             ((Bignum n pX1 wX1) *
             (Bignum n pX2 wX2) *
             (Bignum n pY1 wY1) *
             (Bignum n pY2 wY2) *
             (Bignum n pZ1 wZ1) *
             (Bignum n pZ2 wZ2) * (Bignum n poutx woutx) * (Bignum n pouty wouty) * (Bignum n poutz woutz) * Rout)%sep m'))).

(*Number of lemmas and tactics used in proof.*)
(*First some notation is introduced*)
Notation msplit := Interface.map.split.

Notation montsub a b c :=
  ((eval (from_mont (a))) mod m =
      (eval (from_mont (b)) -
       eval (from_mont (c))) mod m).

Notation montadd a b c :=
  ((eval (from_mont (a))) mod m =
      (eval (from_mont (b)) +
       eval (from_mont (c))) mod m).

Notation montmul a b c :=
  ((eval (from_mont (a))) mod m =
      (eval (from_mont (b)) *
       eval (from_mont (c))) mod m).

Notation S aw := (word.add (word.of_Z word_size_in_bytes) aw).

Add Ring Mp : (MontgomeryRingTheory.mont_enc_ring BLS12Curve_G1.m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).

Local Notation wordof_Z := (@word.of_Z width
(@word _)).

(*Tactics to cast from Bignum to bytes*)
Ltac unfold_Bignum_list_step H l :=
  destruct l; [unfold Bignum in H; sepsimpl_hyps; discriminate|].

Ltac unfold_Bignum_list H l :=
  repeat unfold_Bignum_list_step H l;
  assert (Hl : l = []) by ( unfold Bignum in H; sepsimpl_hyps;
  apply length_nil;
  match goal with 
  | [H : Datatypes.length _ = n|- _ ] 
    => repeat apply NPeano.Nat.succ_inj in H; auto
  end); rewrite Hl in H; clear Hl.

Ltac straightline' :=
  match goal with
  | [Hminit : ?mcond (?minit)
      |- forall (_ : @word.rep _ _)
                (_ _ : @Interface.map.rep _ _ _),
          anybytes _ ?numbytes _ -> msplit _ ?minit _ -> _ ] =>
      let a := (fresh "a") in
      let mStack := (fresh "mStack") in
      let mnew := (fresh "mnew") in
      let Hany := (fresh "Hany") in
      let HanyBignum := (fresh "HanyBignum") in
      let anyval := (fresh "anyval") in
      let Hsplit := (fresh "Hsplit") in
      let Hmnew := (fresh "Hmnew") in
      let R := (fresh "R") in
      intros a mStack mnew Hany Hsplit; destruct (anybytes_Bignum n num_bytes mStack a num_bytes_correct Hany) as [anyval HanyBignum];
      destruct (alloc_seps_alt mnew minit mStack mcond (Bignum _ _ _) Hsplit (empty_frame mcond minit Hminit) (empty_frame (Bignum _ _ _) mStack HanyBignum)) as [R Hmnew];
      clear Hany Hsplit HanyBignum
  | _ => straightline
  end.

Ltac clear_emps_step :=
lazymatch goal with
| [H' : (_ * _)%sep ?mem |- _] =>
    let thisH := (fresh "H") in
    eassert (thisH : (emp _ * _)%sep mem) by ecancel_assumption; clear H'; sepsimpl_hyps
    end.

Ltac get_list_from_length l :=
  (repeat (destruct l; [discriminate| ])); destruct l; [| discriminate].

Ltac Bignum_to_Scalars l := let Hsep := (fresh "Hsep") in
eassert (Hsep : (Bignum n _ l * _)%sep _) by ecancel_assumption;
apply Bignum_manyScalars_R in Hsep; sepsimpl_hyps; get_list_from_length l;
lazymatch goal with
| [H : (many_Scalars n _ _ * _)%sep _ |- _] => let Htemp := (fresh "Htemp") in
  eassert (Htemp : many_Scalars n _ _ = many_Scalars _ _ _) by (vm_compute n; auto);
  rewrite Htemp in H; clear Htemp;
  repeat rewrite many_Scalars_next in H;
  rewrite many_Scalars_nil in H
| _ => fail
end.

(*Tactics to store constants into allocated memory*)
Ltac subst_vars :=
  lazymatch goal with
  | [|- WeakestPrecondition.store _ _ ?thisa _ _] =>
    try subst thisa
  end.

Ltac handle_store_step :=
  lazymatch goal with
    | [ |- ((Scalars.scalar ?thisa _) * _)%sep _ ] =>
     try subst thisa; repeat (rewrite next_word'; try (rewrite word_add_0)); ecancel_assumption
  end.

Ltac handle_store :=
  repeat (subst_vars; eapply Scalars.store_word_of_sep; [handle_store_step|]; repeat straightline'); clear_old_seps.

(*Tactics to handle stack allocation*)
Lemma alloc_anybytes_Bignum n0 : forall (R : Interface.map.rep -> Prop) a m m0 m1, n0 = Z.of_nat (n * Z.to_nat word_size_in_bytes) -> msplit m m0 m1 -> anybytes a n0 m1 -> R m0 -> exists l, (R * (Bignum n a l))%sep m.
Proof.
  intros.
  pose proof (anybytes_Bignum n m1 n0 a).
  apply H3 in H1; [| cbv; auto].
  destruct H1. exists x. unfold sep. exists m0. exists m1. auto. 
Qed.

Ltac alloc_Bignum := lazymatch goal with 
  | Hprec : _ ?mpre |- forall _ _ _, anybytes _ ?n0 _ ->
    msplit _ ?mpre _ -> _ =>
    let a := (fresh "a") in
    let mStack := (fresh "mStack") in
    let mComb := (fresh "mComb") in
    let Hany := (fresh "Hany") in
    let Hcomb := (fresh "Hcomb") in
    let Htemp := (fresh "Htemp") in
    intros a mStack mComb Hany Hcomb;
    assert (Htemp : n0 = Z.of_nat (n * Z.to_nat word_size_in_bytes)) by (cbv; auto);
    destruct (alloc_anybytes_Bignum n0 _ a mComb mpre mStack Htemp Hcomb Hany Hprec); clear Htemp Hprec Hany
  | _ => idtac
  end.

Ltac straightline_stackalloc_Bignum := try (alloc_Bignum); straightline.

(*Lemmas for Montgomery arithmetic*)
Lemma valid_toZ_wordofZ_three_b_mont : valid (toZ (List.map (@word.of_Z bw _) three_b_mont)).
Proof.
  simpl. repeat rewrite Zmod_small; [apply three_b_mont_valid|..]; split; lia.
Qed.

Lemma montadd_to_Mp x y z (Hx : valid' m bw n x) (Hy : valid' m bw n y) (Hz : valid' m bw n z) :
  montadd z x y -> (enc_mont BLS12Curve_G1.m bw n z Hz)
    = mont_add (enc_mont BLS12Curve_G1.m bw n x Hx) (enc_mont BLS12Curve_G1.m bw n y Hy).
Proof.
  intros; apply eval_from_mont_inj; rewrite !mont_enc_val; rewrite mont_add_spec;
  rewrite evfrom_mod; [| apply valid_valid'_equiv]; auto.
Qed.

Lemma montsub_to_Mp x y z (Hx : valid' m bw n x) (Hy : valid' m bw n y) (Hz : valid' m bw n z) :
montsub z x y -> (enc_mont BLS12Curve_G1.m bw n z Hz)
  = mont_sub (enc_mont BLS12Curve_G1.m bw n x Hx) (enc_mont BLS12Curve_G1.m bw n y Hy).
Proof.
intros; apply eval_from_mont_inj; rewrite !mont_enc_val; rewrite mont_sub_spec;
rewrite evfrom_mod; [| apply valid_valid'_equiv]; auto.
Qed.

Lemma montmul_to_Mp x y z (Hx : valid' m bw n x) (Hy : valid' m bw n y) (Hz : valid' m bw n z) :
montmul z x y -> (enc_mont BLS12Curve_G1.m bw n z Hz)
  = mont_mul (enc_mont BLS12Curve_G1.m bw n x Hx) (enc_mont BLS12Curve_G1.m bw n y Hy).
Proof.
intros; apply eval_from_mont_inj; rewrite !mont_enc_val; rewrite mont_mul_spec;
rewrite evfrom_mod; [| apply valid_valid'_equiv]; auto.
Qed.

Ltac assert_valid' x H' := let H := (fresh "Hvalid") in
assert (H : MontgomeryRingTheory.valid' BLS12Curve_G1.m bw n (toZ x)) by (apply H'; assumption).

Local Notation valid' := (valid' m bw n).

Ltac assertvalid' x H :=
  tryif (assert (H : valid' x) by assumption; clear H) then idtac else (assert (H : valid' x) by (apply valid_valid'_equiv; assumption)).

Lemma three_b_mont_rewrite (H : valid'  (toZ (map wordof_Z three_b_mont))) : ((MontgomeryCurveSpecs.three_b_mont m bw n r' m' three_b
three_b_small r'_correct m'_correct bw_big n_nz m_small m_big) = {| val := toZ (map wordof_Z three_b_mont); Hvalid := H |}).
Proof.
  apply mont_enc_irr. rewrite !mont_enc_val. rewrite (toZ_ofZ_eq three_b_mont three_b_mont_valid).
  cbv [MontgomeryCurveSpecs.three_b_mont]. rewrite mont_enc_val.
  rewrite three_b_mont_correct. reflexivity.
Qed.

(*To use return values of callees*)
Ltac this_mod' x :=
  lazymatch goal with
  | H1 : montsub x ?y ?z |- _ => let Htemp := (fresh "Htemp") in let Htemp' := (fresh "Htemp") in
  assertvalid' y Htemp;
  assertvalid' z Htemp';
  lazymatch goal with | Hy : valid' y |- _ => lazymatch goal with Hz : valid' z |- _ =>
  rewrite (montsub_to_Mp y z x Hy Hz) end end; [| apply H1]; try (this_mod' y); try (this_mod' z)
  | H1 : montadd x ?y ?z |- _ => let Htemp := (fresh "Htemp") in let Htemp' := (fresh "Htemp") in
  assertvalid' y Htemp;
  assertvalid' z Htemp';
  lazymatch goal with | Hy : valid' y |- _ => lazymatch goal with Hz : valid' z |- _ =>
  rewrite (montadd_to_Mp y z x Hy Hz) end end; [| apply H1]; try (this_mod' y); try (this_mod' z)
  | H1 : montmul x ?y ?z |- _ => let Htemp := (fresh "Htemp") in let Htemp' := (fresh "Htemp") in
  assertvalid' y Htemp;
  assertvalid' z Htemp';
  lazymatch goal with | Hy : valid' y |- _ => lazymatch goal with Hz : valid' z |- _ =>
  rewrite (montmul_to_Mp y z x Hy Hz) end end; [| apply H1]; try (this_mod' y); try (this_mod' z)
  | _ => idtac
  end.
  
Ltac remember_mont x := lazymatch goal with
| H1 : valid' x |- _ => let p := (fresh "p") in
  remember {| val := x; Hvalid := H1 |} as p
end.

(*For function calls*)
Ltac next_call :=
  lazymatch goal with
    | [H' : (_ * _)%sep _ |- _] =>
      straightline_call; [| ecancel_assumption| ecancel_assumption| ecancel_assumption| ]; [eauto| ]; repeat straightline'; clear H'; repeat clear_emps_step
    end.

(*For undoing memory fragmentation done by stack allocation*)
Ltac defrag_in_context := lazymatch goal with
| [
    |- exists (_ _ : @Interface.map.rep _ _ _),
      (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
      repeat match goal with 
      | [ H : (?Rl * ((Bignum _ addr ?aval) * ?Rr))%sep mem |- _ ] => 
        let Ha := (fresh "Ha") in
        let m := fresh "m" in
        let Htemp := fresh "Htemp" in
        let Htemp' := fresh "Htemp'" in
        let mStack := fresh "mStack" in
        assert (Ha : ((Bignum n addr aval) * (Rl * Rr))%sep mem) by ecancel_assumption; clear H;
        destruct Ha as [mStack [m [ Htemp [Htemp' ]]]];
        exists m; exists mStack; split; [ eapply Bignum_anybytes; [|eassumption]; cbv; reflexivity | split; [apply Properties.map.split_comm; auto| clear Htemp Htemp']]
      | [ H : (((Bignum _ addr ?aval) * ?Rr))%sep mem |- _ ] => 
        let Ha := (fresh "Ha") in
        let m := fresh "m" in
        let mStack := fresh "mStack" in
        assert (Ha : ((Bignum n addr aval) * (Rr))%sep mem) by ecancel_assumption; clear H;
        destruct Ha as [mStack [m [Htemp [Htemp' ]]]];
        exists m; exists mStack; split; [ eapply Bignum_anybytes; [|eassumption]; cbv; reflexivity | split; [apply Properties.map.split_comm; auto| clear Ha]]
          
      | [ H : _ mem |- _ ] => apply (sep_assoc_proj2 mem) in H
      end
end.
        
Ltac defrag_in_context' := lazymatch goal with
| [ |- exists (_ _ : @Interface.map.rep _ _ _),
      (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
      match goal with 
      | [ H : _ mem |- _ ] => cleanup_hyp H mem
      end
    end; defrag_in_context.

Theorem G1_add_func_ok : program_logic_goal_for_function! BLS12_add.
Proof.
  repeat straightline_stackalloc_Bignum.
  (*initialize proof*)
  
  (* clear H33 Hmnew Hmnew0 Hmnew1 Hmnew2 Hmnew3 Hmnew4. *)
  repeat straightline'.
  
  (*Unfolding Bignum-notation in order to store constant into newly allocated memory*)
  Bignum_to_Scalars x. clear H39.

  (*Store values*)
  handle_store.
  
  (*Rephrase hypothesis in terms of Bignum again*)
  eassert ( (Bignum n a (List.map wordof_Z three_b_mont) * _)%sep _).
  {
    unfold Bignum. sepsimpl; [ cbv; auto|]. unfold array. cbv [three_b_mont map].
    repeat rewrite (word_add_comm _ (word.of_Z word_size_in_bytes)).
    repeat (rewrite next_word' in H45; try rewrite word_add_0 in H45).
    ecancel_assumption.
  }

  clear H45 H33.

  (*Must be in context to automate function calls*)
  pose proof valid_toZ_wordofZ_three_b_mont as H3b.

  (*Handle function calls.*)
  repeat next_call.

  (*Rephrase as single separation hypothesis in context*)
  repeat defrag_in_context'.
  repeat straightline.

  (*Postcondition*)

  (*First, trivial subgoals are handled.*)
  split; [reflexivity| ]. split; [reflexivity| ].
  do 4 eexists.
  split; [| ecancel_assumption].
  split; [| auto].

  (*Gallina specification part of postcondition*)
  unfold BLS12_add_Gallina_spec.

  (*Inputs/Outputs are valid elements of Mp*)
  pose proof (valid_valid'_equiv).
  assert_valid' wX1 H105.
  assert_valid' wX2 H105.
  assert_valid' wY1 H105.
  assert_valid' wY2 H105.
  assert_valid' wZ1 H105.
  assert_valid' wZ2 H105.
  assert_valid' x28 H105.
  assert_valid' x25 H105.
  assert_valid' x31 H105.

  (*Use alternative curve spec for a = 0*)
  destruct (MontgomeryCurveSpecs.BLS12_add_specs_equiv' m bw n r' m' (BLS12Curve_G1.a) three_b a_small three_b_small r'_correct m'_correct bw_big n_nz m_small m_big _ _ _ _ _ _ _ _ _ Hvalid Hvalid0 Hvalid1 Hvalid2 Hvalid3 Hvalid4 Hvalid5 Hvalid6 Hvalid7) as [Heq _].
  apply Heq; clear Heq.

  (*Use return values from function calls*)
  this_mod' (toZ x28).
  this_mod' (toZ x25).
  this_mod' (toZ x31).

  unfold BLS12_add_mont_spec.

  (*alias each Mp ring element to help ring tactic*)
  rewrite <- three_b_mont_rewrite.
  rewrite a_mont_zero.

  remember_mont (toZ wX1).
  remember_mont (toZ wX2).
  remember_mont (toZ wY1).
  remember_mont (toZ wY2).
  remember_mont (toZ wZ1).
  remember_mont (toZ wZ2).
  remember (MontgomeryCurveSpecs.three_b_mont BLS12Curve_G1.m bw n r' m'
  three_b three_b_small r'_correct m'_correct bw_big n_nz
  m_small m_big) as pnew.

  (*Equality of each coordinate is solved by ring tactic*)
  apply pair_equal_spec; split; [apply pair_equal_spec; split; ring| ring].
Qed.

(*Version that allows overlapping inputs/outputs. *)

  (*Bedrock2 Function Definition*)
Definition BLS12_add_alt : Syntax.func :=
    let outx := "outx" in
    let outy := "outy" in
    let outz := "outz" in

    let X1 := "X1" in
    let Y1 := "Y1" in
    let Z1 := "Z1" in

    let X2 := "X2" in
    let Y2 := "Y2" in
    let Z2 := "Z2" in

    let X1sep := "X1sep" in
    let Y1sep := "Y1sep" in
    let Z1sep := "Z1sep" in

    let X2sep := "X2sep" in
    let Y2sep := "Y2sep" in
    let Z2sep := "Z2sep" in

    let BLS12_add := "BLS12_add" in  
    let felem_copy := ("felem_copy" ++ felem_suffix) in  
    ("BLS12_add_alt", (
      [outx; outy; outz; X1; Y1; Z1; X2; Y2; Z2], [],
      bedrock_func_body:(

      stackalloc num_bytes as X1sep {
      stackalloc num_bytes as Y1sep {
      stackalloc num_bytes as Z1sep {
      stackalloc num_bytes as X2sep {
      stackalloc num_bytes as Y2sep {
      stackalloc num_bytes as Z2sep {
        
          (*copying X1*)
          felem_copy(X1sep, X1);
          felem_copy(Y1sep, Y1);
          felem_copy(Z1sep, Z1);
          felem_copy(X2sep, X2);
          felem_copy(Y2sep, Y2);
          felem_copy(Z2sep, Z2);

          BLS12_add (outx, outy, outz, X1sep, Y1sep, Z1sep, X2sep, Y2sep, Z2sep)
        }}}}}}
      )
    )).

(*Bedrock2 function Spec*)

Instance spec_of_BLS12_add_alt: spec_of BLS12_add_alt :=
fun functions : list (string * (list string * list string * cmd)) =>
    forall (wX1 wY1 wZ1 wX2 wY2 wZ2 : list Interface.word.rep)
    (pX1 pY1 pZ1 pX2 pY2 pZ2  poutx pouty poutz: Interface.word.rep)
    (wold_outx wold_outy wold_outz: list Interface.word.rep) (t : Semantics.trace)
    (m0 : @Interface.map.rep (@word.rep (@width (@semantics default_parameters))
    (@word (@semantics default_parameters))) Init.Byte.byte (@mem (@semantics default_parameters))) (RX1 RY1 RZ1 RX2 RY2 RZ2 Rout : (@Interface.map.rep (@word.rep (@width (@semantics default_parameters))
    (@word (@semantics default_parameters))) Init.Byte.byte (@mem (@semantics default_parameters))) -> Prop),
    valid (List.map Interface.word.unsigned wX1) /\
    valid (List.map Interface.word.unsigned wY1) /\
    valid (List.map Interface.word.unsigned wZ1) /\
    valid (List.map Interface.word.unsigned wX2) /\
    valid (List.map Interface.word.unsigned wY2) /\
    valid (List.map Interface.word.unsigned wZ2) ->
    (Bignum n pX1 wX1 * RX1)%sep m0 ->
    (Bignum n pX2 wX2 * RX2)%sep m0 ->
    (Bignum n pY1 wY1 * RY1)%sep m0 ->
    (Bignum n pY2 wY2 * RY2)%sep m0 ->
    (Bignum n pZ1 wZ1 * RZ1)%sep m0 ->
    (Bignum n pZ2 wZ2 * RZ2)%sep m0 ->
    ((Bignum n poutx wold_outx) * (Bignum n pouty wold_outy) * (Bignum n poutz wold_outz))%sep m0 ->
    WeakestPrecondition.call functions ( "BLS12_add_alt") t m0
    ([poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutx wouty woutz : list Interface.word.rep) Rout,
        (
                (BLS12_add_Gallina_spec (toZ wX1) (toZ wY1) (toZ wZ1) (toZ wX2) (toZ wY2) 
                (toZ wZ2) (toZ woutx) (toZ wouty) (toZ woutz)/\
                valid (List.map Interface.word.unsigned woutx) /\
                valid (List.map Interface.word.unsigned wouty) /\
                valid (List.map Interface.word.unsigned woutz)) /\
             ((Bignum n poutx woutx) * (Bignum n pouty wouty) * (Bignum n poutz woutz) * Rout)%sep m'))).

Local Definition num_bytes_word := Eval compute in (Z.of_nat (n * Z.to_nat word_size_in_bytes)).

Lemma numbytes_correct : num_bytes_word = (Z.of_nat (n * Z.to_nat word_size_in_bytes)).
Proof. auto. Qed.

Ltac straightline'' :=
lazymatch goal with
| [Hminit : ?mcond (?minit)
    |- forall (_ : @word.rep _ _)
              (_ _ : @Interface.map.rep _ _ _),
        anybytes _ ?numbytes _ -> msplit _ ?minit _ -> _ ] => 
    let a := (fresh "a") in
    let mStack := (fresh "mStack") in
    let mnew := (fresh "mnew") in
    let Hany := (fresh "Hany") in
    let HanyBignum := (fresh "HanyBignum") in
    let anyval := (fresh "anyval") in
    let Hsplit := (fresh "Hsplit") in
    let Hmnew := (fresh "Hmnew") in
    let R := (fresh "R") in
    intros a mStack mnew Hany Hsplit; destruct (anybytes_Bignum n mStack numbytes a numbytes_correct Hany) as [anyval HanyBignum];
    destruct (alloc_seps_alt mnew minit mStack mcond (Bignum _ _ _) Hsplit (empty_frame mcond minit Hminit) (empty_frame (Bignum _ _ _) mStack HanyBignum)) as [R Hmnew];
    clear Hany Hsplit HanyBignum
| _ => straightline
end.

Theorem G1_add_alt_func_ok : program_logic_goal_for_function! BLS12_add_alt.
Proof.
  do 9 straightline''.

  (*Assert single hypothesis for stackallocation.*)
  remember (Bignum n pX1 wX1 * RX1)%sep as RX1'.
  remember (Bignum n pY1 wY1 * RY1)%sep as RY1'.
  remember (Bignum n pZ1 wZ1 * RZ1)%sep as RZ1'.
  remember (Bignum n pX2 wX2 * RX2)%sep as RX2'.
  remember (Bignum n pY2 wY2 * RY2)%sep as RY2'.
  remember (Bignum n pZ2 wZ2 * RZ2)%sep as RZ2'.
  remember ((Bignum n poutx wold_outx * Bignum n pouty wold_outy *
  Bignum n poutz wold_outz)%sep) as Rout'.

  assert (
      id (fun m => (RX1' m /\ RY1' m /\ RZ1' m /\ RX2' m /\ RY2' m /\ RZ2' m /\ Rout' m)) m0).
  {
    cbv [id]. split; auto. repeat (split; auto); auto.
  }


  (*Allocate memory on stack. *)
   repeat straightline''. clear H1 Hmnew Hmnew0 Hmnew1 Hmnew2 Hmnew3.
   repeat straightline''. cbv [id] in *.

  (*Handle calls to felem_copy*)
   Ltac copy_next R fR thism pX1 wX1 RX1 a H := straightline_call; [subst R; remember fR as thisP;
   eassert (thisH : ((fun m => (Bignum n pX1 wX1 * RX1)%sep m /\ thisP m) * Bignum n a _ * _)%sep thism) by (subst thisP; ecancel_assumption); subst thisP; apply thisH |]; clear H; repeat straightline.

   copy_next RX1' (fun m => RY1' m /\ RZ1' m /\ RX2' m /\ RY2' m /\ RZ2' m /\ Rout' m) mnew4 pX1 wX1 RX1 a Hmnew4.
   copy_next RY1' (fun m => RZ1' m /\ RX2' m /\ RY2' m /\ RZ2' m /\ Rout' m) a6 pY1 wY1 RY1 a0 H21.
   copy_next RZ1' (fun m => RX2' m /\ RY2' m /\ RZ2' m /\ Rout' m) a8 pZ1 wZ1 RZ1 a1 H21.
   copy_next RX2' (fun m => RY2' m /\ RZ2' m /\ Rout' m) a6 pX2 wX2 RX2 a2 H21.
   copy_next RY2' (fun m => RZ2' m /\ Rout' m) a8 pY2 wY2 RY2 a3 H21.
   copy_next RZ2' (fun m => Rout' m) a6 pZ2 wZ2 RZ2 a4 H21. 

  (*Handle function call*)
  repeat straightline.
  straightline_call.
  2: {
    assert (Hnumlimbs : n = num_limbs) by auto.
    repeat rewrite Hnumlimbs. repeat rewrite Hnumlimbs in H21. ecancel_assumption.
  }
  1: split; auto.

  (*Defragment memory in context after stack allocation. *)
  repeat straightline.
  repeat Tactics.defrag_in_context (WordByWordMontgomery.n BLS12Curve_G1.m (@width semantics)).
  repeat straightline.

  (*Postcondition*)
  do 2 split; auto.
  do 4 eexists. split.
  2: ecancel_assumption.
  split; auto.
Qed.

(* From bedrock2 Require Import ToCString Bytedump.
Definition bls12_c_add :=
  c_module (add :: nil).
  Definition bls12_c_mul :=
  c_module (mul :: nil).
  Definition bls12_c_sub :=
  c_module (sub :: nil).
  Definition G1_add :=
  c_module (BLS12_add :: nil).
  Definition G1_add_alt :=
    c_module (BLS12_add_alt :: nil).
    Definition G1_felem_copy :=
      c_module (felem_copy :: nil).
  Eval compute in G1_felem_copy. *)
