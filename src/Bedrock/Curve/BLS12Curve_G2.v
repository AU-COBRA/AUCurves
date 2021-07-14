Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery. 
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Coq.Lists.List.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.Syntax.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import bedrock2.Semantics.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.ReifiedOperation.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Spec.MxDH.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Translation.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import Bedrock.Field.bls12prime.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Bedrock.Field.quadratic_extension_bls12.
Require Import Implementations.SOS.SOSReduction.
Require Import coqutil.Map.Properties.
Require Import bedrock2.Lift1Prop.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Require Import Bedrock.Util.Util.
Require Import MontgomeryCurveSpecs.
Require Import Bedrock.Util.Tactics.
Require Import Bedrock.Util.Bignum.
Require Import Bedrock.Util.Word.
Import Syntax.Coercions.
Local Open Scope string_scope.
Import ListNotations.
Local Open Scope Z_scope.

Section Spec.

(*Parameters to be changed: specify prime and import reification from cache.*)
    Require Import Bedrock.Examples.felem_copy_64.
    Local Definition felem_suffix := felem_copy_64.aff.
    Local Notation m := bls12prime.m.
    Local Definition prefix := "bls12_"%string. (* placed before function names *)
    Local Notation ar := (0 mod m).
    Local Notation ai := (0 mod m).
    Local Notation br := (4 mod m).
    Local Notation bi := (4 mod m).
 
    Existing Instances Defaults64.default_parameters bls12_bedrock2_funcs
    bls12_bedrock2_specs bls12_bedrock2_correctness.

    Existing Instance spec_of_my_add_alt2.
    Existing Instance spec_of_my_sub_alt2.
    Existing Instance spec_of_my_mul_alt2.

    Instance spec_of_reified_Fp2_mul :
    spec_of (append prefix "Fp2_mul") := spec_of_my_mul_alt2.
    Instance spec_of_reified_Fp2_add :
    spec_of (append prefix "Fp2_add") := spec_of_my_add_alt2.
    Instance spec_of_reified_Fp2_sub :
    spec_of (append prefix "Fp2_sub") := spec_of_my_sub_alt2.

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
  Local Notation bw := (@width (semantics)).
  Local Notation m' := (@WordByWordMontgomery.m' m bw).
  Notation n := (WordByWordMontgomery.n m bw).
  Local Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
  Local Notation valid := (@WordByWordMontgomery.valid bw n m).
  Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation to_mont := (@WordByWordMontgomery.to_montgomerymod bw n m m').
  Local Notation thisword := (@word semantics).
  Local Definition valid_words w := valid (List.map (@Interface.word.unsigned width thisword) w).
  Local Definition map_words := List.map (@Interface.word.unsigned width thisword).
  Local Notation r := (WordByWordMontgomery.r bw).
  Local Notation r' := (WordByWordMontgomery.r' m bw).
  Local Definition num_bytes := Eval compute in (Z.of_nat (((Z.to_nat bw * n) / 8)%nat)).
  Local Notation three_br := (3 * br mod m).
  Local Notation three_bi := (3 * bi mod m).
  Local Notation uw := (uweight 64).
  Definition three_br_list := (Partition.partition uw 6 (three_br)).
  Definition three_br_mont := Eval native_compute in (WordByWordMontgomery.to_montgomerymod bw n m m' three_br_list).
  Definition three_bi_list := (Partition.partition uw 6 three_bi).
  Definition three_bi_mont := Eval native_compute in (WordByWordMontgomery.to_montgomerymod bw n m m' three_bi_list).

  (*Some Notation*)
  Local Notation evfrom x := ((eval (from_mont (fst x)), eval (from_mont (snd x)))).
  Local Notation toZ x := (List.map Interface.word.unsigned x).

  Local Infix "*p2" := (mulp2 m) (at level 80).
  Local Infix "+p2" := (addp2 m) (at level 90).
  Local Infix "-p2" := (subp2 m) (at level 90).

  Local Notation evfrom_mod' := (@evfrom_mod'  m width n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
  Notation mod_pair x := ((fst x) mod m, (snd x) mod m).
  Definition small x := 0 <= x < m.
  Notation valid_pair x := ((valid (fst x)) /\ (valid (snd x))).
  Notation small_pair x := ((small (fst x)) /\ (small (snd x))).

  Local Infix "+Fp" := (montFp2_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 190).
  Local Infix "*Fp" := (montFp2_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 200).
  Local Infix "-Fp" := (montFp2_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 200).

  Notation S aw := (word.add (word.of_Z word_size_in_bytes) aw).

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

  (*Lemmas of correctness of parameters to be used for montgomery arithmetic.*)
  Lemma r'_correct : (2 ^ bw * r') mod Spec.m = 1.
  Proof. auto with zarith. Qed.

  Lemma m'_correct : (Spec.m * m') mod 2 ^ bw = -1 mod 2 ^ bw.
  Proof. auto with zarith. Qed.

  Lemma bw_big : 0 < bw.
  Proof. unfold bw; simpl; lia. Qed.

  Lemma m_big : 1 < Spec.m.
  Proof. unfold m; lia. Qed.

  Lemma n_nz : n <> 0%nat.
  Proof. unfold n; simpl; auto with zarith. Qed.

  Lemma m_small : Spec.m < (2 ^ bw) ^ Z.of_nat n.
  Proof. unfold n, m; simpl; auto with zarith. Qed.

  Ltac wbw_conds :=
    repeat first [ progress apply r'_correct
                | progress apply m'_correct
                | progress apply bw_big
                | progress apply m_big
                | progress apply n_nz
                | progress apply m_small
                | progress apply m'_correct
                | progress apply m'_correct ].

  Lemma n_small : Z.of_nat n < 2 ^ bw.
  Proof. cbv. auto. Qed.

  Add Ring Mp2 : (montFp2_ring' m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).

  Local Notation toZ_ofZ_eq := (toZ_ofZ_eq n n_nz n_small m).
  Local Notation from_mont_correct := (@from_mont_correct m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
  Local Notation to_mont_correct := (@to_mont_correct m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
  Local Notation from_to_mont_inv := (@from_to_mont_inv m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
  Local Notation valid_mod := (valid_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
  Local Notation mont_add := (mont_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation mont_sub := (mont_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation mont_mul := (mont_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation valid_valid'_equiv := (valid_valid'_equiv m bw n n_nz m_big).
  Local Notation evfrom_mod := (evfrom_mod' m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation eval_from_mont_inj := (eval_from_mont_inj m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation mont_zero := (mont_zero m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation wordof_Z := (@word.of_Z width (@word (@semantics Defaults64.default_parameters))).


  (*Lemmas/Tactics for parameters a and b*)
  Lemma three_br_mont_correct : three_br_mont = (WordByWordMontgomery.to_montgomerymod bw n m m' three_br_list).
  Proof.
    (vm_compute (WordByWordMontgomery.to_montgomerymod bw n m m' three_br_list)); reflexivity.
  Qed.

  Lemma three_br_valid: valid three_br_list.
  Proof.
    split; [cbv; auto| split; cbv; auto; intros; discriminate].
  Qed.

  Lemma three_br_mont_valid : valid three_br_mont.
  Proof.
    split; [cbv; auto| split; cbv; auto; intros; discriminate].
  Qed.

  Lemma three_bi_mont_correct : three_bi_mont = (WordByWordMontgomery.to_montgomerymod bw n m m' three_bi_list).
  Proof.
    (vm_compute (WordByWordMontgomery.to_montgomerymod bw n m m' three_bi_list)); reflexivity.
  Qed.

  Lemma three_bi_valid: valid three_bi_list.
  Proof.
    split; [cbv; auto| split; cbv; auto; intros; discriminate].
  Qed.

  Lemma three_bi_mont_valid : valid three_bi_mont.
  Proof.
    split; [cbv; auto| split; cbv; auto; intros; discriminate].
  Qed.

  Lemma valid_toZ_wordofZ_three_br_mont : valid (toZ (map wordof_Z three_br_mont)).
  Proof.
    rewrite toZ_ofZ_eq; apply three_br_mont_valid.
  Qed.

  Lemma valid_toZ_wordofZ_three_bi_mont : valid (toZ (map wordof_Z three_bi_mont)).
  Proof.
    rewrite toZ_ofZ_eq; apply three_bi_mont_valid.
  Qed.

  Lemma ai_small : ai mod m = ai.
  Proof. cbv; auto. Qed.

  Lemma ar_small : ar mod m = ar.
  Proof. cbv; auto. Qed.

  Lemma three_br_small : three_br = three_br mod m.
  Proof. cbv. auto. Qed.

  Lemma three_bi_small : three_bi = three_bi mod m.
  Proof. cbv. auto. Qed.

  Lemma remember_three_b H : ((enc_mont_pair m bw n (toZ (map wordof_Z three_br_mont), toZ (map wordof_Z three_bi_mont)) H)
    = (three_bp2 m bw n r' m' three_bi three_bi three_br_small three_bi_small r'_correct m'_correct bw_big n_nz m_small m_big)).
  Proof.
    apply pair_equal_spec; split; apply mont_enc_irr; rewrite mont_enc_val; [rewrite Prod.fst_pair| rewrite Prod.snd_pair];
    rewrite toZ_ofZ_eq; [unfold MontgomeryCurveSpecs.three_br_mont|apply three_br_mont_valid| unfold MontgomeryCurveSpecs.three_bi_mont |apply three_bi_mont_valid];
    rewrite mont_enc_val; [unfold three_br_mont_list; rewrite three_br_mont_correct| unfold three_bi_mont_list; rewrite three_bi_mont_correct];
    apply (f_equal (fun y => to_mont y)); cbv; auto.
  Qed.

  Local Notation Mp2_O := (MontgomeryRingTheory.montFp2_zero m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).

  Lemma remember_ap2 : (((ap2 m bw n r' m' 0 0 ar_small ai_small r'_correct m'_correct bw_big n_nz m_small m_big) = Mp2_O)).
  Proof.
    apply pair_equal_spec; split; unfold ar_mont, ai_mont; apply mont_enc_irr;
    rewrite !mont_enc_val; unfold ar_mont_list, ai_mont_list; unfold mont_zero;
    rewrite mont_enc_val; unfold ar_list, ai_list; apply (f_equal (fun y => to_mont y)); cbv; auto.
  Qed.
  
  (*Gallina specs
    Note that we use 2 different specs; one is more general and proven correct in Fiats library.
    The other is correct only when the parameter a is 0; which is the case here.
    Their equivalence is shown below.*)
  Definition BLS12_add_Gallina_spec X1r X1i Y1r Y1i Z1r Z1i X2r X2i Y2r Y2i Z2r Z2i outxr outxi outyr outyi outzr outzi :=
    @BLS12_G2_add_Gallina_spec m bw n m' 0 0 three_br three_bi (X1r, X1i) (Y1r, Y1i) (Z1r, Z1i) (X2r, X2i) (Y2r, Y2i) (Z2r, Z2i) (outxr, outxi) (outyr, outyi) (outzr, outzi).

  (*Bedrock2 Function Definition*)
  Definition BLS12_add : Syntax.func :=
      let outxr := "outxr" in
      let outyr := "outyr" in
      let outzr := "outzr" in

      let X1r := "X1r" in
      let Y1r := "Y1r" in
      let Z1r := "Z1r" in

      let X2r := "X2r" in
      let Y2r := "Y2r" in
      let Z2r := "Z2r" in

      let t0r := "t0r" in
      let t1r := "t1r" in
      let t2r := "t2r" in
      let t3r := "t3r" in
      let t4r := "t4r" in
      let t5r := "t5r" in
      let three_br := "three_br" in

      let outxi := "outxi" in
      let outyi := "outyi" in
      let outzi := "outzi" in

      let X1i := "X1i" in
      let Y1i := "Y1i" in
      let Z1i := "Z1i" in

      let X2i := "X2i" in
      let Y2i := "Y2i" in
      let Z2i := "Z2i" in

      let t0i := "t0i" in
      let t1i := "t1i" in
      let t2i := "t2i" in
      let t3i := "t3i" in
      let t4i := "t4i" in
      let t5i := "t5i" in
      let three_bi := "three_bi" in

      let add := ("Fp2_add_alt2") in
      let mul := ("Fp2_mul_alt2") in
      let sub := ("Fp2_sub_alt2") in  
      ("BLS12_G2_add", (
        [outxr; outxi; outyr; outyi; outzr; outzi; X1r; X1i; Y1r; Y1i; Z1r; Z1i; X2r; X2i; Y2r; Y2i; Z2r; Z2i], [],
        bedrock_func_body:(
        stackalloc num_bytes as three_br{
          stackalloc num_bytes as t0r {
            stackalloc num_bytes as t1r {
              stackalloc num_bytes as t2r {
                stackalloc num_bytes as t3r {
                  stackalloc num_bytes as t4r {
                    stackalloc num_bytes as t5r {
                      stackalloc num_bytes as three_bi{
                        stackalloc num_bytes as t0i {
                          stackalloc num_bytes as t1i {
                            stackalloc num_bytes as t2i {
                              stackalloc num_bytes as t3i {
                                stackalloc num_bytes as t4i {
                                  stackalloc num_bytes as t5i {
                                    store(three_br, (coq:(nth 0 three_br_mont 0)));
                                    store(three_br + coq:(8), coq:(nth 1 three_br_mont 0));
                                    store(three_br + coq:(16), coq:(nth 2 three_br_mont 0));
                                    store(three_br + coq:(24), coq:(nth 3 three_br_mont 0));
                                    store(three_br + coq:(32), coq:(nth 4 three_br_mont 0));
                                    store(three_br + coq:(40), coq:(nth 5 three_br_mont 0));
                                    store(three_bi, (coq:(nth 0 three_bi_mont 0)));
                                    store(three_bi + coq:(8), coq:(nth 1 three_bi_mont 0));
                                    store(three_bi + coq:(16), coq:(nth 2 three_bi_mont 0));
                                    store(three_bi + coq:(24), coq:(nth 3 three_bi_mont 0));
                                    store(three_bi + coq:(32), coq:(nth 4 three_bi_mont 0));
                                    store(three_bi + coq:(40), coq:(nth 5 three_bi_mont 0));
                                    mul (t0r, t0i, X1r, X1i, X2r, X2i);
                                    mul (t1r, t1i, Y1r, Y1i, Y2r, Y2i);
                                    mul (t2r, t2i, Z1r, Z1i, Z2r, Z2i);
                                    add (t3r, t3i, X1r, X1i, Y1r, Y1i);
                                    add (t4r, t4i, X2r, X2i, Y2r, Y2i);
                                    mul (t3r, t3i, t3r, t3i, t4r, t4i);
                                    add (t4r, t4i, t0r, t0i, t1r, t1i);
                                    sub (t3r, t3i, t3r, t3i, t4r, t4i);
                                    add (t4r, t4i, X1r, X1i, Z1r, Z1i);
                                    add (t5r, t5i, X2r, X2i, Z2r, Z2i);
                                    mul (t4r, t4i, t4r, t4i, t5r, t5i);
                                    add (t5r, t5i, t0r, t0i, t2r, t2i);
                                    sub (t4r, t4i, t4r, t4i, t5r, t5i);
                                    add (t5r, t5i, Y1r, Y1i, Z1r, Z1i);
                                    add (outxr, outxi, Y2r, Y2i, Z2r, Z2i);
                                    mul (t5r, t5i, t5r, t5i, outxr, outxi);
                                    add (outxr, outxi, t1r, t1i, t2r, t2i);
                                    sub (t5r, t5i, t5r, t5i, outxr, outxi);
                                    mul (outzr, outzi, three_br, three_bi, t2r, t2i);
                                    sub (outxr, outxi, t1r, t1i, outzr, outzi);
                                    add (outzr, outzi, outzr, outzi, t1r, t1i);
                                    mul (outyr, outyi, outxr, outxi, outzr, outzi);
                                    add (t1r, t1i, t0r, t0i, t0r, t0i);
                                    add (t1r, t1i, t1r, t1i, t0r, t0i);
                                    mul (t4r, t4i, three_br, three_bi, t4r, t4i);
                                    mul (t0r, t0i, t1r, t1i, t4r, t4i);
                                    add (outyr, outyi, outyr, outyi, t0r, t0i);
                                    mul (t0r, t0i, t5r, t5i, t4r, t4i);
                                    mul (outxr, outxi, t3r, t3i, outxr, outxi);
                                    sub (outxr, outxi, outxr, outxi, t0r, t0i);
                                    mul (t0r, t0i, t3r, t3i, t1r, t1i);
                                    mul (outzr, outzi, t5r, t5i, outzr, outzi);
                                    add (outzr, outzi, outzr, outzi, t0r, t0i)
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
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

  (*Bedrock2 function Spec*)
  Instance spec_of_BLS12_add: spec_of BLS12_add :=
  fun functions : list (string * (list string * list string * cmd)) =>
      forall (wX1r wY1r wZ1r wX2r wY2r wZ2r wX1i wY1i wZ1i wX2i wY2i wZ2i : list Interface.word.rep)
      (pX1r pY1r pZ1r pX2r pY2r pZ2r pX1i pY1i pZ1i pX2i pY2i pZ2i poutxr poutyr poutzr poutxi poutyi poutzi: Interface.word.rep)
      (wold_outxr wold_outyr wold_outzr wold_outxi wold_outyi wold_outzi: list Interface.word.rep) (t : Semantics.trace)
      (m0 : Interface.map.rep) (Rout : Interface.map.rep -> Prop),
      valid (List.map Interface.word.unsigned wX1r) /\
      valid (List.map Interface.word.unsigned wY1r) /\
      valid (List.map Interface.word.unsigned wZ1r) /\
      valid (List.map Interface.word.unsigned wX2r) /\
      valid (List.map Interface.word.unsigned wY2r) /\
      valid (List.map Interface.word.unsigned wZ2r) /\
      valid (List.map Interface.word.unsigned wX1i) /\
      valid (List.map Interface.word.unsigned wY1i) /\
      valid (List.map Interface.word.unsigned wZ1i) /\
      valid (List.map Interface.word.unsigned wX2i) /\
      valid (List.map Interface.word.unsigned wY2i) /\
      valid (List.map Interface.word.unsigned wZ2i) ->
      ((Bignum n pX1r wX1r) *
      (Bignum n pX2r wX2r) *
      (Bignum n pY1r wY1r) *
      (Bignum n pY2r wY2r) *
      (Bignum n pZ1r wZ1r) *
      (Bignum n pZ2r wZ2r) *
      (Bignum n pX1i wX1i) *
      (Bignum n pX2i wX2i) *
      (Bignum n pY1i wY1i) *
      (Bignum n pY2i wY2i) *
      (Bignum n pZ1i wZ1i) *
      (Bignum n pZ2i wZ2i) *
      (Bignum n poutxr wold_outxr) * (Bignum n poutyr wold_outyr) * (Bignum n poutzr wold_outzr) *
      (Bignum n poutxi wold_outxi) * (Bignum n poutyi wold_outyi) * (Bignum n poutzi wold_outzi) * Rout)%sep m0 ->
      WeakestPrecondition.call functions ( "BLS12_G2_add") t m0
      ([poutxr; poutxi; poutyr; poutyi; poutzr; poutzi; pX1r; pX1i; pY1r; pY1i; pZ1r; pZ1i; pX2r; pX2i; pY2r; pY2i; pZ2r; pZ2i])
      (fun (t' : Semantics.trace) (m' : Interface.map.rep)
          (rets : list Interface.word.rep) =>
      t = t' /\
      rets = nil /\
      (exists (woutxr woutyr woutzr woutxi woutyi woutzi: list Interface.word.rep) Rout,
          (
                  (BLS12_add_Gallina_spec (toZ wX1r) (toZ wX1i) (toZ wY1r) (toZ wY1i) (toZ wZ1r) (toZ wZ1i) (toZ wX2r)
                  (toZ wX2i) (toZ wY2r) (toZ wY2i) 
                  (toZ wZ2r) (toZ wZ2i) (toZ woutxr) (toZ woutxi) (toZ woutyr) (toZ woutyi) (toZ woutzr) (toZ woutzi) /\
              ((Bignum n pX1r wX1r) *
              (Bignum n pX2r wX2r) *
              (Bignum n pY1r wY1r) *
              (Bignum n pY2r wY2r) *
              (Bignum n pZ1r wZ1r) *
              (Bignum n pX1i wX1i) *
              (Bignum n pX2i wX2i) *
              (Bignum n pY1i wY1i) *
              (Bignum n pY2i wY2i) *
              (Bignum n pZ1i wZ1i) *
              (Bignum n pZ2r wZ2r) *
              (Bignum n pZ2i wZ2i) *
              (Bignum n poutxr woutxr) * (Bignum n poutyr woutyr) * (Bignum n poutzr woutzr) *
              (Bignum n poutxi woutxi) * (Bignum n poutyi woutyi) * (Bignum n poutzi woutzi) * Rout)%sep m')))).

  (*Lemmas/Tactics for handling Bignum/Scalar/many_Scalars*)
  Notation msplit := Interface.map.split.

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

  Ltac straightline' :=
    match goal with
    | [Hminit : ?mcond (?minit : @Interface.map.rep _ _ _)
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
        intros a mStack mnew Hany Hsplit; destruct (anybytes_Bignum mStack a Hany) as [anyval HanyBignum];
        destruct (alloc_seps_alt mnew minit mStack mcond (Bignum _ _ _) Hsplit (empty_frame mcond minit Hminit) (empty_frame (Bignum _ _ _) mStack HanyBignum)) as [R Hmnew];
        clear Hany Hsplit HanyBignum
    | _ => straightline
    end.

    
  (*Tactics to handle stores*)
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


  (*Tactic for function calls*)
  Ltac next_call :=
    lazymatch goal with
      | [H' : (_ * _)%sep _ |- _] =>
      straightline_call; [|ecancel_assumption | ecancel_assumption| ecancel_assumption| ecancel_assumption| ecancel_assumption|]; [split; [assumption| split; [assumption| split; assumption]]|]; repeat straightline; clear H'
      | _ => idtac
        end.


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


  (*Lemmas and tactics casting return values from function calls to Mp2 elements*)
  Lemma montmul_to_Mp2 : forall x y z Hx Hy Hz, Fp2_mul_Gallina_spec x y z -> enc_mont_pair m bw n z Hz = montFp2_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big 
  (enc_mont_pair m bw n x Hx) (enc_mont_pair m bw n y Hy).
  Proof.
    intros [pr pi] [yr yi] [zr zi] Hx Hy Hz [_ [_ [H'1 H'2]]].
    apply pair_equal_spec; split; apply eval_from_mont_inj.
      - rewrite mont_enc_val. rewrite Prod.fst_pair. rewrite Prod.fst_pair in H'1.
        rewrite H'1. rewrite !Prod.fst_pair, !Prod.snd_pair.
        pose proof (mont_sub_spec m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
        rewrite H. rewrite !mont_mul_spec.
        assert (Htempfst : forall y z H, val m bw n (fst (enc_mont_pair m bw n (y, z) H)) = y) by reflexivity.
        assert (Htempsnd : forall y z H, val m bw n (snd (enc_mont_pair m bw n (y, z) H)) = z) by reflexivity.
        rewrite !Htempfst, !Htempsnd. apply Zminus_mod.
      - rewrite mont_enc_val. rewrite Prod.snd_pair. rewrite Prod.snd_pair in H'2.
        rewrite H'2. rewrite !Prod.fst_pair, !Prod.snd_pair.
        pose proof (mont_add_spec m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
        rewrite H. rewrite !mont_mul_spec.
        assert (Htempfst : forall y z H, val m bw n (fst (enc_mont_pair m bw n (y, z) H)) = y) by reflexivity.
        assert (Htempsnd : forall y z H, val m bw n (snd (enc_mont_pair m bw n (y, z) H)) = z) by reflexivity.
        rewrite !Htempfst, !Htempsnd. rewrite <- Zplus_mod. apply (f_equal (fun y => y mod m)). ring.  
  Qed.

  Lemma montsub_to_Mp2 : forall x y z Hx Hy Hz, Fp2_sub_Gallina_spec x y z -> enc_mont_pair m bw n z Hz = montFp2_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big 
      (enc_mont_pair m bw n x Hx) (enc_mont_pair m bw n y Hy).
  Proof.
    intros [pr pi] [yr yi] [zr zi] Hx Hy Hz [_ [_ [H'1 H'2]]].
    apply pair_equal_spec; split; apply eval_from_mont_inj.
      - rewrite mont_enc_val. rewrite Prod.fst_pair. rewrite Prod.fst_pair in H'1.
        rewrite H'1. rewrite !Prod.fst_pair.
        pose proof (mont_sub_spec m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
        rewrite H.
        assert (Htempfst : forall y z H, val m bw n (fst (enc_mont_pair m bw n (y, z) H)) = y) by reflexivity.
        assert (Htempsnd : forall y z H, val m bw n (snd (enc_mont_pair m bw n (y, z) H)) = z) by reflexivity.
        rewrite !Htempfst. reflexivity.
      - rewrite mont_enc_val. rewrite Prod.snd_pair. rewrite Prod.snd_pair in H'2.
        rewrite H'2. rewrite !Prod.snd_pair.
        pose proof (mont_sub_spec m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
        rewrite H.
        assert (Htempfst : forall y z H, val m bw n (fst (enc_mont_pair m bw n (y, z) H)) = y) by reflexivity.
        assert (Htempsnd : forall y z H, val m bw n (snd (enc_mont_pair m bw n (y, z) H)) = z) by reflexivity.
        rewrite !Htempsnd. reflexivity.
  Qed.

  Lemma montadd_to_Mp2 : forall x y z Hx Hy Hz, Fp2_add_Gallina_spec x y z -> enc_mont_pair m bw n z Hz = montFp2_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big 
  (enc_mont_pair m bw n x Hx) (enc_mont_pair m bw n y Hy).
  Proof.
    intros [pr pi] [yr yi] [zr zi] Hx Hy Hz [_ [_ [H'1 H'2]]].
    apply pair_equal_spec; split; apply eval_from_mont_inj.
      - rewrite mont_enc_val. rewrite Prod.fst_pair. rewrite Prod.fst_pair in H'1.
        rewrite H'1. rewrite !Prod.fst_pair.
        pose proof (mont_add_spec m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
        rewrite H.
        assert (Htempfst : forall y z H, val m bw n (fst (enc_mont_pair m bw n (y, z) H)) = y) by reflexivity.
        assert (Htempsnd : forall y z H, val m bw n (snd (enc_mont_pair m bw n (y, z) H)) = z) by reflexivity.
        rewrite !Htempfst. reflexivity.
      - rewrite mont_enc_val. rewrite Prod.snd_pair. rewrite Prod.snd_pair in H'2.
        rewrite H'2. rewrite !Prod.snd_pair.
        pose proof (mont_add_spec m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
        rewrite H.
        assert (Htempfst : forall y z H, val m bw n (fst (enc_mont_pair m bw n (y, z) H)) = y) by reflexivity.
        assert (Htempsnd : forall y z H, val m bw n (snd (enc_mont_pair m bw n (y, z) H)) = z) by reflexivity.
        rewrite !Htempsnd. reflexivity.
  Qed.

  Ltac assert_valid_pair xr xi := let Hv := (fresh "Hv") in
  assert (Hv : valid'_pair m bw n (toZ xr, toZ xi)) by (split; (apply valid_valid'_equiv; assumption)).


  (*Tactics to use return values from function calls*)
  Local Notation valid'_pair := (valid'_pair m bw n).

  Ltac assert_valid_tac := split; [rewrite Prod.fst_pair| rewrite Prod.snd_pair]; apply valid_valid'_equiv; assumption. 

  Ltac assert_valid_pair_new x H := 
    tryif (assert (H : valid'_pair x) by assumption; clear H) then idtac else (assert (H : valid'_pair x) by (assert_valid_tac)).
    
  Ltac use_return_values z :=
      lazymatch goal with
      | H1 : Fp2_sub_Gallina_spec ?x ?y z |- _ => let Htemp := (fresh "Htemp") in let Htemp' := (fresh "Htemp") in
      assert_valid_pair_new y Htemp;
      assert_valid_pair_new x Htemp';
      lazymatch goal with | Hx : valid'_pair x |- _ => lazymatch goal with Hy : valid'_pair y |- _ =>
      rewrite (montsub_to_Mp2 x y z Hx Hy) end end; [| apply H1]; try (use_return_values y); try (use_return_values x)
      | H1 : Fp2_add_Gallina_spec ?x ?y z |- _ => let Htemp := (fresh "Htemp") in let Htemp' := (fresh "Htemp") in
      assert_valid_pair_new y Htemp;
      assert_valid_pair_new x Htemp';
      lazymatch goal with | Hx : valid'_pair x |- _ => lazymatch goal with Hy : valid'_pair y |- _ =>
      rewrite (montadd_to_Mp2 x y z Hx Hy) end end; [| apply H1]; try (use_return_values y); try (use_return_values x)
      | H1 : Fp2_mul_Gallina_spec ?x ?y z |- _ => let Htemp := (fresh "Htemp") in let Htemp' := (fresh "Htemp") in
      assert_valid_pair_new y Htemp;
      assert_valid_pair_new x Htemp';
      lazymatch goal with | Hx : valid'_pair x |- _ => lazymatch goal with Hy : valid'_pair y |- _ =>
      rewrite (montmul_to_Mp2 x y z Hx Hy) end end; [| apply H1]; try (use_return_values y); try (use_return_values x)
      | _ => idtac
      end.

  Theorem G2_add_func_ok : program_logic_goal_for_function! BLS12_add.
  Proof.
    (*initialize proof*)
    repeat straightline_stackalloc_Bignum.
    repeat straightline'.

    (*Store three_br*)
    Bignum_to_Scalars x. clear H33.
    handle_store.
    eassert ( (Bignum n a (List.map wordof_Z three_br_mont) * _)%sep _).
    {
      unfold Bignum. sepsimpl; [ cbv; auto|]. unfold array. cbv [three_br_mont map].
      repeat rewrite (word_add_comm _ (word.of_Z word_size_in_bytes)).
      repeat (rewrite next_word' in H51; try rewrite word_add_0 in H51).
      ecancel_assumption.
    }
    clear H51.

    (*store three_bi*)
    Bignum_to_Scalars x6. clear H33.
    handle_store.
    eassert ( (Bignum n a6 (List.map wordof_Z three_bi_mont) * _)%sep _).
    {
      unfold Bignum. sepsimpl; [ cbv; auto|]. unfold array. cbv [three_bi_mont map].
      repeat rewrite (word_add_comm _ (word.of_Z word_size_in_bytes)).
      repeat (rewrite next_word' in H52; try rewrite word_add_0 in H52).
      ecancel_assumption.
    }
    clear H52.
    
    rename H33 into H'.
    repeat straightline'.

    (*Preconditions of callees must be in context for function calls to handled automatically by the "next_call" tactic*)
    pose proof valid_toZ_wordofZ_three_br_mont.
    pose proof valid_toZ_wordofZ_three_bi_mont.

    (*Handle function calls.*)
    next_call.
    do 5 next_call.
    repeat next_call.

    (*Defragment allocated memory in context*)
    repeat (defrag_in_context (WordByWordMontgomery.n Spec.m bw)).
    repeat straightline.
    
    (*Postcondition*)
    (*Trivial subgoals are handled first*)
    do 2 (split; [reflexivity| ]).
    do 7 eexists; split; [| ecancel_assumption].

    (*Gallina specification part of postcondition*)
    unfold BLS12_add_Gallina_spec.

    (*Inputs/Outputs are valid elements of Mp2*)
    assert_valid_pair wX1r wX1i.
    assert_valid_pair wX2r wX2i.

    assert_valid_pair wY1r wY1i.
    assert_valid_pair wY2r wY2i.

    assert_valid_pair wZ1r wZ1i.
    assert_valid_pair wZ2r wZ2i.

    assert_valid_pair x86 x87.
    assert_valid_pair x77 x78.
    assert_valid_pair x95 x96.

    (*Use alternative curve spec*)
    destruct (MontgomeryCurveSpecs.BLS12_G2_add_Specs_equiv' m bw n r' m' 0 0 three_br three_bi ar_small ai_small three_br_small three_bi_small
      r'_correct m'_correct bw_big n_nz m_small m_big _ _ _ _ _ _ _ _ _ Hv Hv0 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7) as [Hequiv _].
    apply Hequiv; clear Hequiv.
    unfold BLS12_G2_add_mont_spec.

    (*Use return values from function calls*)
    use_return_values (toZ x86, toZ x87).
    use_return_values (toZ x77, toZ x78).
    use_return_values (toZ x95, toZ x96).

    (*Alias ring elements to help ring tactic solve goal*)
    rewrite remember_ap2.
    rewrite <- (remember_three_b Htemp4).
    remember (enc_mont_pair m bw n (toZ (map wordof_Z three_br_mont), toZ (map wordof_Z three_bi_mont)) Htemp4) as tb.
    remember (enc_mont_pair m bw n (toZ wY1r, toZ wY1i) Hv1) as y1.
    remember (enc_mont_pair m bw n (toZ wY2r, toZ wY2i) Hv2) as y2.
    remember (enc_mont_pair m bw n (toZ wX1r, toZ wX1i) Hv) as p1.
    remember (enc_mont_pair m bw n (toZ wX2r, toZ wX2i) Hv0) as p2.
    remember (enc_mont_pair m bw n (toZ wZ1r, toZ wZ1i) Hv3) as z1.
    remember (enc_mont_pair m bw n (toZ wZ2r, toZ wZ2i) Hv4) as z2.

    (*Equality of each coordinate is solved by ring tactic*)
    apply pair_equal_spec; split; [apply pair_equal_spec; split|]; try ring.
  Qed.


(*Variant that allows overlapping inputs/outputs*)
  (*Bedrock2 Function Definition*)
  Definition BLS12_add_alt : Syntax.func :=
      let outxr := "outxr" in
      let outyr := "outyr" in
      let outzr := "outzr" in
  
      let X1r := "X1r" in
      let Y1r := "Y1r" in
      let Z1r := "Z1r" in
  
      let X2r := "X2r" in
      let Y2r := "Y2r" in
      let Z2r := "Z2r" in
  
      let X1rsep := "X1rsep" in
      let Y1rsep := "Y1rsep" in
      let Z1rsep := "Z1rsep" in
  
      let X2rsep := "X2rsep" in
      let Y2rsep := "Y2rsep" in
      let Z2rsep := "Z2rsep" in

      let outxi := "outxi" in
      let outyi := "outyi" in
      let outzi := "outzi" in
  
      let X1i := "X1i" in
      let Y1i := "Y1i" in
      let Z1i := "Z1i" in
  
      let X2i := "X2i" in
      let Y2i := "Y2i" in
      let Z2i := "Z2i" in
  
      let X1isep := "X1isep" in
      let Y1isep := "Y1isep" in
      let Z1isep := "Z1isep" in
  
      let X2isep := "X2isep" in
      let Y2isep := "Y2isep" in
      let Z2isep := "Z2isep" in
  
      let BLS12_G2_add := "BLS12_G2_add" in
      let felem_copy := ("felem_copy" ++ felem_suffix) in  
      ("BLS12_G2_add_alt", (
        [outxr; outxi; outyr; outyi; outzr; outzi; X1r; X1i; Y1r; Y1i; Z1r; Z1i;
            X2r; X2i; Y2r; Y2i; Z2r; Z2i], [],
        bedrock_func_body:(

        stackalloc num_bytes as X1rsep {
        stackalloc num_bytes as X1isep {
        stackalloc num_bytes as Y1rsep {
        stackalloc num_bytes as Y1isep {
        stackalloc num_bytes as Z1rsep {
        stackalloc num_bytes as Z1isep {
        stackalloc num_bytes as X2rsep {
        stackalloc num_bytes as X2isep {
        stackalloc num_bytes as Y2rsep {
        stackalloc num_bytes as Y2isep {
        stackalloc num_bytes as Z2rsep {
        stackalloc num_bytes as Z2isep {
          
            (*copying X1*)
            felem_copy( X1rsep, X1r);
            felem_copy( X1isep, X1i);
            felem_copy( Y1rsep, Y1r);
            felem_copy( Y1isep, Y1i);
            felem_copy( Z1rsep, Z1r);
            felem_copy( Z1isep, Z1i);
            felem_copy( X2rsep, X2r);
            felem_copy( X2isep, X2i);
            felem_copy( Y2rsep, Y2r);
            felem_copy( Y2isep, Y2i);
            felem_copy( Z2rsep, Z2r);
            felem_copy( Z2isep, Z2i);

            BLS12_G2_add (outxr, outxi, outyr, outyi, outzr, outzi, X1rsep, X1isep, Y1rsep, Y1isep,
              Z1rsep, Z1isep, X2rsep, X2isep, Y2rsep, Y2isep, Z2rsep, Z2isep)
          }}}}}}}}}}}}
        )
      )).

Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.

(*Bedrock2 function Spec*)

Instance spec_of_BLS12_add_alt: spec_of BLS12_add_alt :=
fun functions : list (string * (list string * list string * cmd)) =>
    forall (wX1r wY1r wZ1r wX2r wY2r wZ2r wX1i wY1i wZ1i wX2i wY2i wZ2i : list Interface.word.rep)
    (pX1r pY1r pZ1r pX2r pY2r pZ2r pX1i pY1i pZ1i pX2i pY2i pZ2i poutxr poutyr poutzr poutxi poutyi poutzi: Interface.word.rep)
    (wold_outxr wold_outyr wold_outzr wold_outxi wold_outyi wold_outzi: list Interface.word.rep) (t : Semantics.trace)
    (m0 : Interface.map.rep) (RX1r RX1i RY1r RY1i RZ1r RZ1i 
      RX2r RX2i RY2r RY2i RZ2r RZ2i Rout : Interface.map.rep -> Prop),
    valid (List.map Interface.word.unsigned wX1r) /\
    valid (List.map Interface.word.unsigned wY1r) /\
    valid (List.map Interface.word.unsigned wZ1r) /\
    valid (List.map Interface.word.unsigned wX2r) /\
    valid (List.map Interface.word.unsigned wY2r) /\
    valid (List.map Interface.word.unsigned wZ2r) /\
    valid (List.map Interface.word.unsigned wX1i) /\
    valid (List.map Interface.word.unsigned wY1i) /\
    valid (List.map Interface.word.unsigned wZ1i) /\
    valid (List.map Interface.word.unsigned wX2i) /\
    valid (List.map Interface.word.unsigned wY2i) /\
    valid (List.map Interface.word.unsigned wZ2i) ->
    ((Bignum n pX1r wX1r) * RX1r)%sep m0 ->
    ((Bignum n pX1i wX1i) * RX1i)%sep m0 ->
    ((Bignum n pY1r wY1r) * RY1r)%sep m0 ->
    ((Bignum n pY1i wY1i) * RY1i)%sep m0 ->
    ((Bignum n pZ1r wZ1r) * RZ1r)%sep m0 ->
    ((Bignum n pZ1i wZ1i) * RZ1i)%sep m0 ->
    ((Bignum n pX2r wX2r) * RX2r)%sep m0 ->
    ((Bignum n pX2i wX2i) * RX2i)%sep m0 ->
    ((Bignum n pY2r wY2r) * RY2r)%sep m0 ->
    ((Bignum n pY2i wY2i) * RY2i)%sep m0 ->
    ((Bignum n pZ2r wZ2r) * RZ2r)%sep m0 ->
    ((Bignum n pZ2i wZ2i) * RZ2i)%sep m0 ->
    ((Bignum n poutxr wold_outxr) * (Bignum n poutyr wold_outyr) * (Bignum n poutzr wold_outzr) *
    (Bignum n poutxi wold_outxi) * (Bignum n poutyi wold_outyi) * (Bignum n poutzi wold_outzi) * Rout)%sep m0 ->
    WeakestPrecondition.call functions ( "BLS12_G2_add_alt") t m0
    ([poutxr; poutxi; poutyr; poutyi; poutzr; poutzi; pX1r; pX1i; pY1r; pY1i; pZ1r; pZ1i; pX2r; pX2i; pY2r; pY2i; pZ2r; pZ2i])
    (fun (t' : Semantics.trace) (m' : Interface.map.rep)
        (rets : list Interface.word.rep) =>
    t = t' /\
    rets = nil /\
    (exists (woutxr woutyr woutzr woutxi woutyi woutzi: list Interface.word.rep) Rout,
        (
                (BLS12_add_Gallina_spec (toZ wX1r) (toZ wX1i) (toZ wY1r) (toZ wY1i) (toZ wZ1r) (toZ wZ1i) (toZ wX2r)
                (toZ wX2i) (toZ wY2r) (toZ wY2i) 
                (toZ wZ2r) (toZ wZ2i) (toZ woutxr) (toZ woutxi) (toZ woutyr) (toZ woutyi) (toZ woutzr) (toZ woutzi) /\
             ((Bignum n poutxr woutxr) * (Bignum n poutyr woutyr) * (Bignum n poutzr woutzr) *
             (Bignum n poutxi woutxi) * (Bignum n poutyi woutyi) * (Bignum n poutzi woutzi) * Rout)%sep m')))).

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
    do 12 straightline.

    (*Assert single hypothesis for stackallocation.*)
    remember (Bignum n pX1r wX1r * RX1r)%sep as RX1r'.
    remember (Bignum n pY1r wY1r * RY1r)%sep as RY1r'.
    remember (Bignum n pZ1r wZ1r * RZ1r)%sep as RZ1r'.
    remember (Bignum n pX2r wX2r * RX2r)%sep as RX2r'.
    remember (Bignum n pY2r wY2r * RY2r)%sep as RY2r'.
    remember (Bignum n pZ2r wZ2r * RZ2r)%sep as RZ2r'.
    remember (Bignum n pX1i wX1i * RX1i)%sep as RX1i'.
    remember (Bignum n pY1i wY1i * RY1i)%sep as RY1i'.
    remember (Bignum n pZ1i wZ1i * RZ1i)%sep as RZ1i'.
    remember (Bignum n pX2i wX2i * RX2i)%sep as RX2i'.
    remember (Bignum n pY2i wY2i * RY2i)%sep as RY2i'.
    remember (Bignum n pZ2i wZ2i * RZ2i)%sep as RZ2i'.
    remember ((Bignum n poutxr wold_outxr * Bignum n poutyr wold_outyr *
          Bignum n poutzr wold_outzr * Bignum n poutxi wold_outxi *
          Bignum n poutyi wold_outyi * Bignum n poutzi wold_outzi * Rout)%sep) as Rout'.

    assert (
        id (fun m => (RX1r' m /\ RX1i' m /\ RY1r' m /\ RY1i' m /\ RZ1r' m /\ RZ1i' m /\ 
        RX2r' m /\ RX2i' m /\ RY2r' m /\ RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m)) m0).
    {
      cbv [id]. split; auto. repeat (split; auto); auto.
    }

    (*Allocate memory on stack. *)
    repeat straightline''. clear H37 Hmnew Hmnew0 Hmnew1 Hmnew2 Hmnew3 Hmnew4 Hmnew5 Hmnew6 Hmnew7 Hmnew8 Hmnew9.
    repeat straightline'. cbv [id] in *.

    (*Handle calls to felem_copy.
      Perhaps find a good way to automate these tactic applications?*)
      Ltac copy_next R fR thism pX1 wX1 RX1 a H := straightline_call; [subst R; remember fR as thisP;
      eassert (thisH : ((fun m => (Bignum n pX1 wX1 * RX1)%sep m /\ thisP m) * Bignum n a _ * _)%sep thism) by (subst thisP; ecancel_assumption); subst thisP; apply thisH |]; clear H; repeat straightline.


    copy_next RX1r' (fun m => (RX1i' m /\ RY1r' m /\ RY1i' m /\ RZ1r' m /\ RZ1i' m /\ 
    RX2r' m /\ RX2i' m /\ RY2r' m /\ RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m)) mnew10 pX1r wX1r RX1r a Hmnew10.

    copy_next RX1i' (fun m => (RY1r' m /\ RY1i' m /\ RZ1r' m /\ RZ1i' m /\ 
    RX2r' m /\ RX2i' m /\ RY2r' m /\ RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m)) a12 pX1i wX1i RX1i a0 H39.

    copy_next RY1r' (fun m => (RY1i' m /\ RZ1r' m /\ RZ1i' m /\ 
    RX2r' m /\ RX2i' m /\ RY2r' m /\ RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m)) a14 pY1r wY1r RY1r a1 H39.

    copy_next RY1i' (fun m => (RZ1r' m /\ RZ1i' m /\ 
    RX2r' m /\ RX2i' m /\ RY2r' m /\ RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m)) a12 pY1i wY1i RY1i a2 H39.

    copy_next RZ1r' (fun m => (RZ1i' m /\ 
    RX2r' m /\ RX2i' m /\ RY2r' m /\ RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m)) a14 pZ1r wZ1r RZ1r a3 H39.

    copy_next RZ1i' (fun m => (RX2r' m /\ RX2i' m /\ RY2r' m /\ RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m))
        a12 pZ1i wZ1i RZ1i a4 H39.
      
    copy_next RX2r' (fun m => (RX2i' m /\ RY2r' m /\ RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m))
        a14 pX2r wX2r RX2r a5 H39.

    copy_next RX2i' (fun m => (RY2r' m /\ RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m))
        a12 pX2i wX2i RX2i a6 H39.
    
    copy_next RY2r' (fun m => (RY2i' m /\ RZ2r' m /\ RZ2i' m /\ Rout' m))
        a14 pY2r wY2r RY2r a7 H39.

    copy_next RY2i' (fun m => (RZ2r' m /\ RZ2i' m /\ Rout' m))
        a12 pY2i wY2i RY2i a8 H39.

    copy_next RZ2r' (fun m => (RZ2i' m /\ Rout' m))
        a14 pZ2r wZ2r RZ2r a9 H39.

    copy_next RZ2i' (fun m => (Rout' m))
        a12 pZ2i wZ2i RZ2i a10 H39.

    (*Handle function call*)
    repeat straightline.
    straightline_call.
    2: assert (nval : num_limbs = n) by (cbv; auto); rewrite nval in *; ecancel_assumption.
    1: repeat (split; auto).

    (*Defragment memory in context after stack allocation. *)
    repeat straightline.
    repeat (defrag_in_context (WordByWordMontgomery.n Spec.m bw)).

    (*Postcondition*)
    repeat straightline. do 2 split; auto.
    do 7 eexists. split.
    2: ecancel_assumption.
    auto.
  Qed.

(* Printing to C
From bedrock2 Require Import ToCString Bytedump.
Definition bls12_c_add :=
  c_module (add :: nil).
  Definition bls12_c_mul :=
  c_module (mul :: nil).
  Definition bls12_c_sub :=
  c_module (sub :: nil).
  Definition bls12_c_Fp2add' :=
   c_module (Fp2_add :: nil).
  Definition bls12_c_Fp2sub' :=
  c_module (Fp2_sub :: nil).
  Definition bls12_c_Fp2mul' :=
   c_module (Fp2_mul :: nil).
  Definition bls12_c_Fp2add :=
  c_module (Fp2_add_alt2 :: nil).
  Definition bls12_c_felem_copy :=
  c_module (felem_copy :: nil).
  Definition bls12_c_Fp2sub :=
  c_module (Fp2_sub_alt2 :: nil).
  Definition bls12_c_Fp2mul :=
  c_module (Fp2_mul_alt2 :: nil).
  Definition G2_add :=
  c_module (BLS12_add :: nil).
  Eval compute in bls12_c_Fp2mul'. *)

End Spec.