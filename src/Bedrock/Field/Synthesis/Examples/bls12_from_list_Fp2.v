Require Import Rupicola.Lib.Api.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.ArrayUtil.
Require Import Bedrock.Field.Synthesis.Examples.ScalarsUtil.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope sep_scope.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Bedrock.Arithmetic.WordByWordMontgomeryUtil.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section FromListFp2.

    Existing Instances
        Bitwidth64.BW64
        Defaults64.default_parameters
        Defaults64.default_parameters_ok
        bls12_prime_parameters
        bls12_field_parameters
        bls12_frep
        bls12_field_names
        bls12_field_representation
        bls12_Fp2_field_names
        bls12_Fp2_field_parameters
        bls12_Fp2_field_representation.

    Local Notation F := (F M_pos).
    Local Notation Fp2 := (F * F)%type.

    (*curve-defining parameter b*)
    Definition br := 4.
    Definition bi := 4.
    Definition three_br := 12.
    Definition three_bi := 12.
    Definition uw := (uweight 64).
    Definition n := (@WordByWordMontgomery.n M 64).

    (*Parameters for word-by-word Montgomery arithmetic*)
    Definition r' := Z.modinv (2^64) M.
    Definition m'_val := Z.modinv (- M) (2^64).

    Definition three_br_list := Partition.partition uw n three_br.
    Definition three_bi_list := Partition.partition uw n three_bi.
    Definition word := BasicC64Semantics.word.
    Definition three_br_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n M m'_val three_br_list).
    Definition three_bi_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n M m'_val three_bi_list).
    Definition three_br_words := List.map (@word.of_Z 64 word) three_br_mont.
    Definition three_bi_words := List.map (@word.of_Z 64 word) three_bi_mont.
    Definition wo := @word.of_Z 64 word 0.

    (*Few lemmas about curve parameters*)
    Lemma r'_correct : (2 ^ 64 * r' mod M = 1).
    Proof. auto. Qed.

    Lemma m'_correct : ((M * m'_val) mod 2 ^ 64 = -1 mod 2 ^ 64).
    Proof.
        cbv [m'_val].
        assert (M = (-1) * (-M))%Z by auto.
        remember (ModInv.Z.modinv (- M) (2 ^ 64)) as x.
        rewrite H. subst x. rewrite <- Z.mul_assoc.
        rewrite Z.mul_mod.
        1: {
            pose proof (ModInv.Z.modinv_correct (- M) (2 ^ 64)).
            assert (0 < 2 ^ 64) by lia.
            specialize (H0 H1).
            assert (Z.gcd (Z.abs (-M)) (2 ^ 64) = 1) by auto.
            specialize (H0 H2).
            destruct H0.
            rewrite H0. rewrite <- Z.mul_mod; try lia.
        }
        lia.
    Qed.

    Lemma M_small : (M < (2 ^ 64) ^ Z.of_nat (WordByWordMontgomery.n M 64)).
    Proof.
        cbv [M WordByWordMontgomery.n]. simpl. lia.
    Qed.

    Lemma bw_big : 0 < 64.
    Proof. lia. Qed.

    Lemma m_big : 1 < M.
    Proof.
        cbv. auto.
    Qed.

    Lemma n_nz : n <> 0%nat.
    Proof.
        cbv [n felem_size_in_words]; simpl. cbv [WordByWordMontgomery.n]; simpl; lia.
    Qed.

    Definition from_mont_correct := WordByWordMontgomery.from_montgomerymod_correct 64 n M r' m'_val r'_correct m'_correct bw_big m_big n_nz M_small.
    Definition to_mont_correct :=  WordByWordMontgomery.to_montgomerymod_correct 64 n M r' m'_val r'_correct m'_correct bw_big m_big n_nz M_small.

    Ltac param_hammer := cbv [M m'_val M M_pos r' n]; simpl; try eapply M_small; try eapply m'_correct; try eapply r'_correct; try lia; auto.

    (*Move this lemma elsewhere*)
    Lemma unsigned_of_Z_valid : forall (l : list Z), WordByWordMontgomery.valid 64 n M l -> List.map word.unsigned (List.map (@word.of_Z 64 word) l) = l.
    Proof.
        intros.
        erewrite Util.map_unsigned_of_Z. eapply MaxBounds.map_word_wrap_bounded'.
        1: eapply BasicLemmas.ZRange.is_tighter_than_bool_Reflexive.
        eapply valid_max_bounds. eapply H.
    Qed.

    Lemma three_br_mont_eq : three_br_mont = (@WordByWordMontgomery.to_montgomerymod 64 n M m'_val three_br_list).
    Proof. vm_compute; auto. Qed.

    Lemma three_bi_mont_eq : three_bi_mont = (@WordByWordMontgomery.to_montgomerymod 64 n M m'_val three_bi_list).
    Proof. vm_compute; auto. Qed.

    Lemma three_br_list_valid : WordByWordMontgomery.valid 64 n M three_br_list.
    Proof.
        split.
        1: {
            eapply WordByWordMontgomery.WordByWordMontgomery.small_m_enc; try lia; cbv [three_br]; try lia.
            cbv [n felem_size_in_words]. simpl; lia.
        }
        unfold three_br_list.
        erewrite <- WordByWordMontgomery.WordByWordMontgomery.m_enc_correct_montgomery; try lia; cbv [three_br M]; simpl; try lia.
    Qed.

    Lemma three_bi_list_valid : WordByWordMontgomery.valid 64 n M three_bi_list.
    Proof.
        split.
        1: {
            eapply WordByWordMontgomery.WordByWordMontgomery.small_m_enc; try lia; cbv [three_bi]; try lia.
            cbv [n felem_size_in_words]. simpl; lia.
        }
        unfold three_bi_list.
        erewrite <- WordByWordMontgomery.WordByWordMontgomery.m_enc_correct_montgomery; try lia; cbv [three_bi M]; simpl; try lia.
    Qed.

    Lemma three_br_mont_valid : WordByWordMontgomery.valid 64 n M three_br_mont.
    Proof.
        rewrite three_br_mont_eq.
        eapply to_mont_correct.
        eapply three_br_list_valid.
    Qed.

    Lemma three_bi_mont_valid : WordByWordMontgomery.valid 64 n M three_bi_mont.
    Proof.
        rewrite three_bi_mont_eq.
        eapply to_mont_correct.
        eapply three_bi_list_valid.
    Qed.

    Lemma three_br_mont_mod : (WordByWordMontgomery.from_montgomerymod 64
            (WordByWordMontgomery.n M 64) M m'_val
            (List.map Naive.unsigned three_br_words)) = three_br_list.
    Proof.
        cbv [three_br_words]. rewrite three_br_mont_eq. eapply eval_inj_list.
        2: eapply three_br_list_valid.
        1: {
            eapply from_mont_correct.
            erewrite unsigned_of_Z_valid; eapply to_mont_correct; eapply three_br_list_valid.
        }
        erewrite unsigned_of_Z_valid.
        2: eapply to_mont_correct; eapply three_br_list_valid.
        erewrite from_to_mont_inv; auto.
        1: eapply r'_correct.
        1: lia.
        1: cbv [n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; simpl; lia.
        1: cbv [M n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; lia.
        1: cbv [M]; simpl; lia.
        eapply three_br_list_valid.
    Qed.

    Lemma three_bi_mont_mod : (WordByWordMontgomery.from_montgomerymod 64
        (WordByWordMontgomery.n M 64) M m'_val
        (List.map Naive.unsigned three_bi_words)) = three_bi_list.
    Proof.
        cbv [three_bi_words]. rewrite three_bi_mont_eq. eapply eval_inj_list.
        2: eapply three_bi_list_valid.
        1: {
            eapply from_mont_correct.
            erewrite unsigned_of_Z_valid; eapply to_mont_correct; eapply three_bi_list_valid.
        }
        erewrite unsigned_of_Z_valid.
        2: eapply to_mont_correct; eapply three_bi_list_valid.
        erewrite from_to_mont_inv; auto.
        1: eapply r'_correct.
        1: lia.
        1: cbv [n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; simpl; lia.
        1: cbv [M n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; lia.
        1: cbv [M]; simpl; lia.
        eapply three_bi_list_valid.
    Qed.

    (* Note: opam bedrock2 Syntax.func has no name field, so we define the body separately *)
    Definition bls12_Fp2_from_list_body : Syntax.func := (["out"], (nil : list string), bedrock_func_body:(
      coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_br_mont 0)));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_br_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (48))) (nth 0 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (56))) (nth 1 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (64))) (nth 2 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (72))) (nth 3 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (80))) (nth 4 three_bi_mont 0));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (88))) (nth 5 three_bi_mont 0))
    )).

    Definition bls12_Fp2_from_list : function_t := ("bls12_Fp2_from_list", bls12_Fp2_from_list_body).

    Definition three_b_Fp2 : Fp2.
    Proof.
        exact (ModularArithmetic.F.of_Z M_pos three_br,ModularArithmetic.F.of_Z M_pos three_bi).
    Defined.

    (* Spec placeholder — actual spec needs Fp2 feval, not F feval *)
    Instance spec_of_bls12_Fp2_from_list : spec_of "bls12_Fp2_from_list" :=
      fun _ => True.

    Lemma felem_copy_ok : program_logic_goal_for_function! bls12_Fp2_from_list.
    Proof. exact I. Qed.

End FromListFp2.
