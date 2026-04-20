Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.ArrayUtil.
Require Import Bedrock.Field.Synthesis.Examples.ScalarsUtil.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope sep_scope.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Bedrock.Arithmetic.WordByWordMontgomeryUtil.
Require Import Crypto.Util.ZUtil.ModInv.

Section FromListF.

  Existing Instances
      Bitwidth64.BW64
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

  Local Notation F := (F M_pos).

  Existing Instance bls12_field_parameters.
  Existing Instance bls12_frep.

  (*curve-defining parameter b*)
  Definition b := 4.
  Definition three_b := 12.
  Definition uw := (uweight 64).
  Definition n := felem_size_in_words.
  Definition three_b_list := Partition.partition uw n three_b.

  (*Parameters for word-by-word Montgomery arithmetic*)
  Definition r' := Z.modinv (2^64) M.
  Definition m' := Z.modinv (- M) (2^64).

  Definition three_b_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n M m' three_b_list).
  Definition three_b_words := List.map (@word.of_Z 64 BasicC64Semantics.word) three_b_mont.
  Definition wo := @word.of_Z 64 BasicC64Semantics.word 0.

  (*Few lemmas about curve parameters*)
  Lemma r'_correct : (2 ^ 64 * r' mod M = 1).
  Proof. auto. Qed.

  Lemma m'_correct : ((M * m') mod 2 ^ 64 = -1 mod 2 ^ 64).
  Proof.
      cbv [m'].
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
          unfold M in *.
          rewrite H0. rewrite <- Z.mul_mod; try lia.
      }
      lia.
  Qed.

  Lemma M_small : (M < (2 ^ 64) ^ Z.of_nat (WordByWordMontgomery.n M 64)).
  Proof. reflexivity. Qed.

  Lemma bw_big : 0 < 64.
  Proof. reflexivity. Qed.

  Lemma M_big : 1 < M.
  Proof. reflexivity. Qed.

  Lemma n_nz : n <> 0%nat.
  Proof. cbv. congruence. Qed.

  Definition from_mont_correct := WordByWordMontgomery.from_montgomerymod_correct 64 n M r' m' r'_correct m'_correct bw_big M_big n_nz M_small.
  Definition to_mont_correct :=  WordByWordMontgomery.to_montgomerymod_correct 64 n M r' m' r'_correct m'_correct bw_big M_big n_nz M_small.

  Lemma unsigned_of_Z_valid : forall (l : list Z), WordByWordMontgomery.valid 64 n M l -> List.map word.unsigned (List.map (@word.of_Z 64 BasicC64Semantics.word) l) = l.
  Proof.
      intros.
      erewrite Util.map_unsigned_of_Z. eapply MaxBounds.map_word_wrap_bounded'.
      1: eapply BasicLemmas.ZRange.is_tighter_than_bool_Reflexive.
      eapply valid_max_bounds. eapply H.
  Qed.

  Lemma three_b_mont_eq : three_b_mont = (@WordByWordMontgomery.to_montgomerymod 64 n M m' three_b_list).
  Proof. vm_compute; auto. Qed.

  Lemma three_b_list_valid : WordByWordMontgomery.valid 64 n M three_b_list.
  Proof.
      split.
      1: {
          eapply WordByWordMontgomery.WordByWordMontgomery.small_m_enc; try lia; cbv [three_b]; try lia.
          cbv [n felem_size_in_words]. simpl; lia.
      }
      unfold three_b_list.
      erewrite <- WordByWordMontgomery.WordByWordMontgomery.m_enc_correct_montgomery; try lia; cbv [three_b M]; try (simpl; lia).
  Qed.

  Lemma three_b_mont_valid : WordByWordMontgomery.valid 64 n M three_b_mont.
  Proof.
      rewrite three_b_mont_eq.
      eapply to_mont_correct.
      eapply three_b_list_valid.
  Qed.

  Lemma three_b_mont_mod : (WordByWordMontgomery.from_montgomerymod 64
                                (WordByWordMontgomery.n M 64) M m'
                                (List.map Naive.unsigned three_b_words)) = three_b_list.
  Proof.
      cbv [three_b_words]. rewrite three_b_mont_eq. eapply eval_inj_list.
      2: eapply three_b_list_valid.
      1: {
          eapply from_mont_correct.
          erewrite unsigned_of_Z_valid; eapply to_mont_correct; eapply three_b_list_valid.
      }
      erewrite unsigned_of_Z_valid.
      2: eapply to_mont_correct; eapply three_b_list_valid.
      erewrite from_to_mont_inv; auto.
      1: eapply r'_correct.
      1: lia.
      1: cbv [n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; simpl; lia.
      1: cbv [M n felem_size_in_words]; simpl; cbv [WordByWordMontgomery.n]; lia.
      1: cbv; reflexivity.
      eapply three_b_list_valid.
  Qed.

  Lemma feval_three_b_words :
    feval three_b_words = F.of_Z M_pos three_b.
  Proof.
    unfold feval.
    cbv [bls12_frep field_representation Signature.field_representation
         Representation.frep Representation.eval_words].
    unfold eval_trans.
    change (ListDef.map word.unsigned three_b_words) with (List.map Naive.unsigned three_b_words).
    change m with M.
    change (WordByWordMontgomery.m' M 64) with m'.
    rewrite three_b_mont_mod.
    replace (Core.Positional.eval (uweight 64) (WordByWordMontgomery.n M 64) three_b_list)
      with three_b by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  Lemma three_b_words_length : length three_b_words = felem_size_in_words.
  Proof. cbv [three_b_words three_b_mont felem_size_in_words]. simpl. reflexivity. Qed.

  Definition three_b_felem : felem := exist _ three_b_words three_b_words_length.

  Definition bls12_three_b : Syntax.func := (["out"], (nil : list string), bedrock_func_body:(
    coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_b_mont 0)));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_b_mont 0));
    coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_b_mont 0)))).

  Local Notation function_t := ((String.string * Syntax.func)%type).
  Definition bls12_three_b_func : function_t := ("bls12_three_b", bls12_three_b).

  (* Inline spec replacing spec_of_from_list from AbstractField *)
  Instance spec_of_bls12_three_b : spec_of "bls12_three_b" :=
    fnspec! "bls12_three_b" (pout : word) / (outold : felem) Rout,
    {
        requires tr mem :=
        (FElem pout outold * Rout)%sep mem ;
        ensures tr' mem' := exists out : felem,
        feval out = F.of_Z M_pos three_b /\ tr = tr' /\ bounded_by loose_bounds out /\
        (FElem pout out * Rout)%sep mem'
    }.

  Ltac collect H1 H2 := let Hnew := (fresh "Hnew") in
  eassert (Hnew : id (fun M => (_ M) /\ (_ M)) _) by (cbv [id]; split; [eapply H1| eapply H2]); clear H1 H2.

  Local Infix "+w" := word.add (at level 80).
  Local Infix "*w" := word.mul (at level 70).

  Lemma bls12_three_b_ok : program_logic_goal_for_function! bls12_three_b.
  Proof.
    enter bls12_three_b.
    unfold spec_of_bls12_three_b.
    intros.
    eapply WeakestPreconditionProperties.start_func; [exact EnvContains | clear EnvContains].
    cbv match beta delta [WeakestPrecondition.func].
    repeat straightline.
    (* straightline stuck at first store: decompose FElem into individual scalars *)
    cbv [FElem Field.FElem Bignum.Bignum] in H.
    destruct outold as [ws Hlen]. simpl proj1_sig in *.
    change felem_size_in_words with 6%nat in Hlen.
    do 6 (destruct ws as [|? ws]; [simpl in Hlen; lia|]).
    destruct ws; [|simpl in Hlen; lia].
    cbn [array] in H.
    change (Memory.bytes_per_word 64) with 8 in *.
    (* Normalize iterated (pout+8)+8+... addresses cascading *)
    replace ((pout +w word.of_Z 8) +w word.of_Z 8) with (pout +w word.of_Z 16) in H by ring.
    replace ((pout +w word.of_Z 16) +w word.of_Z 8) with (pout +w word.of_Z 24) in H by ring.
    replace ((pout +w word.of_Z 24) +w word.of_Z 8) with (pout +w word.of_Z 32) in H by ring.
    replace ((pout +w word.of_Z 32) +w word.of_Z 8) with (pout +w word.of_Z 40) in H by ring.
    repeat straightline.
    (* Provide three_b_felem as witness *)
    exists three_b_felem.
    split. {
      (* feval (felem_to_list three_b_felem) = F.of_Z M_pos three_b *)
      cbv [felem_to_list three_b_felem proj1_sig].
      exact feval_three_b_words.
    }
    split. { reflexivity. }
    split. {
      (* bounded_by loose_bounds three_b_felem *)
      cbv [felem_to_list three_b_felem proj1_sig three_b_words
           bounded_by Field.bounded_by bls12_frep field_representation
           Signature.field_representation Representation.frep
           loose_bounds Field.loose_bounds].
      rewrite (unsigned_of_Z_valid three_b_mont three_b_mont_valid).
      exact three_b_mont_valid.
    }
    {
      (* (FElem pout three_b_felem * Rout)%sep m4 *)
      (* Unfold FElem into array of scalars *)
      cbv [FElem Field.FElem Bignum.Bignum felem_to_list three_b_felem
           proj1_sig three_b_words three_b_mont felem_size_in_words].
      cbn [array List.map].
      change (Memory.bytes_per_word 64) with 8.
      (* Normalize addresses *)
      replace ((pout +w word.of_Z 8) +w word.of_Z 8) with (pout +w word.of_Z 16) by ring.
      replace ((pout +w word.of_Z 16) +w word.of_Z 8) with (pout +w word.of_Z 24) by ring.
      replace ((pout +w word.of_Z 24) +w word.of_Z 8) with (pout +w word.of_Z 32) by ring.
      replace ((pout +w word.of_Z 32) +w word.of_Z 8) with (pout +w word.of_Z 40) by ring.
      (* Substitute local aliases *)
      subst a a0 a1 a2 a3 v v0 v1 v2 v3 v4.
      ecancel_assumption.
    }
  Qed.

End FromListF.
