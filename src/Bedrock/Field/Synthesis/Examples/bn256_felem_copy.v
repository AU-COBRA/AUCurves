Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.ArrayUtil.
Require Import Bedrock.Field.Synthesis.Examples.ScalarsUtil.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Import Syntax BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope sep_scope.

Section FelemCopy.

    Existing Instances
      Bitwidth64.BW64
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Local Notation F := (F M_pos).

    Existing Instance bn256_field_parameters.
    Existing Instance bn256_frep.
    Existing Instance bn256_frep_ok.

    (* BN256 uses 4 x 64-bit words (256 bits) *)
    Definition bn256_felem_copy : Syntax.func := (["out"; "in"], (nil : list string), bedrock_func_body:(
      coq:(cmd.store access_size.word (expr.var "out") (expr.load access_size.word (expr.var "in")));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (8)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (16)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (24)))))
    )).

    Instance bn256_felem_copy_spec : spec_of felem_copy := spec_of_felem_copy.

    Lemma felem_copy_ok : program_logic_goal_for_function! bn256_felem_copy.
    Proof.
      cbv beta delta [program_logic_goal_for].
      intros functions EnvContains pout px x out R tr mem0 [Hsep Hlen].
      seprewrite_in (felem_from_bytes pout out Hlen) Hsep.
      unfold FElem in Hsep.
      change (Memory.bytes_per_word 64) with 8 in Hsep.
      destruct x as [xl xpf]; simpl proj1_sig in *.
      change felem_size_in_words with 4%nat in xpf.
      destruct xl as [| x0 [| x1 [| x2 [| x3 []]]]];
        try discriminate.
      assert (Hlen32 : Datatypes.length out = Pos.to_nat 32)
        by (change (Z.to_nat felem_size_in_bytes) with (Pos.to_nat 32) in Hlen;
            exact Hlen).
      rewrite Hlen32 in Hsep; rewrite Nat.eqb_refl in Hsep.
      set (ys := bs2ws (Pos.to_nat 8) out) in Hsep.
      assert (Hyslen: length ys = 4%nat)
        by (subst ys;
            change (Pos.to_nat 8) with (Z.to_nat (Memory.bytes_per_word 64));
            change 4%nat with felem_size_in_words;
            apply bs2ws_felem_length; exact Hlen).
      destruct ys as [| y0 [| y1 [| y2 [| y3 []]]]];
        try discriminate.
      clear Hyslen.
      cbn [array] in Hsep.
      change (Memory.bytes_per_word 64) with 8 in Hsep.
      repeat match type of Hsep with
      | context[word.add (word.add ?base (word.of_Z ?a)) (word.of_Z ?b)] =>
        let c := eval cbv in (a + b)%Z in
        replace (word.add (word.add base (word.of_Z a)) (word.of_Z b))
          with (word.add base (word.of_Z c)) in Hsep by ring
      end.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv match beta delta [WeakestPrecondition.func bn256_felem_copy].
      eexists; split; [exact eq_refl|].
      repeat straightline.
      unfold FElem; simpl proj1_sig.
      change (Memory.bytes_per_word 64) with 8.
      cbn [array].
      repeat match goal with
      | |- context[word.add (word.add ?base (word.of_Z ?a)) (word.of_Z ?b)] =>
        let c := eval cbv in (a + b)%Z in
        replace (word.add (word.add base (word.of_Z a)) (word.of_Z b))
          with (word.add base (word.of_Z c)) by ring
      end.
      subst a a0 a1.
      ecancel_assumption.
    Qed.

End FelemCopy.
