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

    Existing Instance bls12_field_parameters.
    Existing Instance bls12_frep.
    Existing Instance bls12_frep_ok.

    Definition bls12_felem_copy : Syntax.func := (["out"; "in"], (nil : list string), bedrock_func_body:(
      coq:(cmd.store access_size.word (expr.var "out") (expr.load access_size.word (expr.var "in")));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (8)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (16)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (24)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (32))))); coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (40)))))
    )).

    Instance bls12_felem_copy_spec : spec_of felem_copy := spec_of_felem_copy.

    Lemma felem_copy_ok : program_logic_goal_for_function! bls12_felem_copy.
    Proof.
      cbv beta delta [program_logic_goal_for].
      intros functions EnvContains pout px x out R tr mem0 [Hsep Hlen].
      (* Convert out$@pout to FElem via felem_from_bytes *)
      seprewrite_in (felem_from_bytes pout out Hlen) Hsep.
      (* Unfold FElem to array scalar 8 *)
      unfold FElem in Hsep.
      change (Memory.bytes_per_word 64) with 8 in Hsep.
      (* Destructure x into 6 words *)
      destruct x as [xl xpf]; simpl proj1_sig in *.
      change felem_size_in_words with 6%nat in xpf.
      destruct xl as [| x0 [| x1 [| x2 [| x3 [| x4 [| x5 []]]]]]];
        try discriminate.
      (* Simplify bs2felem conditional using length hypothesis *)
      assert (Hlen48 : Datatypes.length out = Pos.to_nat 48)
        by (change (Z.to_nat felem_size_in_bytes) with (Pos.to_nat 48) in Hlen;
            exact Hlen).
      rewrite Hlen48 in Hsep; rewrite Nat.eqb_refl in Hsep.
      (* Destructure output word list into 6 words *)
      set (ys := bs2ws (Pos.to_nat 8) out) in Hsep.
      assert (Hyslen: length ys = 6%nat)
        by (subst ys;
            change (Pos.to_nat 8) with (Z.to_nat (Memory.bytes_per_word 64));
            change 6%nat with felem_size_in_words;
            apply bs2ws_felem_length; exact Hlen).
      destruct ys as [| y0 [| y1 [| y2 [| y3 [| y4 [| y5 []]]]]]];
        try discriminate.
      clear Hyslen.
      (* Unfold arrays to individual scalar predicates *)
      cbn [array] in Hsep.
      change (Memory.bytes_per_word 64) with 8 in Hsep.
      (* Normalize nested word.add addresses to flat offsets *)
      repeat match type of Hsep with
      | context[word.add (word.add ?base (word.of_Z ?a)) (word.of_Z ?b)] =>
        let c := eval cbv in (a + b)%Z in
        replace (word.add (word.add base (word.of_Z a)) (word.of_Z b))
          with (word.add base (word.of_Z c)) in Hsep by ring
      end.
      (* Enter the function *)
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv match beta delta [WeakestPrecondition.func bls12_felem_copy].
      eexists; split; [exact eq_refl|].
      (* Process all 6 store commands *)
      repeat straightline.
      (* Close the postcondition: reassemble scalars into FElem arrays *)
      unfold FElem; simpl proj1_sig.
      change (Memory.bytes_per_word 64) with 8.
      cbn [array].
      repeat match goal with
      | |- context[word.add (word.add ?base (word.of_Z ?a)) (word.of_Z ?b)] =>
        let c := eval cbv in (a + b)%Z in
        replace (word.add (word.add base (word.of_Z a)) (word.of_Z b))
          with (word.add base (word.of_Z c)) by ring
      end.
      subst a a0 a1 a2 a3.
      ecancel_assumption.
    Qed.

End FelemCopy.
