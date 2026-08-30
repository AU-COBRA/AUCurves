(** * bls24_509_felem_copy — the felem_copy leaf for BLS24-509.

    Derived from the BN254 file [bn254_felem_copy.v], with the
    instances pointed at [bls24_509_Fp].  The body and its proof are
    NOT curve-generic: both are indexed by the limb count.  BLS24-509
    is 8 x 64-bit words against BN254's 4, so the body carries eight
    store/load pairs at offsets 0..56 rather than four at 0..24, and
    the script's [change felem_size_in_words with 8%nat], the two
    eight-way [destruct]s, and [Pos.to_nat 64] (64 bytes, not 32) all
    follow from that.  The final [subst] is left unqualified because
    eight stores generate more binders than the four names the BN254
    script substitutes by hand. *)

Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_Fp.
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

    Existing Instance bls24_509_field_parameters.
    Existing Instance bls24_509_frep.
    Existing Instance bls24_509_frep_ok.

    (* BLS24-509 uses 8 x 64-bit words (509 bits) *)
    Definition bls24_509_felem_copy : Syntax.func := (["out"; "in"], (nil : list string), bedrock_func_body:(
      coq:(cmd.store access_size.word (expr.var "out") (expr.load access_size.word (expr.var "in")));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (8)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (16)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (24)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (32)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (40)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (48))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (48)))));
      coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (56))) (expr.load access_size.word (expr.op bopname.add (expr.var "in") (expr.literal (56)))))
    )).

    Instance bls24_509_felem_copy_spec : spec_of felem_copy := spec_of_felem_copy.

    Lemma felem_copy_ok : program_logic_goal_for_function! bls24_509_felem_copy.
    Proof.
      cbv beta delta [program_logic_goal_for].
      intros functions EnvContains pout px x out R tr mem0 [Hsep Hlen].
      seprewrite_in (felem_from_bytes pout out Hlen) Hsep.
      unfold FElem in Hsep.
      change (Memory.bytes_per_word 64) with 8 in Hsep.
      destruct x as [xl xpf]; simpl proj1_sig in *.
      change felem_size_in_words with 8%nat in xpf.
      destruct xl as [| x0 [| x1 [| x2 [| x3 [| x4 [| x5 [| x6 [| x7 []]]]]]]]];
        try discriminate.
      assert (Hlen64 : Datatypes.length out = Pos.to_nat 64)
        by (change (Z.to_nat felem_size_in_bytes) with (Pos.to_nat 64) in Hlen;
            exact Hlen).
      rewrite Hlen64 in Hsep; rewrite Nat.eqb_refl in Hsep.
      set (ys := bs2ws (Pos.to_nat 8) out) in Hsep.
      assert (Hyslen: length ys = 8%nat)
        by (subst ys;
            change (Pos.to_nat 8) with (Z.to_nat (Memory.bytes_per_word 64));
            change 8%nat with felem_size_in_words;
            apply bs2ws_felem_length; exact Hlen).
      destruct ys as [| y0 [| y1 [| y2 [| y3 [| y4 [| y5 [| y6 [| y7 []]]]]]]]];
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
      cbv match beta delta [WeakestPrecondition.func bls24_509_felem_copy].
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
      subst.
      ecancel_assumption.
    Qed.

End FelemCopy.
