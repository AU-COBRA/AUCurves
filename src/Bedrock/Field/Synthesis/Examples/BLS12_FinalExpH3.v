(**
 * BLS12-381 Final Exponentiation: H3 Store Helper (Fast v4)
 * Uses per-store peel+normalize+ecancel instead of repeat straightline.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import bedrock2.SepCalls.
Require Import bedrock2.SepAutoArray.
Require Import bedrock2.Scalars.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section H3Store.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Definition h3_limbs : list word :=
    [ word.of_Z 0xe516c3f438e3ba79; word.of_Z 0xfa9912aae208ccf1;
      word.of_Z 0x905ce937335d5b68; word.of_Z 0xc71a2629b0dea236;
      word.of_Z 0x83774940996754c8; word.of_Z 0x21d160aeb6a1e799;
      word.of_Z 0x2ed0b283ed237db4; word.of_Z 0x915c97f36c6f1821;
      word.of_Z 0x67f17fcbde783765; word.of_Z 0x2378b9039096d1b7;
      word.of_Z 0x7988f8761bdc51dc; word.of_Z 0x2076995003fc77a1;
      word.of_Z 0x827eca0ba621315b; word.of_Z 0xe5a72bce8d63cb9f;
      word.of_Z 0xf68f7764c28b6f8a; word.of_Z 0x2f230063cf081517;
      word.of_Z 0x94506632528d6a9a; word.of_Z 0xd3cde88eeb996ca3;
      word.of_Z 0xc0bd38c3195c899e; word.of_Z 0x000f686b3d807d01 ].

  Definition h3_store_cmd : Syntax.cmd.cmd :=
    BLS12_Pairing.cmd_seq_list [
      cmd.store Syntax.access_size.word (expr.var "h3") (expr.literal 0xe516c3f438e3ba79);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 8)) (expr.literal 0xfa9912aae208ccf1);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 16)) (expr.literal 0x905ce937335d5b68);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 24)) (expr.literal 0xc71a2629b0dea236);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 32)) (expr.literal 0x83774940996754c8);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 40)) (expr.literal 0x21d160aeb6a1e799);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 48)) (expr.literal 0x2ed0b283ed237db4);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 56)) (expr.literal 0x915c97f36c6f1821);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 64)) (expr.literal 0x67f17fcbde783765);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 72)) (expr.literal 0x2378b9039096d1b7);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 80)) (expr.literal 0x7988f8761bdc51dc);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 88)) (expr.literal 0x2076995003fc77a1);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 96)) (expr.literal 0x827eca0ba621315b);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 104)) (expr.literal 0xe5a72bce8d63cb9f);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 112)) (expr.literal 0xf68f7764c28b6f8a);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 120)) (expr.literal 0x2f230063cf081517);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 128)) (expr.literal 0x94506632528d6a9a);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 136)) (expr.literal 0xd3cde88eeb996ca3);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 144)) (expr.literal 0xc0bd38c3195c899e);
      cmd.store Syntax.access_size.word (expr.op bopname.add (expr.var "h3") (expr.literal 152)) (expr.literal 0x000f686b3d807d01)
    ].

  Lemma h3_store_limbs_wp :
    forall call t (m : mem) l (a_h3 : word) (oldws : list word) R,
      length oldws = 20%nat ->
      map.get l "h3" = Some a_h3 ->
      (array scalar (word.of_Z 8) a_h3 oldws ⋆ R) m ->
      WeakestPrecondition.cmd call h3_store_cmd t m l
        (fun t' m' l' =>
          t' = t /\ l' = l /\
          (array scalar (word.of_Z 8) a_h3 h3_limbs ⋆ R) m').
  Proof.
    intros call0 t0 m0 l0 a oldws R Hlen Hget Hsep.
    destruct oldws as [|o0 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o1 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o2 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o3 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o4 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o5 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o6 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o7 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o8 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o9 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o10 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o11 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o12 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o13 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o14 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o15 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o16 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o17 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o18 r]; [simpl in Hlen; discriminate|].
    destruct r as [|o19 r]; [simpl in Hlen; discriminate|].
    destruct r; [|simpl in Hlen; discriminate]. clear Hlen.

    Local Ltac solve_dexpr :=
      cbv [DEXPR dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
           get literal Semantics.interp_binop];
      repeat (eexists; split; [first [exact eq_refl | eassumption] |]);
      try exact eq_refl.

    Local Ltac peel_array_head_in H :=
      lazymatch type of H with
      | context [array scalar ?sz ?base (?hd :: ?tl)] =>
        change (array scalar sz base (hd :: tl))
          with (sep (scalar base hd) (array scalar sz (word.add base sz) tl)) in H
      end.

    Local Ltac normalize_addr_in H :=
      let base := match goal with Hg : map.get _ "h3" = Some ?a |- _ => a end in
      repeat match type of H with
      | context [word.add (word.add base (word.of_Z ?x)) (word.of_Z ?y)] =>
        ring_simplify (word.add (word.add base (word.of_Z x)) (word.of_Z y)) in H
      end.

    (* Full normalize: reduce scancel_asm residuals in hypothesis *)
    Local Ltac normalize_hyp H :=
      let base := match goal with Hg : map.get _ "h3" = Some ?a |- _ => a end in
      try (replace (word.sub base base) with (@word.of_Z 64 _ 0) in H by ring;
           change (word.unsigned (@word.of_Z 64 _ 0)) with 0 in H);
      try (cbv [Z.div Z.div_eucl Z.to_nat ListDef.firstn ListDef.skipn
                PosDef.Pos.to_nat Pos.iter_op Nat.add Z.of_nat
                Pos.of_succ_nat Pos.succ Z.mul seps List.fold_right] in H);
      try match type of H with context [word.of_Z (Z.pos (8 * ?p))] =>
        let v := eval cbv in (Z.pos (8 * p)) in
        change (word.of_Z (Z.pos (8 * p))) with (@word.of_Z 64 _ v) in H
      end;
      try peel_array_head_in H;
      try normalize_addr_in H.

    Local Ltac fast_store_step :=
      eexists; split; [solve [solve_dexpr] |];
      eexists; split; [solve [solve_dexpr] |];
      eapply Scalars.store_word_of_sep;
      [ (* Sep goal: find scalar in hypothesis *)
        cbv [Semantics.interp_binop]; ecancel_assumption
      | (* Continuation: intro, clear old, normalize for next *)
        cbv [Semantics.interp_binop]; cbv beta;
        let m := fresh "m" in let H := fresh "H" in
        intros m H;
        repeat match goal with
        | Hold : (_ ⋆ _) ?mold |- _ =>
          lazymatch mold with m => fail | _ => clear Hold end
        end;
        normalize_hyp H ].

    unfold h3_store_cmd, BLS12_Pairing.cmd_seq_list.
    cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].

    (* Store 1: scancel_asm handles initial array directly *)
    eexists; split; [solve [solve_dexpr] |].
    eexists; split; [solve [solve_dexpr] |].
    eapply Scalars.store_word_of_sep; [solve [scancel_asm] |].
    cbv [Semantics.interp_binop]; cbv beta. intros m1 H1.
    clear Hsep.
    normalize_hyp H1.

    (* Stores 2-20 *)
    do 19 fast_store_step.

    (* Final postcondition *)
    (* Final postcondition: t = t /\ l = l /\ (array h3_limbs ⋆ R) m *)
    split; [exact eq_refl |].
    split; [exact eq_refl |].
    (* Unfold array in goal to expose 20 scalars with normalized addresses *)
    cbv [h3_limbs]. cbn [array].
    repeat match goal with
    |- context[word.add (word.add ?x ?y) ?z] =>
      ring_simplify (word.add (word.add x y) z)
    end.
    (* Reduce empty arrays in hypothesis to emp True *)
    match goal with Hlast : (_ ⋆ _) _ |- _ => cbn [array] in Hlast end.
    ecancel_assumption.
  Qed.

End H3Store.
