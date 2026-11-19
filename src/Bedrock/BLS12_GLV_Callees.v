(** * BLS12_GLV_Callees — the two GLV-specific callees, with proofs.

    [BLS12_GLV_Prog.glv_prog] calls, besides the curve operations:
    - ["shift_scalar"] on a TWO-word bignum (the low bit into a word
      cell, the bignum shifted right by one).  [BignumShift.shift_scalar]
      is the four-word version (hard-coded loads); [shift_scalar2_func]
      here is the two-word one, written with two locals and no stack, and
      [shift_scalar2_ok] proves it against [BLS12_GLV_Prog.spec_of_shift_scalar].
    - the conditional move, here ["glv_cmov"]:
        if (load pc) { copy(outx, x2); copy(outy, y2); copy(outz, z2) }
      which is the in-place move aux := if c = 0 then aux else Q when the
      output buffers ARE the first input (the program's calls), proved
      against [BLS12_GLV_Prog.CmovInplaceOK] from fiat-crypto's
      [spec_of_felem_copy].  It branches on the bit: variable time (the
      GLV path is for public scalars only). *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith Lia List.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Bedrock.Group.CurveAdd.BignumShift.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Require Import Bedrock.BLS12_GLV_Prog.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section Bodies.
  Context {width : Z} {BW : Bitwidth width}.
  Context {field_parameters : FieldParameters}.

  Local Notation bytes := (Memory.bytes_per_word width).

  (** shift_scalar(c2, scalar), two words:
        lo := scalar[0]; hi := scalar[1];
        *c2 := lo & 1;
        scalar[0] := (lo >> 1) + (hi << (width - 1));
        scalar[1] := hi >> 1 *)
  Definition shift_scalar2_body : cmd :=
    cmd.seq (cmd.set "lo" (expr.load access_size.word (expr.var "scalar")))
    (cmd.seq (cmd.set "hi" (expr.load access_size.word
                (expr.op bopname.add (expr.var "scalar") (expr.literal bytes))))
    (cmd.seq (cmd.store access_size.word (expr.var "c2")
                (expr.op bopname.and (expr.var "lo") (expr.literal 1)))
    (cmd.seq (cmd.store access_size.word (expr.var "scalar")
                (expr.op bopname.add
                   (expr.op bopname.sru (expr.var "lo") (expr.literal 1))
                   (expr.op bopname.slu (expr.var "hi") (expr.literal (width - 1)))))
             (cmd.store access_size.word
                (expr.op bopname.add (expr.var "scalar") (expr.literal bytes))
                (expr.op bopname.sru (expr.var "hi") (expr.literal 1)))))).

  Definition shift_scalar2_func : string * Syntax.func :=
    ("shift_scalar", (["c2"; "scalar"], @nil string, shift_scalar2_body)).

  Definition glv_cmov_body : cmd :=
    cmd.cond (expr.load access_size.word (expr.var "pc"))
      (cmd.seq (cmd.call [] felem_copy [expr.var "outx"; expr.var "x2"])
      (cmd.seq (cmd.call [] felem_copy [expr.var "outy"; expr.var "y2"])
               (cmd.call [] felem_copy [expr.var "outz"; expr.var "z2"])))
      cmd.skip.

  Definition glv_cmov_func : string * Syntax.func :=
    ("glv_cmov", (["outx"; "outy"; "outz"; "x1"; "y1"; "z1"; "x2"; "y2"; "z2"; "pc"],
                  @nil string, glv_cmov_body)).
End Bodies.

Section Proofs.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width}
          {mem : map.map word Byte.byte}.
  Context {locals : map.map String.string word}.
  Context {ext_spec : bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Local Notation bytes := (Memory.bytes_per_word width).
  Local Notation eval n x := (Positional.eval (uweight width) n (List.map word.unsigned x)).

  Add Ring __wring_glv: (@word.ring_theory width word word_ok)
    (preprocess [autorewrite with rew_word_morphism],
     morphism (@word.ring_morph width word word_ok),
     constants [Properties.word_cst]).

  Lemma eval2_mod2 (w0 w1 : word) :
    eval 2 [w0; w1] mod 2 = word.unsigned (word.and w0 (word.of_Z 1)).
  Proof.
    rewrite word.unsigned_and_nowrap, word.unsigned_of_Z_1.
    replace 1 with (Z.ones 1) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
    cbn [List.map].
    rewrite Positional.eval_cons by reflexivity.
    rewrite uweight_eval_shift; [| destruct width_cases; lia | reflexivity].
    rewrite uweight_0, uweight_1, Z.mul_1_l.
    rewrite Zplus_mod.
    replace (2 ^ width) with (2 * 2 ^ (width - 1))
      by (rewrite <- Z.pow_succ_r by (destruct width_cases; lia); f_equal; lia).
    rewrite <- Z.mul_assoc, (Z.mul_comm 2), Z_mod_mult, Z.add_0_r, Zmod_mod.
    reflexivity.
  Qed.

  Lemma shift_scalar2_ok functions :
    map.get functions "shift_scalar" = Some (snd (shift_scalar2_func (width:=width))) ->
    BLS12_GLV_Prog.spec_of_shift_scalar functions.
  Proof.
    intros Henv.
    cbv [BLS12_GLV_Prog.spec_of_shift_scalar].
    intros pc px c x R tr m Hm.
    eapply WeakestPreconditionProperties.start_func; [ exact Henv | ].
    cbv match beta delta [WeakestPrecondition.func shift_scalar2_func snd shift_scalar2_body].
    pose proof Hm as Hm'.
    destruct Hm' as (m1 & m2 & _ & Hb & _).
    destruct Hb as (m3 & m4 & _ & Hb & _).
    cbv [Bignum] in Hb. destruct Hb as (m5 & m6 & _ & [_ Hlen] & _).
    destruct x as [|w0 [|w1 [|]]]; cbn in Hlen; try lia. clear Hlen m1 m2 m3 m4 m5 m6.
    cbv [Bignum] in Hm.
    assert (E : forall (P : Prop) (q : mem -> Prop), P -> Lift1Prop.iff1 (sep (emp P) q) q).
    { intros P q HP mm. rewrite sep_emp_l. tauto. }
    seprewrite_in (E (Datatypes.length [w0; w1] = 2%nat)
                     (array scalar (word.of_Z bytes) px [w0; w1]) eq_refl) Hm.
    cbn [array] in Hm.
    repeat straightline.
    (* lo := load scalar *)
    eexists; split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.get WeakestPrecondition.load dlet.dlet].
      eexists; split; [ subst l; repeat (first [ apply map.get_put_same | rewrite map.get_put_diff by congruence ]) | ].
      eexists; split; [ eapply load_word_of_sep; ecancel_assumption | reflexivity ]. }
    cbv [dlet.dlet].
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    (* hi := load (scalar + bytes) *)
    eexists; split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.get WeakestPrecondition.load WeakestPrecondition.literal dlet.dlet].
      eexists; split; [ subst l; repeat (first [ apply map.get_put_same | rewrite map.get_put_diff by congruence ]) | ].
      eexists; split.
      { cbv [Semantics.interp_binop]. eapply load_word_of_sep. ecancel_assumption. }
      reflexivity. }
    cbv [dlet.dlet].
    repeat straightline.
    all: repeat (
      first
      [ progress (cbv [dlet.dlet] in * )
      | lazymatch goal with
        | |- exists a : word.rep, WeakestPrecondition.dexpr _ _ _ a /\ _ =>
          eexists; split;
          [ cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
            repeat (eexists; split;
                    [ subst l; repeat (first [ apply map.get_put_same
                                             | rewrite map.get_put_diff by congruence ]) | ]);
            reflexivity
          | ]
        | |- store access_size.word _ _ _ _ =>
          eapply store_word_of_sep; [ ecancel_assumption | intros ?m ?Hm ]
        | |- WeakestPrecondition.cmd _ (cmd.seq _ _) _ _ _ _ =>
          unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]
        | |- WeakestPrecondition.cmd _ (cmd.store _ _ _) _ _ _ _ =>
          unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body]
        end ]).
    cbv [Semantics.interp_binop] in Hm2.
    cbv [list_map list_map_body]. split; [ reflexivity | ].
    exists (word.and w0 (word.of_Z 1)), (bignum_shiftr 2 [w0; w1]).
    split; [ reflexivity | ].
    split; [ apply eval_shift; reflexivity | ].
    split; [ apply eval2_mod2 | ].
    cbv [Bignum]. seprewrite (E (Datatypes.length (bignum_shiftr 2 [w0; w1]) = 2%nat)
                       (array scalar (word.of_Z bytes) px (bignum_shiftr 2 [w0; w1])) eq_refl).
    cbv [bignum_shiftr]. cbn [seq List.map nth_default nth_error Nat.sub List.app array].
    ecancel_assumption.
  Qed.
  Local Notation FElem := Compilation2.FElem.

  Local Ltac solve_mapget :=
    first [ apply map.get_put_same
          | (rewrite !map.get_put_diff by congruence;
             first [ apply map.get_put_same | eassumption | reflexivity ])
          | eassumption
          | reflexivity ].

  Local Ltac eval_call_args :=
    repeat match goal with
           | x := _ : @Interface.map.rep _ _ _ |- _ => subst x
           end;
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.dexpr
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | (eexists; split; [ solve [ solve_mapget ] | ])
      | (eexists; split; [ exact eq_refl | ]) ]).

  Lemma glv_cmov_ok functions :
    map.get functions "glv_cmov" = Some (snd (glv_cmov_func (field_parameters:=field_parameters))) ->
    spec_of_felem_copy functions ->
    CmovInplaceOK "glv_cmov" functions.
  Proof.
    intros Henv Hcopy.
    cbv [CmovInplaceOK].
    change CompilationAbstract.FElem with Compilation2.FElem.
    intros pX pY pZ pX2 pY2 pZ2 pc X Y Z X2 Y2 Z2 c R tr m Hm.
    eapply WeakestPreconditionProperties.start_func; [ exact Henv | ].
    cbv match beta delta [WeakestPrecondition.func glv_cmov_func snd glv_cmov_body].
    repeat straightline.
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    exists c. split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.get WeakestPrecondition.load dlet.dlet].
      eexists; split; [ subst l; solve_mapget | ].
      eexists; split; [ eapply load_word_of_sep; ecancel_assumption | reflexivity ]. }
    split.
    - intros Hc.
      assert (Hb : word.eqb c (word.of_Z 0) = false).
      { rewrite word.unsigned_eqb, word.unsigned_of_Z_0. apply Z.eqb_neq. exact Hc. }
      rewrite Hb.
      unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
      unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
      eexists. split. { solve [ eval_call_args ]. }
      eapply Semantics.weaken_call.
      1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
      intros tr5 m5 rets5 Hp5. cbv beta in Hp5.
      destruct Hp5 as (Hr5 & Ht5 & Hm5). subst rets5. subst tr5.
      eexists. split. { exact eq_refl. }
      unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
      unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
      eexists. split. { solve [ eval_call_args ]. }
      eapply Semantics.weaken_call.
      1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
      intros tr6 m6 rets6 Hp6. cbv beta in Hp6.
      destruct Hp6 as (Hr6 & Ht6 & Hm6). subst rets6. subst tr6.
      eexists. split. { exact eq_refl. }
      unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
      eexists. split. { solve [ eval_call_args ]. }
      eapply Semantics.weaken_call.
      1: { eapply felem_copy_HFelemCopy; [ exact Hcopy | ecancel_assumption ]. }
      intros tr7 m7 rets7 Hp7. cbv beta in Hp7.
      destruct Hp7 as (Hr7 & Ht7 & Hm7). subst rets7. subst tr7.
      eexists. split. { exact eq_refl. }
      cbv [list_map list_map_body]. split; [ reflexivity | ]. split; [ reflexivity | ].
      ecancel_assumption.
    - intros Hc.
      assert (Hb : word.eqb c (word.of_Z 0) = true).
      { rewrite word.unsigned_eqb, word.unsigned_of_Z_0. apply Z.eqb_eq. exact Hc. }
      rewrite Hb.
      unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
      cbv [list_map list_map_body]. split; [ reflexivity | ]. split; [ reflexivity | ].
      ecancel_assumption.
  Qed.
End Proofs.
