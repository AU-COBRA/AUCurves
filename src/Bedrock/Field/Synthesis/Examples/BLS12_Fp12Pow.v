(** * BLS12-381 Fp12 exponentiation by a 256-bit scalar: a proved bedrock2 function.

    [bls12_Fp12_pow] raises an Fp12 element to a 256-bit scalar (four little-endian 64-bit
    limbs) by left-to-right square-and-multiply over the verified Fp12 leaves, as
    [BLS12_G1_ScalarMul.g1_scalar_mul] does over the point operations:

      result := 1                                   ([BLS12_Pairing.fp12_set_one])
      for i = 255 down to 0:
        result := result^2                          ("bls12_Fp12_square", in place)
        if bit i of the scalar is set:
          result := result * base                   ("bls12_Fp12_mul", in place)

    - [fp12_pow_body_wp]: the body computes [fp12_pow_model] (= [dadd_from] of
      [BLS12_G1_ScalarMul] with the product and the square of [Theory.BLS12Pairing.Pairing])
      on the field values, from the contracts of the three leaves it calls:
      ["bls12_Fp12_mul"] and ["bls12_Fp12_square"] ([AbstractField.binop_spec] /
      [unop_spec], which allow the output to alias an input) and ["bls12_from_word"]
      ([PrimeField.spec_of_from_word]);
    - [bls12_Fp12_pow_ok]: the function satisfies [spec_of_bls12_Fp12_pow].

    The branch on the scalar bit makes the running time depend on the scalar (variable
    time).  No Admitted, no Axiom. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith Lia.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CycExpFunctional.
Require Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_G1_ScalarMul.
Require Theory.BLS12Pairing.Pairing.
Require Import bedrock2.Loops.

Module P := Theory.BLS12Pairing.Pairing.

Import BinInt String List.ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section BLS12_Fp12Pow.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.
    Existing Instances bls12_field_parameters bls12_frep bls12_frep_ok.

    Existing Instance BLS12_CycExp.bls12_pf_params.
    Existing Instance BLS12_CycExp.bls12_pf_params_ok.
    Existing Instance prime_field_parameters.
    Existing Instance BLS12_CycExp.bls12_Fp_rep.
    Existing Instance BLS12_CycExp.bls12_Fp_rep_ok.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Existing Instance BLS12_CycExp.bls12_Fp2_params'.
    Existing Instance BLS12_CycExp.bls12_Fp2_rep'.
    Existing Instance BLS12_CycExp.bls12_Fp6_params'.
    Existing Instance BLS12_CycExp.bls12_Fp6_rep'.
    Existing Instance BLS12_CycExp.bls12_Fp12_params'.
    Existing Instance BLS12_CycExp.bls12_Fp12_rep'.

    Local Notation bls12_Fp12_params' := BLS12_CycExp.bls12_Fp12_params'.
    Local Notation bls12_Fp12_rep' := BLS12_CycExp.bls12_Fp12_rep'.

    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque BLS12_CycExp.bls12_Fp6_params'.
    Local Typeclasses Opaque BLS12_CycExp.bls12_Fp2_params'.

    Local Notation word := BasicC64Semantics.word.
    Local Notation mem := BasicC64Semantics.mem.
    Local Notation locals := BasicC64Semantics.locals.

    (** ** The leaves *)

    Definition fp12_mul_name : string := AbstractField.mul (F:=Fp12).
    Definition fp12_sqr_name : string := AbstractField.square (F:=Fp12).

    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep') AbstractField.un_square.

    (** ** The program *)

    (** [i := i - 1; result := result^2;
         a := scalar + ((i >> 6) << 3); bit := (load(a) >> (i & 63)) & 1;
         if bit { result := result * base }]. *)
    Definition fp12_pow_loop_body : Syntax.cmd :=
      cmd.seq (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
      (cmd.seq (cmd.call [] fp12_sqr_name [expr.var "result"; expr.var "result"])
      (cmd.seq (cmd.set "a"
                  (expr.op bopname.add (expr.var "scalar")
                     (expr.op bopname.slu
                        (expr.op bopname.sru (expr.var "i") (expr.literal 6))
                        (expr.literal 3))))
      (cmd.seq (cmd.set "bit"
                  (expr.op bopname.and
                     (expr.op bopname.sru
                        (expr.load access_size.word (expr.var "a"))
                        (expr.op bopname.and (expr.var "i") (expr.literal 63)))
                     (expr.literal 1)))
         (cmd.cond (expr.var "bit")
            (cmd.call [] fp12_mul_name
               [expr.var "result"; expr.var "result"; expr.var "base"])
            cmd.skip)))).

    Definition fp12_pow_body : Syntax.cmd :=
      cmd.seq (BLS12_Pairing.fp12_set_one "result")
      (cmd.seq (cmd.set "i" (expr.literal 256))
         (cmd.while (expr.var "i") fp12_pow_loop_body)).

    Definition bls12_Fp12_pow_func : Syntax.func :=
      (["result"; "base"; "scalar"], [], fp12_pow_body).

    Definition bls12_Fp12_pow : string * Syntax.func := ("bls12_Fp12_pow", bls12_Fp12_pow_func).

    (** ** The model: square-and-multiply in [Pairing]'s Fp12 *)

    Definition fp12_pow_model (s : list Z) (x : Fp12) : Fp12 :=
      dadd_from (P.fp12_mul PrimeField.M_pos) (fun a => P.fp12_mul PrimeField.M_pos a a)
        s x 256 (P.fp12_one PrimeField.M_pos).

    (** ** Word lemmas (as in [BLS12_G2_ScalarMul]) *)

    Lemma unsigned_small (v : Z) :
      0 <= v < 2 ^ 64 -> word.unsigned (word.of_Z v : word) = v.
    Proof. intros. apply word.unsigned_of_Z_nowrap. lia. Qed.

    Lemma word_i_and_63 (v : Z) :
      0 <= v < 256 ->
      word.unsigned (word.and (word.of_Z v) (word.of_Z 63) : word) = v mod 64.
    Proof.
      intros Hv. rewrite word.unsigned_and_nowrap, !unsigned_small by lia.
      change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
    Qed.

    Lemma word_limb_addr (sp : word) (v : Z) :
      0 <= v < 256 ->
      word.add sp (word.slu (word.sru (word.of_Z v) (word.of_Z 6)) (word.of_Z 3))
      = word.add sp (word.of_Z (Z.of_nat 0 * 32 + Z.of_nat (Z.to_nat (v / 64)) * 8)).
    Proof.
      intros Hv. f_equal. apply word.unsigned_inj.
      assert (Hq : 0 <= v / 64 < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      rewrite word.unsigned_slu by (rewrite unsigned_small by lia; lia).
      rewrite word.unsigned_sru_nowrap by (rewrite unsigned_small by lia; lia).
      rewrite !unsigned_small by lia.
      rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      rewrite ?Z2Nat.id by lia.
      unfold word.wrap. rewrite Z.mod_small by lia.
      change (2 ^ 6) with 64. change (2 ^ 3) with 8. lia.
    Qed.

    Lemma word_bit (x : word) (k : word) :
      0 <= word.unsigned k < 64 ->
      word.unsigned (word.and (word.sru x k) (word.of_Z 1) : word)
      = Z.b2z (Z.testbit (word.unsigned x) (word.unsigned k)).
    Proof.
      intros Hk. rewrite word.unsigned_and_nowrap.
      rewrite word.unsigned_sru_nowrap by lia.
      rewrite unsigned_small by lia.
      change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
      rewrite Z.testbit_spec' by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
    Qed.

    Lemma word_sub_1 (v : nat) :
      (0 < v <= 256)%nat ->
      word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1) = (word.of_Z (Z.of_nat (v - 1)) : word).
    Proof.
      intros Hv. apply word.unsigned_inj.
      rewrite word.unsigned_sub, !unsigned_small by lia.
      unfold word.wrap. rewrite Z.mod_small by lia. lia.
    Qed.

    Lemma word_of_nat_zero (v : nat) :
      (v <= 256)%nat -> word.unsigned (word.of_Z (Z.of_nat v) : word) = Z.of_nat v.
    Proof. intros. apply unsigned_small. lia. Qed.

    Lemma scalar_bit_word (s : list word) (v : nat) :
      (v < 256)%nat ->
      scalar_bit (List.map word.unsigned s) v
      = Z.testbit (word.unsigned (nth (Z.to_nat (Z.of_nat v / 64)) s (word.of_Z 0)))
                  (Z.of_nat v mod 64).
    Proof.
      intros Hv. unfold scalar_bit.
      replace (Z.to_nat (Z.of_nat v / 64)) with (Nat.div v 64)
        by (rewrite <- (Nat2Z.id (Nat.div v 64)), Nat2Z.inj_div; reflexivity).
      replace (Z.of_nat v mod 64) with (Z.of_nat (Nat.modulo v 64))
        by (rewrite Nat2Z.inj_mod; reflexivity).
      f_equal.
      replace 0 with (word.unsigned (word.of_Z 0 : word)) at 1
        by apply word.unsigned_of_Z_0.
      apply map_nth.
    Qed.

    (** ** The proof *)

    Ltac solve_get :=
      repeat (rewrite map.get_put_diff by congruence);
      first [ rewrite map.get_put_same; reflexivity | eassumption ].

    Ltac peel :=
      cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body];
      fold WeakestPrecondition.cmd.

    Ltac eval_dexprs :=
      cbv [WeakestPrecondition.dexprs WeakestPrecondition.dexpr list_map list_map_body
           WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.literal WeakestPrecondition.get dlet.dlet];
      repeat (eexists; split; [solve_get|]);
      try reflexivity.

    Local Notation sqr12 := (fun a => P.fp12_mul PrimeField.M_pos a a).

    Definition fp12_pow_inv (tr : Semantics.trace) (presult pbase sp : word) (s : list word)
        (base_val : Fp12_felem) (Rr : mem -> Prop)
        (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\ (v <= 256)%nat /\
      map.get l "result" = Some presult /\ map.get l "base" = Some pbase /\
      map.get l "scalar" = Some sp /\
      map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
      exists r : Fp12_felem,
        Fp12_bounded Fp12_tight r /\
        dadd_from (P.fp12_mul PrimeField.M_pos) sqr12 (List.map word.unsigned s)
          (Fp12_feval base_val) v (Fp12_feval r)
        = fp12_pow_model (List.map word.unsigned s) (Fp12_feval base_val) /\
        (FElem_Fp12 presult r ⋆ (FElem_Fp12 pbase base_val ⋆
           (BLS12_MSM.ScalarsArray sp [s] ⋆ Rr))) m.

    Lemma fp12_pow_body_wp functions
        (HFp12mul : BLS12_CycExp.spec_of_Fp12_mul functions)
        (HFp12sqr : spec_of_Fp12_sqr functions)
        (HFfromword : BLS12_CycExp.spec_of_Fp_from_word functions)
        (presult pbase sp : word) (old base_val : Fp12_felem) (s : list word)
        (Rr : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals) :
      length s = 4%nat ->
      Fp12_bounded Fp12_tight base_val ->
      (FElem_Fp12 presult old ⋆ (FElem_Fp12 pbase base_val ⋆
         (BLS12_MSM.ScalarsArray sp [s] ⋆ Rr))) m ->
      map.get l "result" = Some presult -> map.get l "base" = Some pbase ->
      map.get l "scalar" = Some sp ->
      WeakestPrecondition.cmd functions fp12_pow_body tr m l
        (fun tr' m' l' =>
           tr' = tr /\
           exists out : Fp12_felem,
             Fp12_feval out = fp12_pow_model (List.map word.unsigned s) (Fp12_feval base_val) /\
             Fp12_bounded Fp12_tight out /\
             (FElem_Fp12 presult out ⋆ (FElem_Fp12 pbase base_val ⋆
                (BLS12_MSM.ScalarsArray sp [s] ⋆ Rr))) m').
    Proof.
      intros Hlen Hbbase Hm Hlr Hlb Hls.
      cbv [fp12_pow_body].
      peel.
      (* result := 1 *)
      eapply (fp12_set_one_functional_wp functions HFfromword presult old).
      { exact Hlr. }
      { exact Hm. }
      intros m1 one12 Hb12 Hfe12 Hs12.
      (* i := 256 *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      cbv [dlet.dlet].
      eapply (Loops.while_localsmap (measure := nat)
                (fp12_pow_inv tr presult pbase sp s base_val Rr)
                Wf_nat.lt_wf 256%nat).
      { cbv [fp12_pow_inv]. split; [reflexivity|]. split; [lia|].
        do 4 (split; [solve_get|]).
        exists one12. split; [exact Hb12|]. split.
        - cbv [fp12_pow_model]. rewrite Hfe12. reflexivity.
        - exact Hs12. }
      intros v t mv lv Hinv.
      destruct Hinv as (-> & Hv & Hlr' & Hlb' & Hls' & Hli & r & Hbr & Hacc & Hmv).
      exists (word.of_Z (Z.of_nat v)). split.
      { eval_dexprs. }
      split.
      - intros Hne.
        assert (Hv0 : (0 < v)%nat).
        { destruct v; [|lia]. exfalso. apply Hne. apply word.unsigned_of_Z_0. }
        set (v' := (v - 1)%nat).
        cbv [fp12_pow_loop_body].
        peel. peel.
        eexists; split; [eval_dexprs|].
        cbv [dlet.dlet].
        cbv [Semantics.interp_binop].
        rewrite word_sub_1 by lia. fold v'.
        (* result := result^2 *)
        peel. peel.
        eexists; split; [eval_dexprs|].
        eapply Semantics.weaken_call.
        { eapply (HFp12sqr presult presult r r
                    (FElem_Fp12 pbase base_val ⋆ (BLS12_MSM.ScalarsArray sp [s] ⋆ Rr)) tr mv).
          split; [exact Hbr|].
          split; [eexists; ecancel_assumption|].
          ecancel_assumption. }
        cbv beta. intros t2 m2 rets [-> [<- [r2 [Hfe2 [Hb2 Hm2]]]]].
        cbv [AbstractField.un_model AbstractField.un_square AbstractField.Fsquare] in Hfe2.
        apply F12mul_eq in Hfe2.
        eexists; split; [reflexivity|].
        (* a := scalar + ((i >> 6) << 3) *)
        peel. peel.
        eexists; split; [eval_dexprs|].
        cbv [dlet.dlet].
        assert (Hv'256 : (v' < 256)%nat) by lia.
        set (limb := Z.to_nat (Z.of_nat v' / 64)).
        assert (Hlimb : (limb < 4)%nat).
        { unfold limb. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
          apply Z.div_lt_upper_bound; lia. }
        pose proof (BLS12_MSM.ScalarsArray_load_limb
                      (field_parameters := bls12_field_parameters)
                      (field_representation := bls12_frep)
                      eq_refl (fun p _ => p) (fun p => p) (F.zero, F.zero, F.zero)
                      sp [s] 0 limb
                      (FElem_Fp12 presult r2 ⋆ (FElem_Fp12 pbase base_val ⋆ Rr)) m2
                      ltac:(cbn; lia) Hlimb) as Hload.
        cbn [nth] in Hload.
        (* bit := (load(a) >> (i & 63)) & 1 *)
        peel. peel.
        eexists; split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get WeakestPrecondition.load dlet.dlet].
          eexists; split; [solve_get|].
          eexists; split.
          { cbv [Semantics.interp_binop].
            rewrite word_limb_addr by lia. apply Hload. ecancel_assumption. }
          eexists; split; [solve_get|].
          reflexivity. }
        cbv [dlet.dlet Semantics.interp_binop].
        set (bitw := word.and
                       (word.sru (nth limb s (word.of_Z 0))
                          (word.and (word.of_Z (Z.of_nat v')) (word.of_Z 63)))
                       (word.of_Z 1) : word).
        assert (Hbit : word.unsigned bitw
                       = Z.b2z (scalar_bit (List.map word.unsigned s) v')).
        { unfold bitw. rewrite word_bit by (rewrite word_i_and_63 by lia;
                                           pose proof (Z.mod_pos_bound (Z.of_nat v') 64); lia).
          rewrite word_i_and_63 by lia. rewrite scalar_bit_word by lia. reflexivity. }
        peel.
        eexists; split; [eval_dexprs|].
        replace v with (S v') in Hacc by lia.
        cbn [dadd_from] in Hacc. rewrite <- Hfe2 in Hacc.
        split.
        + intros Hb.
          assert (Hsb : scalar_bit (List.map word.unsigned s) v' = true).
          { destruct (scalar_bit (List.map word.unsigned s) v'); [reflexivity|].
            rewrite Hbit in Hb. cbn in Hb. congruence. }
          rewrite Hsb in Hacc.
          (* result := result * base *)
          peel.
          eexists; split; [eval_dexprs|].
          eapply Semantics.weaken_call.
          { eapply (HFp12mul presult presult pbase r2 r2 base_val
                      (FElem_Fp12 pbase base_val ⋆ (BLS12_MSM.ScalarsArray sp [s] ⋆ Rr)) tr m2).
            split; [exact Hb2|].
            split; [exact Hbbase|].
            split; [eexists; ecancel_assumption|].
            split; [eexists; ecancel_assumption|].
            ecancel_assumption. }
          cbv beta. intros t3 m3 rets [-> [<- [r3 [Hfe3 [Hb3 Hm3]]]]].
          cbv [AbstractField.bin_model AbstractField.bin_mul] in Hfe3.
          apply F12mul_eq in Hfe3.
          rewrite <- Hfe3 in Hacc.
          eexists; split; [reflexivity|].
          exists v'. split; [|lia].
          cbv [fp12_pow_inv]. split; [reflexivity|]. split; [lia|].
          do 4 (split; [solve_get|]).
          exists r3. split; [exact Hb3|]. split; [exact Hacc|]. ecancel_assumption.
        + intros Hb.
          assert (Hsb : scalar_bit (List.map word.unsigned s) v' = false).
          { destruct (scalar_bit (List.map word.unsigned s) v'); [|reflexivity].
            rewrite Hbit in Hb. cbn in Hb. congruence. }
          rewrite Hsb in Hacc.
          peel.
          exists v'. split; [|lia].
          cbv [fp12_pow_inv]. split; [reflexivity|]. split; [lia|].
          do 4 (split; [solve_get|]).
          exists r2. split; [exact Hb2|]. split; [exact Hacc|]. ecancel_assumption.
      - intros Hz.
        rewrite word_of_nat_zero in Hz by exact Hv.
        assert (v = 0%nat) as -> by lia.
        cbn [dadd_from] in Hacc.
        split; [reflexivity|].
        exists r. split; [exact Hacc|]. split; [exact Hbr|exact Hmv].
    Qed.

    (** ** The function *)

    Definition spec_of_bls12_Fp12_pow (functions : Semantics.env) : Prop :=
      forall (presult pbase sp : word) (old base_val : Fp12_felem) (s : list word)
             (Rr : mem -> Prop) (tr : Semantics.trace) (m : mem),
        length s = 4%nat ->
        Fp12_bounded Fp12_tight base_val ->
        (FElem_Fp12 presult old ⋆ (FElem_Fp12 pbase base_val ⋆
           (BLS12_MSM.ScalarsArray sp [s] ⋆ Rr))) m ->
        Semantics.call functions "bls12_Fp12_pow" tr m [presult; pbase; sp]
          (fun tr' m' rets =>
             rets = [] /\ tr = tr' /\
             exists out : Fp12_felem,
               Fp12_feval out = fp12_pow_model (List.map word.unsigned s) (Fp12_feval base_val) /\
               Fp12_bounded Fp12_tight out /\
               (FElem_Fp12 presult out ⋆ (FElem_Fp12 pbase base_val ⋆
                  (BLS12_MSM.ScalarsArray sp [s] ⋆ Rr))) m').

    Theorem bls12_Fp12_pow_ok functions :
      map.get functions "bls12_Fp12_pow" = Some bls12_Fp12_pow_func ->
      BLS12_CycExp.spec_of_Fp12_mul functions ->
      spec_of_Fp12_sqr functions ->
      BLS12_CycExp.spec_of_Fp_from_word functions ->
      spec_of_bls12_Fp12_pow functions.
    Proof.
      intros Henv HFp12mul HFp12sqr HFfromword presult pbase sp old base_val s Rr tr m
        Hlen Hbbase Hm.
      unfold Semantics.call.
      do 3 eexists. split; [exact Henv|].
      destruct (map.of_list_zip ["result"; "base"; "scalar"] [presult; pbase; sp])
        as [l0|] eqn:Hzip.
      2: { exfalso. cbn in Hzip. discriminate Hzip. }
      exists l0. split; [reflexivity|].
      cbn in Hzip. injection Hzip as <-.
      eapply Semantics.exec.weaken.
      { eapply WeakestPreconditionProperties.sound_cmd.
        eapply (fp12_pow_body_wp functions HFp12mul HFp12sqr HFfromword presult pbase sp
                  old base_val s Rr tr m); try exact Hlen; try exact Hbbase; try exact Hm;
          reflexivity. }
      intros tr' m' l' (-> & out & Hfe & Hb & Hm').
      exists []. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      exists out. split; [exact Hfe|]. split; [exact Hb|exact Hm'].
    Qed.

End BLS12_Fp12Pow.

Print Assumptions bls12_Fp12_pow_ok.
