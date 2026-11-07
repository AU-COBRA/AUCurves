(** * BLS12_G2_ScalarMulCT — constant-time G2 scalar multiplication (proved bedrock2).

    The G2 counterpart of [BLS12_G1_ScalarMulCT]: [g2_scalar_mul_ct]
    computes k P on E'(Fp2) with the scalar-independent sequence

      out := (px - px : 3b' : px - px) = (0 : 3b' : 0);
      for i = 255 down to 0:
        out := double(out);                       ("g2_curve_double_ip")
        bit := (scalar[i / 64] >> (i mod 64)) & 1;
        t   := out + P;                           ("g2_curve_add", out of place, always)
        ct_cswap(bit, out.c, t.c), c = x, y, z    (12 words each)

    [t] is a caller-provided scratch triple.  Constant time at the
    bedrock2 level in the same sense as G1 (see [BLS12_G1_ScalarMulCT]):
    no [cmd.cond], loop conditions on counters only, addresses from
    pointers and counters only; the scalar enters only as word-arithmetic
    operands and the [ct_cswap] mask.  Not a theorem about bedrock2's
    semantics; says nothing about the Fp2 leaves or the compiled Rust.

    Proved:
    - [g2_scalar_mul_ct_ok]: the function returns
      [BLS12_G2_ScalarMul.g2_smul_target] (the same value as the
      variable-time [g2_scalar_mul]) from the callee contracts (record
      [CtCallees2]);
    - [g2_scalar_mul_ct_closed]: the closed statement, with only the Fp2
      leaf contracts as premises: [pt_eq] to [k P] for on-curve P.

    No Admitted, no Axiom. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith List Lia.
From Stdlib Require Import RelationClasses Morphisms Setoid.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require bedrock2.Loops.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
Require Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Bedrock.Field.FieldExtensions.Compilation2_Fp2.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Crypto.Algebra.Ring.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Import Bedrock.Group.CurveAdd.CurveAddAF.
Require Import Bedrock.Group.CurveAdd.RcbLawsAF.
Require Import Bedrock.BLS12_G2_ThreeB.
Require Import Bedrock.BLS12_G2_Closed.
Require Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_MSM_Functional.
Require Import Bedrock.BLS12_G1_ScalarMul.
Require Bedrock.BLS12_MSM_Closed.
Require Import Bedrock.BLS12_G2_ScalarMul.
Require Import Bedrock.Group.CurveAdd.CtSwap.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Import Syntax BinInt String List.ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Local Notation Fp := (F PrimeField.M_pos).
Local Notation Fp2 := (Fp * Fp)%type.
Local Notation AFElem := Compilation2_Fp2.AFElem.

(* ================================================================== *)
(** ** 1. The bedrock2 program                                          *)
(* ================================================================== *)

Definition g2_curve_add_name : string := "g2_curve_add".

Definition g2_scalar_mul_ct_loop_body : Syntax.cmd :=
  cmd.seq (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
  (cmd.seq (cmd.call [] g2_curve_double_ip_name
              [expr.var "outx"; expr.var "outy"; expr.var "outz"])
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
  (cmd.seq (cmd.call [] g2_curve_add_name
              [expr.var "outx"; expr.var "px";
               expr.var "outy"; expr.var "py";
               expr.var "outz"; expr.var "pz";
               expr.var "tx"; expr.var "ty"; expr.var "tz"])
  (cmd.seq (cmd.call [] "ct_cswap" [expr.var "bit"; expr.var "outx"; expr.var "tx"])
  (cmd.seq (cmd.call [] "ct_cswap" [expr.var "bit"; expr.var "outy"; expr.var "ty"])
           (cmd.call [] "ct_cswap" [expr.var "bit"; expr.var "outz"; expr.var "tz"]))))))).

Definition g2_scalar_mul_ct_body : Syntax.cmd :=
  cmd.seq (cmd.call [] g2_sub_name [expr.var "outx"; expr.var "px"; expr.var "px"])
  (cmd.seq (cmd.call [] g2_sub_name [expr.var "outz"; expr.var "px"; expr.var "px"])
  (cmd.seq (cmd.call [] g2_three_b_name [expr.var "outy"])
  (cmd.seq (cmd.set "i" (expr.literal 256))
     (cmd.while (expr.var "i") g2_scalar_mul_ct_loop_body)))).

Definition g2_scalar_mul_ct_func : Syntax.func :=
  (["outx"; "outy"; "outz"; "tx"; "ty"; "tz"; "scalar"; "px"; "py"; "pz"], [],
   g2_scalar_mul_ct_body).

(** [ct_cswap] at the Fp2 representation (12 words). *)
Definition g2_ct_cswap_func : Syntax.func :=
  ct_cswap (word:=BasicC64Semantics.word)
    (@AbstractField.felem_size_in_words Fp2 _ _ _ _ _ bls12_Fp2_field_representation).

(* ================================================================== *)
(** ** 2. Correctness                                                   *)
(* ================================================================== *)

Section ProofCT.
  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls12_prime_parameters bls12_field_representation
    bls12_Fp2_field_parameters bls12_Fp2_field_representation
    bls12_prime_parameters_ok bls12_field_representation_ok.
  Existing Instance prime_field_parameters.
  Existing Instances bls12_field_parameters bls12_frep bls12_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation mem := BasicC64Semantics.mem.
  Local Notation locals := BasicC64Semantics.locals.
  Local Notation cadd := (@RcbLawsAF.cadd Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation cdbl := (@RcbLawsAF.cdbl Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation tight := (@AbstractField.tight_bounds Fp2 _ _ _ _ _ bls12_Fp2_field_representation).
  Local Notation FElemT := (AFElem (Some tight)).
  Local Notation Fsub := (@AbstractField.Fsub Fp2 bls12_Fp2_field_parameters).

  Local Notation nw2 := (@AbstractField.felem_size_in_words Fp2 _ _ _ _ _ bls12_Fp2_field_representation).

  Lemma g2_n_small : Z.of_nat nw2 < 2 ^ 64.
  Proof. vm_compute. reflexivity. Qed.

  Record CtCallees2 (functions : Semantics.env) : Prop := mkCtCallees2 {
    c2_add : spec_of_af_curve_add (F:=Fp2) g2_tb functions;
    c2_dbl : spec_of_af_curve_double_ip (F:=Fp2) g2_tb functions;
    c2_sub : spec_of_af_sub (F:=Fp2) functions;
    c2_tb : spec_of_af_three_b (F:=Fp2) g2_tb g2_three_b_name functions;
    c2_swap : map.get functions "ct_cswap" = Some g2_ct_cswap_func }.

  Lemma add_out_triple X1 X2 Y1 Y2 Z1 Z2 Xo Yo Zo :
    af_add_gallina (three_b_val:=g2_tb) X1 X2 Y1 Y2 Z1 Z2 = \<Xo, Yo, Zo\> ->
    cadd (X1, Y1, Z1) (X2, Y2, Z2) = (Xo, Yo, Zo).
  Proof. intros H. cbv [RcbLawsAF.cadd]. rewrite H. reflexivity. Qed.

  (** [ct_cswap] on two tight Fp2 elements. *)
  Lemma afelem_cswap_call (functions : Semantics.env)
      (Henv : map.get functions "ct_cswap" = Some g2_ct_cswap_func)
      (b : bool) (p1 p2 : word) (v1 v2 : Fp2) (R : mem -> Prop) tr m :
    (FElemT p1 v1 * FElemT p2 v2 * R)%sep m ->
    Semantics.call functions "ct_cswap" tr m [word.of_Z (Z.b2z b); p1; p2]
      (fun tr' m' rets =>
         rets = [] /\ tr = tr' /\
         (FElemT p1 (if b then v2 else v1) * FElemT p2 (if b then v1 else v2) * R)%sep m').
  Proof.
    intros Hm.
    unfold AFElem, Compilation2_Fp2.AFElem in Hm.
    destruct Hm as (m12 & mR & Hs & H12 & HR).
    destruct H12 as (m1 & m2 & Hs12 & H1 & H2).
    destruct H1 as (l1 & H1). destruct H2 as (l2 & H2).
    apply sep_emp_l in H1. destruct H1 as ((Hv1 & Hb1) & H1).
    apply sep_emp_l in H2. destruct H2 as ((Hv2 & Hb2) & H2).
    assert (Hm' : (Bignum nw2 p1 l1 * Bignum nw2 p2 l2 * R)%sep m).
    { exists m12, mR. split; [exact Hs|]. split; [|exact HR].
      exists m1, m2. split; [exact Hs12|]. split; assumption. }
    eapply Semantics.weaken_call.
    { exact (ct_cswap_call nw2 g2_n_small functions Henv b p1 p2 l1 l2 R tr m Hm'). }
    cbv beta. intros tr' m' rets (Hr & Htr & Hm2).
    split; [exact Hr|]. split; [exact Htr|].
    destruct Hm2 as (n12 & nR & Hs' & H12' & HR').
    destruct H12' as (n1 & n2 & Hs12' & H1' & H2').
    exists n12, nR. split; [exact Hs'|]. split; [|exact HR'].
    exists n1, n2. split; [exact Hs12'|].
    unfold AFElem, Compilation2_Fp2.AFElem.
    destruct b.
    - split.
      + exists l2. apply sep_emp_l. split; [split; assumption|]. exact H1'.
      + exists l1. apply sep_emp_l. split; [split; assumption|]. exact H2'.
    - split.
      + exists l1. apply sep_emp_l. split; [split; assumption|]. exact H1'.
      + exists l2. apply sep_emp_l. split; [split; assumption|]. exact H2'.
  Qed.

  Lemma drop3_2 (tx ty tz : word) (a b c : Fp2) (Rest : mem -> Prop) m :
    (FElemT tx a * FElemT ty b * FElemT tz c * Rest)%sep m ->
    (AFElem None tx a * AFElem None ty b * AFElem None tz c * Rest)%sep m.
  Proof.
    intros H.
    eapply Proper_sep_impl1; [ | reflexivity | exact H ].
    eapply Proper_sep_impl1; [ | apply Compilation2_Fp2.drop_bounds_AFElem ].
    eapply Proper_sep_impl1; apply Compilation2_Fp2.drop_bounds_AFElem.
  Qed.

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

  Lemma ct2_unsigned_small (v : Z) :
    0 <= v < 2 ^ 64 -> word.unsigned (word.of_Z v : word) = v.
  Proof. intros. apply word.unsigned_of_Z_nowrap. lia. Qed.

  Lemma ct2_word_i_and_63 (v : Z) :
    0 <= v < 256 ->
    word.unsigned (word.and (word.of_Z v) (word.of_Z 63) : word) = v mod 64.
  Proof.
    intros Hv. rewrite word.unsigned_and_nowrap, !ct2_unsigned_small by lia.
    change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
  Qed.

  Lemma ct2_word_limb_addr (sp : word) (v : Z) :
    0 <= v < 256 ->
    word.add sp (word.slu (word.sru (word.of_Z v) (word.of_Z 6)) (word.of_Z 3))
    = word.add sp (word.of_Z (Z.of_nat 0 * 32 + Z.of_nat (Z.to_nat (v / 64)) * 8)).
  Proof.
    intros Hv. f_equal. apply word.unsigned_inj.
    assert (Hq : 0 <= v / 64 < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite word.unsigned_slu by (rewrite ct2_unsigned_small by lia; lia).
    rewrite word.unsigned_sru_nowrap by (rewrite ct2_unsigned_small by lia; lia).
    rewrite !ct2_unsigned_small by lia.
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    rewrite ?Z2Nat.id by lia.
    unfold word.wrap. rewrite Z.mod_small by lia.
    change (2 ^ 6) with 64. change (2 ^ 3) with 8. lia.
  Qed.

  Lemma ct2_word_bit (x : word) (k : word) :
    0 <= word.unsigned k < 64 ->
    word.unsigned (word.and (word.sru x k) (word.of_Z 1) : word)
    = Z.b2z (Z.testbit (word.unsigned x) (word.unsigned k)).
  Proof.
    intros Hk. rewrite word.unsigned_and_nowrap.
    rewrite word.unsigned_sru_nowrap by lia.
    rewrite ct2_unsigned_small by lia.
    change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
    rewrite Z.testbit_spec' by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  Qed.

  Lemma ct2_word_sub_1 (v : nat) :
    (0 < v <= 256)%nat ->
    word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1) = (word.of_Z (Z.of_nat (v - 1)) : word).
  Proof.
    intros Hv. apply word.unsigned_inj.
    rewrite word.unsigned_sub, !ct2_unsigned_small by lia.
    unfold word.wrap. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma ct2_word_of_nat_zero (v : nat) :
    (v <= 256)%nat -> word.unsigned (word.of_Z (Z.of_nat v) : word) = Z.of_nat v.
  Proof. intros. apply ct2_unsigned_small. lia. Qed.

  Lemma ct2_scalar_bit_word (s : list word) (v : nat) :
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

  Lemma bit_word2 (bitw : word) (b : bool) :
    word.unsigned bitw = Z.b2z b -> bitw = word.of_Z (Z.b2z b).
  Proof.
    intros H. apply word.unsigned_inj. rewrite H.
    rewrite word.unsigned_of_Z_nowrap; [reflexivity|]. destruct b; cbn; lia.
  Qed.

  Definition ct2_loop_inv (functions : Semantics.env) (tr : Semantics.trace)
      (outx outy outz tx ty tz sp px py pz : word) (s : list word) (X Y Z : Fp2)
      (R : mem -> Prop) (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\ (v <= 256)%nat /\
    map.get l "outx" = Some outx /\ map.get l "outy" = Some outy /\
    map.get l "outz" = Some outz /\ map.get l "tx" = Some tx /\
    map.get l "ty" = Some ty /\ map.get l "tz" = Some tz /\
    map.get l "scalar" = Some sp /\
    map.get l "px" = Some px /\ map.get l "py" = Some py /\
    map.get l "pz" = Some pz /\
    map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
    exists ax ay az bx by_ bz : Fp2,
      dadd_from cadd cdbl (List.map word.unsigned s) (X, Y, Z) v (ax, ay, az)
      = g2_smul_target s (X, Y, Z) /\
      (FElemT outx ax * FElemT outy ay * FElemT outz az
       * AFElem None tx bx * AFElem None ty by_ * AFElem None tz bz
       * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m.

  Lemma g2_scalar_mul_ct_body_wp functions (HC : CtCallees2 functions)
      (outx outy outz tx ty tz sp px py pz : word) (ox0 oy0 oz0 tx0 ty0 tz0 X Y Z : Fp2)
      (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals) :
    length s = 4%nat ->
    (AFElem None outx ox0 * AFElem None outy oy0 * AFElem None outz oz0
     * AFElem None tx tx0 * AFElem None ty ty0 * AFElem None tz tz0
     * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
    map.get l "outx" = Some outx -> map.get l "outy" = Some outy ->
    map.get l "outz" = Some outz -> map.get l "tx" = Some tx ->
    map.get l "ty" = Some ty -> map.get l "tz" = Some tz ->
    map.get l "scalar" = Some sp ->
    map.get l "px" = Some px -> map.get l "py" = Some py -> map.get l "pz" = Some pz ->
    WeakestPrecondition.cmd functions g2_scalar_mul_ct_body tr m l
      (fun tr' m' l' =>
         tr' = tr /\
         exists ox oy oz tx1 ty1 tz1 : Fp2,
           (ox, oy, oz) = g2_smul_target s (X, Y, Z) /\
           (FElemT outx ox * FElemT outy oy * FElemT outz oz
            * AFElem None tx tx1 * AFElem None ty ty1 * AFElem None tz tz1
            * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m').
  Proof.
    intros Hlen Hm Hox Hoy Hoz Htx Hty Htz Hsp Hpx Hpy Hpz.
    destruct HC as [HA HD HS HT HW].
    cbv [g2_scalar_mul_ct_body].
    (* outx := px - px *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    eapply Semantics.weaken_call.
    { eapply (g2_sub_self_call functions HS outx px X ox0
                (AFElem None outy oy0 * AFElem None outz oz0
                 * AFElem None tx tx0 * AFElem None ty ty0 * AFElem None tz tz0
                 * BLS12_MSM.ScalarsArray sp [s] * FElemT py Y * FElemT pz Z * R)%sep tr m).
      ecancel_assumption. }
    cbv beta. intros tr1 m1 rets (-> & <- & Hm1).
    eexists; split; [reflexivity|].
    (* outz := px - px *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    eapply Semantics.weaken_call.
    { eapply (g2_sub_self_call functions HS outz px X oz0
                (FElemT outx (Fsub X X) * AFElem None outy oy0
                 * AFElem None tx tx0 * AFElem None ty ty0 * AFElem None tz tz0
                 * BLS12_MSM.ScalarsArray sp [s] * FElemT py Y * FElemT pz Z * R)%sep tr m1).
      ecancel_assumption. }
    cbv beta. intros tr2 m2 rets (-> & <- & Hm2).
    eexists; split; [reflexivity|].
    (* outy := 3b' *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    eapply Semantics.weaken_call.
    { eapply (HT outy oy0
                (FElemT outx (Fsub X X) * FElemT outz (Fsub X X)
                 * AFElem None tx tx0 * AFElem None ty ty0 * AFElem None tz tz0
                 * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep
                tr m2).
      ecancel_assumption. }
    cbv beta. intros tr3 m3 rets (-> & <- & Hm3).
    rewrite g2_bounds_eq in Hm3.
    eexists; split; [reflexivity|].
    (* i := 256 *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    cbv [dlet.dlet].
    eapply (Loops.while_localsmap (measure := nat)
              (ct2_loop_inv functions tr outx outy outz tx ty tz sp px py pz s X Y Z R)
              Wf_nat.lt_wf 256%nat).
    { cbv [ct2_loop_inv]. split; [reflexivity|]. split; [lia|].
      do 11 (split; [solve_get|]).
      exists (Fsub X X), g2_tb, (Fsub X X), tx0, ty0, tz0. split.
      - unfold g2_smul_target, smul_prog, g2_init. reflexivity.
      - ecancel_assumption. }
    intros v t mv lv Hinv.
    destruct Hinv as (-> & Hv & Hlx & Hly & Hlz & Hltx & Hlty & Hltz & Hls & Hlpx & Hlpy & Hlpz
                      & Hli & ax & ay & az & bx & by_ & bz & Hacc & Hmv).
    exists (word.of_Z (Z.of_nat v)). split.
    { eval_dexprs. }
    split.
    - intros Hne.
      assert (Hv0 : (0 < v)%nat).
      { destruct v; [|lia]. exfalso. apply Hne. apply word.unsigned_of_Z_0. }
      set (v' := (v - 1)%nat).
      cbv [g2_scalar_mul_ct_loop_body].
      peel. peel.
      eexists; split; [eval_dexprs|].
      cbv [dlet.dlet].
      cbv [Semantics.interp_binop].
      rewrite ct2_word_sub_1 by lia. fold v'.
      (* out := double(out) in place *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (HD outx outy outz ax ay az
                  (AFElem None tx bx * AFElem None ty by_ * AFElem None tz bz
                   * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep
                  tr mv).
        ecancel_assumption. }
      cbv beta. intros t2 md rets (-> & <- & dx & dy & dz & Hdg & Hmd).
      pose proof (double_ip_triple _ _ _ _ _ _ Hdg) as Hd. clear Hdg.
      eexists; split; [reflexivity|].
      peel. peel.
      eexists; split; [eval_dexprs|].
      cbv [dlet.dlet].
      assert (Hv'256 : (v' < 256)%nat) by lia.
      set (limb := Z.to_nat (Z.of_nat v' / 64)).
      assert (Hlimb : (limb < 4)%nat).
      { unfold limb. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
        apply Z.div_lt_upper_bound; lia. }
      pose proof (BLS12_MSM.ScalarsArray_load_limb (field_parameters := bls12_field_parameters)
                    (field_representation := bls12_frep)
                    eq_refl (fun p _ => p) (fun p => p) (F.zero, F.zero, F.zero)
                    sp [s] 0 limb
                    (FElemT outx dx * FElemT outy dy * FElemT outz dz
                     * AFElem None tx bx * AFElem None ty by_ * AFElem None tz bz
                     * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep md
                    ltac:(cbn; lia) Hlimb) as Hload.
      cbn [nth] in Hload.
      peel. peel.
      eexists; split.
      { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
             WeakestPrecondition.expr_body WeakestPrecondition.literal
             WeakestPrecondition.get WeakestPrecondition.load dlet.dlet].
        eexists; split; [solve_get|].
        eexists; split.
        { cbv [Semantics.interp_binop].
          rewrite ct2_word_limb_addr by lia. apply Hload. ecancel_assumption. }
        eexists; split; [solve_get|].
        reflexivity. }
      cbv [dlet.dlet Semantics.interp_binop].
      set (bitw := word.and
                     (word.sru (nth limb s (word.of_Z 0))
                        (word.and (word.of_Z (Z.of_nat v')) (word.of_Z 63)))
                     (word.of_Z 1) : word).
      set (sb := scalar_bit (List.map word.unsigned s) v').
      assert (Hbit : bitw = word.of_Z (Z.b2z sb)).
      { apply bit_word2. unfold bitw.
        rewrite ct2_word_bit by (rewrite ct2_word_i_and_63 by lia;
                                pose proof (Z.mod_pos_bound (Z.of_nat v') 64); lia).
        rewrite ct2_word_i_and_63 by lia. unfold sb. rewrite ct2_scalar_bit_word by lia.
        reflexivity. }
      clearbody bitw. subst bitw.
      (* t := out + P *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (HA outx px outy py outz pz tx ty tz dx X dy Y dz Z bx by_ bz
                  (BLS12_MSM.ScalarsArray sp [s] * R)%sep tr md).
        ecancel_assumption. }
      cbv beta. intros t3 ma rets (-> & <- & sx & sy & sz & Hsg & Hma).
      pose proof (add_out_triple _ _ _ _ _ _ _ _ _ Hsg) as Hs. clear Hsg.
      eexists; split; [reflexivity|].
      (* the three swaps *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (afelem_cswap_call functions HW sb outx tx dx sx
                  (FElemT outy dy * FElemT outz dz * FElemT ty sy * FElemT tz sz
                   * FElemT px X * FElemT py Y * FElemT pz Z * BLS12_MSM.ScalarsArray sp [s] * R)%sep
                  tr ma).
        ecancel_assumption. }
      cbv beta. intros t4 m4 rets (-> & <- & Hm4).
      eexists; split; [reflexivity|].
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (afelem_cswap_call functions HW sb outy ty dy sy
                  (FElemT outx (if sb then sx else dx) * FElemT tx (if sb then dx else sx)
                   * FElemT outz dz * FElemT tz sz
                   * FElemT px X * FElemT py Y * FElemT pz Z * BLS12_MSM.ScalarsArray sp [s] * R)%sep
                  tr m4).
        ecancel_assumption. }
      cbv beta. intros t5 m5 rets (-> & <- & Hm5).
      eexists; split; [reflexivity|].
      peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (afelem_cswap_call functions HW sb outz tz dz sz
                  (FElemT outx (if sb then sx else dx) * FElemT tx (if sb then dx else sx)
                   * FElemT outy (if sb then sy else dy) * FElemT ty (if sb then dy else sy)
                   * FElemT px X * FElemT py Y * FElemT pz Z * BLS12_MSM.ScalarsArray sp [s] * R)%sep
                  tr m5).
        ecancel_assumption. }
      cbv beta. intros t6 m6 rets (-> & <- & Hm6).
      eexists; split; [reflexivity|].
      exists v'. split; [|lia].
      cbv [ct2_loop_inv]. split; [reflexivity|]. split; [lia|].
      do 11 (split; [solve_get|]).
      replace v with (S v') in Hacc by lia.
      cbn [dadd_from] in Hacc. rewrite Hd in Hacc. fold sb in Hacc.
      exists (if sb then sx else dx), (if sb then sy else dy), (if sb then sz else dz),
        (if sb then dx else sx), (if sb then dy else sy), (if sb then dz else sz).
      split.
      + rewrite <- Hacc. destruct sb; [rewrite Hs|]; reflexivity.
      + assert (Hm7 : (AFElem None tx (if sb then dx else sx) * AFElem None ty (if sb then dy else sy)
                       * AFElem None tz (if sb then dz else sz)
                       * (FElemT outx (if sb then sx else dx) * FElemT outy (if sb then sy else dy)
                          * FElemT outz (if sb then sz else dz)
                          * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z
                          * R))%sep m6).
        { apply drop3_2. ecancel_assumption. }
        ecancel_assumption.
    - intros Hz.
      rewrite ct2_word_of_nat_zero in Hz by exact Hv.
      assert (v = 0%nat) as -> by lia.
      cbn [dadd_from] in Hacc.
      split; [reflexivity|].
      exists ax, ay, az, bx, by_, bz. split; [exact Hacc|exact Hmv].
  Qed.

  Definition spec_of_g2_scalar_mul_ct (functions : Semantics.env) : Prop :=
    forall (outx outy outz tx ty tz sp px py pz : word) (ox0 oy0 oz0 tx0 ty0 tz0 X Y Z : Fp2)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      (AFElem None outx ox0 * AFElem None outy oy0 * AFElem None outz oz0
       * AFElem None tx tx0 * AFElem None ty ty0 * AFElem None tz tz0
       * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
      Semantics.call functions "g2_scalar_mul_ct" tr m
        [outx; outy; outz; tx; ty; tz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz tx1 ty1 tz1 : Fp2,
             (ox, oy, oz) = g2_smul_target s (X, Y, Z) /\
             (FElemT outx ox * FElemT outy oy * FElemT outz oz
              * AFElem None tx tx1 * AFElem None ty ty1 * AFElem None tz tz1
              * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m').

  Theorem g2_scalar_mul_ct_ok functions :
    map.get functions "g2_scalar_mul_ct" = Some g2_scalar_mul_ct_func ->
    CtCallees2 functions ->
    spec_of_g2_scalar_mul_ct functions.
  Proof.
    intros Henv HC outx outy outz tx ty tz sp px py pz ox0 oy0 oz0 tx0 ty0 tz0 X Y Z s R tr m
           Hlen Hm.
    unfold Semantics.call.
    do 3 eexists. split; [exact Henv|].
    destruct (map.of_list_zip ["outx"; "outy"; "outz"; "tx"; "ty"; "tz"; "scalar"; "px"; "py"; "pz"]
                [outx; outy; outz; tx; ty; tz; sp; px; py; pz]) as [l0|] eqn:Hzip.
    2: { exfalso. cbn in Hzip. discriminate Hzip. }
    exists l0. split; [reflexivity|].
    cbn in Hzip. injection Hzip as <-.
    eapply Semantics.exec.weaken.
    { eapply WeakestPreconditionProperties.sound_cmd.
      eapply (g2_scalar_mul_ct_body_wp functions HC outx outy outz tx ty tz sp px py pz
                ox0 oy0 oz0 tx0 ty0 tz0 X Y Z s R tr m); try exact Hlen; try exact Hm;
        reflexivity. }
    intros tr' m' l' (-> & ox & oy & oz & tx1 & ty1 & tz1 & Hres & Hm').
    exists []. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    exists ox, oy, oz, tx1, ty1, tz1. split; [exact Hres|exact Hm'].
  Qed.
End ProofCT.

(* ================================================================== *)
(** ** 3. The closed statement                                          *)
(* ================================================================== *)

Section ClosedCT.
  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls12_prime_parameters bls12_field_representation
    bls12_Fp2_field_parameters bls12_Fp2_field_representation
    bls12_prime_parameters_ok bls12_field_representation_ok.
  Existing Instance prime_field_parameters.
  #[local] Existing Instances g2_fld g2_dec g2_char_ge_3 g2_char_ge_12 g2_char_ge_21.

  #[local] Instance prime_M_sm : Znumtheory.prime (Z.pos PrimeField.M_pos) :=
    bls12_prime_certif.prime_bls12_381.

  Add Ring Fp_ring_sm : (F.ring_theory PrimeField.M_pos)
    (morphism (F.ring_morph PrimeField.M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory PrimeField.M_pos),
     power_tac (F.power_theory PrimeField.M_pos) [F.is_pow_constant]).

  Local Notation word := BasicC64Semantics.word.
  Local Notation mem := BasicC64Semantics.mem.
  Local Notation cadd := (@RcbLawsAF.cadd Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation cdbl := (@RcbLawsAF.cdbl Fp2 bls12_Fp2_field_parameters g2_tb).
  Local Notation pt_eq := (@RcbLawsAF.pt_eq Fp2 bls12_Fp2_field_parameters g2_dec).
  Local Notation id_pt := (@RcbLawsAF.id_pt Fp2 bls12_Fp2_field_parameters).
  Local Notation Fzero := (@AbstractField.Fzero Fp2 bls12_Fp2_field_parameters).
  Local Notation Fone2 := (@AbstractField.Fone Fp2 bls12_Fp2_field_parameters).
  Local Notation Fopp2 := (@AbstractField.Fopp Fp2 bls12_Fp2_field_parameters).
  Local Notation Fadd2 := (@AbstractField.Fadd Fp2 bls12_Fp2_field_parameters).
  Local Notation Fsub2 := (@AbstractField.Fsub Fp2 bls12_Fp2_field_parameters).
  Local Notation Fmul2 := (@AbstractField.Fmul Fp2 bls12_Fp2_field_parameters).

  Add Ring Fp2_ring_sm :
    (@Ring.ring_theory_for_stdlib_tactic Fp2 (@eq Fp2) Fzero Fone2 Fopp2 Fadd2 Fsub2 Fmul2 _).
  Local Notation tight := (@AbstractField.tight_bounds Fp2 _ _ _ _ _ bls12_Fp2_field_representation).
  Local Notation FElemT := (AFElem (Some tight)).

  #[local] Instance g2_rep_ok_ct :
    @AbstractField.FieldRepresentation_ok Fp2 _ _ _ _ _ bls12_Fp2_field_representation :=
    Fp2_field_representation_ok _ _.

  (** In an environment holding the printed bodies, with only the Fp2 leaf
      contracts as premises, [g2_scalar_mul_ct] returns a tight triple
      projectively equal to [k P] for every point P of E'(Fp2) with tight
      coordinates, [k] the 256-bit integer of the limbs.  The scratch
      triple [t] is left holding arbitrary values. *)
  Theorem g2_scalar_mul_ct_closed (functions : Semantics.env) :
    map.get functions "g2_scalar_mul_ct" = Some g2_scalar_mul_ct_func ->
    map.get functions "ct_cswap" = Some g2_ct_cswap_func ->
    map.get functions g2_curve_add_name = Some g2_add_body ->
    map.get functions g2_curve_double_ip_name = Some g2_double_ip_body ->
    map.get functions g2_three_b_name = Some g2_three_b_body ->
    spec_of_af_mul (F:=Fp2) functions ->
    spec_of_af_add (F:=Fp2) functions ->
    spec_of_af_sub (F:=Fp2) functions ->
    forall (outx outy outz tx ty tz sp px py pz : word) (ox0 oy0 oz0 tx0 ty0 tz0 X Y Z : Fp2)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      g2_oncurve (X, Y, Z) ->
      (AFElem None outx ox0 * AFElem None outy oy0 * AFElem None outz oz0
       * AFElem None tx tx0 * AFElem None ty ty0 * AFElem None tz tz0
       * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
      Semantics.call functions "g2_scalar_mul_ct" tr m
        [outx; outy; outz; tx; ty; tz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz tx1 ty1 tz1 : Fp2,
             pt_eq (ox, oy, oz) (smul id_pt cadd (BLS12_MSM_Closed.scalar_value s) (X, Y, Z))
             /\ (FElemT outx ox * FElemT outy oy * FElemT outz oz
                 * AFElem None tx tx1 * AFElem None ty ty1 * AFElem None tz tz1
                 * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z
                 * R)%sep m').
  Proof.
    intros Hsm Hsw Hca Hdi Htb Hmul Hadd Hsub.
    assert (HC : CtCallees2 functions).
    { pose proof (g2_three_b_ok functions Htb) as Hload.
      constructor.
      - exact (@af_curve_add_correct 64 BW64 BasicC64Semantics.word BasicC64Semantics.mem
                 _ _ _ _ _ _ Fp2 bls12_Fp2_field_parameters bls12_Fp2_field_representation _
                 g2_bounds_eq g2_tb g2_three_b_name I functions Hca Hmul Hadd Hsub Hload).
      - exact (@af_curve_double_ip_correct 64 BW64 BasicC64Semantics.word BasicC64Semantics.mem
                 _ _ _ _ _ _ Fp2 bls12_Fp2_field_parameters bls12_Fp2_field_representation _
                 g2_bounds_eq g2_tb g2_three_b_name I functions Hdi Hmul Hadd Hsub Hload).
      - exact Hsub.
      - exact Hload.
      - exact Hsw. }
    pose proof (g2_scalar_mul_ct_ok functions Hsm HC) as Hspec.
    intros outx outy outz tx ty tz sp px py pz ox0 oy0 oz0 tx0 ty0 tz0 X Y Z s R tr m Hlen Hon Hm.
    eapply Semantics.weaken_call.
    { exact (Hspec outx outy outz tx ty tz sp px py pz ox0 oy0 oz0 tx0 ty0 tz0 X Y Z s R tr m
                   Hlen Hm). }
    cbv beta. intros tr' m' rets (Hr & Htr & ox & oy & oz & tx1 & ty1 & tz1 & Hres & Hm').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists ox, oy, oz, tx1, ty1, tz1. split; [ | exact Hm' ].
    rewrite Hres. exact (g2_smul_correct s (X, Y, Z) Hlen Hon).
  Qed.
End ClosedCT.
