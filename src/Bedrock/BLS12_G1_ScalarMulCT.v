(** * BLS12_G1_ScalarMulCT — constant-time G1 scalar multiplication (proved bedrock2).

    [g1_scalar_mul_ct] multiplies a point by a 256-bit scalar (four
    little-endian 64-bit limbs), most significant bit first, with a
    sequence of operations that does not depend on the scalar:

      out := (0 : 1 : 0);
      for i = 255 down to 0:
        out := double(out);                      (in place)
        bit := (scalar[i / 64] >> (i mod 64)) & 1;
        t   := out + P;                          (always; complete formulas)
        ct_cswap(bit, out.x, t.x);  ct_cswap(bit, out.y, t.y);
        ct_cswap(bit, out.z, t.z)                (out := bit ? t : out)

    [ct_cswap] ([Group.CurveAdd.CtSwap], Qed) swaps two n-word arrays
    with the mask arithmetic nmask := 0 - bit, mask := ~nmask,
    a := (mask & a) | (nmask & b), b := (mask & b) | (nmask & a), on every
    word, in a loop of fixed length.  [t] is a caller-provided scratch
    triple (three more pointer arguments), so the function performs no
    stack allocation.

    Constant time, at the bedrock2 level: the program text contains no
    [cmd.cond] and no [expr.ite]; the only loop conditions are the
    counters [i] (256 down to 0) and the [ct_cswap] index (0 to n); every
    address is a pointer argument plus an offset computed from those
    counters (the scalar limb read at [scalar + 8 (i >> 6)] depends on
    [i] only).  The scalar's bits enter only as operands of [and], [or],
    [xor], [sub], [sru] and as the mask argument of [ct_cswap].  Hence the
    sequence of executed commands, of function calls and of memory
    addresses is the same for every scalar.  This is a statement about
    the program text, read off the definitions below; it is not a theorem
    about bedrock2's semantics (whose trace records only external calls,
    [tr' = tr]), and it says nothing about the timing of the field leaves
    (bls12_mul/add/sub, supplied by the Rust runtime) or of the Rust code
    the printer produces after compilation.

    Proved here:
    - [g1_scalar_mul_ct_ok]: the bedrock2 function returns
      [smul_target] = [dadd_from add dbl s P 256 id] (the same Gallina
      value as the variable-time [g1_scalar_mul]), from the contracts of
      the out-of-place addition, the in-place doubling, the identity
      store and [ct_cswap]'s body;
    the closed BLS12-381 statement is [BLS12_G1_CT_Closed.g1_scalar_mul_ct_closed].

    No Admitted, no Axiom. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith List Lia.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require bedrock2.Loops.
Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_MSM_Functional.
Require Import Bedrock.BLS12_G1_ScalarMul.
Require Import Bedrock.Group.CurveAdd.CtSwap.
Import Syntax BinInt String List.ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ================================================================== *)
(** ** 1. The bedrock2 program                                          *)
(* ================================================================== *)

Section Program.
  Context (curve_add_name curve_double_name store_zero_name : string).

  Definition ct_cswap_call3 (a b c : string) : Syntax.cmd :=
    cmd.seq (cmd.call [] "ct_cswap" [expr.var "bit"; expr.var a; expr.var "tx"])
    (cmd.seq (cmd.call [] "ct_cswap" [expr.var "bit"; expr.var b; expr.var "ty"])
             (cmd.call [] "ct_cswap" [expr.var "bit"; expr.var c; expr.var "tz"])).

  (** Loop body: [i := i - 1; out := 2 out;
      a := scalar + ((i >> 6) << 3); bit := (load(a) >> (i & 63)) & 1;
      t := out + P; cswap(bit, out, t)]. *)
  Definition g1_scalar_mul_ct_loop_body : Syntax.cmd :=
    cmd.seq (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
    (cmd.seq (cmd.call [] curve_double_name
                [expr.var "outx"; expr.var "outy"; expr.var "outz";
                 expr.var "outx"; expr.var "outy"; expr.var "outz"])
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
    (cmd.seq (cmd.call [] curve_add_name
                [expr.var "outx"; expr.var "px";
                 expr.var "outy"; expr.var "py";
                 expr.var "outz"; expr.var "pz";
                 expr.var "tx"; expr.var "ty"; expr.var "tz"])
       (ct_cswap_call3 "outx" "outy" "outz"))))).

  Definition g1_scalar_mul_ct_body : Syntax.cmd :=
    cmd.seq (cmd.call [] store_zero_name
               [expr.var "outx"; expr.var "outy"; expr.var "outz"])
    (cmd.seq (cmd.set "i" (expr.literal 256))
       (cmd.while (expr.var "i") g1_scalar_mul_ct_loop_body)).

  Definition g1_scalar_mul_ct
    : string * (list string * list string * Syntax.cmd) :=
    ("g1_scalar_mul_ct",
     (["outx"; "outy"; "outz"; "tx"; "ty"; "tz"; "scalar"; "px"; "py"; "pz"], [],
      g1_scalar_mul_ct_body)).
End Program.

(* ================================================================== *)
(** ** 2. The program computes [smul_target] on raw triples             *)
(* ================================================================== *)

Section Proof.
  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {mem : map.map word Byte.byte}.
  Context {locals : map.map String.string word}.
  Context {ext_spec : bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok (field_representation:=field_representation)}.
  Context (Hwidth64 : width = 64).
  Context (n_small : Z.of_nat felem_size_in_words < 2 ^ width).
  Context (curve_add_name curve_double_name store_zero_name : String.string).

  Local Notation F := (F M_pos).
  Local Notation G1_F := (F * F * F)%type.
  Local Notation FElemT := (FElem (Some tight_bounds)).

  Context (g1_add_spec : G1_F -> G1_F -> G1_F)
          (g1_double_spec : G1_F -> G1_F)
          (g1_identity : G1_F).

  (** The out-of-place addition: tight inputs, arbitrary output buffers. *)
  Definition CurveAddOutOK (functions : Semantics.env) : Prop :=
    forall (pX1 pX2 pY1 pY2 pZ1 pZ2 pXo pYo pZo : word)
           (X1 X2 Y1 Y2 Z1 Z2 Xo0 Yo0 Zo0 : F) R tr m,
      (FElemT pX1 X1 * FElemT pX2 X2 * FElemT pY1 Y1 * FElemT pY2 Y2
       * FElemT pZ1 Z1 * FElemT pZ2 Z2
       * FElem None pXo Xo0 * FElem None pYo Yo0 * FElem None pZo Zo0 * R)%sep m ->
      Semantics.call functions curve_add_name tr m
        [pX1; pX2; pY1; pY2; pZ1; pZ2; pXo; pYo; pZo]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           let '(Xo, Yo, Zo) := g1_add_spec (X1, Y1, Z1) (X2, Y2, Z2) in
           (FElemT pX1 X1 * FElemT pX2 X2 * FElemT pY1 Y1 * FElemT pY2 Y2
            * FElemT pZ1 Z1 * FElemT pZ2 Z2
            * FElemT pXo Xo * FElemT pYo Yo * FElemT pZo Zo * R)%sep m').

  (** The callee contracts, behind a record so that they stay folded. *)
  Record CtCallees (functions : Semantics.env) : Prop := mkCtCallees {
    ct_add : CurveAddOutOK functions;
    ct_dbl : CurveDoubleInplaceOK curve_double_name g1_double_spec functions;
    ct_zero : StoreZero3OK store_zero_name g1_identity functions;
    ct_swap : map.get functions "ct_cswap" = Some (ct_cswap (word:=word) felem_size_in_words) }.

  (** [ct_cswap] on two tight field elements. *)
  Lemma felem_cswap_call (functions : Semantics.env)
      (Henv : map.get functions "ct_cswap" = Some (ct_cswap (word:=word) felem_size_in_words))
      (b : bool) (p1 p2 : word) (v1 v2 : F) (R : mem -> Prop) tr m :
    (FElemT p1 v1 * FElemT p2 v2 * R)%sep m ->
    Semantics.call functions "ct_cswap" tr m [word.of_Z (Z.b2z b); p1; p2]
      (fun tr' m' rets =>
         rets = [] /\ tr = tr' /\
         (FElemT p1 (if b then v2 else v1) * FElemT p2 (if b then v1 else v2) * R)%sep m').
  Proof.
    intros Hm.
    unfold FElem, Compilation2.FElem in Hm.
    destruct Hm as (m12 & mR & Hs & H12 & HR).
    destruct H12 as (m1 & m2 & Hs12 & H1 & H2).
    destruct H1 as (x1 & H1). destruct H2 as (x2 & H2).
    apply sep_emp_l in H1. destruct H1 as ((Hv1 & Hb1) & H1).
    apply sep_emp_l in H2. destruct H2 as ((Hv2 & Hb2) & H2).
    destruct x1 as [l1 Hl1]. destruct x2 as [l2 Hl2].
    cbv [Field.FElem proj1_sig] in H1, H2.
    assert (Hm' : (Bignum felem_size_in_words p1 l1 * Bignum felem_size_in_words p2 l2 * R)%sep m).
    { exists m12, mR. split; [exact Hs|]. split; [|exact HR].
      exists m1, m2. split; [exact Hs12|].
      split; (apply sep_emp_l; split; [assumption|]); assumption. }
    eapply Semantics.weaken_call.
    { exact (ct_cswap_call felem_size_in_words n_small functions Henv b p1 p2 l1 l2 R tr m Hm'). }
    cbv beta. intros tr' m' rets (Hr & Htr & Hm2).
    split; [exact Hr|]. split; [exact Htr|].
    destruct Hm2 as (n12 & nR & Hs' & H12' & HR').
    destruct H12' as (n1 & n2 & Hs12' & H1' & H2').
    unfold Bignum in H1', H2'.
    apply sep_emp_l in H1'. destruct H1' as (Hn1 & H1').
    apply sep_emp_l in H2'. destruct H2' as (Hn2 & H2').
    exists n12, nR. split; [exact Hs'|]. split; [|exact HR'].
    exists n1, n2. split; [exact Hs12'|].
    unfold FElem, Compilation2.FElem.
    destruct b.
    - split.
      + exists (exist _ l2 Hl2). apply sep_emp_l. split; [split; assumption|]. exact H1'.
      + exists (exist _ l1 Hl1). apply sep_emp_l. split; [split; assumption|]. exact H2'.
    - split.
      + exists (exist _ l1 Hl1). apply sep_emp_l. split; [split; assumption|]. exact H1'.
      + exists (exist _ l2 Hl2). apply sep_emp_l. split; [split; assumption|]. exact H2'.
  Qed.

  Lemma drop3 (tx ty tz : word) (a b c : F) (Rest : mem -> Prop) m :
    (FElemT tx a * FElemT ty b * FElemT tz c * Rest)%sep m ->
    (FElem None tx a * FElem None ty b * FElem None tz c * Rest)%sep m.
  Proof.
    intros H.
    eapply Proper_sep_impl1; [ | reflexivity | exact H ].
    eapply Proper_sep_impl1; [ | apply drop_bounds_FElem ].
    eapply Proper_sep_impl1; apply drop_bounds_FElem.
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

  Lemma ct_unsigned_small (v : Z) :
    0 <= v < 2 ^ 64 -> word.unsigned (word.of_Z v : word) = v.
  Proof. intros. apply word.unsigned_of_Z_nowrap. rewrite Hwidth64. lia. Qed.

  Lemma ct_word_i_and_63 (v : Z) :
    0 <= v < 256 ->
    word.unsigned (word.and (word.of_Z v) (word.of_Z 63) : word) = v mod 64.
  Proof.
    intros Hv. rewrite word.unsigned_and_nowrap, !ct_unsigned_small by lia.
    change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
  Qed.

  Lemma ct_word_limb_addr (sp : word) (v : Z) :
    0 <= v < 256 ->
    word.add sp (word.slu (word.sru (word.of_Z v) (word.of_Z 6)) (word.of_Z 3))
    = word.add sp (word.of_Z (Z.of_nat 0 * 32 + Z.of_nat (Z.to_nat (v / 64)) * 8)).
  Proof.
    intros Hv. f_equal. apply word.unsigned_inj.
    assert (Hq : 0 <= v / 64 < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite word.unsigned_slu by (rewrite ct_unsigned_small, Hwidth64 by lia; lia).
    rewrite word.unsigned_sru_nowrap by (rewrite ct_unsigned_small, Hwidth64 by lia; lia).
    rewrite !ct_unsigned_small by lia.
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    rewrite ?Z2Nat.id by lia.
    unfold word.wrap. rewrite Hwidth64. rewrite Z.mod_small by lia.
    change (2 ^ 6) with 64. change (2 ^ 3) with 8. lia.
  Qed.

  Lemma ct_word_bit (x : word) (k : word) :
    0 <= word.unsigned k < 64 ->
    word.unsigned (word.and (word.sru x k) (word.of_Z 1) : word)
    = Z.b2z (Z.testbit (word.unsigned x) (word.unsigned k)).
  Proof.
    intros Hk. rewrite word.unsigned_and_nowrap.
    rewrite word.unsigned_sru_nowrap by (rewrite Hwidth64; lia).
    rewrite ct_unsigned_small by lia.
    change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
    rewrite Z.testbit_spec' by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  Qed.

  Lemma ct_word_sub_1 (v : nat) :
    (0 < v <= 256)%nat ->
    word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1) = (word.of_Z (Z.of_nat (v - 1)) : word).
  Proof.
    intros Hv. apply word.unsigned_inj.
    rewrite word.unsigned_sub, !ct_unsigned_small by lia.
    unfold word.wrap. rewrite Hwidth64. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma ct_word_of_nat_zero (v : nat) :
    (v <= 256)%nat -> word.unsigned (word.of_Z (Z.of_nat v) : word) = Z.of_nat v.
  Proof. intros. apply ct_unsigned_small. lia. Qed.

  Lemma ct_scalar_bit_word (s : list word) (v : nat) :
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

  Lemma bit_word (bitw : word) (b : bool) :
    word.unsigned bitw = Z.b2z b -> bitw = word.of_Z (Z.b2z b).
  Proof.
    intros H. apply word.unsigned_inj. rewrite H.
    rewrite word.unsigned_of_Z_nowrap; [reflexivity|].
    rewrite Hwidth64. destruct b; cbn; lia.
  Qed.

  Definition ct_loop_inv (functions : Semantics.env) (tr : Semantics.trace)
      (outx outy outz tx ty tz sp px py pz : word) (s : list word) (X Y Z : F)
      (R : mem -> Prop) (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\ (v <= 256)%nat /\
    map.get l "outx" = Some outx /\ map.get l "outy" = Some outy /\
    map.get l "outz" = Some outz /\ map.get l "tx" = Some tx /\
    map.get l "ty" = Some ty /\ map.get l "tz" = Some tz /\
    map.get l "scalar" = Some sp /\
    map.get l "px" = Some px /\ map.get l "py" = Some py /\
    map.get l "pz" = Some pz /\
    map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
    exists ax ay az bx by_ bz,
      dadd_from g1_add_spec g1_double_spec (List.map word.unsigned s) (X, Y, Z) v (ax, ay, az)
      = smul_target g1_add_spec g1_double_spec g1_identity s (X, Y, Z) /\
      (FElemT outx ax * FElemT outy ay * FElemT outz az
       * FElem None tx bx * FElem None ty by_ * FElem None tz bz
       * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m.

  Lemma g1_scalar_mul_ct_body_wp functions (HC : CtCallees functions)
      (outx outy outz tx ty tz sp px py pz : word) (ox0 oy0 oz0 tx0 ty0 tz0 X Y Z : F)
      (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals) :
    length s = 4%nat ->
    (FElem None outx ox0 * FElem None outy oy0 * FElem None outz oz0
     * FElem None tx tx0 * FElem None ty ty0 * FElem None tz tz0
     * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
    map.get l "outx" = Some outx -> map.get l "outy" = Some outy ->
    map.get l "outz" = Some outz -> map.get l "tx" = Some tx ->
    map.get l "ty" = Some ty -> map.get l "tz" = Some tz ->
    map.get l "scalar" = Some sp ->
    map.get l "px" = Some px -> map.get l "py" = Some py -> map.get l "pz" = Some pz ->
    WeakestPrecondition.cmd functions
      (g1_scalar_mul_ct_body curve_add_name curve_double_name store_zero_name) tr m l
      (fun tr' m' l' =>
         tr' = tr /\
         exists ox oy oz tx1 ty1 tz1,
           (ox, oy, oz) = smul_target g1_add_spec g1_double_spec g1_identity s (X, Y, Z) /\
           (FElemT outx ox * FElemT outy oy * FElemT outz oz
            * FElem None tx tx1 * FElem None ty ty1 * FElem None tz tz1
            * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m').
  Proof.
    intros Hlen Hm Hox Hoy Hoz Htx Hty Htz Hsp Hpx Hpy Hpz.
    destruct HC as [HA HD HZ HW].
    cbv [g1_scalar_mul_ct_body].
    (* store_zero(out) *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    eapply Semantics.weaken_call.
    { eapply (HZ outx outy outz ox0 oy0 oz0
                (FElem None tx tx0 * FElem None ty ty0 * FElem None tz tz0
                 * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep tr m).
      ecancel_assumption. }
    cbv beta. intros tr1 m1 rets (-> & <- & Hm1).
    eexists; split; [reflexivity|].
    (* i := 256 *)
    peel. peel.
    eexists; split; [eval_dexprs|].
    cbv [dlet.dlet].
    eapply (Loops.while_localsmap (measure := nat)
              (ct_loop_inv functions tr outx outy outz tx ty tz sp px py pz s X Y Z R)
              Wf_nat.lt_wf 256%nat).
    { (* entry *)
      cbv [ct_loop_inv]. split; [reflexivity|]. split; [lia|].
      do 11 (split; [solve_get|]).
      case_eq g1_identity. intros [ix iy] iz Hid. rewrite Hid in Hm1.
      exists ix, iy, iz, tx0, ty0, tz0. split.
      - unfold smul_target, smul_prog. try rewrite Hid. reflexivity.
      - ecancel_assumption. }
    intros v t mv lv Hinv.
    destruct Hinv as (-> & Hv & Hlx & Hly & Hlz & Hltx & Hlty & Hltz & Hls & Hlpx & Hlpy & Hlpz
                      & Hli & ax & ay & az & bx & by_ & bz & Hacc & Hmv).
    exists (word.of_Z (Z.of_nat v)). split.
    { eval_dexprs. }
    split.
    - (* loop body *)
      intros Hne.
      assert (Hv0 : (0 < v)%nat).
      { destruct v; [|lia]. exfalso. apply Hne. apply word.unsigned_of_Z_0. }
      set (v' := (v - 1)%nat).
      cbv [g1_scalar_mul_ct_loop_body].
      (* i := i - 1 *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      cbv [dlet.dlet].
      cbv [Semantics.interp_binop].
      rewrite ct_word_sub_1 by lia. fold v'.
      (* out := double(out) *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (HD outx outy outz ax ay az
                  (FElem None tx bx * FElem None ty by_ * FElem None tz bz
                   * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep tr mv).
        ecancel_assumption. }
      cbv beta. intros t2 m2 rets (-> & <- & Hm2).
      case_eq (g1_double_spec (ax, ay, az)). intros [dx dy] dz Hd. rewrite Hd in Hm2.
      eexists; split; [reflexivity|].
      (* a := scalar + ((i >> 6) << 3) *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      cbv [dlet.dlet].
      (* bit := (load(a) >> (i & 63)) & 1 *)
      assert (Hv'256 : (v' < 256)%nat) by lia.
      set (limb := Z.to_nat (Z.of_nat v' / 64)).
      assert (Hlimb : (limb < 4)%nat).
      { unfold limb. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia).
        apply Z.div_lt_upper_bound; lia. }
      pose proof (ScalarsArray_load_limb Hwidth64 g1_add_spec g1_double_spec g1_identity sp [s] 0 limb
                    (FElemT outx dx * FElemT outy dy * FElemT outz dz
                     * FElem None tx bx * FElem None ty by_ * FElem None tz bz
                     * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m2
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
          rewrite ct_word_limb_addr by lia. apply Hload. ecancel_assumption. }
        eexists; split; [solve_get|].
        reflexivity. }
      cbv [dlet.dlet Semantics.interp_binop].
      set (bitw := word.and
                     (word.sru (nth limb s (word.of_Z 0))
                        (word.and (word.of_Z (Z.of_nat v')) (word.of_Z 63)))
                     (word.of_Z 1) : word).
      set (sb := scalar_bit (List.map word.unsigned s) v').
      assert (Hbit : bitw = word.of_Z (Z.b2z sb)).
      { apply bit_word. unfold bitw.
        rewrite ct_word_bit by (rewrite ct_word_i_and_63 by lia;
                                         pose proof (Z.mod_pos_bound (Z.of_nat v') 64); lia).
        rewrite ct_word_i_and_63 by lia. unfold sb. rewrite ct_scalar_bit_word by lia.
        reflexivity. }
      clearbody bitw. subst bitw.
      (* t := out + P *)
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (HA outx px outy py outz pz tx ty tz dx X dy Y dz Z bx by_ bz
                  (ScalarsArray sp [s] * R)%sep tr m2).
        ecancel_assumption. }
      cbv beta. intros t3 m3 rets (-> & <- & Hm3).
      case_eq (g1_add_spec (dx, dy, dz) (X, Y, Z)). intros [sx sy] sz Hs.
      rewrite Hs in Hm3.
      eexists; split; [reflexivity|].
      (* the three swaps *)
      cbv [ct_cswap_call3].
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (felem_cswap_call functions HW sb outx tx dx sx
                  (FElemT outy dy * FElemT outz dz * FElemT ty sy * FElemT tz sz
                   * FElemT px X * FElemT py Y * FElemT pz Z * ScalarsArray sp [s] * R)%sep
                  tr m3).
        ecancel_assumption. }
      cbv beta. intros t4 m4 rets (-> & <- & Hm4).
      eexists; split; [reflexivity|].
      peel. peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (felem_cswap_call functions HW sb outy ty dy sy
                  (FElemT outx (if sb then sx else dx) * FElemT tx (if sb then dx else sx)
                   * FElemT outz dz * FElemT tz sz
                   * FElemT px X * FElemT py Y * FElemT pz Z * ScalarsArray sp [s] * R)%sep
                  tr m4).
        ecancel_assumption. }
      cbv beta. intros t5 m5 rets (-> & <- & Hm5).
      eexists; split; [reflexivity|].
      peel.
      eexists; split; [eval_dexprs|].
      eapply Semantics.weaken_call.
      { eapply (felem_cswap_call functions HW sb outz tz dz sz
                  (FElemT outx (if sb then sx else dx) * FElemT tx (if sb then dx else sx)
                   * FElemT outy (if sb then sy else dy) * FElemT ty (if sb then dy else sy)
                   * FElemT px X * FElemT py Y * FElemT pz Z * ScalarsArray sp [s] * R)%sep
                  tr m5).
        ecancel_assumption. }
      cbv beta. intros t6 m6 rets (-> & <- & Hm6).
      eexists; split; [reflexivity|].
      exists v'. split; [|lia].
      cbv [ct_loop_inv]. split; [reflexivity|]. split; [lia|].
      do 11 (split; [solve_get|]).
      cbn [dadd_from] in Hacc.
      replace v with (S v') in Hacc by lia.
      cbn [dadd_from] in Hacc. rewrite Hd in Hacc. fold sb in Hacc.
      exists (if sb then sx else dx), (if sb then sy else dy), (if sb then sz else dz),
        (if sb then dx else sx), (if sb then dy else sy), (if sb then dz else sz).
      split.
      + rewrite <- Hacc. destruct sb; [rewrite Hs|]; reflexivity.
      + assert (Hm7 : (FElem None tx (if sb then dx else sx) * FElem None ty (if sb then dy else sy)
                       * FElem None tz (if sb then dz else sz)
                       * (FElemT outx (if sb then sx else dx) * FElemT outy (if sb then sy else dy)
                          * FElemT outz (if sb then sz else dz)
                          * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R))%sep m6).
        { apply drop3. ecancel_assumption. }
        ecancel_assumption.
    - (* exit *)
      intros Hz.
      rewrite ct_word_of_nat_zero in Hz by exact Hv.
      assert (v = 0%nat) as -> by lia.
      cbn [dadd_from] in Hacc.
      split; [reflexivity|].
      exists ax, ay, az, bx, by_, bz. split; [exact Hacc|exact Hmv].
  Qed.

  Definition spec_of_g1_scalar_mul_ct (functions : Semantics.env) : Prop :=
    forall (outx outy outz tx ty tz sp px py pz : word) (ox0 oy0 oz0 tx0 ty0 tz0 X Y Z : F)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      (FElem None outx ox0 * FElem None outy oy0 * FElem None outz oz0
       * FElem None tx tx0 * FElem None ty ty0 * FElem None tz tz0
       * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
      Semantics.call functions "g1_scalar_mul_ct" tr m
        [outx; outy; outz; tx; ty; tz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz tx1 ty1 tz1,
             (ox, oy, oz) = smul_target g1_add_spec g1_double_spec g1_identity s (X, Y, Z) /\
             (FElemT outx ox * FElemT outy oy * FElemT outz oz
              * FElem None tx tx1 * FElem None ty ty1 * FElem None tz tz1
              * ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m').

  Theorem g1_scalar_mul_ct_ok functions :
    map.get functions "g1_scalar_mul_ct"
      = Some (snd (g1_scalar_mul_ct curve_add_name curve_double_name store_zero_name)) ->
    CtCallees functions ->
    spec_of_g1_scalar_mul_ct functions.
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
      eapply (g1_scalar_mul_ct_body_wp functions HC outx outy outz tx ty tz sp px py pz
                ox0 oy0 oz0 tx0 ty0 tz0 X Y Z s R tr m); try exact Hlen; try exact Hm;
        repeat (rewrite map.get_put_diff by congruence); apply map.get_put_same. }
    intros tr' m' l' (-> & ox & oy & oz & tx1 & ty1 & tz1 & Hres & Hm').
    exists []. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    exists ox, oy, oz, tx1, ty1, tz1. split; [exact Hres|exact Hm'].
  Qed.
End Proof.
