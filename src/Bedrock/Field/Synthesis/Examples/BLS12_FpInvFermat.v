(** * BLS12-381: a verified bedrock2 base-field inverse, by Fermat's little theorem.

    [bls12_inv x = x^(p-2)], computed by square-and-multiply over the constant exponent
    [p - 2], scanned from the top in six 64-bit words:
    - [bls12_inv_pow_word(acc, x, e)]: [acc <- acc^(2^64) * x^e], a loop of 64 iterations
      ([acc <- acc^2], then [acc <- acc * x] when bit [i] of the word [e] is set).  The
      sequence of calls depends only on [e], which is public (a literal at every call site),
      so the inverse runs in time independent of [x].
    - [bls12_inv(out, x)]: [x] is copied to the stack (so [out] may alias [x]), [out <- 1],
      then six calls of [bls12_inv_pow_word] with the words of [p - 2], top word first.
    Correctness: [F.pow] algebra ([pow_word_step], [pow_words_comb]) and Fermat
    ([F.Fq_inv_fermat] with [Prime381.p381_prime]).  The callees are the fiat-crypto
    [bls12_square], [bls12_mul], [bls12_felem_copy] and the verified [bls12_from_word]
    ([BLS12_PairingLeavesFp]).

    These two functions are verified extras (in [BLS12_PairingFunctionalLeaves.bls12_extra_funcs]);
    the generated C/Rust code, which uses a hand-written divstep inversion, is unchanged.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Loops.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpExtra.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp.
Require Theory.BLS12Pairing.Prime381.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp2.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.

Local Open Scope string_scope.

Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

(** ** [F.pow] algebra, on an abstract modulus *)

Section PowAlgebra.
  Context {m : positive}.
  Add Ring Fm_ring : (@F.ring_theory m).
  Local Notation pw x k := (F.pow (m:=m) x (Z.to_N k)).

  Lemma pw_add (x : F m) a b : 0 <= a -> 0 <= b -> pw x (a + b) = F.mul (pw x a) (pw x b).
  Proof. intros. rewrite Z2N.inj_add by assumption. apply F.pow_add_r. Qed.

  Lemma pw_mul (x : F m) a b : 0 <= a -> 0 <= b -> pw x (a * b) = pw (pw x a) b.
  Proof. intros. rewrite Z2N.inj_mul by assumption. symmetry. apply F.pow_pow_l. Qed.

  Lemma pw_0 (x : F m) : pw x 0 = F.one.
  Proof. apply F.pow_0_r. Qed.

  Lemma pw_1 (x : F m) : pw x 1 = x.
  Proof. apply F.pow_1_r. Qed.

  Lemma pw_one k : 0 <= k -> pw (F.one (m:=m)) k = F.one.
  Proof.
    intros _. apply F.pow_1_l.
  Qed.

  Lemma Fmul_1_r (x : F m) : F.mul x F.one = x.
  Proof. ring. Qed.

  (** One iteration of the loop: [r = a^(2^k) * x^s]  ->  [r^2 * x^b = a^(2^(k+1)) * x^(2s+b)]. *)
  Lemma pow_word_step (a x : F m) (k s : Z) (b : bool) :
    0 <= k -> 0 <= s ->
    F.mul (F.mul (F.mul (pw a (2 ^ k)) (pw x s)) (F.mul (pw a (2 ^ k)) (pw x s)))
          (if b then x else F.one)
    = F.mul (pw a (2 ^ (k + 1))) (pw x (2 * s + Z.b2z b)).
  Proof.
    intros Hk Hs.
    assert (Hpk : 0 <= 2 ^ k) by (apply Z.pow_nonneg; lia).
    replace (2 ^ (k + 1)) with (2 ^ k + 2 ^ k) by (rewrite Z.pow_add_r by lia; lia).
    replace (2 * s + Z.b2z b) with ((s + s) + Z.b2z b) by lia.
    rewrite (pw_add a (2 ^ k) (2 ^ k)) by lia.
    rewrite (pw_add x (s + s) (Z.b2z b)) by (destruct b; cbn; lia).
    rewrite (pw_add x s s) by lia.
    destruct b; cbn [Z.b2z]; [rewrite pw_1 | rewrite pw_0]; ring.
  Qed.

  (** Composition of the six word steps: [(x^E)^(2^64) * x^w = x^(E * 2^64 + w)]. *)
  Lemma pow_words_comb (x : F m) (E w : Z) :
    0 <= E -> 0 <= w ->
    F.mul (pw (pw x E) (2 ^ 64)) (pw x w) = pw x (E * 2 ^ 64 + w).
  Proof.
    intros HE Hw.
    rewrite (pw_add x (E * 2 ^ 64) w) by lia.
    rewrite (pw_mul x E (2 ^ 64)) by lia.
    reflexivity.
  Qed.

  (** [shiftr e k = 2 * shiftr e (k+1) + bit k]. *)
  Lemma shiftr_step (e k : Z) :
    0 <= k ->
    Z.shiftr e k = 2 * Z.shiftr e (k + 1) + Z.b2z (Z.testbit e k).
  Proof.
    intros Hk.
    rewrite <- (Z.shiftr_shiftr e k 1) by lia.
    rewrite <- Z.div2_spec.
    replace (Z.testbit e k) with (Z.odd (Z.shiftr e k)).
    - apply Z.div2_odd.
    - rewrite <- Z.bit0_odd, Z.shiftr_spec by lia. f_equal.
  Qed.
End PowAlgebra.

(** ** The functions *)

(** The words of [p - 2], top word first. *)
Definition bls12_inv_w5 : Z := 0x1a0111ea397fe69a.
Definition bls12_inv_w4 : Z := 0x4b1ba7b6434bacd7.
Definition bls12_inv_w3 : Z := 0x64774b84f38512bf.
Definition bls12_inv_w2 : Z := 0x6730d2a0f6b0f624.
Definition bls12_inv_w1 : Z := 0x1eabfffeb153ffff.
Definition bls12_inv_w0 : Z := 0xb9feffffffffaaa9.

Definition bls12_inv_pow_word_loop : Syntax.cmd :=
  cmd.seq (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
  (cmd.seq (cmd.call [] "bls12_square" [expr.var "acc"; expr.var "acc"])
  (cmd.seq (cmd.set "bit" (expr.op bopname.and
                             (expr.op bopname.sru (expr.var "e") (expr.var "i"))
                             (expr.literal 1)))
           (cmd.cond (expr.var "bit")
              (cmd.call [] "bls12_mul" [expr.var "acc"; expr.var "acc"; expr.var "x"])
              cmd.skip))).

(** [acc <- acc^(2^64) * x^e]. *)
Definition bls12_inv_pow_word : string * Syntax.func :=
  ("bls12_inv_pow_word", (["acc"; "x"; "e"], (nil : list string),
    cmd.seq (cmd.set "i" (expr.literal 64))
            (cmd.while (expr.var "i") bls12_inv_pow_word_loop))).

Definition bls12_inv_pow_call (w : Z) : Syntax.cmd :=
  cmd.call [] "bls12_inv_pow_word" [expr.var "out"; expr.var "t"; expr.literal w].

(** [out <- x^(p-2)]. *)
Definition bls12_inv : string * Syntax.func :=
  ("bls12_inv", (["out"; "x"], (nil : list string), bedrock_func_body:(
    stackalloc 48 as t;
    coq:(cmd.call [] "bls12_felem_copy" [expr.var "t"; expr.var "x"]);
    coq:(cmd.call [] "bls12_from_word" [expr.var "out"; expr.literal 1]);
    coq:(bls12_inv_pow_call bls12_inv_w5);
    coq:(bls12_inv_pow_call bls12_inv_w4);
    coq:(bls12_inv_pow_call bls12_inv_w3);
    coq:(bls12_inv_pow_call bls12_inv_w2);
    coq:(bls12_inv_pow_call bls12_inv_w1);
    coq:(bls12_inv_pow_call bls12_inv_w0)
  ))).

Local Notation env := (Interface.map.rep (map:=Semantics.env)).
Local Notation pp := MS.bls12_pf_params.
Local Notation frep := MS.bls12_Fp_rep.
Local Notation Fp := (F (@PrimeField.M_pos pp)).
Local Notation FElem1 := (@AbstractField.FElem _ _ _ _ _ _ frep).
Local Notation feval1 := (@AbstractField.feval _ _ _ _ _ _ frep).
Local Notation tight1 := (@AbstractField.bounded_by _ _ _ _ _ _ frep
                            (@AbstractField.tight_bounds _ _ _ _ _ _ frep)).
Local Notation pw x k := (F.pow (m:=@PrimeField.M_pos pp) x (Z.to_N k)).

Definition spec_of_bls12_inv_pow_word : spec_of "bls12_inv_pow_word" :=
  fnspec! "bls12_inv_pow_word" (pacc px e : word) / (a xv : list word) R,
  { requires tr mem :=
      tight1 a /\ tight1 xv /\ (FElem1 pacc a * FElem1 px xv * R)%sep mem;
    ensures tr' mem' :=
      tr = tr' /\
      exists a',
        feval1 a' = F.mul (pw (feval1 a) (2 ^ 64)) (pw (feval1 xv) (word.unsigned e))
        /\ tight1 a' /\ (FElem1 pacc a' * FElem1 px xv * R)%sep mem' }.

(** The Fp inverse spec of the tower (as in [BLS12_PairingFunctionalLeaves]). *)
Definition spec_of_bls12_Fp_inv' (fs : env) : Prop :=
  AbstractField.unop_spec (F:=Fp) (field_representation:=frep) AbstractField.un_inv fs.

(** ** The loop *)

Definition pow_word_inv (pacc px e : word) (a xv : list word) (R : mem -> Prop)
  (tr : Semantics.trace) (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
  t = tr /\ (v <= 64)%nat /\
  exists r,
    tight1 r /\
    feval1 r = F.mul (pw (feval1 a) (2 ^ (64 - Z.of_nat v)))
                     (pw (feval1 xv) (Z.shiftr (word.unsigned e) (Z.of_nat v))) /\
    (FElem1 pacc r * FElem1 px xv * R)%sep m /\
    map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
    map.get l "acc" = Some pacc /\
    map.get l "x" = Some px /\
    map.get l "e" = Some e.

Lemma bit_word (e : word) (v : nat) :
  (0 < v <= 64)%nat ->
  word.unsigned (word.and (word.sru e (word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1)))
                          (word.of_Z 1)) =
  Z.b2z (Z.testbit (word.unsigned e) (Z.of_nat (v - 1))).
Proof.
  intros Hv.
  assert (Hi : word.unsigned (word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1) : word)
               = Z.of_nat (v - 1)).
  { rewrite word.unsigned_sub_nowrap; rewrite !word.unsigned_of_Z_nowrap; lia. }
  rewrite word.unsigned_and_nowrap, word.unsigned_sru_nowrap by (rewrite Hi; lia).
  rewrite Hi, word.unsigned_of_Z_nowrap by lia.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
  rewrite Zmod_odd, <- Z.bit0_odd, Z.shiftr_spec by lia.
  rewrite Z.add_0_l. destruct (Z.testbit _ _); reflexivity.
Qed.

Lemma bls12_inv_pow_word_ok (functions : env) :
  map.get functions "bls12_inv_pow_word" = Some (snd bls12_inv_pow_word) ->
  map.get functions "bls12_square" = Some (snd bls12_square) ->
  map.get functions "bls12_mul" = Some (snd bls12_mul) ->
  spec_of_bls12_inv_pow_word functions.
Proof.
  intros E Esq Emul.
  pose proof (bls12_Fp_square_leaf functions Esq) as Hsq.
  pose proof (bls12_Fp_mul_leaf functions Emul) as Hmul.
  clear Esq Emul.
  cbv [spec_of_bls12_inv_pow_word].
  intros pacc px e a xv R tr m0 (Hba & Hbx & Hm).
  eapply start_func; [exact E | clear E].
  cbv match beta delta [WeakestPrecondition.func bls12_inv_pow_word snd].
  eexists; split; [exact eq_refl|].
  repeat straightline.
  eapply (Loops.while_localsmap (pow_word_inv pacc px e a xv R tr) (lt:=Nat.lt) lt_wf 64%nat).
  { cbv [pow_word_inv]. split; [reflexivity|]. split; [lia|].
    exists a. split; [exact Hba|]. split.
    { change (2 ^ (64 - Z.of_nat 64)) with 1. rewrite pw_1.
      rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by (pose proof (word.unsigned_range e); exact H).
      rewrite pw_0. symmetry. apply Fmul_1_r. }
    split; [ecancel_assumption|].
    subst l i. repeat split. }
  intros v t m l0 (Ht & Hv & r & Hbr & Hfr & Hsep & Hgi & Hga & Hgx & Hge). subst t.
  exists (word.of_Z (Z.of_nat v)). split.
  { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get]. eexists. split; [exact Hgi | reflexivity]. }
  split.
  2: { intro Heq.
    assert (Hv0 : v = 0%nat).
    { destruct v; [reflexivity | exfalso]. rewrite word.unsigned_of_Z_nowrap in Heq by lia. lia. }
    subst v. cbn [list_map]. split; [reflexivity|]. split; [reflexivity|].
    exists r. split; [| split; [exact Hbr | ecancel_assumption]].
    rewrite Hfr. rewrite Z.shiftr_0_r. reflexivity. }
  intro Hne.
  assert (Hv_pos : (0 < v)%nat) by (destruct v; [exfalso; apply Hne; reflexivity | lia]).
  cbv [bls12_inv_pow_word_loop].
  repeat straightline.
  eexists; split.
  { cbv [DEXPR WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get]. eexists; split; [exact Hgi|]. cbv [WeakestPrecondition.literal dlet.dlet]. reflexivity. }
  cbv [dlet.dlet].
  repeat straightline.
  eexists; split.
  { cbv [dexprs list_map list_map_body WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
    rewrite !map.get_put_diff by congruence. rewrite Hga. eexists; split; [reflexivity|]. eexists; split; [reflexivity|]. reflexivity. }
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hsq pacc pacc r r _ tr m (conj Hbr (conj _ _)));
        [ eexists; ecancel_assumption | ecancel_assumption ] ].
  intros tr2 m2 rets (Hrets & Htr2 & r2 & Hv2 & Hb2 & Hm2). subst rets tr2.
  eexists; split; [reflexivity|].
  clear Hsep.
  straightline. straightline. straightline.
  eexists; split.
  { cbv [DEXPR WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
    rewrite map.get_put_diff by congruence. rewrite Hge. eexists; split; [reflexivity|].
    rewrite map.get_put_same. eexists; split; [reflexivity|]. reflexivity. }
  cbv [dlet.dlet].
  pose proof (bit_word e v (conj Hv_pos Hv)) as Hbitv.
  straightline.
  assert (Hstep : F.mul (F.mul (feval1 r) (feval1 r)) (if Z.testbit (word.unsigned e) (Z.of_nat (v-1)) then feval1 xv else F.one) = F.mul (pw (feval1 a) (2 ^ (64 - Z.of_nat (v - 1)))) (pw (feval1 xv) (Z.shiftr (word.unsigned e) (Z.of_nat (v - 1))))).
  { rewrite Hfr. rewrite pow_word_step by (try lia; apply Z.shiftr_nonneg; apply word.unsigned_range).
    replace (64 - Z.of_nat (v-1)) with ((64 - Z.of_nat v) + 1) by lia.
    rewrite (shiftr_step _ (Z.of_nat (v-1))) by lia. replace (Z.of_nat (v-1) + 1) with (Z.of_nat v) by lia. reflexivity. }
  clear Hfr.
  unfold1_cmd_goal; cbv beta match delta [cmd_body].
  assert (Hv2' : feval1 r2 = F.mul (feval1 r) (feval1 r)) by (rewrite Hv2; reflexivity).
  clear Hv2.
  eexists; split.
  { cbv [DEXPR WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
    rewrite map.get_put_same. eexists; split; reflexivity. }
  split.
  { intro Hbit.
    assert (Htb : Z.testbit (word.unsigned e) (Z.of_nat (v - 1)) = true).
    { destruct (Z.testbit (word.unsigned e) (Z.of_nat (v - 1))); [reflexivity|].
      exfalso. apply Hbit. exact Hbitv. }
    rewrite Htb in Hstep.
    repeat straightline.
    eexists; split.
    { cbv [dexprs list_map list_map_body WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
      rewrite !map.get_put_diff by congruence. rewrite Hga, Hgx.
      eexists; split; [reflexivity|]. eexists; split; [reflexivity|]. eexists; split; [reflexivity|]. reflexivity. }
    eapply WeakestPreconditionProperties.Proper_call;
      [ | refine (Hmul pacc pacc px r2 r2 xv _ tr m2 (conj Hb2 (conj Hbx (conj _ (conj _ _)))));
          [ eexists; ecancel_assumption | eexists; ecancel_assumption | ecancel_assumption ] ].
    intros tr3 m3 rets (Hrets & Htr3 & r3 & Hv3 & Hb3 & Hm3). subst rets tr3.
    eexists; split; [reflexivity|].
    exists (v - 1)%nat. split; [| unfold Nat.lt; lia].
    cbv [pow_word_inv]. split; [reflexivity|]. split; [lia|].
    exists r3. split; [exact Hb3|]. split.
    { rewrite <- Hstep. rewrite Hv3. rewrite <- Hv2'. reflexivity. }
    split; [ecancel_assumption|].
    split.
    { rewrite map.get_put_diff by congruence. rewrite map.get_put_same. f_equal.
      rewrite Nat2Z.inj_sub by lia. symmetry. apply word.ring_morph_sub. }
    repeat split; rewrite ?map.get_put_diff by congruence; assumption. }
  { intro Hbit0.
    assert (Htb : Z.testbit (word.unsigned e) (Z.of_nat (v - 1)) = false).
    { destruct (Z.testbit (word.unsigned e) (Z.of_nat (v - 1))); [|reflexivity].
      exfalso. rewrite Hbitv in Hbit0. discriminate Hbit0. }
    rewrite Htb, Fmul_1_r in Hstep.
    repeat straightline.
    exists (v - 1)%nat. split; [| unfold Nat.lt; lia].
    cbv [pow_word_inv]. split; [reflexivity|]. split; [lia|].
    exists r2. split; [exact Hb2|]. split.
    { rewrite <- Hstep. exact Hv2'. }
    split; [ecancel_assumption|].
    split.
    { rewrite map.get_put_diff by congruence. rewrite map.get_put_same. f_equal.
      rewrite Nat2Z.inj_sub by lia. symmetry. apply word.ring_morph_sub. }
    repeat split; rewrite ?map.get_put_diff by congruence; assumption. }
Qed.


(** ** The exponent [p - 2] and Fermat *)

Lemma bls12_M_pos_prime : Znumtheory.prime (Z.pos (@PrimeField.M_pos pp)).
Proof.
  replace (@PrimeField.M_pos pp) with Prime381.p381 by (vm_compute; reflexivity).
  exact Prime381.p381_prime.
Qed.

Lemma bls12_two_lt_M : 2 < Z.pos (@PrimeField.M_pos pp).
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_inv_chain (x : Fp) :
  let step r w := F.mul (pw r (2 ^ 64)) (pw x w) in
  step (step (step (step (step (step F.one bls12_inv_w5) bls12_inv_w4) bls12_inv_w3)
          bls12_inv_w2) bls12_inv_w1) bls12_inv_w0 = F.inv x.
Proof.
  intros step. subst step. cbv beta.
  rewrite <- (pw_0 x).
  rewrite !pow_words_comb
    by (cbv [bls12_inv_w0 bls12_inv_w1 bls12_inv_w2 bls12_inv_w3 bls12_inv_w4 bls12_inv_w5]; lia).
  rewrite (@F.Fq_inv_fermat (@PrimeField.M_pos pp) bls12_M_pos_prime bls12_two_lt_M x).
  f_equal. all: vm_compute; reflexivity.
Qed.

(** ** The inverse *)

Local Notation sep_eq_l := BLS12_PairingLeavesFp2.sep_eq_l.
Local Notation sep_impl_l := BLS12_PairingLeavesFp2.sep_impl_l.

Lemma bls12_inv_ok (functions : env) :
  map.get functions "bls12_inv" = Some (snd bls12_inv) ->
  map.get functions "bls12_inv_pow_word" = Some (snd bls12_inv_pow_word) ->
  map.get functions "bls12_square" = Some (snd bls12_square) ->
  map.get functions "bls12_mul" = Some (snd bls12_mul) ->
  map.get functions "bls12_felem_copy" = Some bls12_felem_copy ->
  map.get functions "bls12_from_word" = Some (snd bls12_from_word) ->
  map.get functions "bls12_to_mont" = Some (snd bls12_to_mont) ->
  spec_of_bls12_Fp_inv' functions.
Proof.
  intros E Epw Esq Emul Ecp Efw Etm.
  pose proof (bls12_inv_pow_word_ok functions Epw Esq Emul) as Hpw.
  pose proof (bls12_Fp_felem_copy_leaf functions Ecp) as Hcp.
  pose proof (bls12_Fp_from_word_leaf_MS functions Efw Etm) as Hfw.
  clear Epw Esq Emul Ecp Efw Etm.
  cbv [spec_of_bls12_Fp_inv' AbstractField.unop_spec].
  intros pout px out x Rr tr m (Hb & [Ra HX] & HO).
  eapply start_func; [exact E | clear E].
  cbv match beta delta [WeakestPrecondition.func bls12_inv snd].
  eexists; split; [exact eq_refl|].
  repeat straightline.
  clear HX HO H1 H2 length_stack length_stack0 stack stack0.
  rename HX0 into HX, HO0 into HO.
  destruct (proj1 (AbstractField.FElem_from_bytes (field_representation:=frep) a mStack) H)
    as [old Hold].
  assert (Hm0 : (eq m1 * FElem1 a old)%sep m0) by (exists m1, mStack; auto).
  clear H H0.
  pose proof (sep_eq_l _ _ _ _ HX Hm0) as HXm.
  pose proof (sep_eq_l _ _ _ _ HO Hm0) as HOm.
  subst args.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hcp a px old x Ra (eq m1) tr m0 (conj _ _)); ecancel_assumption ].
  intros tr2 m2 rets (Hrets & Htr2 & Hm2). subst rets tr2.
  eexists; split; [reflexivity|].
  pose proof (sep_eq_l _ _ _ _ HO (proj1 (sep_comm _ _ _) Hm2)) as H2.
  clear HXm HOm Hm0 Hold HX HO Hm2.
  repeat straightline.
  subst args.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | exact (Hfw pout (word.of_Z 1) out _ tr m2 H2) ].
  intros tr3 m3 rets (Hrets & Htr3 & r0 & Hr0 & Hbr0 & Hm3). subst rets tr3.
  eexists; split; [reflexivity|].
  clear H2.
  cbv [bls12_inv_pow_call].
  repeat straightline.
  subst args.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hpw pout a _ r0 x Rr tr _ (conj Hbr0 (conj Hb _))); ecancel_assumption ].
  intros tr0 m0' rets0 (Hrets0 & Htr0 & r1 & Hr1 & Hbr1 & Hmr1). subst rets0 tr0.
  eexists; split; [reflexivity|].
  clear Hm3.
  repeat straightline.
  subst args.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hpw pout a _ r1 x Rr tr _ (conj Hbr1 (conj Hb _))); ecancel_assumption ].
  intros tr1 m1' rets1 (Hrets1 & Htr1 & r2 & Hr2 & Hbr2 & Hmr2). subst rets1 tr1.
  eexists; split; [reflexivity|].
  clear Hmr1.
  repeat straightline.
  subst args.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hpw pout a _ r2 x Rr tr _ (conj Hbr2 (conj Hb _))); ecancel_assumption ].
  intros tr2 m2' rets2 (Hrets2 & Htr2 & r3 & Hr3 & Hbr3 & Hmr3). subst rets2 tr2.
  eexists; split; [reflexivity|].
  clear Hmr2.
  repeat straightline.
  subst args.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hpw pout a _ r3 x Rr tr _ (conj Hbr3 (conj Hb _))); ecancel_assumption ].
  intros tr3 m3' rets3 (Hrets3 & Htr3 & r4 & Hr4 & Hbr4 & Hmr4). subst rets3 tr3.
  eexists; split; [reflexivity|].
  clear Hmr3.
  repeat straightline.
  subst args.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hpw pout a _ r4 x Rr tr _ (conj Hbr4 (conj Hb _))); ecancel_assumption ].
  intros tr4 m4' rets4 (Hrets4 & Htr4 & r5 & Hr5 & Hbr5 & Hmr5). subst rets4 tr4.
  eexists; split; [reflexivity|].
  clear Hmr4.
  repeat straightline.
  subst args.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hpw pout a _ r5 x Rr tr _ (conj Hbr5 (conj Hb _))); ecancel_assumption ].
  intros tr5 m5' rets5 (Hrets5 & Htr5 & r6 & Hr6 & Hbr6 & Hmr6). subst rets5 tr5.
  eexists; split; [reflexivity|].
  clear Hmr5.
  repeat straightline.
  assert (H14 : (FElem1 a x * (FElem1 pout r6 * Rr))%sep m5') by ecancel_assumption.
  clear Hmr6.
  apply (sep_impl_l _ _ _ _ (AbstractField.FElem_to_bytes a _)) in H14.
  destruct H14 as (mS & mR & Hs & HS & HR).
  exists mR, mS. split; [exact HS|]. split; [apply map.split_comm; exact Hs|].
  cbn [list_map]. split; [reflexivity|]. split; [reflexivity|].
  exists r6. split; [|split; [exact Hbr6 | exact HR]].
  transitivity (F.inv (feval1 x)); [| reflexivity].
  assert (Hr0' : feval1 r0 = F.one).
  { rewrite Hr0, word.unsigned_of_Z_nowrap by lia. reflexivity. }
  rewrite Hr6, Hr5, Hr4, Hr3, Hr2, Hr1, Hr0'.
  rewrite !word.unsigned_of_Z_nowrap
    by (cbv [bls12_inv_w0 bls12_inv_w1 bls12_inv_w2 bls12_inv_w3 bls12_inv_w4 bls12_inv_w5]; lia).
  exact (bls12_inv_chain (feval1 x)).
Qed.
