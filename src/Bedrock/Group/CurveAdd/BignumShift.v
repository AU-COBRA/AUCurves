Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Bedrock.Field.Synthesis.Examples.ArrayUtil.
(* Require Import Crypto.Bedrock.Specs.Field. *)
Local Open Scope Z_scope.

Section generic.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {scalar_words : nat}.

  (* Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}. *)

  (* Condider incorporating this into FieldRepresentation (though this is not a field, so the class should be generalized)
     Or maybe make a BignumRepresentation class *)
  Local Notation eval n x := (Positional.eval (uweight width) n (List.map word.unsigned x)).

  Instance spec_of_shift_scalar : spec_of "shift_scalar" :=
    fnspec! "shift_scalar"
          (pc px : word)
          / c x R,
    { requires tr mem :=
        (Bignum scalar_words px x ⋆ scalar pc c ⋆ R) mem;
      ensures tr' mem' :=
        exists c' x' (* output values *),
          tr = tr'
          /\ eval scalar_words x / 2 = eval scalar_words x'
          /\ eval scalar_words x mod 2 = word.unsigned c'
          /\ ((Bignum scalar_words px x' ⋆ scalar pc c' ⋆ R) mem')}.

    Local Infix "+w" := word.add (at level 80).
    Local Infix "*w" := word.mul (at level 70).
    Local Infix ">>w" := word.sru (at level 60).
    Local Infix "<<w" := word.slu (at level 60).

    Definition bignum_shiftr n (l : list (@word.rep width word)) :=
      (List.map
         (fun i =>
            ((nth_default (word.of_Z 0) l i) >>w (word.of_Z 1)) +w
              ((nth_default (word.of_Z 0) l (S i)) <<w (word.of_Z (width - 1))))
         (seq 0 (n - 1))) ++ [(nth_default (word.of_Z 0) l (n - 1)) >>w (word.of_Z 1)].

    Lemma eval_shift l n :
      Datatypes.length l = n ->
      eval n l / 2 =
        eval n (bignum_shiftr n l).
    Proof.
      intros.
      generalize dependent n. induction l; intros; subst.
      - now rewrite !Positional.eval0.
      - unfold bignum_shiftr; simpl.
        rewrite !Positional.eval_cons, uweight_eval_shift.
        destruct l.
        + simpl.
          rewrite Positional.eval_cons, uweight_0, Positional.eval0, ListUtil.nth_default_cons, uweight_eq_alt',
            Z.mul_0_r, !Z.add_0_r, !Z.mul_1_l.
          rewrite word.unsigned_sru_nowrap.
          rewrite word.unsigned_of_Z_1.
          rewrite Z.shiftr_div_pow2.
          reflexivity. lia.
          rewrite word.unsigned_of_Z_1.
          destruct width_cases; lia.
          reflexivity.
        + remember (r :: l).
          rewrite Heql0 at 4 5.
          simpl.
          rewrite !Positional.eval_cons, uweight_eval_shift.
          replace ((List.map _ _) ++ _) with (bignum_shiftr (length l0) (r :: l)).
          { rewrite <- Heql0. rewrite <- IHl; auto.
            rewrite uweight_0, ListUtil.nth_default_cons_S, uweight_eq_alt'.
            rewrite !ListUtil.nth_default_cons, !Z.mul_1_l, !Z.mul_1_r.
            rewrite !word.unsigned_add.
            rewrite !word.unsigned_sru_nowrap.
            rewrite !word.unsigned_slu.
            rewrite word.unsigned_of_Z_1.

            replace (2 ^ width) with (2 * 2 ^ (width - 1)) at 1.
            rewrite <- Z.mul_assoc.
            rewrite Z.mul_comm.
            (* G2: 2 * 2^(w-1) = 2^w *)
            2: { rewrite <- Z.pow_succ_r by (destruct width_cases; lia).
                 f_equal. lia. }
            (* G3: word.unsigned (word.of_Z (width - 1)) < width *)
            2: { rewrite word.unsigned_of_Z. unfold word.wrap.
                 destruct width_cases as [Hw|Hw]; rewrite Hw;
                 rewrite Z.mod_small by lia; lia. }
            (* G4: word.unsigned (word.of_Z 1) < width *)
            2: { rewrite word.unsigned_of_Z_1. destruct width_cases; lia. }
            (* G1: main arithmetic *)
            rewrite Z.add_comm, Z.div_add_l by lia.
            rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
            assert (Hwm1: word.unsigned (@word.of_Z _ word (width - 1)) = width - 1).
            { rewrite word.unsigned_of_Z. unfold word.wrap.
              apply Z.mod_small. destruct width_cases as [Hw|Hw]; rewrite Hw; lia. }
            rewrite Hwm1.
            rewrite Z.shiftl_mul_pow2 by (destruct width_cases; lia).
            set (ua := word.unsigned a).
            set (b := word.unsigned (nth_default (word.of_Z 0) l0 0)).
            set (E := eval (Datatypes.length l0) l0).
            pose proof (word.unsigned_range a) as [Hau0 Hau1]. fold ua in Hau0, Hau1.
            assert (Hb : 0 <= b < 2 ^ width) by (subst b; apply word.unsigned_range).
            assert (Hwp : 1 < width) by (destruct width_cases; lia).
            assert (Hp1 : 0 < 2 ^ (width - 1)) by (apply Z.pow_pos_nonneg; lia).
            assert (Hp2 : 2 * 2 ^ (width - 1) = 2 ^ width).
            { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
            assert (Hwb: word.wrap (b * 2 ^ (width - 1)) = (b mod 2) * 2 ^ (width - 1)).
            { unfold word.wrap.
              rewrite (Z.div_mod b 2) at 1 by lia.
              replace ((2 * (b / 2) + b mod 2) * 2 ^ (width - 1))
                with (b mod 2 * 2 ^ (width - 1) + b / 2 * (2 * 2 ^ (width - 1))) by ring.
              rewrite Hp2, Z_mod_plus_full.
              apply Z.mod_small.
              assert (0 <= b mod 2 < 2) by (apply Z.mod_pos_bound; lia).
              split; [nia|nia]. }
            rewrite Hwb.
            assert (Hwa: word.wrap (ua / 2 + b mod 2 * 2 ^ (width - 1)) =
                         ua / 2 + b mod 2 * 2 ^ (width - 1)).
            { unfold word.wrap. apply Z.mod_small.
              assert (0 <= b mod 2 < 2) by (apply Z.mod_pos_bound; lia).
              split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos|]; nia|].
              assert (ua / 2 < 2 ^ (width - 1)).
              { apply Z.div_lt_upper_bound; nia. }
              nia. }
            rewrite Hwa.
            assert (HbE: b mod 2 = E mod 2).
            { subst b E. rewrite Heql0.
              cbn [List.map Datatypes.length nth_default].
              rewrite Positional.eval_cons by (rewrite ?map_length; reflexivity).
              rewrite uweight_eval_shift;
                [| destruct width_cases; lia | rewrite ?map_length; reflexivity].
              rewrite uweight_0, uweight_1, Z.mul_1_l.
              rewrite Zplus_mod.
              replace (2 ^ width) with (2 * 2 ^ (width - 1))
                by (rewrite <- Z.pow_succ_r by (destruct width_cases; lia); f_equal; lia).
              rewrite <- Z.mul_assoc, (Z.mul_comm 2), Z_mod_mult, Z.add_0_r, Zmod_mod.
              reflexivity. }
            rewrite HbE.
            assert (HEM: E = 2 * (E / 2) + E mod 2) by (apply Z.div_mod; lia).
            nia. }
          { (* replace sub-goal *)
            subst l0. unfold bignum_shiftr.
            cbn [Datatypes.length Nat.sub].
            rewrite !Nat.sub_0_r.
            rewrite <- seq_shift, map_map.
            f_equal. }
          (* side conditions from rewrites on line 77 *)
          all: try (destruct width_cases; lia).
          all: try (rewrite ?map_app, ?app_length, ?map_length, ?seq_length;
                    try subst l0; simpl; lia).
          all: try (rewrite ?map_length; reflexivity).
        (* side conditions from rewrite on line 62 *)
        + destruct width_cases; lia.
        + rewrite map_length; reflexivity.
        + rewrite map_length; reflexivity.
    Qed.

End generic.

(* I make an implementation where scalar_words is 4, figure out how to do it generally (maybe implement it using fiat) *)
Section impl.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Require Import bedrock2.NotationsCustomEntry.
  Require Import bedrock2.WeakestPrecondition.
  Import Syntax BinInt String List.ListNotations.
  Local Open Scope string_scope.
  Local Open Scope Z_scope.
  Local Open Scope list_scope.

  (* Local Infix "x & y" := (expr.op bopname.and (expr.load access_size.word x) (expr.literal y)) (at level 90). *)
  (* Local Infix "x ++ y" := (expr.op bopname.add x (expr.literal y)) (at level 90). *)

  Local Notation get := (expr.load access_size.word).
  Local Notation and := (expr.op bopname.and).
  Local Notation store := (cmd.store access_size.word).
  Local Notation lit := (expr.literal).
  Local Notation sr1 x := (expr.op bopname.sru x (expr.literal 1)).
  Local Notation sl7 x := (expr.op bopname.slu x (expr.literal (width - 1))).
  Local Notation add_words x y := (expr.op bopname.add x y).
  (* Local Notation add8 x := (expr.op bopname.add (expr.var x) (expr.literal 8)). *)
  Local Notation addany n x := (expr.op bopname.add (expr.var x) (expr.literal n)).
  (* Local Notation op1 carry scalar n := (store (expr.var carry) (and (get ( addany n scalar)) (lit 1))). *)
  (* Local Notation op2 carry := ( store (expr.var carry) (sl7 (get (expr.var carry)))). *)
  (* Local Notation op3 carry scalar n := ( store (addany n scalar) (add_words ((sr1 (get (addany n scalar)))) (get (expr.var carry)))). *)
  (* Local Notation op4 carry n := (store (addany n carry) (expr.literal 0)). *)

  Instance spec_of_shift_scalar6 : spec_of "shift_scalar" := spec_of_shift_scalar (scalar_words := 4).

    (* Definition shift_scalar : bedrock2.Syntax.func := *)
    (*     ("shift_scalar", (["c2"; "scalar"], []:list String.string, bedrock_func_body:( *)
    (*         stackalloc (Memory.bytes_per_word width) as carry; *)

    (*         coq:( store (expr.var "c2") (and (get (expr.var "scalar")) (lit 1))); *)

    (*         coq:( fold_right *)
    (*                (fun n c => cmd.seq c *)
    (*                           (cmd.seq (store (expr.var "carry") (and (get (addany ((Z.of_nat n + 1) * 8) "scalar")) (lit 1))) *)
    (*                              (cmd.seq (store (expr.var "carry") (sl7 (get (expr.var "carry")))) *)
    (*                                 (store (expr.var "scalar") (add_words (sr1 (get (addany (Z.of_nat n * 8) "scalar"))) (get (expr.var "carry"))))))) *)
    (*                cmd.skip (seq 0 scalar_words)); *)

    (*         coq:( store (addany (Z.of_nat scalar_words * 8) "scalar") (sr1 (get (addany (Z.of_nat scalar_words * 8) "scalar"))))))). *)

  Local Notation bytes := (Memory.bytes_per_word width).

    Definition shift_scalar : bedrock2.Syntax.func :=
        (["c2"; "scalar"], []:list String.string, bedrock_func_body:(
            stackalloc bytes as carry;

            coq:( store (expr.var "c2") (and (get (expr.var "scalar")) (lit 1)));
            coq:( store (expr.var "carry")
                    (and (get (addany bytes "scalar")) (lit 1)));
            coq:( store (expr.var "carry")
                    (sl7 (get (expr.var "carry"))));
            coq:( store (expr.var "scalar")
                    (add_words (sr1 (get (expr.var "scalar"))) (get (expr.var "carry"))));

            coq:( store (expr.var "carry")
                    (and (get (addany (2 * bytes) "scalar")) (lit 1)));
            coq:( store (expr.var "carry")
                    (sl7 (get (expr.var "carry"))));
            coq:( store (addany bytes "scalar")
                    (add_words (sr1 (get (addany bytes "scalar"))) (get (expr.var "carry"))));

            coq:( store (expr.var "carry")
                    (and (get (addany (3 * bytes) "scalar")) (lit 1)));
            coq:( store (expr.var "carry")
                    (sl7 (get (expr.var "carry"))));
            coq:( store (addany (2 * bytes) "scalar")
                    (add_words (sr1 (get (addany (2 * bytes) "scalar"))) (get (expr.var "carry"))));

            coq:( store (addany (3 * bytes) "scalar")
                    (sr1 (get (addany (3 * bytes) "scalar")))))).

        (* From bedrock2 Require Import ToCString Bytedump. *)
        (* Definition c_mod := (c_module (shift_scalar :: nil)). *)

        (* Eval native_compute in c_mod. *)

    Ltac solve_locals l :=
        subst l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

    Ltac solve_locals2 l0 l :=
        subst l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.
        
    Ltac solve_locals3 l1 l0 l :=
        subst l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

    Ltac solve_locals4 l2 l1 l0 l :=
        subst l2 l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

    Ltac solve_locals5 l3 l2 l1 l0 l :=
        subst l3 l2 l1 l0 l; repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same.

                
        (* Lemma alloc_to_FElem : forall a m, Memory.anybytes a felem_size_in_bytes m -> exists f, Field.FElem a f m.
        Proof.
          intros. eapply anybytes_to_array_1 in H. destruct H, H. cbv [felem_size_in_bytes] in *.
          eapply (Bignum.Bignum_of_bytes felem_size_in_words) in H; try lia.
          eexists. cbv [Field.FElem]. eauto.
        Qed. *)
    Opaque Memory.bytes_per_word.
    Opaque Z.mul.
    Add Ring __wring: (@word.ring_theory width word word_ok)
      (preprocess [autorewrite with rew_word_morphism],
       morphism (@word.ring_morph width word word_ok),
       constants [Properties.word_cst]).

    Ltac update_mem :=
      match goal with
      | Hsplit : map.split ?comb ?mem ?stack |- _ =>
          match goal with
          | Hold_mem : ?p mem,
              Hstack : Memory.anybytes ?a (Memory.bytes_per_word _) stack
            |- _ =>
              let x := fresh "x" in
              let Hmem := fresh "Hmem" in
              eapply anybytes_to_scalar in Hstack as [x Hstack]
              ; eassert (Hnew_mem : (p ⋆ scalar a x) comb) by (eexists; eauto)
              ; clear dependent mem
              ; clear dependent stack
              ; rename Hnew_mem into Hmem
          end
      end.

    Ltac straightline' :=
        match goal with
        | |- ?a mod ?a = 0 => eapply Z_mod_same_full
        (* | _ => update_mem *)
        | _ => straightline
        | l := _ : map.rep |- _ => subst l
        | l := _ : list word.rep |- _ => subst l
        | |- Some _ = Some _ => try reflexivity
        | |- exists _, _ => eexists
        | |- _ /\ _ => split
        | |- map.get _ _ = _ => repeat (erewrite map.get_put_diff; [| intros contra; discriminate]); eapply map.get_put_same
        end.

    Local Infix "+w" := word.add (at level 80).
    Local Infix "*w" := word.mul (at level 70).
    Local Infix ">>w" := word.sru (at level 60).
    Local Infix "<<w" := word.slu (at level 60).

    Lemma width_pos : 1 < width.
    Proof. destruct width_cases; lia. Qed.

    (* (w & 1) << (width-1) = w << (width-1) as words:
       only bit 0 survives a left shift by width-1. *)
    Lemma slu_and1_width_minus_1 (w : @word.rep width word) :
      word.slu (word.and w (word.of_Z 1)) (word.of_Z (width - 1)) =
      word.slu w (word.of_Z (width - 1)).
    Proof.
      apply word.unsigned_inj.
      pose proof (word.unsigned_range w) as Hwr.
      assert (Hwp: 1 < width) by (destruct width_cases; lia).
      rewrite !word.unsigned_slu_shamtZ by lia.
      unfold word.wrap.
      rewrite word.unsigned_and_nowrap, word.unsigned_of_Z_1.
      rewrite !Z.shiftl_mul_pow2 by lia.
      (* Z.land (unsigned w) 1 * 2^(w-1) mod 2^w = unsigned w * 2^(w-1) mod 2^w *)
      replace (Z.land (word.unsigned w) 1) with (word.unsigned w mod 2).
      2: { replace 1 with (Z.ones 1) by reflexivity.
           rewrite Z.land_ones by lia. reflexivity. }
      replace (2 ^ width) with (2 * 2 ^ (width - 1))
        by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
      assert (Hdm: word.unsigned w = 2 * (word.unsigned w / 2) + word.unsigned w mod 2)
        by (apply Z.div_mod; lia).
      rewrite Hdm at 2.
      replace ((2 * (word.unsigned w / 2) + word.unsigned w mod 2) * 2 ^ (width - 1))
        with (word.unsigned w mod 2 * 2 ^ (width - 1) +
              word.unsigned w / 2 * (2 * 2 ^ (width - 1))) by ring.
      rewrite Z_mod_plus_full. reflexivity.
    Qed.

    Lemma cmov_ok : program_logic_goal_for_function! shift_scalar.
    Proof.
      cbv [program_logic_goal_for].
      cbv beta match delta [shift_scalar].
      unfold spec_of_shift_scalar6, spec_of_shift_scalar.
      intros.
      eapply WeakestPreconditionProperties.start_func; [exact EnvContains | clear EnvContains].
      cbv match beta delta [WeakestPrecondition.func].
      (* Step through cmd.seq and stackalloc manually to get anybytes *)
      repeat straightline.
      (* After straightline_stackalloc, we have byte array for stack.
         Decompose Bignum 4 px x into individual scalars for loads/stores. *)
      cbv [Bignum array] in *.
      repeat straightline.
      (* Stackalloc: bytes mod bytes = 0 /\ forall a mStack ..., anybytes -> split -> WP *)
      split. { apply Z_mod_same_full. }
      intros.
      (* Extract length from Bignum in H before update_mem consumes it *)
      assert (Hlen : Datatypes.length x = 4%nat).
      { pose proof H as Hb. cbv [Bignum] in Hb.
        (* sep = exists mp mq, split /\ P /\ Q; emp P m = m = empty /\ P *)
        repeat match goal with
        | Hb : sep _ _ _ |- _ => destruct Hb as (?&?&?&Hb&?)
        | Hb : emp _ _ |- _ => cbv [emp] in Hb; destruct Hb; assumption
        end. }
      (* Destruct x into 4 words *)
      do 4 (destruct x as [|? x]; [simpl in Hlen; lia|]).
      destruct x; [|simpl in Hlen; lia]. clear Hlen.
      (* Convert stack anybytes to scalar *)
      update_mem.
      (* Unfold Bignum and reduce array on the concrete 4-element list *)
      cbv [Bignum] in Hmem.
      cbn [array] in Hmem.
      (* Normalize iterated addresses to match flat code addresses *)
      replace ((px +w word.of_Z bytes) +w word.of_Z bytes)
        with (px +w word.of_Z (2 * bytes)) in Hmem by ring.
      replace ((px +w word.of_Z (2 * bytes)) +w word.of_Z bytes)
        with (px +w word.of_Z (3 * bytes)) in Hmem by ring.
      (* Process all stores/loads, stop at stack dealloc postcondition *)
      repeat match goal with
      | v := _ : word.rep |- _ => subst v
      | _ => lazymatch goal with
             | |- exists _ _, Memory.anybytes _ _ _ /\ _ => fail
             | _ => straightline'
             end
      end.
      (* Clear intermediate store hypotheses to reduce memory *)
      clear Hmem H H0 H1 H2 H3 H4 H5 H6 H7 H8.
      (* Separate stack scalar at address a from final memory *)
      eassert (Hsep_split : (sep _ (scalar a _)) m9) by ecancel_assumption.
      destruct Hsep_split as (m_ret & m_stk & Hsplit_mem & Hret & Hstk).
      eapply Scalars.scalar_to_anybytes in Hstk.
      clear H9.
      (* Provide stack dealloc witnesses *)
      exists m_ret, m_stk.
      split. { exact Hstk. }
      split. { exact Hsplit_mem. }
      (* list_map for empty return values *)
      cbv beta delta [list_map].
      split. { reflexivity. }
      (* Postcondition witnesses *)
      exists (word.and r (word.of_Z 1)), (bignum_shiftr 4 [r; r0; r1; r2]).
      refine (conj eq_refl (conj _ (conj _ _))).
      { apply eval_shift. reflexivity. }
      { transitivity (word.unsigned r mod 2).
        - (* eval 4 [r; r0; r1; r2] mod 2 = word.unsigned r mod 2 *)
          cbn [List.map].
          rewrite Positional.eval_cons by reflexivity.
          rewrite uweight_eval_shift;
            [| destruct width_cases; lia | reflexivity].
          rewrite uweight_0, uweight_1, Z.mul_1_l.
          rewrite Zplus_mod.
          replace (2 ^ width) with (2 * 2 ^ (width - 1))
            by (rewrite <- Z.pow_succ_r by (destruct width_cases; lia); f_equal; lia).
          rewrite <- Z.mul_assoc, (Z.mul_comm 2), Z_mod_mult, Z.add_0_r, Zmod_mod.
          reflexivity.
        - (* word.unsigned r mod 2 = word.unsigned (word.and r (word.of_Z 1)) *)
          symmetry.
          rewrite word.unsigned_and_nowrap, word.unsigned_of_Z_1.
          replace 1 with (Z.ones 1) by reflexivity.
          rewrite Z.land_ones by lia.
          reflexivity. }
      { cbv [bignum_shiftr].
        cbn [seq Datatypes.length Nat.sub List.map nth_default app array].
        change (Memory.bytes_per_word width) with bytes.
        replace ((px +w word.of_Z bytes) +w word.of_Z bytes)
          with (px +w word.of_Z (2 * bytes)) by ring.
        replace ((px +w word.of_Z (2 * bytes)) +w word.of_Z bytes)
          with (px +w word.of_Z (3 * bytes)) by ring.
        rewrite <- !(slu_and1_width_minus_1).
        ecancel_assumption. }
    Qed.

End impl.
