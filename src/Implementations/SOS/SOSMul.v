Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LinearSubstitute.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

(*Implementation of the multiplication part of the Separated Operand Scanning method of Montgomery multiplication
  for more details, see section 4 of https://www.microsoft.com/en-us/research/wp-content/uploads/1996/01/j37acmon.pdf
  The implementation is designed to compatible with the Fiat Crypto pipeline, so that efficient code can be extracted.
  Note that some parts were copied from Fiat Crypto, this is made clear when appropriate.*)

Module WordByWordMontgomery.
  Section with_args.
    (*... This part (until next ...) is copied from Fiat Crypto Arithmetic/WordByWordMontgomery*)
          Context (lgr : Z)
                  (m : Z).
          Local Notation weight := (uweight lgr).
          Let T (n : nat) := list Z.
          Let r := (2^lgr).
          Definition eval {n} : T n -> Z := Positional.eval weight n.
          Let zero {n} : T n := Positional.zeros n.
          Let divmod {n} : T (S n) -> T n * Z := Rows.divmod.
          Let scmul {n} (c : Z) (p : T n) : T (S n) (* uses double-output multiply *)
            := let '(v, c) := Rows.mul weight r n (S n) (Positional.extend_to_length 1 n [c]) p in
              v.
          Let addT {n} (p q : T n) : T (S n) (* joins carry *)
            := let '(v, c) := Rows.add weight n p q in
              v ++ [c].
          Let drop_high_addT' {n} (p : T (S n)) (q : T n) : T (S n) (* drops carry *)
            := fst (Rows.add weight (S n) p (Positional.extend_to_length n (S n) q)).
          Let conditional_sub {n} (arg : T (S n)) (N : T n) : T n  (* computes [arg - N] if [N <= arg], and drops high bit *)
            := Positional.drop_high_to_length n (Rows.conditional_sub weight (S n) arg (Positional.extend_to_length n (S n) N)).
          Context (R_numlimbs : nat)
                  (N : T R_numlimbs). (* encoding of m *)
          Let T_app {n} (p : T n) (e : Z) : T (S n)
              := p ++ [e].
          Let sub_then_maybe_add (a b : T R_numlimbs) : T R_numlimbs (* computes [a - b + if (a - b) <? 0 then N else 0] *)
            := fst (Rows.sub_then_maybe_add weight R_numlimbs (r-1) a b N).
    (*... *)


    Section mul_Iteration. (*This section defines the body of the loop*)
        Context (pred_A_numlimbs : nat)
                (pred_x_numlimbs : nat)
                (B : T R_numlimbs) (k : Z)
                (A : T (S pred_A_numlimbs))
                (x : T pred_x_numlimbs)
                (S : T (S R_numlimbs)).

        Local Definition A_a := dlet p := @divmod _ A in p. Local Definition A' := fst A_a. Local Definition a := snd A_a.
        Local Definition S1 := @addT _ S (@scmul _ a B).
        Local Definition S2_x1 := (@divmod _ S1).
        Local Definition S2 := fst S2_x1.
        Local Definition x1 := snd S2_x1.
        Local Definition x' := T_app x x1.

        Local Definition A'_x'_S2
        := dlet A_a := @divmod _ A in
            dlet A' := fst A_a in
            dlet a := snd A_a in
            dlet S1 := @addT _ S (@scmul _ a B) in
            dlet S2_x1 := @divmod _ S1 in
            dlet S2 := fst S2_x1 in
            dlet x1 := snd S2_x1 in
            dlet x' := T_app x x1 in
            (A', x', S2).


        Local Definition A'_x'_S2'
        := dlet A_a := @divmod pred_A_numlimbs A in
            dlet A' := fst A_a in
            dlet a := snd A_a in
            dlet S1 := @addT _ S (@scmul _ a B) in
            dlet S2_x1 := @divmod _ S1 in
            dlet S2 := fst S2_x1 in
            dlet x1 := snd S2_x1 in
            (A', x1, S2).



        Lemma A'_x'_S2_alt : A'_x'_S2 = (A',x', S2).
        Proof using Type. cbv [A'_x'_S2 A' S2 Let_In x1 S2_x1 S1 A' a A_a]; reflexivity. Qed.
    End mul_Iteration.

    Section mul_loop. (*This section defines the looping function*)
        Context (A_numlimbs : nat)
                (A : T A_numlimbs)
                (B : T R_numlimbs)
                (k : Z)
                (S' : T (S R_numlimbs)).

        Definition mul_body {pred_A_numlimbs pred_x_numlimbs} : T (S pred_A_numlimbs) * T pred_x_numlimbs * T (S R_numlimbs)
        -> T pred_A_numlimbs * T (S pred_x_numlimbs) * T (S R_numlimbs)
        := fun '(A, x, S') => A'_x'_S2 pred_A_numlimbs pred_x_numlimbs B A x S'.

        Definition mul_loop (init : nat) (count : nat) : T (R_numlimbs - init) * T init * T (S R_numlimbs) -> T (R_numlimbs - (init + count)) * T (init + count) * T (S R_numlimbs)
        := nat_rect
                (fun count => T (R_numlimbs - init) * T init * T (S R_numlimbs) -> T (R_numlimbs - (init + count)) * T (init + count) * T (S R_numlimbs))
                (fun A_x_S => A_x_S)
                (fun count' mul_loop_count' A_x_S
                => mul_loop_count' (@mul_body ((R_numlimbs - (init + count))) (init) A_x_S))   
                count.

        Definition pre_mul : T (2 * R_numlimbs + 1)
        := let res := (mul_loop O A_numlimbs (A, [], @zero (1 + R_numlimbs))) in
            snd (fst res) ++ (snd res).

        Definition mul : T (2 * R_numlimbs) := firstn (2 * R_numlimbs) pre_mul.
    End mul_loop.

    (*... This part (until next ...) is copied from Fiat Crypto Arithmetic/WordByWordMontgomery*)
          Create HintDb word_by_word_montgomery.

          Definition add (A B : T R_numlimbs) : T R_numlimbs
            := conditional_sub (@addT _ A B) N.
          Definition sub (A B : T R_numlimbs) : T R_numlimbs
            := sub_then_maybe_add A B.
          Definition opp (A : T R_numlimbs) : T R_numlimbs
            := sub (@zero _) A.
          Definition nonzero (A : list Z) : Z
            := fold_right Z.lor 0 A.

          Context (lgr_big : 0 < lgr)
                  (R_numlimbs_nz : R_numlimbs <> 0%nat).
          Let R := (r^Z.of_nat R_numlimbs).
          Definition small {n} (v : T n) : Prop
            := v = Partition.partition weight n (eval v).
          Definition sc_small sc : Prop
            := 0 <= sc < r.
          Context (small_N : small N)
                  (N_lt_R : eval N < R)
                  (N_nz : 0 < eval N)
                  (B : T R_numlimbs)
                  (B_bounds : 0 <= eval B < R)
                  (small_B : small B)
                  (B_length : length B = R_numlimbs)
                  ri (ri_correct : r*ri mod (eval N) = 1 mod (eval N))
                  (k : Z) (k_correct : k * eval N mod r = (-1) mod r).

          Local Lemma r_big : r > 1.
          Proof using lgr_big. clear -lgr_big; subst r. auto with zarith. Qed.
          Local Notation wprops := (@uwprops lgr lgr_big).

          Local Hint Immediate (wprops) : core.
          Local Hint Immediate (weight_0 wprops) : core.
          Local Hint Immediate (weight_positive wprops) : core.
          Local Hint Immediate (weight_multiples wprops) : core.
          Local Hint Immediate (weight_divides wprops) : core.
          Local Hint Immediate r_big : core.

          Lemma length_small {n v} : @small n v -> length v = n.
          Proof using Type. clear; cbv [small]; intro H; rewrite H; autorewrite with distr_length; reflexivity. Qed.
          Lemma small_bound {n v} : @small n v -> 0 <= eval v < weight n.
          Proof using lgr_big. clear - lgr_big; cbv [small eval]; intro H; rewrite H; autorewrite with push_eval; auto with zarith. Qed.

          Lemma R_plusR_le : R + R <= weight (S R_numlimbs).
          Proof using lgr_big.
            clear - lgr_big.
            etransitivity; [ | apply uweight_double_le; lia ].
            rewrite uweight_eq_alt by lia.
            subst r R; lia.
          Qed.

          Lemma mask_r_sub1 n x :
            map (Z.land (r - 1)) (Partition.partition weight n x) = Partition.partition weight n x.
          Proof using lgr_big.
            clear - lgr_big. cbv [Partition.partition].
            rewrite map_map. apply map_ext; intros.
            rewrite uweight_S by lia.
            rewrite <-Z.mod_pull_div by auto with zarith.
            replace (r - 1) with (Z.ones lgr) by (rewrite Z.ones_equiv; subst r; reflexivity).
            rewrite <-Z.land_comm, Z.land_ones by lia.
            auto with zarith.
          Qed.

          Let partition_Proper := (@Partition.partition_Proper _ wprops).
          Local Existing Instance partition_Proper.
          Lemma eval_nonzero n A : @small n A -> nonzero A = 0 <-> @eval n A = 0.
          Proof using lgr_big.
            clear -lgr_big partition_Proper.
            cbv [nonzero eval small]; intro Heq.
            do 2 rewrite Heq.
            rewrite !eval_partition, Z.mod_mod by auto with zarith.
            generalize (Positional.eval weight n A); clear Heq A.
            induction n as [|n IHn].
            { cbn; rewrite weight_0 by auto; intros; autorewrite with zsimplify_const; lia. }
            { intro; rewrite partition_step.
              rewrite fold_right_snoc, Z.lor_comm, <- fold_right_push, Z.lor_eq_0_iff by auto using Z.lor_assoc.
              assert (Heq : Z.equiv_modulo (weight n) (z mod weight (S n)) (z mod (weight n))).
              { cbv [Z.equiv_modulo].
                generalize (weight_multiples ltac:(auto) n).
                generalize (weight_positive ltac:(auto) n).
                generalize (weight_positive ltac:(auto) (S n)).
                generalize (weight (S n)) (weight n); clear; intros wsn wn.
                clear; intros.
                Z.div_mod_to_quot_rem; subst.
                autorewrite with zsimplify_const in *.
                Z.linear_substitute_all.
                apply Zminus_eq; ring_simplify.
                rewrite <- !Z.add_opp_r, !Z.mul_opp_comm, <- !Z.mul_opp_r, <- !Z.mul_assoc.
                rewrite <- !Z.mul_add_distr_l, Z.mul_eq_0.
                nia. }
              rewrite Heq at 1; rewrite IHn.
              rewrite Z.mod_mod by auto with zarith.
              generalize (weight_multiples ltac:(auto) n).
              generalize (weight_positive ltac:(auto) n).
              generalize (weight_positive ltac:(auto) (S n)).
              generalize (weight (S n)) (weight n); clear; intros wsn wn; intros.
              Z.div_mod_to_quot_rem.
              repeat (intro || apply conj); destruct_head'_or; try lia; destruct_head'_and; subst; autorewrite with zsimplify_const in *; try nia;
                Z.linear_substitute_all.
              all: apply Zminus_eq; ring_simplify.
              all: rewrite <- ?Z.add_opp_r, ?Z.mul_opp_comm, <- ?Z.mul_opp_r, <- ?Z.mul_assoc.
              all: rewrite <- !Z.mul_add_distr_l, Z.mul_eq_0.
              all: nia. }
          Qed.

          Local Ltac push_step :=
            first [ progress eta_expand
                  | rewrite Rows.mul_partitions
                  | rewrite Rows.mul_div
                  | rewrite Rows.add_partitions
                  | rewrite Rows.add_div
                  | progress autorewrite with push_eval distr_length
                  | match goal with
                    | [ H : ?v = _ |- context[length ?v] ] => erewrite length_small by eassumption
                    | [ H : small ?v |- context[length ?v] ] => erewrite length_small by eassumption
                    end
                  | rewrite Positional.eval_cons by distr_length
                  | progress rewrite ?weight_0, ?uweight_1 by auto;
                    autorewrite with zsimplify_fast
                  | rewrite (weight_0 wprops)
                  | rewrite <- Z.div_mod'' by auto with lia
                  | solve [ trivial ] ].
          Local Ltac push := repeat push_step.

          Local Ltac t_step :=
            match goal with
            | [ H := _ |- _ ] => progress cbv [H] in *
            | _ => progress push_step
            | _ => progress autorewrite with zsimplify_const
            | _ => solve [ auto with lia ]
            end.

          Local Hint Unfold eval zero small divmod scmul drop_high_addT' addT R : loc.
          Local Lemma eval_zero : forall n, eval (@zero n) = 0.
          Proof using Type.
            clear; autounfold with loc; intros; autorewrite with push_eval; auto.
          Qed.
          Local Lemma small_zero : forall n, small (@zero n).
          Proof using Type.
            etransitivity; [ eapply Positional.zeros_ext_map | rewrite eval_zero ]; cbv [Partition.partition]; cbn; try reflexivity; autorewrite with distr_length; reflexivity.
          Qed.
          Local Hint Immediate small_zero : core.

          Ltac push_recursive_partition :=
            repeat match goal with
                  | _ => progress cbn [recursive_partition]
                  | H : small _ |- _ => rewrite H; clear H
                  | _ => rewrite recursive_partition_equiv by auto using wprops
                  | _ => rewrite uweight_eval_shift by distr_length
                  | _ => progress push
                  end.

          Lemma eval_div : forall n v, small v -> eval (fst (@divmod n v)) = eval v / r.
          Proof using lgr_big.
            pose proof r_big as r_big.
            clear - r_big lgr_big; intros; autounfold with loc.
            push_recursive_partition; cbn [Rows.divmod fst tl].
            autorewrite with zsimplify; reflexivity.
          Qed.
          Lemma eval_mod : forall n v, small v -> snd (@divmod n v) = eval v mod r.
          Proof using lgr_big.
            clear - lgr_big; intros; autounfold with loc.
            push_recursive_partition; cbn [Rows.divmod snd hd].
            autorewrite with zsimplify; reflexivity.
          Qed.
          Lemma small_div : forall n v, small v -> small (fst (@divmod n v)).
          Proof using lgr_big.
            pose proof r_big as r_big.
            clear - r_big lgr_big. intros; autounfold with loc.
            push_recursive_partition. cbn [Rows.divmod fst tl].
            rewrite <-recursive_partition_equiv by auto.
            rewrite <-uweight_recursive_partition_equiv with (i:=1%nat) by lia.
            push.
            apply Partition.partition_Proper; [ solve [auto] | ].
            cbv [Z.equiv_modulo]. autorewrite with zsimplify.
            reflexivity.
          Qed.

          Definition canon_rep {n} x (v : T n) : Prop :=
            (v = Partition.partition weight n x) /\ (0 <= x < weight n).
          Lemma eval_canon_rep n x v : @canon_rep n x v -> eval v = x.
          Proof using lgr_big.
            clear - lgr_big.
            cbv [canon_rep eval]; intros [Hv Hx].
            rewrite Hv. autorewrite with push_eval.
            auto using Z.mod_small.
          Qed.
          Lemma small_canon_rep n x v : @canon_rep n x v -> small v.
          Proof using lgr_big.
            clear - lgr_big.
            cbv [canon_rep eval small]; intros [Hv Hx].
            rewrite Hv. autorewrite with push_eval.
            apply partition_eq_mod; auto; [ ].
            Z.rewrite_mod_small; reflexivity.
          Qed.

          Local Lemma scmul_correct: forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> canon_rep (a * eval v) (@scmul n a v).
          Proof using lgr_big.
            pose proof r_big as r_big.
            clear - lgr_big r_big.
            autounfold with loc; intro n; destruct (zerop n); intros *; intro Hsmall; intros.
            { intros; subst; cbn; rewrite Z.add_with_get_carry_full_mod.
              split; cbn; autorewrite with zsimplify_fast; auto with zarith. }
            { rewrite (surjective_pairing (Rows.mul _ _ _ _ _ _)).
              rewrite Rows.mul_partitions by (try rewrite Hsmall; auto using length_partition, Positional.length_extend_to_length with lia).
              autorewrite with push_eval.
              rewrite Positional.eval_cons by reflexivity.
              rewrite weight_0 by auto.
              autorewrite with push_eval zsimplify_fast.
              split; [reflexivity | ].
              rewrite uweight_S, uweight_eq_alt by lia.
              subst r; nia. }
          Qed.

          Local Lemma addT_correct : forall n a b, small a -> small b -> canon_rep (eval a + eval b) (@addT n a b).
          Proof using lgr_big.
            intros n a b Ha Hb.
            generalize (length_small Ha); generalize (length_small Hb).
            generalize (small_bound Ha); generalize (small_bound Hb).
            clear -lgr_big Ha Hb.
            autounfold with loc; destruct (zerop n); subst.
            { destruct a, b; cbn; try lia; split; auto with zarith. }
            { pose proof (uweight_double_le lgr ltac:(lia) n).
              eta_expand; split; [ | lia ].
              rewrite Rows.add_partitions, Rows.add_div by auto.
              rewrite partition_step.
              Z.rewrite_mod_small; reflexivity. }
          Qed.

          Local Lemma drop_high_addT'_correct : forall n a b, small a -> small b -> canon_rep ((eval a + eval b) mod (r^Z.of_nat (S n))) (@drop_high_addT' n a b).
          Proof using lgr_big.
            intros n a b Ha Hb; generalize (length_small Ha); generalize (length_small Hb).
            clear -lgr_big Ha Hb.
            autounfold with loc in *; subst; intros.
            rewrite Rows.add_partitions by auto using Positional.length_extend_to_length.
            autorewrite with push_eval.
            split; try apply partition_eq_mod; auto; rewrite uweight_eq_alt by lia; subst r; Z.rewrite_mod_small; auto with zarith.
          Qed.

          Local Lemma conditional_sub_correct : forall v, small v -> 0 <= eval v < eval N + R -> canon_rep (eval v + (if eval N <=? eval v then -eval N else 0)) (conditional_sub v N).
          Proof using small_N lgr_big N_nz N_lt_R.
            pose proof R_plusR_le as R_plusR_le.
            clear - small_N lgr_big N_nz N_lt_R R_plusR_le.
            intros; autounfold with loc; cbv [conditional_sub].
            repeat match goal with H : small _ |- _ =>
                                  rewrite H; clear H end.
            autorewrite with push_eval.
            assert (weight R_numlimbs < weight (S R_numlimbs)) by (rewrite !uweight_eq_alt by lia; autorewrite with push_Zof_nat; auto with zarith).
            assert (eval N mod weight R_numlimbs < weight (S R_numlimbs)) by (pose proof (Z.mod_pos_bound (eval N) (weight R_numlimbs) ltac:(auto)); lia).
            rewrite Rows.conditional_sub_partitions by (repeat (autorewrite with distr_length push_eval; auto using partition_eq_mod with zarith)).
            rewrite drop_high_to_length_partition by lia.
            autorewrite with push_eval.
            assert (weight R_numlimbs = R) by (rewrite uweight_eq_alt by lia; subst R; reflexivity).
            Z.rewrite_mod_small.
            break_match; autorewrite with zsimplify_fast; Z.ltb_to_lt.
            { split; [ reflexivity | ].
              rewrite Z.add_opp_r. fold (eval N).
              auto using Z.mod_small with lia. }
            { split; auto using Z.mod_small with lia. }
          Qed.

          Local Lemma sub_then_maybe_add_correct : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> canon_rep (eval a - eval b + (if eval a - eval b <? 0 then eval N else 0)) (sub_then_maybe_add a b).
          Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R.
            pose proof mask_r_sub1 as mask_r_sub1.
            clear - small_N lgr_big R_numlimbs_nz N_nz N_lt_R mask_r_sub1.
            intros; autounfold with loc; cbv [sub_then_maybe_add].
            repeat match goal with H : small _ |- _ =>
                                  rewrite H; clear H end.
            rewrite Rows.sub_then_maybe_add_partitions by (autorewrite with push_eval distr_length; auto with zarith).
            autorewrite with push_eval.
            assert (weight R_numlimbs = R) by (rewrite uweight_eq_alt by lia; subst r R; reflexivity).
            Z.rewrite_mod_small.
            split; [ reflexivity | ].
            break_match; Z.ltb_to_lt; lia.
          Qed.

          Local Lemma eval_scmul: forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> eval (@scmul n a v) = a * eval v.
          Proof using lgr_big. eauto using scmul_correct, eval_canon_rep. Qed.
          Local Lemma small_scmul : forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> small (@scmul n a v).
          Proof using lgr_big. eauto using scmul_correct, small_canon_rep. Qed.
          Local Lemma eval_addT : forall n a b, small a -> small b -> eval (@addT n a b) = eval a + eval b.
          Proof using lgr_big. eauto using addT_correct, eval_canon_rep. Qed.
          Local Lemma small_addT : forall n a b, small a -> small b -> small (@addT n a b).
          Proof using lgr_big. eauto using addT_correct, small_canon_rep. Qed.
          Local Lemma eval_drop_high_addT' : forall n a b, small a -> small b -> eval (@drop_high_addT' n a b) = (eval a + eval b) mod (r^Z.of_nat (S n)).
          Proof using lgr_big. eauto using drop_high_addT'_correct, eval_canon_rep. Qed.
          Local Lemma small_drop_high_addT' : forall n a b, small a -> small b -> small (@drop_high_addT' n a b).
          Proof using lgr_big. eauto using drop_high_addT'_correct, small_canon_rep. Qed.
          Local Lemma eval_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> eval (conditional_sub v N) = eval v + (if eval N <=? eval v then -eval N else 0).
          Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using conditional_sub_correct, eval_canon_rep. Qed.
          Local Lemma small_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> small (conditional_sub v N).
          Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using conditional_sub_correct, small_canon_rep. Qed.
          Local Lemma eval_sub_then_maybe_add : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> eval (sub_then_maybe_add a b) = eval a - eval b + (if eval a - eval b <? 0 then eval N else 0).
          Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using sub_then_maybe_add_correct, eval_canon_rep. Qed.
          Local Lemma small_sub_then_maybe_add : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> small (sub_then_maybe_add a b).
          Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using sub_then_maybe_add_correct, small_canon_rep. Qed.
          (*... *)

    Lemma length_addT: forall n1 v1 v2, length v1 = n1 -> length v2 = n1 -> length (@addT n1 v1 v2) = S (length v1).
    Proof.
      intros n1 v1 v2 H H0. simpl. unfold addT. destruct (Rows.add weight n1 v1 v2) eqn:eq1. simpl in eq1. rewrite app_length.
      simpl. apply (f_equal (fun y => fst y)) in eq1.
      rewrite Rows.add_partitions in eq1; auto. simpl in eq1; apply (f_equal (fun y : list Z => length y)) in eq1.
      rewrite <- eq1. rewrite Partition.length_partition; auto with zarith.
    Qed.


    Lemma length_sc_mul: forall n v sc, n <> O -> length v = n -> length (@scmul n sc v) = S (length v).
    Proof.
      intros n v sc H H0. unfold scmul. destruct (Rows.mul weight r n (S n)) eqn:eq1.
      apply (f_equal (fun y => fst y)) in eq1.
      apply (f_equal (fun (y : list Z) => length y)) in eq1. rewrite Rows.length_mul in eq1; auto.
        - simpl in eq1; rewrite H0; auto.
        - simpl; rewrite Positional.length_zeros; auto with zarith.
    Qed.

    Lemma undo_div: forall n1 n2: nat, forall A : list Z, length A <> O -> A = snd (@divmod n1 A) :: (fst (@divmod n2 A)).
    Proof. intros. destruct A; [contradiction| auto]. Qed.

    Lemma fst_divmod_nil: forall n n', fst (@divmod n ([] : T n')) = [].
    Proof. auto. Qed.

    Lemma fst_divmod_app: forall n v sc, fst (@divmod n (sc :: v)) = v.
    Proof. auto. Qed.

    (*... This part (until next ...) is copied from Fiat Crypto Arithmetic/WordByWordMontgomery*)
          Local Opaque T addT drop_high_addT' divmod zero scmul conditional_sub sub_then_maybe_add.
          Create HintDb push_mont_eval discriminated.
          Create HintDb word_by_word_montgomery.
          (* Hint Unfold A'_S3 S3' S2 q s S1 a A' A_a Let_In : word_by_word_montgomery. *)
          Let r_big' := r_big. (* to put it in the context *)
          Local Ltac t_small :=
            repeat first [ assumption
                        | apply small_addT
                        | apply small_drop_high_addT'
                        | apply small_div
                        | apply small_zero
                        | apply small_scmul
                        | apply small_conditional_sub
                        | apply small_sub_then_maybe_add
                        | apply Z_mod_lt
                        | rewrite Z.mul_split_mod
                        | solve [ auto with zarith ]
                        | lia
                        | progress autorewrite with push_mont_eval
                        | progress autounfold with word_by_word_montgomery
                        | match goal with
                          | [ H : and _ _ |- _ ] => destruct H
                          end ].
          Hint Rewrite
              eval_zero
              eval_div
              eval_mod
              eval_addT
              eval_drop_high_addT'
              eval_scmul
              eval_conditional_sub
              eval_sub_then_maybe_add
              using (repeat autounfold with word_by_word_montgomery; t_small)
            : push_mont_eval.

          Local Arguments eval {_} _.
          Local Arguments small {_} _.
          Local Arguments divmod {_} _.
    (*... *)

    (*The rest of This file contains proofs of correctness; the main correctness theorems are mul_loop_good
      and mul_loop_eval_full, stating that the output is a proper multi-limb encoding af a number and that
      the encoded number evaluates to the product of the inputs respectively*)
    
    Lemma T_app_small:forall n v sc, small v -> sc_small sc -> small (@T_app n v sc).
    Proof.
      intros n v sc H H0. unfold T_app. unfold small. unfold eval. rewrite Positional.eval_snoc with (n := n); auto with zarith; [|symmetry; apply length_small; auto].
      rewrite Partition.partition_step.
      rewrite Weight.weight_mod_pull_div; auto with zarith.
      assert (H1: weight n * sc = sc * weight n) by auto with zarith. rewrite H1. rewrite Z_div_plus; auto with zarith.
      assert (H2: Positional.eval weight n v / weight n = 0); [apply Z.div_small; apply small_bound; auto|].
      rewrite H2. simpl.
      rewrite uweight_S; auto with zarith. simpl. rewrite Z_div_mult; auto with zarith. assert (H3: sc mod 2 ^lgr = sc) by (apply Z.mod_small; assumption).
      rewrite H3.
      assert (H4: (Partition.partition weight n (Positional.eval weight n v + sc * weight n)) = (Partition.partition weight n (Positional.eval weight n v))).
        - apply partition_eq_mod. auto. apply Z_mod_plus; auto with zarith.
        - rewrite H4. unfold small in H. unfold eval in H. rewrite <- H. auto.
    Qed.

    Lemma snd_divmod_sc_small: forall n v, small v -> sc_small (snd (@divmod n v)).
    Proof. intros; unfold sc_small; rewrite eval_mod; auto with zarith. Qed.

    Lemma length_T_app: forall n v sc, length (@T_app n v sc) = S (length v).
    Proof. intros; unfold T_app; rewrite app_length; simpl; auto with zarith. Qed.

    Lemma weight_S: forall i, weight (S i) = r * (weight i).
    Proof. intros. rewrite uweight_S; auto with zarith. Qed.

    Definition eval_hyp sc : list Z -> Prop
    := fun v => (@eval (S (length v)) (sc :: v) = sc + weight 1 * @eval (length v) v).

    Lemma eval_app_aux: forall v sc, @eval (S (length v)) (sc :: v) = sc + (weight 1) * @eval (length v) v.
    Proof.
      intros v sc. generalize dependent v. pose proof (@rev_ind Z (eval_hyp sc)). apply H.
        - unfold eval_hyp. unfold eval. rewrite Positional.eval_nil. unfold Positional.eval, Associational.eval, Positional.to_associational.
          simpl; pose proof wprops as H0; destruct H0; auto with zarith.
        - intros x l H0. unfold eval_hyp. unfold eval_hyp in H0. unfold eval. rewrite Positional.eval_snoc with (n := length (l)); auto; [| rewrite app_length; simpl; auto with zarith].
          assert (H1: sc :: l ++ [x] = (sc :: l) ++ [x]) by auto. rewrite H1. rewrite Positional.eval_snoc with (n := length (l ++ [x])); auto; [| rewrite app_length; simpl; auto with zarith].
          simpl. unfold eval in H0. assert (H2: length (l ++ [x]) = length (sc :: l)) by (simpl; rewrite app_length; simpl; auto with zarith).
          simpl in H2. rewrite H2. rewrite H0. simpl.
          rewrite Z.mul_add_distr_l. rewrite Z.mul_assoc.
          pose proof wprops as H3. destruct H3. rewrite (weight_S (length l)). unfold r. simpl.
          assert (H3: weight 1 = r).
            + unfold r. unfold weight. simpl. unfold ModOps.weight. simpl. auto. auto with zarith.
              rewrite Z.mul_1_r. rewrite Z.div_1_r. simpl. rewrite Z.opp_involutive. auto.
            + rewrite H3. unfold r. auto with zarith.
    Qed.
          

    Definition app_hyp v1 : list Z -> Prop
    := fun v2 => 
        (
          @eval (length v1 + length v2) (v1 ++ v2) = @eval (length v1) v1 + r ^ Z.of_nat (length v1) * @eval (length v2) v2
        ).


    Lemma eval_app: forall (n1 n2 : nat) v1 v2, length v1 = n1 -> length v2 = n2 -> @eval (n1 + n2) (v1 ++ v2) = @eval n1 v1 + (r ^ (Z.of_nat (length v1)) * (@eval n2 v2)).
    Proof.
      intros n1 n2 v1 v2. generalize dependent n1. generalize dependent n2.
      pose proof (@rev_ind Z (app_hyp v1)) as H. unfold app_hyp in H. intros n1 n2 H0 H1. unfold eval.
      rewrite <- H1. rewrite <- H0. apply H.
        - unfold eval. rewrite Positional.eval_nil. rewrite Z.mul_0_r. simpl.
          repeat rewrite Z.add_0_r. Local Close Scope Z_scope. assert (H2: length v1 + 0 = length v1) by auto.
          rewrite H2. rewrite app_nil_r. auto.
        - intros x l H2. unfold eval. rewrite app_length. simpl. rewrite Nat.add_1_r.
          assert (H3: v1 ++ l ++ [x] = (v1 ++ l) ++ [x]) by apply app_assoc. rewrite H3.
          rewrite NPeano.Nat.add_succ_r. rewrite Positional.eval_snoc_S; [| rewrite app_length; auto]. rewrite Positional.eval_snoc_S; auto.
          simpl. unfold eval in H2. rewrite H2. simpl.
          rewrite Z.mul_add_distr_l. rewrite Z.mul_assoc. rewrite uweight_sum_indices; auto with zarith.
          rewrite uweight_eq_alt; auto with zarith.
    Qed.

    Local Open Scope Z_scope.

    Lemma eval_T_app: forall v sc, eval (@T_app (length v) v sc) = @eval (length v) (v) + r^(Z.of_nat (length v)) * sc.
    Proof.
      intros v sc. unfold T_app. pose proof eval_app (length v) 1 v [sc]as H. Local Close Scope Z_scope.
      assert (H0: S (length v) = length v + 1) by auto with zarith.
      unfold eval. rewrite H0. unfold eval in H. rewrite H; auto.
      assert (H1: Positional.eval weight 1 [sc] = sc).
        - unfold Positional.eval, Positional.to_associational, Associational.eval. simpl.
          rewrite weight_0; [| apply wprops]. auto with zarith.
        - rewrite H1. auto.
    Qed.

Local Open Scope Z_scope.

    Ltac rsmallscmul := apply small_scmul.
    Ltac rsmalladdT := apply small_addT.

    Ltac assert_small_op expr := lazymatch expr with
        | scmul ?n1 ?n2 => (rsmallscmul; [assert_small_op n1|auto| auto])
        | addT ?n1 ?n2 => (rsmalladdT; [assert_small_op n1| assert_small_op n2])
        | T_app ?n1 ?n2 => apply T_app_small; [assert_small_op n1| auto]
        | fst (divmod ?n1) => apply small_div; assert_small_op n1
        | _ => auto
    end.
    
    Ltac assert_small := lazymatch goal with
        | |- @small _ ?n1 => assert_small_op n1
        | _ => auto
    end.

    Ltac reduce_eval_expr expr := lazymatch expr with
        | fst (divmod ?n1) => rewrite eval_div; [try apply (f_equal (fun y => y / r)); reduce_eval_expr n1|assert_small]
        | addT ?n1 ?n2 => rewrite eval_addT; [reduce_eval_expr n1; reduce_eval_expr n2| assert_small| assert_small]
        | scmul ?n1 ?n2 => rewrite eval_scmul; [reduce_eval_expr n2| assert_small |auto |auto]
        | snd (divmod ?n1) => rewrite eval_mod; [| |]
        | T_app ?n1 ?n2 => rewrite eval_T_app
        | _ => auto
    end.

    Ltac reduce_eval := lazymatch goal with
        | |- eval ?n1 = _ => reduce_eval_expr n1
        | |- snd (divmod ?n1) = _ => rewrite eval_mod; [try apply (f_equal (fun y => y mod r)); reduce_eval |assert_small]
        | _ => auto
    end.

    Ltac assert_sc_small := try (apply snd_divmod_sc_small); auto.

    Section mul_iteration_proofs.
        Context (pred_A_numlimbs : nat)
        (A : T (S pred_A_numlimbs))
        (S : T (S R_numlimbs))
        (small_A : small A)
        (small_S : small S).
        (* (S_nonneg : 0 <= eval S). *)

        Local Notation a := (@a pred_A_numlimbs A).
        Local Notation A' := (@A' pred_A_numlimbs A).
        Local Notation S2 := (@S2 pred_A_numlimbs B A S).
        Local Notation x1 := (@x1 pred_A_numlimbs B A S).
        Local Notation x' := (@x' pred_A_numlimbs B A S).

        Local Notation eval_S2 := ((eval S + a * eval B) / r).
        Local Notation eval_x1 := ((eval S + a * eval B) mod r).

        (* Local Coercion eval : T >-> Z. *)

        Lemma a_small: 0 <= a < r.
        Proof. unfold a; rewrite eval_mod; auto with zarith. Qed.

        Lemma eval_S2_eq : eval S2 = eval_S2.
        Proof. pose proof a_small; unfold S2, S2_x1, S1. reduce_eval. Qed.

        Lemma eval_x1_eq : x1 = eval_x1.
        Proof. pose proof a_small; unfold x1, S2_x1, S1; reduce_eval. Qed.

        Lemma S2_x1_invariant : x1 + r * eval S2 = eval S + a * eval B.
        Proof. rewrite eval_S2_eq, eval_x1_eq. rewrite Z_div_mod_eq with (b := r); auto with zarith. Qed.

    End mul_iteration_proofs.

    Section mul_proofs.
      Local Notation mul_body := (@mul_body B).
      Local Notation mul_loop := (@mul_loop B).
      Local Notation A'_x'_S2 := (@A'_x'_S2 _ _ B).
      Local Notation pre_mul A := (@pre_mul _ A B).

      Section mul_body_proofs.
        Context (pred_A_numlimbs : nat)
                (pred_x_numlimbs : nat)
                (A_x_S : T (S pred_A_numlimbs) * T pred_x_numlimbs * T (S R_numlimbs))
                (A_init : T R_numlimbs).
        Let A := fst (fst A_x_S).
        Let x := snd (fst A_x_S).
        Let Sp := snd (A_x_S).
        Let A_a := divmod A.
        Let A' := fst A_a.
        Let a := snd A_a.
        Context (small_A : small A)
                (small_S : small Sp)
                (small_x: small x)
                (Sp_len: length Sp = (S R_numlimbs))
                (B_len: length B = R_numlimbs)
                (A_len: length A = S (pred_A_numlimbs))
                (x_len: length x = pred_x_numlimbs)
                (A_init_len: length A_init = R_numlimbs)
                (s_len_small: Nat.le pred_x_numlimbs R_numlimbs)
                (A_correct: A = skipn pred_x_numlimbs A_init).
               (* (S_bound : 0 <= eval S < eval N * eval N).*)

        Lemma unfold_A_x_S : A_x_S = (A, x, Sp).
        Proof. destruct A_x_S, p. auto. Qed.

        Lemma unfold_A : A = a :: A'.
        Proof. subst a. simpl. subst A'. subst A_a. rewrite <- (undo_div _ _); auto. rewrite A_len. auto. Qed.  

        Lemma small_fst_fst_mul_body: small (fst (fst (mul_body A_x_S))).
        Proof. destruct A_x_S, p; simpl; assert_small. Qed.

        Lemma small_snd_fst_mul_body: small (snd (fst (mul_body A_x_S))).
        Proof. destruct A_x_S, p; simpl; do 2 (assert_small; assert_sc_small). Qed.

        Lemma small_snd_mul_body: small (snd (mul_body A_x_S)).
        Proof. destruct A_x_S, p; simpl; assert_small; assert_sc_small. Qed.

        Lemma length_A'_x'_S2: length (snd (fst (A'_x'_S2 A x Sp))) = S (length x).
        Proof. simpl; rewrite length_T_app; auto. Qed.

        Lemma length_mul_body_x': length (snd (fst (mul_body A_x_S))) = S (length (snd (fst A_x_S))).
        Proof.
          unfold mul_body. destruct A_x_S, p. simpl. rewrite length_T_app. auto.
        Qed.
        
        Lemma div_nil: forall n, @divmod n [] = ([], 0).
        Proof. reflexivity. Qed.

        Lemma div_app: forall n v a, @divmod n (a :: v) = (v, a).
        Proof. reflexivity. Qed.


        Lemma length_div: forall n v, length (fst (@divmod n v)) = Nat.pred (length v).
        Proof. destruct v; simpl; [rewrite (div_nil n)| rewrite (div_app n v z)]; auto. Qed.


        Lemma length_mul_body_S: length (snd (mul_body A_x_S)) = length (snd A_x_S).
        Proof.
          rewrite unfold_A_x_S. simpl. rewrite length_div. rewrite length_addT; auto.
          rewrite length_sc_mul; auto.
        Qed.

        Lemma mul_body_correct_snd_fst: eval(snd (fst (mul_body A_x_S))) = eval (snd (fst A_x_S)) + ((eval (snd A_x_S) + a * (eval B)) mod r) * r ^ (Z.of_nat pred_x_numlimbs).
        Proof.
          intros. rewrite unfold_A_x_S. simpl. pose proof eval_T_app x ((snd (divmod (addT Sp (scmul (snd (divmod A)) B))))) as H.
          simpl. rewrite <- x_len. rewrite H. rewrite eval_mod. rewrite eval_addT. rewrite eval_scmul.
          simpl. auto with zarith.
          all: assert_small; assert_sc_small.
        Qed.

        Lemma mul_body_correct_snd: eval (snd (mul_body A_x_S)) = (eval Sp + a * eval B) / r.
        Proof.
          rewrite unfold_A_x_S. simpl. reduce_eval; assert_sc_small. Qed.

        Lemma exp_succ: forall x n, x ^ (Z.of_nat (S n)) = x ^ (Z.of_nat n) * x.
        Proof. intros; rewrite Nat2Z.inj_succ; rewrite Z.pow_succ_r; auto with zarith. Qed.


        Lemma mul_body_correct: length x = pred_x_numlimbs -> eval x + r ^ (Z.of_nat ( pred_x_numlimbs)) * (a * eval B + eval Sp) = (@eval (S pred_x_numlimbs + S R_numlimbs) ((snd ( fst (mul_body A_x_S))) ++ (snd (mul_body A_x_S)))).
        Proof. intros. destruct (mul_body A_x_S) eqn:eq1, p. Local Close Scope Z_scope. assert (H0: S pred_x_numlimbs + S R_numlimbs = S R_numlimbs + S pred_x_numlimbs) by auto with zarith.
        rewrite H0. Local Open Scope Z_scope. unfold Positional.eval. rewrite <- H0.
        rewrite eval_app; simpl.
          - inversion eq1 as [H2]. apply (f_equal (fun y => (snd (fst y)))) in eq1. simpl in eq1.
            assert (H1: length t1 = S (pred_x_numlimbs)).
              {rewrite <- eq1. rewrite length_mul_body_x'. auto. }
            rewrite H1. rewrite <- eq1. rewrite mul_body_correct_snd_fst; auto.
            apply (f_equal (fun y => snd y)) in H2. simpl in H2. rewrite <- H2. rewrite mul_body_correct_snd.
            rewrite exp_succ. 
            rewrite (Z.mul_comm (r ^ Z.of_nat pred_x_numlimbs)).  
            rewrite <- (Z.mul_assoc _ r).  rewrite Z.mul_div_eq; [| lia]. rewrite unfold_A_x_S; simpl; auto with zarith.
          - apply (f_equal (fun y => snd (fst y))) in eq1. simpl in eq1. rewrite <- eq1. rewrite length_mul_body_x'. auto.
          - apply (f_equal (fun y => snd y)) in eq1. simpl in eq1. rewrite <- eq1.
            rewrite length_mul_body_S. rewrite unfold_A_x_S. simpl. auto.
        Qed.
        
        Lemma firstn_a: firstn (S pred_x_numlimbs) A = [a] ++ firstn pred_x_numlimbs A'.
        Proof. rewrite unfold_A. auto. Qed.

        Lemma eval_firstn: forall n, @eval (length (firstn ( S n) A)) (firstn (S n) A) = a + r * @eval (length (firstn n A')) (firstn n A').
        Proof. clear x_len.
          intros n. rewrite unfold_A; simpl. assert (H: forall l, a :: l = [a] ++ l) by auto. rewrite H.
          rewrite (eval_app 1 _). simpl. assert (@eval 1 [a] = a). unfold eval, Positional.eval, Positional.to_associational, Associational.eval. simpl. rewrite weight_0; [auto with zarith| apply wprops].
          rewrite H0. all: auto with zarith.
        Qed.

        Lemma eval_sc: forall sc, @eval 1 [sc] = sc.
        Proof. clear x_len.
          intros sc. unfold eval, Positional.eval, Associational.eval, Positional.to_associational.
          simpl. rewrite weight_0; [auto with zarith | apply wprops].
        Qed. 

        Lemma eval_nil: @eval 0 [] = 0.
        Proof. auto. Qed.

        Lemma skip_pad: forall n (l : list Z), skipn n (Positional.zeros n ++ l) = l.
        Proof. intros n l. induction n; auto. Qed.

        Local Close Scope Z_scope.
        Lemma skipn_skipn: forall n1 n2 (l : list Z), skipn n1 (skipn n2 l) = skipn (n1 + n2) l.
        Proof.
            intros n1 n2. induction n2.
              - simpl; assert (H: n1 + 0 = n1) by auto with zarith; rewrite H; auto.
              - intros l; rewrite NPeano.Nat.add_succ_r; destruct l.
                + repeat rewrite skipn_nil; auto.
                + simpl; auto.
        Qed.

        Lemma firstn_sum: forall n1 n2 (l : list Z), firstn (n1 + n2) l = firstn n1 l ++ firstn n2 (skipn n1 l).
        Proof.
          induction n1.
            - auto.
            - destruct l eqn:eq1.
              + rewrite skipn_nil. repeat rewrite firstn_nil. auto.
              + simpl. apply (f_equal (fun y => z :: y)). auto.
        Qed.

        Lemma A'_correct: skipn (S pred_x_numlimbs) A_init = A'.
        Proof.
          apply (f_equal (fun (y : list Z) => skipn 1 y)) in A_correct. rewrite unfold_A in A_correct. rewrite skipn_skipn in A_correct.
          simpl in A_correct. rewrite A_correct. auto.
        Qed.

        Lemma firstn_S: forall n (l : list Z) sc l', length l = n -> firstn (S n) (l ++ [sc] ++ l') = l ++ [sc].
        Proof.
          intros n l sc l' H. assert (H0: S n = length (l ++ [sc])) by (rewrite app_length; simpl; auto with zarith).
          rewrite H0. assert (length (l ++ [sc]) = length (l ++ [sc]) + 0) by auto. rewrite H1. rewrite app_assoc.
          rewrite firstn_app_2. simpl. rewrite app_nil_r. auto.
        Qed.

        Lemma length_firstn_A_init: length (firstn pred_x_numlimbs A_init) = pred_x_numlimbs.
        Proof. rewrite firstn_length_le; lia. Qed.

        Lemma a_A'_correct: firstn (S pred_x_numlimbs) A_init = firstn (pred_x_numlimbs) A_init ++ [a].
        Proof.
          pose proof (firstn_skipn pred_x_numlimbs A_init) as H. rewrite <- A_correct in H. rewrite unfold_A in H.
          apply (f_equal (fun y => firstn (S pred_x_numlimbs) y)) in H. rewrite <- H.
          assert (H0: forall l (sc : Z) l', l ++ sc :: l' = l ++ [sc] ++ l') by auto.
          rewrite H0; rewrite firstn_S; auto; apply firstn_length_le; lia.
        Qed.
        Local Open Scope Z_scope.

        Lemma mul_body_inv: @eval (pred_x_numlimbs + S (R_numlimbs)) (x ++ Sp) = @eval (length (firstn pred_x_numlimbs A_init)) (firstn pred_x_numlimbs A_init) * eval B ->
            @eval (S pred_x_numlimbs + S (R_numlimbs)) (snd (fst (mul_body A_x_S)) ++ snd (mul_body A_x_S)) = @eval (length (firstn (S pred_x_numlimbs) A_init)) (firstn (S pred_x_numlimbs) A_init) * eval B.
          Proof.
            intros H. rewrite a_A'_correct. rewrite <- mul_body_correct; auto. rewrite app_length. rewrite eval_app; auto.
            simpl. rewrite length_firstn_A_init. rewrite eval_sc. rewrite Z.mul_add_distr_r. rewrite length_firstn_A_init in H. rewrite <- H.
            rewrite eval_app; ( try rewrite x_len; auto with zarith).
        Qed. 
      End mul_body_proofs.

      Lemma body_notation : forall n1 n2 (A : T (S n1)) (x : T n2) Sp, (A'_x'_S2 A x Sp) = @mul_body (S n1) n2 (A, x, Sp).
      Proof. reflexivity. Qed.
      Definition eval_loop n1 n2 (A_x_S' : ( (T (n1)) * T n2 * T (S R_numlimbs))) := @eval (n2 + S R_numlimbs ) ((snd (fst A_x_S')) ++ (snd A_x_S')).

      Lemma nth_0_divmod: forall n v, nth 0 v 0 = snd (@divmod n v).
      Proof. destruct v; auto. Qed.

      Lemma T_app_nil: forall n sc, (@T_app n [] sc) = [sc].
      Proof. reflexivity. Qed.

      Lemma eval_sc': forall sc, @eval 1 [sc] = sc.
      Proof. intros. unfold eval, Positional.eval, Associational.eval, Positional.to_associational. simpl. rewrite weight_0. auto with zarith. apply wprops. Qed. 

      Lemma mul_body_snd_fst_length: forall init n1 n2 (x : T( S n1) * T n2 * T (S R_numlimbs)), length (snd (fst x)) = init -> length (snd (fst (@mul_body n1 n2 x))) = S init.
      Proof.
        intros init n1 n2 x H. destruct x, p. simpl. simpl in H. rewrite length_T_app. auto.
      Qed.

      Lemma mul_loop_first_it: forall x, mul_loop 0 1 x = mul_body x.
      Proof. reflexivity. Qed.

      Lemma mul_loop_next_inner: forall n n' x, mul_loop n' (S n) x = mul_loop (S n') n (mul_body x).
      Proof. auto. Qed.

        Lemma mul_loop_body_comm: forall n n' x, mul_body (mul_loop n' n x) = mul_loop (S n') n (mul_body x).
       Proof.
        intros n n' x. generalize dependent n'. induction n.
          - auto.
          - intros. pose proof (mul_loop_next_inner n) as H. rewrite (H n'). remember (mul_body x) as x'.
            remember (IHn (S n') x'). repeat rewrite <- Nat.add_succ_comm.
            rewrite e. rewrite (H (S n') ). auto.
       Qed.
        Lemma mul_loop_next: forall n x, mul_body (mul_loop 0 n x) = mul_loop 0 (S n) x.
       Proof. intros n x.
       
        induction n as [|n' IHn'].
          - reflexivity.
          - simpl. pose proof (mul_loop_next_inner (S n') 0 x) as H.  pose proof (mul_loop_body_comm (S n') 0 x). repeat rewrite <- Nat.add_succ_comm.
            repeat rewrite <- Nat.add_succ_comm in H. rewrite H. auto.
       Qed.

       Local Close Scope Z_scope.
       Lemma mul_loop_snd_fst_length: forall n init (x : T (R_numlimbs - init) * (T init) * T(S R_numlimbs)), length (snd (fst x)) = init -> length (snd( fst (mul_loop init n x))) = init + n.
       Proof. Local Open Scope Z_scope.
         induction n.
          - intros init x. unfold mul_loop. simpl. rewrite Nat.add_0_r. auto with zarith.
          - intros init x H. repeat rewrite <- Nat.add_succ_comm. pose proof (mul_loop_next_inner n init x) as H0. repeat rewrite <- Nat.add_succ_comm in H0. rewrite H0.
            rewrite IHn. auto. apply mul_body_snd_fst_length. auto.
       Qed.


       Lemma nth_fst_fst_mul_body: forall n1 n2 n x, nth n (fst (fst (@mul_body n1 n2 x))) 0 = nth (S n) (fst (fst x)) 0.
       Proof.
         intros n1 n2 n x. destruct x, p. simpl. destruct t0 eqn:eq1.
          - rewrite (fst_divmod_nil n1); auto with zarith. repeat rewrite nth_overflow; simpl; auto with zarith.
          - simpl. rewrite (fst_divmod_app n1). auto.
       Qed.
    
       
       Lemma divmod_fst_fst_mul_loop: forall n1 n2 n x, (snd (@divmod n1 (fst (fst( mul_loop n2 n x))))) = nth n (fst (fst x)) 0.
       Proof. intros n1 n2 n. generalize dependent n2.
         induction n.
          - intros. rewrite nth_0_divmod with (n := n1). auto.
          - intros n2 x. repeat rewrite Nat.add_succ_comm. pose proof (mul_loop_next_inner n n2 x) as H. rewrite H.
            pose proof (IHn (S n2) (mul_body x)) as H0.
            repeat rewrite Nat.add_succ_comm. repeat rewrite Nat.add_succ_comm in H0.
            rewrite H0. rewrite nth_fst_fst_mul_body. auto.
       Qed.
 

       Lemma nat_sub: forall x y, (S x <= y)%nat -> S (y - S x) = (y - x)%nat.
       Proof.
          intros. rewrite <- Nat.sub_succ_l. rewrite NPeano.Nat.sub_succ; auto. auto. Qed.

        Lemma nat_sub_0: forall y : nat, (y - 0)%nat = y.
        Proof. auto with zarith. Qed.

        Lemma nat_0_add_r: forall y, (0 + y)%nat = y.
        Proof. auto. Qed.

        Lemma length_mul_body_snd: forall n1 n2 x, length (snd x) = S R_numlimbs -> length (snd (@mul_body n1 n2 x)) = S R_numlimbs.
        Proof.
          intros n1 n2 x H. destruct x, p. simpl.
          rewrite length_div. rewrite length_addT. all: auto.
          rewrite length_sc_mul; auto.
        Qed.

        Lemma length_mul_loop_snd: forall x count, length (snd x) = S R_numlimbs -> length (snd (mul_loop 0 count x)) = S R_numlimbs.
        Proof.
          intros x count H. generalize dependent x. induction count.
          - intros. unfold mul_loop. simpl. auto.
          - intros. rewrite <- mul_loop_next.
            rewrite (length_mul_body_snd _ _ (mul_loop 0 count x)); auto.
        Qed.


        Lemma length_fst_fst_mul_body: forall x n n1 n2, length (fst (fst x)) = n -> length (fst (fst (@mul_body n1 n2 x))) = (n - 1)%nat.
        Proof.
          intros x n n1 n2 H. destruct x, p. simpl. rewrite length_div.
          rewrite pred_of_minus. simpl in H. auto.
        Qed. 
          
        Lemma length_fst_fst_mul_loop_inv: forall count x, length (fst (fst x)) = R_numlimbs
        -> length (fst (fst (mul_loop 0 count x))) = (R_numlimbs - count)%nat
        -> length (fst (fst (mul_loop 0 (S count) x))) = (R_numlimbs - (S count))%nat.
        Proof.
          intros count x H H0. rewrite <- mul_loop_next. rewrite (length_fst_fst_mul_body (mul_loop 0 count x) (R_numlimbs - count) _ _).
          auto with zarith. auto.
        Qed.

         Lemma length_fst_fst_mul_loop: forall count x, length (fst (fst x)) = R_numlimbs 
          -> length (fst (fst (mul_loop 0 count x))) = (R_numlimbs - count)%nat.
        Proof.
          induction count.
            - intros x H. unfold mul_loop. simpl. assert (H0: forall y : nat, (y - 0)%nat = y) by auto with zarith.
              rewrite H0; auto.
            - intros. rewrite length_fst_fst_mul_loop_inv; auto.
        Qed. 

        Lemma length_snd_fst_mul_body: forall n1 n2 x, length (snd (fst (@mul_body n1 n2 x))) = S (length (snd (fst x))).
        Proof.
          intros n1 n2 x; destruct x, p; simpl; rewrite length_T_app; auto.
        Qed.

        Lemma length_snd_fst_mul_loop: forall count x, (snd (fst x)) = ([] : T 0) -> length (snd (fst ( mul_loop 0 count x))) = (count)%nat.
        Proof.
          induction count.
          - intros x H. unfold mul_loop. simpl. rewrite H. auto.
          - intros x H. rewrite <- mul_loop_next. rewrite (length_snd_fst_mul_body _ _ (mul_loop 0 count x)).
            auto.
        Qed.

        Lemma fst_fst_mul_body_skipn: forall n1 n2 x, (fst (fst (@mul_body n1 n2 x))) = (skipn 1 (fst (fst x))).
        Proof.
          intros n1 n2 x; destruct x, p; simpl; reflexivity.
        Qed.

        Lemma fst_fst_mul_loop_skipn: forall count x, fst (fst (mul_loop 0 count x)) = skipn count (fst (fst x)).
        Proof.
          induction count.
            - intros; unfold mul_loop; simpl; auto.
            - intros. rewrite <- mul_loop_next. rewrite (fst_fst_mul_body_skipn _ _).
              rewrite IHcount. rewrite skipn_skipn. auto.
        Qed.

        Lemma small_mul_loop: forall count x, (S count <= R_numlimbs)%nat
          -> small (fst (fst x))
          -> (snd (fst x)) = []
          -> length (snd x) = (S R_numlimbs)
          -> length (fst (fst x)) = R_numlimbs
          -> small (snd (fst (mul_loop 0 count x)))
          -> small (fst (fst (mul_loop 0 count x)))
          -> small (snd (mul_loop 0 count x))
          -> small (fst (fst (mul_loop 0 (S count) x))) /\
              small (snd (fst (mul_loop 0 (S count) x))) /\
              small (snd (mul_loop 0 (S count) x)).
       Proof.
         intros count x H H0 H1 H2 H3 H4 H5 H6. repeat split.
          - rewrite <- mul_loop_next. pose proof (small_fst_fst_mul_body (R_numlimbs - (S count)) count (mul_loop 0 count x) (fst (fst x))) as H7.
            apply H7; auto.
            + repeat rewrite nat_sub. apply H5. auto.
            + pose proof (length_mul_loop_snd x count) as H8. apply H8. auto.
            + pose proof (length_fst_fst_mul_loop count x). repeat rewrite nat_0_add_r in H6.
              repeat rewrite nat_sub; auto.
            + pose proof (length_snd_fst_mul_loop count x) as H8.
              repeat rewrite nat_sub. repeat rewrite nat_0_add_r in H8. rewrite H8; auto. auto.
            + pose proof (fst_fst_mul_loop_skipn count x) as H8. repeat rewrite nat_0_add_r in H8. repeat rewrite nat_sub; auto.
          - rewrite <- mul_loop_next. pose proof (small_snd_fst_mul_body (R_numlimbs - (S count)) count (mul_loop 0 count x) (fst (fst x))) as H7.
            apply H7. repeat rewrite nat_0_add_r in H5. repeat rewrite nat_sub; auto. auto.
            repeat rewrite nat_0_r in H4. repeat rewrite nat_sub; auto.
            pose proof (length_mul_loop_snd x count) as H8. apply H8. auto.
            repeat rewrite nat_sub; auto.
            pose proof (length_fst_fst_mul_loop count x) as H8. repeat rewrite nat_0_add_r in H8. auto.
            pose proof (length_snd_fst_mul_loop count x) as H8. repeat rewrite nat_sub; auto.
            apply (fst_fst_mul_loop_skipn count x).
          - rewrite <- mul_loop_next. apply small_snd_mul_body with (A_init := fst(fst x)); auto.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_0_add_r in H5.
              repeat rewrite nat_sub; auto.
            + pose proof (length_mul_loop_snd x count) as H7. apply H7. auto.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop. auto.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply length_snd_fst_mul_loop. auto.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply fst_fst_mul_loop_skipn.
       Qed.

       Lemma small_fst_fst_mul_loop: forall count x, (S count <= R_numlimbs)%nat
       -> small (fst (fst x))
       -> (snd (fst x)) = []
       -> length (snd x) = (S R_numlimbs)
       -> length (fst (fst x)) = R_numlimbs
       -> small (snd (fst (mul_loop 0 count x)))
       -> small (fst (fst (mul_loop 0 count x)))
       -> small (snd (mul_loop 0 count x))
       -> small (fst (fst (mul_loop 0 (S count) x))).
       Proof. apply small_mul_loop. Qed.

        Lemma small_snd_fst_mul_loop: forall count x, (S count <= R_numlimbs)%nat
          -> small (fst (fst x))
          -> (snd (fst x)) = []
          -> length (snd x) = (S R_numlimbs)
          -> length (fst (fst x)) = R_numlimbs
          -> small (snd (fst (mul_loop 0 count x)))
          -> small (fst (fst (mul_loop 0 count x)))
          -> small (snd (mul_loop 0 count x))
          -> small (snd (fst (mul_loop 0 (S count) x))).
        Proof. apply small_mul_loop. Qed.
            

        Lemma small_snd_mul_loop: forall count x, (S count <= R_numlimbs)%nat
          -> small (fst (fst x))
          -> (snd (fst x)) = []
          -> length (snd x) = (S R_numlimbs)
          -> length (fst (fst x)) = R_numlimbs
          -> small (snd (fst (mul_loop 0 count x)))
          -> small (fst (fst (mul_loop 0 count x)))
          -> small (snd (mul_loop 0 count x))
          -> small (snd (mul_loop 0 (S count) x)).
        Proof. apply small_mul_loop. Qed.

        Lemma small_mul_loop': forall count A, small A -> (count <= R_numlimbs)%nat
        -> small (fst (fst (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))))) /\
           small (snd (fst (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))))) /\
           small (snd (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs)))).
        Proof. induction count.
            - intros. unfold mul_loop. simpl. repeat split; auto.
            - intros A H H0. repeat split.
              + rewrite <- mul_loop_next. apply small_fst_fst_mul_body with (A_init := A).
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply (IHcount A); auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply (IHcount A); auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply (IHcount A); auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. pose proof (length_mul_loop_snd (A, [], Positional.zeros (S R_numlimbs))). apply H1.
                  simpl. rewrite repeat_length. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop.
                  simpl. auto. rewrite length_small. rewrite nat_sub_0. auto. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
                  apply length_snd_fst_mul_loop. simpl. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply fst_fst_mul_loop_skipn.
              + rewrite <- mul_loop_next. apply small_snd_fst_mul_body with (A_init := A).
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. pose proof (length_mul_loop_snd (A, [], Positional.zeros (S R_numlimbs))). apply H1.
                  simpl. rewrite repeat_length. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop.
                  simpl. auto. rewrite length_small. rewrite nat_sub_0. auto. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
                  apply length_snd_fst_mul_loop. simpl. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply fst_fst_mul_loop_skipn.
              + rewrite <- mul_loop_next. apply small_snd_mul_body with (A_init := A).
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. pose proof (length_mul_loop_snd (A, [], Positional.zeros (S R_numlimbs))). apply H1.
                simpl. rewrite repeat_length. auto.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop.
                simpl. auto. rewrite length_small. rewrite nat_sub_0. auto. auto.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
                apply length_snd_fst_mul_loop. simpl. auto.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply fst_fst_mul_loop_skipn.
        Qed.

        Lemma small_fst_fst_mul_loop': forall count A, small A -> (count <= R_numlimbs)%nat
        -> small (fst (fst (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))))).
        Proof. apply small_mul_loop'. Qed.

        Lemma small_snd_fst_mul_loop': forall count A, small A -> (count <= R_numlimbs)%nat
        -> small (snd (fst (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))))).
        Proof. apply small_mul_loop'. Qed.

        Lemma small_snd_mul_loop': forall count A, small A -> (count <= R_numlimbs)%nat
        -> small (snd (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs)))).
        Proof. apply small_mul_loop'. Qed.


      Lemma mul_loop_inv (A: T (R_numlimbs)): forall count,
      small A ->
      (S (S count) <= R_numlimbs)%nat 
      -> eval_loop (R_numlimbs - count) count (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))) + r ^ (Z.of_nat count) *  (nth count A 0) * eval B = eval_loop (R_numlimbs - (S count)) (S count) (mul_loop O (S count) (A, [], Positional.zeros (S R_numlimbs)))
      -> eval_loop (R_numlimbs - (S count)) (S count) (mul_loop 0 (S count) (A, [], Positional.zeros (S R_numlimbs))) + r ^ (Z.of_nat (S count)) *  (nth (S count) A 0) * eval B = eval_loop (R_numlimbs - (S (S count))) (S (S count)) (mul_loop O (S (S count)) (A, [], Positional.zeros (S R_numlimbs))).
      Proof. intros c' H Hcount H'. assert (A_len: length A = R_numlimbs) by (rewrite length_small; auto). 
      - unfold eval_loop. rewrite <- (mul_loop_next (S c')).
        remember (A, [], Positional.zeros (S R_numlimbs)) as x.
        unfold eval_loop in H'. 
        repeat rewrite eval_app. rewrite eval_app in H'. rewrite eval_app in H'.
        rewrite mul_body_correct_snd with (A_init := A).
        rewrite mul_body_correct_snd_fst with (A_init := A).
        rewrite mul_body_snd_fst_length with (init := (S c')).
        assert (H0: forall y, r ^ Z.of_nat (S y) = r * r ^ Z.of_nat y).
        Local Close Scope Z_scope.
        assert (S (S c') = 1 + S c') as H'' by auto with zarith. intros. Local Open Scope Z_scope. assert (Z.of_nat(S y) = 1 + Z.of_nat y). auto with zarith. rewrite H0. rewrite Zpower_exp. auto with zarith. lia. lia. 
        rewrite H0. rewrite H0. 
        rewrite <- Z.mul_assoc. rewrite <- Z.mul_assoc. rewrite <- Z.mul_assoc. rewrite (Z.mul_comm (r ^ Z.of_nat (S c'))).
        rewrite Z.mul_assoc. assert (H1: Z.of_nat (0 + S c') = Z.of_nat (S c')) by auto with zarith.
        rewrite H1. repeat rewrite <- Z.add_assoc. rewrite Z.mul_assoc. rewrite Z.mul_assoc. rewrite <- (Z.mul_add_distr_r _ _ (r ^ Z.of_nat (S c'))).
        rewrite <- Z.div_mod'' with (b := r). rewrite (mul_loop_snd_fst_length (S c') 0) in H'.
        rewrite H1 in H'. rewrite Z.mul_add_distr_r. rewrite (Z.mul_comm _ (r ^ Z.of_nat (S c'))).
        rewrite Z.add_assoc. rewrite Z.add_assoc. simpl in Heqx.
        assert (H2: forall y, Init.Nat.add O y = y) by auto with zarith. repeat rewrite H2.
        Local Close Scope Z_scope. assert (H3: forall y, ((S y) <= R_numlimbs) -> S (Init.Nat.sub R_numlimbs (S y)) = Init.Nat.sub R_numlimbs y).
        intros. rewrite <- NPeano.Nat.sub_succ_l. 
         rewrite Nat.sub_succ. auto. auto.
         rewrite H3. rewrite <- H'.
         rewrite <- mul_loop_next. rewrite mul_body_correct_snd_fst with (A_init := A).
         rewrite mul_body_correct_snd with (A_init := A). rewrite H2.
         rewrite mul_body_snd_fst_length with (init := c'). rewrite H0.
         rewrite (mul_loop_snd_fst_length c' 0). repeat rewrite H2. rewrite <- Z.mul_assoc.
         rewrite (Z.mul_comm (r ^ (_)) _). rewrite Z.mul_assoc. repeat rewrite H3.
         Local Open Scope Z_scope.
         assert (forall y1 y2 y3 y4, y1 + y2 + y3 + y4 = y1 + (y2 + y3) + y4) as H4 by auto with zarith.
         rewrite H4. 
         rewrite <- (Z.mul_add_distr_r _ _ (Z.pow r (Z.of_nat c'))).
         rewrite <- Z.div_mod''. simpl.
         repeat rewrite <- Z.add_assoc.
         apply (f_equal (fun y => eval (snd (fst (mul_loop 0 c' x))) + y)).
         rewrite Z.mul_add_distr_r. rewrite Z.mul_comm.
         repeat rewrite <- Z.add_assoc.
         apply (f_equal (fun y => r ^ Z.of_nat c' * eval (snd (mul_loop 0 c' x)) + y)).
         simpl. pose proof divmod_fst_fst_mul_loop.
         rewrite (H5 _ O c').
         rewrite (mul_loop_next c'). rewrite (H5 _ O (S c')).
         simpl. auto with zarith. rewrite Heqx. simpl. auto with zarith.
         all: auto with zarith; try lia; try (rewrite Heqx; auto; assert_small).
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto; try lia.
            apply length_snd_fst_mul_loop. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto; try lia.
            apply small_fst_fst_mul_loop'; auto; try lia. rewrite nat_sub_0. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_snd_mul_loop'.
              * rewrite nat_sub_0. auto.
              * lia.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_snd_fst_mul_loop'.  
              * rewrite nat_sub_0. auto.
              * lia.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. 
            apply (length_mul_loop_snd (A, [], Positional.zeros (S R_numlimbs)) c').
            simpl. rewrite repeat_length. auto.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (length_fst_fst_mul_loop). simpl. auto.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (length_snd_fst_mul_loop). simpl. auto.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply fst_fst_mul_loop_skipn.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (small_fst_fst_mul_loop'). rewrite nat_sub_0. auto.
              * lia.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (small_snd_mul_loop'). rewrite nat_sub_0. auto.
              * lia.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (small_snd_fst_mul_loop'). rewrite nat_sub_0. auto.
            * lia. 
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (length_mul_loop_snd). simpl. rewrite repeat_length; auto.
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_fst_fst_mul_loop. simpl. auto.
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_snd_fst_mul_loop. simpl. auto.
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply fst_fst_mul_loop_skipn.
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (length_snd_fst_mul_loop). auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_fst_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_snd_mul_loop.
              * lia.
              * simpl. rewrite nat_sub_0. auto.
              * auto.
              * simpl. rewrite repeat_length. auto.
              * auto.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
                apply small_snd_fst_mul_loop'. rewrite nat_sub_0. auto.
                lia.
              * apply small_fst_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
              * apply small_snd_mul_loop'. rewrite nat_sub_0. auto. lia.
          + apply small_snd_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_mul_loop_snd. simpl. rewrite repeat_length; auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_fst_fst_mul_loop. simpl. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_snd_fst_mul_loop. simpl. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply fst_fst_mul_loop_skipn.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_fst_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_snd_mul_loop'. rewrite nat_sub_0. auto. lia.
          + apply small_snd_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_mul_loop_snd.
            simpl. rewrite repeat_length; auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop.
            simpl. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_snd_fst_mul_loop. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply fst_fst_mul_loop_skipn.
          + apply length_snd_fst_mul_loop. auto.
          + apply length_mul_loop_snd. simpl. rewrite repeat_length. auto.
          + apply length_snd_fst_mul_loop. auto.
          + apply length_mul_loop_snd. simpl. rewrite repeat_length. auto.
          + rewrite length_snd_fst_mul_body. apply (f_equal (fun y => S y)).
            repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_snd_fst_mul_loop. auto.
          + rewrite length_mul_body_snd; auto.
          repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_mul_loop_snd.
          simpl. rewrite repeat_length. auto.
          + apply length_snd_fst_mul_loop. auto.
          + apply length_mul_loop_snd. simpl. rewrite repeat_length; auto.
      Qed.
        

      Lemma mul_loop_eval (A: T (R_numlimbs)): forall count,
      small A ->
      (S count <= R_numlimbs)%nat
      -> eval_loop (R_numlimbs - count) count (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))) + r ^ (Z.of_nat count) *  (nth count A 0) * eval B = eval_loop (R_numlimbs - (S count)) (S count) (mul_loop O (S count) (A, [], Positional.zeros (S R_numlimbs))).
      Proof.
        intros count H H0. assert (Alen: length A = R_numlimbs) by (apply length_small; auto). induction count.
        - pose proof (mul_body_correct (R_numlimbs - 1) 0 (A, [], (Positional.zeros (S R_numlimbs))) A) as H1. unfold mul_body in H1. unfold eval_loop. simpl in H1.
          assert (Init.Nat.sub R_numlimbs O = R_numlimbs) as H2 by auto with zarith. simpl. rewrite <- H1; try auto. rewrite eval_zero. simpl.
          rewrite (@nth_0_divmod (Init.Nat.sub R_numlimbs (S O)) A). rewrite Z.add_0_r. destruct (snd (divmod A)) eqn:eq1; auto with zarith.
          destruct (p * eval B); auto. destruct (Z.neg p * eval B); auto.
          + rewrite nat_sub; auto. rewrite nat_sub_0. auto.
          + reflexivity.
          + rewrite repeat_length; auto.
          + auto with zarith.
          + auto with zarith.
        - apply mul_loop_inv; auto. apply IHcount. lia.
      Qed.


      Definition first_n n : T R_numlimbs -> T n
      := fun (A : T R_numlimbs) => (firstn n A).

      Lemma first_n_length: forall n A, (n <= length A)%nat -> length (first_n n A) = n.
      Proof.
        intros. rewrite firstn_length. lia.
      Qed.

      Lemma first_n_S: forall n n1 (A : T (n1)), (n < length A)%nat -> first_n (S n) A = (first_n n A) ++ [nth n A 0].
      Proof.
        intros n n1 A H. rewrite firstn_succ with (d := 0); auto. rewrite nth_default_eq. auto.
      Qed.

      Lemma eval_first_n_S : forall n n1 (A : T n1), (n < length A)%nat -> eval (first_n (S n) A) = eval (first_n n A) + r ^ Z.of_nat n * (nth n A 0).
      Proof.
        intros n n1 A H.
        assert (H0: (first_n (S n) A) = (first_n n A) ++ [nth n A 0]) by (apply first_n_S; auto).
        rewrite H0. pose proof (eval_app n 1 (first_n n A) [nth n A 0]) as H1. simpl in H1.
        rewrite Nat.add_1_r in H1. rewrite H1. rewrite eval_sc'.
        rewrite first_n_length. all: (auto; try lia). apply first_n_length. lia.
      Qed.

      
      Lemma mul_loop_eval_first (A: T(R_numlimbs)) n: small A -> (n <= R_numlimbs)%nat -> eval_loop (R_numlimbs - n) n (mul_loop 0 n (A, [], Positional.zeros (S R_numlimbs)))
        = (eval (first_n n A) * eval B).
      Proof. intros. induction n.
        - unfold mul_loop, eval_loop, eval. simpl. rewrite Positional.eval_zeros. auto.
        - rewrite <- mul_loop_eval. rewrite IHn. rewrite eval_first_n_S. auto with zarith.
          all: (auto with zarith; try lia). rewrite length_small; auto.
      Qed. 

      Lemma mul_loop_eval_full (A: T (R_numlimbs)): small A ->
      eval_loop 0 R_numlimbs (mul_loop 0 R_numlimbs (A, [], Positional.zeros (S R_numlimbs)))
        = eval (A) * eval B.
        Proof. intros H.
            pose proof (mul_loop_eval_first A R_numlimbs) as H0. rewrite NPeano.Nat.sub_diag in H0. rewrite H0; auto.
            auto. pose proof length_small H as H1. rewrite <- H1. unfold first_n. rewrite List.firstn_all. auto.
        Qed.

      Local Close Scope Z_scope.
      Lemma mul_loop_good count A_x_S 
          (Hsmall: small (snd(fst A_x_S)) /\ small (fst (fst A_x_S)) /\ small (snd A_x_S)) : count <= R_numlimbs ->
          small (snd (fst (mul_loop 0 count A_x_S))) /\ small (fst (fst (mul_loop 0 count A_x_S))) /\ small (snd (mul_loop 0 count A_x_S)).
        Proof. induction count as [|count' IHcount'].
          - auto.
          - intros. rewrite <- mul_loop_next.  destruct Hsmall, H0.
            repeat split. assert (count' <= R_numlimbs) as H0 by lia. apply IHcount' in H0. destruct H0. destruct H2.
            + repeat rewrite Nat.add_0_l.
              
            apply small_snd_fst_mul_body with (A_init := fst (fst A_x_S)); auto.
              * repeat rewrite Nat.add_0_l in H2.
                assert (S (R_numlimbs - S count') = R_numlimbs - count') as H4 by auto with zarith. repeat rewrite H4. apply H2.
              * apply length_small. auto.
              * apply length_small. repeat rewrite Nat.add_0_l in H2.
              assert (S (R_numlimbs - S count') = R_numlimbs - count') as H4 by auto with zarith. repeat rewrite H4. apply H2.
              * apply length_small. auto.
              * auto. pose proof (fst_fst_mul_loop_skipn count' A_x_S) as H4. apply H4.
            + assert (count' <= R_numlimbs) as H0 by lia. apply IHcount' in H0. destruct H0. destruct H2.
              apply small_fst_fst_mul_body with (A_init := fst (fst A_x_S)); auto.
              * repeat rewrite Nat.add_0_l in H2. repeat rewrite Nat.add_0_l.
                assert (S (R_numlimbs - S count') = R_numlimbs - count') as H4 by auto with zarith. repeat rewrite H4. apply H2.
              * apply length_small. auto.
              * apply length_small. repeat rewrite Nat.add_0_l in H2. repeat rewrite Nat.add_0_l.
              assert (S (R_numlimbs - S count') = R_numlimbs - count') as H4 by auto with zarith. repeat rewrite H4. apply H2.
              * apply length_small. auto.
              * pose proof (fst_fst_mul_loop_skipn count' A_x_S) as H4. apply H4.
            + assert (count' <= R_numlimbs) as H0 by lia. apply IHcount' in H0. destruct H0. destruct H2.
              apply small_snd_mul_body with (A_init := fst (fst A_x_S)); auto.
              * repeat rewrite Nat.add_0_l in H2. repeat rewrite Nat.add_0_l.
                assert (H4: S (R_numlimbs - S count') = R_numlimbs - count') by auto with zarith. repeat rewrite H4. apply H2.
              * apply length_small. auto.
              * apply length_small. repeat rewrite Nat.add_0_l in H2. repeat rewrite Nat.add_0_l.
              assert (H4: S (R_numlimbs - S count') = R_numlimbs - count') by auto with zarith. repeat rewrite H4. apply H2.
              * apply length_small. auto.
              * pose proof (fst_fst_mul_loop_skipn count' A_x_S) as H4. apply H4.
        Qed.

    End mul_proofs.
  End with_args.
End WordByWordMontgomery.
