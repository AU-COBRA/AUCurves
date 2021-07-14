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
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.
(*Implementation of the reduction part of the Separated Operand Scanning method of Montgomery multiplication
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
        Let SOS_red_add {n n'} (p : T n) ( q : T n') :  T (n)
            := let '(v,c) := (Rows.add weight n p (Positional.extend_to_length n' n q)) in
            v.
        Let drop_high_addT' {n} (p : T (S n)) (q : T n) : T (S n) (* drops carry *)
          := fst (Rows.add weight (S n) p (Positional.extend_to_length n (S n) q)).
        Let conditional_sub {n} (arg : T (S n)) (N : T n) : T n  (* computes [arg - N] if [N <= arg], and drops high bit *)
          := Positional.drop_high_to_length n (Rows.conditional_sub weight (S n) arg (Positional.extend_to_length n (S n) N)).
        Context (R_numlimbs : nat)
                (N : T R_numlimbs). (* encoding of m *)
        Let sub_then_maybe_add (a b : T R_numlimbs) : T R_numlimbs (* computes [a - b + if (a - b) <? 0 then N else 0] *)
          := fst (Rows.sub_then_maybe_add weight R_numlimbs (r-1) a b N).
          Let T_app {n} (p : T n) (e : Z) : T (S n)
          := p ++ [e].
        Local Opaque T.
    (*... *)

    Section red_iteration.
      Context (pred_A_numlimbs : nat)
              (num_it : nat)
              (A : T (S pred_A_numlimbs))
              (k : Z).
    
      Local Definition A_s := dlet p := @divmod _ A in p. Local Definition A' := fst A_s. Local Definition s := snd A_s.
      Local Definition thism := fst (Z.mul_split r s k).
      Local Definition q := (@scmul _ thism N).
      Local Definition S1 := @SOS_red_add _ _ A q.
      Local Definition S2 := fst (@divmod _ S1).


      Local Definition red_steps
      :=  dlet A_s := @divmod _ A in
          dlet A' := fst A_s in
          dlet s := snd A_s in
          dlet thism := fst (Z.mul_split r s k) in
          dlet q := @scmul _ thism N in
          dlet S1 := @SOS_red_add _ _ A q in
          dlet S2 := fst (@divmod _ S1) in
          S2.

      Lemma red_steps': red_steps = S2. Proof. reflexivity. Qed.
        
    End red_iteration.

    Section red_loop.
      Context (pred_A_numlimbs : nat)
      (N_numlimbs : nat)
      (num_it : nat)
      (A : T (S pred_A_numlimbs))
      (k : Z).

      Definition red_body {pred_A_numlimbs} : T (S pred_A_numlimbs) -> T pred_A_numlimbs
      := fun A => red_steps _ A k.

      Definition red_loop (count : nat) : T (N_numlimbs + count + 1) -> T (N_numlimbs + 1)
      := nat_rect
      (fun count => T (N_numlimbs + count + 1)  -> _ )
      (fun A => A)
      (fun count' red_loop_count' A
      => red_loop_count' (red_body A))
      count.

      Definition pre_red : T (2 * N_numlimbs + 1)
      := (red_loop num_it (Positional.extend_to_length (2 * N_numlimbs) (2 * N_numlimbs + 1) A)).

      Definition red : T (R_numlimbs )
      := conditional_sub (red_loop R_numlimbs (Positional.extend_to_length (2 * R_numlimbs) (2 * R_numlimbs + 1) A)) N.
    End red_loop. 

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
        Transparent T.
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
                ri (ri_correct : r*ri mod (eval N) = 1 mod (eval N))
                (k : Z) (k_correct : k * eval N mod r = (-1) mod r)
                (numbits_big: Z.of_nat R_numlimbs < r).

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
        Proof. clear; cbv [small]; intro H; rewrite H; autorewrite with distr_length; reflexivity. Qed.
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
    (*... *)


    (* Proves behavior on eval on appended lists.*)
    Definition app_hyp v1 : list Z -> Prop
    := fun v2 => 
        (
          @eval (length v1 + length v2) (v1 ++ v2) = @eval (length v1) v1 + r ^ Z.of_nat (length v1) * @eval (length v2) v2
        ).

    Lemma eval_sc: forall sc, @eval 1 [sc] = sc.
    Proof.
      intros; unfold eval, Positional.eval, Associational.eval, Positional.to_associational;
      simpl; rewrite weight_0; [auto with zarith | apply wprops].
    Qed. 

    Lemma eval_app: forall (n1 n2 : nat) v1 v2, length v1 = n1 -> length v2 = n2 -> @eval (n1 + n2) (v1 ++ v2) = @eval n1 v1 + (r ^ (Z.of_nat (length v1)) * (@eval n2 v2)).
    Proof.
      intros n1 n2 v1 v2; generalize dependent n1; generalize dependent n2.
      pose proof (@rev_ind Z (app_hyp v1)) as H. unfold app_hyp in H. intros n1 n2 H0 H1. unfold eval.
      rewrite <- H1. rewrite <- H0. apply H.
        - unfold eval; rewrite Positional.eval_nil; rewrite Z.mul_0_r; simpl;
          repeat rewrite Z.add_0_r. Local Close Scope Z_scope. assert (H2 : length v1 + 0 = length v1) by auto;
          rewrite H2; rewrite app_nil_r; auto.
        - intros x l H2; unfold eval. rewrite app_length. simpl. rewrite Nat.add_1_r.
          assert (H3 : v1 ++ l ++ [x] = (v1 ++ l) ++ [x]) by apply app_assoc. rewrite H3.
          rewrite NPeano.Nat.add_succ_r.
          rewrite Positional.eval_snoc_S; [| rewrite app_length; auto].
          rewrite Positional.eval_snoc_S; try auto.
          unfold eval in H2. rewrite H2.
          rewrite Z.mul_add_distr_l. rewrite Z.mul_assoc. rewrite uweight_sum_indices; try lia.
          rewrite uweight_eq_alt; try lia. unfold r. auto with zarith.
    Qed.

    Local Open Scope Z_scope.
    (*... This part (until next ...) is copied from Fiat Crypto Arithmetic/WordByWordMontgomery*)
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
        Proof.
          clear; autounfold with loc; intros; autorewrite with push_eval; auto.
        Qed.
        Local Lemma small_zero : forall n, small (@zero n).
        Proof.
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

        Lemma small_nil: @small 0 [].
        Proof. reflexivity. Qed.

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

        Lemma length_sc_mul: forall n v sc, n <> O -> length v = n -> length (@scmul n sc v) = S (length v).
        Proof.
          intros. unfold scmul. destruct (Rows.mul weight r n (S n)) eqn:eq1.
          apply (f_equal (fun y => fst y)) in eq1.
          apply (f_equal (fun (y : list Z) => length y)) in eq1. rewrite Rows.length_mul in eq1. simpl in eq1. rewrite H0.
          all: auto. simpl. rewrite Positional.length_zeros. auto with zarith.
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


        Local Open Scope Z_scope.

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


    Lemma length_SOS_red_add: forall n1 n2 (A : T n1) (B : T n2), length A = n1 -> length B = n2 -> (n2 <= n1)%nat -> length (SOS_red_add A B) = length A.
    Proof.
      intros. unfold SOS_red_add. simpl.
      rewrite Saturated.Rows.length_sum_rows with (n := length A); auto; rewrite Positional.length_extend_to_length; auto.
    Qed.
    
    (*These proofs gives an alternative characterisation of small lists; the criterion is contained in the definition below*)
    Definition small_crit n v := (Forall sc_small v) /\ (length v = n).

    Lemma length_S_app: forall (l: list Z) n, length l = S n -> exists l' a, l = @T_app (n) l' a.
    Proof. intros l; apply (rev_ind (fun (y : list Z) => (forall n, length y = S (n) -> exists l' a, y = l' ++ [a]))).
      - intros; discriminate.
      - intros x l0. exists l0, x; auto.
    Qed.

    Lemma weight_value: forall n, weight n = r ^ (Z.of_nat n).
    Proof.
      intros; rewrite uweight_eq_alt'; apply Z.pow_mul_r; lia.
    Qed.

    Lemma r_pow_S : forall n, r ^ (Z.of_nat (S n)) = r ^ (Z.of_nat n) * r.
    Proof.
      intros; rewrite Nat2Z.inj_succ; rewrite Z.pow_succ_r; auto with zarith.
    Qed.

    Lemma sc_small_length_small: forall n (v: T n), length v = n -> Forall sc_small v -> small v.
    Proof. induction n as [| n IHn].
        - intros v H H0. rewrite length_zero_iff_nil in H. rewrite H. apply small_nil.
        - intros v H H0. assert (H': length v = S n) by auto. apply length_S_app in H. destruct H, H.
          assert (small x).
            + apply IHn.
              * apply (f_equal (fun (y : list Z) => length y)) in H. unfold T_app in H.
              rewrite app_length in H. rewrite H' in H. simpl in H. rewrite Nat.add_1_r in H. inversion H.
              auto.
              * unfold T_app in H. rewrite H in H0. rewrite Forall_app in H0. destruct H0. auto.
            + unfold T_app in H. rewrite H. unfold small. rewrite Partition.partition_step.
              rewrite H in H'. rewrite app_length in H'. simpl in H'.
              rewrite Nat.add_1_r in H'. inversion H'.
              assert (Partition.partition weight n (@eval (S n) (x ++ [x0])) = Partition.partition weight n (@eval n (x))).
                { apply Partition.partition_eq_mod; auto. rewrite <- Nat.add_1_r.
                  rewrite eval_app; auto. rewrite H3.
                   rewrite weight_value. rewrite Z.mod_add'_full. auto.
                }
              assert (@eval (S n) (x ++ [x0]) mod weight (S n) / weight n = x0).
              {
                rewrite <- Nat.add_1_r. rewrite eval_app; auto.
                rewrite uweight_pull_mod; auto with zarith.
                assert (n + 1 - n = 1)%nat by auto with zarith. rewrite H4.
                rewrite (weight_value n). rewrite H3. rewrite Z.div_add'; [| unfold r; auto with zarith].
                rewrite Zdiv_small.
                  - rewrite eval_sc. simpl. apply Z.mod_small.
                    assert (sc_small x0).
                      + apply (Forall_forall sc_small v); auto. rewrite H.
                        apply in_or_app. right. simpl. auto.
                      + unfold sc_small in H5. rewrite weight_value. auto with zarith.
                  - apply small_bound in H1. rewrite weight_value in H1. auto.
              }
              unfold small in H1. rewrite H3, H2, H4. rewrite <- H1. auto.
    Qed.

    Lemma small_rem: forall n (v : T n) x, @small (S n) (v ++ [x]) -> small v.
    Proof.
      intros n v x H. pose proof (length_small H) as H0. rewrite app_length in H0. rewrite Nat.add_1_r in H0. inversion H0 as [H2].
      unfold small in H. rewrite Partition.partition_step in H. rewrite <- Nat.add_1_r in H. rewrite eval_app in H; auto.
      apply app_inj_tail in H. destruct H.
      unfold small.
      assert (H3 : Partition.partition weight n
      (eval v + r ^ Z.of_nat (length v) * @eval 1 [x]) = Partition.partition weight (length v) (eval v)).
        - rewrite H2; apply Partition.partition_eq_mod; auto;
          rewrite weight_value; rewrite Z.mod_add'_full; auto.
        - rewrite H2; rewrite H2 in H3; rewrite <- H3; auto; rewrite H2 in H; auto.
    Qed.

    Lemma small_sc_small: forall n (v : T n), small v -> Forall sc_small v.
    Proof. intros n v H.
      apply (rev_ind (fun v => (@small (length v) v -> Forall sc_small v))); [auto | | pose proof (length_small H) as H'; rewrite H'; auto].
      intros x l H0 H1. rewrite Forall_app; split.
        - apply H0. apply (small_rem) with (x := x). auto. simpl in H1.
          unfold small in H1. unfold small. rewrite app_length in H1. simpl in H1. rewrite Nat.add_1_r in H1. auto.
        - apply Forall_cons; auto. unfold small in H1.
          rewrite app_length in H1. simpl in H1. rewrite Nat.add_1_r in H1. rewrite Partition.partition_step in H1.
          apply app_inj_tail in H1. destruct H1. rewrite uweight_pull_mod in H2; auto; try lia.
          assert (H3 : forall n, (S n - n = 1)% nat) by auto with zarith. rewrite H3 in H2. rewrite weight_value in H2.
          unfold sc_small. rewrite H2. rewrite weight_value.
          assert (H4 : r ^ Z.of_nat 1 = r) by auto with zarith. rewrite H4. apply Z.mod_pos_bound. unfold r. auto with zarith.
    Qed.

    Lemma small_if_Forall_sc_small: forall n (v : T n),
    small v <-> (length v = n) /\ (Forall sc_small v).
    Proof.
      intros. split.
        - intros; split; [apply length_small; auto | apply small_sc_small; auto].
        - intros H; apply sc_small_length_small; destruct H; auto.
    Qed.
    
    Lemma small_s_mod: forall n (A : T (S n)), small A -> with_args.s n A = eval A mod r.
    Proof.
      intros n A H. unfold s. simpl. apply small_if_Forall_sc_small in H. destruct H as [H H0].
      destruct A; auto with zarith. simpl. apply Forall_inv in H0. unfold sc_small in H0.
      assert (z :: A = ([z] ++ A)); auto. rewrite H1. pose proof (eval_app 1 n [z] A) as H2.
      assert (H3 : (Init.Nat.add (S O) n) = (S n)) by auto. rewrite H3 in H2. rewrite H2; auto.
      simpl. rewrite Zpow_facts.Zpower_pos_1_r. rewrite Z.mod_add'; auto with zarith.
      rewrite Z.mod_small; [rewrite eval_sc; auto| rewrite eval_sc; auto].
    Qed.

    Lemma nat_sub: forall x y, (S x <= y)%nat -> S (y - S x) = (y - x)%nat.
    Proof.
       intros. rewrite <- Nat.sub_succ_l. rewrite NPeano.Nat.sub_succ; auto. auto. Qed.

    Lemma extend_app: forall n1 n2 v, Positional.extend_to_length (n1) (n1 + n2) v = (v ++ (Positional.zeros n2)).
    Proof.
      intros n1 n2 v. unfold Positional.extend_to_length. assert (H : (n1 + n2 - n1)%nat = n2) by auto with zarith.
      rewrite H. auto.
    Qed.

    Lemma extend_length: forall n1 n2 v, (length v = n2)%nat -> (n2 <= n1)%nat -> length (Positional.extend_to_length n2 n1 v) = n1.
    Proof.
      intros n1 n2 v H H0. assert (H1 : (n1 = n2 + (n1 - n2))%nat) by auto with zarith. rewrite H1. rewrite extend_app.
      rewrite app_length. rewrite Positional.length_zeros. auto.
    Qed.

    Lemma zeros_S: forall n, Positional.zeros (S n) = (Positional.zeros n ++ [0%Z]).
    Proof.
      induction n as [| n IHn].
        - unfold Positional.zeros. simpl. auto.
        - unfold Positional.zeros in IHn. simpl in IHn.
          unfold Positional.zeros. simpl. rewrite IHn. auto.
    Qed.

    Lemma weight_geq: forall n1 n2, ((weight n1) <= (weight (n1 + n2)))%Z.
    Proof. intros n1. induction n2 as [| n2 IHn2].
      - simpl. rewrite Nat.add_0_r. lia.
      - rewrite NPeano.Nat.add_succ_r. simpl. pose proof wprops.
        destruct H. assert ((weight (n1 + n2) <= (weight (S (n1 + n2))))%Z).
          + unfold weight. unfold ModOps.weight. repeat rewrite Z.div_1_r.
            repeat rewrite Z.opp_involutive. auto with zarith.
          + lia.
    Qed.

    Local Close Scope Z_scope.
    Lemma weight_geq': forall n1 n2, n2 <= n1 -> ((weight n2) <= (weight n1))%Z.
    Proof.
      intros n1 n2 H. assert (H0 : (n1 = (n2 + (n1 - n2)))). auto with zarith. rewrite H0.
      apply weight_geq.
    Qed.

    Lemma Partition_long: forall n1 n2 (v : T n1), small v -> Partition.partition weight (n1 + n2) (eval v) = v ++ (Positional.zeros n2).
    Proof.
      induction n2 as [| n2 IHn2].
      - intros v H. rewrite Nat.add_0_r. simpl. unfold Positional.zeros. simpl.
        rewrite <- H. rewrite app_nil_r. auto.
      - intros v H. rewrite NPeano.Nat.add_succ_r.
        rewrite Partition.partition_step. rewrite Z.mod_small;
        [| pose proof (small_bound H); pose proof (weight_geq n1 (S n2)); rewrite <- NPeano.Nat.add_succ_r; lia].
        rewrite Z.div_small;
        [| pose proof (small_bound H); pose proof (weight_geq n1 n2); lia].
        rewrite IHn2; auto. rewrite zeros_S.
        rewrite app_assoc. auto.
    Qed.

    Lemma undo_div: forall n1 n2: nat, forall A : list Z, length A <> O -> A = snd (@divmod n1 A) :: (fst (@divmod n2 A)).
    Proof. intros n1 n2 A. destruct A; [contradiction| auto]. Qed.


    Lemma small_exten: forall n1 (n2: nat) (v : T n2), (n2 <= n1)%nat -> small v -> @small n1 (Positional.extend_to_length n2 n1 v).
    Proof. intros n1 n2 v H H0. apply small_canon_rep with (x := (eval v)). split.
      - assert (H1 : (n1 = n2 + (n1 - n2))%nat) by auto with zarith. rewrite H1. rewrite Partition_long; auto.
        simpl. rewrite <- H1. reflexivity.
      - pose proof (small_bound H0); pose proof (weight_geq' n1 n2); lia.
    Qed.

    Lemma eval_extend: forall n1 n2 (v : T n2), (n2 <= n1)%nat -> length v = n2 -> eval v =  @eval n1 (Positional.extend_to_length n2 n1 v).
    Proof. intros n1 n2 v H H0. assert (H1 : (n1 = n2 + (n1 - n2))%nat) by auto with zarith. rewrite H1. rewrite extend_app.
      rewrite eval_app; try rewrite Positional.length_zeros; auto. rewrite eval_zero. auto with zarith.
    Qed.

    Lemma small_SOS_red_add: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 -> small (SOS_red_add v1 v2).
    Proof. intros n1 n2 v1 v2 H H0 H1.
      destruct n1 eqn:eq1.
        - assert (H2 : (n2 = 0)%nat) by auto with zarith. apply length_small in H0. apply length_small in H1.
          rewrite H2 in H1. apply length_zero_iff_nil in H0.
          apply length_zero_iff_nil in H1. rewrite H0, H1.
          unfold SOS_red_add. simpl. apply small_nil.
        - unfold SOS_red_add. assert (H2 : @small n1 (Positional.extend_to_length n2 n1 v2)) by (apply small_exten; auto; lia).
          rewrite eq1 in H2.
          pose proof (small_addT (S n) v1 (Positional.extend_to_length n2 (S n) v2) H0 H2) as H3. unfold addT in H3.
          remember ( Rows.add weight (S n) v1 (Positional.extend_to_length n2 (S n) v2)) as v'.
          destruct v'. apply small_rem with (x := z). auto.
    Qed.
    
  Local Open Scope Z_scope.

    Lemma eval_SOS_red_add_mod: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 -> eval (SOS_red_add v1 v2) = (eval v1 + eval v2) mod r ^ Z.of_nat n1.
    Proof.
      intros n1 n2 v1 v2 H H0 H1. unfold SOS_red_add. simpl. unfold eval. rewrite Rows.sum_rows_mod;
        [ rewrite weight_value; rewrite <- eval_extend with (n1 := n1); try apply length_small; auto   
        | auto 
        | apply length_small; auto
        | rewrite extend_length; try apply length_small; auto].
    Qed.

    Lemma eval_SOS_add_full: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
      eval (SOS_red_add v1 v2) + (weight n1 * ((eval v1 + eval v2) / weight n1)) = (eval v1 + eval v2).
    Proof.
      intros n1 n2 v1 v2 H H0 H1. unfold SOS_red_add. simpl. unfold eval. rewrite Rows.sum_rows_mod; try apply extend_length; try apply length_small; auto.
      rewrite <- eval_extend with (n1 := n1); try apply length_small; auto.  rewrite <- Z.div_mod''; auto.
    Qed.

    Lemma eval_SOS_add_full': forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
    eval (SOS_red_add v1 v2) = (eval v1 + eval v2) - (weight n1 * ((eval v1 + eval v2) / weight n1)).
    Proof.
      intros n1 n2 v1 v2 H H0 H1. pose proof (eval_SOS_add_full n1 n2 v1 v2 H H0 H1) as H2. apply (f_equal (fun y => y - (weight n1 * ((eval v1 + eval v2) / weight n1)))) in H2.
      assert (H3 : forall (x : Z) y, x + y - y = x). auto with zarith. rewrite H3 in H2. auto.
    Qed.

    Lemma eval_SOS_add_small: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
      (eval v1 + eval v2) < (weight n1)  -> eval (SOS_red_add v1 v2) = (eval v1 + eval v2).
    Proof.
      intros n1 n2 v1 v2 H H0 H1 H2. rewrite eval_SOS_add_full'; auto. rewrite Zdiv_small; auto with zarith.
      apply small_bound in H0. apply small_bound in H1. lia.
    Qed.

    Lemma eval_SOS_bound: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
      eval (SOS_red_add v1 v2) <= eval v1 + eval v2.
    Proof.
      intros n1 n2 v1 v2 H H0 H1. rewrite <- eval_SOS_add_full; auto with zarith.
      pose proof (@small_bound _ v1 H0) as H2. pose proof (@small_bound _ v2 H1) as H3.
      assert (H4 : 0 <= eval v1 + eval v2) by lia. assert (H5 : 0 <= (eval v1 + eval v2) / weight n1 ) by (apply Z.div_nonneg; lia).
      assert (0 <= weight n1 * ((eval v1 + eval v2) / weight n1)); try apply Z.mul_nonneg_nonneg; lia.
    Qed.

    Lemma smallthism': forall n (A : T (S n)), sc_small (thism n A k).
    Proof. intros; unfold thism; rewrite Z.mul_split_mod; unfold sc_small; auto with zarith. Qed. 


    Lemma add_q_low_word: forall n (A : T (S n)), small A -> (eval A + eval (q n A k)) mod r = 0.
    Proof.
      intros n A H. unfold q. rewrite eval_scmul; auto; try lia; try apply smallthism'. unfold thism.
      rewrite Z.mul_split_mod. rewrite small_s_mod; auto. rewrite Z.add_mod; auto with zarith.
      rewrite Z.mul_mod; auto with zarith. repeat rewrite Z.mod_mod; auto with zarith. rewrite <- Z.mul_mod; auto with zarith.
      rewrite <- Z.mul_assoc. rewrite Z.mul_mod; auto with zarith. rewrite k_correct.
      rewrite <- Z.mul_mod; auto with zarith. rewrite <- Z.opp_eq_mul_m1.
      rewrite <- Z.add_mod; auto with zarith. rewrite Z.add_opp_r.
      rewrite Zminus_mod. rewrite Z.mod_mod; auto with zarith. rewrite <- Zminus_mod.
      rewrite Z.sub_diag. auto.
    Qed.

    Lemma r_nz: r <> 0.
    Proof.
      unfold r. auto with zarith.
    Qed.

    Lemma small_carry: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
    ((eval v1 + eval v2) / weight n1) <= 1.
    Proof.
      intros n1 n2 v1 v2 H H0 H1. apply Z.div_floor; auto. simpl.  apply small_bound in H0. apply small_bound in H1.
      pose proof (weight_geq' n1 n2 H). lia.
    Qed.

    Lemma S1_mod_r: forall n (A : T (S n)), (R_numlimbs <= n)%nat -> small A -> eval (S1 n A k) mod r = 0.
    Proof. intros n A H'' H'.
      unfold S1. rewrite eval_SOS_add_full'; auto; try lia. 
      - rewrite Zminus_mod. rewrite weight_value. rewrite r_pow_S.
        rewrite Z.mul_comm.
        rewrite Z.mul_assoc. rewrite Z.mod_mul; auto with zarith. simpl. rewrite Z.sub_0_r.
        rewrite Z.mod_mod; auto with zarith. unfold q. unfold thism. rewrite eval_scmul; auto; try lia; try apply smallthism'.
        rewrite Z.mul_split_mod. rewrite Z.add_mod; auto with zarith. rewrite Z.mul_mod; auto with zarith. rewrite Z.mod_mod; auto with zarith.
        rewrite (Z.mul_mod _ k _); auto with zarith. rewrite <- Z.mul_mod; auto with zarith. rewrite <- Z.mul_assoc. rewrite Z.mul_mod; auto with zarith.
        rewrite (Z.mul_mod _ (eval N) _); auto with zarith. repeat rewrite Z.mod_mod; auto with zarith.
        rewrite <- (Z.mul_mod k _ _); auto with zarith. rewrite k_correct.
        rewrite <- Z.mul_mod; auto with zarith. rewrite <- Z.add_mod; auto with zarith. 
        rewrite <- Z.opp_eq_mul_m1. rewrite Z.add_opp_r.
        rewrite small_s_mod; auto. rewrite Zminus_mod. rewrite Z.mod_mod; auto with zarith. 
        rewrite <- Zminus_mod. rewrite Z.sub_diag. auto.
      - unfold q; apply small_scmul; auto; try apply smallthism'; lia.
    Qed.


    Lemma conditional_sub_final_correct: forall (v : T (S R_numlimbs)), small v -> eval v < eval N + eval N -> eval (conditional_sub v N)= eval (v) mod eval N.
    Proof.
      intros v H H0. assert (H1 : 0 <= eval v < eval N + R) by (pose proof (small_bound H); lia).
      pose proof (conditional_sub_correct v H H1) as H2. destruct H2 as [H2 H3]. rewrite H2.
      destruct (eval N <=? eval v) eqn:eq1; unfold eval; rewrite Partition.eval_partition; auto.
        - rewrite Zmod_small; [|rewrite Z.add_opp_r in H3; unfold eval in H3; auto].
          rewrite <- (Z.mod_add_full _ (-1) _).
          assert (H4 : (Positional.eval weight (S R_numlimbs) v +
          -1 * Positional.eval weight R_numlimbs N) = (Positional.eval weight (S R_numlimbs) v - Positional.eval weight R_numlimbs N)) by
          auto with zarith. rewrite H4. rewrite Zmod_small; auto. 
          simpl in H3. rewrite Z.add_opp_r in H3.
          apply (Z.sub_lt_mono_r _ _ (eval N)) in H0. unfold eval in H0.
          rewrite Z.add_simpl_r in H0.
          unfold eval in H3. lia.
        - rewrite Z.add_0_r. repeat rewrite Zmod_small; auto;
          [| rewrite Z.add_0_r in H3; unfold eval in H3; lia].
          rewrite Z.add_0_r in H3.
          apply Z.leb_gt in eq1. unfold eval in eq1. pose proof (small_bound H) as H4.
          unfold eval in H4. lia. 
    Qed.

    (*... This part (until next ...) is copied from Fiat Crypto Arithmetic/WordByWordMontgomery*)
        Local Opaque T addT drop_high_addT' divmod zero scmul conditional_sub sub_then_maybe_add.
        Create HintDb push_mont_eval discriminated.
        Create HintDb word_by_word_montgomery.
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

    (*The rest of This file contains proofs of correctness; the main correctness theorems are red_correct,
      which states that the output is a proper multi-limb encoding af a number and that
      the encoded number evaluates to the correct number*)
    Section red_body_proofs.
      Context (pred_A_numlimbs : nat)
        (N_numlimbs : nat)
        (A : T (S pred_A_numlimbs))
        (small_A : @small (S pred_A_numlimbs) A)
        (A_len : length A = S pred_A_numlimbs)
        (A_big : (R_numlimbs <= pred_A_numlimbs)%nat)
        (N_len : length N = R_numlimbs)
        (N_eval: 0 <= eval N < r ^ Z.of_nat R_numlimbs).

      Local Notation red_steps A := (@red_steps pred_A_numlimbs A k).

      Lemma A_bounds: 0 <= eval A.
      Proof.
            apply small_bound; auto.
          Qed.

      Lemma q_bounds: 0 <= eval (q (pred_A_numlimbs) A k).
      Proof.
        apply small_bound; unfold q; apply small_scmul; auto; unfold thism; rewrite Z.mul_split_mod; auto with zarith.
      Qed.
          
      Lemma smallthism: sc_small (thism pred_A_numlimbs A k).
      Proof. clear small_A A_len; unfold thism; rewrite Z.mul_split_mod; unfold sc_small; auto with zarith. Qed. 

      Lemma smallq: small (q pred_A_numlimbs A k).
      Proof. unfold q; apply small_scmul; auto; apply smallthism. Qed.
          
      Lemma smallS1 : small (S1 pred_A_numlimbs A k).
      Proof. clear A_len; apply small_SOS_red_add; auto with zarith; apply small_scmul; auto; apply smallthism. Qed.

      Lemma div_monot: forall a b c, 0 <= c -> a <= b -> a / c <= b / c.
      Proof.
        intros. apply Z.div_le_mono_nonneg; auto.
      Qed. 

      Local Open Scope Z_scope.
      Lemma div_bound_aux: forall a b d, 0 < d -> b < d -> (a + b)/ d <= a / d + 1.
      Proof. clear A_len A_big small_A.
        intros a b d H H0. assert (H1 : a + b <= a + d) by lia; apply div_monot with (c := d) in H1; auto; try lia.
        assert (H2 : a + d = a + d * 1) by auto with zarith; rewrite H2 in H1; rewrite Z.div_add' in H1; auto with zarith.
      Qed.

      Lemma red_body_bounds: (S R_numlimbs < pred_A_numlimbs)%nat ->  (eval (red_steps A)) / (weight (Nat.pred pred_A_numlimbs)) <= (eval A) / (weight (pred_A_numlimbs)) + 1.
      Proof. pose proof smallq as Hq. intros H''.
        destruct pred_A_numlimbs eqn:eq'; auto with zarith.
        rewrite red_steps'. unfold S2. rewrite eval_div; [| unfold S1; apply small_SOS_red_add; auto; try lia].
        rewrite Zdiv_Zdiv; try lia; [| pose proof wprops as Hw; destruct Hw; rewrite Nat.pred_succ;
        pose proof (weight_positive n); lia]. simpl.
        pose proof (weight_value (S n)) as H. rewrite Nat2Z.inj_succ in H. rewrite Z.pow_succ_r in H; try lia.
        rewrite H. rewrite weight_value. simpl.
        unfold S1. rewrite eval_SOS_add_full'; auto with zarith.
        destruct (eval A + eval (q (S n) A k) <? (weight (S (S n)))) eqn:eq1.
          - apply Z.ltb_lt in eq1. rewrite (Zdiv_small _ (weight _)).
            + rewrite Z.mul_0_r. rewrite Z.sub_0_r. rewrite weight_value in eq1. rewrite Nat2Z.inj_succ in eq1.
              rewrite Z.pow_succ_r in eq1; try lia.
              apply div_bound_aux; try apply Z.mul_pos_pos; try lia;
              [unfold r; rewrite <- Z.pow_mul_r; auto with zarith|].
              apply small_bound in Hq. rewrite weight_value in Hq. rewrite Nat2Z.inj_succ in Hq. rewrite Z.pow_succ_r in Hq; try lia.
              apply lt_S_n in H''.
              assert (r * r ^ (Z.of_nat R_numlimbs) <= r * r ^ (Z.of_nat n)) by
              (apply Z.mul_le_mono_pos_l; try lia; apply Zpow_facts.Zpower_le_monotone; try lia).
              lia.
            + split; auto. 
              assert (small (q (S n) A k)) by (unfold q; apply small_scmul; auto; unfold thism; rewrite Z.mul_split_mod; auto with zarith).
              apply Z.add_nonneg_nonneg; (apply small_bound; auto).
          - apply Z.ltb_nlt in eq1.
            assert (H0 : ((eval A + eval (q (S n) A k)) / weight (S (S n))) = 1).
              + apply Z.le_antisymm.
                * apply small_carry; auto; lia.
                * assert (1 = 0 + 1) by auto. rewrite H0.
                  apply Ztac.Zlt_le_add_1. apply Z.div_str_pos. apply Z.nlt_ge in eq1.
                  split; try lia. apply wprops.
              + rewrite H0. pose proof (small_bound Hq) as H1. rewrite Z.add_1_r.
                apply Z.le_succ_r; left. apply div_monot;
                [apply Z.mul_nonneg_nonneg; try apply Z.pow_nonneg; lia|].
                rewrite Z.mul_1_r. assert (weight (S R_numlimbs) <= weight (S (S n))); try apply weight_geq'; lia.
      Qed.

    End red_body_proofs.

    Section red_body_proofs.
      Context (pred_A_numlimbs : nat)
              (N_numlimbs : nat)
              (A : T (S pred_A_numlimbs))
              (small_A : small A)
              (A_len : length A = S pred_A_numlimbs)
              (A_big : (R_numlimbs <= pred_A_numlimbs)%nat)
              (N_len : length N = R_numlimbs)
              (N_eval: 0 <= eval N < r ^ Z.of_nat R_numlimbs).

      Local Notation red_body := (@red_body k).
      Local Notation red_loop := (@red_loop N_numlimbs k).

      Let A_s := divmod A.
      Let A' := fst A_s.
      Let s := snd A_s.

      Lemma unfold_A : A = s :: A'.
      Proof. subst s. simpl. subst A'. subst A_s. rewrite <- (undo_div _ _); auto. rewrite A_len. auto. Qed.  

      Lemma small_red_body: small (red_body A).
      Proof. 
        unfold red_body. rewrite red_steps'. rewrite unfold_A.
        unfold S2. pose proof (small_div ( pred_A_numlimbs) (S1 pred_A_numlimbs (s :: A') k)) as H.
        apply H. unfold S1. apply small_SOS_red_add; try lia; [rewrite <- unfold_A; auto| ].
        unfold q. apply small_scmul; auto; apply smallthism'.
      Qed.

      Lemma divmod_A: eval A mod r = s.
        unfold s, A_s; rewrite eval_mod; auto.
      Qed.

      Lemma div_nil: forall n, @divmod n [] = ([], 0).
      Proof. reflexivity. Qed.

      Lemma div_app: forall n v a, @divmod n (a :: v) = (v, a).
      Proof. reflexivity. Qed.

      Lemma length_div: forall n v, length (fst (@divmod n v)) = Nat.pred (length v).
      Proof. destruct v; simpl; [rewrite (div_nil n)| rewrite (div_app n v z)]; auto. Qed.

      Lemma length_red_body: length (red_body A) = pred_A_numlimbs.
      Proof.
        unfold red_body. rewrite red_steps'. unfold S2. rewrite length_div.
        unfold S1. rewrite length_SOS_red_add; auto with zarith.
        unfold q. rewrite length_sc_mul; auto with zarith.
      Qed.

    End red_body_proofs.

    Section red_loop_proofs.
      Context (pred_A_numlimbs : nat)
              (N_numlimbs : nat)
              (N_len : length N = R_numlimbs)
              (A_big : (R_numlimbs <= pred_A_numlimbs)%nat)
              (N_eval: 0 <= eval N < r ^ Z.of_nat R_numlimbs).
  
      Definition first_n {n2} n1 : T (n2) -> T n1
      := fun A => firstn n1 A.

      Local Notation red_body := (@red_body k).
      Local Notation red_loop N_num := (@red_loop N_num k).

      Lemma red_loop_next: forall count init A, red_loop init (S count) A = red_loop init count (red_body (A)).
      Proof. auto. Qed.

      Lemma red_loop_comm: forall count init A, red_body (red_loop (S init) count A) = red_loop init count (red_body A).
      Proof.
      intros count init A. generalize dependent A. induction count as [|count IHcount].
        - intros. simpl. rewrite Nat.add_0_r. auto.
        - intros. pose proof (red_loop_next). rewrite (H count). remember (red_body A) as A'.
          remember (IHcount A'). repeat rewrite <- Nat.add_succ_comm. repeat rewrite <- Nat.add_succ_comm in e. destruct Heqe. rewrite HeqA' in e. simpl in e.
          rewrite Nat.add_0_r. repeat rewrite <- Nat.add_succ_comm in e.
          rewrite Nat.add_0_r in e. rewrite e.
          rewrite H. rewrite HeqA'. repeat rewrite Nat.add_succ_comm.
          repeat rewrite Nat.add_0_r. auto.
      Qed.

      Lemma red_loop_next': forall count init A, red_loop init (S count) (A) = red_body (red_loop (S init) count A).
      Proof.
        intros. rewrite red_loop_comm. auto.
      Qed.

      Lemma small_red_loop: forall init count (A : T (init + count + 1)), small A -> (R_numlimbs <= init)%nat -> (length (A) = init + count + 1)%nat -> small (red_loop (init) count A).
      Proof. clear A_big.
        induction count as [| count IHcount].
          - intros. unfold red_loop. simpl. rewrite Nat.add_0_r in H. auto.
          - intros. rewrite red_loop_next. apply (IHcount); try rewrite length_red_body; auto with zarith. apply small_red_body; auto; try lia.
            repeat rewrite <- Nat.add_succ_comm. rewrite NPeano.Nat.add_succ_l.
            repeat rewrite <- Nat.add_succ_comm in H. rewrite NPeano.Nat.add_succ_l in H.
            auto.
      Qed.

      Lemma length_red_loop: forall init count A, (R_numlimbs <= init)%nat -> (length A = init + count + 1)%nat -> length (red_loop init count A) = (init + 1)%nat.
      Proof. clear A_big.
      intros init count A. generalize dependent A. generalize dependent init. induction count as [| count IHcount].
        - intros. unfold red_loop. simpl. auto with zarith.
        - intros init A H H0.  rewrite red_loop_next'. rewrite length_red_body; auto with zarith.
          + rewrite (IHcount (S init)). auto. auto with zarith. lia.
          + rewrite <- Nat.add_succ_comm. lia.
      Qed. 

    End red_loop_proofs.

    Section red_loop_proofs'.
      Context (pred_A_numlimbs : nat)
              (N_numlimbs : nat)
              (N_len : length N = R_numlimbs)
              (A_big : (R_numlimbs <= pred_A_numlimbs)%nat)
              (N_eval: 0 <= eval N < r ^ Z.of_nat R_numlimbs)
              (A : T (R_numlimbs + R_numlimbs))
              (A_bound : eval A < eval N * eval N)
              (A' : T (S (R_numlimbs + R_numlimbs)) := Positional.extend_to_length (R_numlimbs + R_numlimbs) (S (R_numlimbs + R_numlimbs)) A)
              (A_small: small A).

      Definition A_it (iterations : nat) := red_loop (R_numlimbs + R_numlimbs - iterations) k iterations A'.        

      Lemma small_A': small A'.
      Proof. unfold A'. apply small_exten; auto. Qed.

      Lemma small_A_it : forall it, (it <= R_numlimbs)%nat -> small (A_it it).
      Proof.
        intros. unfold A_it. apply small_red_loop. all: (auto with zarith; try lia).
        assert (S (R_numlimbs + R_numlimbs) = (R_numlimbs + R_numlimbs - it + it + 1)%nat). auto with zarith.
        rewrite <- H0. apply small_exten. lia. auto.
        apply length_small in A_small. unfold A'. rewrite extend_length; auto with zarith.
      Qed.

      Lemma small_red_loop_A': forall it, (it <= R_numlimbs)%nat -> small (red_loop (R_numlimbs + R_numlimbs - it) k it A').
      Proof.
        intros it H.
        assert (H0 : (R_numlimbs + R_numlimbs - it + it + 1 = S (R_numlimbs + R_numlimbs))%nat) by auto with zarith.
        apply small_red_loop; auto; try lia; rewrite H0; try apply length_small; apply small_A'.
      Qed.

      Lemma red_loop_bound_N: forall it, (0 < it <= R_numlimbs)%nat ->
      eval (A_it it) < eval N * r ^ (Z.of_nat (R_numlimbs - it)) + eval N.
      Proof.
        intros it H. destruct it; try (exfalso; apply (Nat.lt_irrefl O); lia).
        induction it as [| it IHit].
          - unfold A_it. simpl. unfold red_body. rewrite red_steps'.
            unfold S2. rewrite Nat.add_0_r. assert (H0 : (forall y, 0 < y -> y + y -1 + 1 = y + y)%nat ) by auto with zarith.
            rewrite H0; try lia.
            rewrite eval_div; [| apply small_SOS_red_add; try lia; try apply small_A'; apply small_scmul; auto; apply smallthism'].
            apply (Zmult_gt_0_lt_reg_r _ _ r); try lia.
            rewrite Z.mul_div_eq'; try lia. rewrite S1_mod_r; try lia; try apply small_A'.
            rewrite Z.sub_0_r. rewrite Z.mul_add_distr_r.
            unfold S1.
            assert (H1 : eval (SOS_red_add A' (q (R_numlimbs + R_numlimbs) A' k)) <= eval A' + eval (q (R_numlimbs + R_numlimbs) A' k)).
            {
              apply eval_SOS_bound; try lia; try apply small_A'. unfold q.
              apply small_scmul; auto; apply smallthism'.
            }
            rewrite <- Z.mul_assoc. rewrite (Z.mul_comm _ r).
            rewrite <- Z.pow_succ_r; try lia. rewrite <- Nat2Z.inj_succ.
            assert (H2 : S (R_numlimbs - 1) = R_numlimbs) by auto with zarith. rewrite H2.
            assert (eval A' < eval N * r ^ Z.of_nat R_numlimbs).
            {
              unfold A'. rewrite <- eval_extend; try lia; try (apply length_small; auto).
              pose proof (small_bound A_small). pose proof (small_bound small_N) as H4.
              destruct H4 as [H4 H5]. rewrite weight_value in H5.
              assert ( eval N * eval N <= eval N * r ^ Z.of_nat R_numlimbs) by (apply Z.mul_le_mono_pos_l; lia). lia.
            }
            assert (H4 : eval (q (R_numlimbs + R_numlimbs) A' k) < eval N * r).
            {
              unfold q. rewrite eval_scmul; auto; try apply smallthism'. pose proof (smallthism' (R_numlimbs + R_numlimbs) A') as H4.
              unfold sc_small in H4. rewrite Z.mul_comm. apply Zmult_gt_0_lt_compat_l; try lia.
            }
            lia.
          - remember (S it) as it'.
            unfold A_it in IHit.
            assert (HZ: (R_numlimbs + R_numlimbs - it' + it' + 1)%nat = (S (R_numlimbs + R_numlimbs))%nat) by auto with zarith.
            assert (H0 : (S (R_numlimbs + R_numlimbs - (S it')) = R_numlimbs + R_numlimbs - it')%nat) by auto with zarith.
            unfold A_it. rewrite red_loop_next'. repeat rewrite Nat.add_1_r. unfold red_body.
            rewrite red_steps'. unfold S2. rewrite eval_div.
            + apply (Zmult_gt_0_lt_reg_r _ _ r); try lia.
              rewrite Z.mul_div_eq'; try lia. rewrite S1_mod_r; auto; try lia; [| rewrite H0; rewrite <- Nat.add_1_r; apply small_red_loop_A'; lia].
              rewrite Z.sub_0_r. rewrite Z.mul_add_distr_r.
              rewrite H0. unfold S1.
              assert (H1 : eval
              (SOS_red_add (red_loop (R_numlimbs + R_numlimbs - it') k it' A')
                (q (R_numlimbs + R_numlimbs - it')
                (red_loop (R_numlimbs + R_numlimbs - it') k it' A') k)) 
                <= eval (red_loop (R_numlimbs + R_numlimbs - it') k it' A') + eval (q (R_numlimbs + R_numlimbs - it')
                (red_loop (R_numlimbs + R_numlimbs - it') k it' A') k)).
                {
                  apply eval_SOS_bound; try lia.
                  + apply small_red_loop; try lia. rewrite HZ. apply small_A'.
                    rewrite HZ. apply length_small. apply small_A'.
                  + unfold q; apply small_scmul; auto; apply smallthism'.
                }
              assert (H2 : r ^ Z.of_nat (R_numlimbs - S it') * r = r ^ Z.of_nat (R_numlimbs - it')).
                {
                  rewrite Z.mul_comm. rewrite <- Z.pow_succ_r; try lia. rewrite <- Nat2Z.inj_succ.
                  assert (H2 : (S (R_numlimbs - S it') = R_numlimbs - it')%nat) by auto with zarith.
                  rewrite H2; auto.
                }
              rewrite <- Z.mul_assoc. rewrite H2.
              assert (H3 : (0 < it' <= R_numlimbs)%nat) by lia.
              remember (IHit H3) as H4. destruct HeqH4.
              assert (H5 :eval (q (R_numlimbs + R_numlimbs - it')
                (red_loop (R_numlimbs + R_numlimbs - it') k it' A') k) <= eval N * (r - 1)).
                {
                  unfold q; rewrite eval_scmul; auto; try apply smallthism'. rewrite Z.mul_comm.
                  assert ((thism (R_numlimbs + R_numlimbs - it')
                  (red_loop (R_numlimbs + R_numlimbs - it') k it' A') k) <= r - 1).
                  - apply Z.lt_succ_r. assert (Z.succ (r - 1) = r) by auto with zarith. rewrite H5.
                    apply smallthism'.
                  - apply Z.mul_le_mono_pos_l; lia.
                }
              assert (H6 : eval N * r = eval N + eval N * (r - 1)) by auto with zarith. rewrite H6. rewrite Z.add_assoc.
              assert (H7 : eval (red_loop (R_numlimbs + R_numlimbs - it') k it' A') +
                eval (q (R_numlimbs + R_numlimbs - it')
                (red_loop (R_numlimbs + R_numlimbs - it') k it' A') k)
                < eval N * r ^ Z.of_nat (R_numlimbs - it') + eval N + eval N * (r - 1)) by lia.
              apply Le.Z.le_lt_trans with (m := eval (red_loop (R_numlimbs + R_numlimbs - it') k it' A') +
                eval
                (q (R_numlimbs + R_numlimbs - it')
                (red_loop (R_numlimbs + R_numlimbs - it') k it' A') k)); try lia.
              repeat rewrite Nat.add_1_r in H1. repeat rewrite Nat.add_1_r. apply H1.
            + unfold S1; apply small_SOS_red_add; try lia; [rewrite H0; rewrite <- Nat.add_1_r; apply small_red_loop_A'; lia
              |unfold q; apply small_scmul; auto; apply smallthism'].
      Qed.

      Lemma red_loop_it: forall it, (it < R_numlimbs)%nat -> eval (A_it it) / weight (R_numlimbs + R_numlimbs - it) <= Z.of_nat it.
      Proof.
        induction it as [|it IHit].
          - intros H. unfold A_it. unfold red_loop. simpl. assert (small A') by (apply small_exten; auto; try lia).
            rewrite Zdiv_small; auto with zarith. unfold A'.
            rewrite Nat.sub_0_r. rewrite Nat.add_1_r.
            rewrite <- eval_extend; [| lia| apply length_small in A_small; auto]. apply small_bound in A_small. auto. 
          - intros H'. unfold A_it. unfold A_it in IHit. rewrite red_loop_next'.
            assert (H : (S (R_numlimbs + R_numlimbs - S it) = R_numlimbs + R_numlimbs - it)%nat).  auto with zarith.
            rewrite H.
            remember (red_loop (R_numlimbs + R_numlimbs - it) k it A') as A''.
            assert (H0 : eval (red_body k (red_loop (S (R_numlimbs + R_numlimbs - S it)) k it A')) /
            weight (R_numlimbs + R_numlimbs - S it) <= eval A'' / weight (R_numlimbs + R_numlimbs - it) + 1).
              {
                rewrite H. rewrite <- HeqA''. unfold red_body.
                pose proof (red_body_bounds (R_numlimbs + R_numlimbs - it) A'').
                rewrite Nat.add_1_r. assert (R_numlimbs + R_numlimbs - S it = Nat.pred (R_numlimbs + R_numlimbs - it))%nat by auto with zarith.
                rewrite H1. rewrite NPeano.Nat.succ_pred_pos; try lia.
                rewrite Nat.add_1_r. apply H0; auto; try lia.
                - pose proof (length_small small_N).
                  rewrite HeqA''. assert (0 <= eval N < r ^ Z.of_nat R_numlimbs) by auto.
                  pose proof (small_red_loop H2 H3 (R_numlimbs + R_numlimbs - it) it A').
                  repeat rewrite Nat.add_1_r in H4. apply H4; try lia.
                  + assert (S (R_numlimbs + R_numlimbs - it + it) = S (R_numlimbs + R_numlimbs)). auto with zarith.
                  rewrite H5. apply small_A'.
                  + unfold A'. rewrite extend_length; auto with zarith; try lia.
                    pose proof (length_small A_small). auto.
                - rewrite HeqA''. pose proof (length_small small_N).
                  pose proof (length_red_loop H2 (R_numlimbs + R_numlimbs - it) it A').
                  repeat rewrite Nat.add_1_r in H3. apply H3; try lia.
                  unfold A'. assert (S (R_numlimbs + R_numlimbs - it + it) = S (R_numlimbs + R_numlimbs)) by auto with zarith.
                  rewrite H4. apply extend_length; auto; try lia. apply length_small; auto. 
              }
            assert (S (R_numlimbs + R_numlimbs - S it)= R_numlimbs + R_numlimbs - it)%nat by auto with zarith.
            rewrite H1 in H0. rewrite <- HeqA'' in H0.
            repeat rewrite Nat.add_1_r. repeat rewrite Nat.add_1_r in H0.
            repeat rewrite Nat.add_1_r in IHit. assert (it < R_numlimbs)%nat by lia.
            apply IHit in H2. lia.
      Qed.

      Lemma add_small_it: forall it, (it < R_numlimbs)%nat -> eval (A_it it) + eval (q (R_numlimbs + R_numlimbs - it) (A_it it) k)
        < weight (S (R_numlimbs + R_numlimbs - it)).
      Proof. intros it H. pose proof Z.add_0_r as H0. pose proof Z.add_0_l as H1. 
        pose proof (red_loop_it it) as H2. assert (H3 : (it < R_numlimbs)%nat) by lia.
        apply H2 in H3.
        apply (Z.mul_le_mono_pos_r _ _ (weight (R_numlimbs + R_numlimbs - it))) in H3.
        2: {rewrite weight_value. unfold r. rewrite <- Z.pow_mul_r.
            apply Pow2.Z.pow2_gt_0. assert (0 < R_numlimbs + R_numlimbs - it)%nat by lia.
            lia. lia. lia. }
        rewrite Z.mul_comm in H3. rewrite Z.mul_div_eq_full in H3; auto.
        apply (Z.add_le_mono_r _ _ (eval (A_it it) mod weight (R_numlimbs + R_numlimbs - it))) in H3.
        simpl in H3. rewrite Z.sub_add in H3.
        assert (eval (A_it it) mod weight (R_numlimbs + R_numlimbs - it) < weight (R_numlimbs + R_numlimbs - it)).
        - apply Z.mod_bound_pos; auto with zarith. apply small_bound. rewrite Nat.add_1_r. auto.
          unfold A_it. pose proof (length_small small_N) as HN.
          pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
          pose proof (small_red_loop HN HN' (R_numlimbs + R_numlimbs - it) it A').
          repeat rewrite Nat.add_1_r in H4. apply H4; try lia.
          + pose proof small_A'.
            assert (H6 : (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat) by auto with zarith.
            rewrite H6. auto.
          + assert (H5 : (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat) by auto with zarith.
            rewrite H5. apply length_small. apply small_A'.
        - assert ( (Z.of_nat it) * weight (R_numlimbs + R_numlimbs - it) + eval (A_it it) mod weight (R_numlimbs + R_numlimbs - it) < (Z.of_nat it + 1) * weight (R_numlimbs + R_numlimbs - it)) by lia.
          assert (eval (A_it it) <=  (Z.of_nat it + 1) * weight (R_numlimbs + R_numlimbs - it)) by lia.
          assert (H7 : small (q (R_numlimbs + R_numlimbs - it)
          (red_loop (R_numlimbs + R_numlimbs - it) k it A') k)).
            * unfold q. apply small_scmul; auto; apply smallthism'.
            * apply small_bound in H7.
            assert (H8 : weight (S R_numlimbs) + (Z.of_nat it + 1) * weight (R_numlimbs + R_numlimbs - it) <= weight (S (R_numlimbs + R_numlimbs - it))).
            {
              repeat rewrite weight_value.
              assert (Z.of_nat it + 1 <= r - 1); try lia. 
              assert (H9 : (Z.of_nat it + 1) * r ^ Z.of_nat (R_numlimbs + R_numlimbs - it) <= (r - 1) * r ^ Z.of_nat ((R_numlimbs + R_numlimbs - it))).
              {
                apply Z.mul_le_mono_nonneg_r; try lia. assert (H9 : (O < R_numlimbs + R_numlimbs - it)%nat) by lia.
                unfold r. rewrite <- Z.pow_mul_r; try lia.
                apply Pow2.Z.pow2_ge_0.
              }
              assert (H10 : r ^ Z.of_nat (S R_numlimbs) <= r ^ Z.of_nat (R_numlimbs + R_numlimbs - it)).
              {
                pose proof (Z.pow_le_mono_r r (Z.of_nat (S R_numlimbs)) (Z.of_nat (R_numlimbs + R_numlimbs - it))) as H10.
                apply H10; lia.
              }
              rewrite Z.mul_sub_distr_r in H9. rewrite Z.mul_1_l in H9.
              rewrite (Z.add_le_mono_r _ _ (r ^ Z.of_nat (R_numlimbs + R_numlimbs - it))) in H9.
              rewrite Z.sub_add in H9.
              rewrite Z.add_comm in H9. rewrite (Nat2Z.inj_succ (R_numlimbs + R_numlimbs - it) ).
              rewrite (Z.pow_succ_r  _ (Z.of_nat (R_numlimbs + R_numlimbs - it))); lia.
          }
          unfold A_it in H6. rewrite Z.add_comm in H8.
          assert (H9 :  (eval (red_loop (R_numlimbs + R_numlimbs - it) k it A') +
          eval
            (q (R_numlimbs + R_numlimbs - it)
              (red_loop (R_numlimbs + R_numlimbs - it) k it A') k)) < (Z.of_nat it + 1) * weight (R_numlimbs + R_numlimbs - it) +
              weight (S R_numlimbs)); try lia. repeat rewrite Nat.add_1_r in H9. unfold A_it.
              lia.
      Qed.

      Lemma red_loop_it_mod: forall it, (it < R_numlimbs)%nat -> ((r ^ Z.of_nat it * eval (A_it it) mod eval N)
        = eval A mod eval N).
      Proof.
        intros it H. assert (Haux: (R_numlimbs + R_numlimbs - it + it)%nat = (R_numlimbs + R_numlimbs)%nat) by auto with zarith.
        assert (small_A_it: small (A_it it)).
        {
          unfold A_it. apply small_red_loop; auto; try lia. 
          - rewrite Haux. rewrite Nat.add_1_r. apply small_A'.
          - rewrite Haux. rewrite Nat.add_1_r. apply length_small. apply small_A'.
        } 
        induction it as [|it IHit].
        - unfold A_it. unfold red_loop. simpl. simpl. assert (eval A = eval A'); [unfold A'; rewrite <- eval_extend; try apply length_small; auto|].
          rewrite Nat.sub_0_r. rewrite Nat.add_1_r. rewrite H0. destruct (eval A'); auto.
        - unfold A_it. rewrite red_loop_next'. rewrite r_pow_S.
          assert (it < R_numlimbs)%nat by lia. apply IHit in H0; try lia.
          + repeat rewrite Nat.add_1_r. unfold red_body. rewrite red_steps'.
            unfold S2. rewrite eval_div.
            2: {
              unfold S1. apply small_SOS_red_add; try lia.
              assert (HN: length N = R_numlimbs). apply length_small; auto.
              pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
              pose proof (small_red_loop HN HN' ( (R_numlimbs + R_numlimbs - it)) it). Set Printing All.
              assert ((S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S it)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( it)))) by auto with zarith.
              rewrite H2. repeat rewrite Nat.add_1_r in H1.
              Set Printing All.
              apply H1.
              assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
              rewrite H3. apply small_A'. lia.
              assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
              rewrite H3. apply extend_length; auto. apply length_small. auto.
              unfold q. apply small_scmul; auto; apply smallthism'.
            }
            rewrite <- Z.mul_assoc.
            rewrite Z.mul_div_eq_full; auto with zarith. rewrite S1_mod_r; try lia.
            2: {
              assert (HN: length N = R_numlimbs). apply length_small; auto.
              pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
              pose proof (small_red_loop HN HN' ( (R_numlimbs + R_numlimbs - it)) it). Set Printing All.
              assert ((S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S it)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( it)))) by auto with zarith.
              rewrite H2. repeat rewrite Nat.add_1_r in H1.
              Set Printing All.
              apply H1.
              assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
              rewrite H3. apply small_A'. lia.
              assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
              rewrite H3. apply extend_length; auto. apply length_small. auto.
            }
            rewrite Z.sub_0_r.
            unfold A_it in H0. unfold S1. rewrite eval_SOS_add_small; try lia.
            * unfold q. rewrite eval_scmul; [|auto|apply smallthism'; auto|lia]. rewrite Z.mul_mod; auto with zarith.
              rewrite Z.add_mod; auto with zarith.
              rewrite Z.mod_mul; auto with zarith. rewrite Z.add_0_r.
              rewrite <- Z.mod_mod; auto with zarith. rewrite <- Z.mul_mod; auto with zarith. rewrite Z.mod_mod; auto with zarith.
              assert (S (R_numlimbs + R_numlimbs - S it) = (R_numlimbs + R_numlimbs - it))%nat by auto with zarith.
              rewrite H1. 
              rewrite Nat.add_1_r in H0.
              rewrite Z.mul_mod; auto with zarith. rewrite Z.mod_mod; auto with zarith. rewrite <- Z.mul_mod; auto with zarith.
            * pose proof (length_small small_N) as HN.
              pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
              pose proof (small_red_loop HN HN' (R_numlimbs + R_numlimbs - it) it A') as H1.
              assert (H2 : (S (R_numlimbs + R_numlimbs - S it) = (R_numlimbs + R_numlimbs - it))%nat) by auto with zarith.
              rewrite H2.
              repeat rewrite Nat.add_1_r in H1. apply H1; try lia.
              {
                assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
                rewrite H3. apply small_A'.
              }
              assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
              rewrite H3. apply length_small. apply small_A'.
            * unfold q. apply small_scmul; auto; try lia. apply smallthism'.
            * assert (H1: (S (R_numlimbs + R_numlimbs - S it) = (R_numlimbs + R_numlimbs - it))%nat) by auto with zarith.
              rewrite H1. pose proof (add_small_it it) as H2. unfold A_it in H2.
              rewrite Nat.add_1_r in H2. apply H2. lia.
          + repeat rewrite Nat.add_1_r.
            unfold A_it.
            assert (HN: length N = R_numlimbs) by (apply length_small; auto).
            pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
            pose proof (small_red_loop HN HN' ( (R_numlimbs + R_numlimbs - it)) it) as H1.
            assert (H2 : (S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S it)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( it)))) by auto with zarith.
            repeat rewrite Nat.add_1_r in H1.
            apply H1; try lia.
            * assert (H3: (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat) by auto with zarith.
              rewrite H3. apply small_A'. 
            * assert (H3: (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat) by auto with zarith.
              rewrite H3. apply extend_length; auto. apply length_small. auto.
      Qed.


      Lemma small_red_loop_final:forall x, R_numlimbs = S x -> small (red_loop (S R_numlimbs) k x A').
      Proof.
        intros x H.
        assert (HN: length N = R_numlimbs); [apply length_small; auto|].
        pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
        pose proof (small_red_loop HN HN' (S R_numlimbs ) x A') as H0.
        assert (H1: (S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S x)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( x)))) by auto with zarith.
        repeat rewrite Nat.add_1_r in H1. apply H0; try lia.
        - pose proof small_A' as H2.
          unfold small. unfold small in H2.
          assert (H3 : (R_numlimbs + R_numlimbs = S R_numlimbs + x)%nat) by auto with zarith.
          rewrite <- H3. rewrite Nat.add_1_r. auto.
        - unfold A'. rewrite extend_length; auto with zarith; try lia.
          apply length_small; auto. 
      Qed.

      Lemma red_loop_final: (r ^ Z.of_nat R_numlimbs) * eval (A_it R_numlimbs) mod eval N = eval A mod eval N.
      Proof.
        unfold A_it. assert (H: (forall (y : nat), y + y - y = y)%nat) by auto with zarith. rewrite H.
        assert (H0 : exists x, R_numlimbs = S x). apply Nat.neq_0_r. auto. destruct H0.
        assert (H1: eval (red_loop R_numlimbs k R_numlimbs A') = eval (red_loop R_numlimbs k (S x) A')) by (rewrite <- H0; auto).
        rewrite H1. rewrite red_loop_next'. repeat rewrite Nat.add_1_r. unfold red_body.
        rewrite red_steps'. unfold S2. rewrite eval_div.
        - unfold S1. rewrite eval_SOS_add_small; try lia.
          + assert (r ^ Z.of_nat R_numlimbs = r ^ (Z.of_nat (S x))) by (rewrite H0; auto).
          rewrite H2. rewrite r_pow_S. rewrite <- Z.mul_assoc.
          rewrite Z.mul_div_eq; try lia. pose proof S1_mod_r as H3. unfold S1 in H3.
          unfold SOS_red_add in H3. rewrite add_q_low_word; [| rewrite <- Nat.add_1_r; apply small_red_loop_final; auto].
          rewrite Z.sub_0_r. unfold q. rewrite eval_scmul; auto; try apply smallthism'.
          rewrite Z.mul_add_distr_l. rewrite Z.add_mod; auto with zarith.
          rewrite Z.mul_assoc. rewrite Z_mod_mult. rewrite Z.add_0_r.
          rewrite Z.mul_mod; auto with zarith. rewrite Z.mod_mod; auto with zarith.
          rewrite <- Z.mul_mod; auto with zarith. assert (x < R_numlimbs)%nat by lia.
          pose proof (red_loop_it_mod x H4) as H5. unfold A_it in H5.
          assert (H6 : (R_numlimbs + R_numlimbs - x = S R_numlimbs)%nat) by auto with zarith.
          rewrite H6 in H5. rewrite Nat.add_1_r in H5. 
          apply H5.
          + rewrite <- Nat.add_1_r; apply small_red_loop_final; auto.
          + unfold q; apply small_scmul; auto; apply smallthism'.
          + assert (H2: (S R_numlimbs = R_numlimbs + R_numlimbs - x)%nat) by auto with zarith.
            repeat rewrite H2. pose proof (add_small_it x) as H3. unfold A_it in H3. rewrite Nat.add_1_r in H3.
            rewrite H2 in H3. apply H3. lia.
        - unfold S1. apply small_SOS_red_add; try lia;
          [rewrite <- Nat.add_1_r; apply small_red_loop_final; auto
          |unfold q; apply small_scmul; auto; apply smallthism'].
      Qed.

    End red_loop_proofs'.

    Section final_proofs.

      Definition R'
      := Z.modinv R (eval N).

      Hypothesis R'_correct: R' * R mod eval N = 1.

      Lemma small_aux: forall (A : T (R_numlimbs + R_numlimbs)), small A -> small (red_loop R_numlimbs k R_numlimbs (Positional.extend_to_length (2 * R_numlimbs) (2 * R_numlimbs + 1) A)).
      Proof.
        intros A H.
        assert (H'' : @small (R_numlimbs + R_numlimbs + 1) (Positional.extend_to_length (2 * R_numlimbs) (2 * R_numlimbs + 1) A)).
          {
            assert (2 * R_numlimbs = R_numlimbs + R_numlimbs)%nat as Hmul by auto with zarith.
            rewrite Hmul. apply small_exten; try lia; auto.
          }
        rewrite <- Nat.add_1_r. apply small_red_loop; try apply length_small; auto; try lia.
      Qed.

      Lemma red_correct: forall (A : T (R_numlimbs + R_numlimbs)), small A -> eval A < eval N * eval N -> eval (red (Nat.pred (R_numlimbs + R_numlimbs)) R_numlimbs A k) = (R' * eval A) mod eval N
        /\ small (red (Nat.pred R_numlimbs + R_numlimbs) R_numlimbs A k).
      Proof.
        intros A H H'. split.
          - rewrite Z.mul_mod; auto with zarith. rewrite <- red_loop_final with (pred_A_numlimbs := Nat.pred (R_numlimbs + R_numlimbs)); try apply length_small; auto; try lia.
            rewrite (Z.mul_mod  (r ^ _) _ _); auto with zarith. rewrite <- Z.mul_mod; auto with zarith. rewrite Z.mul_assoc.
            rewrite Z.mul_mod; auto with zarith. rewrite Z.mod_mod; auto with zarith. rewrite (Z.mul_mod R' _ _); auto with zarith.
            rewrite Z.mod_mod; auto with zarith.
            rewrite <- (Z.mul_mod R' _ _); auto with zarith. assert (R = r ^ Z.of_nat R_numlimbs) as H0 by auto.
            rewrite <- H0.
            rewrite R'_correct. rewrite Z.mul_1_l. rewrite Z.mod_mod; auto with zarith. unfold red.
            rewrite conditional_sub_final_correct; try (rewrite <- Nat.add_1_r; apply small_aux; auto).
            + unfold A_it.
            assert ((2 * R_numlimbs)%nat = R_numlimbs + R_numlimbs)%nat as H1 by auto with zarith.
            assert (S (R_numlimbs + R_numlimbs) = R_numlimbs + R_numlimbs + 1)%nat as H2 by auto with zarith.
            rewrite H1. rewrite H2. auto. assert ( R_numlimbs + R_numlimbs - R_numlimbs = R_numlimbs)%nat as H3 by auto with zarith.
            rewrite H3. auto.  repeat rewrite Nat.add_1_r. reflexivity.
            + pose proof (red_loop_bound_N (2 * R_numlimbs)) as H1.
              assert (HN : length N = R_numlimbs) by (apply length_small; auto).
              assert (R_numlimbs <= 2 * R_numlimbs)%nat as H2 by lia.
              pose proof (small_bound small_N) as H3. rewrite weight_value in H3.
              pose proof (red_loop_bound_N (2 * R_numlimbs) HN H2 H3 A H' H R_numlimbs) as H4. 
              assert (r ^ Z.of_nat (R_numlimbs - R_numlimbs) = 1) as H5 by
              (rewrite Nat.sub_diag; rewrite Z.pow_0_r; auto).
              rewrite H5 in H4. rewrite Z.mul_1_r in H4. unfold A_it in H4.
              assert (R_numlimbs + R_numlimbs - R_numlimbs = R_numlimbs)%nat as H6 by auto with zarith.
              rewrite H6 in H4.
              assert (2 * R_numlimbs = R_numlimbs + R_numlimbs)%nat as H7 by auto with zarith.
              rewrite H7. repeat rewrite Nat.add_1_r. repeat rewrite Nat.add_1_r in H4. apply H4. lia.
        - unfold red. apply small_conditional_sub; try (rewrite <- Nat.add_1_r; apply small_aux; auto).
          assert (HN : length N = R_numlimbs) by (apply length_small; auto).
          assert (R_numlimbs <= 2 * R_numlimbs)%nat as H0 by lia.
          pose proof (small_bound small_N) as H1. rewrite weight_value in H1.
          assert (0 < R_numlimbs <= R_numlimbs)%nat as H2 by lia.
          pose proof (red_loop_bound_N (2 * R_numlimbs) HN H0 H1 A H' H R_numlimbs H2) as H3. 
          assert (r ^ Z.of_nat (R_numlimbs - R_numlimbs) = 1) as H4 by
          (rewrite Nat.sub_diag; rewrite Z.pow_0_r; auto).
          rewrite H4 in H3. rewrite Z.mul_1_r in H3. unfold A_it in H3.
          assert (R_numlimbs + R_numlimbs - R_numlimbs = R_numlimbs)%nat as H5 by auto with zarith.
          rewrite H5 in H3.
          assert (2 * R_numlimbs = R_numlimbs + R_numlimbs)%nat as H6 by auto with zarith.
          split.
          + apply small_bound.
            rewrite H6. rewrite <- Nat.add_1_r. apply small_red_loop; auto; try lia;
            [apply small_exten; auto; lia|].
            apply Positional.length_extend_to_length; try lia. apply length_small; auto.
          + assert (eval N + eval N <= eval N + R). lia. rewrite H6.
            rewrite Nat.add_1_r. repeat rewrite Nat.add_1_r in H3. lia.
      Qed.
    End final_proofs.
  End with_args.
End WordByWordMontgomery.