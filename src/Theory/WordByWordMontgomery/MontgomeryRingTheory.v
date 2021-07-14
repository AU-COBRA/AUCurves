Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Eqdep_dec.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Coqprime.elliptic.GZnZ.

Open Scope Z_scope.

Section wbw_ring.
(*We define the ring structure of Biglist encodings of numbers in montgomery form mod m.*)

        Context (m : Z)
                (bw : Z)
                (n : nat)
                (r' : Z)
                (m' : Z).

        Definition r := (2 ^ bw).
        Definition uw := uweight bw.

        Local Coercion Z.of_nat : nat >-> Z.

        Context (r'_correct : (r * r') mod m = 1)
                (m'_correct : (m * m') mod r = (-1) mod r)
                (bw_big : 0 < bw)
                (n_nz : n <> 0%nat)
                (m_small : m < r ^ (n%nat))
                (m_big : 1 < m).

        Lemma m_big' : 0 < m.
        Proof. pose proof m_big; lia. Qed.

        Lemma m_small' : m < uw n.
        Proof.
                cbv [uw uweight ModOps.weight].
                rewrite Z.div_1_r, Z.opp_involutive.
                pose proof m_small as H. unfold r in H. rewrite Z.pow_mul_r; [auto| pose proof bw_big; lia| pose proof n_nz; lia].
        Qed.


        Local Notation eval := (@WordByWordMontgomery.eval bw n).
        Local Notation valid := (@WordByWordMontgomery.valid bw n m).
        Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
        Local Notation to_mont := (@WordByWordMontgomery.to_montgomerymod bw n m m').
        Local Notation wbw_add := (@WordByWordMontgomery.addmod bw n m).
        Local Notation wbw_sub := (@WordByWordMontgomery.submod bw n m).
        Local Notation wbw_opp := (@WordByWordMontgomery.oppmod bw n m).
        Local Notation wbw_mul := (@WordByWordMontgomery.mulmod bw n m m').

        Definition from_mont_correct := (WordByWordMontgomery.from_montgomerymod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
        Definition to_mont_correct := (WordByWordMontgomery.to_montgomerymod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
        Definition add_mod_correct := (WordByWordMontgomery.addmod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
        Definition sub_mod_correct := (WordByWordMontgomery.submod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
        Definition opp_mod_correct := (WordByWordMontgomery.oppmod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
        Definition mul_mod_correct := (WordByWordMontgomery.mulmod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
        Notation evfrom x := (eval (from_mont x)).

        (*Technical lemma. TODO: move*)

        Lemma Zmod_mod_small : forall a b c, b > 0 -> b < c -> (a mod b) mod c = a mod b.
        Proof.
        intros. rewrite Zmod_small; auto.
        assert (a mod b < b) by (apply Z_mod_lt; auto).
        split; try lia. apply Z_mod_lt; auto.
        Qed.

        Lemma valid_partition_small : forall x, x = x mod m -> valid (Partition.partition uw n x).
        Proof.
        intros. split.
        - unfold WordByWordMontgomery.small. unfold eval. rewrite eval_partition; [| apply uwprops, bw_big].
        rewrite Zmod_small.
        2: {
                        assert (x < m) by (rewrite H; apply Z_mod_lt; pose proof m_big'; lia). 
                        pose proof m_small'.
                        split; [| lia]; rewrite H; apply Z_mod_lt; pose proof m_big; lia.
                }
                reflexivity.
                - unfold eval. rewrite eval_partition; [| apply uwprops, bw_big].
                rewrite H. rewrite Zmod_mod_small.
                        + apply Z_mod_lt. pose proof m_big'; lia.
                        + pose proof m_big'; lia.
                        + apply m_small'.
        Qed.

        Definition valid' x := @WordByWordMontgomery.small bw n x /\ eval x = eval x mod m.

        Structure mont_enc : Set := enc_mont { val : (list Z) ; Hvalid : valid' val }.

        Lemma valid_valid'_equiv : forall x, valid x <-> valid' x.
        Proof.
                unfold valid'; split; intros H.
                - split; unfold valid in H; destruct H; auto; rewrite Zmod_small; auto.
                - destruct H; split; auto; rewrite H0; apply Z_mod_lt; pose proof m_big; lia.
        Qed.

        Lemma valid_mod {x : list Z} : valid x -> eval (from_mont x) mod m = eval (from_mont x).
        Proof.
        intros. assert (H0 : valid (from_mont x)) by (apply from_mont_correct; auto).
        apply valid_valid'_equiv in H0.
        destruct H0 as [_ H1]. auto. 
        Qed.

        Lemma valid'_mod {x : list Z} : valid' x -> eval (from_mont x) mod m = eval (from_mont x).
        Proof.
        intros. apply valid_valid'_equiv in H. apply valid_mod. auto.
        Qed.

        Lemma valid_mod' {x : list Z} : valid x -> (eval x mod m) = eval x.
        Proof. 
                intros H. apply valid_valid'_equiv in H. destruct H. auto.
        Qed.

        Lemma valid'_mod' {x : list Z} : valid' x -> (eval x mod m) = eval x.
        Proof. intros [_ H]; auto. Qed.

        Lemma mont_enc_val : forall x H, val (enc_mont x H) = x.
        Proof. reflexivity. Qed.

        Lemma mont_enc_irr : forall (x y : mont_enc), val x = val y -> x = y.
        Proof.
                intros [x [Hx1 Hx2]] [y [Hy1 Hy2]] H. simpl in H. subst x.
                rewrite (fun H => eq_proofs_unicity H Hx1 Hy1).
                1: rewrite (fun H => eq_proofs_unicity H Hx2 Hy2); auto.
                1: apply Z.eq_decidable.
                pose proof (@list_eq_dec Z) as H. pose proof Z.eq_decidable as H0.
                unfold Decidable.decidable in H0.
                intros x y0.
                assert (forall x y : Z, {x = y} + {x <> y}) as H1.
                {
                intros. destruct (x0 =? y1) eqn:eq.
                - apply Z.eqb_eq in eq. left. auto.
                - apply Z.eqb_neq in eq. right; auto. 
                }
                remember (H H1) as H2.
                remember (H2 x y0) as H3.
                destruct H3; auto.
        Qed.

        Lemma eval_inj_list : forall x y, valid x -> valid y -> eval x = eval y -> x = y.
        Proof.
                intros x y [Hx1 Hx2] [Hy1 Hy2] H. unfold WordByWordMontgomery.small in *.
                rewrite Hx1, Hy1. rewrite H. auto.
        Qed.

        Lemma eval_inj : forall x y, eval (val x) = eval (val y) -> x = y.
        Proof.
                intros [x Hx] [y Hy] H. simpl in H. apply mont_enc_irr. simpl.
                destruct Hx as [H0 H1]. destruct Hy as [H2 H3]. unfold WordByWordMontgomery.small in *.
                rewrite H0. rewrite H2. unfold eval.
                unfold WordByWordMontgomery.eval in H.
                rewrite H. reflexivity.
        Qed.

        Lemma eval_from_mont_inj : forall x y , eval (from_mont (val x)) = eval (from_mont (val y)) -> x = y.
        Proof.
                intros [x Hx] [y Hy] H. apply eval_inj_list in H.
                2, 3:   rewrite mont_enc_val;
                        pose proof from_mont_correct as Htemp;
                        apply Htemp; apply valid_valid'_equiv; auto.

                rewrite !mont_enc_val in H. apply mont_enc_irr.
                rewrite !mont_enc_val. apply eval_inj_list; [apply valid_valid'_equiv; auto|apply valid_valid'_equiv; auto|].
                apply (f_equal (fun z => eval z)) in H.
                destruct (from_mont_correct x) as [H0 H1]; [apply valid_valid'_equiv; auto| ].
                destruct (from_mont_correct y) as [H2 H3]; [apply valid_valid'_equiv; auto| ].
                rewrite Zmod_small in H0; [| destruct H1; assumption].
                rewrite Zmod_small in H2; [| destruct H3; assumption].
                rewrite H in H0.
                apply (f_equal (fun y => y * (2^ bw) ^ Z.of_nat n mod m)) in H0.
                pose proof r'_correct as H4.
                eassert (Hx' : forall x, ((eval x * r' ^ Z.of_nat n) mod m * ((2 ^ bw) ^ Z.of_nat n)) mod m = _).
                {
                        intros. assert ((eval x0 * r' ^ Z.of_nat n) mod m * (2 ^ bw) ^ Z.of_nat n mod m = (eval x0 * (r' * 2 ^ bw mod m)^ Z.of_nat n) mod m) as H5.
                        {
                                push_Zmod; pull_Zmod; rewrite Z.pow_mul_l; rewrite Z.mul_assoc; reflexivity.
                        }
                        rewrite H5. pose proof r'_correct. rewrite Z.mul_comm in H6; unfold r in H6; rewrite H6.
                        rewrite (Z.pow_1_l); [| pose proof n_nz; lia]; rewrite Z.mul_1_r. reflexivity.
                }
                rewrite Hx' in H0.
                apply (f_equal (fun y => y * (2^ bw) ^ Z.of_nat n mod m)) in H2.
                rewrite Hx' in H2.
                pose proof (Zmod_small (eval x) m); rewrite H5 in H0; [| apply valid_valid'_equiv in Hx; destruct Hx; auto].
                pose proof (Zmod_small (eval y) m); rewrite H6 in H2; [| apply valid_valid'_equiv in Hy; destruct Hy; auto].
                rewrite <- H0, H2; reflexivity.
        Qed.

        Lemma valid_zeros : valid (Positional.zeros n).
        Proof.
                apply valid_valid'_equiv. split.
                - unfold WordByWordMontgomery.small.
                unfold eval.
                rewrite Positional.eval_zeros. rewrite partition_0. reflexivity.
                - unfold eval. rewrite Positional.eval_zeros. auto with zarith.
        Qed.

        Lemma valid_to_mont : forall x, valid x -> valid (WordByWordMontgomery.to_montgomerymod bw n m m' x).
        Proof. apply to_mont_correct. Qed.

        Lemma valid_from_mont : forall x, valid x -> valid (from_mont x).
        Proof. apply from_mont_correct. Qed.

        Lemma valid_from_to_mont : forall x, valid x -> (valid (from_mont (WordByWordMontgomery.to_montgomerymod bw n m m' x))).
        Proof. intros; apply valid_from_mont; apply valid_to_mont; auto. Qed.

        Lemma eval_from_mont_mod_inj : forall x y , eval (from_mont (val x)) mod m = eval (from_mont (val y)) mod m -> x = y.
        Proof.
                intros x y H. rewrite Zmod_small in H.
                2: {
                assert (H0 : valid (val x)) by (destruct x; rewrite mont_enc_val; apply valid_valid'_equiv; auto).
                apply valid_from_mont in H0. destruct H0; auto.
                }
                rewrite Zmod_small in H.
                2: {
                assert (H0 : valid (val y)) by (destruct y; rewrite mont_enc_val; apply valid_valid'_equiv; auto).
                apply valid_from_mont in H0. destruct H0; auto. 
                }
                apply eval_from_mont_inj. auto.
        Qed.  

        Program Definition F_to_mont x : mont_enc := enc_mont (Partition.partition uw n (GZnZ.val m x)) _.
        Next Obligation.
        Proof.
                apply valid_valid'_equiv. apply valid_partition_small. destruct x; auto.
        Defined.

        Lemma val_small : forall x : mont_enc, eval (val x) = eval (val x) mod m.
        Proof.
                intros [x [xvalid1 xvalid2]]; auto with zarith.
        Qed.

        Definition mont_to_F (x : mont_enc) : (GZnZ.znz m) := (GZnZ.mkznz m (eval (val x)) (val_small x)).

        Lemma mont_to_F_inverse : forall x, mont_to_F (F_to_mont x) = x.
        Proof.
                intros [x xmod]. apply GZnZ.zirr. unfold WordByWordMontgomery.eval. simpl.
                rewrite eval_partition; [| apply uwprops, bw_big].
                apply Zmod_small.
                pose proof m_small'.
                assert (mbig' : m > 0) by (pose proof m_big'; lia).
                pose proof (Z_mod_lt x m mbig'). lia.
        Qed.

        Lemma F_to_mont_inverse : forall x, F_to_mont (mont_to_F x) = x.
        Proof.
                intros [x xvalid]. apply mont_enc_irr. simpl. destruct xvalid. auto.
        Qed.

        Program Definition mont_mul (x y : mont_enc) : mont_enc := enc_mont (wbw_mul (val x) (val y)) _.
        Next Obligation.
        Proof.
                apply valid_valid'_equiv; destruct x, y; apply mul_mod_correct; apply valid_valid'_equiv; auto.
        Defined.

        Program Definition mont_add (x y : mont_enc) : mont_enc := enc_mont (wbw_add (val x) (val y)) _.
        Next Obligation.
        Proof.
                apply valid_valid'_equiv; destruct x, y; apply add_mod_correct; apply valid_valid'_equiv; auto.
        Defined.

        Program Definition mont_sub (x y : mont_enc) : mont_enc := enc_mont (wbw_sub (val x) (val y)) _.
        Next Obligation.
        Proof.
                apply valid_valid'_equiv; destruct x, y; apply sub_mod_correct; apply valid_valid'_equiv; auto.
        Defined.

        Program Definition mont_opp (x : mont_enc) : mont_enc := enc_mont (WordByWordMontgomery.oppmod bw n m (val x)) _.
        Next Obligation.
        Proof.
                apply valid_valid'_equiv; destruct x; apply opp_mod_correct; apply valid_valid'_equiv; auto.
        Defined.

        Program Definition mont_zero : mont_enc := enc_mont (WordByWordMontgomery.to_montgomerymod bw n m m' (Positional.zeros n)) _.
        Next Obligation.
        Proof.
                apply valid_valid'_equiv. destruct to_mont_correct as [_ H0].
                apply H0. apply valid_zeros.
        Defined.

        Program Definition Z_to_mont x : mont_enc := enc_mont (WordByWordMontgomery.encodemod bw n m m' (x mod m)) _.
        Next Obligation.
        Proof.
                apply valid_valid'_equiv.
                unfold WordByWordMontgomery.encodemod.
                destruct (to_mont_correct) as [_ H]. apply H.
                apply valid_partition_small. rewrite Zmod_mod; auto.
        Defined.

        Program Definition mont_one := Z_to_mont 1.

        Lemma valid'_length : forall x, valid' x -> length x = n.
        Proof.
                intros. apply valid_valid'_equiv in H. destruct H. 
                apply (@WordByWordMontgomery.length_small bw). auto.
        Qed.

        Lemma eval_frommont_montzero: eval (from_mont (val mont_zero)) = 0.
        Proof.
                unfold mont_zero. rewrite mont_enc_val.
                destruct (to_mont_correct) as [H H0].
                pose proof (H0 (Positional.zeros n) valid_zeros). apply valid_mod in H1. rewrite <- H1.
                rewrite H; [unfold eval; rewrite <- (partition_0 uw); rewrite eval_partition; [auto with zarith| apply uwprops, bw_big]| apply valid_zeros].
        Qed.

        (*Proving ring properties of mont_enc*)
        Lemma mont_add_0 : forall x : mont_enc, mont_add mont_zero x = x.
        Proof.
                intros [x Hx]. apply eval_from_mont_inj.
                unfold mont_add.
                assert (H : valid (val mont_zero)) by apply valid_valid'_equiv, (Hvalid mont_zero).
                assert (H0 : valid x) by (apply valid_valid'_equiv; auto).
                destruct (add_mod_correct).
                repeat rewrite mont_enc_val.
                pose proof (H2 (val mont_zero) H x H0). apply valid_mod in H3. rewrite H1 in H3; [| auto| auto].
                rewrite eval_frommont_montzero in H3. rewrite Z.add_0_l in H3. rewrite <- H3.
                apply valid_mod; auto.
        Qed.

        Lemma valid'_valid : forall x, valid' x -> valid x.
        Proof. apply valid_valid'_equiv. Qed.

        Lemma mont_add_comm : forall x y : mont_enc, mont_add x y = mont_add y x.
        Proof.
                intros.
                assert (Hx : valid (val x)) by (destruct x; apply valid'_valid; auto).
                assert (Hy : valid (val y)) by (destruct y; apply valid'_valid; auto).
                unfold mont_add. apply eval_from_mont_mod_inj. rewrite !mont_enc_val.
                destruct add_mod_correct. rewrite !H; auto. rewrite Z.add_comm. auto.
        Qed.

        (*move these lemmas*)
        Lemma evfrom_mod : forall x, evfrom (val x) = (evfrom (val x)) mod m.
        Proof.
                intros [x Hx]; simpl; apply valid_valid'_equiv in Hx;
                destruct (from_mont_correct x Hx) as [_ H'];
                apply valid_valid'_equiv in H'; apply H'.
        Qed.

        Lemma evfrom_mod' : forall x, valid x -> evfrom x = evfrom x mod m.
        Proof.
                intros; apply valid_valid'_equiv, from_mont_correct; auto.
        Qed.

        Lemma mont_add_spec_mod : forall x y, evfrom (val (mont_add x y)) mod m = (evfrom (val x) + evfrom (val y)) mod m.
        Proof.
                intros [x Hx] [y Hy]. apply add_mod_correct; (apply valid_valid'_equiv; auto).
        Qed.

        Lemma mont_sub_spec_mod : forall x y, evfrom (val (mont_sub x y)) mod m = (evfrom (val x) - evfrom (val y)) mod m.
        Proof.
                intros [x Hx] [y Hy]. apply sub_mod_correct; (apply valid_valid'_equiv; auto).
        Qed.

        Lemma mont_mul_spec_mod : forall x y, evfrom (val (mont_mul x y)) mod m = (evfrom (val x) * evfrom (val y)) mod m.
        Proof.
                intros [x Hx] [y Hy]. apply mul_mod_correct; (apply valid_valid'_equiv; auto).
        Qed.

        Lemma mont_opp_spec_mod : forall x, evfrom (val (mont_opp x)) mod m = (- evfrom (val x)) mod m.
        Proof.
                intros [x Hx]. apply opp_mod_correct; (apply valid_valid'_equiv; auto).
        Qed.

        Lemma mont_enc_valid':  forall (x : mont_enc), valid' (val x).
        Proof. intros [x H]; auto. Qed.

        Lemma mont_add_spec : forall x y, evfrom (val (mont_add x y))= (evfrom (val x) + evfrom (val y)) mod m.
        Proof.
                intros x y.
                pose proof (mont_enc_valid' (mont_add x y)) as H.
                apply valid_valid'_equiv in H.
                apply from_mont_correct in H. destruct H as [_ H].
                apply valid_valid'_equiv in H. destruct H as [_ Hmod].
                rewrite Hmod. apply mont_add_spec_mod.
        Qed.

        Lemma mont_sub_spec : forall x y, evfrom (val (mont_sub x y))= (evfrom (val x) - evfrom (val y)) mod m.
        Proof.
                intros x y.
                pose proof (mont_enc_valid' (mont_sub x y)) as H.
                apply valid_valid'_equiv in H.
                apply from_mont_correct in H. destruct H as [_ H].
                apply valid_valid'_equiv in H. destruct H as [_ Hmod].
                rewrite Hmod; apply mont_sub_spec_mod.
        Qed.

        Lemma mont_mul_spec : forall x y, evfrom (val (mont_mul x y))= (evfrom (val x) * evfrom (val y)) mod m.
        Proof.
                intros x y.
                pose proof (mont_enc_valid' (mont_mul x y)) as H.
                apply valid_valid'_equiv in H.
                apply from_mont_correct in H. destruct H as [_ H].
                apply valid_valid'_equiv in H. destruct H as [_ Hmod].
                rewrite Hmod; apply mont_mul_spec_mod.
        Qed.

        Lemma mont_opp_spec : forall x, evfrom (val (mont_opp x))= (- evfrom (val x)) mod m.
        Proof.
                intros x.
                pose proof (mont_enc_valid' (mont_opp x)) as H.
                apply valid_valid'_equiv in H.
                apply from_mont_correct in H. destruct H as [_ H].
                apply valid_valid'_equiv in H. destruct H as [_ Hmod].
                rewrite Hmod; apply mont_opp_spec_mod.
        Qed.

        Lemma mont_add_assoc : forall x y z : mont_enc, mont_add x (mont_add y z) = mont_add (mont_add x y) z.
        Proof.
                intros.
                assert (Hx : valid (val x)) by (destruct x; apply valid'_valid; auto).
                assert (Hy : valid (val y)) by (destruct y; apply valid'_valid; auto).
                assert (Hz : valid (val z)) by (destruct z; apply valid'_valid; auto).
                unfold mont_add. apply eval_from_mont_mod_inj. rewrite !mont_enc_val.
                destruct add_mod_correct. rewrite !H; auto.
                rewrite Z.add_mod; [|pose proof m_big; lia].
                rewrite !H; auto.
                symmetry.
                rewrite Z.add_mod; [|pose proof m_big; lia].
                rewrite !H; auto.
                pull_Zmod. auto with zarith.
        Qed.

        Lemma mont_enc_proj : forall x y, x = y -> val x = val y.
        Proof. intros x y H; rewrite H; auto. Qed.

        Lemma from_to_mont_inv : forall x, valid x -> from_mont (to_mont x) = x.
        Proof.
                intros x H.
                assert (H0 :  valid' x) by (apply valid_valid'_equiv; auto).
                pose (enc_mont x H0).
                destruct (to_mont_correct) as [H' H1].
                pose proof (H1 x H).
                destruct (from_mont_correct (to_mont x) H2).
                apply valid_valid'_equiv in H4.
                pose (enc_mont (from_mont (to_mont x)) H4).
                assert (m0 = m1).
                {
                        subst m0. subst m1.
                        apply eval_inj.
                        repeat rewrite !mont_enc_val. apply valid_mod in H2. rewrite <- H2.
                        rewrite H'; auto. rewrite Zmod_small; auto. unfold valid in *; lia.
                }
                apply mont_enc_proj in H5. subst m0 m1. rewrite !mont_enc_val in H5. auto.
        Qed.

        Lemma eval_from_mont_one : eval (from_mont (val mont_one)) = 1.
        Proof.
                unfold mont_one.
                unfold Z_to_mont. unfold WordByWordMontgomery.encodemod. rewrite mont_enc_val.
                rewrite from_to_mont_inv.
                        - unfold eval. rewrite eval_partition.
                                + rewrite !Zmod_1_l; auto.
                                pose proof m_small'. pose proof m_big. unfold uw in H. lia.
                                + apply uwprops, bw_big.
                        - apply valid_partition_small. rewrite Zmod_mod. auto.
        Qed.       

        Lemma mont_mul_one : forall x : mont_enc, mont_mul mont_one x = x.
        Proof.
                intros [x H]. apply eval_from_mont_mod_inj. unfold mont_mul. rewrite !mont_enc_val.
                destruct mul_mod_correct. rewrite H0; auto.
                - rewrite eval_from_mont_one. rewrite (Z.mul_1_l). reflexivity.
                - apply valid_valid'_equiv, (Hvalid mont_one).
                - apply valid_valid'_equiv; auto.
        Qed.

        Lemma mont_mul_comm : forall x y : mont_enc, mont_mul x y = mont_mul y x.
        Proof.
                intros.
                assert (Hx : valid (val x)) by (destruct x; apply valid'_valid; auto).
                assert (Hy : valid (val y)) by (destruct y; apply valid'_valid; auto).
                unfold mont_mul. apply eval_from_mont_mod_inj. rewrite !mont_enc_val.
                destruct mul_mod_correct. rewrite !H; auto.
                rewrite Z.mul_comm; auto.
        Qed.

        Lemma mont_mul_assoc : forall x y z : mont_enc, mont_mul x (mont_mul y z) = mont_mul (mont_mul x y) z.
        Proof.
                intros.
                assert (Hx : valid (val x)) by (destruct x; apply valid'_valid; auto).
                assert (Hy : valid (val y)) by (destruct y; apply valid'_valid; auto).
                assert (Hz : valid (val z)) by (destruct z; apply valid'_valid; auto).
                unfold mont_mul. apply eval_from_mont_mod_inj. rewrite !mont_enc_val.
                destruct mul_mod_correct.
                rewrite !H; auto.
                rewrite Z.mul_mod; [| pose proof m_big; lia].
                rewrite !H; auto.
                symmetry.
                rewrite Z.mul_mod; [| pose proof m_big; lia].
                rewrite !H; auto.
                pull_Zmod. auto with zarith.
        Qed.

        Lemma mont_mul_distr : forall x y z : mont_enc, mont_mul (mont_add x y) z = mont_add (mont_mul x z) (mont_mul y z).
        Proof.
                intros.
                assert (Hx : valid (val x)) by (destruct x; apply valid'_valid; auto).
                assert (Hy : valid (val y)) by (destruct y; apply valid'_valid; auto).
                assert (Hz : valid (val z)) by (destruct z; apply valid'_valid; auto).
                unfold mont_mul. unfold mont_add. apply eval_from_mont_mod_inj. rewrite !mont_enc_val.
                destruct mul_mod_correct.
                destruct add_mod_correct.
                rewrite H; auto. rewrite H1; auto.
                rewrite Z.add_mod, Z.mul_mod; [| pose proof m_big; lia| pose proof m_big; lia].
                rewrite !H, H1; auto. pull_Zmod. auto with zarith.
        Qed.

        Lemma mont_opp_sub : forall x y : mont_enc, mont_sub x y = mont_add x (mont_opp y).
        Proof.
                intros.
                assert (Hx : valid (val x)) by (destruct x; apply valid'_valid; auto).
                assert (Hy : valid (val y)) by (destruct y; apply valid'_valid; auto).
                unfold mont_sub, mont_add, mont_opp. apply eval_from_mont_mod_inj. rewrite !mont_enc_val.
                destruct sub_mod_correct. rewrite H; auto.
                destruct opp_mod_correct.
                destruct add_mod_correct. rewrite H3; auto.
                rewrite Z.add_mod; [| pose proof m_big; lia].
                rewrite H1; auto.
                pull_Zmod. auto with zarith.
        Qed.

        Lemma mont_add_opp : forall x : mont_enc, mont_add x (mont_opp x) = mont_zero.
        Proof.
                intros.
                assert (Hx : valid (val x)) by (destruct x; apply valid'_valid; auto).
                unfold mont_add, mont_opp, mont_zero. apply eval_from_mont_mod_inj. rewrite !mont_enc_val.
                destruct opp_mod_correct, add_mod_correct.
                rewrite H1; auto.
                rewrite Z.add_mod; [| pose proof m_big; lia].
                rewrite H; auto.
                pose proof eval_frommont_montzero. unfold mont_zero in H3. rewrite mont_enc_val in H3. rewrite H3.
                pull_Zmod. auto with zarith.
        Qed.

        Theorem mont_enc_ring : ring_theory mont_zero mont_one mont_add mont_mul mont_sub mont_opp (@eq mont_enc).
                Proof.
                split;
                [ 
                apply mont_add_0
                | apply mont_add_comm
                | apply mont_add_assoc
                | apply mont_mul_one
                | apply mont_mul_comm
                | apply mont_mul_assoc
                | apply mont_mul_distr
                | apply mont_opp_sub
                | apply mont_add_opp
                ].
                Qed.

        Add Ring mont : (mont_enc_ring).
                
        Lemma eval_from_mont_Z_to_mont : forall x, eval (from_mont (val (Z_to_mont x))) = x mod m.
        Proof.
                intros x. unfold Z_to_mont. simpl.
                unfold WordByWordMontgomery.encodemod.
                destruct to_mont_correct.
                assert (H' : valid (to_mont (Partition.partition uw n (x mod m))))by (apply to_mont_correct, valid_partition_small; symmetry; apply Zmod_mod).
                destruct (from_mont_correct _ H') as [_ H1].
                apply valid_valid'_equiv in H1. destruct H1.
                assert (uw = uweight bw) by auto. rewrite <- H3.
                rewrite H2.
                rewrite H.
                        - unfold eval. rewrite eval_partition; [| apply uwprops; pose proof bw_big; lia].
                                eassert ( (x mod m) mod uw n = _).
                                {
                                rewrite Zmod_mod_small.
                                2: pose proof m_big; lia.
                                2: apply m_small'.
                                reflexivity.      
                                }
                                rewrite H4. rewrite Zmod_mod. auto.
                        - apply valid_partition_small; symmetry; apply Zmod_mod.
        Qed.

(*Now, take care of field extensions :D *)

        Local Notation "1mont" := mont_one.
        Local Notation "0mont" := mont_zero.
        Local Infix "*m" := mont_mul (at level 80).
        Local Infix "+m" := mont_add (at level 70).
        Local Infix "-m" := mont_sub (at level 70).

        Definition montFp2 : Type := (mont_enc * mont_enc).
        Definition montFp2_zero := (mont_zero, mont_zero).
        Definition montFp2_one := (mont_one, mont_zero).
        Definition montFp2_add x y := ((fst x) +m (fst y), (snd x) +m (snd y)).
        Definition montFp2_sub x y := ((fst x) -m (fst y), (snd x) -m (snd y)).
        Definition montFp2_mul x y := ((((fst x) *m (fst y)) -m ((snd x) *m (snd y))), (((fst x) *m (snd y)) +m ((snd x) *m (fst y)))).
        Definition montFp2_opp x := (mont_opp (fst x), mont_opp (snd x)).

        Theorem montFp2_ring : ring_theory montFp2_zero montFp2_one montFp2_add montFp2_mul montFp2_sub montFp2_opp (@eq montFp2).
        Proof.
        split; intros [x1 x2]; try intros [y1 y2]; try intros [z1 z2]; try unfold montFp2_add;
        try unfold montFp2_mul; try unfold montFp2_sub; try unfold montFp2_opp; apply pair_equal_spec; split; (simpl; ring).
        Qed.

        Definition enc_mont_pair x (H : valid' (fst x) /\ valid' (snd x)) : (mont_enc * mont_enc) := (enc_mont (fst x) (proj1 H), enc_mont (snd x) (proj2 H)).

        Theorem montFp2_ring' : ring_theory montFp2_zero montFp2_one montFp2_add montFp2_mul montFp2_sub montFp2_opp (@eq (mont_enc * mont_enc)).
        Proof. apply montFp2_ring. Qed.
        (*Technical Lemmas*)

        Lemma add_val x y : val (x +m y) = wbw_add (val x) (val y).
        Proof. reflexivity. Qed.

        Lemma mul_val x y : val (x *m y) = wbw_mul (val x) (val y).
        Proof. reflexivity. Qed.

        Lemma sub_val x y : val (x -m y) = wbw_sub (val x) (val y).
        Proof. reflexivity. Qed.

        Lemma evfrom_val_add x y : eval (from_mont (val (x +m y))) = ((eval (from_mont (val x))) + (eval (from_mont (val y)))) mod m.
        Proof.
                destruct x as [x Hx], y as [y Hy]. simpl. destruct add_mod_correct. rewrite <- H.
                2, 3: apply valid_valid'_equiv; auto.
                apply valid_valid'_equiv in Hx, Hy.
                remember (H0 x Hx y Hy) as H1.
                eassert (valid' _).
                {
                        apply valid_valid'_equiv. apply H1.
                }
                destruct (from_mont_correct _ H1) as [_ H4]. apply valid_valid'_equiv in H4. destruct H4 as [_ H4].
                rewrite H4. auto with zarith.
        Qed.

        Lemma evfrom_val_mul x y : eval (from_mont (val (x *m y))) = ((eval (from_mont (val x))) * (eval (from_mont (val y)))) mod m.
        Proof.
                destruct x as [x Hx], y as [y Hy]. simpl. destruct mul_mod_correct. rewrite <- H.
                2, 3: apply valid_valid'_equiv; auto.
                apply valid_valid'_equiv in Hx, Hy.
                remember (H0 x Hx y Hy) as H1.
                eassert (valid' _).
                {
                        apply valid_valid'_equiv. apply H1.
                }
                destruct (from_mont_correct _ H1) as [_ H4]. apply valid_valid'_equiv in H4. destruct H4 as [_ H4].
                rewrite H4. auto with zarith.
        Qed.

        Lemma evfrom_val_sub x y : eval (from_mont (val (x -m y))) = ((eval (from_mont (val x))) - (eval (from_mont (val y)))) mod m.
        Proof.
                destruct x as [x Hx], y as [y Hy]. simpl. destruct sub_mod_correct. rewrite <- H.
                2, 3: apply valid_valid'_equiv; auto.
                apply valid_valid'_equiv in Hx, Hy.
                remember (H0 x Hx y Hy) as H1.
                eassert (valid' _).
                {
                        apply valid_valid'_equiv. apply H1.
                }
                destruct (from_mont_correct _ H1) as [_ H4]. apply valid_valid'_equiv in H4. destruct H4 as [_ H4].
                rewrite H4. auto with zarith.
        Qed.

        Lemma evfrom_val_addFp2 x y : eval (from_mont (val (fst (montFp2_add x y)))) = (eval (from_mont (val (fst x))) + eval (from_mont (val (fst y)))) mod m
                /\ eval (from_mont (val (snd (montFp2_add x y)))) = (eval (from_mont (val (snd x))) + eval (from_mont (val (snd y)))) mod m.
        Proof.
                split; apply evfrom_val_add.
        Qed.

        Lemma evfrom_val_subFp2 x y : eval (from_mont (val (fst (montFp2_sub x y)))) = (eval (from_mont (val (fst x))) - eval (from_mont (val (fst y)))) mod m
                /\ eval (from_mont (val (snd (montFp2_sub x y)))) = (eval (from_mont (val (snd x))) - eval (from_mont (val (snd y)))) mod m.
        Proof.
                split; apply evfrom_val_sub.
        Qed.

        Lemma evfrom_val_mulFp2 x y : eval (from_mont (val (fst (montFp2_mul x y)))) = ((eval (from_mont (val (fst x))) * (eval (from_mont (val (fst y)))) ) - (eval (from_mont (val (snd x))) * (eval (from_mont (val (snd y)))))) mod m
        /\ eval (from_mont (val (snd (montFp2_mul x y)))) = ((eval (from_mont (val (fst x))) * (eval (from_mont (val (snd y)))) ) + (eval (from_mont (val (snd x))) * (eval (from_mont (val (fst y)))))) mod m.
        Proof.
                destruct x as [xr xi], y as [yr yi].
                split; unfold montFp2_mul; simpl; rewrite <- !mul_val; [rewrite <- sub_val; rewrite evfrom_val_sub| rewrite <- add_val; rewrite evfrom_val_add];
                rewrite !evfrom_val_mul; pull_Zmod; reflexivity.
        Qed.

End wbw_ring.
