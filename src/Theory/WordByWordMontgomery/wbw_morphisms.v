Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Require Import Rewriter.Util.Bool.
Require Import ArithRing Ring.
Open Scope Z_scope.

(*We define ring morphisms between Zp and valid encodings of such elements in Montgomery form.*)
Section Rings.
  Context (m_ : Z)
          (* (m_prime : Znumtheory.prime p) *)
          (bw : Z)
          (n : nat)
          (r' : Z)
          (m' : Z).
  Definition m := m_.
  
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


  Notation mont_enc := (MontgomeryRingTheory.mont_enc m bw n).
  Notation Z_to_mont := (@MontgomeryRingTheory.Z_to_mont m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation val := (@MontgomeryRingTheory.val  m bw n).
  Notation mont_zero := (@MontgomeryRingTheory.mont_zero m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation mont_one := (@MontgomeryRingTheory.mont_one m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation mont_add := (@MontgomeryRingTheory.mont_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation mont_mul := (@MontgomeryRingTheory.mont_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation mont_sub := (@MontgomeryRingTheory.mont_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation mont_opp := (@MontgomeryRingTheory.mont_opp m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation eval_from_mont_inj := (@MontgomeryRingTheory.eval_from_mont_inj  m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation eval := (@WordByWordMontgomery.eval bw n).
  Notation valid := (@WordByWordMontgomery.valid bw n m).
  Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Notation evfrom x := (eval (from_mont x)).
  Notation evfrom_mod := (@MontgomeryRingTheory.evfrom_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).

  Notation F := (GZnZ.znz m).

  Definition Fzero := (GZnZ.zero m).
  Definition Fone := (GZnZ.one m).
  Definition Fadd := (GZnZ.add m).
  Definition Fmul := (GZnZ.mul m).
  Definition Fsub := (GZnZ.sub m).
  Definition Fopp := (GZnZ.opp m).

  Definition phi (x : F) : mont_enc := Z_to_mont (GZnZ.val m x).
  
  Definition mont_eqb x y:= ListUtil.list_beq Z (Z.eqb) (val x) (val y).
  
  Lemma mont_eqb_eq : forall x y, mont_eqb x y = true <-> x = y.
  Proof.
          intros x y; split; intros H.
                  - unfold mont_eqb in H.
                    assert (Hdec : (forall x y : Z, (x =? y) = true -> x = y)) by apply Z.eqb_eq.
                    pose proof (ListUtil.internal_list_dec_bl Z (Z.eqb) Hdec) as H0; simpl in H0.
                    apply mont_enc_irr; apply H0; auto.
          - rewrite H; unfold mont_eqb; apply ListUtil.internal_list_dec_lb.
                  + apply Z.eqb_eq.
                  + auto.
  Qed.

  Definition Fp_eqb (x y : F) := Z.eqb (GZnZ.val m x) (GZnZ.val m y).

  Lemma phi_morph : ring_morph mont_zero mont_one mont_add mont_mul mont_sub mont_opp (@eq mont_enc)
  Fzero Fone Fadd Fmul Fsub Fopp Fp_eqb phi.
  Proof.
          split; unfold phi, Fzero, Fone, Fadd, Fmul, Fsub, Fopp.
                  - cbv [GZnZ.zero GZnZ.val]. rewrite Zmod_0_l.
                    apply eval_from_mont_inj. rewrite eval_frommont_montzero.
                    pose proof eval_from_mont_Z_to_mont. rewrite H. auto with zarith.
                  - cbv [GZnZ.one GZnZ.val]. rewrite Zmod_small; [| pose proof m_big; lia].
                    apply eval_from_mont_inj. rewrite eval_from_mont_one. rewrite eval_from_mont_Z_to_mont.
                    apply Zmod_small. pose proof m_big. lia.
                  - intros. apply eval_from_mont_inj. rewrite eval_from_mont_Z_to_mont.
                    rewrite mont_add_spec. rewrite !eval_from_mont_Z_to_mont.
                    cbv [GZnZ.add]. simpl. rewrite Zmod_mod.
                    rewrite <- PullPush.Z.add_mod_full. auto. 
                  - intros. apply eval_from_mont_inj. rewrite eval_from_mont_Z_to_mont.
                    rewrite mont_sub_spec. rewrite !eval_from_mont_Z_to_mont.
                    cbv [GZnZ.sub]. simpl. rewrite Zmod_mod.
                    rewrite <- PullPush.Z.sub_mod_full. auto.
                  - intros. apply eval_from_mont_inj. rewrite eval_from_mont_Z_to_mont.
                    rewrite mont_mul_spec. rewrite !eval_from_mont_Z_to_mont.
                    cbv [GZnZ.mul]. simpl. rewrite Zmod_mod.
                    rewrite <- PullPush.Z.mul_mod_full. auto.
                  - intros. apply eval_from_mont_inj. rewrite eval_from_mont_Z_to_mont.
                    rewrite mont_opp_spec. rewrite !eval_from_mont_Z_to_mont.
                    cbv [GZnZ.opp]. simpl. rewrite Zmod_mod.
                    rewrite PullPush.Z.opp_mod_mod. auto.
                  - intros. unfold Fp_eqb in H. apply Z.eqb_eq in H. rewrite H. auto.
  Qed.

  Definition psi x : (GZnZ.znz m) := GZnZ.mkznz m (evfrom (val x)) (evfrom_mod x).

  Lemma znz_val : forall x H, GZnZ.val m {|GZnZ.val := x; GZnZ.inZnZ := H|} = x.
  Proof. reflexivity. Qed.

  Lemma psi_morph : ring_morph (GZnZ.zero m) (GZnZ.one m) (GZnZ.add m) (GZnZ.mul m) (GZnZ.sub m) (GZnZ.opp m) (@eq (GZnZ.znz m))
  mont_zero mont_one mont_add mont_mul mont_sub mont_opp (mont_eqb) psi.
  Proof.
          split; intros; unfold psi; apply GZnZ.zirr; try rewrite !znz_val.
                  - rewrite eval_frommont_montzero. auto with zarith.
                  - rewrite eval_from_mont_one. rewrite Zmod_small; auto. pose proof m_big; lia.
                  - apply mont_add_spec.
                  - apply mont_sub_spec.
                  - apply mont_mul_spec.
                  - apply mont_opp_spec.
                  - apply mont_eqb_eq in H. rewrite H. auto.
  Qed.

  (*Field Extensions*)
  Notation montFp2_add := (MontgomeryRingTheory.montFp2_add  m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation montFp2_sub := (MontgomeryRingTheory.montFp2_sub  m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation montFp2_mul := (MontgomeryRingTheory.montFp2_mul  m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation montFp2_opp := (MontgomeryRingTheory.montFp2_opp  m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation montFp2 := (MontgomeryRingTheory.montFp2 m bw n).
  Notation montFp2_zero := (MontgomeryRingTheory.montFp2_zero  m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Notation montFp2_one := (MontgomeryRingTheory.montFp2_one  m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).

  Definition montFp2_eqb x y := andb (mont_eqb (fst x) (fst y)) (mont_eqb (snd x) (snd y)).
  
  Lemma montFp2_eqb_eq : forall x y, montFp2_eqb x y = true <-> x = y.
  Proof.
          split; intros.
          - destruct x, y; apply pair_equal_spec; (unfold montFp2_eqb in H;
            apply Rewriter.Util.Bool.andb_prop in H; simpl in H; destruct H;
            split; apply mont_eqb_eq; auto).
          - unfold montFp2_eqb. apply Rewriter.Util.Bool.andb_true_intro. split; (apply mont_eqb_eq; rewrite H; auto).
  Qed.

  Definition Fp2_eqb x y := andb (Z.eqb (GZnZ.val m (fst x)) (GZnZ.val m (fst y))) (Z.eqb (GZnZ.val m (snd x)) (GZnZ.val m (snd y))).  
  Definition phiFp2 x := (phi (fst x), phi (snd x)).

  Definition Fp2zero := (Fzero, Fzero).
  Definition Fp2one := (Fone, Fzero).
  Definition Fp2add x y := (Fadd (fst x) (fst y), Fadd (snd x) (snd y)).
  Definition Fp2mul x y := (Fsub (Fmul (fst x) (fst y)) (Fmul (snd x) (snd y)), Fadd (Fmul (fst x) (snd y)) (Fmul (snd x) (fst y))).
  Definition Fp2sub x y := (Fsub (fst x) (fst y), Fsub (snd x) (snd y)).
  Definition Fp2opp x := (Fopp (fst x), (Fopp (snd x))).

  Ltac push_by_morphism morph := repeat progress first
          [ rewrite (morph0 morph)
          | rewrite (morph1 morph) 
          | rewrite (morph_add morph)
          | rewrite (morph_sub morph)
          | rewrite (morph_mul morph)
          | rewrite (morph_opp morph)].

  Ltac push_to_mont := push_by_morphism phi_morph.
  Ltac push_to_F := push_by_morphism psi_morph.

  Lemma phiFp2_ring_morph : ring_morph 
  montFp2_zero montFp2_one montFp2_add montFp2_mul montFp2_sub montFp2_opp (@eq montFp2)
  Fp2zero Fp2one Fp2add Fp2mul Fp2sub Fp2opp Fp2_eqb phiFp2.
  Proof. destruct phi_morph.
          split; intros; apply pair_equal_spec; split; simpl; push_to_mont; auto.
                  - apply morph_eq. unfold Fp2_eqb in H. symmetry in H.
                    apply Bool.andb_true_eq in H. destruct H. auto.
                  - apply morph_eq. unfold Fp2_eqb in H. symmetry in H.
                    apply Bool.andb_true_eq in H. destruct H. auto.
  Qed.

  Definition psiFp2 x := (psi (fst x), psi (snd x)).

  Lemma psiFp2_ring_morph : ring_morph Fp2zero Fp2one Fp2add Fp2mul Fp2sub Fp2opp (@eq (F * F))
  montFp2_zero montFp2_one montFp2_add montFp2_mul montFp2_sub montFp2_opp montFp2_eqb psiFp2.
  Proof. destruct psi_morph.
          split; intros; apply pair_equal_spec; split; simpl; push_to_F; auto.
                  - apply morph_eq. unfold Fp2_eqb in H. symmetry in H.
                    apply Bool.andb_true_eq in H. destruct H. auto.
                  - apply morph_eq. unfold Fp2_eqb in H. symmetry in H.
                    apply Bool.andb_true_eq in H. destruct H. auto.
  Qed.

End Rings.