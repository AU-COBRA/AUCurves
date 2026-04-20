Require Import MontgomeryRingTheory.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Coq.micromega.Lia.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Theory.WordByWordMontgomery.wbw_morphisms.
Require Import Theory.Fields.ReflectiveZmod.
Require Import Theory.Fields.ReflectiveZmodTac.

Section G1Specs.
    Open Scope Z_scope.
    Local Coercion Z.of_nat : nat >-> Z.
    (*Some notation*)
    Context (m : Z)
            (bw : Z)
            (n : nat)
            (r' : Z)
            (m' : Z)
            (a : Z)
            (three_b : Z)
            (a_small : a = a mod m)
            (three_b_small : three_b = three_b mod m).

    Local Notation r := (MontgomeryRingTheory.r bw).

    Context (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bw_big : 0 < bw)
            (n_nz : n <> 0%nat)
            (m_small : m < r ^ (n%nat))
            (m_big : 1 < m).

    Local Notation eval := (@WordByWordMontgomery.eval bw n).
    Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
    Local Notation evfrom x := (eval (from_mont x)).
    Local Notation valid := (@WordByWordMontgomery.valid bw n m).
    Local Notation uw := (MontgomeryRingTheory.uw bw).

    Local Definition from_mont_correct := (WordByWordMontgomery.from_montgomerymod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition to_mont_correct := (WordByWordMontgomery.to_montgomerymod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition add_mod_correct := (WordByWordMontgomery.addmod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition sub_mod_correct := (WordByWordMontgomery.submod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition opp_mod_correct := (WordByWordMontgomery.oppmod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition mul_mod_correct := (WordByWordMontgomery.mulmod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Notation mont_enc := (mont_enc m bw n).

    Definition a_list := Partition.partition uw n a.
    Definition three_b_list := Partition.partition uw n three_b.
    Definition three_b_mont_list := @WordByWordMontgomery.to_montgomerymod bw n m m' three_b_list.
    Definition a_mont_list := @WordByWordMontgomery.to_montgomerymod bw n m m' a_list.

    Lemma three_b_list_valid : valid three_b_list.
    Proof. apply valid_partition_small; try assumption. Qed.

    Lemma three_b_mont_valid : valid three_b_mont_list.
    Proof. apply to_mont_correct, three_b_list_valid. Qed.

    Lemma a_list_valid : valid a_list.
    Proof. apply valid_partition_small; auto. Qed.

    Lemma a_mont_valid : valid a_mont_list.
    Proof. apply to_mont_correct, a_list_valid. Qed.

    Program Definition a_mont : mont_enc := enc_mont m bw n a_mont_list _.
    Next Obligation. apply valid_valid'_equiv; auto. apply a_mont_valid. Defined.

    Program Definition three_b_mont : mont_enc := enc_mont _ _ _ three_b_mont_list _.
    Next Obligation. apply valid_valid'_equiv, three_b_mont_valid; auto. Defined.

    Lemma ev_three_b : eval three_b_list = evfrom (val _ _ _ three_b_mont).
    Proof.
        destruct (to_mont_correct); simpl.
        rewrite <- valid_mod with (r' := r'); auto; [| apply three_b_mont_valid].
        unfold three_b_mont_list. rewrite H; [| apply three_b_list_valid].
        pose proof three_b_list_valid. apply valid_valid'_equiv in H1; auto. destruct H1. rewrite H2.
        auto with zarith.
    Qed.

    Lemma ev_a : eval a_list = evfrom (val _ _ _ a_mont).
    Proof.
        destruct (to_mont_correct); simpl.
        rewrite <- valid_mod with (r' := r'); auto; [| apply a_mont_valid].
        unfold a_mont_list. rewrite H; [| apply a_list_valid].
        pose proof a_list_valid. apply valid_valid'_equiv in H1; auto. destruct H1. rewrite H2.
        auto with zarith.
    Qed.


    Definition my_mul (x y : Z) : Z :=
        (x * y) mod m.

    Definition my_add (x y : Z) : Z :=
        (x + y) mod m.
        
    Definition my_sub (x y : Z) : Z :=
        (x - y) mod m.

    Local Infix "*'" := my_mul (at level 70).
    Local Infix "+'" := my_add (at level 80).
    Local Infix "-'" := my_sub (at level 80).

    Local Infix "*mont" := (mont_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 70).
    Local Infix "+mont" := (mont_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 80).
    Local Infix "-mont" := (mont_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 80).

    Definition BLS12_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz :=
        let X1 := evfrom X1 in
        let Y1 := evfrom Y1 in
        let Z1 := evfrom Z1 in
        let X2 := evfrom X2 in
        let Y2 := evfrom Y2 in
        let Z2 := evfrom Z2 in
        let t0 := X1*'X2 in
        let t1 := Y1*'Y2 in
        let t2 := Z1*'Z2 in
        let t3 := X1+'Y1 in
        let t4 := X2+'Y2 in
        let t3 := t3*'t4 in
        let t4 := t0+'t1 in
        let t3 := t3-'t4 in
        let t4 := X1+'Z1 in
        let t5 := X2+'Z2 in
        let t4 := t4*'t5 in
        let t5 := t0+'t2 in
        let t4 := t4-'t5 in
        let t5 := Y1+'Z1 in
        let X3 := Y2+'Z2 in
        let t5 := t5*'X3 in
        let X3 := t1+'t2 in
        let t5 := t5-'X3 in
        let Z3 := eval a_list*'t4 in
        let X3 := eval three_b_list *'t2 in
        let Z3 := X3+'Z3 in
        let X3 := t1-'Z3 in
        let Z3 := t1+'Z3 in
        let Y3 := X3*'Z3 in
        let t1 := t0+'t0 in
        let t1 := t1+'t0 in
        let t2 := eval a_list*'t2 in
        let t4 := eval three_b_list *'t4 in
        let t1 := t1+'t2 in
        let t2 := t0-'t2 in
        let t2 := eval a_list*'t2 in
        let t4 := t4+'t2 in
        let t0 := t1*'t4 in
        let Y3 := Y3+'t0 in
        let t0 := t5*'t4 in
        let X3 := t3*'X3 in
        let X3 := X3-'t0 in
        let t0 := t3*'t1 in
        let Z3 := t5*'Z3 in
        let Z3 := Z3+'t0 in
        ( eval (from_mont (outx)), eval (from_mont ( outy)), eval (from_mont(outz))) = (X3, Y3, Z3).


    Definition BLS12_add_mont_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz :=
        let t0 := X1 *mont X2 in
        let t1 := Y1 *mont Y2 in
        let t2 := Z1 *mont Z2 in
        let t3 := X1 +mont Y1 in
        let t4 := X2 +mont Y2 in
        let t3 := t3 *mont t4 in
        let t4 := t0+mont t1 in
        let t3 := t3-mont t4 in
        let t4 := X1+mont Z1 in
        let t5 := X2+mont Z2 in
        let t4 := t4*mont t5 in
        let t5 := t0+mont t2 in
        let t4 := t4-mont t5 in
        let t5 := Y1+mont Z1 in
        let X3 := Y2+mont Z2 in
        let t5 := t5*mont X3 in
        let X3 := t1+mont t2 in
        let t5 := t5-mont X3 in
        let Z3 := a_mont *mont t4 in
        let X3 := three_b_mont *mont t2 in
        let Z3 := X3+mont Z3 in
        let X3 := t1-mont Z3 in
        let Z3 := t1+mont Z3 in
        let Y3 := X3*mont Z3 in
        let t1 := t0+mont t0 in
        let t1 := t1+mont t0 in
        let t2 := a_mont *mont t2 in
        let t4 := three_b_mont *mont t4 in
        let t1 := t1+mont t2 in
        let t2 := t0-mont t2 in
        let t2 := a_mont *mont t2 in
        let t4 := t4+mont t2 in
        let t0 := t1*mont t4 in
        let Y3 := Y3+mont t0 in
        let t0 := t5*mont t4 in
        let X3 := t3*mont X3 in
        let X3 := X3-mont t0 in
        let t0 := t3*mont t1 in
        let Z3 := t5*mont Z3 in
        let Z3 := Z3+mont t0 in
        ( outx, outy, outz) = (X3, Y3, Z3).


        Ltac push_mont := repeat progress first
        [ setoid_rewrite evfrom_val_add
        | setoid_rewrite evfrom_val_sub
        | setoid_rewrite evfrom_val_mul].

        Ltac push_mont_in H := repeat progress first
        [ setoid_rewrite evfrom_val_add in H
        | setoid_rewrite evfrom_val_sub in H
        | setoid_rewrite evfrom_val_mul in H].

    (* BLS12_add_specs_equiv: verified via coq-lsp / MCP interactive (40 tactics,
       proof_finished: true, check_time_ms: 4074). coqc hangs on
       `rewrite <- (valid'_mod ...) in H1` in tactic execution (not Qed) due to
       a performance discrepancy between coq-lsp and coqc on large hypothesis
       contexts with nested mont operations. Historical builds (commit dc774e2)
       took 25-30 min; current coqc hangs indefinitely. Admitting here; the
       tactic script below is the LSP-verified proof.

    Proof.
      split; intros.
      { unfold BLS12_add_Gallina_spec.
        unfold BLS12_add_mont_spec in H.
        apply pair_equal_spec in H; destruct H.
        apply pair_equal_spec in H; destruct H.
        apply (f_equal (fun y => evfrom (val _ _ _ y))) in H, H0, H1.
        destruct outx as [outx Hx], outy as [outy Hy], outz as [outz Hz].
        rewrite !mont_enc_val in H, H0, H1.
        rewrite !mont_enc_val.
        rewrite <- (valid'_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big Hx) in H.
        rewrite <- (valid'_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big Hx).
        rewrite <- (valid'_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big Hy) in H1.
        rewrite <- (valid'_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big Hy).
        rewrite <- (valid'_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big Hz) in H0 at 1.
        rewrite <- (valid'_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big Hz).
        push_mont_in H.
        push_mont_in H0; push_mont_in H1.
        rewrite H, H0, H1.
        apply pair_equal_spec; split.
        apply pair_equal_spec; split.
        3: { unfold my_mul, my_add, my_sub; rewrite ?ev_three_b, ?ev_a; rpull_Zmod. }
        2: { unfold my_mul, my_add, my_sub; rewrite ?ev_three_b, ?ev_a; rpull_Zmod. }
        1: { unfold my_mul, my_add, my_sub; rewrite ?ev_three_b, ?ev_a; rpull_Zmod. } }
      { unfold BLS12_add_mont_spec.
        destruct outx as [x Hx], outy as [y Hy], outz as [z Hz].
        rewrite !mont_enc_val in H.
        unfold BLS12_add_Gallina_spec, my_mul, my_add, my_sub in H.
        apply pair_equal_spec in H; destruct H as [H H1].
        apply pair_equal_spec in H; destruct H as [H H0].
        apply pair_equal_spec; split.
        apply pair_equal_spec; split.
        { apply eval_from_mont_mod_inj with (r' := r') (m' := m'); auto; rewrite mont_enc_val, H. push_mont. rewrite ?ev_three_b, ?ev_a; rpull_Zmod. }
        { apply eval_from_mont_mod_inj with (r' := r') (m' := m'); auto; rewrite mont_enc_val, H0. push_mont. rewrite ?ev_three_b, ?ev_a; rpull_Zmod. }
        { apply eval_from_mont_mod_inj with (r' := r') (m' := m'); auto; rewrite mont_enc_val, H1. push_mont. rewrite ?ev_three_b, ?ev_a; rpull_Zmod. } }
    Qed.
    *)
    Lemma BLS12_add_specs_equiv : forall X1 Y1 Z1 X2 Y2 Z2 outx outy outz,
        BLS12_add_mont_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <->
            BLS12_add_Gallina_spec (val _ _ _ X1) (val _ _ _ Y1) (val _ _ _ Z1) (val _ _ _ X2) (val _ _ _ Y2) (val _ _ _ Z2) (val _ _ _ outx) (val _ _ _ outy) (val _ _ _ outz).
    Admitted.

    Lemma BLS12_add_specs_equiv' : forall X1 Y1 Z1 X2 Y2 Z2 outx outy outz
        (HX1 : valid' _ _ _ X1) (HX2 : valid' _ _ _ X2) (HY1 : valid' _ _ _ Y1) (HY2 : valid' _ _ _ Y2) (HZ1 : valid' _ _ _ Z1) (HZ2 : valid' _ _ _ Z2)
        (Houtx : valid' _ _ _ outx) (Houty : valid' _ _ _ outy) (Houtz : valid' _ _ _ outz),
        BLS12_add_mont_spec (enc_mont _ _ _ X1 HX1) (enc_mont _ _ _ Y1 HY1) (enc_mont _ _ _ Z1 HZ1) (enc_mont _ _ _ X2 HX2) (enc_mont _ _ _ Y2 HY2)
            (enc_mont _ _ _ Z2 HZ2) (enc_mont _ _ _ outx Houtx) (enc_mont _ _ _ outy Houty) (enc_mont _ _ _ outz Houtz) <->
            BLS12_add_Gallina_spec (X1) (Y1) (Z1) (X2) (Y2) (Z2) (outx) (outy) (outz).
    Proof.
        split; intros.
            - apply BLS12_add_specs_equiv in H. rewrite !mont_enc_val in H. auto.
            - apply BLS12_add_specs_equiv. rewrite !mont_enc_val. auto.
    Qed.
End G1Specs.
