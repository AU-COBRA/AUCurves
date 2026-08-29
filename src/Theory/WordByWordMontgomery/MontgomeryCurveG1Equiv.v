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

    (** ** [BLS12_add_specs_equiv], restructured for [coqc].

        The earlier script (LSP-verified, but 25-30 min under [coqc] at
        commit dc774e2 and non-terminating afterwards) worked inside the
        laden context: it destructed the three output records, rewrote
        [valid'_mod] backwards inside hypotheses whose right-hand sides
        are the 133-node zeta-normal form of the mont chain, and then ran
        [push_mont_in] — a [repeat progress first [setoid_rewrite ...]]
        that restarts a setoid search over a growing term once per
        Montgomery operation.

        The restructuring follows [RcbGeneralAChain]: the algebra is
        stated once over fresh names with a small context, closed by
        [subst; reflexivity], and the main proof only transports
        equalities.

        - [gallina_chain] is the Z-level chain: forty fresh intermediates
          [z1..z40] with one defining equation each, concluding the
          Gallina spec.  Proof: [subst] into the spec's own zeta-normal
          form, then [reflexivity].  No mont_enc record occurs in it.
        - [evm_mul_eq] / [evm_add_eq] / [evm_sub_eq] / [evm_mulA_eq] /
          [evm_mulB_eq] are the five one-step homomorphism facts, each
          over three abstract [mont_enc] variables and each its own
          [Qed].
        - [add_chain_gallina] is the mont-level chain: it is
          [gallina_chain] instantiated at [evm x1 .. evm x40], with the
          forty premises discharged by one fully applied [exact] each.
        - [BLS12_add_specs_equiv] instantiates [add_chain_gallina] with
          forty [eq_refl]s (so the [xi] evars are assigned the spec's own
          zeta-normal subterms) and then transports: forward by
          [rewrite]ing the three output equalities into the goal,
          backward by [evm_eq_mont_eq] on the three coordinate
          equalities.  No tactic rewrites inside a large hypothesis. *)

    Local Notation evm x := (eval (from_mont (val m bw n x))).

    (** *** One-step homomorphism facts (small context, one [Qed] each). *)

    Lemma evm_mul_eq (u x y : mont_enc) :
        u = (x *mont y) -> evm u = ((evm x) *' (evm y)).
    Proof. intros ->. unfold my_mul. apply evfrom_val_mul. Qed.

    Lemma evm_add_eq (u x y : mont_enc) :
        u = (x +mont y) -> evm u = ((evm x) +' (evm y)).
    Proof. intros ->. unfold my_add. apply evfrom_val_add. Qed.

    Lemma evm_sub_eq (u x y : mont_enc) :
        u = (x -mont y) -> evm u = ((evm x) -' (evm y)).
    Proof. intros ->. unfold my_sub. apply evfrom_val_sub. Qed.

    Lemma evm_mulA_eq (u y : mont_enc) :
        u = (a_mont *mont y) -> evm u = ((eval a_list) *' (evm y)).
    Proof.
        intros ->. unfold my_mul. rewrite evfrom_val_mul.
        rewrite <- ev_a. reflexivity.
    Qed.

    Lemma evm_mulB_eq (u y : mont_enc) :
        u = (three_b_mont *mont y) -> evm u = ((eval three_b_list) *' (evm y)).
    Proof.
        intros ->. unfold my_mul. rewrite evfrom_val_mul.
        rewrite <- ev_three_b. reflexivity.
    Qed.

    Lemma evm_eq_mont_eq (x y : mont_enc) : evm x = evm y -> x = y.
    Proof.
        intros H. apply eval_from_mont_mod_inj with (r' := r') (m' := m'); auto.
        rewrite H; reflexivity.
    Qed.

    (** *** The Z-level chain.

        [z1..z40] name the forty intermediate values of
        [BLS12_add_Gallina_spec]'s let-chain; the spec reuses the
        bedrock2 temporaries [t0..t5], [X3], [Y3], [Z3] in place, so the
        mapping is
        z1=t0 z2=t1 z3=t2 z4=t3 z5=t4 z6=t3 z7=t4 z8=t3 z9=t4 z10=t5
        z11=t4 z12=t5 z13=t4 z14=t5 z15=X3 z16=t5 z17=X3 z18=t5 z19=Z3
        z20=X3 z21=Z3 z22=X3 z23=Z3 z24=Y3 z25=t1 z26=t1 z27=t2 z28=t4
        z29=t1 z30=t2 z31=t2 z32=t4 z33=t0 z34=Y3 z35=t0 z36=X3 z37=X3
        z38=t0 z39=Z3 z40=Z3, with the result at (z37, z34, z40). *)
    Lemma gallina_chain
        (X1 Y1 Z1 X2 Y2 Z2 outx outy outz : list Z)
        (z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
         z11 z12 z13 z14 z15 z16 z17 z18 z19 z20
         z21 z22 z23 z24 z25 z26 z27 z28 z29 z30
         z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 : Z)
        (E1  : z1  = ((evfrom X1) *' (evfrom X2)))
        (E2  : z2  = ((evfrom Y1) *' (evfrom Y2)))
        (E3  : z3  = ((evfrom Z1) *' (evfrom Z2)))
        (E4  : z4  = ((evfrom X1) +' (evfrom Y1)))
        (E5  : z5  = ((evfrom X2) +' (evfrom Y2)))
        (E6  : z6  = (z4 *' z5))
        (E7  : z7  = (z1 +' z2))
        (E8  : z8  = (z6 -' z7))
        (E9  : z9  = ((evfrom X1) +' (evfrom Z1)))
        (E10 : z10 = ((evfrom X2) +' (evfrom Z2)))
        (E11 : z11 = (z9 *' z10))
        (E12 : z12 = (z1 +' z3))
        (E13 : z13 = (z11 -' z12))
        (E14 : z14 = ((evfrom Y1) +' (evfrom Z1)))
        (E15 : z15 = ((evfrom Y2) +' (evfrom Z2)))
        (E16 : z16 = (z14 *' z15))
        (E17 : z17 = (z2 +' z3))
        (E18 : z18 = (z16 -' z17))
        (E19 : z19 = ((eval a_list) *' z13))
        (E20 : z20 = ((eval three_b_list) *' z3))
        (E21 : z21 = (z20 +' z19))
        (E22 : z22 = (z2 -' z21))
        (E23 : z23 = (z2 +' z21))
        (E24 : z24 = (z22 *' z23))
        (E25 : z25 = (z1 +' z1))
        (E26 : z26 = (z25 +' z1))
        (E27 : z27 = ((eval a_list) *' z3))
        (E28 : z28 = ((eval three_b_list) *' z13))
        (E29 : z29 = (z26 +' z27))
        (E30 : z30 = (z1 -' z27))
        (E31 : z31 = ((eval a_list) *' z30))
        (E32 : z32 = (z28 +' z31))
        (E33 : z33 = (z29 *' z32))
        (E34 : z34 = (z24 +' z33))
        (E35 : z35 = (z18 *' z32))
        (E36 : z36 = (z8 *' z22))
        (E37 : z37 = (z36 -' z35))
        (E38 : z38 = (z8 *' z29))
        (E39 : z39 = (z18 *' z23))
        (E40 : z40 = (z39 +' z38))
        (Ex : (evfrom outx) = z37)
        (Ey : (evfrom outy) = z34)
        (Ez : (evfrom outz) = z40) :
        BLS12_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz.
    Proof.
        unfold BLS12_add_Gallina_spec.
        Timeout 120 (cbv beta zeta).
        Timeout 120 (rewrite Ex, Ey, Ez).
        clear Ex Ey Ez.
        Timeout 120 (subst z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
                           z11 z12 z13 z14 z15 z16 z17 z18 z19 z20
                           z21 z22 z23 z24 z25 z26 z27 z28 z29 z30
                           z31 z32 z33 z34 z35 z36 z37 z38 z39 z40).
        Timeout 120 reflexivity.
    Qed.

    (** *** The mont-level chain: [gallina_chain] at [evm x1 .. evm x40].

        Premise order matches [BLS12_add_mont_spec]'s let-chain exactly,
        so no commutation step is needed. *)
    Lemma add_chain_gallina
        (X1 Y1 Z1 X2 Y2 Z2 : mont_enc)
        (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
         x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
         x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
         x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 : mont_enc)
        (H1  : x1  = (X1  *mont X2))
        (H2  : x2  = (Y1  *mont Y2))
        (H3  : x3  = (Z1  *mont Z2))
        (H4  : x4  = (X1  +mont Y1))
        (H5  : x5  = (X2  +mont Y2))
        (H6  : x6  = (x4  *mont x5))
        (H7  : x7  = (x1  +mont x2))
        (H8  : x8  = (x6  -mont x7))
        (H9  : x9  = (X1  +mont Z1))
        (H10 : x10 = (X2  +mont Z2))
        (H11 : x11 = (x9  *mont x10))
        (H12 : x12 = (x1  +mont x3))
        (H13 : x13 = (x11 -mont x12))
        (H14 : x14 = (Y1  +mont Z1))
        (H15 : x15 = (Y2  +mont Z2))
        (H16 : x16 = (x14 *mont x15))
        (H17 : x17 = (x2  +mont x3))
        (H18 : x18 = (x16 -mont x17))
        (H19 : x19 = (a_mont *mont x13))
        (H20 : x20 = (three_b_mont *mont x3))
        (H21 : x21 = (x20 +mont x19))
        (H22 : x22 = (x2  -mont x21))
        (H23 : x23 = (x2  +mont x21))
        (H24 : x24 = (x22 *mont x23))
        (H25 : x25 = (x1  +mont x1))
        (H26 : x26 = (x25 +mont x1))
        (H27 : x27 = (a_mont *mont x3))
        (H28 : x28 = (three_b_mont *mont x13))
        (H29 : x29 = (x26 +mont x27))
        (H30 : x30 = (x1  -mont x27))
        (H31 : x31 = (a_mont *mont x30))
        (H32 : x32 = (x28 +mont x31))
        (H33 : x33 = (x29 *mont x32))
        (H34 : x34 = (x24 +mont x33))
        (H35 : x35 = (x18 *mont x32))
        (H36 : x36 = (x8  *mont x22))
        (H37 : x37 = (x36 -mont x35))
        (H38 : x38 = (x8  *mont x29))
        (H39 : x39 = (x18 *mont x23))
        (H40 : x40 = (x39 +mont x38)) :
        BLS12_add_Gallina_spec
            (val m bw n X1) (val m bw n Y1) (val m bw n Z1)
            (val m bw n X2) (val m bw n Y2) (val m bw n Z2)
            (val m bw n x37) (val m bw n x34) (val m bw n x40).
    Proof.
        Timeout 120 (apply (gallina_chain
            (val m bw n X1) (val m bw n Y1) (val m bw n Z1)
            (val m bw n X2) (val m bw n Y2) (val m bw n Z2)
            (val m bw n x37) (val m bw n x34) (val m bw n x40)
            (evm x1)  (evm x2)  (evm x3)  (evm x4)  (evm x5)
            (evm x6)  (evm x7)  (evm x8)  (evm x9)  (evm x10)
            (evm x11) (evm x12) (evm x13) (evm x14) (evm x15)
            (evm x16) (evm x17) (evm x18) (evm x19) (evm x20)
            (evm x21) (evm x22) (evm x23) (evm x24) (evm x25)
            (evm x26) (evm x27) (evm x28) (evm x29) (evm x30)
            (evm x31) (evm x32) (evm x33) (evm x34) (evm x35)
            (evm x36) (evm x37) (evm x38) (evm x39) (evm x40))).
        exact (evm_mul_eq  _ _ _ H1).
        exact (evm_mul_eq  _ _ _ H2).
        exact (evm_mul_eq  _ _ _ H3).
        exact (evm_add_eq  _ _ _ H4).
        exact (evm_add_eq  _ _ _ H5).
        exact (evm_mul_eq  _ _ _ H6).
        exact (evm_add_eq  _ _ _ H7).
        exact (evm_sub_eq  _ _ _ H8).
        exact (evm_add_eq  _ _ _ H9).
        exact (evm_add_eq  _ _ _ H10).
        exact (evm_mul_eq  _ _ _ H11).
        exact (evm_add_eq  _ _ _ H12).
        exact (evm_sub_eq  _ _ _ H13).
        exact (evm_add_eq  _ _ _ H14).
        exact (evm_add_eq  _ _ _ H15).
        exact (evm_mul_eq  _ _ _ H16).
        exact (evm_add_eq  _ _ _ H17).
        exact (evm_sub_eq  _ _ _ H18).
        exact (evm_mulA_eq _ _ H19).
        exact (evm_mulB_eq _ _ H20).
        exact (evm_add_eq  _ _ _ H21).
        exact (evm_sub_eq  _ _ _ H22).
        exact (evm_add_eq  _ _ _ H23).
        exact (evm_mul_eq  _ _ _ H24).
        exact (evm_add_eq  _ _ _ H25).
        exact (evm_add_eq  _ _ _ H26).
        exact (evm_mulA_eq _ _ H27).
        exact (evm_mulB_eq _ _ H28).
        exact (evm_add_eq  _ _ _ H29).
        exact (evm_sub_eq  _ _ _ H30).
        exact (evm_mulA_eq _ _ H31).
        exact (evm_add_eq  _ _ _ H32).
        exact (evm_mul_eq  _ _ _ H33).
        exact (evm_add_eq  _ _ _ H34).
        exact (evm_mul_eq  _ _ _ H35).
        exact (evm_mul_eq  _ _ _ H36).
        exact (evm_sub_eq  _ _ _ H37).
        exact (evm_mul_eq  _ _ _ H38).
        exact (evm_mul_eq  _ _ _ H39).
        exact (evm_add_eq  _ _ _ H40).
        reflexivity.
        reflexivity.
        reflexivity.
    Qed.

    Lemma BLS12_add_specs_equiv : forall X1 Y1 Z1 X2 Y2 Z2 outx outy outz,
        BLS12_add_mont_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <->
            BLS12_add_Gallina_spec (val _ _ _ X1) (val _ _ _ Y1) (val _ _ _ Z1) (val _ _ _ X2) (val _ _ _ Y2) (val _ _ _ Z2) (val _ _ _ outx) (val _ _ _ outy) (val _ _ _ outz).
    Proof.
        intros X1 Y1 Z1 X2 Y2 Z2 outx outy outz.
        (* Instantiate the chain at the spec's own zeta-normal subterms:
           each [eq_refl] assigns one [xi] evar. *)
        Timeout 120 (epose proof (add_chain_gallina X1 Y1 Z1 X2 Y2 Z2
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            eq_refl eq_refl eq_refl eq_refl eq_refl
            eq_refl eq_refl eq_refl eq_refl eq_refl
            eq_refl eq_refl eq_refl eq_refl eq_refl
            eq_refl eq_refl eq_refl eq_refl eq_refl
            eq_refl eq_refl eq_refl eq_refl eq_refl
            eq_refl eq_refl eq_refl eq_refl eq_refl
            eq_refl eq_refl eq_refl eq_refl eq_refl
            eq_refl eq_refl eq_refl eq_refl eq_refl) as HG).
        split.
        - intros H.
          unfold BLS12_add_mont_spec in H.
          Timeout 120 (cbv beta zeta in H).
          apply pair_equal_spec in H; destruct H as [H Hz].
          apply pair_equal_spec in H; destruct H as [Hx Hy].
          Timeout 120 (rewrite Hx, Hy, Hz).
          Timeout 120 (exact HG).
        - intros H.
          unfold BLS12_add_Gallina_spec in H, HG.
          Timeout 120 (cbv beta zeta in H, HG).
          apply pair_equal_spec in H; destruct H as [H Hz].
          apply pair_equal_spec in H; destruct H as [Hx Hy].
          apply pair_equal_spec in HG; destruct HG as [HG HGz].
          apply pair_equal_spec in HG; destruct HG as [HGx HGy].
          pose proof (evm_eq_mont_eq _ _ (eq_trans Hx (eq_sym HGx))) as Ex.
          pose proof (evm_eq_mont_eq _ _ (eq_trans Hy (eq_sym HGy))) as Ey.
          pose proof (evm_eq_mont_eq _ _ (eq_trans Hz (eq_sym HGz))) as Ez.
          unfold BLS12_add_mont_spec.
          Timeout 120 (cbv beta zeta).
          Timeout 120 (rewrite Ex, Ey, Ez; reflexivity).
    Qed.

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
