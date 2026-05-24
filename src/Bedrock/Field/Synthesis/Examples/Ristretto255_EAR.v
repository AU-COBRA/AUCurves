(** DSP scratch for encode_aux_rotate: imports the built CaseScratch.vo
    (helpers + sqrt_ratio_m1_correct) so MCP loads fast and reliably.
    Develop ear_proof here, then port into CaseScratch's encode_aux_rotate. *)
From Stdlib Require Import ZArith NArith Lists.List micromega.Lia Bool.Bool.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Algebra.Group Crypto.Spec.Curve25519 Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Sqrt.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_CaseScratch.
Import ListNotations.
Local Open Scope F_scope.
Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).
Local Existing Instance Curve25519.field.
Local Existing Instance Curve25519.char_ge_3.
Add Field _f : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F (2^255-19)%positive))
  (morphism (F.ring_morph (2^255-19)%positive), constants [F.is_constant],
   div (F.morph_div_theory (2^255-19)%positive),
   power_tac (F.power_theory (2^255-19)%positive) [F.is_pow_constant]).

(** [(-1)] raised to an odd power is [-1]. *)
Lemma negone_odd_pow : forall k:N, ((F.opp Fone : Fp) ^ (2*k+1))%F = F.opp Fone.
Proof.
  intro k. rewrite F.pow_add_r, F.pow_1_r, <- (F.pow_pow_l (F.opp Fone : Fp) 2 k).
  rewrite F.pow_2_r.
  assert (Hoo : (F.opp Fone * F.opp Fone)%F = (Fone:Fp))
    by (apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  rewrite Hoo.
  assert (Hpk : (Fone:Fp) ^ k = Fone)
    by (etransitivity; [ apply F.pow_1_l | reflexivity ]).
  rewrite Hpk. apply Hierarchy.left_identity.
Qed.

(** [SQRT_M1] is a quadratic non-residue mod [p = 2^255-19].
    By Euler's criterion, if [SQRT_M1] were a square then
    [SQRT_M1 ^ ((p-1)/2) = 1]; but [(p-1)/2 = 2*(2^253-5)], so
    [SQRT_M1 ^ ((p-1)/2) = (SQRT_M1^2)^(2^253-5) = (-1)^(2^253-5) = -1]
    since [2^253-5] is odd, contradicting [1 <> -1]. *)
Lemma SQRT_M1_nonsquare : ~ (exists b:Fp, (b*b)%F = SQRT_M1).
Proof.
  intros [b Hb].
  pose proof (@F.euler_criterion (2^255-19)%positive prime_p ltac:(Decidable.vm_decide)
              SQRT_M1 SQRT_M1_nz) as Heuler.
  assert (Hsq : (SQRT_M1 ^ Z.to_N ((2^255-19) / 2))%F = Fone)
    by (apply Heuler; exists b; exact Hb).
  assert (Hexp : Z.to_N ((2^255-19) / 2) = (2 * (2^253 - 5))%N)
    by (vm_compute; reflexivity).
  rewrite Hexp in Hsq.
  rewrite <- (F.pow_pow_l SQRT_M1 2 (2^253-5)) in Hsq.
  rewrite F.pow_2_r, SQRT_M1_sq in Hsq.
  assert (Hodd : (2^253-5)%N = (2 * (2^252 - 3) + 1)%N) by (vm_compute; reflexivity).
  rewrite Hodd in Hsq. rewrite negone_odd_pow in Hsq.
  apply one_ne_opp_one. symmetry. exact Hsq.
Qed.

Lemma ear_proof : forall (c Qx Qy : Fp),
  (c * c)%F = F.opp Fone ->
  (E.a * (Qx * Qx) + Qy * Qy =
   Fone + E.d * (Qx * Qx) * (Qy * Qy))%F ->
  ristretto_encode_aux (c * Qy) (c * Qx) Fone (c * Qy * (c * Qx))
  = ristretto_encode_aux Qx Qy Fone (Qx * Qy).
Proof.
  intros c Qx Qy Hc HQ.
  unfold ristretto_encode_aux.
  destruct (F.eq_dec (Qx * Qy)%F Fzero) as [Hxy0 | Hxynz].
  - (* DEGENERATE: Qx*Qy = 0.  Both sqrt args are 0, so invsqrt = 0 on each
       side, hence den_inv = 0 and both encodings collapse to [abs Fzero]. *)
    assert (HargL : ((Fone + c * Qx) * (Fone - c * Qx) *
                     (c * Qy * (c * Qx) * (c * Qy * (c * Qx))))%F = Fzero).
    { assert (Hr : (c * Qy * (c * Qx))%F = Fzero).
      { assert (He : (c * Qy * (c * Qx))%F = (c*c*(Qx*Qy))%F) by field.
        rewrite He, Hxy0. field. }
      rewrite Hr. field. }
    assert (HargR : ((Fone + Qy) * (Fone - Qy) * (Qx * Qy * (Qx * Qy)))%F = Fzero).
    { rewrite Hxy0. field. }
    rewrite HargL, HargR.
    assert (Hsr0 : snd (sqrt_ratio_m1 Fone Fzero) = Fzero).
    { unfold sqrt_ratio_m1. cbv zeta. cbn [snd].
      set (r0 := (Fone * (Fzero * Fzero * Fzero) *
        (Fone * (Fzero * Fzero * Fzero * (Fzero * Fzero * Fzero) * Fzero))
        ^ Z.to_N ((2 ^ 255 - 19 - 5) / 8))%F).
      assert (Hr0 : r0 = Fzero) by (unfold r0; field). rewrite Hr0.
      destruct (F.to_Z (Fzero * Fzero * Fzero) =? F.to_Z Fone)%Z;
        [ unfold abs; rewrite is_negative_zero; reflexivity
        | destruct (F.to_Z (Fzero * Fzero * Fzero) =? F.to_Z (F.opp Fone))%Z;
          [ assert (Hz : (Fzero * SQRT_M1)%F = Fzero) by field; rewrite Hz;
            unfold abs; rewrite is_negative_zero; reflexivity
          | destruct (F.to_Z (Fzero * Fzero * Fzero)
                       =? F.to_Z (F.opp (SQRT_M1 * Fone)))%Z;
            [ assert (Hz : (Fzero * SQRT_M1)%F = Fzero) by field; rewrite Hz;
              unfold abs; rewrite is_negative_zero; reflexivity
            | unfold abs; rewrite is_negative_zero; reflexivity ] ] ]. }
    destruct (sqrt_ratio_m1 Fone Fzero) as [bb invsqrt] eqn:Esr.
    cbn [snd] in Hsr0. subst invsqrt.
    transitivity (abs Fzero);
      [ f_equal;
        destruct (is_negative (c * Qy * (c * Qx) *
          (Fzero * ((Fone + c * Qx) * (Fone - c * Qx)) *
           (Fzero * (c * Qy * (c * Qx))) * (c * Qy * (c * Qx))))); field
      | symmetry; f_equal;
        destruct (is_negative (Qx * Qy *
          (Fzero * ((Fone + Qy) * (Fone - Qy)) * (Fzero * (Qx * Qy)) *
           (Qx * Qy)))); field ].
  - (* MAIN: Qx*Qy <> 0. *)
    assert (HQxnz : Qx <> Fzero). { intro H. apply Hxynz. rewrite H. field. }
    assert (HQynz : Qy <> Fzero). { intro H. apply Hxynz. rewrite H. field. }
    assert (Hcnz : c <> Fzero).
    { intro H. assert (Hbad : (c*c)%F = Fzero) by (rewrite H; field).
      rewrite Hc in Hbad. apply one_ne_opp_one.
      assert (Hr : (Fone:Fp) = F.opp (F.opp Fone)) by field.
      rewrite Hr at 1. rewrite Hbad. field. }
    assert (Hxy2nz : (Qx * Qy * (Qx * Qy))%F <> Fzero).
    { intro H. apply mul_zero_factor in H. destruct H; apply Hxynz; assumption. }
    assert (Hu1L_eq : ((Fone + c * Qx) * (Fone - c * Qx))%F = (Fone + Qx * Qx)%F).
    { assert (Hr : ((Fone + c * Qx) * (Fone - c * Qx))%F = (Fone - (c*c)*(Qx*Qx))%F)
        by field. rewrite Hr, Hc. field. }
    assert (HargL : ((Fone + c * Qx) * (Fone - c * Qx) *
                     (c * Qy * (c * Qx) * (c * Qy * (c * Qx))))%F <> Fzero).
    { rewrite Hu1L_eq. intro H. apply mul_zero_factor in H. destruct H as [H | H].
      { apply (PL_nonzero Qx Qy HQ HQxnz HQynz); exact H. }
      { apply Hxy2nz.
        assert (He : (c * Qy * (c * Qx) * (c * Qy * (c * Qx)))%F
                   = ((c*c)*(c*c)*(Qx * Qy * (Qx * Qy)))%F) by field.
        rewrite He, Hc in H.
        assert (Hr : (Qx * Qy * (Qx * Qy))%F
                   = (F.opp Fone * F.opp Fone * (Qx * Qy * (Qx * Qy)))%F) by field.
        rewrite Hr; exact H. } }
    assert (HargR : ((Fone + Qy) * (Fone - Qy) * (Qx * Qy * (Qx * Qy)))%F <> Fzero).
    { intro H. apply mul_zero_factor in H. destruct H as [H | H].
      { apply (vR_nonzero Qx Qy HQ HQxnz HQynz); exact H. }
      { apply Hxy2nz; exact H. } }
    pose proof (sqrt_ratio_m1_correct Fone _ HargL) as HL.
    destruct (sqrt_ratio_m1 Fone
      ((Fone + c * Qx) * (Fone - c * Qx) * (c * Qy * (c * Qx) * (c * Qy * (c * Qx)))))
      as [wsL iL] eqn:EL.
    pose proof (sqrt_ratio_m1_correct Fone _ HargR) as HR.
    destruct (sqrt_ratio_m1 Fone ((Fone + Qy) * (Fone - Qy) * (Qx * Qy * (Qx * Qy))))
      as [wsR iR] eqn:ER.
    destruct HL as [HLcase HLneg]. destruct HR as [HRcase HRneg].
    apply abs_eq_of_sq.
    set (eL := (c * Qy * (c * Qx))%F) in *.
    set (aL := ((Fone + c * Qx) * (Fone - c * Qx))%F) in *.
    set (aR := ((Fone + Qy) * (Fone - Qy))%F) in *.
    set (P := (Qx * Qy)%F) in *.
    assert (HeL : eL = F.opp P).
    { unfold eL, P.
      assert (Hr : (c * Qy * (c * Qx))%F = ((c*c)*(Qx*Qy))%F) by field.
      rewrite Hr, Hc. field. }
    set (zL := (eL * (iL * aL * (iL * eL) * eL))%F) in *.
    set (zR := (P * (iR * aR * (iR * P) * P))%F) in *.
    assert (HeLsq : (eL * eL)%F = (P * P)%F) by (rewrite HeL; field).
    assert (HzL_val : zL = (F.opp (aL * (eL * eL) * iL * iL) * P)%F).
    { unfold zL. rewrite HeL. field. }
    assert (HzR_val : zR = (aR * (P * P) * iR * iR * P)%F) by (unfold zR; field).
    (* Case-independent facts. *)
    assert (Ha : (E.a : Fp) = F.opp Fone)
      by (unfold E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
    assert (K2 : (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d))%F = Fone)
      by (unfold INVSQRT_A_MINUS_D, E.a, E.d;
          apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
    assert (HaRnz : aR <> Fzero) by (intro Hk; apply HargR; rewrite Hk; field).
    assert (HaLnz : aL <> Fzero) by (intro Hk; apply HargL; rewrite Hk; field).
    assert (HaLaR : (aL * aR)%F = (P * P * (E.a - E.d))%F).
    { unfold aR, P. rewrite Ha in HQ |- *.
      assert (Hd : (E.d*(Qx*Qx)*(Qy*Qy))%F = (Qy*Qy - Qx*Qx - Fone)%F).
      { assert (Hr : (E.d*(Qx*Qx)*(Qy*Qy))%F
                   = ((Fone + E.d*(Qx*Qx)*(Qy*Qy)) - Fone)%F) by field.
        rewrite Hr.
        assert (HQc : (Qy*Qy - Qx*Qx)%F = (Fone + E.d*(Qx*Qx)*(Qy*Qy))%F).
        { assert (Hr2 : (Qy*Qy - Qx*Qx)%F = (F.opp Fone*(Qx*Qx) + Qy*Qy)%F) by field.
          rewrite Hr2. exact HQ. }
        rewrite <- HQc. field. }
      assert (Hr : ((Fone + Qx * Qx) * ((Fone + Qy) * (Fone - Qy)))%F
                 = (Fone + Qx*Qx - Qy*Qy - Qx*Qx*(Qy*Qy))%F) by field.
      change ((Fone + c * Qx) * (Fone - c * Qx))%F with aL. rewrite Hu1L_eq, Hr.
      assert (Hr3 : (Qx * Qy * (Qx * Qy) * (F.opp Fone - E.d))%F
                  = (F.opp (Qx*Qx*(Qy*Qy)) - E.d*(Qx*Qx)*(Qy*Qy))%F) by field.
      rewrite Hr3, Hd. field. }
    assert (Hcval : c = SQRT_M1 \/ c = F.opp SQRT_M1).
    { assert (Hfac : ((c - SQRT_M1) * (c + SQRT_M1))%F = Fzero).
      { assert (Hr : ((c - SQRT_M1) * (c + SQRT_M1))%F = (c*c - SQRT_M1*SQRT_M1)%F) by field.
        rewrite Hr, Hc, SQRT_M1_sq. field. }
      apply mul_zero_factor in Hfac. destruct Hfac as [H | H].
      { left. apply sub_eq_zero in H. exact H. }
      { right. assert (Hr2 : c = ((c + SQRT_M1) - SQRT_M1)%F) by field.
        rewrite Hr2, H. field. } }
    (* SQRT_M1 is itself a nonzero square root of -1; needed for sign-flip lemmas. *)
    assert (HSQ : (SQRT_M1 * SQRT_M1)%F = F.opp Fone) by exact SQRT_M1_sq.
    destruct HLcase as [[HwsL HsqL] | [HwsL HsqL]];
      destruct HRcase as [[HwsR HsqR] | [HwsR HsqR]].
    + (* wsL = true, wsR = true: zL = -P, zR = P. *)
      rewrite HsqL in HzL_val. rewrite HsqR in HzR_val.
      assert (HnzR : zR <> Fzero) by (rewrite HzR_val; intro Hk; apply Hxynz;
        assert (Hr : P = (Fone * P)%F) by field; rewrite Hr; exact Hk).
      assert (HsignL : is_negative zL = negb (is_negative zR)).
      { rewrite HzL_val, HzR_val. assert (He : (F.opp Fone * P)%F = F.opp (Fone * P)%F) by field.
        rewrite He. apply is_negative_opp_nonzero. rewrite <- HzR_val. exact HnzR. }
      rewrite HsignL.
      assert (HML : (iL * aL * (iL * eL) * eL)%F = Fone) by (rewrite <- HsqL; field).
      assert (HMR : (iR * aR * (iR * P) * P)%F = Fone) by (rewrite <- HsqR; field).
      rewrite HML, HMR.
      assert (Hmag : (iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))%F
                   = (iR * P * (iR * P))%F).
      { apply (mul_cancel_l aR _ _ HaRnz).
        transitivity ((aL * (eL * eL) * iL * iL)
          * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F.
        { rewrite HeLsq.
          assert (Hexp : (aR * (iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D)))%F
            = ((aL * aR) * (aL * iL * iL) * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F) by field.
          rewrite Hexp, HaLaR. field. }
        { rewrite HsqL, K2.
          assert (Hr : (aR * (iR * P * (iR * P)))%F = (aR * (P * P) * iR * iR)%F) by field.
          rewrite Hr, HsqR. field. } }
      assert (Hmag2 : (iL * eL * (iL * eL))%F
                    = (iR * aR * INVSQRT_A_MINUS_D * (iR * aR * INVSQRT_A_MINUS_D))%F).
      { apply (mul_cancel_l aL _ _ HaLnz).
        transitivity ((aR * (P * P) * iR * iR)
          * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F.
        { rewrite HsqR, K2.
          assert (Hr : (aL * (iL * eL * (iL * eL)))%F = (aL * (eL * eL) * iL * iL)%F) by field.
          rewrite Hr, HsqL. field. }
        { assert (Hr : (aL * (iR * aR * INVSQRT_A_MINUS_D * (iR * aR * INVSQRT_A_MINUS_D)))%F
            = ((aL * aR) * (aR * iR * iR) * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F) by field.
          rewrite Hr, HaLaR.
          assert (Ht : (P * P * (E.a - E.d) * (aR * iR * iR)
                        * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F
            = ((aR * (P * P) * iR * iR)
               * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F) by field.
          rewrite Ht, HsqR. field. } }
      destruct (is_negative zR) eqn:EzR; simpl negb; cbn match.
      * (* zR negative: LHS no-rotate (iL*eL), RHS rotate (iR*aR*INVSQRT). *)
        assert (HF1 : (c * Qy * Fone)%F = (c * Qy)%F) by field.
        assert (HF2 : (Qy * SQRT_M1 * Fone)%F = (Qy * SQRT_M1)%F) by field.
        rewrite HF1, HF2.
        destruct Hcval as [Hcv | Hcv].
        { assert (HE1 : (c * Qy)%F = (Qy * SQRT_M1)%F) by (rewrite Hcv; field).
          assert (HE2 : (c * Qx)%F = (Qx * SQRT_M1)%F) by (rewrite Hcv; field).
          rewrite HE1, HE2.
          destruct (is_negative (Qy * SQRT_M1)); cbn match;
            [ set (S := (Fone - F.opp (Qx * SQRT_M1))%F) in *
            | set (S := (Fone - Qx * SQRT_M1)%F) in * ];
            (transitivity ((iL * eL * (iL * eL)) * (S * S))%F;
              [ field | rewrite Hmag2; field ]). }
        { assert (HE1 : (c * Qy)%F = F.opp (Qy * SQRT_M1)%F) by (rewrite Hcv; field).
          assert (HE2 : (c * Qx)%F = F.opp (Qx * SQRT_M1)%F) by (rewrite Hcv; field).
          rewrite HE1, HE2.
          assert (HQySnz : (Qy * SQRT_M1)%F <> Fzero)
            by (intro Hk; apply mul_zero_factor in Hk; destruct Hk as [Hk|Hk];
                [apply HQynz; exact Hk | apply SQRT_M1_nz; exact Hk]).
          rewrite (is_negative_opp_nonzero _ HQySnz).
          destruct (is_negative (Qy * SQRT_M1)); simpl negb; cbn match.
          { set (S := (Fone - F.opp (Qx * SQRT_M1))%F) in *.
            transitivity ((iL * eL * (iL * eL)) * (S * S))%F; [ field | rewrite Hmag2; field ]. }
          { assert (Hyy : (F.opp (F.opp (Qx * SQRT_M1)))%F = (Qx * SQRT_M1)%F) by field.
            rewrite Hyy. set (S := (Fone - Qx * SQRT_M1)%F) in *.
            transitivity ((iL * eL * (iL * eL)) * (S * S))%F; [ field | rewrite Hmag2; field ]. } }
      * (* zR not negative: LHS rotate (iL*aL*INVSQRT), RHS no-rotate (iR*P). *)
        assert (HF1 : (c * Qx * SQRT_M1 * Fone)%F = (c * Qx * SQRT_M1)%F) by field.
        assert (HF2 : (Qx * Fone)%F = Qx) by field.
        rewrite HF1, HF2.
        destruct Hcval as [Hcv | Hcv].
        { assert (HE1 : (c * Qx * SQRT_M1)%F = F.opp Qx) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qx * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qx)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HE2 : (c * Qy * SQRT_M1)%F = F.opp Qy) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qy * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          rewrite HE1, HE2.
          rewrite (is_negative_opp_nonzero _ HQxnz).
          destruct (is_negative Qx); simpl negb; cbn match.
          { set (S := (Fone - F.opp Qy)%F) in *.
            transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * (S * S))%F; [ field | rewrite Hmag; field ]. }
          { assert (Hyy : (F.opp (F.opp Qy))%F = Qy) by field. rewrite Hyy.
            set (S := (Fone - Qy)%F) in *.
            transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * (S * S))%F; [ field | rewrite Hmag; field ]. } }
        { assert (HE1 : (c * Qx * SQRT_M1)%F = Qx) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qx * SQRT_M1)%F = (F.opp (SQRT_M1 * SQRT_M1) * Qx)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HE2 : (c * Qy * SQRT_M1)%F = Qy) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qy * SQRT_M1)%F = (F.opp (SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          rewrite HE1, HE2.
          destruct (is_negative Qx); cbn match;
            [ set (S := (Fone - F.opp Qy)%F) in *
            | set (S := (Fone - Qy)%F) in * ];
            (transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * (S * S))%F; [ field | rewrite Hmag; field ]). }
    + (* wsL = true, wsR = false: VACUOUS.  From HsqL [aL*P^2*iL^2 = 1] and
         HsqR [aR*P^2*iR^2 = SQRT_M1], multiplying and using
         HaLaR [aL*aR = P^2*(E.a-E.d)] and K2 [INVSQRT^2*(E.a-E.d) = 1] gives
         (P^3*iL*iR*F.inv INVSQRT_A_MINUS_D)^2 = SQRT_M1, i.e. SQRT_M1 is a
         square, contradicting [SQRT_M1_nonsquare]. *)
      exfalso.
      assert (HInz : INVSQRT_A_MINUS_D <> Fzero)
        by (unfold INVSQRT_A_MINUS_D; Decidable.vm_decide).
      apply SQRT_M1_nonsquare.
      exists (F.inv INVSQRT_A_MINUS_D * (P * P * P) * iL * iR)%F.
      set (X := ((P*P*P*iL*iR) * (P*P*P*iL*iR))%F).
      assert (HsqL' : (aL * (P * P) * iL * iL)%F = Fone)
        by (rewrite <- HeLsq; exact HsqL).
      assert (HsqR' : (aR * (P * P) * iR * iR)%F = SQRT_M1)
        by (rewrite HsqR; field).
      assert (Hpre : ((E.a - E.d) * X)%F = SQRT_M1).
      { transitivity ((aL * (P*P) * iL * iL) * (aR * (P*P) * iR * iR))%F.
        { assert (Hr : ((aL * (P*P) * iL * iL) * (aR * (P*P) * iR * iR))%F
                     = ((aL * aR) * ((P*P*iL*iR) * (P*P*iL*iR)))%F) by field.
          rewrite Hr, HaLaR. unfold X. field. }
        { rewrite HsqL', HsqR'. field. } }
      assert (HX : X = (SQRT_M1 * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F).
      { transitivity ((INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)) * X)%F.
        { rewrite K2. field. }
        { assert (Hr : (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d) * X)%F
                     = (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * ((E.a - E.d) * X))%F) by field.
          rewrite Hr, Hpre. field. } }
      transitivity (F.inv INVSQRT_A_MINUS_D * F.inv INVSQRT_A_MINUS_D * X)%F.
      * unfold X. field; exact HInz.
      * rewrite HX. field; exact HInz.
    + (* wsL = false, wsR = true: VACUOUS, symmetric to the previous
         (SQRT_M1 would be a square via P^3*iL*iR*F.inv INVSQRT_A_MINUS_D). *)
      exfalso.
      assert (HInz : INVSQRT_A_MINUS_D <> Fzero)
        by (unfold INVSQRT_A_MINUS_D; Decidable.vm_decide).
      apply SQRT_M1_nonsquare.
      exists (F.inv INVSQRT_A_MINUS_D * (P * P * P) * iL * iR)%F.
      set (X := ((P*P*P*iL*iR) * (P*P*P*iL*iR))%F).
      assert (HsqL' : (aL * (P * P) * iL * iL)%F = SQRT_M1)
        by (rewrite <- HeLsq, HsqL; field).
      assert (HsqR' : (aR * (P * P) * iR * iR)%F = Fone) by exact HsqR.
      assert (Hpre : ((E.a - E.d) * X)%F = SQRT_M1).
      { transitivity ((aL * (P*P) * iL * iL) * (aR * (P*P) * iR * iR))%F.
        { assert (Hr : ((aL * (P*P) * iL * iL) * (aR * (P*P) * iR * iR))%F
                     = ((aL * aR) * ((P*P*iL*iR) * (P*P*iL*iR)))%F) by field.
          rewrite Hr, HaLaR. unfold X. field. }
        { rewrite HsqL', HsqR'. field. } }
      assert (HX : X = (SQRT_M1 * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F).
      { transitivity ((INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)) * X)%F.
        { rewrite K2. field. }
        { assert (Hr : (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d) * X)%F
                     = (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * ((E.a - E.d) * X))%F) by field.
          rewrite Hr, Hpre. field. } }
      transitivity (F.inv INVSQRT_A_MINUS_D * F.inv INVSQRT_A_MINUS_D * X)%F.
      * unfold X. field; exact HInz.
      * rewrite HX. field; exact HInz.
    + (* wsL = false, wsR = false: zL = -SQRT_M1*P, zR = SQRT_M1*P. *)
      rewrite HsqL in HzL_val. rewrite HsqR in HzR_val.
      assert (HnzR : zR <> Fzero) by (rewrite HzR_val; intro Hk;
        apply mul_zero_factor in Hk; destruct Hk as [Hk|Hk];
        [ apply SQRT_M1_nz; assert (Hr : SQRT_M1 = (SQRT_M1*Fone)%F) by field;
          rewrite Hr; exact Hk | apply Hxynz; exact Hk ]).
      assert (HsignL : is_negative zL = negb (is_negative zR)).
      { rewrite HzL_val, HzR_val.
        assert (He : (F.opp (SQRT_M1 * Fone) * P)%F = F.opp (SQRT_M1 * Fone * P)%F) by field.
        rewrite He. apply is_negative_opp_nonzero. rewrite <- HzR_val. exact HnzR. }
      rewrite HsignL.
      assert (HML : (iL * aL * (iL * eL) * eL)%F = SQRT_M1)
        by (transitivity (SQRT_M1 * Fone)%F; [ rewrite <- HsqL; field | field ]).
      assert (HMR : (iR * aR * (iR * P) * P)%F = SQRT_M1)
        by (transitivity (SQRT_M1 * Fone)%F; [ rewrite <- HsqR; field | field ]).
      rewrite HML, HMR.
      assert (Hmag : (iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))%F
                   = (iR * P * (iR * P))%F).
      { apply (mul_cancel_l aR _ _ HaRnz).
        transitivity ((aL * (eL * eL) * iL * iL)
          * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F.
        { rewrite HeLsq.
          assert (Hexp : (aR * (iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D)))%F
            = ((aL * aR) * (aL * iL * iL) * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F) by field.
          rewrite Hexp, HaLaR. field. }
        { rewrite HsqL, K2.
          assert (Hr : (aR * (iR * P * (iR * P)))%F = (aR * (P * P) * iR * iR)%F) by field.
          rewrite Hr, HsqR. field. } }
      assert (Hmag2 : (iL * eL * (iL * eL))%F
                    = (iR * aR * INVSQRT_A_MINUS_D * (iR * aR * INVSQRT_A_MINUS_D))%F).
      { apply (mul_cancel_l aL _ _ HaLnz).
        transitivity ((aR * (P * P) * iR * iR)
          * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F.
        { rewrite HsqR, K2.
          assert (Hr : (aL * (iL * eL * (iL * eL)))%F = (aL * (eL * eL) * iL * iL)%F) by field.
          rewrite Hr, HsqL. field. }
        { assert (Hr : (aL * (iR * aR * INVSQRT_A_MINUS_D * (iR * aR * INVSQRT_A_MINUS_D)))%F
            = ((aL * aR) * (aR * iR * iR) * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F) by field.
          rewrite Hr, HaLaR.
          assert (Ht : (P * P * (E.a - E.d) * (aR * iR * iR)
                        * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F
            = ((aR * (P * P) * iR * iR)
               * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F) by field.
          rewrite Ht, HsqR. field. } }
      destruct (is_negative zR) eqn:EzR; simpl negb; cbn match.
      * (* zR negative: LHS no-rotate, RHS rotate; inner args carry an extra SQRT_M1. *)
        assert (HRA : (Qy * SQRT_M1 * SQRT_M1)%F = F.opp Qy)
          by (assert (Hr : (Qy * SQRT_M1 * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qy)%F) by field;
              rewrite Hr, SQRT_M1_sq; field).
        rewrite HRA. rewrite (is_negative_opp_nonzero _ HQynz).
        destruct Hcval as [Hcv | Hcv].
        { assert (HLA : (c * Qy * SQRT_M1)%F = F.opp Qy) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qy * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HLB : (c * Qx)%F = (Qx * SQRT_M1)%F) by (rewrite Hcv; field).
          rewrite HLA, HLB. rewrite (is_negative_opp_nonzero _ HQynz).
          destruct (is_negative Qy); simpl negb; cbn match.
          { transitivity ((iL * eL * (iL * eL))
              * ((Fone - Qx * SQRT_M1) * (Fone - Qx * SQRT_M1)))%F;
              [ field | rewrite Hmag2; field ]. }
          { transitivity ((iL * eL * (iL * eL))
              * ((Fone - F.opp (Qx * SQRT_M1)) * (Fone - F.opp (Qx * SQRT_M1))))%F;
              [ field | rewrite Hmag2; field ]. } }
        { assert (HLA : (c * Qy * SQRT_M1)%F = Qy) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qy * SQRT_M1)%F = (F.opp (SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HLB : (c * Qx)%F = F.opp (Qx * SQRT_M1)%F) by (rewrite Hcv; field).
          rewrite HLA, HLB.
          destruct (is_negative Qy); simpl negb; cbn match.
          { assert (Hyy : (F.opp (F.opp (Qx * SQRT_M1)))%F = (Qx * SQRT_M1)%F) by field.
            rewrite Hyy.
            transitivity ((iL * eL * (iL * eL))
              * ((Fone - Qx * SQRT_M1) * (Fone - Qx * SQRT_M1)))%F;
              [ field | rewrite Hmag2; field ]. }
          { transitivity ((iL * eL * (iL * eL))
              * ((Fone - F.opp (Qx * SQRT_M1)) * (Fone - F.opp (Qx * SQRT_M1))))%F;
              [ field | rewrite Hmag2; field ]. } }
      * (* zR not negative: LHS rotate, RHS no-rotate. *)
        destruct Hcval as [Hcv | Hcv].
        { assert (HA : (c * Qx * SQRT_M1 * SQRT_M1)%F = F.opp (Qx * SQRT_M1)%F) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qx * SQRT_M1 * SQRT_M1)%F = (SQRT_M1 * (SQRT_M1 * SQRT_M1) * Qx)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HB : (c * Qy * SQRT_M1)%F = F.opp Qy) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qy * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          rewrite HA, HB.
          assert (HQxSnz : (Qx * SQRT_M1)%F <> Fzero) by (intro Hk;
            apply mul_zero_factor in Hk; destruct Hk as [Hk|Hk];
            [apply HQxnz; exact Hk | apply SQRT_M1_nz; exact Hk]).
          rewrite (is_negative_opp_nonzero _ HQxSnz).
          destruct (is_negative (Qx * SQRT_M1)); simpl negb; cbn match.
          { transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * ((Fone - F.opp Qy) * (Fone - F.opp Qy)))%F; [ field | rewrite Hmag; field ]. }
          { assert (Hyy : (F.opp (F.opp Qy))%F = Qy) by field. rewrite Hyy.
            transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * ((Fone - Qy) * (Fone - Qy)))%F; [ field | rewrite Hmag; field ]. } }
        { assert (HA : (c * Qx * SQRT_M1 * SQRT_M1)%F = (Qx * SQRT_M1)%F) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qx * SQRT_M1 * SQRT_M1)%F = (F.opp (SQRT_M1 * (SQRT_M1 * SQRT_M1)) * Qx)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HB : (c * Qy * SQRT_M1)%F = Qy) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qy * SQRT_M1)%F = (F.opp (SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          rewrite HA, HB.
          destruct (is_negative (Qx * SQRT_M1)); cbn match.
          { transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * ((Fone - F.opp Qy) * (Fone - F.opp Qy)))%F; [ field | rewrite Hmag; field ]. }
          { transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * ((Fone - Qy) * (Fone - Qy)))%F; [ field | rewrite Hmag; field ]. } }
Qed.
