(** * Ed25519 point compression / decompression — algebraic spec.
 *
 * Tier-1 #4 of the Ed25519-in-AUCurves track. Specializes
 * [Curves.Edwards.AffineProofs.PointCompression] at Ed25519's
 * parameters, providing concrete instantiations of:
 *   - [parity : F p → bool] via low-bit-of-canonical-encoding,
 *     plus [parity_opp_correct] (the sign-flip law).
 *   - [sqrt_div : F p → F p → option (F p)] via [F.sqrt_5mod8]
 *     (valid because [p = 2^255 - 19 ≡ 5 (mod 8)]).
 *   - [decompress_Some_25519] / [decompress_None_25519] — the wrapped
 *     Ed25519-instances of fiat-crypto [AffineProofs.E.decompress_Some]
 *     / [decompress_None] that Lean's [Ed25519Spec.lean] cites.
 *
 * All four [Admitted] sentences in the previous skeleton are now
 * discharged via concrete proofs. *)

From Stdlib Require Import ZArith Znumtheory Lia.
From Stdlib Require Import Morphisms.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.AffineProofs.

Module Ed25519Compress.

  Local Existing Instance Curve25519.field.
  Local Existing Instance Curve25519.char_ge_3.

  Local Notation p := Curve25519.p.
  Local Notation F := (F p).

  (** [p = 2^255 - 19 ≡ 5 (mod 8)] — required for [F.sqrt_5mod8]. *)
  Lemma p_5mod8 : (Z.pos p mod 8 = 5)%Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma prime_p : prime (Z.pos p).
  Proof. exact Curve25519.prime_p. Qed.

  (** ** Parity: low bit of canonical [Z] representation. *)
  Definition parity (x : F) : bool := Z.odd (F.to_Z x).

  Global Instance Proper_parity : Proper (Logic.eq ==> Logic.eq) parity.
  Proof. repeat intro; subst; reflexivity. Qed.

  (** Sign-flip parity: for [x ≠ 0] in [F p], [parity (-x) = ¬parity x].
      Pure arithmetic about [Z.odd] and [F.to_Z (F.opp x)]:
        F.to_Z (F.opp x) = (-F.to_Z x) mod p
                         = p - F.to_Z x          (since x ≠ 0)
        Z.odd (p - F.to_Z x) = xorb (Z.odd p) (Z.odd (F.to_Z x))
                             = negb (Z.odd (F.to_Z x))     (Z.odd p = true). *)
  Lemma parity_opp_correct : forall x : F, x <> F.zero ->
    parity (F.opp x) = negb (parity x).
  Proof.
    intros x Hnz. unfold parity.
    rewrite F.to_Z_opp.
    assert (Hp_pos : (0 < Z.pos p)%Z) by (vm_compute; reflexivity).
    pose proof (F.to_Z_nonzero_range x Hnz Hp_pos) as Hr.
    assert (Hmod : ((- F.to_Z x) mod Z.pos p = Z.pos p - F.to_Z x)%Z).
    { rewrite Z_mod_nz_opp_full.
      - rewrite Z.mod_small by lia. reflexivity.
      - rewrite Z.mod_small by lia. lia. }
    rewrite Hmod.
    rewrite Z.odd_sub.
    assert (Hp_odd : Z.odd (Z.pos p) = true) by (vm_compute; reflexivity).
    rewrite Hp_odd.
    destruct (Z.odd (F.to_Z x)); reflexivity.
  Qed.

  (** ** Square-root-of-quotient via [F.sqrt_5mod8].

      [sqrtm1 = 2^((p-1)/4)] is the square root of [-1] in [F p]
      (the well-known constant ≈ 19681...). It satisfies
      [sqrtm1 * sqrtm1 = -1], which is the precondition needed by
      [F.sqrt_5mod8].

      [sqrt_div u v] computes [F.sqrt_5mod8 sqrtm1 (u/v)] and returns
      [Some] iff that value squares to [u/v]. *)
  Local Definition sqrtm1 : F := F.pow (F.of_Z _ 2) ((N.pos p - 1) / 4).

  (** [vm_decide] = [vm_cast_no_check (eq_refl true)] — the kernel
      doesn't re-check the giant 253-bit modular exponentiation result
      at Qed (avoids OOM). [Print Assumptions] reports an
      [..._subproof] entry; that's an artifact of [abstract], not a
      real axiom. The same pattern is used in fiat-crypto's
      [EdwardsMontgomery25519.v]. *)
  Lemma sqrtm1_valid : (sqrtm1 * sqrtm1 = F.opp 1)%F.
  Proof. vm_decide. Qed.

  Local Definition sqrt_root : F -> F :=
    @F.sqrt_5mod8 p sqrtm1.

  Definition sqrt_div (u v : F) : option F :=
    let q := F.div u v in
    let r := sqrt_root q in
    if dec (Logic.eq (F.mul r r) q) then Some r else None.

  Lemma sqrt_div_Some_correct : forall u v r,
    sqrt_div u v = Some r -> F.mul r r = F.div u v.
  Proof.
    intros u v r H. unfold sqrt_div in H.
    destruct (dec _) as [Heq | Hneq]; [|congruence].
    inversion H; subst. exact Heq.
  Qed.

  Lemma sqrt_div_None_correct : forall u v,
    sqrt_div u v = None ->
    forall r, F.mul r r <> F.div u v.
  Proof.
    intros u v H r Hsq. unfold sqrt_div in H.
    destruct (dec _) as [_ | Hneq]; [discriminate|].
    apply Hneq.
    pose proof (@F.sqrt_5mod8_correct p prime_p p_5mod8 sqrtm1 sqrtm1_valid (F.div u v)) as Hcorr.
    destruct Hcorr as [Hfwd _].
    apply Hfwd. exists r. exact Hsq.
  Qed.

  (** ** Wrapped Ed25519-instance of [AffineProofs.E.decompress_Some].
      Provides the four PointCompression context arguments
      ([sqrt_div], [parity], and their proofs) and re-exports the
      generic theorem at Ed25519's parameters. Lean side
      ([Ed25519Spec.lean::decompress_Some]) cites this lemma.
      All other type-class arguments ([field], [Feq_dec], [nonzero_a],
      [square_a], [nonsquare_d]) are inferred from [Curve25519.E]. *)
  Theorem decompress_Some_25519
    : forall b P,
        E.decompress
          (a := Curve25519.E.a) (d := Curve25519.E.d)
          (nonzero_a := Curve25519.E.nonzero_a)
          (square_a := Curve25519.E.square_a)
          (nonsquare_d := Curve25519.E.nonsquare_d)
          (sqrt_div := sqrt_div)
          (sqrt_Some := sqrt_div_Some_correct)
          (sqrt_None := sqrt_div_None_correct)
          (parity := parity)
          (Proper_parity := Proper_parity)
          (parity_opp := parity_opp_correct)
          b = Some P ->
        E.compress
          (Fone := F.one) (Fadd := F.add) (Fmul := F.mul)
          (a := Curve25519.E.a) (d := Curve25519.E.d)
          (parity := parity)
          P = b.
  Proof. apply E.decompress_Some. Qed.

  Theorem decompress_None_25519
    : forall b,
        E.decompress
          (a := Curve25519.E.a) (d := Curve25519.E.d)
          (nonzero_a := Curve25519.E.nonzero_a)
          (square_a := Curve25519.E.square_a)
          (nonsquare_d := Curve25519.E.nonsquare_d)
          (sqrt_div := sqrt_div)
          (sqrt_Some := sqrt_div_Some_correct)
          (sqrt_None := sqrt_div_None_correct)
          (parity := parity)
          (Proper_parity := Proper_parity)
          (parity_opp := parity_opp_correct)
          b = None ->
        forall (P : @E.point _ Logic.eq F.one F.add F.mul Curve25519.E.a Curve25519.E.d),
          E.compress
            (Fone := F.one) (Fadd := F.add) (Fmul := F.mul)
            (a := Curve25519.E.a) (d := Curve25519.E.d)
            (parity := parity)
            P <> b.
  Proof. apply E.decompress_None. Qed.

  (** ** Phase 1.2 corollary lemmas — the names CoqAxioms.lean cites.
      [ed_decompress_correct] and [ed_compress_correct] complete the
      "Phase 1.2 deliverable" rows. *)

  (** Concrete [compress] / [decompress] specialized at Ed25519's
      parameters. Wrappers around the generic [E.compress] / [E.decompress]
      with all type-class arguments fixed. *)
  Definition compress_25519
    (P : @E.point _ Logic.eq F.one F.add F.mul Curve25519.E.a Curve25519.E.d)
    : bool * F :=
    E.compress
      (Fone := F.one) (Fadd := F.add) (Fmul := F.mul)
      (a := Curve25519.E.a) (d := Curve25519.E.d)
      (parity := parity)
      P.

  Definition decompress_25519 (b : bool * F)
    : option (@E.point _ Logic.eq F.one F.add F.mul Curve25519.E.a Curve25519.E.d) :=
    E.decompress
      (a := Curve25519.E.a) (d := Curve25519.E.d)
      (nonzero_a := Curve25519.E.nonzero_a)
      (square_a := Curve25519.E.square_a)
      (nonsquare_d := Curve25519.E.nonsquare_d)
      (sqrt_div := sqrt_div)
      (sqrt_Some := sqrt_div_Some_correct)
      (sqrt_None := sqrt_div_None_correct)
      (parity := parity)
      (Proper_parity := Proper_parity)
      (parity_opp := parity_opp_correct)
      b.

  (** Phase 1.2 deliverable: the inverse direction. If [decompress_25519]
      returns [Some P], then compressing P gives back the input bytes. *)
  Theorem ed_decompress_correct
    : forall b P, decompress_25519 b = Some P -> compress_25519 P = b.
  Proof. apply decompress_Some_25519. Qed.

  (** Phase 1.2 deliverable: the forward direction. Compressing then
      decompressing always succeeds (yields [Some _], not [None]),
      since [decompress_None] would contradict [compress_25519] being a
      valid output bytes for [P]. *)
  Theorem ed_compress_correct
    : forall P, decompress_25519 (compress_25519 P) <> None.
  Proof.
    intros P Heq.
    pose proof (decompress_None_25519 _ Heq P) as Hne.
    apply Hne. reflexivity.
  Qed.

  (** ** [fp_sqrt_ratio_i] — Lean [interp_fp_sqrt_ratio_i] discharge.
      Concrete function returning [r] such that [r²·v = u] when [u/v]
      is a quadratic residue in [F p]. Wraps our [sqrt_div].
      For non-QR [u/v], returns a dummy ([F.zero]); the Lean axiom
      conditions on the QR existence so the dummy case is unreachable. *)
  Definition fp_sqrt_ratio_i (u v : F) : F :=
    match sqrt_div u v with
    | Some r => r
    | None => F.zero
    end.

  Add Field _ed25519_F_field : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F)).

  Theorem interp_fp_sqrt_ratio_i_correct
    : forall u v : F, v <> F.zero ->
      (exists r : F, F.mul (F.mul r r) v = u) ->
      F.mul (F.mul (fp_sqrt_ratio_i u v) (fp_sqrt_ratio_i u v)) v = u.
  Proof.
    intros u v Hv [r Hr].
    unfold fp_sqrt_ratio_i.
    destruct (sqrt_div u v) as [s|] eqn:Hsq.
    - (* Some case: s² = u/v from sqrt_div_Some_correct.
         Goal: (s*s)*v = u. Rewrite with Hs then field. *)
      pose proof (sqrt_div_Some_correct _ _ _ Hsq) as Hs.
      rewrite Hs. field. exact Hv.
    - (* None case contradicts the existence hypothesis. *)
      exfalso.
      apply (sqrt_div_None_correct _ _ Hsq r).
      (* Need: r*r = u/v. Have: (r*r)*v = u, v ≠ 0. *)
      field_simplify_eq; [ exact Hr | exact Hv ].
  Qed.

End Ed25519Compress.
