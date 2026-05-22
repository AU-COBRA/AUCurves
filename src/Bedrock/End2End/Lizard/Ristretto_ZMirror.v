(** * Ristretto_ZMirror — Phase B.5a equivalence of the Z-level Gallina
      mirror against the F_p-typed functional spec.
 *
 *  Bridges the two existing ristretto255 Gallina layers:
 *
 *  - [Bedrock.End2End.Lizard.RistrettoDecode.ristretto_decode_gallina]
 *      Z-level (list Byte.byte → list Byte.byte, returns 200-byte
 *      xyzt slot or bad_point); the layer that the RustCmd / bedrock2
 *      extraction sees.
 *
 *  - [Bedrock.Field.Synthesis.Examples.Ristretto255_Decode.ristretto_decode_coords]
 *      F_p-level (list Byte.byte → option (Fp * Fp), returns affine
 *      Edwards coordinates); the layer that downstream algebraic /
 *      security proofs cite.
 *
 *  Statement: the two decoders agree under the [F.to_Z] injection.
 *  Specifically, the Z-mirror returns [pack_xyzt5 x y 1 x y] (resp.
 *  [bad_point]) iff the F_p decoder returns [Some (x, y)] (resp. [None]).
 *
 *  This is the SINGLE EQUIVALENCE that unblocks moving the 24 §A.2
 *  per-vector rejection checks off Rocq's kernel and onto [cargo test]
 *  in [curve25519-jasmin-rs] (per [BLS/writeup/RISTRETTO255_B5_ZMIRROR_PLAN.md]).
 *
 *  Proof structure: trace both decoders line-by-line under [F.to_Z].
 *  Each algorithmic step ([ss = s²], [u1 = 1 - ss], [sqrt_ratio_m1],
 *  etc.) has the same shape in both layers; the proof is a [cbv zeta]
 *  + [f_equal] cascade plus rewriting under the [F.to_Z]
 *  homomorphism lemmas already in fiat-crypto.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Lizard.RistrettoConsts.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Require Import Bedrock.End2End.Lizard.RistrettoDecode.
Require Import Bedrock.End2End.Lizard.RistrettoEncode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Decode.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation Fp := (F.F (2^255 - 19)).

(* ========================================================================
   Section 1: [F.to_Z] homomorphism transport lemmas.

   These are statements of the [F.to_Z] homomorphism specialized to the
   ristretto algorithmic shape.  All follow from existing fiat-crypto
   [PrimeFieldTheorems] / [ModularArithmeticTheorems] machinery; we
   collect them under [Local Notation] for the per-step rewrite cascade
   in §3.

   Note on the [ed25519_p] vs [(2^255 - 19)] discrepancy: [ed25519_p]
   is the [Z] literal used by the Z-mirror, [(2^255 - 19)] is the
   notation used by [Fp = F.F (2^255 - 19)].  These are equal as [Z]
   literals; the rewrite cascade just folds one to the other via
   [unfold ed25519_p].
   ======================================================================== *)

Lemma ed25519_p_eq : ed25519_p = 2^255 - 19.
Proof. reflexivity. Qed.

(** [F.to_Z (F.of_Z _ z) = z mod p] — the canonicalisation step that
    bridges any [Z]-literal coming into the F_p layer. *)
Lemma F_to_Z_of_Z :
  forall z : Z, F.to_Z (F.of_Z (2^255 - 19) z) = z mod (2^255 - 19).
Proof. intro z. apply F.to_Z_of_Z. Qed.

(** Field-multiplication transports to Z-multiplication-mod-p. *)
Lemma F_to_Z_mul :
  forall x y : Fp,
    F.to_Z (F.mul x y) = (F.to_Z x * F.to_Z y) mod (2^255 - 19).
Proof. intros x y. apply F.to_Z_mul. Qed.

Lemma F_to_Z_add :
  forall x y : Fp,
    F.to_Z (F.add x y) = (F.to_Z x + F.to_Z y) mod (2^255 - 19).
Proof. intros x y. apply F.to_Z_add. Qed.

Lemma F_to_Z_sub :
  forall x y : Fp,
    F.to_Z (F.sub x y) = (F.to_Z x - F.to_Z y) mod (2^255 - 19).
Proof.
  intros x y.
  unfold F.sub. rewrite F.to_Z_add, F.to_Z_opp.
  rewrite Z.add_mod_idemp_r by (vm_compute; discriminate).
  f_equal; ring.
Qed.

Lemma F_to_Z_opp :
  forall x : Fp,
    F.to_Z (F.opp x) = (- F.to_Z x) mod (2^255 - 19).
Proof. intros x. apply F.to_Z_opp. Qed.

(** Helper: [pow_mod_pos b p m] computes [b^(Zpos p) mod m]. *)
Lemma pow_mod_pos_correct :
  forall (p : positive) (b m : Z),
    0 < m ->
    pow_mod_pos b p m = (b ^ Z.pos p) mod m.
Proof.
  induction p as [p IHp | p IHp | ]; intros b m Hm; simpl pow_mod_pos.
  - (* xI p : (((pow_mod_pos b p m * pow_mod_pos b p m) mod m) * b) mod m *)
    rewrite !IHp by exact Hm.
    rewrite Pos2Z.inj_xI.
    (* Goal: ((((b^p) mod m) * ((b^p) mod m)) mod m * b) mod m
             = (b ^ (2*Z.pos p + 1)) mod m *)
    rewrite <- Zmult_mod.
    (* Goal: ((b^p * b^p) mod m * b) mod m = (b^(2*Zpos p + 1)) mod m *)
    rewrite Z.mul_mod_idemp_l by lia.
    (* Goal: (b^p * b^p * b) mod m = (b^(2*Zpos p + 1)) mod m *)
    f_equal.
    replace (2 * Z.pos p + 1) with (Z.pos p + Z.pos p + 1) by lia.
    rewrite !Z.pow_add_r by (try lia; apply Pos2Z.pos_is_nonneg).
    rewrite Z.pow_1_r. ring.
  - (* xO p : (pow_mod_pos b p m * pow_mod_pos b p m) mod m *)
    rewrite !IHp by exact Hm.
    rewrite Pos2Z.inj_xO.
    (* Goal: ((b^p) mod m * ((b^p) mod m)) mod m = (b^(2*Zpos p)) mod m *)
    rewrite <- Zmult_mod.
    f_equal.
    replace (2 * Z.pos p) with (Z.pos p + Z.pos p) by lia.
    rewrite Z.pow_add_r by apply Pos2Z.pos_is_nonneg.
    reflexivity.
  - (* xH : b mod m = b^1 mod m *)
    rewrite Z.pow_1_r. reflexivity.
Qed.

(** [F.pow] transports to Z-level [pow_mod].
    Stated against the [Z] form of the exponent ([Z.to_N exp]) to match
    the Z-mirror's [pow_mod] which takes [Z]. *)
Lemma F_to_Z_pow_pow_mod :
  forall (x : Fp) (n : Z),
    0 <= n ->
    F.to_Z (F.pow x (Z.to_N n)) = pow_mod (F.to_Z x) n (2^255 - 19).
Proof.
  intros x n Hn.
  (* LHS by fiat-crypto's F.to_Z_pow:
       F.to_Z (F.pow x k) = (F.to_Z x ^ Z.of_N k) mod (2^255 - 19) *)
  rewrite F.to_Z_pow.
  rewrite Z2N.id by exact Hn.
  (* Goal: (F.to_Z x ^ n) mod (2^255 - 19) = pow_mod (F.to_Z x) n (2^255 - 19) *)
  assert (Hp : (0 < 2^255 - 19)%Z) by (vm_compute; reflexivity).
  destruct n as [|p|p].
  - (* n = 0 : pow_mod base 0 m = 1 mod m, and base^0 = 1 *)
    simpl pow_mod. rewrite Z.pow_0_r. reflexivity.
  - (* n = Zpos p : pow_mod base (Zpos p) m = pow_mod_pos base p m *)
    simpl pow_mod. symmetry. apply pow_mod_pos_correct.
    (* The modulus appears as a literal; show it's positive. *)
    vm_compute; reflexivity.
  - (* n = Zneg p : impossible by Hn *)
    exfalso. lia.
Qed.

(** [pow_mod_pos] is invariant under [b mod m] of the base. *)
Lemma pow_mod_pos_base_mod : forall (p : positive) (b m : Z),
  0 < m ->
  pow_mod_pos (b mod m) p m = pow_mod_pos b p m.
Proof.
  intros p b m Hm. rewrite !pow_mod_pos_correct by exact Hm.
  rewrite <- Z.mod_pow_l. rewrite Z.mod_mod by lia.
  rewrite Z.mod_pow_l. reflexivity.
Qed.

(** [pow_mod] is invariant under [b mod m] of the base. *)
Lemma pow_mod_base_mod : forall (b e m : Z),
  0 < m ->
  pow_mod (b mod m) e m = pow_mod b e m.
Proof.
  intros b e m Hm. destruct e; simpl; auto using pow_mod_pos_base_mod.
Qed.

(* ========================================================================
   Section 2: Parser equivalence.

   The Z-level [ristretto_parse_canonical_felem] and the F_p-level
   [bytes_to_canonical_F] are syntactically the same checks; we prove
   their option types correspond.
   ======================================================================== *)

(** ** Parsers agree under [F.to_Z], with sign-bit asymmetry.

    The Z-level [ristretto_parse_canonical_felem] INLINES the
    [is_negative s] rejection check (RFC 9496 §4.3.1 line 3), while
    the F_p-level [bytes_to_canonical_F] does NOT — it only checks
    length, bit 255, and the canonical range, leaving the
    [is_negative s] check to the F_p-layer decoder body.

    Hence:
      - both [Some]: byte string passes ALL rejection checks ⇒
        parsed values agree under [F.to_Z], AND is_negative is false.
      - Z [None], F [Some]: byte string passed length/bit255/range
        but failed Z's inline is_negative ⇒ F.to_Z s = le_combine bs
        AND ristretto_is_negative (le_combine bs) = true.
      - both [None]: failed length, bit 255, or range — coincides.
      - Z [Some], F [None]: IMPOSSIBLE.  Z's accepts ⇒ length=32 ∧
        bit255=0 ∧ z < ed25519_p ∧ ¬is_negative.  F's accepts iff
        length=32 ∧ bit255=0 ∧ z < 2^255-19 = ed25519_p.  Z strictly
        stronger.

    Bug fix 2026-05-22 (B.5a agent finding): the previous statement
    asserted a strict bijection and was provably FALSE (counter-
    example: integer 1 — low bit set).  Replaced with the
    asymmetry-aware form, which is what downstream callers actually
    need (the decoder body case-splits on is_negative right after
    parse, absorbing the asymmetry there). *)
Lemma parse_canonical_felem_correspondence :
  forall bs : list Byte.byte,
    match ristretto_parse_canonical_felem bs, bytes_to_canonical_F bs with
    | Some z, Some s =>
        F.to_Z s = z /\ ristretto_is_negative z = false
    | None, Some s =>
        F.to_Z s = le_combine bs /\
        ristretto_is_negative (le_combine bs) = true
    | None, None => True
    | Some _, None => False
    end.
Proof.
  intros bs.
  unfold ristretto_parse_canonical_felem, bytes_to_canonical_F.
  destruct (Nat.eqb (length bs) 32) eqn:Hlen32; [|exact I].
  destruct (Z.testbit (le_combine bs) 255) eqn:Hbit; [exact I|].
  destruct (Z.ltb (le_combine bs) ed25519_p) eqn:Hlt_p;
    destruct (Z.ltb (le_combine bs) (2^255 - 19)) eqn:Hlt_p2.
  - (* both: z < p *)
    assert (Hbnd : 0 <= le_combine bs < 2^255 - 19).
    { split; [apply (proj1 (le_combine_bound bs))|].
      apply Z.ltb_lt in Hlt_p2; exact Hlt_p2. }
    destruct (ristretto_is_negative (le_combine bs)) eqn:Hneg.
    + (* Z = None (rejected via is_negative), F = Some *)
      split; [|reflexivity].
      rewrite F_to_Z_of_Z. apply Z.mod_small; lia.
    + (* both Some *)
      split; [|exact Hneg].
      rewrite F_to_Z_of_Z. apply Z.mod_small; lia.
  - exfalso. apply Z.ltb_lt in Hlt_p. apply Z.ltb_ge in Hlt_p2.
    change ed25519_p with (2^255 - 19) in Hlt_p. lia.
  - exfalso. apply Z.ltb_lt in Hlt_p2. apply Z.ltb_ge in Hlt_p.
    change ed25519_p with (2^255 - 19) in Hlt_p. lia.
  - exact I.
Qed.

(** ** [ristretto_is_negative] on a [Z] in [0, p) equals [is_negative]
    on the [F_p] embedding (bit 0 unchanged by the embedding). *)
Lemma is_negative_correspondence :
  forall z : Z, 0 <= z < (2^255 - 19) ->
    ristretto_is_negative z = is_negative (F.of_Z _ z).
Proof.
  intros z [Hlo Hhi].
  unfold ristretto_is_negative, is_negative.
  rewrite F_to_Z_of_Z. rewrite Z.mod_small by lia.
  reflexivity.
Qed.

(* ========================================================================
   Section 3: sqrt_ratio_m1 equivalence.

   Both decoders call a square-root-ratio helper.  The Z-level
   [ristretto_sqrt_ratio_m1] uses [pow_mod]; the F_p-level
   [sqrt_ratio_m1] uses [F.pow].  They agree under [F.to_Z], modulo
   the parser-equivalence's identification of the input.
   ======================================================================== *)

(** PROGRESS (B.5a, 2026-05-22):

    The Z-layer [was_square] bug is FIXED upstream in
    [RistrettoHelpers.ristretto_sqrt_ratio_m1] (now uses
    [correct_sign_sqrt || flipped_sign_sqrt], matching RFC 9496 §3.1.3
    and the F-layer).  The two implementations are now structurally
    parallel under [F.to_Z].

    The remaining proof is mechanical (~150-200 LoC of [F_to_Z_*]
    rewrites cascading through v3, v7, pow_val, r0, check,
    correct_sign_sqrt, flipped_sign_sqrt, flipped_sign_sqrt_i, r1, r).
    Shape:
      - Open both implementations with [unfold].
      - Apply [F_to_Z_pow_pow_mod] at the [pow_val]/[F.pow] step.
      - Chain [F_to_Z_mul]/[F_to_Z_sub]/[F_to_Z_opp]/[F_to_Z_of_Z]
        through r0, check, neg_u, neg_iu.
      - The eqb comparisons reduce to [Z.eqb (F.to_Z _) (F.to_Z _)],
        matching by [F.eq_to_Z_iff] / [Z.eqb_eq].
      - The conditional [r1] dispatch matches branch-by-branch.
      - The abs/canonical_negate dispatch matches via
        [is_negative_correspondence] applied to [r1 mod p].

    Not closed this pass due to wall-time budget on the cascading
    rewrite proof (each iteration is ~10 min of compile cycle to
    validate, and the proof body involves >100 sequential rewrites
    where any single failure restarts the cycle).
*)
Lemma sqrt_ratio_m1_correspondence :
  forall (uZ vZ : Z) (uF vF : Fp),
    uZ = F.to_Z uF ->
    vZ = F.to_Z vF ->
    let '(wsZ, rZ) := ristretto_sqrt_ratio_m1 uZ vZ in
    let '(wsF, rF) := sqrt_ratio_m1 uF vF in
    wsZ = wsF /\ rZ = F.to_Z rF.
Proof.
  intros uZ vZ uF vF Hu Hv. subst uZ vZ.
  unfold ristretto_sqrt_ratio_m1, sqrt_ratio_m1.
  cbn beta iota.
  assert (Hp_pos : 0 < ed25519_p) by (vm_compute; reflexivity).
  assert (Hppos : (0 < Z.pos (2^255-19))%Z) by (vm_compute; reflexivity).
  pose proof (F.to_Z_range uF Hppos) as Hu_rng.
  pose proof (F.to_Z_range vF Hppos) as Hv_rng.
  change (Z.pos (2^255-19))%Z with ed25519_p in *.
  assert (He_nn : 0 <= (2^255-19-5)/8) by (vm_compute; discriminate).
  set (sZ := F.to_Z vF) in *.
  set (uZv := F.to_Z uF) in *.
  (* Establish F.to_Z of F-level intermediates equal Z-level intermediates *)
  assert (Hv3 : F.to_Z (vF * vF * vF) = (sZ * sZ * sZ) mod ed25519_p) by
    (rewrite !F_to_Z_mul; change (2^255-19) with ed25519_p;
     rewrite Z.mul_mod_idemp_l by lia; reflexivity).
  assert (Hv7 : F.to_Z (vF * vF * vF * (vF * vF * vF) * vF) =
                ((sZ * sZ * sZ) mod ed25519_p * ((sZ * sZ * sZ) mod ed25519_p) * sZ) mod ed25519_p) by
    (rewrite !F_to_Z_mul; change (2^255-19) with ed25519_p; fold sZ;
     rewrite <- Hv3; rewrite Z.mul_mod_idemp_l by lia; reflexivity).
  assert (HuvF : F.to_Z (uF * (vF * vF * vF * (vF * vF * vF) * vF)) =
                 (uZv * (((sZ * sZ * sZ) mod ed25519_p * ((sZ * sZ * sZ) mod ed25519_p) * sZ) mod ed25519_p)) mod ed25519_p) by
    (rewrite F_to_Z_mul; change (2^255-19) with ed25519_p;
     rewrite Hv7; reflexivity).
  assert (Hpow : F.to_Z ((uF * (vF * vF * vF * (vF * vF * vF) * vF))
                          ^ Z.to_N ((2^255-19-5)/8))
               = pow_mod ((uZv * (((sZ * sZ * sZ) mod ed25519_p
                       * ((sZ * sZ * sZ) mod ed25519_p) * sZ) mod ed25519_p)) mod ed25519_p)
                         ((ed25519_p - 5)/8) ed25519_p) by
    (rewrite F_to_Z_pow_pow_mod by exact He_nn;
     rewrite HuvF;
     change (2^255-19) with ed25519_p; reflexivity).
  set (powZ := pow_mod ((uZv * (((sZ * sZ * sZ) mod ed25519_p
                       * ((sZ * sZ * sZ) mod ed25519_p) * sZ) mod ed25519_p)) mod ed25519_p)
                       ((ed25519_p - 5)/8) ed25519_p).
  assert (Hr0 : F.to_Z (uF * (vF * vF * vF) *
                       (uF * (vF * vF * vF * (vF * vF * vF) * vF))
                       ^ Z.to_N ((2^255-19-5)/8))
              = (uZv * ((sZ * sZ * sZ) mod ed25519_p) * powZ) mod ed25519_p).
  { rewrite F_to_Z_mul. rewrite Hpow. fold powZ.
    rewrite F_to_Z_mul. change (2^255-19) with ed25519_p.
    rewrite Hv3. fold uZv.
    rewrite (Z.mul_mod_idemp_l (uZv * _) _) by lia.
    reflexivity. }
  set (r0Z := (uZv * ((sZ * sZ * sZ) mod ed25519_p) * powZ) mod ed25519_p).
  (* Introduce r0F as a local abbreviation via remember from the goal *)
  remember (uF * (vF * vF * vF) *
              (uF * (vF * vF * vF * (vF * vF * vF) * vF))
              ^ Z.to_N ((2^255-19-5)/8))%F as r0F eqn:Hr0F_def.
  assert (Hr0F : F.to_Z r0F = r0Z) by (subst r0F; exact Hr0).
  assert (Hcheck : F.to_Z (vF * r0F * r0F) = (sZ * r0Z * r0Z) mod ed25519_p) by
    (rewrite !F_to_Z_mul; change (2^255-19) with ed25519_p;
     rewrite Hr0F;
     rewrite Z.mul_mod_idemp_l by lia; reflexivity).
  (* Z-level uses uZv mod p which equals uZv (uZv in [0,p)) *)
  assert (Hu_mod : uZv mod ed25519_p = uZv) by (apply Z.mod_small; lia).
  (* F.to_Z (F.opp uF) = (- uZv) mod p = canonical_negate uZv *)
  assert (Hopp : F.to_Z (F.opp uF) = ristretto_canonical_negate uZv).
  { rewrite F_to_Z_opp. change (2^255-19) with ed25519_p.
    unfold ristretto_canonical_negate.
    fold uZv.
    rewrite <- (Z.mod_add (- uZv) 1 ed25519_p) by lia.
    f_equal. lia. }
  (* F.to_Z SQRT_M1 = ristretto_SQRT_M1 *)
  assert (HSQRT : F.to_Z SQRT_M1 = ristretto_SQRT_M1).
  { unfold SQRT_M1, ristretto_SQRT_M1.
    rewrite F_to_Z_of_Z. apply Z.mod_small. lia. }
  (* F.to_Z (SQRT_M1 * uF) = (ristretto_SQRT_M1 * uZv) mod p *)
  assert (HSQu : F.to_Z (SQRT_M1 * uF) = (ristretto_SQRT_M1 * uZv) mod ed25519_p) by
    (rewrite F_to_Z_mul; change (2^255-19) with ed25519_p;
     rewrite HSQRT; reflexivity).
  (* F.to_Z (F.opp (SQRT_M1 * uF)) = canonical_negate ((SQRT_M1 * uZv) mod p) *)
  assert (HoppSQu : F.to_Z (F.opp (SQRT_M1 * uF))
                    = ristretto_canonical_negate ((ristretto_SQRT_M1 * uZv) mod ed25519_p)).
  { rewrite F_to_Z_opp. change (2^255-19) with ed25519_p.
    rewrite HSQu.
    unfold ristretto_canonical_negate.
    set (k := (ristretto_SQRT_M1 * uZv) mod ed25519_p).
    assert (Hk_rng : 0 <= k < ed25519_p) by
      (subst k; split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound]; lia).
    rewrite <- (Z.mod_add (- k) 1 ed25519_p) by lia.
    f_equal. lia. }
  (* Now rewrite the check expression and booleans *)
  rewrite Hcheck.
  fold uZv. rewrite Hopp.
  (* For F.to_Z (F.opp (SQRT_M1 * uF)) on the RHS — fold via HoppSQu *)
  rewrite HoppSQu.
  rewrite Hu_mod.
  set (checkZ := (sZ * r0Z * r0Z) mod ed25519_p) in *.
  set (B1 := (checkZ =? uZv)).
  set (B2 := (checkZ =? ristretto_canonical_negate uZv)).
  set (B3 := (checkZ =? ristretto_canonical_negate ((ristretto_SQRT_M1 * uZv) mod ed25519_p))).
  (* Now split into was_square equality and r-value equality *)
  split.
  - (* was_square equality *)
    reflexivity.
  - (* r-value equality *)
    assert (Hr0SQF : F.to_Z (F.mul r0F SQRT_M1)
                   = (r0Z * ristretto_SQRT_M1) mod ed25519_p) by
      (rewrite F_to_Z_mul; change (2^255-19) with ed25519_p;
       rewrite Hr0F, HSQRT; reflexivity).
    (* Helper: prove abs/canonical_negate match for any r1F:Fp, r1Z:Z
       with F.to_Z r1F = r1Z. *)
    assert (Habsmatch : forall (r1F : Fp) (r1Z : Z),
                F.to_Z r1F = r1Z ->
                (if ristretto_is_negative r1Z
                 then ristretto_canonical_negate r1Z else r1Z)
                = F.to_Z (if is_negative r1F then F.opp r1F else r1F)).
    { intros r1F r1Z Hrf.
      assert (Hr1Z_rng : 0 <= r1Z < ed25519_p).
      { subst r1Z. change ed25519_p with (Z.pos (2^255-19)).
        apply F.to_Z_range. lia. }
      unfold is_negative, ristretto_is_negative. rewrite Hrf.
      destruct (Z.testbit r1Z 0) eqn:Hneg.
      - unfold ristretto_canonical_negate.
        rewrite F_to_Z_opp. change (2^255-19) with ed25519_p.
        rewrite Hrf.
        rewrite <- (Z.mod_add (- r1Z) 1 ed25519_p) by lia.
        f_equal. lia.
      - symmetry. exact Hrf. }
    (* Case analysis on B1, B2, B3 *)
    destruct B1 eqn:HB1.
    + apply (Habsmatch r0F r0Z Hr0F).
    + destruct B2 eqn:HB2.
      * apply (Habsmatch (F.mul r0F SQRT_M1) ((r0Z * ristretto_SQRT_M1) mod ed25519_p) Hr0SQF).
      * destruct B3 eqn:HB3.
        -- apply (Habsmatch (F.mul r0F SQRT_M1) ((r0Z * ristretto_SQRT_M1) mod ed25519_p) Hr0SQF).
        -- apply (Habsmatch r0F r0Z Hr0F).
Qed.

(* ========================================================================
   Section 4: Main equivalence theorem.

   Statement: the Z-level decoder's output is exactly the [pack_xyzt5]
   image of the F_p-level decoder's output (or the bad-point on the
   rejection branch).
   ======================================================================== *)

(** ** The B.5a main theorem.

    [ristretto_decode_gallina] (Z-level, 200-byte xyzt output) agrees
    with [ristretto_decode_coords] (F_p-level, [option (Fp * Fp)]
    output) under the [pack_xyzt5 ∘ F.to_Z] embedding. *)
(** PROGRESS (B.5a, blocked on Lemmas 2 and 3):

    The main decoder mirror theorem is the composition of the parser
    correspondence (Lemma [parse_canonical_felem_correspondence]) and
    the [sqrt_ratio_m1] correspondence — both of which are blocked
    above on a statement-level fix (parser) and an algorithmic fix
    in [RistrettoHelpers] (sqrt_ratio_m1's [was_square]).  Once
    those land, the cascade is mechanical:

      * Unfold both decoders.
      * Apply the (corrected) parser correspondence to align the
        [Some s] / [Some (F.of_Z _ z)] case with the [is_negative]
        rejection that the Z-layer inlined.
      * For each let-binding (ss, u1, u2, u2_sqr, u1_sq, v, den,
        was_square, I_val, Dx, Dy, x_raw, x, y, t), rewrite under
        [F_to_Z_*] homomorphism lemmas already in this file's §1.
      * The failure-disjunct dispatch closes via
        [is_negative_correspondence] (already Qed above) for the
        [is_negative t] check, and direct [Z.eqb] computation for the
        [y = 0] check (matches [F.to_Z y = 0] by [F.to_Z_0] /
        eq_to_Z_iff).
      * On success, the goal reduces to a pure
        [f_equal] / [pack_xyzt5] congruence under the
        per-coordinate [F.to_Z] image.

    Estimated 200-400 LoC, fully mechanical once 2 and 3 are unblocked.
*)
Theorem ristretto_decode_Z_mirror_correct :
  forall (bs : list Byte.byte),
    ristretto_decode_gallina bs =
      match ristretto_decode_coords bs with
      | None        => ristretto_bad_point
      | Some (x, y) =>
          pack_xyzt5 (F.to_Z x) (F.to_Z y) 1
                     (F.to_Z x) (F.to_Z y)
      end.
Proof.
  intros bs.
  unfold ristretto_decode_gallina, ristretto_decode_coords.
  pose proof (parse_canonical_felem_correspondence bs) as Hparse.
  destruct (ristretto_parse_canonical_felem bs) as [zS|] eqn:HparseZ;
  destruct (bytes_to_canonical_F bs) as [sF|] eqn:HparseF;
  [ idtac
  | contradiction Hparse
  | destruct Hparse as [Hsf_eq Hneg_t];
    replace (is_negative sF) with true;
    [ reflexivity
    | unfold is_negative; rewrite Hsf_eq; symmetry; exact Hneg_t ]
  | reflexivity ].
  destruct Hparse as [Hsf_eq Hneg_f]. subst zS.
  replace (is_negative sF) with false by (symmetry; exact Hneg_f).
  assert (Hd_eq : F.to_Z Curve25519.E.d = ed25519_d) by (vm_compute; reflexivity).
  assert (HFp_one : F.to_Z (F.of_Z (2^255-19) 1) = 1) by
    (rewrite F_to_Z_of_Z; reflexivity).
  assert (HFp_two : F.to_Z (F.of_Z (2^255-19) 2) = 2) by
    (rewrite F_to_Z_of_Z; reflexivity).
  assert (Hopp_mod_eq : forall x : Z,
    (- (x mod ed25519_p)) mod ed25519_p =
    (ed25519_p - x mod ed25519_p) mod ed25519_p) by
    (intros x;
     rewrite <- (Z.mod_add (- (x mod ed25519_p)) 1 ed25519_p) by (cbv; discriminate);
     f_equal; lia).
  set (ssZ := (F.to_Z sF * F.to_Z sF) mod ed25519_p) in *.
  set (u1Z := (1 - ssZ) mod ed25519_p) in *.
  set (u2Z := (1 + ssZ) mod ed25519_p) in *.
  set (u2_sqrZ := (u2Z * u2Z) mod ed25519_p) in *.
  set (u1_sqZ := (u1Z * u1Z) mod ed25519_p) in *.
  set (vZ := ((ed25519_p - (ed25519_d * u1_sqZ) mod ed25519_p) mod ed25519_p
              - u2_sqrZ) mod ed25519_p) in *.
  set (denZ := (vZ * u2_sqrZ) mod ed25519_p) in *.
  set (denF := ((F.opp (E.d * ((F.of_Z p 1 - sF * sF) * (F.of_Z p 1 - sF * sF))) -
                  (F.of_Z p 1 + sF * sF) * (F.of_Z p 1 + sF * sF)) *
                ((F.of_Z p 1 + sF * sF) * (F.of_Z p 1 + sF * sF)))%F) in *.
  assert (Hden_eq : F.to_Z denF = denZ).
  { unfold denF, denZ, vZ, u2_sqrZ, u1_sqZ, u2Z, u1Z, ssZ.
    repeat (rewrite F_to_Z_mul || rewrite F_to_Z_sub ||
            rewrite F_to_Z_add || rewrite F_to_Z_opp).
    rewrite !HFp_one, Hd_eq.
    change (2^255-19)%Z with ed25519_p.
    rewrite Hopp_mod_eq. reflexivity. }
  pose proof (sqrt_ratio_m1_correspondence 1 denZ (F.of_Z _ 1) denF
                (eq_sym HFp_one) (eq_sym Hden_eq)) as Hsqrt.
  destruct (ristretto_sqrt_ratio_m1 1 denZ) as [wsZ rZ] eqn:HsqrtZ.
  destruct (sqrt_ratio_m1 (F.of_Z _ 1) denF) as [wsF rF] eqn:HsqrtF.
  destruct Hsqrt as [Hws_eq Hr_eq]. subst wsZ. rewrite Hr_eq.
  set (DxZ := (F.to_Z rF * u2Z) mod ed25519_p) in *.
  set (DyZ := (F.to_Z rF * DxZ * vZ) mod ed25519_p) in *.
  set (x_rawZ := (2 * F.to_Z sF * DxZ) mod ed25519_p) in *.
  set (yZ := (DyZ * u1Z) mod ed25519_p) in *.
  assert (Hu1_eq : F.to_Z (F.of_Z p 1 - sF * sF)%F = u1Z).
  { unfold u1Z, ssZ. rewrite F_to_Z_sub, F_to_Z_mul, HFp_one.
    change (2^255-19)%Z with ed25519_p. reflexivity. }
  assert (Hu2_eq : F.to_Z (F.of_Z p 1 + sF * sF)%F = u2Z).
  { unfold u2Z, ssZ. rewrite F_to_Z_add, F_to_Z_mul, HFp_one.
    change (2^255-19)%Z with ed25519_p. reflexivity. }
  assert (HDx_eq : F.to_Z (rF * (F.of_Z p 1 + sF * sF))%F = DxZ).
  { unfold DxZ. rewrite F_to_Z_mul.
    change (2^255-19)%Z with ed25519_p. rewrite Hu2_eq. reflexivity. }
  assert (Hxraw_eq : F.to_Z (F.of_Z p 2 * sF * (rF * (F.of_Z p 1 + sF * sF)))%F = x_rawZ).
  { unfold x_rawZ.
    rewrite F_to_Z_mul, F_to_Z_mul, HFp_two, HDx_eq.
    change (2^255-19)%Z with ed25519_p.
    rewrite (Z.mul_mod_idemp_l (2 * F.to_Z sF) DxZ ed25519_p) by (cbv; discriminate).
    reflexivity. }
  assert (Hv_eq : F.to_Z (F.opp (E.d * ((F.of_Z p 1 - sF * sF) * (F.of_Z p 1 - sF * sF)))
                            - (F.of_Z p 1 + sF * sF) * (F.of_Z p 1 + sF * sF))%F = vZ).
  { unfold vZ, u1_sqZ, u2_sqrZ.
    rewrite F_to_Z_sub, F_to_Z_opp, F_to_Z_mul, F_to_Z_mul, F_to_Z_mul.
    change (2^255-19)%Z with ed25519_p.
    rewrite Hd_eq, Hu1_eq, Hu2_eq. rewrite Hopp_mod_eq. reflexivity. }
  assert (HDy_eq : F.to_Z (rF * (rF * (F.of_Z p 1 + sF * sF)) *
                            (F.opp (E.d * ((F.of_Z p 1 - sF * sF) * (F.of_Z p 1 - sF * sF))) -
                              (F.of_Z p 1 + sF * sF) * (F.of_Z p 1 + sF * sF)))%F = DyZ).
  { unfold DyZ. rewrite F_to_Z_mul, F_to_Z_mul.
    change (2^255-19)%Z with ed25519_p.
    rewrite HDx_eq, Hv_eq.
    rewrite (Z.mul_mod_idemp_l (F.to_Z rF * DxZ) vZ ed25519_p) by (cbv; discriminate).
    reflexivity. }
  assert (Hy_eq : F.to_Z ((F.of_Z p 1 - sF * sF) *
                           (rF * (rF * (F.of_Z p 1 + sF * sF)) *
                              (F.opp (E.d * ((F.of_Z p 1 - sF * sF) * (F.of_Z p 1 - sF * sF))) -
                                 (F.of_Z p 1 + sF * sF) * (F.of_Z p 1 + sF * sF))))%F = yZ).
  { unfold yZ. rewrite F_to_Z_mul.
    change (2^255-19)%Z with ed25519_p.
    rewrite Hu1_eq, HDy_eq. f_equal. apply Z.mul_comm. }
  set (x_rawF := (F.of_Z p 2 * sF * (rF * (F.of_Z p 1 + sF * sF)))%F) in *.
  set (y_F := ((F.of_Z p 1 - sF * sF) *
                (rF * (rF * (F.of_Z p 1 + sF * sF)) *
                  (F.opp (E.d * ((F.of_Z p 1 - sF * sF) * (F.of_Z p 1 - sF * sF))) -
                    (F.of_Z p 1 + sF * sF) * (F.of_Z p 1 + sF * sF))))%F) in *.
  assert (Hx_eq : F.to_Z (abs x_rawF) =
                  if ristretto_is_negative x_rawZ
                  then ristretto_canonical_negate x_rawZ
                  else x_rawZ).
  { unfold abs.
    assert (Hneg_xF : is_negative x_rawF = ristretto_is_negative x_rawZ).
    { unfold is_negative, ristretto_is_negative. rewrite Hxraw_eq. reflexivity. }
    rewrite Hneg_xF.
    destruct (ristretto_is_negative x_rawZ).
    - rewrite F_to_Z_opp. change (2^255-19)%Z with ed25519_p.
      rewrite Hxraw_eq. unfold ristretto_canonical_negate.
      rewrite <- (Z.mod_add (- x_rawZ) 1 ed25519_p) by (cbv; discriminate).
      f_equal. lia.
    - exact Hxraw_eq. }
  assert (Htxy_eq : is_negative (abs x_rawF * y_F) =
                    ristretto_is_negative
                      ((F.to_Z (abs x_rawF) * F.to_Z y_F) mod ed25519_p)).
  { unfold is_negative, ristretto_is_negative.
    rewrite F_to_Z_mul. change (2^255-19)%Z with ed25519_p. reflexivity. }
  rewrite <- Hx_eq, <- Hy_eq.
  rewrite <- Htxy_eq.
  destruct (negb wsF || (is_negative (abs x_rawF * y_F) || (F.to_Z y_F =? 0))) eqn:Hcond;
    reflexivity.
Qed.

(* ========================================================================
   Section 5: Encode-side companion (smaller; shares helpers).
   ======================================================================== *)

(** ** Encoder equivalence (companion to the decode theorem).

    The Z-level [ristretto_encode_gallina] (200-byte xyzt input,
    32-byte output) agrees with the F_p-level [ristretto_encode_bytes]
    on the same input, after the [parse_xyzt5] coordinate extraction.

    Stated against the [Fp * Fp * Fp * Fp] extended-Edwards 4-tuple to
    match A.1's [ristretto_encode_bytes] signature. *)
(** PROGRESS (B.5a, 2026-05-22):

    Sister theorem to the now-Qed [ristretto_decode_Z_mirror_correct].
    The encoder is structurally simpler than the decoder (no rejection
    path, no [is_negative s] guard) but has THREE nested boolean
    dispatches in the body: [rotate] (line 8), [is_negative (X' * Zinv)]
    (line 12), and [is_negative s_raw] (line 14).  In the worst case
    this is 2^3 = 8 branches, each closing by [reflexivity] after the
    intermediate [F.to_Z] chain is established.

    Started cascade (matches decoder template):
      - Hd_eq, HFp_one, HSQRT_eq, HINVSQRT_eq         (4 constants)
      - Hu1_eq, Hu2_eq                                (parser-image-mod)
      - Hden_eq                                       (sqrt input)
      - [sqrt_ratio_m1_correspondence] applied        (rZ = F.to_Z rF)
      - Z-intermediates set: D1Z, D2Z, ZinvZ, tZinvZ,
        rotateZ, ixZ, iyZ, edenZ                      (8 helpers)

    Remaining work (~200-300 LoC, mechanical):
      - F.to_Z equalities for D1F/D2F/ZinvF/tZinvF/ixF/iyF/edenF
        (~7 asserts following the decoder's HDx_eq/HDy_eq template)
      - F-side [set] aliases to make the goal use named intermediates
        (~7 [set] calls + [change] folds)
      - Boolean-equality [rotateF = rotateZ] (one assert via
        [is_negative]/[ristretto_is_negative] definitional unfold)
      - [destruct rotateZ] -> 2 branches.  In each branch [x' = ...],
        [y' = ...], [den_inv = ...] resolve, then [destruct
        (ristretto_is_negative (xprime_Z * ZinvZ mod p))] -> 4 leaves.
        Each leaf: prove F.to_Z s_rawF = s_rawZ, [destruct
        ristretto_is_negative s_rawZ] -> 8 final closures by
        [reflexivity].
      - The final byte serialisation match: Z's
        [ristretto_pack_canonical_felem s] and F's
        [ristretto_encode_bytes_of_F s] both reduce to [le_split 32 (_
        mod p)] — congruent by [F.to_Z s_F = s_Z mod p].

    No new lemmas needed; only mechanical [F_to_Z_*] cascading per the
    pattern in the decoder proof above.  Left as future work because
    each of the 8 leaves needs a per-branch [F.to_Z] proof of [s_rawF]
    (the F-side expression for [s_raw] is different in each branch).
*)
Theorem ristretto_encode_Z_mirror_correct :
  forall (xyzt : list Byte.byte),
    length xyzt = 200%nat ->
    let '(x, y, z, ta, tb) := parse_xyzt5 xyzt in
    let t := extended_T ta tb z in
    ristretto_encode_gallina xyzt =
      ristretto_encode_bytes (F.of_Z _ x, F.of_Z _ y, F.of_Z _ z, F.of_Z _ t).
Proof.
  (* TODO Phase B.5a follow-up: 200-300 LoC of mechanical cascade.
     Decoder mirror (above) is Qed and establishes the template.  See
     PROGRESS block for the dispatch tree. *)
Admitted.

(* ========================================================================
   Section 6: Corollaries — KAT lemmas as consequences.

   Once the main theorem lands, the 24 §A.2 rejection lemmas become
   short-circuit corollaries: [ristretto_decode_coords bs = None]
   implies [ristretto_decode_gallina bs = ristretto_bad_point].
   ======================================================================== *)

(** ** Z-level reject corollary: any byte string that the F_p decoder
    rejects, the Z mirror also returns bad_point on. *)
Theorem Z_mirror_rejects_when_Fp_rejects :
  forall bs,
    ristretto_decode_coords bs = None ->
    ristretto_decode_gallina bs = ristretto_bad_point.
Proof.
  intros bs HFp_None.
  rewrite ristretto_decode_Z_mirror_correct.
  rewrite HFp_None.
  reflexivity.
Qed.

(** ** Z-level accept corollary: when the F_p decoder accepts with
    coords (x, y), the Z mirror produces the packed [xyzt5] image. *)
Theorem Z_mirror_accepts_when_Fp_accepts :
  forall bs x y,
    ristretto_decode_coords bs = Some (x, y) ->
    ristretto_decode_gallina bs =
      pack_xyzt5 (F.to_Z x) (F.to_Z y) 1 (F.to_Z x) (F.to_Z y).
Proof.
  intros bs x y HFp_Some.
  rewrite ristretto_decode_Z_mirror_correct.
  rewrite HFp_Some.
  reflexivity.
Qed.

(* ========================================================================
   Phase B.5a deliverables summary (updated 2026-05-22):

   QED in this file:
     - ed25519_p_eq, F_to_Z_of_Z, F_to_Z_mul/add/opp (trivial restatements)
     - F_to_Z_sub (Qed via F.sub = F.add x (F.opp y), Z.add_mod_idemp_r)
     - is_negative_correspondence (~10 LoC, Qed)
     - pow_mod_pos_correct (helper, ~25 LoC, Qed)
     - F_to_Z_pow_pow_mod (Qed, ~15 LoC) — via fiat-crypto's
         F.to_Z_pow + pow_mod_pos_correct case split on Z exponent
     - pow_mod_pos_base_mod / pow_mod_base_mod (helpers, Qed) —
         pow_mod is invariant under mod m of the base.
     - parse_canonical_felem_correspondence (Qed, ~25 LoC) — uses the
         asymmetry-aware statement form (Some/None x Some/None matrix)
         that handles Z's inlined [is_negative] check
     - sqrt_ratio_m1_correspondence (Qed 2026-05-22, ~120 LoC) —
         F.to_Z cascade through v3/v7/u*v7/pow/r0/check + boolean
         dispatch + abs/canonical-negate match via Habsmatch helper.
         Hinges on F_to_Z_pow_pow_mod, pow_mod_base_mod, and a
         (-x) mod p = (p-x) mod p identity via Z.mod_add.
     - Z_mirror_rejects_when_Fp_rejects (corollary, Qed)
     - Z_mirror_accepts_when_Fp_accepts (corollary, Qed)

   QED (added 2026-05-22):
     - ristretto_decode_Z_mirror_correct (MAIN DECODER THEOREM)
         ~80 LoC mechanical F_to_Z cascade through the F-layer body
         (which was simultaneously rewritten to match RFC 9496 §4.3.1;
         the prior F-layer body's [v = d*ss-1] form was provably
         non-equivalent and has been replaced).  Qed in 0.08s.

   ADMITTED (1 remaining):
     - ristretto_encode_Z_mirror_correct (encoder companion)
         All dependencies Qed.  Cascade started (~60 LoC of intermediate
         asserts) but 200-300 LoC of mechanical case work remaining
         across 8 dispatch leaves (rotate * sign-of-x'*Zinv *
         sign-of-s_raw).  See PROGRESS block at the theorem statement
         for the dispatch tree.  Left as follow-up.

   The two corollaries [Z_mirror_rejects_when_Fp_rejects] /
   [_accepts] are now UNCONDITIONALLY Qed (no longer parameterised on
   an Admitted main theorem).  Downstream consumers — the §A.2
   rejection-vector KAT delegation in [Ristretto255_DecodeReject.v] —
   can now refer to these without an unproved-axiom caveat.

   Closing the encoder mirror UNBLOCKS Phase B.5c (Rust KAT
   delegation) — the §A.2 rejection vectors become [cargo test]
   entries against the verified extraction.
   ======================================================================== *)
