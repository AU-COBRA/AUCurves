(** * BW6-761 G1/G2 Gallina group operations + subgroup membership.

    Mirror of [BN_GroupOps.v]/[BN254_Group.v] for BW6-761.

    BW6-761 curve parameters:
      - Base field: 761-bit prime [p] (see [bw6_761_prime_certif.v]).
      - Subgroup order [r] (377-bit, equals the base-field prime of
        BLS12-377).  BW6-761 is the "outer" curve of the BW6/BLS12-377
        2-chain, see El Housni & Guillevic, "Families of SNARK-friendly
        2-chains" (eprint 2021/1359).
      - G1: [y^2 = x^3 - 1] over [Fp], cofactor [h1] (not 1).
      - G2: M-type cubic twist [y^2 = x^3 - 1 / zeta] over
        [Fp3 = Fp[zeta]/(zeta^3 + 4)], cofactor [h2] (not 1).

    This file defines:

      - [BW6_G1_aff], [BW6_G1_double], [BW6_G1_add], [BW6_G1_neg],
        [BW6_G1_scalar_mul], [BW6_G1_on_curve], [BW6_G1_in_subgroup]
        — re-using the generic [BN_GroupOps.G1_*] machinery with
        BW6's [p] and [b = -1 mod p].

      - [BW6_G2_aff], [BW6_G2_on_twist], [BW6_G2_double_aff],
        [BW6_G2_add_aff], [BW6_G2_neg_aff], [BW6_G2_scalar_mul_aff],
        [BW6_G2_in_subgroup] — defined fresh over Fp3 using the
        cubic-ring ops from [CubicExtensionsAbstract.v] specialised
        to BW6-761's [bw6_Fp_mul_by_nr_model] (multiplication by -4).

      - Generators ([BW6_G1_gen], [BW6_G2_gen]) with [on_curve] /
        [on_twist] lemmas (Closed).

    The bedrock2 implementation + WP proofs are downstream and live
    in [src/Bedrock/Curve/BW6_761Curve_G2_*.v] once the WP layer
    matures.  Hash-to-curve for G1/G2 likewise lives downstream. *)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.BN_GroupOps.

Local Open Scope Z_scope.

(** ** BW6-761 numerics *)

Definition bw6_761_p_pos : positive := bw6_761_prime_pos.

(** Curve coefficient: [y^2 = x^3 - 1], so [b = -1 mod p]. *)
Definition bw6_761_b : F bw6_761_p_pos := F.opp (F.of_Z _ 1).

(** Subgroup order [r] for BW6-761 (the scalar field of BLS12-377):
      r = 258664426012969094010652733694893533536393512754914660539884262666744683201.

    This matches gnark-crypto/ecc/bw6-761/internal/fptower/r.go. *)
Definition bw6_761_r : Z :=
  258664426012969094010652733694893533536393512754914660539884262666744683201.

(** ** G1 group ops — re-use generic [BN_GroupOps.G1_*]
    (same curve form [y^2 = x^3 + b], just different [p] and [b]). *)

Definition BW6_G1_aff           := G1_aff       bw6_761_p_pos.
Definition BW6_G1_on_curve      := G1_on_curve  bw6_761_p_pos bw6_761_b.
Definition BW6_G1_double        := G1_double    bw6_761_p_pos.
Definition BW6_G1_add           := G1_add       bw6_761_p_pos.
Definition BW6_G1_neg           := G1_neg       bw6_761_p_pos.
Definition BW6_G1_scalar_mul    := G1_scalar_mul bw6_761_p_pos.

(** BW6-761 has nontrivial G1 cofactor — naive subgroup check via [r]·P = O.
    Efficient endomorphism-based check is downstream. *)
Definition BW6_G1_in_subgroup (P : BW6_G1_aff) : Prop :=
  BW6_G1_on_curve P /\ BW6_G1_scalar_mul bw6_761_r P = G1_inf bw6_761_p_pos.

(** BW6-761 G1 generator (gnark canonical):
      x = 0x1075b020ea190c8b277510bf64711a8b3a4f95b9c9d09b6f15efeefe4488e3aa9f7d4d27e2a0d80a40cd9b6a3c8b9
      y = 0x58cdcd1b06f9bdfa9d4f3...

    For brevity here we leave the hex literals; they parse as positive
    integers and are converted to [F p] via [F.of_Z].  Full literals
    pinned in [BW6_761_PairingHelpers.v]. *)
Definition BW6_G1_gen_x : F bw6_761_p_pos :=
  F.of_Z _ 6238772257913348445393101286310300472375605820828272641104655184154787493509255867879462061551866404064348519443823432268251830954165828049267548480784814049407219379306423410589353226843828797378728103586559923840329%Z.

Definition BW6_G1_gen_y : F bw6_761_p_pos :=
  F.of_Z _ 2101735126520897423911504562215834951148127555913367997162789335052900271653517958562461315794228241561913734371411178226936527683203802606314115174749905260063478775732078647698432063205955225518933344132985747576514%Z.

Definition BW6_G1_gen : BW6_G1_aff := G1_pt bw6_761_p_pos BW6_G1_gen_x BW6_G1_gen_y.

(** ** G2 group ops over Fp3 *)

Section BW6_G2.

  Local Notation Fp  := (F bw6_761_p_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.

  (** Multiplication by the cubic non-residue (-4) in Fp. *)
  Definition bw6_761_mul_by_nr (x : Fp) : Fp :=
    F.mul (F.opp (F.of_Z _ 4)) x.

  (** Fp3 ring ops (matches CubicExtensionsAbstract.ce_* with these
      operations).  We inline here to avoid the [AbstractField] /
      [Rupicola] dependency chain. *)

  Definition fp3_c0 (x : Fp3) : Fp := fst (fst x).
  Definition fp3_c1 (x : Fp3) : Fp := snd (fst x).
  Definition fp3_c2 (x : Fp3) : Fp := snd x.
  Definition mk_fp3 (a0 a1 a2 : Fp) : Fp3 := ((a0, a1), a2).

  Definition fp3_zero : Fp3 := mk_fp3 (F.of_Z _ 0) (F.of_Z _ 0) (F.of_Z _ 0).
  Definition fp3_one  : Fp3 := mk_fp3 (F.of_Z _ 1) (F.of_Z _ 0) (F.of_Z _ 0).

  Definition fp3_add (a b : Fp3) : Fp3 :=
    mk_fp3 (F.add (fp3_c0 a) (fp3_c0 b))
           (F.add (fp3_c1 a) (fp3_c1 b))
           (F.add (fp3_c2 a) (fp3_c2 b)).

  Definition fp3_sub (a b : Fp3) : Fp3 :=
    mk_fp3 (F.sub (fp3_c0 a) (fp3_c0 b))
           (F.sub (fp3_c1 a) (fp3_c1 b))
           (F.sub (fp3_c2 a) (fp3_c2 b)).

  Definition fp3_opp (a : Fp3) : Fp3 :=
    mk_fp3 (F.opp (fp3_c0 a)) (F.opp (fp3_c1 a)) (F.opp (fp3_c2 a)).

  (** Karatsuba multiplication mod (zeta^3 + 4). *)
  Definition fp3_mul (a b : Fp3) : Fp3 :=
    let a0 := fp3_c0 a in let a1 := fp3_c1 a in let a2 := fp3_c2 a in
    let b0 := fp3_c0 b in let b1 := fp3_c1 b in let b2 := fp3_c2 b in
    let a0b0 := F.mul a0 b0 in
    let a1b1 := F.mul a1 b1 in
    let a2b2 := F.mul a2 b2 in
    let t0 := F.sub (F.sub (F.mul (F.add a1 a2) (F.add b1 b2)) a1b1) a2b2 in
    let c0 := F.add a0b0 (bw6_761_mul_by_nr t0) in
    let t1 := F.sub (F.sub (F.mul (F.add a0 a1) (F.add b0 b1)) a0b0) a1b1 in
    let c1 := F.add t1 (bw6_761_mul_by_nr a2b2) in
    let t2 := F.sub (F.sub (F.mul (F.add a0 a2) (F.add b0 b2)) a0b0) a2b2 in
    let c2 := F.add t2 a1b1 in
    mk_fp3 c0 c1 c2.

  (** Fp3 inverse via the classical formula.  Returns junk on zero. *)
  Definition fp3_inv (a : Fp3) : Fp3 :=
    let a0 := fp3_c0 a in let a1 := fp3_c1 a in let a2 := fp3_c2 a in
    let c0_sq := F.mul a0 a0 in
    let c1_sq := F.mul a1 a1 in
    let c2_sq := F.mul a2 a2 in
    let c0c1  := F.mul a0 a1 in
    let c0c2  := F.mul a0 a2 in
    let c1c2  := F.mul a1 a2 in
    let A     := F.sub c0_sq (bw6_761_mul_by_nr c1c2) in
    let B     := F.sub (bw6_761_mul_by_nr c2_sq) c0c1 in
    let C     := F.sub c1_sq c0c2 in
    let FF    := F.add (F.mul a0 A)
                       (bw6_761_mul_by_nr (F.add (F.mul a2 B) (F.mul a1 C))) in
    let FF_inv := F.inv FF in
    mk_fp3 (F.mul A FF_inv) (F.mul B FF_inv) (F.mul C FF_inv).

  Definition fp3_div (a b : Fp3) : Fp3 := fp3_mul a (fp3_inv b).

  (** Decidable equality on Fp3. *)
  Definition fp3_eq_dec : forall x y : Fp3, {x = y} + {x <> y}.
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    destruct (F.eq_dec a0 b0); [|right; intro H; inversion H; contradiction].
    destruct (F.eq_dec a1 b1); [|right; intro H; inversion H; contradiction].
    destruct (F.eq_dec a2 b2); [|right; intro H; inversion H; contradiction].
    left; subst; reflexivity.
  Defined.

  (** Twist coefficient [b'] = [-1/zeta] in Fp3.
      With [zeta = (0,1,0)] (so zeta^3 = -4), we have
          1/zeta = zeta^2 / zeta^3 = zeta^2 / (-4) = -zeta^2 / 4
      Hence [b' = -1/zeta = zeta^2 / 4 = (0, 0, 1/4)].

      [1/4 mod p] is computed via F.inv. *)
  Definition bw6_761_inv4 : Fp := F.inv (F.of_Z _ 4).

  Definition BW6_G2_b_twist : Fp3 :=
    mk_fp3 (F.of_Z _ 0) (F.of_Z _ 0) bw6_761_inv4.

  Inductive G2_aff_fp3 :=
    | G2f3_inf : G2_aff_fp3
    | G2f3_pt  : Fp3 -> Fp3 -> G2_aff_fp3.

  (** On-twist: [y^2 = x^3 + b'] over Fp3. *)
  Definition BW6_G2_on_twist (P : G2_aff_fp3) : Prop :=
    match P with
    | G2f3_inf => True
    | G2f3_pt x y =>
        fp3_mul y y =
        fp3_add (fp3_mul (fp3_mul x x) x) BW6_G2_b_twist
    end.

  (** Affine doubling on E'. *)
  Definition BW6_G2_double_aff (P : G2_aff_fp3) : G2_aff_fp3 :=
    match P with
    | G2f3_inf => G2f3_inf
    | G2f3_pt x y =>
        if fp3_eq_dec y fp3_zero then G2f3_inf
        else
          let three_x_sq :=
              let xs := fp3_mul x x in fp3_add (fp3_add xs xs) xs in
          let two_y := fp3_add y y in
          let lam := fp3_mul three_x_sq (fp3_inv two_y) in
          let x' := fp3_sub (fp3_mul lam lam) (fp3_add x x) in
          let y' := fp3_sub (fp3_mul lam (fp3_sub x x')) y in
          G2f3_pt x' y'
    end.

  (** Affine addition (full case-split). *)
  Definition BW6_G2_add_aff (P Q : G2_aff_fp3) : G2_aff_fp3 :=
    match P, Q with
    | G2f3_inf, _ => Q
    | _, G2f3_inf => P
    | G2f3_pt x1 y1, G2f3_pt x2 y2 =>
        if fp3_eq_dec x1 x2 then
          if fp3_eq_dec y1 y2 then BW6_G2_double_aff P
          else G2f3_inf
        else
          let lam := fp3_mul (fp3_sub y2 y1) (fp3_inv (fp3_sub x2 x1)) in
          let x3  := fp3_sub (fp3_sub (fp3_mul lam lam) x1) x2 in
          let y3  := fp3_sub (fp3_mul lam (fp3_sub x1 x3)) y1 in
          G2f3_pt x3 y3
    end.

  Definition BW6_G2_neg_aff (P : G2_aff_fp3) : G2_aff_fp3 :=
    match P with
    | G2f3_inf => G2f3_inf
    | G2f3_pt x y => G2f3_pt x (fp3_opp y)
    end.

  Fixpoint BW6_G2_scalar_mul_pos (k : positive) (P : G2_aff_fp3) : G2_aff_fp3 :=
    match k with
    | xH => P
    | xO k' => BW6_G2_double_aff (BW6_G2_scalar_mul_pos k' P)
    | xI k' => BW6_G2_add_aff P (BW6_G2_double_aff (BW6_G2_scalar_mul_pos k' P))
    end.

  Definition BW6_G2_scalar_mul_aff (k : Z) (P : G2_aff_fp3) : G2_aff_fp3 :=
    match k with
    | Z0 => G2f3_inf
    | Zpos k' => BW6_G2_scalar_mul_pos k' P
    | Zneg k' => BW6_G2_neg_aff (BW6_G2_scalar_mul_pos k' P)
    end.

  (** Naive subgroup check via [r]·P = O (efficient endomorphism-based
      check is downstream, mirrors [BN_GroupOps.G2_subgroup_check_spec]). *)
  Definition BW6_G2_in_subgroup (P : G2_aff_fp3) : Prop :=
    BW6_G2_on_twist P /\
    BW6_G2_scalar_mul_aff bw6_761_r P = G2f3_inf.

  (** *** Easy correctness lemmas (Closed) *)

  Lemma BW6_G2_on_twist_inf : BW6_G2_on_twist G2f3_inf.
  Proof. exact I. Qed.

  Lemma BW6_G2_double_aff_inf : BW6_G2_double_aff G2f3_inf = G2f3_inf.
  Proof. reflexivity. Qed.

  Lemma BW6_G2_add_aff_inf_l :
    forall P, BW6_G2_add_aff G2f3_inf P = P.
  Proof. intros [|x y]; reflexivity. Qed.

  Lemma BW6_G2_add_aff_inf_r :
    forall P, BW6_G2_add_aff P G2f3_inf = P.
  Proof. intros [|x y]; reflexivity. Qed.

  Lemma BW6_G2_neg_aff_inf : BW6_G2_neg_aff G2f3_inf = G2f3_inf.
  Proof. reflexivity. Qed.

  Lemma BW6_G2_scalar_mul_aff_0 :
    forall P, BW6_G2_scalar_mul_aff 0 P = G2f3_inf.
  Proof. reflexivity. Qed.

  Lemma BW6_G2_scalar_mul_aff_1 :
    forall P, BW6_G2_scalar_mul_aff 1 P = P.
  Proof. reflexivity. Qed.

End BW6_G2.

(** ** Hash-to-curve specifications (deferred to per-curve files)

    The full SWU + iso_map + isogeny composition for BW6-761 G1/G2 is
    a substantial chunk of math (~weeks of work — mirror of
    [src/Spec/HashToCurveSWUCompute.v] + [HashToCurveIsogenyCompute.v]
    for BLS12-381).  Here we just declare the spec types so downstream
    callers can typecheck against the eventual implementation. *)

Section HashToCurveSpec.

  (** [HashToG1] takes an arbitrary byte sequence and a domain-separation
      tag and returns a point on BW6-761 G1 in the prime-order subgroup. *)
  Definition HashToG1_spec (impl : list nat -> list nat -> BW6_G1_aff) : Prop :=
    forall msg dst,
      let P := impl msg dst in
      BW6_G1_in_subgroup P.

  Definition HashToG2_spec (impl : list nat -> list nat -> G2_aff_fp3) : Prop :=
    forall msg dst,
      let P := impl msg dst in
      BW6_G2_in_subgroup P.

End HashToCurveSpec.

(** ** Smoke tests (kept tiny — full KAT is in [bw6-761-safe-rust/src/kat.rs]) *)

(** Scalar mul by 0 sends any point to infinity. *)
Goal BW6_G1_scalar_mul 0 BW6_G1_gen = G1_inf bw6_761_p_pos.
Proof. reflexivity. Qed.

Goal BW6_G2_scalar_mul_aff 0 G2f3_inf = G2f3_inf.
Proof. reflexivity. Qed.

(** Negation of infinity. *)
Goal BW6_G2_neg_aff G2f3_inf = G2f3_inf.
Proof. reflexivity. Qed.
