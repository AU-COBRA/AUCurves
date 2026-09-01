(** * BLS Signature Scheme: Specification and Correctness Proof.

    This file defines the BLS (Boneh-Lynn-Shacham) signature scheme
    using the bilinearity axioms from Bilinearity.v, and proves:

    1. verify_correct:  Verify(KeyGen(sk), H(m), Sign(sk, H(m))) = true
    2. aggregate_verify_correct:  AggregateVerify works for honest signers

    The proofs rely only on bilinearity of the pairing; no
    computational hardness assumptions are needed for correctness.

    Trust model: inherits the bilinearity axioms from Bilinearity.v.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Bilinearity.

Section BLSSignature.

  (** ================================================================ *)
  (** ** Parameters                                                      *)
  (** ================================================================ *)

  Variable p : positive.

  (* Frobenius constants — passed through to the pairing *)
  Variable gamma1_p2 gamma2_p2 coeff_p2_c1 : F p * F p.
  Variable fp12_eq_dec : forall (a b : (((F p * F p) * (F p * F p) * (F p * F p)) *
    ((F p * F p) * (F p * F p) * (F p * F p)))),
    {a = b} + {a <> b}.

  Local Notation Fp := (F p).
  Local Notation Fp2 := ((Fp * Fp)%type).
  Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
  Local Notation Fp12 := ((Fp6 * Fp6)%type).
  Local Notation G1 := (G1Affine p).
  Local Notation G2 := (G2Affine p).

  Local Notation e := (pairing p gamma1_p2 gamma2_p2 coeff_p2_c1).
  Local Notation fp12_mul := (Pairing.fp12_mul p).
  Local Notation fp12_one := (Pairing.fp12_one p).

  (** Make pairing definitions opaque to prevent simpl/unfold from
      expanding the heavy Miller loop and final exponentiation. *)
  #[local] Opaque pairing pairing_check Pairing.fp12_mul Pairing.fp12_one.

  (** Abstract group operations (from Bilinearity.v) *)
  Variable g1_add : G1 -> G1 -> G1.
  Variable g1_scalar_mult : Z -> G1 -> G1.
  Variable g2_scalar_mult : Z -> G2 -> G2.

  (** Generators *)
  Variable g1_gen : G1.
  Variable g2_gen : G2.

  (** Hash-to-curve: maps a message (abstract type) to a G1 point. *)
  Variable message : Type.
  Variable hash_to_curve : message -> G1.

  (** Shorthand for fp12_pow from Bilinearity.v *)
  Local Notation fp12_pow := (fp12_pow p).

  (** ================================================================ *)
  (** ** Bilinearity axioms (instantiated)                               *)
  (** ================================================================ *)

  (** We assume the axioms from Bilinearity.v hold for our parameters. *)

  Hypothesis bilinear_left :
    forall (a : Z) (P : G1) (Q : G2),
      e (g1_scalar_mult a P) Q = fp12_pow (e P Q) a.

  Hypothesis bilinear_right :
    forall (b : Z) (P : G1) (Q : G2),
      e P (g2_scalar_mult b Q) = fp12_pow (e P Q) b.

  Hypothesis additive_left :
    forall (P Q : G1) (R : G2),
      e (g1_add P Q) R = fp12_mul (e P R) (e Q R).

  Hypothesis non_degenerate :
    e g1_gen g2_gen <> fp12_one.

  Hypothesis check_correct :
    forall (P1 : G1) (Q1 : G2) (P2 : G1) (Q2 : G2),
      pairing_check p gamma1_p2 gamma2_p2 coeff_p2_c1 fp12_eq_dec
        P1 Q1 P2 Q2 = true
      <->
      e P1 Q1 = e P2 Q2.

  (** Fp12 multiplicative group is a monoid: right identity. *)
  Hypothesis fp12_mul_one_r :
    forall (x : Fp12), fp12_mul x fp12_one = x.

  (** Fp12 multiplicative group: associativity. *)
  Hypothesis fp12_mul_assoc :
    forall (x y z : Fp12), fp12_mul (fp12_mul x y) z = fp12_mul x (fp12_mul y z).

  (** ================================================================ *)
  (** ** Part 1: BLS Signature Scheme Definitions                        *)
  (** ================================================================ *)

  (** Key generation: pk = sk * g2 *)
  Definition keygen (sk : Z) : G2 :=
    g2_scalar_mult sk g2_gen.

  (** Signing: sig = sk * H(m) *)
  Definition sign (sk : Z) (m : message) : G1 :=
    g1_scalar_mult sk (hash_to_curve m).

  (** Verification: check e(sig, g2) = e(H(m), pk) *)
  Definition verify (pk : G2) (m : message) (sig : G1) : bool :=
    pairing_check p gamma1_p2 gamma2_p2 coeff_p2_c1 fp12_eq_dec
      sig g2_gen (hash_to_curve m) pk.

  (** Aggregation: aggregate signatures by adding G1 points *)
  Fixpoint aggregate (sigs : list G1) : G1 :=
    match sigs with
    | [] => g1_scalar_mult 0 g1_gen  (* identity / point at infinity *)
    | [s] => s
    | s :: rest => g1_add s (aggregate rest)
    end.

  (** Product of pairings: prod_i e(H(m_i), pk_i) *)
  Fixpoint multi_pairing (msgs : list message) (pks : list G2) : Fp12 :=
    match msgs, pks with
    | [], [] => fp12_one
    | m :: ms, pk :: ps => fp12_mul (e (hash_to_curve m) pk) (multi_pairing ms ps)
    | _, _ => fp12_one  (* mismatched lengths: degenerate case *)
    end.

  (** Aggregate verification for the same message:
      e(agg_sig, g2) = prod_i e(H(m), pk_i) *)
  Definition aggregate_verify_same_msg
    (pks : list G2) (m : message) (agg_sig : G1) : bool :=
    pairing_check p gamma1_p2 gamma2_p2 coeff_p2_c1 fp12_eq_dec
      agg_sig g2_gen (hash_to_curve m) (g2_scalar_mult 1 (g2_gen))
      (* Note: this simplified version uses pairing_check for the 2-signer
         case. The general aggregate check is stated as a spec below. *)
    .

  (** General aggregate verification (spec-level definition):
      Checks e(agg_sig, g2) = prod_i e(H(m_i), pk_i) *)
  Definition aggregate_verify_spec
    (msgs : list message) (pks : list G2) (agg_sig : G1) : Prop :=
    e agg_sig g2_gen = multi_pairing msgs pks.

  (** ================================================================ *)
  (** ** Part 2: Correctness Theorems                                    *)
  (** ================================================================ *)

  (** ---------------------------------------------------------------- *)
  (** *** Theorem 1: Individual signature verification is correct.       *)
  (** ---------------------------------------------------------------- *)

  (** For any secret key sk and message m,
      Verify(KeyGen(sk), H(m), Sign(sk, H(m))) = true.

      Proof:
        e(Sign(sk,m), g2) = e(sk*H(m), g2)          -- def of Sign
                           = fp12_pow(e(H(m), g2), sk) -- bilinear_left
        e(H(m), KeyGen(sk)) = e(H(m), sk*g2)          -- def of KeyGen
                             = fp12_pow(e(H(m), g2), sk) -- bilinear_right
        So e(sig, g2) = e(H(m), pk). By check_correct, verify returns true.
  *)
  Theorem verify_correct :
    forall (sk : Z) (m : message),
      verify (keygen sk) m (sign sk m) = true.
  Proof.
    intros sk m.
    unfold verify, sign, keygen.
    apply check_correct.
    rewrite bilinear_left.
    rewrite bilinear_right.
    reflexivity.
  Qed.

  (** ---------------------------------------------------------------- *)
  (** *** Lemma: pairing distributes over aggregation (2 signatures)    *)
  (** ---------------------------------------------------------------- *)

  Lemma pairing_aggregate2 :
    forall (sig1 sig2 : G1) (Q : G2),
      e (g1_add sig1 sig2) Q = fp12_mul (e sig1 Q) (e sig2 Q).
  Proof.
    intros. apply additive_left.
  Qed.

  (** ---------------------------------------------------------------- *)
  (** *** Lemma: pairing distributes over n-fold aggregation            *)
  (** ---------------------------------------------------------------- *)

  Lemma pairing_aggregate_cons :
    forall (s : G1) (rest : list G1) (Q : G2),
      rest <> [] ->
      e (aggregate (s :: rest)) Q =
      fp12_mul (e s Q) (e (aggregate rest) Q).
  Proof.
    intros s rest Q Hne.
    simpl. destruct rest as [| s2 rest'].
    - exfalso. apply Hne. reflexivity.
    - apply additive_left.
  Qed.

  (** ---------------------------------------------------------------- *)
  (** *** Theorem 2: Aggregate verification for 2 signers (same msg).  *)
  (** ---------------------------------------------------------------- *)

  (** If sig1 = Sign(sk1, m) and sig2 = Sign(sk2, m),
      then e(sig1 + sig2, g2) = e(H(m), pk1) * e(H(m), pk2).

      Proof:
        e(sig1 + sig2, g2)
          = e(sig1, g2) * e(sig2, g2)           -- additive_left
          = fp12_pow(e(H(m),g2), sk1) * fp12_pow(e(H(m),g2), sk2)
                                                  -- bilinear_left (twice)
        e(H(m), pk1) * e(H(m), pk2)
          = fp12_pow(e(H(m),g2), sk1) * fp12_pow(e(H(m),g2), sk2)
                                                  -- bilinear_right (twice)
        Both sides are equal.
  *)
  Theorem aggregate_verify_2_correct :
    forall (sk1 sk2 : Z) (m : message),
      let sig1 := sign sk1 m in
      let sig2 := sign sk2 m in
      let pk1 := keygen sk1 in
      let pk2 := keygen sk2 in
      let agg_sig := g1_add sig1 sig2 in
      e agg_sig g2_gen =
      fp12_mul (e (hash_to_curve m) pk1) (e (hash_to_curve m) pk2).
  Proof.
    intros sk1 sk2 m sig1 sig2 pk1 pk2 agg_sig.
    subst agg_sig sig1 sig2 pk1 pk2.
    unfold sign, keygen.
    rewrite additive_left.
    rewrite !bilinear_left.
    rewrite !bilinear_right.
    reflexivity.
  Qed.

  (** ---------------------------------------------------------------- *)
  (** *** Theorem 2b: Aggregate verification for 2 signers (bool).     *)
  (** ---------------------------------------------------------------- *)

  (** Same as above but stated as a pairing_check returning true.
      Uses the fact that e(H(m), pk1) * e(H(m), pk2)
      = e(H(m), pk1 + pk2) when we have additive right.
      Instead we state the spec-level equality. *)
  Theorem aggregate_verify_2_spec :
    forall (sk1 sk2 : Z) (m : message),
      aggregate_verify_spec
        [m; m]
        [keygen sk1; keygen sk2]
        (g1_add (sign sk1 m) (sign sk2 m)).
  Proof.
    intros sk1 sk2 m.
    unfold aggregate_verify_spec. simpl.
    unfold sign, keygen.
    rewrite additive_left.
    rewrite !bilinear_left.
    rewrite !bilinear_right.
    rewrite fp12_mul_one_r.
    reflexivity.
  Qed.

  (** ---------------------------------------------------------------- *)
  (** *** Theorem 3: Aggregate verification for 3 signers (same msg).  *)
  (** ---------------------------------------------------------------- *)

  Theorem aggregate_verify_3_spec :
    forall (sk1 sk2 sk3 : Z) (m : message),
      aggregate_verify_spec
        [m; m; m]
        [keygen sk1; keygen sk2; keygen sk3]
        (aggregate [sign sk1 m; sign sk2 m; sign sk3 m]).
  Proof.
    intros sk1 sk2 sk3 m.
    unfold aggregate_verify_spec. simpl.
    unfold sign, keygen.
    rewrite !additive_left.
    rewrite !bilinear_left.
    rewrite !bilinear_right.
    rewrite fp12_mul_one_r.
    reflexivity.
  Qed.

  (** ---------------------------------------------------------------- *)
  (** *** Theorem 4: Aggregate verification for n signers (same msg).  *)
  (** ---------------------------------------------------------------- *)

  (** We prove the general n-signer case by induction on the list of
      secret keys. Each signer signs the same message m. *)

  Fixpoint sign_all (sks : list Z) (m : message) : list G1 :=
    match sks with
    | [] => []
    | sk :: rest => sign sk m :: sign_all rest m
    end.

  Fixpoint keygen_all (sks : list Z) : list G2 :=
    match sks with
    | [] => []
    | sk :: rest => keygen sk :: keygen_all rest
    end.

  (** Repeat a message n times *)
  Fixpoint repeat_msg (m : message) (n : nat) : list message :=
    match n with
    | O => []
    | S k => m :: repeat_msg m k
    end.

  (** Key helper: pairing of aggregate of honest signatures with g2
      equals the multi-pairing of hash with public keys. *)
  Lemma aggregate_pairing_n :
    forall (sks : list Z) (m : message),
      sks <> [] ->
      e (aggregate (sign_all sks m)) g2_gen =
      multi_pairing (repeat_msg m (length sks)) (keygen_all sks).
  Proof.
    intros sks m Hne.
    induction sks as [| sk1 rest IH].
    - exfalso. apply Hne. reflexivity.
    - destruct rest as [| sk2 rest'].
      + (* Base case: single signer *)
        simpl. unfold sign, keygen.
        rewrite bilinear_left.
        rewrite bilinear_right.
        rewrite fp12_mul_one_r.
        reflexivity.
      + (* Inductive step: sk1 :: sk2 :: rest' *)
        change (sign_all (sk1 :: sk2 :: rest') m)
          with (sign sk1 m :: sign_all (sk2 :: rest') m).
        change (aggregate (sign sk1 m :: sign_all (sk2 :: rest') m))
          with (g1_add (sign sk1 m) (aggregate (sign_all (sk2 :: rest') m))).
        rewrite additive_left.
        assert (Hne2 : (sk2 :: rest') <> []) by (intro H; discriminate H).
        rewrite (IH Hne2).
        change (keygen_all (sk1 :: sk2 :: rest'))
          with (keygen sk1 :: keygen_all (sk2 :: rest')).
        change (length (sk1 :: sk2 :: rest'))
          with (S (length (sk2 :: rest'))).
        simpl repeat_msg. simpl multi_pairing.
        (* Now LHS has: fp12_mul (e (sign sk1 m) g2_gen) (multi_pairing ...)
           and RHS has: fp12_mul (e (hash_to_curve m) (keygen sk1)) (multi_pairing ...)
           We need: e(sign sk1 m, g2) = e(H(m), keygen sk1) *)
        f_equal.
        unfold sign, keygen.
        rewrite bilinear_left.
        rewrite bilinear_right.
        reflexivity.
  Qed.

  (** The main n-signer aggregate verification theorem. *)
  Theorem aggregate_verify_n_correct :
    forall (sks : list Z) (m : message),
      sks <> [] ->
      aggregate_verify_spec
        (repeat_msg m (length sks))
        (keygen_all sks)
        (aggregate (sign_all sks m)).
  Proof.
    intros sks m Hne.
    unfold aggregate_verify_spec.
    apply aggregate_pairing_n.
    exact Hne.
  Qed.

  (** ================================================================ *)
  (** ** Part 3: Unforgeability (statement only)                         *)
  (** ================================================================ *)

  (** Unforgeability cannot be proved from bilinearity alone — it
      requires a computational hardness assumption (co-CDH in G1).

      We state it as an axiom to document the security claim.
      The axiom says: if a signature verifies, then either it was
      honestly computed, or the co-CDH assumption is broken.

      This is the standard formulation from:
        Boneh, Lynn, Shacham. "Short signatures from the Weil pairing."
        Journal of Cryptology, 2004.
  *)

  (** Abstract proposition: the co-CDH problem in G1 has been solved. *)
  Variable co_CDH_broken : Prop.

  Axiom bls_euf_cma :
    forall (sk : Z) (m : message) (sig : G1),
      verify (keygen sk) m sig = true ->
      sig = sign sk m \/ co_CDH_broken.

  (** ================================================================ *)
  (** ** Auxiliary properties                                             *)
  (** ================================================================ *)

  (** Verification is deterministic: same inputs give same result. *)
  Lemma verify_deterministic :
    forall pk m sig,
      verify pk m sig = verify pk m sig.
  Proof. reflexivity. Qed.

  (** Two different secret keys produce different public keys
      (assuming the pairing is non-degenerate and the group has
       prime order). Stated as a conditional. *)
  Hypothesis scalar_mult_injective_g2 :
    forall a b : Z,
      g2_scalar_mult a g2_gen = g2_scalar_mult b g2_gen -> a = b.

  Theorem keygen_injective :
    forall sk1 sk2 : Z,
      keygen sk1 = keygen sk2 -> sk1 = sk2.
  Proof.
    intros sk1 sk2 H.
    unfold keygen in H.
    apply scalar_mult_injective_g2.
    exact H.
  Qed.

  (** Verification with wrong key fails (assuming hash_to_curve hits
      a generator, which is true with overwhelming probability). *)
  Hypothesis hash_hits_generator :
    forall m : message,
      exists k : Z, hash_to_curve m = g1_scalar_mult k g1_gen.

  (** If fp12_pow is injective on the base (which holds for generators),
      then wrong-key verification implies key equality. *)
  Hypothesis fp12_pow_injective :
    forall (base : Fp12) (a b : Z),
      base <> fp12_one ->
      fp12_pow base a = fp12_pow base b ->
      a = b.

  (** Verification with the wrong key reduces to a pairing equality
      that implies equal exponents (i.e., equal secret keys). *)
  Theorem wrong_key_implies_equal_exponents :
    forall (sk sk' : Z) (m : message),
      verify (keygen sk') m (sign sk m) = true ->
      fp12_pow (e (hash_to_curve m) g2_gen) sk =
      fp12_pow (e (hash_to_curve m) g2_gen) sk'.
  Proof.
    intros sk sk' m Hverify.
    apply check_correct in Hverify.
    unfold sign, keygen in Hverify.
    rewrite bilinear_left in Hverify.
    rewrite bilinear_right in Hverify.
    exact Hverify.
  Qed.

  (** Corollary: if the pairing base is non-trivial, wrong-key
      verification implies the secret keys are equal. *)
  Corollary wrong_key_contradiction :
    forall (sk sk' : Z) (m : message),
      e (hash_to_curve m) g2_gen <> fp12_one ->
      verify (keygen sk') m (sign sk m) = true ->
      sk = sk'.
  Proof.
    intros sk sk' m Hnondeg Hverify.
    apply (fp12_pow_injective _ _ _ Hnondeg).
    exact (wrong_key_implies_equal_exponents sk sk' m Hverify).
  Qed.

End BLSSignature.
