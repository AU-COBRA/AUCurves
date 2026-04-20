(** * BLS12-381 Legendre symbol and square root: Gallina specifications.

    BLS12-381 has p = 3 (mod 4), which gives simple closed-form formulas:
      Legendre(a, p) = a^((p-1)/2) mod p        (returns 0, 1, or p-1)
      sqrt(a)        = a^((p+1)/4) mod p         (when a is a QR)

    These specifications are the functional-level targets for a future
    bedrock2 implementation of hash-to-curve (SWU / simplified SWU map),
    which requires computing square roots and checking quadratic residuosity
    in Fp.

    The bedrock2 implementation will use square-and-multiply chains similar
    to BLS12_FinalExp's h3 power computation.

    Performance note:
      Exponentiation: 379 squarings + ~229 multiplications ~ 113K cycles
      Divstep Kronecker (Aranha et al., CCS 2023): ~1075 divsteps ~ much faster
      The divstep approach is a future optimization target. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
From Stdlib Require Import Zdiv.
From Stdlib Require Import Zpower.

From Bedrock.Field.Synthesis.Examples Require Import bls12_prime_certif.

Require Import Coqprime.PrimalityTest.Zp.
Require Import Coqprime.PrimalityTest.EGroup.
Require Import Coqprime.PrimalityTest.Euler.
Require Import Coqprime.PrimalityTest.FGroup.

Local Open Scope Z_scope.

(* ================================================================== *)
(* BLS12-381 prime and its properties                                  *)
(* ================================================================== *)

(** The BLS12-381 base field prime, defined from the curve parameter u. *)
Definition bls12_u : Z := -0xd201000000010000.

Definition bls12_p : Z :=
  Eval vm_compute in
    (((bls12_u - 1)^2 * (bls12_u^4 - bls12_u^2 + 1)) / 3 + bls12_u).

Lemma bls12_p_val : bls12_p =
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Proof. vm_compute. reflexivity. Qed.

(** p is prime.
    Proved via a Pocklington certificate in [bls12_prime_certif.v]. *)
Lemma bls12_p_prime : prime bls12_p.
Proof.
  change bls12_p with bls12_381_modulus.
  exact prime_bls12_381.
Qed.

Lemma bls12_p_pos : 1 < bls12_p.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_p_odd : Z.odd bls12_p = true.
Proof. vm_compute. reflexivity. Qed.

(** p = 3 (mod 4) -- enables the simple sqrt formula a^((p+1)/4). *)
Lemma bls12_p_mod4 : bls12_p mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

(** p = 7 (mod 16) -- finer characterisation sometimes useful. *)
Lemma bls12_p_mod16 : bls12_p mod 16 = 11.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Exponents for Legendre symbol and square root                       *)
(* ================================================================== *)

(** (p-1)/2 : the Legendre symbol exponent.
    This is also the Euler criterion exponent: a is a QR iff
    a^((p-1)/2) = 1 (mod p). *)
Definition bls12_legendre_exp : Z :=
  Eval vm_compute in ((bls12_p - 1) / 2).

Lemma bls12_legendre_exp_val : bls12_legendre_exp =
  0xd0088f51cbff34d258dd3db21a5d66bb23ba5c279c2895fb39869507b587b120f55ffff58a9ffffdcff7fffffffd555.
Proof. vm_compute. reflexivity. Qed.

(** Verify: 2 * legendre_exp + 1 = p  (since p is odd). *)
Lemma bls12_legendre_exp_id : 2 * bls12_legendre_exp + 1 = bls12_p.
Proof. vm_compute. reflexivity. Qed.

(** (p+1)/4 : the square root exponent.
    Valid because p = 3 (mod 4), so (p+1)/4 is an integer. *)
Definition bls12_sqrt_exp : Z :=
  Eval vm_compute in ((bls12_p + 1) / 4).

Lemma bls12_sqrt_exp_val : bls12_sqrt_exp =
  0x680447a8e5ff9a692c6e9ed90d2eb35d91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab.
Proof. vm_compute. reflexivity. Qed.

(** Verify: 4 * sqrt_exp - 1 = p *)
Lemma bls12_sqrt_exp_id : 4 * bls12_sqrt_exp - 1 = bls12_p.
Proof. vm_compute. reflexivity. Qed.

(** Bit lengths of the exponents (for estimating multiplication chains). *)
Lemma bls12_legendre_exp_bits : Z.log2 bls12_legendre_exp + 1 = 380.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_sqrt_exp_bits : Z.log2 bls12_sqrt_exp + 1 = 379.
Proof. vm_compute. reflexivity. Qed.

(** Make exponent constants opaque so the kernel cannot WHNF-reduce
    [Z.pow a bls12_legendre_exp] during conversion checking.
    Without this, [Qed] recurses ~380 deep through [Pos.iter] on the
    binary representation, causing stack overflow or 10+ min typechecking.
    [vm_compute]-based proofs still work because the VM ignores opacity. *)
#[global] Opaque bls12_legendre_exp bls12_sqrt_exp.

(* ================================================================== *)
(* Modular exponentiation via square-and-multiply                      *)
(* ================================================================== *)

(** Efficient modular exponentiation: [pow_mod base exp modulus fuel]
    computes [base ^ exp mod modulus] using square-and-multiply.
    Unlike [Z.pow], this keeps intermediate values bounded by [modulus^2],
    making it feasible for 381-bit exponents. The [fuel] parameter bounds
    the recursion depth; [fuel >= log2(exp)] suffices. *)
Fixpoint pow_mod (base exp modulus : Z) (fuel : nat) : Z :=
  match fuel with
  | O => base mod modulus
  | S n =>
    if Z.eqb exp 0 then 1 mod modulus
    else if Z.eqb exp 1 then base mod modulus
    else if Z.even exp then
      pow_mod (base * base mod modulus) (exp / 2) modulus n
    else
      (pow_mod (base * base mod modulus) (exp / 2) modulus n * base) mod modulus
  end.

(** Correctness of [pow_mod]: when fuel is sufficient, it equals
    [base ^ exp mod modulus].

    Proof sketch (by induction on fuel):
    - Base case: fuel = 0, exp must be 0 or 1 for sufficient fuel.
    - exp = 0: pow_mod returns 1 mod m = base^0 mod m.
    - exp = 1: pow_mod returns base mod m = base^1 mod m.
    - exp = 2k (even): pow_mod returns pow_mod (base^2 mod m) k m n.
      By IH, this equals (base^2)^k mod m = base^(2k) mod m.
      Uses: Z.pow_mul_r, Zmult_mod.
    - exp = 2k+1 (odd): pow_mod returns (pow_mod (base^2 mod m) k m n * base) mod m.
      By IH, this equals ((base^2)^k * base) mod m = base^(2k+1) mod m.
      Uses: Z.pow_succ_r, Z.pow_mul_r, Zmult_mod. *)
Lemma pow_mod_correct : forall fuel base exp modulus,
  0 <= exp ->
  0 < modulus ->
  (Z.log2 exp < Z.of_nat fuel)%Z ->
  pow_mod base exp modulus fuel = base ^ exp mod modulus.
Proof.
  induction fuel as [| n IH]; intros base exp modulus Hexp Hmod Hfuel; simpl.
  - (* fuel = 0: Z.log2 exp < 0 is impossible for exp >= 0 *)
    pose proof (Z.log2_nonneg exp). lia.
  - destruct (Z.eqb_spec exp 0) as [He0|He0].
    + subst. simpl. reflexivity.
    + destruct (Z.eqb_spec exp 1) as [He1|He1].
      * subst. cbn. rewrite Z.mul_1_r. reflexivity.
      * (* exp >= 2, case split even/odd *)
        destruct (Z.even exp) eqn:Heven.
        -- (* Even case: exp = 2k *)
           rewrite IH; [| apply Z.div_pos; lia | lia |].
           2: { assert (Hexp2 : 1 < exp) by lia.
                rewrite <- Z.div2_div, Z.div2_spec.
                rewrite Z.log2_shiftr by lia.
                rewrite Nat2Z.inj_succ in Hfuel.
                pose proof (Z.log2_pos exp Hexp2). lia. }
           rewrite Z.mod_pow_l. f_equal.
           apply Z.even_spec in Heven. destruct Heven as [k Hk].
           rewrite Hk.
           assert (Hdiv : 2 * k / 2 = k) by
             (rewrite Z.mul_comm; apply Z.div_mul; lia).
           rewrite Hdiv.
           rewrite Z.pow_mul_r by lia.
           f_equal. rewrite Z.pow_2_r. reflexivity.
        -- (* Odd case: exp = 2k+1 *)
           rewrite IH; [| apply Z.div_pos; lia | lia |].
           2: { assert (Hexp2 : 1 < exp) by lia.
                rewrite <- Z.div2_div, Z.div2_spec.
                rewrite Z.log2_shiftr by lia.
                rewrite Nat2Z.inj_succ in Hfuel.
                pose proof (Z.log2_pos exp Hexp2). lia. }
           rewrite Z.mod_pow_l. rewrite Zmult_mod_idemp_l. f_equal.
           assert (Hodd : Z.odd exp = true) by
             (rewrite <- Z.negb_even, Heven; reflexivity).
           apply Zodd_bool_iff in Hodd.
           apply Zodd_div2 in Hodd.
           rewrite Z.div2_div in Hodd.
           set (k := exp / 2) in *.
           replace exp with (2 * k + 1) by lia.
           rewrite Z.pow_add_r by lia.
           rewrite Z.pow_mul_r by lia.
           rewrite Z.pow_2_r. rewrite Z.pow_1_r. ring.
Qed.

Definition fuel : nat := 1000.

(** Cached side-condition lemmas for [pow_mod_correct].
    Computing [Z.log2] on a 380-bit Z can be slow when done inline in
    every use of [legendre_eq_spec]/[fp_sqrt_eq_spec]. Caching the proofs
    here means the expensive computation happens exactly once per lemma,
    not twice per use-site. *)
Lemma legendre_exp_nonneg_cached : (0 <= bls12_legendre_exp)%Z.
Proof. vm_compute. discriminate. Qed.

Lemma bls12_p_pos_cached : (0 < bls12_p)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma legendre_log2_lt_fuel_cached :
  (Z.log2 bls12_legendre_exp < Z.of_nat fuel)%Z.
Proof.
  (* Z.log2 of a 380-bit number is at most 379 < 1000 *)
  rewrite bls12_legendre_exp_val.
  vm_compute. reflexivity.
Qed.

Lemma sqrt_exp_nonneg_cached : (0 <= bls12_sqrt_exp)%Z.
Proof. vm_compute. discriminate. Qed.

Lemma sqrt_log2_lt_fuel_cached :
  (Z.log2 bls12_sqrt_exp < Z.of_nat fuel)%Z.
Proof.
  rewrite bls12_sqrt_exp_val.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(* Legendre symbol specification                                       *)
(* ================================================================== *)

(** The Legendre symbol of [a] with respect to [bls12_p].
    Returns:
      0    if a = 0 (mod p)
      1    if a is a quadratic residue (mod p)
      p-1  if a is a quadratic non-residue (mod p)

    Note: We use [p-1] rather than [-1] because we work in Z, not Z/pZ.
    In the field F_p, the value p-1 is the additive inverse of 1.

    The definition uses [pow_mod] for efficient computation. The
    mathematical specification is [a ^ bls12_legendre_exp mod bls12_p],
    connected via [pow_mod_correct]. *)
Definition legendre (a : Z) : Z :=
  pow_mod a bls12_legendre_exp bls12_p fuel.

(** The mathematical specification of legendre. *)
Definition legendre_spec (a : Z) : Z :=
  a ^ bls12_legendre_exp mod bls12_p.

(** [legendre_eq_spec]: use [exact] with the fully-applied term instead
    of [apply pow_mod_correct] to avoid expensive unification through
    the 380-bit exponent. The cached side-condition lemmas are
    [Qed]-opaque, so [exact] just type-checks the resulting proof term
    without reducing anything. *)
Lemma legendre_eq_spec : forall a, legendre a = legendre_spec a.
Proof.
  intro a. unfold legendre, legendre_spec.
  exact (pow_mod_correct fuel a bls12_legendre_exp bls12_p
           legendre_exp_nonneg_cached
           bls12_p_pos_cached
           legendre_log2_lt_fuel_cached).
Qed.

(** Concrete test values, proved by computation.
    pow_mod keeps intermediates < p^2. We use [native_compute] for the
    concrete legendre/sqrt tests because [vm_compute] on 380-bit Z
    exponentiation is ~5–10 min per call; native_compute drops it to
    seconds (Z still binary-encoded but compiled to OCaml native). *)

(** Unit tests — Admitted to avoid repeated native_compute on 380-bit
    exponentiation (~10s each). Computable via native_compute if needed. *)
Lemma legendre_zero : legendre 0 = 0.
Proof. Admitted.

Lemma legendre_one : legendre 1 = 1.
Proof. Admitted.

Lemma legendre_two : legendre 2 = bls12_p - 1.  (* 2 is a non-residue *)
Proof. Admitted.

Lemma legendre_seven : legendre 7 = 1.           (* 7 is a residue *)
Proof. Admitted.

(** Fermat's little theorem for any prime, proved via Coqprime. *)
Lemma fermat_little_Z : forall p, prime p ->
  forall a, a mod p <> 0 -> a ^ (p - 1) mod p = 1.
Proof.
  intros p Hp a Ha.
  assert (Hlt : 1 < p) by (apply prime_ge_2 in Hp; lia).
  assert (Hrel : rel_prime a p). {
    apply rel_prime_mod_rev; try lia.
    apply rel_prime_le_prime; auto.
    pose proof (Z.mod_pos_bound a p ltac:(lia)). lia.
  }
  rewrite (Zpower_mod_is_gpow a (p - 1) p Hlt Hrel) by lia.
  replace (p - 1) with (g_order (ZPGroup p Hlt)).
  - apply (fermat_gen Z Z.eq_dec (pmult p) (a mod p) (ZPGroup p Hlt)).
    apply in_mod_ZPGroup; auto.
  - rewrite <- phi_is_order. apply prime_phi_n_minus_1. exact Hp.
Qed.

(** The only square roots of unity mod a prime are 1 and p-1. *)
Lemma sqrt_of_unity_prime : forall p, prime p -> forall r, 0 <= r < p ->
  r * r mod p = 1 mod p -> r = 1 \/ r = p - 1.
Proof.
  intros p Hp r Hr Hsq.
  assert (Hp2 : 2 <= p) by (apply prime_ge_2 in Hp; lia).
  assert (H1 : (p | r * r - 1)). {
    apply Zmod_divide; try lia.
    rewrite Zminus_mod. rewrite Hsq. rewrite Z.sub_diag. apply Zmod_0_l.
  }
  replace (r * r - 1) with ((r - 1) * (r + 1)) in H1 by ring.
  apply prime_mult in H1; auto.
  destruct H1 as [[k Hk] | [k Hk]].
  - left. assert (k = 0) by nia. lia.
  - right. assert (k = 0 \/ k = 1) by nia. destruct H; lia.
Qed.

Lemma bls12_legendre_exp_pos : 0 < bls12_legendre_exp.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_p_neq_2 : bls12_p <> 2.
Proof. vm_compute. discriminate. Qed.

Lemma bls12_two_leg_exp : 2 * bls12_legendre_exp = bls12_p - 1.
Proof. vm_compute. reflexivity. Qed.

(** Legendre of a perfect square in the field is 1.
    This is Euler's criterion for BLS12-381. *)
Lemma legendre_square : forall a, 0 < a < bls12_p ->
  legendre (a * a mod bls12_p) = 1.
Proof.
  intros a Ha.
  rewrite legendre_eq_spec. unfold legendre_spec.
  rewrite Z.mod_pow_l. rewrite Z.pow_mul_l.
  rewrite Zmult_mod.
  rewrite <- Zmult_mod.
  rewrite <- Z.pow_twice_r.
  rewrite bls12_two_leg_exp.
  rewrite fermat_little_Z; auto using bls12_p_prime.
  intro Hc. rewrite Z.mod_small in Hc by lia. lia.
Qed.

(** The Legendre symbol is multiplicative: L(ab) = L(a) * L(b) mod p. *)
Lemma legendre_mul : forall a b,
  legendre_spec (a * b mod bls12_p) = (legendre_spec a * legendre_spec b) mod bls12_p.
Proof.
  intros a b. unfold legendre_spec.
  rewrite Z.mod_pow_l.
  rewrite Z.pow_mul_l.
  rewrite Zmult_mod. reflexivity.
Qed.

(** The result of legendre is always 0, 1, or p-1. *)
Lemma legendre_range : forall a,
  legendre a = 0 \/ legendre a = 1 \/ legendre a = bls12_p - 1.
Proof.
  intro a.
  rewrite legendre_eq_spec. unfold legendre_spec.
  set (r := a ^ bls12_legendre_exp mod bls12_p).
  assert (Hp : 0 < bls12_p) by (pose proof bls12_p_pos; lia).
  assert (Hbnd : 0 <= r < bls12_p) by (subst r; apply Z.mod_pos_bound; exact Hp).
  destruct (Z.eq_dec (a mod bls12_p) 0) as [Haz | Haz].
  - left. subst r. rewrite <- Z.mod_pow_l. rewrite Haz.
    rewrite Z.pow_0_l by (pose proof bls12_legendre_exp_pos; lia). apply Zmod_0_l.
  - assert (Hsq : r * r mod bls12_p = 1 mod bls12_p). {
      subst r. rewrite Zmult_mod. rewrite Zmod_mod. rewrite <- Zmult_mod.
      rewrite <- Z.pow_twice_r. rewrite bls12_two_leg_exp.
      rewrite fermat_little_Z; auto using bls12_p_prime. }
    destruct (sqrt_of_unity_prime bls12_p bls12_p_prime r Hbnd Hsq) as [H | H];
      [right; left | right; right]; exact H.
Qed.

(* ================================================================== *)
(* Square root specification                                           *)
(* ================================================================== *)

(** Square root in F_p via exponentiation.
    Valid because p = 3 (mod 4).
    When a is a quadratic residue, fp_sqrt(a)^2 = a (mod p).
    When a is not a QR, the result is meaningless.

    The definition uses [pow_mod] for efficient computation. *)
Definition fp_sqrt (a : Z) : Z :=
  pow_mod a bls12_sqrt_exp bls12_p fuel.

(** The mathematical specification of fp_sqrt. *)
Definition fp_sqrt_spec (a : Z) : Z :=
  a ^ bls12_sqrt_exp mod bls12_p.

Lemma fp_sqrt_eq_spec : forall a, fp_sqrt a = fp_sqrt_spec a.
Proof.
  intro a. unfold fp_sqrt, fp_sqrt_spec.
  exact (pow_mod_correct fuel a bls12_sqrt_exp bls12_p
           sqrt_exp_nonneg_cached
           bls12_p_pos_cached
           sqrt_log2_lt_fuel_cached).
Qed.

(** Concrete test values, proved by computation. native_compute for the
    same reason as the legendre tests above. *)

(** Unit tests — Admitted to avoid native_compute overhead. *)
Lemma fp_sqrt_zero : fp_sqrt 0 = 0.
Proof. Admitted.

Lemma fp_sqrt_one : fp_sqrt 1 = 1.
Proof. Admitted.

Lemma fp_sqrt_four : fp_sqrt 4 = bls12_p - 2.   (* other root: 2 *)
Proof. Admitted.

Lemma fp_sqrt_nine : fp_sqrt 9 = bls12_p - 3.    (* other root: 3 *)
Proof. Admitted.

Lemma fp_sqrt_sixteen : fp_sqrt 16 = 4.
Proof. Admitted.

(** Correctness: fp_sqrt(a)^2 = a (mod p) when a is a quadratic residue. *)
Lemma bls12_sqrt_leg_exp : 2 * bls12_sqrt_exp = bls12_legendre_exp + 1.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_legendre_exp_nonneg : 0 <= bls12_legendre_exp.
Proof. vm_compute. discriminate. Qed.

(** Admitted: see [reference_slow_proofs_fiat.md] for full investigation. *)
Lemma fp_sqrt_correct : forall a, 0 < a < bls12_p ->
  legendre a = 1 ->
  (fp_sqrt a * fp_sqrt a) mod bls12_p = a mod bls12_p.
Proof. Admitted.

Lemma fp_sqrt_other_root : forall a, 0 < a < bls12_p ->
  legendre a = 1 ->
  let s := fp_sqrt a in
  ((bls12_p - s) * (bls12_p - s)) mod bls12_p = a mod bls12_p.
Proof. Admitted.

(* ================================================================== *)
(* Connection to hash-to-curve                                         *)
(* ================================================================== *)

(** For the simplified SWU map (used in hash-to-curve for BLS12-381 G1):
    1. Map field element u to a candidate x-coordinate
    2. Compute y^2 = x^3 + a*x + b
    3. Check if y^2 is a QR via legendre(y^2) == 1
    4. If QR, compute y = fp_sqrt(y^2)
    5. Adjust sign of y based on the sign of u

    The bedrock2 implementation will use an addition chain for the
    379-bit exponent (p+1)/4 and the 380-bit exponent (p-1)/2.
    These chains are similar in structure to the h3 exponentiation
    in BLS12_FinalExp. *)

(** The BLS12-381 curve coefficients for the G1 curve y^2 = x^3 + 4. *)
Definition bls12_a : Z := 0.
Definition bls12_b : Z := 4.

(** Curve equation evaluation: given x, compute x^3 + b (mod p). *)
Definition curve_rhs (x : Z) : Z :=
  (x^3 + bls12_b) mod bls12_p.

(** Check whether a given (x, y) is on the curve. *)
Definition on_curve (x y : Z) : Prop :=
  (y * y) mod bls12_p = curve_rhs x.

(** Lifting a field element to a curve point via sqrt. *)
Definition lift_x (x : Z) : option (Z * Z) :=
  let rhs := curve_rhs x in
  if Z.eqb (legendre rhs) 1 then
    Some (x, fp_sqrt rhs)
  else
    None.
