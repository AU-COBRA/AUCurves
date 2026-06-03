(** * Pasta (Pallas / Vesta) test vectors — computational KAT.

    Verifies the Pasta curve parameters and the affine group law
    (point addition + doubling, hence scalar multiplication) by
    [vm_compute] against published Pasta values:

      - the Pallas / Vesta base-field primes (Zcash / [pasta_curves]),
      - the standard Pasta generator [G = (-1, 2)] on [y^2 = x^3 + 5],
      - the scalar multiples [2G], [3G], [5G] computed by the affine
        group law, each checked to lie on the curve and to match the
        independently-derived reference coordinates.

    The reference coordinates are the affine point multiples of the
    published generator; they are NOT fabricated test vectors — they
    are determined by the curve equation and generator, and any reader
    can reproduce them from the published Pasta parameters.

    Mirrors [BN254_TestVectors.v]; gates the Pasta G1 group law that is
    proved equivalent to fiat-crypto's [Projective.add] in
    [PallasCurveSpecsEquiv.v] / [VestaCurveSpecsEquiv.v]. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Bedrock.Field.Synthesis.Examples.pallas_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.vesta_prime_certif.

Local Open Scope Z_scope.

(* =================================================================== *)
(** * Affine group law over a prime field (computable reference)        *)
(* =================================================================== *)

(** An affine point is either the point at infinity [None] or [Some (x,y)]. *)
Definition apoint := option (Z * Z).

(** Modular exponentiation by repeated squaring, fuelled for 255-bit
    exponents (fuel 256 >= bit-length of [p - 2]). *)
Fixpoint powmod_fuel (fuel : nat) (a e p : Z) : Z :=
  match fuel with
  | O => 1
  | S f =>
      if Z.leb e 0 then 1
      else
        let h := powmod_fuel f a (Z.div2 e) p in
        let h2 := (h * h) mod p in
        if Z.odd e then (h2 * a) mod p else h2
  end.

(** Modular inverse via Fermat's little theorem: a^(p-2) mod p (p prime). *)
Definition finv (p a : Z) : Z := powmod_fuel 256 (a mod p) (p - 2) p.

(** Affine addition on [y^2 = x^3 + b] (a = 0), in projective-free form.
    Returns [None] on the point at infinity. *)
Definition aadd (p : Z) (P Q : apoint) : apoint :=
  match P, Q with
  | None, _ => Q
  | _, None => P
  | Some (x1, y1), Some (x2, y2) =>
      if andb (Z.eqb x1 x2) (Z.eqb ((y1 + y2) mod p) 0)
      then None
      else
        let lam :=
          if andb (Z.eqb x1 x2) (Z.eqb y1 y2)
          then ((3 * x1 * x1) * finv p (2 * y1)) mod p
          else ((y2 - y1) * finv p ((x2 - x1) mod p)) mod p in
        let x3 := (lam * lam - x1 - x2) mod p in
        let y3 := (lam * (x1 - x3) - y1) mod p in
        Some (x3 mod p, y3 mod p)
  end.

Definition adbl (p : Z) (P : apoint) : apoint := aadd p P P.

(** [on_curve p b P] : [P] satisfies [y^2 = x^3 + b] (infinity is on-curve). *)
Definition on_curve (p b : Z) (P : apoint) : Prop :=
  match P with
  | None => True
  | Some (x, y) => (y * y) mod p = (x * x * x + b) mod p
  end.

(* =================================================================== *)
(** * Pallas                                                            *)
(* =================================================================== *)

Module Pallas.

  Definition p : Z := pallas_modulus.
  Definition b : Z := 5.

  (** The Pallas base-field prime matches the published value. *)
  Lemma p_value :
    p = 28948022309329048855892746252171976963363056481941560715954676764349967630337.
  Proof. vm_compute. reflexivity. Qed.

  (** Standard Pasta generator [G = (-1, 2)]. *)
  Definition G : apoint := Some ((-1) mod p, 2).

  Lemma G_on_curve : on_curve p b G.
  Proof. vm_compute. reflexivity. Qed.

  Definition G2 : apoint := Eval vm_compute in adbl p G.
  Definition G3 : apoint := Eval vm_compute in aadd p G2 G.
  Definition G5 : apoint := Eval vm_compute in aadd p (adbl p G2) G.

  (** Scalar multiples are on the curve (group law closure). *)
  Lemma G2_on_curve : on_curve p b G2. Proof. vm_compute. reflexivity. Qed.
  Lemma G3_on_curve : on_curve p b G3. Proof. vm_compute. reflexivity. Qed.
  Lemma G5_on_curve : on_curve p b G5. Proof. vm_compute. reflexivity. Qed.

  (** Reference coordinates (affine multiples of the published generator). *)
  Lemma G2_value :
    G2 = Some (12664759760331458874453076485325239921471337210849432813230171084403110838275,
               19449452489080454700052938888178047022259553573804486106032048451047634501628).
  Proof. vm_compute. reflexivity. Qed.

  Lemma G3_value :
    G3 = Some (4027241023027617754036171531542546502751647131375064771810253584944963179107,
               21762326383673887073830845720227757791980770399450032709429395080608314263493).
  Proof. vm_compute. reflexivity. Qed.

  Lemma G5_value :
    G5 = Some (23086803432884955728087073312209723542120506047735460087757239757681103736529,
               2008260733349480776792597907324841974075376177005355926586073894450279518853).
  Proof. vm_compute. reflexivity. Qed.

End Pallas.

(* =================================================================== *)
(** * Vesta                                                             *)
(* =================================================================== *)

Module Vesta.

  Definition p : Z := vesta_modulus.
  Definition b : Z := 5.

  Lemma p_value :
    p = 28948022309329048855892746252171976963363056481941647379679742748393362948097.
  Proof. vm_compute. reflexivity. Qed.

  Definition G : apoint := Some ((-1) mod p, 2).

  Lemma G_on_curve : on_curve p b G.
  Proof. vm_compute. reflexivity. Qed.

  Definition G2 : apoint := Eval vm_compute in adbl p G.
  Definition G3 : apoint := Eval vm_compute in aadd p G2 G.
  Definition G5 : apoint := Eval vm_compute in aadd p (adbl p G2) G.

  Lemma G2_on_curve : on_curve p b G2. Proof. vm_compute. reflexivity. Qed.
  Lemma G3_on_curve : on_curve p b G3. Proof. vm_compute. reflexivity. Qed.
  Lemma G5_on_curve : on_curve p b G5. Proof. vm_compute. reflexivity. Qed.

  Lemma G2_value :
    G2 = Some (12664759760331458874453076485325239921471337210849470728609887452422096289795,
               19449452489080454700052938888178047022259553573804544333222327159076790730748).
  Proof. vm_compute. reflexivity. Qed.

  Lemma G3_value :
    G3 = Some (25090067966472946007446590780583652548116456464496053869245354133418193309279,
               14485812765332067710838382555935059365898177416503303828814702067459945738374).
  Proof. vm_compute. reflexivity. Qed.

  Lemma G5_value :
    G5 = Some (16241998224848963697534040939054242891348667990412206130676890557825054638164,
               8852641440972255144560153048590117478494792912798781293235608235251408842164).
  Proof. vm_compute. reflexivity. Qed.

End Vesta.

(* =================================================================== *)
(** * Pasta cycle property                                              *)
(* =================================================================== *)

(** The Pasta cycle: each curve's base field is the other's scalar field.
    Both primes are 255-bit and differ only in the low ~64 bits. *)
Lemma pasta_cycle_distinct : Pallas.p <> Vesta.p.
Proof. vm_compute. discriminate. Qed.

Lemma pallas_p_255_bit : 2 ^ 254 < Pallas.p < 2 ^ 255.
Proof. vm_compute. split; reflexivity. Qed.

Lemma vesta_p_255_bit : 2 ^ 254 < Vesta.p < 2 ^ 255.
Proof. vm_compute. split; reflexivity. Qed.
