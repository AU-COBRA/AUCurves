(** * BW6-761 pairing — type-signature stub.

    Establishes the type signature for the BW6-761 optimal-ate
    pairing without committing to the body.  The real body comes
    from the (B+C) phase of the pairing-tower plan
    (docs/bw6-761-pairing-plan.md):

      - (B) [GenericCubic.CE_funcs] / [GenericQuadratic.QE_funcs] for
        the Fp / Fp3 / Fp6 tower (Fp3_typetest mechanises this).
      - (C) A [GenericMillerLoop.miller_iter] supporting BW6's
        5-symbol {-3,-1,0,1,3} step alphabet.
      - BW6-specific: line evaluation in the BW6 twist, hard-part
        final-exp (cyclotomic structure of order ~p^6 / r).

    Per the spike verdict in docs/bw6-761-spike-verdict.md, the
    Brezing-Weng decomposition lemma `e_BW6 = e_BLS12-377^k` does
    NOT exist — the BW6 / BLS12-377 relationship is purely
    scalar-field-level for SNARK recursion.  So the pairing body
    must be implemented directly over BW6's own Fp6 arithmetic.

    This stub gives downstream consumers (extraction, Rust shim,
    KAT tests) a concrete type to import while the real body is
    being proved. *)

From Stdlib Require Import Strings.String ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Import BinInt String List.ListNotations.
Local Open Scope Z_scope.

Section BW6_761_Pairing_Stub.

  (** Abstract Fp / Fp3 / Fp6 types — the actual BW6 fields once
      the Instances file lands.  For the stub we only need the
      type-level shape. *)
  Context {Fp : Type}.

  Local Notation Fp3 := (Fp * Fp * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  (** G1 = affine point on E(Fp): y^2 = x^3 - 1
      (BW6-761 has a = 0, b = -1 per src/Bedrock/Curve/BW6_761Curve_G1.v) *)
  Definition G1 : Type := Fp * Fp.

  (** G2 = affine point on E'(Fp3): the M-type twist.
      Specifically y^2 = x^3 - 1/w where w ∈ Fp3 is the cubic
      non-residue used to define Fp6. *)
  Definition G2 : Type := Fp3 * Fp3.

  Context {Fp6_one : Fp6}.

  (** *** The pairing stub ***
      Real body (path B+C): one Miller loop with the 5-symbol
      {-3,-1,0,1,3} alphabet over 189 iterations, post-composed with
      BW6-761's hard-part final exponentiation.

      Type signature: G1 × G2 → Fp6. *)
  Definition bw6_761_pairing (P : G1) (Q : G2) : Fp6 :=
    Fp6_one. (* TODO(B+C): real Miller-loop + final-exp body *)

End BW6_761_Pairing_Stub.

(** This file builds when Rocq accepts the type signature above. The
    stub is intentionally trivial — its value is to fix the API surface
    that downstream files (extraction, Rust wiring, KATs) can import
    without waiting for the bespoke proof work. *)
