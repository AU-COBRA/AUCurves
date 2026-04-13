(** * XEdDSA signature verification — bedrock2 specification

    Verify Signal's XEdDSA signature:
      Given: public key A (32 bytes, Montgomery x-coordinate),
             signature (R, s) (64 bytes), message
      Check: s · G == R + SHA-512(R || A_ed || msg) · A_ed

    where A_ed is the Edwards form of the Montgomery public key.

    ## Key operations
    1. Montgomery → Edwards conversion (EdwardsMontgomeryIsomorphism, Qed)
    2. Hash: e = SHA-512(R || A_ed || msg) mod l
    3. Double scalar multiplication: s·G + (-e)·A_ed
       (variable-time is OK — inputs are public during verification)
    4. Compare with R

    ## Verification chain
    Spec: Spec/XEdDSA.v (verify equation)
    Security: Commitments/XEdDSA_Security.v (SSProve Schnorr soundness)
    Implementation: this file (bedrock2 WP)

    Step 8d of the Signal verification plan. *)

From Coq Require Import ZArith Lia String List.
From Coq.Init Require Import Byte.
Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry.
Require Import bedrock2.Map.Separation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Import Syntax Syntax.Coercions NotationsCustomEntry ListNotations.

(** TODO: bedrock2 implementation + WP proof.

    Dependencies:
    - EdwardsMontgomeryIsomorphism (fiat-crypto, read-only)
    - Ristretto/ScalarMult.v (Step 8b)
    - SHA512_axiom (Signal/)
    - Edwards XYZT add/double (fiat-crypto, read-only)

    The verification uses Straus' method for double scalar mul:
      s·G + (-e)·A = s·G - e·A
    which is more efficient than two separate scalar muls.

    For the bedrock2 implementation, this can be decomposed as:
    1. Decompress A from Montgomery to Edwards XYZT
    2. Decompress R from bytes
    3. Compute e = SHA512(R || A || msg) mod l
    4. Compute s·G (fixed-base, can use precomputed table)
    5. Compute e·A (variable-base)
    6. Subtract: check s·G - e·A == R

    Template: EdwardsXYZT.v (add/double/readd operations)
    Estimated: 1 week *)
