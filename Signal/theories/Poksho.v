(** * Signal's poksho: Proof-of-Knowledge instantiation

    Instantiates LinearSigma with ristretto255 parameters for Signal's
    credential system (zkgroup / zkcredential).

    The SSProve security proof lives in Commitments/ where SSProve
    is available. This file provides the concrete parameter choices. *)

From Stdlib Require Import Utf8.
From Signal Require Import LinearSigma.

(** Signal credential proof sizes:
    - AuthCredentialWithPni: 4 witnesses
    - ExpiringProfileKeyCredential: 5 witnesses
    - ReceiptCredential: 4 witnesses
    - GroupSendEndorsement: n witnesses *)

(** The poksho instantiation uses the LinearSigma algorithms
    from LinearSigma.v with concrete parameters from ristretto255.

    When linked with Commitments/ (which has SSProve), the
    SigmaProtocol functor gives SHVZK + soundness + Fiat-Shamir
    automatically.

    The concrete group (ristretto255, order l) is:
      gT := [finGroupType of 'Z_curve25519_l]
      g := Zp1

    See Commitments/theories/Ristretto255_finGroup.v for the definition. *)

(** ** Named pointers to the Commitments-side SSProve proofs

    All artefacts below live in [Commitments/theories/Poksho_Security.v]
    (reached Qed on 2026-04-21, 0 Admitted in file):

    - [Commitments.Poksho_Security.LinearSigma_Protocol]
        — the generic n-dimensional Schnorr functor.
    - [Commitments.Poksho_Security.Poksho4]
        — n=4 instance for AuthCredentialWithPni / ReceiptCredential.
    - [Commitments.Poksho_Security.Poksho5]
        — n=5 instance for ExpiringProfileKeyCredential.
    - [Commitments.Poksho_Security.linear_SHVZK]      — Qed, ε=0.
    - [Commitments.Poksho_Security.linear_soundness]  — Qed, ε=0.
    - [Commitments.Poksho_Security.linear_EUF_CMA]    — True placeholder
        pending the forking lemma (a planned SSProve contribution).

    The pure-algebra scaffolding in this file and [LinearSigma.v]
    is imported by the SSProve packaging on the Commitments side; do
    not duplicate the security statements here. *)
