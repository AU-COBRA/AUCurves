(** * Ed25519 sign — bedrock2 implementation (skeleton).
 *
 * Tier-1 #5 of the Ed25519-in-AUCurves track. RFC 8032 Ed25519:
 *
 * Algorithm:
 *   1. h = SHA-512(seed)                            (64 B)
 *   2. a = clamp(h[0..32])                          (scalar)
 *   3. prefix = h[32..64]
 *   4. A = a · B                                    (public key, 32 B compressed)
 *   5. r = SHA-512(prefix || M) mod L               (per-msg nonce scalar)
 *   6. R = r · B                                    (32 B compressed)
 *   7. k = SHA-512(R || A || M) mod L               (challenge scalar)
 *   8. s = (r + k · a) mod L
 *   9. signature = R || s
 *
 * STATUS (2026-04-25): Parameter skeleton — bedrock2 body and Hoare-spec
 * correctness pending. Phase 1.3 of [docs/option-b-plan.md] (Lean-side path
 * `$WORKSPACE/../SSProve-lean/docs/option-b-plan.md`).
 *
 * Working template: [Bedrock/End2End/XEdDSA/Sign.v] (300 LoC):
 *   - Reusable `scalar_reduce` (lines 71-148): mod-L reduction of a 64-byte
 *     hash output. Same `l` constant as Ed25519 — directly reusable.
 *   - Reusable `scalar_muladd` (lines 150-223): r + k·a mod L. Same modulus.
 *   - `xeddsa_sign` (lines 225-300): the wrapper. Differs from RFC 8032
 *     Ed25519 in: SHA-512 vs SHAKE-256; no random nonce (Ed25519 derives
 *     nonce from prefix bytes, XEdDSA from random || prefix). Structural
 *     shape is the same — but XEdDSA uses [montladder] (Montgomery ladder
 *     for Curve25519); Ed25519 needs Edwards scalarmult instead.
 *
 * Edwards scalarmult: now declared as [Parameter]s in
 * [Scalarmult.v] (ed25519_scalarmult, ed25519_scalarmult_base) with
 * implementation pending in [Scalarmult_Impl.v.todo]. The discharge
 * file's header has the concrete bedrock2 plan. Multi-day focused
 * effort to close (~500-1100 LoC total) — comparable to a single
 * fiat-crypto bedrock2 file like [MontgomeryLadder.v].
 *
 * Sign.v's bedrock2 body, when written, will compose:
 *   - [fe25519_scalar_funcs] (from [Scalar25519_64.v]) — already declared
 *   - SHA-512 axiom (Parameter [sha512] below)
 *   - field operations from [Field25519_64.v] (already in tree)
 *   - [ed25519_scalarmult] (BLOCKED — see above)
 *   - point compression from [EdwardsCompressDecompress.v] — already done
 *
 * The Lean side cites [ed25519_sign_correct] from this file via
 * [CoqAxioms.lean::ed25519_sign_correct]; until the blocker is resolved
 * AND the body is written, the citation row remains 🚧 phase1.
 *)

From Stdlib Require Import String List ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Syntax.
(* Pulls in fe25519_scalar_funcs + the 6 spec_of_*_correct Parameters. *)
Require Import Bedrock.End2End.Ed25519.Scalar25519_64.
(* Pulls in ed25519_scalarmult_{,base} + correctness Parameters/Axioms. *)
Require Import Bedrock.End2End.Ed25519.Scalarmult.

Module Ed25519Sign.

  (** Bedrock2 [Func] implementing RFC 8032 Ed25519 sign.
      Parameter pending the body — when filled, mirrors
      [XEdDSA/Sign.v::xeddsa_sign].
      Inputs: [sig_out : ptr 64], [seed : ptr 32], [msg : ptr], [msg_len : nat].
      Output: [sig_out] populated with the 64-byte signature. *)
  Parameter ed25519_sign : Syntax.func.

  (** SHA-512 model — pending verified Jasmin-asm citation.
      Same axiomatization shape as [XEdDSA/Sign.v]'s SHAKE-256 axiom.
      The runtime is libjade's verified SHA-512 asm; the Coq side
      currently treats it as opaque. *)
  Parameter sha512 : list Byte.byte -> list Byte.byte.
  Parameter sha512_output_64 : forall input, length (sha512 input) = 64%nat.

  (** Spec — Phase 1.3 deliverable.
      Currently `True` as a placeholder. Real shape (per option-b-plan.md):

        Theorem ed25519_sign_correct :
          forall (functions : Semantics.env)
                 (t : Semantics.trace) (m : Semantics.mem)
                 (sig_out_ptr seed_ptr msg_ptr : word)
                 (sig_out_init : list Byte.byte)
                 (seed : list Byte.byte) (msg : list Byte.byte)
                 (R : Semantics.mem -> Prop),
            length sig_out_init = 64%nat ->
            length seed = 32%nat ->
            (FElemBytes sig_out_ptr sig_out_init *
             array ptsto (word.of_Z 1) seed_ptr seed *
             array ptsto (word.of_Z 1) msg_ptr msg *
             R)%sep m ->
            map.get functions "ed25519_sign" = Some ed25519_sign ->
            WeakestPrecondition.call functions "ed25519_sign" t m
              [sig_out_ptr; seed_ptr; msg_ptr; word.of_Z (Z.of_nat (length msg))]
              (fun t' m' rets =>
                 t' = t /\ rets = nil /\
                 exists sig_out,
                   length sig_out = 64%nat /\
                   sig_out = rfc8032_ed25519_sign seed msg /\
                   (FElemBytes sig_out_ptr sig_out *
                    array ptsto (word.of_Z 1) seed_ptr seed *
                    array ptsto (word.of_Z 1) msg_ptr msg *
                    R)%sep m').

      Where [rfc8032_ed25519_sign] is the abstract spec (composing
      [Ed25519Scalar.field_l] arithmetic + [Ed25519XYZT.m1add_correct]
      curve law + [Ed25519Compress.decompress_Some_25519] +
      [sha512] axiom).

      Proof structure (matches XEdDSA/Sign.v):
        straightline. handle_call (SHA-512 axiom).
        handle_call (fe25519_scalar_mul_correct). ...
        handle_call (Ed25519XYZT.m1add_correct).
        handle_call (Ed25519Compress.decompress_Some_25519).
        ecancel_assumption. *)
  Axiom ed25519_sign_correct :
    forall (seed : list Byte.byte) (msg : list Byte.byte),
      length seed = 32%nat ->
      True.

End Ed25519Sign.
