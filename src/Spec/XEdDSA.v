(** * XEdDSA: Functional Specification

    Signal's XEdDSA signature scheme: Schnorr signatures using X25519
    (Montgomery) private keys by converting to Edwards form.

    This file specifies the sign and verify algorithms.  No SSProve,
    no mathcomp — pure algebra over [Crypto.Algebra.Hierarchy.field].

    **Location (2026-04-15):** moved from [fiat-crypto/src/Spec/XEdDSA.v]
    to [AUCurves/src/Spec/XEdDSA.v] per repo separation policy
    (fiat-crypto is upstream, AUCurves is ours).  It cannot live in
    [Signal/theories/] because that repo uses mathcomp, which triggers
    a universe inconsistency with this file's [Crypto.Algebra.Hierarchy]
    import.  Import as [Spec.XEdDSA].

    The security proof (EUF-CMA via SSProve Schnorr + Fiat-Shamir) is in
    [Commitments/theories/XEdDSA_Security.v] and the Fiat-Shamir derivation
    in [Commitments/theories/XEdDSA_FiatShamir.v].  Both define their own
    Schnorr references and do not import this spec; the files communicate
    semantically via the Signal protocol, not syntactically.

    References:
    - Signal XEdDSA spec: https://signal.org/docs/specifications/xeddsa/
    - Bernstein et al., "High-speed high-security signatures" (EdDSA)
    - The Edwards↔Montgomery isomorphism is proved in
      [Crypto.Curves.EdwardsMontgomery.EdwardsMontgomeryIsomorphism]
*)

Require Import Coq.ZArith.ZArith.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable.

Module XEdDSA.
  Section WithParams.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}.

    Local Infix "=" := Feq : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).

    (** Scalar field (order l of the prime-order subgroup). *)
    Context {S Seq Szero Sone Sopp Sadd Ssub Smul}
            {scalar_ring : @Hierarchy.ring S Seq Szero Sone Sopp Sadd Ssub Smul}.

    (** Group point type and scalar multiplication. *)
    Context {Point : Type}
            {point_eq : Point -> Point -> Prop}
            {G : Point}                      (* basepoint *)
            {scalar_mul : S -> Point -> Point}
            {point_add : Point -> Point -> Point}.

    Local Notation "n '·' P" := (scalar_mul n P) (at level 40).
    Local Notation "P '⊕' Q" := (point_add P Q) (at level 50).

    (** Hash function: (Point, Point, Msg) → S
        Axiomatized — instantiated with SHA-512 mod l in bedrock2. *)
    Context {Msg : Type}
            {hash_to_scalar : Point -> Point -> Msg -> S}.

    (** ** Key Conversion

        An X25519 private key is a Montgomery scalar.  XEdDSA converts:
          1. a_ed = clamp(privkey)
          2. A = a_ed · G_ed  (Edwards basepoint multiplication)
          3. if sign_bit(A) = 1 then a_ed := -a_ed
                                     A := -A

        The conversion is proved correct by
        [EdwardsMontgomeryIsomorphism] in fiat-crypto. *)

    (** ** Sign

        Input: private key a ∈ S, message M
        Output: signature (R, s) where R : Point, s : S

        Algorithm:
          r = H_nonce(Z || a || M)   — synthetic nonce (Z = 64 random bytes)
          R = r · G
          e = H(R, A, M)
          s = r + e * a  mod l

        This is textbook Schnorr with the hash challenge e = H(R, A, M). *)

    Record signature := mk_sig {
      sig_R : Point;
      sig_s : S;
    }.

    Definition sign (a : S) (A : Point) (r : S) (M : Msg) : signature :=
      let R := r · G in
      let e := hash_to_scalar R A M in
      let s := Sadd r (Smul e a) in
      mk_sig R s.

    (** ** Verify

        Input: public key A : Point, message M, signature (R, s)
        Output: bool

        Check: s · G == R ⊕ (H(R, A, M) · A) *)

    Definition verify (A : Point) (M : Msg) (sig : signature) : Prop :=
      let e := hash_to_scalar (sig_R sig) A M in
      point_eq (sig_s sig · G) ((sig_R sig) ⊕ (e · A)).

    (** ** Correctness

        If (R, s) = sign(a, A, r, M) and A = a · G, then verify(A, M, (R, s)).

        Proof: s · G = (r + e*a) · G = r·G + e·a·G = R + e·A.

        This holds by linearity of scalar multiplication. *)

    (* TODO: State and prove correctness assuming scalar_mul distributes
       over scalar addition:
         (a + b) · G = a·G ⊕ b·G
       This is [Hierarchy.Group.homomorphism] in fiat-crypto. *)

  End WithParams.
End XEdDSA.
