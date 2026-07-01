# src/Spec

High-level Rocq specifications: pairing, hash-to-curve, scalar multiplication,
and the XEdDSA/X25519 protocol stack.

## Pairing

`BLS12Pairing/` — BLS12-381 optimal-ate pairing spec and proof of bilinearity.

## Hash-to-curve

These files implement the IETF hash-to-curve standard (RFC 9380) for G1 and G2:

| File pattern | Role |
|---|---|
| `HashToCurve*.v` | G1: SWU map, isogeny, closure proof |
| `HashToCurveG2*.v` | G2: SWU map, isogeny, closure proof |
| `HashToCurveFieldSetup.v` | Field setup shared by G1 and G2 |
| `HashToCurvePolyArith.v` | Polynomial arithmetic helpers (used by KZG bridge) |
| `FpLegendre_G2.v` | Fp2 square-root (Legendre symbol) for G2 SWU |

Hash function: SHAKE-256 via `SHAKE256.v` (verified Keccak, 0 axioms).

## XEdDSA / Curve25519

| File | Contents |
|------|----------|
| `XEdDSA_Curve25519.v` | Sign + verify correctness at Edwards25519 |
| `SHAKE256.v` | Concrete SHAKE-256 via verified bedrock2 Keccak |

## Other

| File | Contents |
|------|----------|
| `GLV_Endomorphism.v` | GLV endomorphism spec |
| `wNAF_*.v` | wNAF scalar multiplication spec and correctness |
