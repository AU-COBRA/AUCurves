# src/Bedrock/End2End

End-to-end verified pipelines connecting bedrock2 WP proofs to concrete
implementations. Each subdirectory is a self-contained protocol stack.

## Subdirectories

### `X25519_64/`

Verified X25519 scalar multiplication over Curve25519 (64-bit).

| File | Contents |
|------|----------|
| `Field25519_64.v` | Bedrock2 field arithmetic for GF(2²⁵⁵-19) |
| `MontgomeryLadder64.v` | Montgomery ladder scalar mult WP proof |
| `DettmanMul25519.v` | Dettman-optimized field multiplication |
| `clamp_64.v` | Scalar clamping |
| `ExtractJasmin.v` | Jasmin extraction driver |

### `XEdDSA/`

Verified XEdDSA sign and verify over Curve25519/Edwards25519.

| File | Contents |
|------|----------|
| `Sign.v` | XEdDSA signing WP proof |
| `Verify.v` | XEdDSA verification WP proof |

### `Ristretto/`

`ScalarMult.v` — verified Ristretto255 scalar multiplication.

### `RupicolaCrypto/`

`Keccak.v` — verified bedrock2 Keccak / SHAKE-256 implementation.
Used as the hash function in XEdDSA and hash-to-curve.
