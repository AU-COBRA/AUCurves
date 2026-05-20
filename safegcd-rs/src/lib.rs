//! Bernstein–Yang constant-time modular inversion across 14+1 primes.
//!
//! The const-generic core is [`Signed62`]; each prime is instantiated as a
//! small wrapper module exposing `<curve>_invert_divstep_sat(out, x)`.
//!
//! Convergence is verified in `AUCurves/src/Arithmetic/safegcd/`
//! (δ₀=1 in `divsteps_<curve>.v`, δ₀=1/2 in `divsteps_<curve>_half.v`).

#![allow(non_snake_case, dead_code)]

pub mod safegcd;
// safegcd25519 stays in curve25519-jasmin-rs (it has a fiat-crypto dep for
// the 5×51 unsaturated limb conversion specific to Curve25519's representation).
pub mod safegcd_secp256k1;
pub mod safegcd_p224;
pub mod safegcd_p256;
pub mod safegcd_p384;
pub mod safegcd_p521;
pub mod safegcd_bn254;
pub mod safegcd_bn256;
pub mod safegcd_bn446;
pub mod safegcd_bls12_381;
pub mod safegcd_bls24_509;
pub mod safegcd_bw6_761;
pub mod safegcd_pallas;
pub mod safegcd_vesta;
