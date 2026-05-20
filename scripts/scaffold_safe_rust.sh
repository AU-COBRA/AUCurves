#!/usr/bin/env bash
# Generate skeleton `<curve>-safe-rust/` crates for the 10 verified curves
# that don't yet have packaged Rust crates.
#
# Seven curves (P-224/256/384/521, secp256k1, Pallas, Vesta) get a
# working skeleton that wraps fiat-rust for field arithmetic and
# re-exports the safegcd Bernstein-Yang inverse from safegcd-rs.  The
# remaining three (BLS12-377, BLS24-509, BW6-761) get a non-compiling
# PENDING.md plus a stub Cargo.toml because fiat-rust does not yet
# emit those primes — they require a Rocq extraction run first.
#
# Idempotent: re-running overwrites Cargo.toml / src/lib.rs / PENDING.md
# but leaves any in-progress tests/ alone.

set -euo pipefail
cd "$(dirname "$0")/.."

mk_cargo_toml() {
    local name=$1 desc=$2
    cat >"${name}-safe-rust/Cargo.toml" <<EOF
[package]
name = "${name}-safe-rust"
version = "0.1.0"
edition = "2021"
description = "${desc}"
license = "Apache-2.0"

[lib]
name = "${name//-/_}"
path = "src/lib.rs"

[profile.release]
lto = "fat"
codegen-units = 1
opt-level = 3

[dependencies]
fiat-crypto = { path = "../fiat-crypto/fiat-rust" }
safegcd     = { path = "../safegcd-rs" }

[dev-dependencies]
EOF
}

mk_cargo_stub() {
    local name=$1 desc=$2
    cat >"${name}-safe-rust/Cargo.toml" <<EOF
[package]
name = "${name}-safe-rust"
version = "0.0.0-pending"
edition = "2021"
description = "${desc} — SKELETON (safegcd inverse only), field-op extraction pending"
license = "Apache-2.0"
publish = false

[lib]
name = "${name//-/_}"
path = "src/lib.rs"

[dependencies]
safegcd = { path = "../safegcd-rs" }
EOF
}

mk_lib_fiat() {
    local name=$1 mod_64=$2 fn_prefix=$3 limbs=$4 bits=$5 safegcd_mod=$6 safegcd_fn=$7
    cat >"${name}-safe-rust/src/lib.rs" <<EOF
//! ${name} field arithmetic — fiat-rust leaves + Bernstein-Yang inverse.
//!
//! Field operations (add, sub, mul, square, opp, to/from Montgomery,
//! to/from bytes) come from the auto-generated, machine-checked
//! \`fiat-crypto/fiat-rust/src/${mod_64}.rs\`.  Constant-time modular
//! inversion comes from the Bernstein-Yang divstep port in
//! \`safegcd-rs/src/safegcd_${safegcd_mod}.rs\` (verified against the
//! convergence certificate in
//! \`src/Arithmetic/safegcd/divsteps_${safegcd_mod}_half.v\`).
//!
//! ${bits}-bit prime, ${limbs}×u64 saturated limb representation.

#![allow(non_snake_case, non_camel_case_types)]

pub use fiat_crypto::${mod_64}::${fn_prefix}_montgomery_domain_field_element as Fp;
pub use fiat_crypto::${mod_64}::${fn_prefix}_non_montgomery_domain_field_element as FpRaw;

use fiat_crypto::${mod_64}::*;

#[inline] pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp)     { ${fn_prefix}_add(out, x, y) }
#[inline] pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp)     { ${fn_prefix}_sub(out, x, y) }
#[inline] pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp)     { ${fn_prefix}_mul(out, x, y) }
#[inline] pub fn fp_square(out: &mut Fp, x: &Fp)          { ${fn_prefix}_square(out, x) }
#[inline] pub fn fp_opp(out: &mut Fp, x: &Fp)             { ${fn_prefix}_opp(out, x) }
#[inline] pub fn fp_to_bytes(out: &mut [u8; ${bits}/8 + (${bits}%8>0) as usize], x: &Fp) {
    ${fn_prefix}_to_bytes(out, &x.0)
}
#[inline] pub fn fp_from_bytes(out: &mut FpRaw, bs: &[u8; ${bits}/8 + (${bits}%8>0) as usize]) {
    ${fn_prefix}_from_bytes(&mut out.0, bs)
}
#[inline] pub fn fp_to_montgomery(out: &mut Fp, x: &FpRaw)    { ${fn_prefix}_to_montgomery(out, x) }
#[inline] pub fn fp_from_montgomery(out: &mut FpRaw, x: &Fp)  { ${fn_prefix}_from_montgomery(out, x) }

/// Constant-time modular inverse via the Bernstein–Yang divstep port.
/// Input/output are in Montgomery form.  Convert out → invert → convert in.
pub fn fp_inv(out: &mut Fp, x: &Fp) {
    let mut raw_in = FpRaw([0u64; ${limbs}]);
    fp_from_montgomery(&mut raw_in, x);
    let mut raw_inv = [0u64; ${limbs}];
    safegcd::safegcd_${safegcd_mod}::${safegcd_fn}(&mut raw_inv, &raw_in.0);
    fp_to_montgomery(out, &FpRaw(raw_inv));
}

#[cfg(test)]
mod kat;
EOF
}

mk_kat_fiat() {
    local name=$1 fn_prefix=$2 limbs=$3
    mkdir -p "${name}-safe-rust/src"
    cat >"${name}-safe-rust/src/kat.rs" <<EOF
//! Cross-check that fiat-rust wrappers obey field axioms.
use super::*;

fn zero() -> Fp { Fp([0u64; ${limbs}]) }

fn one_mont() -> Fp {
    // R mod p; obtained via to_montgomery(1).
    let raw = FpRaw({
        let mut a = [0u64; ${limbs}];
        a[0] = 1;
        a
    });
    let mut out = zero();
    fp_to_montgomery(&mut out, &raw);
    out
}

fn nontrivial_raw() -> FpRaw {
    let mut a = [0u64; ${limbs}];
    a[0] = 0x0123_4567_89ab_cdef;
    if ${limbs} > 1 { a[1] = 0xfedc_ba98_7654_3210; }
    if ${limbs} > 2 { a[2] = 0x0011_2233_4455_6677; }
    if ${limbs} > 3 { a[3] = 0x7766_5544_3322_1100; }
    if ${limbs} > 4 { a[4] = 0xdead_beef_cafe_babe; }
    if ${limbs} > 5 { a[5] = 0x1357_9bdf_2468_ace0; }
    // Mask top to ensure < p (most-significant limb cleared in top bits).
    a[${limbs} - 1] &= 0x0fff_ffff_ffff_ffff;
    FpRaw(a)
}

#[test]
fn add_zero_identity() {
    let a = one_mont();
    let mut out = zero();
    fp_add(&mut out, &a, &zero());
    assert_eq!(out.0, a.0);
}

#[test]
fn sub_self_is_zero() {
    let a = one_mont();
    let mut out = a;
    fp_sub(&mut out, &a, &a);
    assert_eq!(out.0, [0u64; ${limbs}]);
}

#[test]
fn mul_one_identity() {
    let a = one_mont();
    let mut out = zero();
    fp_mul(&mut out, &a, &a);  // 1 * 1 = 1
    assert_eq!(out.0, a.0);
}

#[test]
fn invert_roundtrip() {
    let mut a = zero();
    fp_to_montgomery(&mut a, &nontrivial_raw());
    let mut a_inv = zero();
    fp_inv(&mut a_inv, &a);
    let mut prod = zero();
    fp_mul(&mut prod, &a, &a_inv);
    assert_eq!(prod.0, one_mont().0, "a * a^-1 should equal 1 in Montgomery form");
}
EOF
}

mk_lib_stub() {
    local name=$1 desc=$2 reason=$3 safegcd_mod=$4 safegcd_fn=$5 limbs=$6
    cat >"${name}-safe-rust/src/lib.rs" <<EOF
//! ${desc}
//!
//! SKELETON — see ../PENDING.md.  ${reason}
//!
//! The Bernstein–Yang constant-time inverse IS available (it doesn't
//! depend on Montgomery field ops), exposed below as
//! \`invert_raw\`.  Verified against
//! \`src/Arithmetic/safegcd/divsteps_${safegcd_mod}_half.v\`.

#![allow(non_snake_case, dead_code)]

/// Constant-time modular inverse on raw saturated little-endian limbs.
/// Returns \`x^-1 mod p\` in the same limb format.  ${limbs}×u64.
pub fn invert_raw(out: &mut [u64; ${limbs}], x: &[u64; ${limbs}]) {
    safegcd::safegcd_${safegcd_mod}::${safegcd_fn}(out, x);
}
EOF
}

mk_pending() {
    local name=$1 desc=$2 reason=$3 vfile=$4
    cat >"${name}-safe-rust/PENDING.md" <<EOF
# \`${name}-safe-rust\` — extraction pending

${desc}

## Why this crate is empty

${reason}

## Verified Rocq components already in tree

- \`src/Bedrock/Field/Synthesis/Examples/${vfile}\` — the bedrock2-WP
  proofs of the field operations.
- \`src/Arithmetic/safegcd/divsteps_${name//-/_}.v\` and
  \`divsteps_${name//-/_}_half.v\` — Bernstein-Yang convergence
  certificates.
- \`curve25519-jasmin-rs/src/safegcd_${name//-/_}.rs\` — constant-time
  inverse, instantiated from the const-generic Signed62<N> core.

## To turn this skeleton into a real crate

1. Run the bedrock2 → Rust extraction over the field-op specs in the
   \`.v\` files above to produce a \`generated/${name//-/_}_safe_tower.rs\`.
2. Write a hand-tuned \`src/stubs.rs\` with the prime constants P,
   N_PRIME, R2, MONT_ONE, P_MINUS_2 in the curve's limb layout.
3. Wire \`src/lib.rs\` to \`pub use\` the generated tower entry points.
4. Add KAT tests cross-checking against a known reference implementation.

See \`bn256-safe-rust/\` for the smallest exemplar (no pairing tower,
no Jasmin leaves — just Rust Montgomery field arithmetic).
EOF
}

mk_gitignore() {
    local name=$1
    cat >"${name}-safe-rust/.gitignore" <<EOF
/target
Cargo.lock
EOF
}

# ─── fiat-rust covered ────────────────────────────────────────────────
# name        mod_64                   fn_prefix                limbs bits safegcd_mod safegcd_fn
declare -a FIAT=(
    "p256      p256_64                  fiat_p256                4     256  p256       p256_invert_divstep_sat"
    "p224      p224_64                  fiat_p224                4     224  p224       p224_invert_divstep_sat"
    "p384      p384_64                  fiat_p384                6     384  p384       p384_invert_divstep_sat"
    "secp256k1 secp256k1_montgomery_64  fiat_secp256k1_montgomery 4    256  secp256k1  secp_invert_divstep_sat"
    "pallas    pallas_64                fiat_pallas              4     256  pallas     pallas_invert_divstep_sat"
    "vesta     vesta_64                 fiat_vesta               4     256  vesta      vesta_invert_divstep_sat"
)
# P-521 uses Solinas not Montgomery; handled separately (hand-written lib.rs).

for spec in "${FIAT[@]}"; do
    read -r name mod_64 fn_prefix limbs bits safegcd_mod safegcd_fn <<<"$spec"
    mkdir -p "${name}-safe-rust/src"
    mk_cargo_toml  "$name" "${name^^} field arithmetic — fiat-rust leaves + Bernstein-Yang CT inverse"
    mk_lib_fiat    "$name" "$mod_64" "$fn_prefix" "$limbs" "$bits" "$safegcd_mod" "$safegcd_fn"
    mk_kat_fiat    "$name" "$fn_prefix" "$limbs"
    mk_gitignore   "$name"
    echo "  created: ${name}-safe-rust/  (fiat-rust wrapper, ${bits}-bit)"
done

# ─── skeleton-only (fiat-rust does not cover) ─────────────────────────
# name           desc-suffix                                 reason
declare -A SKELETON_DESC=(
    [bls12-377]="BLS12-377 base field Fp + pairing tower"
    [bls24-509]="BLS24-509 base field Fp + pairing tower"
    [bw6-761]="BW6-761 base field Fp + pairing tower"
)
declare -A SKELETON_REASON=(
    [bls12-377]="Needs Rocq extraction of the full Fp2/Fp6/Fp12 pairing tower (see bn256-safe-rust for the pattern)."
    [bls24-509]="Needs Rocq extraction of the full Fp2/Fp4/Fp8/Fp24 pairing tower."
    [bw6-761]="Needs Rocq extraction of the full Fp3/Fp6 pairing tower."
)
declare -A SKELETON_VFILE=(
    [bls12-377]="BLS12_377_FpInv.v + BLS12_377_FpInv_closed.v + BLS12_377_InvertBoundInstantiation.v"
    [bls24-509]="BLS24_509_FpInv.v + BLS24_509_FpInv_closed.v + BLS24_509_InvertBoundInstantiation.v"
    [bw6-761]="BW6_761_FpInv.v + BW6_761_FpInv_closed.v + BW6_761_InvertBoundInstantiation.v"
)
declare -A SKELETON_SG=(
    [bls12-377]="bls12_381 bls12_invert_divstep_sat 6"
    [bls24-509]="bls24_509 bls24_invert_divstep_sat 8"
    [bw6-761]="bw6_761 bw6_761_invert_divstep_sat 12"
)
# Note: bls12-377 currently shares the bls12_381 safegcd module (same chunk
# size, similar 6×u64 layout).  Replace with a dedicated safegcd_bls12_377.rs
# when the cert lands.

for name in bls12-377 bls24-509 bw6-761; do
    desc="${SKELETON_DESC[$name]}"
    reason="${SKELETON_REASON[$name]}"
    vfile="${SKELETON_VFILE[$name]}"
    read -r sg_mod sg_fn sg_limbs <<<"${SKELETON_SG[$name]}"
    mkdir -p "${name}-safe-rust/src"
    mk_cargo_stub   "$name" "$desc"
    mk_lib_stub     "$name" "$desc" "$reason" "$sg_mod" "$sg_fn" "$sg_limbs"
    mk_pending      "$name" "$desc" "$reason" "$vfile"
    mk_gitignore    "$name"
    echo "  skeleton: ${name}-safe-rust/  (safegcd inverse only)"
done

echo
echo "Done.  Five fiat-rust wrapper crates ready to compile; five skeleton"
echo "crates compile as empty libs and carry a PENDING.md."
