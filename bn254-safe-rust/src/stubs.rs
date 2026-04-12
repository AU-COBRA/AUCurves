//! Rust-side leaf ops for BN254 (alt_bn128).
//!
//! These provide a fully working pairing implementation without requiring
//! Jasmin or any external assembly. When jasminc is available, the heavy
//! ops (add/sub/mul/square) come from Jasmin assembly via the `jasmin`
//! cfg flag (set by build.rs when build.sh succeeds), and these stubs
//! are excluded.
//!
//! All ops operate on 4-limb little-endian Montgomery-form Fp elements
//! (R = 2^256). The prime is the alt_bn128 (Ethereum BN254) prime
//! p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
//!   = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

const P: [u64; 4] = [
    0x3c208c16d87cfd47,
    0x97816a916871ca8d,
    0xb85045b68181585d,
    0x30644e72e131a029,
];

/// -1/p[0] mod 2^64, used by CIOS Montgomery reduction.
const N_PRIME: u64 = 0x87d20782e4866389;

#[inline(always)]
fn read4(p: *const u64) -> [u64; 4] {
    unsafe { [*p, *p.add(1), *p.add(2), *p.add(3)] }
}

#[inline(always)]
fn write4(p: *mut u64, v: [u64; 4]) {
    unsafe {
        *p = v[0];
        *p.add(1) = v[1];
        *p.add(2) = v[2];
        *p.add(3) = v[3];
    }
}

/// Conditional subtract p if [r] >= p.
#[inline(always)]
fn sub_p_if_ge(r: [u64; 5]) -> [u64; 4] {
    // r is 5 limbs (the 5th is a carry from the previous add). Subtract p
    // and choose the result if the subtraction did not borrow past the
    // 5th limb (i.e., r >= p).
    let (d0, b1) = r[0].overflowing_sub(P[0]);
    let (d1, b2a) = r[1].overflowing_sub(P[1]);
    let (d1, b2b) = d1.overflowing_sub(b1 as u64);
    let (d2, b3a) = r[2].overflowing_sub(P[2]);
    let (d2, b3b) = d2.overflowing_sub((b2a as u64) + (b2b as u64));
    let (d3, b4a) = r[3].overflowing_sub(P[3]);
    let (d3, b4b) = d3.overflowing_sub((b3a as u64) + (b3b as u64));
    let final_borrow = (b4a as u64) + (b4b as u64);
    // r >= p iff r[4] >= final_borrow (no underflow at the high end)
    if r[4] >= final_borrow {
        [d0, d1, d2, d3]
    } else {
        [r[0], r[1], r[2], r[3]]
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn254_add(out: *mut u64, x: *const u64, y: *const u64) {
    let a = read4(x);
    let b = read4(y);
    let mut r = [0u64; 5];
    let (s0, c1) = a[0].overflowing_add(b[0]);
    r[0] = s0;
    let (s1, c2a) = a[1].overflowing_add(b[1]);
    let (s1, c2b) = s1.overflowing_add(c1 as u64);
    r[1] = s1;
    let (s2, c3a) = a[2].overflowing_add(b[2]);
    let (s2, c3b) = s2.overflowing_add((c2a as u64) + (c2b as u64));
    r[2] = s2;
    let (s3, c4a) = a[3].overflowing_add(b[3]);
    let (s3, c4b) = s3.overflowing_add((c3a as u64) + (c3b as u64));
    r[3] = s3;
    r[4] = (c4a as u64) + (c4b as u64);
    write4(out, sub_p_if_ge(r));
}

#[no_mangle]
pub unsafe extern "C" fn _bn254_sub(out: *mut u64, x: *const u64, y: *const u64) {
    let a = read4(x);
    let b = read4(y);
    let (d0, b1) = a[0].overflowing_sub(b[0]);
    let (d1, b2a) = a[1].overflowing_sub(b[1]);
    let (d1, b2b) = d1.overflowing_sub(b1 as u64);
    let (d2, b3a) = a[2].overflowing_sub(b[2]);
    let (d2, b3b) = d2.overflowing_sub((b2a as u64) + (b2b as u64));
    let (d3, b4a) = a[3].overflowing_sub(b[3]);
    let (d3, b4b) = d3.overflowing_sub((b3a as u64) + (b3b as u64));
    let borrow = (b4a as u64) + (b4b as u64);
    // If borrow, add p back.
    let mut r = [d0, d1, d2, d3];
    if borrow != 0 {
        let (a0, c1) = r[0].overflowing_add(P[0]);
        r[0] = a0;
        let (a1, c2a) = r[1].overflowing_add(P[1]);
        let (a1, c2b) = a1.overflowing_add(c1 as u64);
        r[1] = a1;
        let (a2, c3a) = r[2].overflowing_add(P[2]);
        let (a2, c3b) = a2.overflowing_add((c2a as u64) + (c2b as u64));
        r[2] = a2;
        let (a3, _) = r[3].overflowing_add(P[3]);
        let (a3, _) = a3.overflowing_add((c3a as u64) + (c3b as u64));
        r[3] = a3;
    }
    write4(out, r);
}

/// CIOS Montgomery multiplication: out = (x * y * R^{-1}) mod p
/// where R = 2^256.
#[inline(always)]
fn mont_mul(x: [u64; 4], y: [u64; 4]) -> [u64; 4] {
    let mut t = [0u128; 5]; // 5 wide accumulators
    for i in 0..4 {
        // t += x * y[i]
        let mut carry: u128 = 0;
        for j in 0..4 {
            let prod = (x[j] as u128) * (y[i] as u128) + (t[j] as u128 & 0xffffffffffffffff) + carry;
            t[j] = (t[j] & !0xffffffffffffffff_u128) | (prod & 0xffffffffffffffff);
            carry = prod >> 64;
        }
        let s = (t[4] & 0xffffffffffffffff) + carry;
        t[4] = s;
        // m = t[0] * N_PRIME mod 2^64
        let m = ((t[0] as u64).wrapping_mul(N_PRIME)) as u128;
        // t += m * p; this makes t[0] divisible by 2^64
        let mut carry: u128 = 0;
        for j in 0..4 {
            let prod = m * (P[j] as u128) + (t[j] & 0xffffffffffffffff) + carry;
            t[j] = (t[j] & !0xffffffffffffffff_u128) | (prod & 0xffffffffffffffff);
            carry = prod >> 64;
        }
        let s = (t[4] & 0xffffffffffffffff) + carry;
        t[4] = s;
        // Shift right by one limb
        for j in 0..4 {
            t[j] = t[j + 1];
        }
        t[4] = 0;
    }
    let r = [
        t[0] as u64,
        t[1] as u64,
        t[2] as u64,
        t[3] as u64,
        0u64, // t was shifted; the high carry sits in nothing (CIOS keeps t < 2p)
    ];
    sub_p_if_ge(r)
}

#[no_mangle]
pub unsafe extern "C" fn _bn254_mul(out: *mut u64, x: *const u64, y: *const u64) {
    let xv = read4(x);
    let yv = read4(y);
    write4(out, mont_mul(xv, yv));
}

#[no_mangle]
pub unsafe extern "C" fn _bn254_square(out: *mut u64, x: *const u64) {
    let xv = read4(x);
    write4(out, mont_mul(xv, xv));
}

#[no_mangle]
pub unsafe extern "C" fn _bn254_opp(out: *mut u64, x: *const u64) {
    // opp(x) = p - x (with no need for conditional add since x < p)
    unsafe {
        let mut borrow: u64 = 0;
        for i in 0..4 {
            let (d, b1) = P[i].overflowing_sub(*x.add(i));
            let (d2, b2) = d.overflowing_sub(borrow);
            *out.add(i) = d2;
            borrow = (b1 as u64) + (b2 as u64);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn254_felem_copy(out: *mut u64, x: *const u64) {
    unsafe {
        for i in 0..4 {
            *out.add(i) = *x.add(i);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn254_from_word(out: *mut u64, w: u64) {
    // out = w * R mod p
    // For arbitrary w we'd compute mont_mul([w,0,0,0], R^2 mod p), but the
    // pairing pipeline only ever calls this with w in {0, 1}, so we
    // special-case.
    unsafe {
        if w == 0 {
            for i in 0..4 {
                *out.add(i) = 0;
            }
        } else if w == 1 {
            // R mod p
            *out.add(0) = 0xd35d438dc58f0d9d;
            *out.add(1) = 0x0a78eb28f5c70b3d;
            *out.add(2) = 0x666ea36f7879462c;
            *out.add(3) = 0x0e0a77c19a07df2f;
        } else {
            // General case: mont_mul([w,0,0,0], R^2)
            const R2: [u64; 4] = [
                0xf32cfc5b538afa89,
                0xb5e71911d44501fb,
                0x47ab1eff0a417ff6,
                0x06d89f71cab8351f,
            ];
            let r = mont_mul([w, 0, 0, 0], R2);
            write4(out, r);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn254_select_znz(
    out: *mut u64,
    c: u64,
    x: *const u64,
    y: *const u64,
) {
    let src = if c != 0 { x } else { y };
    unsafe {
        for i in 0..4 {
            *out.add(i) = *src.add(i);
        }
    }
}

/// Fp inversion via Fermat's little theorem: x^(p-2) mod p.
/// p-2 = 0x30644e72e131a029 b85045b68181585d 97816a916871ca8d 3c208c16d87cfd45
#[no_mangle]
pub unsafe extern "C" fn _bn254_inv(out: *mut u64, x: *const u64) {
    const P_MINUS_2: [u64; 4] = [
        0x3c208c16d87cfd45,
        0x97816a916871ca8d,
        0xb85045b68181585d,
        0x30644e72e131a029,
    ];
    // Montgomery 1 = R mod p (verified: Python confirms 2^256 mod p)
    let mut result: [u64; 4] = [
        0xd35d438dc58f0d9d,
        0x0a78eb28f5c70b3d,
        0x666ea36f7879462c,
        0x0e0a77c19a07df2f,
    ];
    let mut base = read4(x);
    for limb_idx in 0..4 {
        let mut bits = P_MINUS_2[limb_idx];
        for _ in 0..64 {
            if bits & 1 == 1 {
                result = mont_mul(result, base);
            }
            base = mont_mul(base, base);
            bits >>= 1;
        }
    }
    write4(out, result);
}
