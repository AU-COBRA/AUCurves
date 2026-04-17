//! Rust-side leaf ops for BN256.
//!
//! 4-limb little-endian Montgomery-form Fp elements (R = 2^256).
//! WordByWordMontgomery derives n=4 limbs automatically from the
//! 256-bit prime. (SafeRustBN256Concrete.v's "5 limbs" comment is
//! about a different padded representation; the bedrock2 source
//! tower uses 4 limbs.)
//!
//! Curve: BN with seed u = 0x5A76AE9AEC588301
//! Prime p = 36u^4 + 36u^3 + 24u^2 + 6u + 1 (256 bits).

const P: [u64; 4] = [
    0x185cac6c5e089667,
    0xee5b88d120b5b59e,
    0xaa6fecb86184dc21,
    0x8fb501e34aa387f9,
];

/// -1/p[0] mod 2^64, used by CIOS Montgomery reduction.
const N_PRIME: u64 = 0x2387f9007f17daa9;

/// R^2 mod p (R = 2^256), needed for from_word general case.
const R2: [u64; 4] = [
    0x9c21c3ff7e444f56,
    0x409ed151b2efb0c2,
    0x0c6dc37b80fb1651,
    0x7c36e0e62c2380b7,
];

/// 1 in Montgomery form (R mod p).
const MONT_ONE: [u64; 4] = [
    0xe7a35393a1f76999,
    0x11a4772edf4a4a61,
    0x559013479e7b23de,
    0x704afe1cb55c7806,
];

const P_MINUS_2: [u64; 4] = [
    0x185cac6c5e089665,
    0xee5b88d120b5b59e,
    0xaa6fecb86184dc21,
    0x8fb501e34aa387f9,
];

#[inline(always)]
fn read4(p: *const u64) -> [u64; 4] {
    unsafe { [*p, *p.add(1), *p.add(2), *p.add(3)] }
}

#[inline(always)]
fn write4(p: *mut u64, v: [u64; 4]) {
    unsafe {
        *p = v[0]; *p.add(1) = v[1]; *p.add(2) = v[2]; *p.add(3) = v[3];
    }
}

/// Conditional subtract p from a 5-limb intermediate (4 + carry).
#[inline(always)]
fn sub_p_if_ge(r: [u64; 5]) -> [u64; 4] {
    let (d0, b1) = r[0].overflowing_sub(P[0]);
    let (d1, b2a) = r[1].overflowing_sub(P[1]);
    let (d1, b2b) = d1.overflowing_sub(b1 as u64);
    let (d2, b3a) = r[2].overflowing_sub(P[2]);
    let (d2, b3b) = d2.overflowing_sub((b2a as u64) + (b2b as u64));
    let (d3, b4a) = r[3].overflowing_sub(P[3]);
    let (d3, b4b) = d3.overflowing_sub((b3a as u64) + (b3b as u64));
    let final_borrow = (b4a as u64) + (b4b as u64);
    if r[4] >= final_borrow {
        [d0, d1, d2, d3]
    } else {
        [r[0], r[1], r[2], r[3]]
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn256_add(out: *mut u64, x: *const u64, y: *const u64) {
    let a = read4(x);
    let b = read4(y);
    let mut r = [0u64; 5];
    let (s0, c1) = a[0].overflowing_add(b[0]);
    r[0] = s0;
    let mut carry = c1 as u64;
    for i in 1..4 {
        let (s, ca) = a[i].overflowing_add(b[i]);
        let (s, cb) = s.overflowing_add(carry);
        r[i] = s;
        carry = (ca as u64) + (cb as u64);
    }
    r[4] = carry;
    write4(out, sub_p_if_ge(r));
}

#[no_mangle]
pub unsafe extern "C" fn _bn256_sub(out: *mut u64, x: *const u64, y: *const u64) {
    let a = read4(x);
    let b = read4(y);
    let (d0, b1) = a[0].overflowing_sub(b[0]);
    let mut r = [0u64; 4];
    r[0] = d0;
    let mut borrow = b1 as u64;
    for i in 1..4 {
        let (d, ba) = a[i].overflowing_sub(b[i]);
        let (d, bb) = d.overflowing_sub(borrow);
        r[i] = d;
        borrow = (ba as u64) + (bb as u64);
    }
    if borrow != 0 {
        let (a0, c1) = r[0].overflowing_add(P[0]);
        r[0] = a0;
        let mut c = c1 as u64;
        for i in 1..4 {
            let (s, ca) = r[i].overflowing_add(P[i]);
            let (s, cb) = s.overflowing_add(c);
            r[i] = s;
            c = (ca as u64) + (cb as u64);
        }
    }
    write4(out, r);
}

/// CIOS Montgomery multiplication for 4 limbs: out = (x * y * R^{-1}) mod p, R = 2^256.
///
/// Uses n+2 accumulator (t[0..5]) so the high carry is preserved across
/// step1 + step2 within an outer iteration.  BN256's prime has its top
/// bit set (p > 2^255, 2p > 2^256), so naïve CIOS with only n+1 limbs
/// loses a bit during reduction.  The standard textbook algorithm is
/// T[0..n+1] (n+2 limbs); cf. Acar 1998 §4.1 and Garner 1965.
#[inline(always)]
fn mont_mul(x: [u64; 4], y: [u64; 4]) -> [u64; 4] {
    let mut t = [0u64; 6];
    for i in 0..4 {
        let mut carry: u128 = 0;
        for j in 0..4 {
            let prod = (x[j] as u128) * (y[i] as u128) + (t[j] as u128) + carry;
            t[j] = prod as u64;
            carry = prod >> 64;
        }
        let s = (t[4] as u128) + carry;
        t[4] = s as u64;
        t[5] = (s >> 64) as u64;
        let m = (t[0]).wrapping_mul(N_PRIME);
        let mut carry: u128 = 0;
        for j in 0..4 {
            let prod = (m as u128) * (P[j] as u128) + (t[j] as u128) + carry;
            t[j] = prod as u64;
            carry = prod >> 64;
        }
        let s = (t[4] as u128) + carry;
        t[4] = s as u64;
        t[5] = t[5].wrapping_add((s >> 64) as u64);
        for j in 0..5 {
            t[j] = t[j + 1];
        }
        t[5] = 0;
    }
    let r = [t[0], t[1], t[2], t[3], t[4]];
    sub_p_if_ge(r)
}

#[no_mangle]
pub unsafe extern "C" fn _bn256_mul(out: *mut u64, x: *const u64, y: *const u64) {
    write4(out, mont_mul(read4(x), read4(y)));
}

#[no_mangle]
pub unsafe extern "C" fn _bn256_square(out: *mut u64, x: *const u64) {
    let xv = read4(x);
    write4(out, mont_mul(xv, xv));
}

#[no_mangle]
pub unsafe extern "C" fn _bn256_opp(out: *mut u64, x: *const u64) {
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
pub unsafe extern "C" fn _bn256_felem_copy(out: *mut u64, x: *const u64) {
    unsafe {
        for i in 0..4 {
            *out.add(i) = *x.add(i);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn256_from_word(out: *mut u64, w: u64) {
    unsafe {
        if w == 0 {
            for i in 0..4 { *out.add(i) = 0; }
        } else if w == 1 {
            for i in 0..4 { *out.add(i) = MONT_ONE[i]; }
        } else {
            let r = mont_mul([w, 0, 0, 0], R2);
            write4(out, r);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn256_select_znz(
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

#[no_mangle]
pub unsafe extern "C" fn _bn256_inv(out: *mut u64, x: *const u64) {
    let xv = read4(x);
    let mut result = MONT_ONE;
    let mut base = xv;
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
