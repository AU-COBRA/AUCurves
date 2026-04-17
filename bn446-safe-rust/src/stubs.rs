//! Rust-side leaf ops for BN446.
//!
//! 7-limb little-endian Montgomery-form Fp elements (R = 2^448).
//! 446-bit prime fits comfortably in 7 limbs (top byte not full),
//! but we use n+2 accumulator anyway for parity with BN256.
//!
//! Curve: BN with seed u = 0x4000000000000000001000000001
//! Prime p = 36u^4 + 36u^3 + 24u^2 + 6u + 1 (446 bits).

const P: [u64; 7] = [
    0x0000132000000067,
    0x0057c00000015c00,
    0x870000000b040000,
    0x0000001800000000,
    0x00000d800000021c,
    0x002400000002d000,
    0x2400000000000000,
];

const N_PRIME: u64 = 0x6bd6c9022cbce4a9;

const R2: [u64; 7] = [
    0xd34e88fda2ae51de,
    0x96be2aa69f55a2aa,
    0xbf2f6e78b8f76882,
    0x38c7156da12c0355,
    0x596974c71b678406,
    0x6007fffb409d11c6,
    0x07fff258aaaaaa8a,
];

const MONT_ONE: [u64; 7] = [
    0xffff7a1ffffffd2f,
    0xfd99bffffff67bff,
    0x4effffffb2e3ffff,
    0xffffff57fffffffc,
    0xffffa17ffffff13b,
    0xff03ffffffec4fff,
    0x03ffffffffffffff,
];

const P_MINUS_2: [u64; 7] = [
    0x0000132000000065,
    0x0057c00000015c00,
    0x870000000b040000,
    0x0000001800000000,
    0x00000d800000021c,
    0x002400000002d000,
    0x2400000000000000,
];

#[inline(always)]
fn read7(p: *const u64) -> [u64; 7] {
    unsafe { [*p, *p.add(1), *p.add(2), *p.add(3), *p.add(4), *p.add(5), *p.add(6)] }
}

#[inline(always)]
fn write7(p: *mut u64, v: [u64; 7]) {
    unsafe {
        *p = v[0]; *p.add(1) = v[1]; *p.add(2) = v[2];
        *p.add(3) = v[3]; *p.add(4) = v[4]; *p.add(5) = v[5];
        *p.add(6) = v[6];
    }
}

#[inline(always)]
fn sub_p_if_ge(r: [u64; 8]) -> [u64; 7] {
    let (d0, b1) = r[0].overflowing_sub(P[0]);
    let (d1, b2a) = r[1].overflowing_sub(P[1]);
    let (d1, b2b) = d1.overflowing_sub(b1 as u64);
    let (d2, b3a) = r[2].overflowing_sub(P[2]);
    let (d2, b3b) = d2.overflowing_sub((b2a as u64) + (b2b as u64));
    let (d3, b4a) = r[3].overflowing_sub(P[3]);
    let (d3, b4b) = d3.overflowing_sub((b3a as u64) + (b3b as u64));
    let (d4, b5a) = r[4].overflowing_sub(P[4]);
    let (d4, b5b) = d4.overflowing_sub((b4a as u64) + (b4b as u64));
    let (d5, b6a) = r[5].overflowing_sub(P[5]);
    let (d5, b6b) = d5.overflowing_sub((b5a as u64) + (b5b as u64));
    let (d6, b7a) = r[6].overflowing_sub(P[6]);
    let (d6, b7b) = d6.overflowing_sub((b6a as u64) + (b6b as u64));
    let final_borrow = (b7a as u64) + (b7b as u64);
    if r[7] >= final_borrow {
        [d0, d1, d2, d3, d4, d5, d6]
    } else {
        [r[0], r[1], r[2], r[3], r[4], r[5], r[6]]
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn446_add(out: *mut u64, x: *const u64, y: *const u64) {
    let a = read7(x);
    let b = read7(y);
    let mut r = [0u64; 8];
    let (s0, c1) = a[0].overflowing_add(b[0]);
    r[0] = s0;
    let mut carry = c1 as u64;
    for i in 1..7 {
        let (s, ca) = a[i].overflowing_add(b[i]);
        let (s, cb) = s.overflowing_add(carry);
        r[i] = s;
        carry = (ca as u64) + (cb as u64);
    }
    r[7] = carry;
    write7(out, sub_p_if_ge(r));
}

#[no_mangle]
pub unsafe extern "C" fn _bn446_sub(out: *mut u64, x: *const u64, y: *const u64) {
    let a = read7(x);
    let b = read7(y);
    let (d0, b1) = a[0].overflowing_sub(b[0]);
    let mut r = [0u64; 7];
    r[0] = d0;
    let mut borrow = b1 as u64;
    for i in 1..7 {
        let (d, ba) = a[i].overflowing_sub(b[i]);
        let (d, bb) = d.overflowing_sub(borrow);
        r[i] = d;
        borrow = (ba as u64) + (bb as u64);
    }
    if borrow != 0 {
        let (a0, c1) = r[0].overflowing_add(P[0]);
        r[0] = a0;
        let mut c = c1 as u64;
        for i in 1..7 {
            let (s, ca) = r[i].overflowing_add(P[i]);
            let (s, cb) = s.overflowing_add(c);
            r[i] = s;
            c = (ca as u64) + (cb as u64);
        }
    }
    write7(out, r);
}

/// CIOS Montgomery multiplication for 7 limbs (n+2 accumulator).
#[inline(always)]
fn mont_mul(x: [u64; 7], y: [u64; 7]) -> [u64; 7] {
    let mut t = [0u64; 9];
    for i in 0..7 {
        let mut carry: u128 = 0;
        for j in 0..7 {
            let prod = (x[j] as u128) * (y[i] as u128) + (t[j] as u128) + carry;
            t[j] = prod as u64;
            carry = prod >> 64;
        }
        let s = (t[7] as u128) + carry;
        t[7] = s as u64;
        t[8] = (s >> 64) as u64;
        let m = (t[0]).wrapping_mul(N_PRIME);
        let mut carry: u128 = 0;
        for j in 0..7 {
            let prod = (m as u128) * (P[j] as u128) + (t[j] as u128) + carry;
            t[j] = prod as u64;
            carry = prod >> 64;
        }
        let s = (t[7] as u128) + carry;
        t[7] = s as u64;
        t[8] = t[8].wrapping_add((s >> 64) as u64);
        for j in 0..8 {
            t[j] = t[j + 1];
        }
        t[8] = 0;
    }
    let r = [t[0], t[1], t[2], t[3], t[4], t[5], t[6], t[7]];
    sub_p_if_ge(r)
}

#[no_mangle]
pub unsafe extern "C" fn _bn446_mul(out: *mut u64, x: *const u64, y: *const u64) {
    write7(out, mont_mul(read7(x), read7(y)));
}

#[no_mangle]
pub unsafe extern "C" fn _bn446_square(out: *mut u64, x: *const u64) {
    let xv = read7(x);
    write7(out, mont_mul(xv, xv));
}

#[no_mangle]
pub unsafe extern "C" fn _bn446_opp(out: *mut u64, x: *const u64) {
    unsafe {
        let mut borrow: u64 = 0;
        for i in 0..7 {
            let (d, b1) = P[i].overflowing_sub(*x.add(i));
            let (d2, b2) = d.overflowing_sub(borrow);
            *out.add(i) = d2;
            borrow = (b1 as u64) + (b2 as u64);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn446_felem_copy(out: *mut u64, x: *const u64) {
    unsafe { for i in 0..7 { *out.add(i) = *x.add(i); } }
}

#[no_mangle]
pub unsafe extern "C" fn _bn446_from_word(out: *mut u64, w: u64) {
    unsafe {
        if w == 0 {
            for i in 0..7 { *out.add(i) = 0; }
        } else if w == 1 {
            for i in 0..7 { *out.add(i) = MONT_ONE[i]; }
        } else {
            let r = mont_mul([w, 0, 0, 0, 0, 0, 0], R2);
            write7(out, r);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bn446_select_znz(
    out: *mut u64,
    c: u64,
    x: *const u64,
    y: *const u64,
) {
    let src = if c != 0 { x } else { y };
    unsafe { for i in 0..7 { *out.add(i) = *src.add(i); } }
}

#[no_mangle]
pub unsafe extern "C" fn _bn446_inv(out: *mut u64, x: *const u64) {
    let xv = read7(x);
    let mut result = MONT_ONE;
    let mut base = xv;
    for limb_idx in 0..7 {
        let mut bits = P_MINUS_2[limb_idx];
        for _ in 0..64 {
            if bits & 1 == 1 {
                result = mont_mul(result, base);
            }
            base = mont_mul(base, base);
            bits >>= 1;
        }
    }
    write7(out, result);
}
