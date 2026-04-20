//! Rust-side leaf ops for BLS12-381.
//!
//! 6-limb little-endian Montgomery-form Fp elements (R = 2^384).
//! Prime:
//!   p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

const P: [u64; 6] = [
    0xb9feffffffffaaab,
    0x1eabfffeb153ffff,
    0x6730d2a0f6b0f624,
    0x64774b84f38512bf,
    0x4b1ba7b6434bacd7,
    0x1a0111ea397fe69a,
];

/// -1/p[0] mod 2^64, used by CIOS Montgomery reduction.
const N_PRIME: u64 = 0x89f3fffcfffcfffd;

/// R^2 mod p (R = 2^384), needed for from_word general case.
const R2: [u64; 6] = [
    0xf4df1f341c341746,
    0x0a76e6a609d104f1,
    0x8de5476c4c95b6d5,
    0x67eb88a9939d83c0,
    0x9a793e85b519952d,
    0x11988fe592cae3aa,
];

/// 1 in Montgomery form (R mod p).
const MONT_ONE: [u64; 6] = [
    0x760900000002fffd,
    0xebf4000bc40c0002,
    0x5f48985753c758ba,
    0x77ce585370525745,
    0x5c071a97a256ec6d,
    0x15f65ec3fa80e493,
];

#[inline(always)]
fn read6(p: *const u64) -> [u64; 6] {
    unsafe { [*p, *p.add(1), *p.add(2), *p.add(3), *p.add(4), *p.add(5)] }
}

#[inline(always)]
fn write6(p: *mut u64, v: [u64; 6]) {
    unsafe {
        *p = v[0]; *p.add(1) = v[1]; *p.add(2) = v[2];
        *p.add(3) = v[3]; *p.add(4) = v[4]; *p.add(5) = v[5];
    }
}

/// Conditional subtract p from a 7-limb intermediate (6 + carry); the top limb is r[6].
#[inline(always)]
fn sub_p_if_ge(r: [u64; 7]) -> [u64; 6] {
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
    let final_borrow = (b6a as u64) + (b6b as u64);
    if r[6] >= final_borrow {
        [d0, d1, d2, d3, d4, d5]
    } else {
        [r[0], r[1], r[2], r[3], r[4], r[5]]
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bls12_add(out: *mut u64, x: *const u64, y: *const u64) {
    let a = read6(x);
    let b = read6(y);
    let mut r = [0u64; 7];
    let (s0, c1) = a[0].overflowing_add(b[0]);
    r[0] = s0;
    let mut carry = c1 as u64;
    for i in 1..6 {
        let (s, ca) = a[i].overflowing_add(b[i]);
        let (s, cb) = s.overflowing_add(carry);
        r[i] = s;
        carry = (ca as u64) + (cb as u64);
    }
    r[6] = carry;
    write6(out, sub_p_if_ge(r));
}

#[no_mangle]
pub unsafe extern "C" fn _bls12_sub(out: *mut u64, x: *const u64, y: *const u64) {
    let a = read6(x);
    let b = read6(y);
    let (d0, b1) = a[0].overflowing_sub(b[0]);
    let mut r = [0u64; 6];
    r[0] = d0;
    let mut borrow = b1 as u64;
    for i in 1..6 {
        let (d, ba) = a[i].overflowing_sub(b[i]);
        let (d, bb) = d.overflowing_sub(borrow);
        r[i] = d;
        borrow = (ba as u64) + (bb as u64);
    }
    if borrow != 0 {
        // Add p back.
        let (a0, c1) = r[0].overflowing_add(P[0]);
        r[0] = a0;
        let mut c = c1 as u64;
        for i in 1..6 {
            let (s, ca) = r[i].overflowing_add(P[i]);
            let (s, cb) = s.overflowing_add(c);
            r[i] = s;
            c = (ca as u64) + (cb as u64);
        }
    }
    write6(out, r);
}

/// CIOS Montgomery multiplication for 6 limbs: out = (x * y * R^{-1}) mod p, R = 2^384.
#[inline(always)]
fn mont_mul(x: [u64; 6], y: [u64; 6]) -> [u64; 6] {
    // CIOS form keeps a 7-wide accumulator; t[6] holds the high-end carry.
    let mut t = [0u64; 7];
    for i in 0..6 {
        // Step 1: t = t + x * y[i]
        let mut carry: u128 = 0;
        for j in 0..6 {
            let prod = (x[j] as u128) * (y[i] as u128) + (t[j] as u128) + carry;
            t[j] = prod as u64;
            carry = prod >> 64;
        }
        let s = (t[6] as u128) + carry;
        t[6] = s as u64; // high carry kept (s fits in u64 because t<2p and product carries are bounded)
        // Step 2: m = t[0] * N_PRIME mod 2^64
        let m = (t[0]).wrapping_mul(N_PRIME);
        // Step 3: t = t + m * p; this makes t[0] divisible by 2^64
        let mut carry: u128 = 0;
        for j in 0..6 {
            let prod = (m as u128) * (P[j] as u128) + (t[j] as u128) + carry;
            t[j] = prod as u64;
            carry = prod >> 64;
        }
        let s = (t[6] as u128) + carry;
        t[6] = s as u64;
        // Step 4: shift t right by one limb
        for j in 0..6 {
            t[j] = t[j + 1];
        }
        t[6] = 0;
    }
    let r = [t[0], t[1], t[2], t[3], t[4], t[5], 0u64];
    sub_p_if_ge(r)
}

#[cfg(not(feature = "cryptopt"))]
#[no_mangle]
pub unsafe extern "C" fn _bls12_mul(out: *mut u64, x: *const u64, y: *const u64) {
    write6(out, mont_mul(read6(x), read6(y)));
}

#[cfg(not(feature = "cryptopt"))]
#[no_mangle]
pub unsafe extern "C" fn _bls12_square(out: *mut u64, x: *const u64) {
    let xv = read6(x);
    write6(out, mont_mul(xv, xv));
}

#[no_mangle]
pub unsafe extern "C" fn _bls12_opp(out: *mut u64, x: *const u64) {
    unsafe {
        let mut borrow: u64 = 0;
        for i in 0..6 {
            let (d, b1) = P[i].overflowing_sub(*x.add(i));
            let (d2, b2) = d.overflowing_sub(borrow);
            *out.add(i) = d2;
            borrow = (b1 as u64) + (b2 as u64);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bls12_felem_copy(out: *mut u64, x: *const u64) {
    unsafe {
        for i in 0..6 {
            *out.add(i) = *x.add(i);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bls12_from_word(out: *mut u64, w: u64) {
    unsafe {
        if w == 0 {
            for i in 0..6 { *out.add(i) = 0; }
        } else if w == 1 {
            for i in 0..6 { *out.add(i) = MONT_ONE[i]; }
        } else {
            // General case: mont_mul([w,0,...,0], R^2)
            let r = mont_mul([w, 0, 0, 0, 0, 0], R2);
            write6(out, r);
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn _bls12_select_znz(
    out: *mut u64,
    c: u64,
    x: *const u64,
    y: *const u64,
) {
    let src = if c != 0 { x } else { y };
    unsafe {
        for i in 0..6 {
            *out.add(i) = *src.add(i);
        }
    }
}

/// Inversion via Fermat: x^(p-2). Used by Fp2_inv (called from the tower).
#[no_mangle]
pub unsafe extern "C" fn _bls12_inv(out: *mut u64, x: *const u64) {
    // p - 2 limbs (little-endian)
    const P_MINUS_2: [u64; 6] = [
        0xb9feffffffffaaa9,
        0x1eabfffeb153ffff,
        0x6730d2a0f6b0f624,
        0x64774b84f38512bf,
        0x4b1ba7b6434bacd7,
        0x1a0111ea397fe69a,
    ];
    let xv = read6(x);
    // result = 1 in Montgomery form
    let mut result = MONT_ONE;
    let mut base = xv;
    for limb_idx in 0..6 {
        let mut bits = P_MINUS_2[limb_idx];
        for _ in 0..64 {
            if bits & 1 == 1 {
                result = mont_mul(result, base);
            }
            base = mont_mul(base, base);
            bits >>= 1;
        }
    }
    write6(out, result);
}
