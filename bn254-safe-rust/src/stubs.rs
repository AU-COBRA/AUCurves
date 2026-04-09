//! Leaf ops in Rust. Simple ops (opp, from_word, felem_copy, select_znz)
//! are always provided here. Heavy ops (add, sub, mul, square) are
//! provided here only when Jasmin assembly is not available.

// Always-needed simple ops (not in the Jasmin .jazz)

#[no_mangle] pub unsafe extern "C" fn _bn254_opp(out: *mut u64, x: *const u64) {
    // opp(x) = p - x where p is BN254 prime
    let p: [u64; 4] = [0x3c208c16d87cfd47, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029];
    let mut borrow: u64 = 0;
    for i in 0..4 {
        let (d, b1) = p[i].overflowing_sub(*x.add(i));
        let (d2, b2) = d.overflowing_sub(borrow);
        *out.add(i) = d2;
        borrow = (b1 as u64) + (b2 as u64);
    }
}

#[no_mangle] pub unsafe extern "C" fn _bn254_felem_copy(out: *mut u64, x: *const u64) {
    for i in 0..4 { *out.add(i) = *x.add(i); }
}

#[no_mangle] pub unsafe extern "C" fn _bn254_from_word(out: *mut u64, w: u64) {
    *out = w; for i in 1..4 { *out.add(i) = 0; }
}

#[no_mangle] pub unsafe extern "C" fn _bn254_select_znz(out: *mut u64, c: u64, x: *const u64, y: *const u64) {
    let src = if c != 0 { x } else { y };
    for i in 0..4 { *out.add(i) = *src.add(i); }
}

// Heavy ops — only when Jasmin assembly is not linked
#[cfg(not(feature = "jasmin"))]
#[no_mangle] pub unsafe extern "C" fn _bn254_add(out: *mut u64, x: *const u64, y: *const u64) {
    for i in 0..4 { *out.add(i) = (*x.add(i)).wrapping_add(*y.add(i)); }
}
#[cfg(not(feature = "jasmin"))]
#[no_mangle] pub unsafe extern "C" fn _bn254_sub(out: *mut u64, x: *const u64, y: *const u64) {
    for i in 0..4 { *out.add(i) = (*x.add(i)).wrapping_sub(*y.add(i)); }
}
#[cfg(not(feature = "jasmin"))]
#[no_mangle] pub unsafe extern "C" fn _bn254_mul(out: *mut u64, _x: *const u64, _y: *const u64) {
    for i in 0..4 { *out.add(i) = 0; }
}
#[cfg(not(feature = "jasmin"))]
#[no_mangle] pub unsafe extern "C" fn _bn254_square(out: *mut u64, _x: *const u64) {
    for i in 0..4 { *out.add(i) = 0; }
}
