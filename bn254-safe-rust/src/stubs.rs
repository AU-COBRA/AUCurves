//! Stub implementations for testing. In production, these come from
//! Jasmin-compiled assembly (bn254_leaves.s → bn254_leaves.o).

#[no_mangle] pub unsafe extern "C" fn _bn254_add(out: *mut u64, x: *const u64, y: *const u64) {
    for i in 0..4 { *out.add(i) = (*x.add(i)).wrapping_add(*y.add(i)); }
}
#[no_mangle] pub unsafe extern "C" fn _bn254_sub(out: *mut u64, x: *const u64, y: *const u64) {
    for i in 0..4 { *out.add(i) = (*x.add(i)).wrapping_sub(*y.add(i)); }
}
#[no_mangle] pub unsafe extern "C" fn _bn254_mul(out: *mut u64, _x: *const u64, _y: *const u64) {
    for i in 0..4 { *out.add(i) = 0; } // stub
}
#[no_mangle] pub unsafe extern "C" fn _bn254_square(out: *mut u64, _x: *const u64) {
    for i in 0..4 { *out.add(i) = 0; } // stub
}
#[no_mangle] pub unsafe extern "C" fn _bn254_opp(out: *mut u64, x: *const u64) {
    for i in 0..4 { *out.add(i) = (!*x.add(i)).wrapping_add(if i == 0 { 1 } else { 0 }); }
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
