mod safe { include!("bls12_381_safe_inner.rs"); }
use safe::*;

#[no_mangle] pub extern "C" fn bls12_add(_: usize, _: usize, _: usize) {}
#[no_mangle] pub extern "C" fn bls12_sub(_: usize, _: usize, _: usize) {}
#[no_mangle] pub extern "C" fn bls12_mul(_: usize, _: usize, _: usize) {}
#[no_mangle] pub extern "C" fn bls12_square(_: usize, _: usize) {}
#[no_mangle] pub extern "C" fn bls12_Fp2_add(_: usize, _: usize, _: usize) {}
#[no_mangle] pub extern "C" fn bls12_Fp2_mul(_: usize, _: usize, _: usize) {}
#[no_mangle] pub extern "C" fn bls12_Fp12_mul(_: usize, _: usize, _: usize) {}
#[no_mangle] pub extern "C" fn bls12_Fp12_square(_: usize, _: usize) {}
#[no_mangle] pub extern "C" fn bls12_miller_loop(_: usize, _: usize, _: usize, _: usize, _: usize) {}
#[no_mangle] pub extern "C" fn bls12_pairing(_: usize, _: usize, _: usize, _: usize, _: usize) {}

fn main() {
    let mut a = Fp::zero();
    fp_add(&mut a, &a, &a);  // SHOULD FAIL: a borrowed mutably and immutably
}
