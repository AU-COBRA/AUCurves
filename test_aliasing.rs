// Test that aliasing is rejected by Rust's borrow checker.
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
    let a = Fp::from_limbs([1u64; 6]);
    let b = Fp::from_limbs([2u64; 6]);
    let mut c = Fp::zero();
    fp_add(&mut c, &a, &b);
    println!("disjoint args: OK");

    let p_x = Fp::zero();
    let p_y = Fp::zero();
    let q_x = Fp2::zero();
    let q_y = Fp2::zero();
    let mut out = Fp12::zero();
    pairing(&mut out, &p_x, &p_y, &q_x, &q_y);
    println!("typed pairing API: OK");
}
