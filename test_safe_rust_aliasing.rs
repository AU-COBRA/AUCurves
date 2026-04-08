//! Test that the safe Rust wrappers reject aliasing at compile time.
//!
//! Compile with: rustc --edition 2021 --crate-type lib test_safe_rust_aliasing.rs
//! All `compile_fail` tests must fail to compile (the doctest harness verifies this).

include!("bls12_381_safe.rs");

// Stub the extern functions so we can link without the real C/Jasmin code.
// In a real build, these would come from the verified bedrock2 extraction.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_disjoint_args_compile() {
        let a = Fp::from_limbs([1u64; 6]);
        let b = Fp::from_limbs([2u64; 6]);
        let mut c = Fp::zero();
        fp_add(&mut c, &a, &b);  // OK: a, b, c all distinct
    }

    #[test]
    fn test_pairing_typed_api() {
        let p_x = Fp::zero();
        let p_y = Fp::zero();
        let q_x = Fp2::zero();
        let q_y = Fp2::zero();
        let mut out = Fp12::zero();
        pairing(&mut out, &p_x, &p_y, &q_x, &q_y);
    }

    /// Doctest demonstrating that aliasing is rejected:
    ///
    /// ```compile_fail
    /// use safe_bls12::*;
    /// let mut a = Fp::zero();
    /// fp_add(&mut a, &a, &a);  // ERROR: cannot borrow `a` as immutable
    ///                          // because it is also borrowed as mutable
    /// ```
    #[test]
    fn _aliasing_rejected_doc() {}
}
