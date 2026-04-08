use bn254::*;

fn main() {
    let a = Fp::from_limbs([1, 2, 3, 4]);
    let b = Fp::from_limbs([5, 6, 7, 8]);
    let mut c = Fp::zero();
    fp_add(&mut c, &a, &b);
    println!("fp_add OK: {:?}", c.as_limbs());

    let p_x = Fp::from_limbs([1, 0, 0, 0]);
    let p_y = Fp::from_limbs([2, 0, 0, 0]);
    let q_x = Fp2::zero();
    let q_y = Fp2::zero();
    let mut result = Fp12::zero();
    pairing(&mut result, &p_x, &p_y, &q_x, &q_y);
    println!("pairing OK: first limb = {:#x}", result.as_limbs()[0]);
}
