use bn254::*;

fn main() {
    let a = Fp([1, 2, 3, 4]);
    let b = Fp([5, 6, 7, 8]);
    let mut c = Fp::zero();
    fp_add(&mut c, &a, &b);
    println!("fp_add OK: {:?}", c.0);

    let p_x = Fp([1, 0, 0, 0]);
    let p_y = Fp([2, 0, 0, 0]);
    let q_x = Fp2::zero();
    let q_y = Fp2::zero();
    let mut result = Fp12::zero();
    pairing(&mut result, &p_x, &p_y, &q_x, &q_y);
    println!("pairing OK: first limb = {:#x}", result.c0.c0.c0.0[0]);
}
