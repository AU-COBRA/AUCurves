use bn254::*;

fn fp12_eq(a: &Fp12, b: &Fp12) -> bool {
    a.c0.c0.c0 == b.c0.c0.c0 && a.c0.c0.c1 == b.c0.c0.c1 &&
    a.c0.c1.c0 == b.c0.c1.c0 && a.c0.c1.c1 == b.c0.c1.c1 &&
    a.c0.c2.c0 == b.c0.c2.c0 && a.c0.c2.c1 == b.c0.c2.c1 &&
    a.c1.c0.c0 == b.c1.c0.c0 && a.c1.c0.c1 == b.c1.c0.c1 &&
    a.c1.c1.c0 == b.c1.c1.c0 && a.c1.c1.c1 == b.c1.c1.c1 &&
    a.c1.c2.c0 == b.c1.c2.c0 && a.c1.c2.c1 == b.c1.c2.c1
}

fn main() {
    let g1_x = Fp([1, 0, 0, 0]); // degenerate input for comparison
    let g1_y = Fp([2, 0, 0, 0]);
    let q_x = Fp2 { c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
                     c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]) };
    let q_y = Fp2 { c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
                     c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]) };
    let mut bare = Fp12::zero();
    let mut optimal = Fp12::zero();
    miller_loop(&mut bare, &g1_x, &g1_y, &q_x, &q_y);
    miller_loop_optimal(&mut optimal, &g1_x, &g1_y, &q_x, &q_y);
    println!("bare c0.c0.c0: {:?}", bare.c0.c0.c0.0);
    println!("opt  c0.c0.c0: {:?}", optimal.c0.c0.c0.0);
    println!("bare==opt (before corrections): {}", fp12_eq(&bare, &optimal));
    // pairing includes final exp
    let mut p_bare = Fp12::zero();
    let mut p_opt = Fp12::zero();
    pairing(&mut p_bare, &g1_x, &g1_y, &q_x, &q_y);
    pairing_optimal(&mut p_opt, &g1_x, &g1_y, &q_x, &q_y);
    println!("pairing_bare c0.c0.c0: {:?}", p_bare.c0.c0.c0.0);
    println!("pairing_opt  c0.c0.c0: {:?}", p_opt.c0.c0.c0.0);
}
