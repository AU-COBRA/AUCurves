use bn254::*;

fn main() {
    let g1_x = Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]);
    let g1_y = Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]);
    let q_x = Fp2 { c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
                     c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]) };
    let q_y = Fp2 { c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
                     c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]) };
    // Test: bare pairing consistency
    let mut p1 = Fp12::zero();
    let mut p2 = Fp12::zero();
    pairing(&mut p1, &g1_x, &g1_y, &q_x, &q_y);
    pairing(&mut p2, &g1_x, &g1_y, &q_x, &q_y);
    println!("bare consistent: {}", p1.c0.c0.c0 == p2.c0.c0.c0);
    
    // Test: optimal pairing consistency
    let mut o1 = Fp12::zero();
    let mut o2 = Fp12::zero();
    pairing_optimal(&mut o1, &g1_x, &g1_y, &q_x, &q_y);
    pairing_optimal(&mut o2, &g1_x, &g1_y, &q_x, &q_y);
    println!("optimal consistent: {}", o1.c0.c0.c0 == o2.c0.c0.c0);
    
    // Compare bare vs optimal
    println!("bare==opt: {}", p1.c0.c0.c0 == o1.c0.c0.c0);
    println!("bare: {:?}", p1.c0.c0.c0.0);
    println!("opt:  {:?}", o1.c0.c0.c0.0);
}
