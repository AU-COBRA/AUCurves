use bn254::*;

const G1_X: Fp = Fp([15230403791020821917, 754611498739239741, 7381016538464732716, 1011752739694698287]);
const G1_Y: Fp = Fp([12014063508332092218, 1509222997478479483, 14762033076929465432, 2023505479389396574]);

fn main() {
    let q_x = Fp2 { c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
                     c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]) };
    let q_y = Fp2 { c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
                     c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]) };
    let mut ml_bare = Fp12::zero();
    let mut ml_opt = Fp12::zero();
    miller_loop(&mut ml_bare, &G1_X, &G1_Y, &q_x, &q_y);
    miller_loop_optimal(&mut ml_opt, &G1_X, &G1_Y, &q_x, &q_y);
    // Compare all 12 limbs of c0.c0
    println!("Miller loop bare c0.c0: {:?}", ml_bare.c0.c0.c0.0);
    println!("Miller loop opt  c0.c0: {:?}", ml_opt.c0.c0.c0.0);
    println!("Same c0.c0.c0: {}", ml_bare.c0.c0.c0 == ml_opt.c0.c0.c0);
}
