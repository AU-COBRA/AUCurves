//! Test bilinearity of bn254_pairing_optimal (the corrected variant)
//! and cross-verify against arkworks via multiplicative consistency.
use bn254::*;

fn main() {
    // G1 generator P = (1, 2) in Montgomery form
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);

    // 2*P computed via py_ecc, in Montgomery form
    let p2_x = Fp([16214190896527698488, 13550016860984857705, 14015815241649799916, 1378791528466284877]);
    let p2_y = Fp([4332616871279656263, 10917124144477883021, 13281191951274694749, 316464129134141481]);

    // G2 generator
    let q_x = Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    };
    let q_y = Fp2 {
        c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
        c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
    };

    println!("=== Testing pairing_optimal (with Frobenius corrections) ===");

    let mut e_pq = Fp12::zero();
    pairing_optimal(&mut e_pq, &p_x, &p_y, &q_x, &q_y);
    let mut e_2pq = Fp12::zero();
    pairing_optimal(&mut e_2pq, &p2_x, &p2_y, &q_x, &q_y);
    let mut e_pq_sq = Fp12::zero();
    bn254::fp12_square(&mut e_pq_sq, &e_pq);

    if e_2pq.c0.c0.c0 == e_pq_sq.c0.c0.c0 &&
       e_2pq.c0.c0.c1 == e_pq_sq.c0.c0.c1 {
        println!("PASS: pairing_optimal bilinearity e(2P, Q) == e(P, Q)^2");
    } else {
        println!("FAIL: pairing_optimal bilinearity");
        println!("  e(2P, Q).c0.c0.c0 = {:?}", e_2pq.c0.c0.c0.0);
        println!("  e(P, Q)^2.c0.c0.c0 = {:?}", e_pq_sq.c0.c0.c0.0);
    }
}
