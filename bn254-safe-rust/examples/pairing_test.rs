//! End-to-end pairing validation against py_ecc.
//!
//! Direct limb-by-limb comparison against py_ecc would not work: py_ecc
//! represents Fp12 as Fp[w]/(w^12 - 18 w^6 + 82) with the basis
//! (1, w, ..., w^11), whereas the bedrock2-extracted tower uses
//! Fp -> Fp2[u]/(u^2+1) -> Fp6[v]/(v^3 - (9+u)) -> Fp12[w]/(w^2 - v),
//! which has a different (but isomorphic) basis. We instead do a
//! basis-independent **bilinearity** check:
//!
//!     e(2*P, Q) == e(P, Q)^2     (computed in the tower basis)
//!
//! Both sides are computed entirely in the safe-Rust tower, so the
//! comparison only depends on the tower's internal consistency, which
//! is exactly what we want to validate. The 2*G1 coordinates are
//! pre-computed via py_ecc and embedded as Montgomery limbs.

use bn254::*;

fn main() {
    // G1 generator (1, 2) in Montgomery form
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);

    // 2*G1, computed via py_ecc (group law on alt_bn128), in Montgomery form
    let p2_x = Fp([16214190896527698488, 13550016860984857705, 14015815241649799916, 1378791528466284877]);
    let p2_y = Fp([4332616871279656263, 10917124144477883021, 13281191951274694749, 316464129134141481]);

    // G2 generator in Montgomery form
    let q_x = Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    };
    let q_y = Fp2 {
        c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
        c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
    };

    // Compute e(P, Q) and e(2P, Q)
    let mut e_pq = Fp12::zero();
    pairing(&mut e_pq, &p_x, &p_y, &q_x, &q_y);
    let mut e_2pq = Fp12::zero();
    pairing(&mut e_2pq, &p2_x, &p2_y, &q_x, &q_y);

    // Compute e(P, Q)^2 by squaring in Fp12
    let mut e_pq_sq = Fp12::zero();
    bn254::fp12_square(&mut e_pq_sq, &e_pq);

    // Bilinearity: e(2P, Q) should equal e(P, Q)^2
    if e_2pq.c0.c0.c0 == e_pq_sq.c0.c0.c0 &&
       e_2pq.c0.c0.c1 == e_pq_sq.c0.c0.c1 &&
       e_2pq.c0.c1.c0 == e_pq_sq.c0.c1.c0 &&
       e_2pq.c0.c1.c1 == e_pq_sq.c0.c1.c1 &&
       e_2pq.c0.c2.c0 == e_pq_sq.c0.c2.c0 &&
       e_2pq.c0.c2.c1 == e_pq_sq.c0.c2.c1 &&
       e_2pq.c1.c0.c0 == e_pq_sq.c1.c0.c0 &&
       e_2pq.c1.c0.c1 == e_pq_sq.c1.c0.c1 &&
       e_2pq.c1.c1.c0 == e_pq_sq.c1.c1.c0 &&
       e_2pq.c1.c1.c1 == e_pq_sq.c1.c1.c1 &&
       e_2pq.c1.c2.c0 == e_pq_sq.c1.c2.c0 &&
       e_2pq.c1.c2.c1 == e_pq_sq.c1.c2.c1
    {
        println!("PASS: e(2P, Q) == e(P, Q)^2 (bilinearity check)");
    } else {
        println!("FAIL: bilinearity check failed");
        println!("  e(2P, Q).c0.c0.c0 = {:?}", e_2pq.c0.c0.c0.0);
        println!("  e(P, Q)^2.c0.c0.c0 = {:?}", e_pq_sq.c0.c0.c0.0);
        std::process::exit(1);
    }
}
