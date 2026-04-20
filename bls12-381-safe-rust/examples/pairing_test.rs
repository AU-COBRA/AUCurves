//! Bilinearity check for the BLS12-381 pairing tower:
//!     e(2*P, Q) == e(P, Q)^2
//! Both sides are computed entirely inside the safe-Rust BLS12-381 tower,
//! so the check only depends on the tower's internal consistency.

use bls12_381::*;

fn main() {
    // BLS12-381 G1 generator in Montgomery form (R = 2^384)
    let p_x = Fp([6679831729115696150, 8653662730902241269, 1535610680227111361,
                  17342916647841752903, 17135755455211762752, 1297449291367578485]);
    let p_y = Fp([13451288730302620273, 10097742279870053774, 15949884091978425806,
                  5885175747529691540, 1016841820992199104, 845620083434234474]);
    // 2*G1 (precomputed via affine doubling on E: y² = x³ + 4)
    let p2_x = Fp([6046496802367715900, 4512703842675942905, 5557647857818872160,
                   11911007586355426777, 2789226406901363231, 2402832991291269]);
    let p2_y = Fp([8075247918781118784, 15723127573743364860, 13289805640942397317,
                   12593984073093990549, 2724610382811436832, 447576566110657301]);
    // BLS12-381 G2 generator in Montgomery form
    let q_x = Fp2 {
        c0: Fp([17722385409647053328, 12967546844987299354, 11648722842835150208,
                10994581490347323113, 8027586497049998955, 396758299565931735]),
        c1: Fp([11937283898719073798, 12295044263989567683, 4301357764460312582,
                1953074377943790439, 14030662337566180679, 1266120665323335155]),
    };
    let q_y = Fp2 {
        c0: Fp([5508758831087832138, 6448303779119275098, 16710190169160573786,
                13542242618704742751, 563980702369916322, 37152010398653157]),
        c1: Fp([12520284671833321565, 1777275927576994268, 9704602344324656032,
                8739618045342622522, 16651875250601773805, 804950956836789234]),
    };

    let mut e_pq = Fp12::zero();
    pairing(&mut e_pq, &p_x, &p_y, &q_x, &q_y);
    let mut e_2pq = Fp12::zero();
    pairing(&mut e_2pq, &p2_x, &p2_y, &q_x, &q_y);

    let mut e_pq_sq = Fp12::zero();
    bls12_381::fp12_square(&mut e_pq_sq, &e_pq);

    let eq = e_2pq.c0.c0.c0 == e_pq_sq.c0.c0.c0 &&
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
             e_2pq.c1.c2.c1 == e_pq_sq.c1.c2.c1;

    if eq {
        println!("PASS: e(2P, Q) == e(P, Q)^2 (BLS12-381 bilinearity check)");
    } else {
        println!("FAIL: BLS12-381 bilinearity check failed");
        println!("  e(2P, Q).c0.c0.c0 = {:?}", e_2pq.c0.c0.c0.0);
        println!("  e(P, Q)^2.c0.c0.c0 = {:?}", e_pq_sq.c0.c0.c0.0);
        std::process::exit(1);
    }
}
