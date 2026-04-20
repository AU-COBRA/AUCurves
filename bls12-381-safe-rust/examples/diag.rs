use bls12_381::*;
fn main() {
    let p_x = Fp([6679831729115696150, 8653662730902241269, 1535610680227111361,
                  17342916647841752903, 17135755455211762752, 1297449291367578485]);
    let p_y = Fp([13451288730302620273, 10097742279870053774, 15949884091978425806,
                  5885175747529691540, 1016841820992199104, 845620083434234474]);
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
    let mut e1 = Fp12::zero();
    let mut e2 = Fp12::zero();
    pairing(&mut e1, &p_x, &p_y, &q_x, &q_y);
    println!("e(P,Q).c0.c0.c0 = {:?}", e1.c0.c0.c0.0);
    // Check it's not all zero
    let all_zero = e1.c0.c0.c0.0.iter().all(|x| *x == 0);
    println!("all_zero: {}", all_zero);

    // Compare with the slow correct fallback
    let mut ml = Fp12::zero();
    miller_loop(&mut ml, &p_x, &p_y, &q_x, &q_y);
    println!("miller c0.c0.c0 = {:?}", ml.c0.c0.c0.0);

    // Quick check: is pairing output = 1 (identity)?
    // If so, the inputs might be on the wrong curve.
    let mont_one = Fp([0x760900000002fffd, 0xebf4000bc40c0002, 0x5f48985753c758ba,
                       0x77ce585370525745, 0x5c071a97a256ec6d, 0x15f65ec3fa80e493]);
    let is_one = e1.c0.c0.c0 == mont_one && e1.c0.c0.c1 == Fp::zero();
    println!("pairing output c0.c0 is (1,0)? {}", is_one);

    // Benchmark to estimate performance
    use std::time::Instant;
    let start = Instant::now();
    for _ in 0..10 { pairing(&mut e1, &p_x, &p_y, &q_x, &q_y); }
    let elapsed = start.elapsed();
    println!("10 pairings in {:?} → {:.2} ms/pairing", elapsed, elapsed.as_millis() as f64 / 10.0);
}
