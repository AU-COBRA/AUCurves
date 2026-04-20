use bls12_381::*;
use std::time::Instant;

fn main() {
    // BLS12-381 G1 generator in Montgomery form (R = 2^384)
    let p_x = Fp([6679831729115696150, 8653662730902241269, 1535610680227111361,
                  17342916647841752903, 17135755455211762752, 1297449291367578485]);
    let p_y = Fp([13451288730302620273, 10097742279870053774, 15949884091978425806,
                  5885175747529691540, 1016841820992199104, 845620083434234474]);
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

    // Warmup
    let mut out = Fp12::zero();
    pairing(&mut out, &p_x, &p_y, &q_x, &q_y);

    // Benchmark Fp mul
    let a = p_x;
    let b = p_y;
    let mut c = Fp::zero();
    let n_mul = 1_000_000;
    let start = Instant::now();
    for _ in 0..n_mul { fp_mul(&mut c, &a, &b); }
    let elapsed = start.elapsed();
    println!("Fp mul:     {:.1} ns ({} iters)", elapsed.as_nanos() as f64 / n_mul as f64, n_mul);

    // Benchmark pairing
    let n_pair = 50;
    let start = Instant::now();
    for _ in 0..n_pair { pairing(&mut out, &p_x, &p_y, &q_x, &q_y); }
    let elapsed = start.elapsed();
    println!("Pairing:    {:.1} us ({} iters)", elapsed.as_micros() as f64 / n_pair as f64, n_pair);
    println!("            {:.2} ms per pairing", elapsed.as_millis() as f64 / n_pair as f64);
}
