//! Measure what fraction of the Miller-loop time is fp2_inv.
//!
//! The affine Miller loop does one fp2_inv per doubling/addition step
//! (~70 steps for BN254 with loop param 6u+2). If fp2_inv dominates,
//! switching to projective is worth the refactor cost; if it doesn't,
//! the gap is elsewhere.
use bn254::*;
use std::time::Instant;

const N: usize = 100_000;
const N_MILLER: usize = 100;

fn main() {
    // A non-trivial Fp2 to invert repeatedly.
    let a = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
    let b = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);
    let x = Fp2 { c0: a, c1: b };
    let mut out = Fp2::zero();

    // Warmup
    for _ in 0..1000 { fp2_inv(&mut out, &x); }

    let start = Instant::now();
    for _ in 0..N { fp2_inv(&mut out, &x); }
    let elapsed = start.elapsed().as_nanos() as f64 / N as f64;
    println!("fp2_inv:          {:.1} ns  ({} iters)", elapsed, N);

    // ~70 iterations of doubling + ~10 additions in BN254 Miller
    let steps: f64 = 70.0 + 10.0;
    let inv_budget_per_miller = steps * elapsed / 1000.0; // us
    println!("fp2_inv / miller: {:.1} us  ({:.0} steps x fp2_inv)", inv_budget_per_miller, steps);

    // Compare to the full Miller loop
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
    let q_x = Fp2 { c0: Fp([0x8e83b5d102bc2026,0xdceb1935497b0172,0xfbb8264797811adf,0x19573841af96503b]),
                    c1: Fp([0xafb4737da84c6140,0x6043dd5a5802d8c4,0x09e950fc52a02f86,0x14fef0833aea7b6b]) };
    let q_y = Fp2 { c0: Fp([0x619dfa9d886be9f6,0xfe7fd297f59e9b78,0xff9e1a62231b7dfe,0x28fd7eebae9e4206]),
                    c1: Fp([0x64095b56c71856ee,0xdc57f922327d3cbb,0x55f935be33351076,0x0da4a0e693fd6482]) };
    let mut out12 = Fp12::zero();
    miller_loop(&mut out12, &p_x, &p_y, &q_x, &q_y);  // warmup

    let start = Instant::now();
    for _ in 0..N_MILLER { miller_loop(&mut out12, &p_x, &p_y, &q_x, &q_y); }
    let miller_us = start.elapsed().as_micros() as f64 / N_MILLER as f64;
    println!("miller_loop:      {:.1} us", miller_us);

    println!("\nfp2_inv share of miller: {:.1}% ({:.1} us of {:.1} us)",
             100.0 * inv_budget_per_miller / miller_us,
             inv_budget_per_miller, miller_us);
    println!("Projective ceiling (remove all fp2_invs): {:.1} us", miller_us - inv_budget_per_miller);
}
