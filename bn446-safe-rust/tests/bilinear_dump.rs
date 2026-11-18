//! BN446 (scripts/bn446/bn446_test.py): evaluate the crate's
//! `pairing` (tower::bn446_pairing_dsd_optimal), `miller_loop` (tower::bn446_miller_loop_optimal)
//! and, as a control, `pairing_dsd_uncorrected` (tower::bn446_pairing_dsd) on points supplied by
//! bn446_test.py, which checks bilinearity, non-degeneracy, e^r = 1 and the reference.
//! Input (BN446_IN): lines "label px py qx.c0 qx.c1 qy.c0 qy.c1", Montgomery form, big-endian hex.
//! Output (BN446_OUT): "label e c_0..c_11 ml c_0..c_11 u c_0..c_11", canonical big-endian hex in the
//! tower order c0.c0.c0, c0.c0.c1, c0.c1.c0, ...; "u" only for labels ending in ":e" or ":ab".
//! Without BN446_IN: no-op.  Copied by bn446_test.py to bn446-safe-rust/tests/bilinear_dump.rs.
use bn446::*;

fn parse(h: &str) -> Fp {
    let h = format!("{:0>112}", h);
    let mut f = Fp::zero();
    for i in 0..7 {
        let s = &h[h.len() - 16 * (i + 1)..h.len() - 16 * i];
        f.0[i] = u64::from_str_radix(s, 16).unwrap();
    }
    f
}

fn canon_hex(x: &Fp) -> String {
    let mut one = Fp::zero();
    one.0[0] = 1;
    let mut c = Fp::zero();
    fp_mul(&mut c, x, &one);
    c.0.iter().rev().map(|l| format!("{:016x}", l)).collect()
}

fn c12(f: &Fp12) -> String {
    let z = [&f.c0.c0, &f.c0.c1, &f.c0.c2, &f.c1.c0, &f.c1.c1, &f.c1.c2];
    z.iter().map(|a| format!("{} {}", canon_hex(&a.c0), canon_hex(&a.c1))).collect::<Vec<_>>().join(" ")
}

#[test]
fn bilinear_dump() {
    let Ok(inp) = std::env::var("BN446_IN") else { return };
    let outp = std::env::var("BN446_OUT").unwrap();
    let mut out = String::new();
    for line in std::fs::read_to_string(inp).unwrap().lines() {
        let w: Vec<&str> = line.split_whitespace().collect();
        if w.len() != 7 { continue; }
        let (px, py) = (parse(w[1]), parse(w[2]));
        let qx = Fp2 { c0: parse(w[3]), c1: parse(w[4]) };
        let qy = Fp2 { c0: parse(w[5]), c1: parse(w[6]) };
        let mut e = Fp12::zero();
        pairing(&mut e, &px, &py, &qx, &qy);
        let mut ml = Fp12::zero();
        miller_loop(&mut ml, &px, &py, &qx, &qy);
        out += &format!("{} e {} ml {}", w[0], c12(&e), c12(&ml));
        if w[0].ends_with(":e") || w[0].ends_with(":ab") {
            let mut u = Fp12::zero();
            pairing_dsd_uncorrected(&mut u, &px, &py, &qx, &qy);
            out += &format!(" u {}", c12(&u));
        }
        out += "\n";
    }
    std::fs::write(outp, out).unwrap();
}
