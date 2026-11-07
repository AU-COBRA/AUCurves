//! BN256 optimal-ate Miller loop and pairing (hand-written Rust over the emitted tower; not
//! emitted from bedrock2).
//!
//! The emitted tower::bn256_pairing_dsd is not bilinear, for two reasons:
//!   * tower::bn256_make_line puts the D-twist line in the wrong Fp12 slots:
//!     (lam Tx - Ty) + (-lam Px) v + Py v w, where the line through untwisted T at P is
//!     Py + (-lam Px) w + (lam Tx - Ty) v w (BN254's bn254_make_line_corrected layout);
//!   * tower::bn256_miller_loop stops after the 6u+2 loop, without the lines through
//!     Q1 = pi(Q) and -Q2 = -pi^2(Q).
//! This module mirrors BN254's bn254_miller_loop_optimal (same calls, same order) with BN256's
//! constants.  The Frobenius constants are the emitted loaders (gamma1 = xi^((p-1)/3),
//! gamma1_p2 = xi^((p^2-1)/3)) plus Q1_Y_CONST = xi^((p-1)/2), xi = 3 + u.
use crate::tower::*;

/// 6u+2 = 0x21EC817A18A131208 (66 bits), little-endian words.
const U6P2: [u64; 2] = [2218048799053648392, 2];
const U6P2_TOP: u64 = 65;

/// xi^((p-1)/2) in Montgomery form (R = 2^256).
fn load_q1_y_const(out: &mut Fp2) {
    out.c0.0 = [0x18dbee03fb7708fa, 0x1e7601a602c843c7, 0x5dde0688cdb231cb, 0x86db5cf2c605a524];
    out.c1.0 = [0x19da71333653ee20, 0x7eaaf34fc6ed6019, 0xc4ba3a29a60cdd1d, 0x75281311bcc9df79];
}

/// The D-twist line through T with slope lam, at P: Py + (-lam Px) w + (lam Tx - Ty) v w.
pub fn make_line_corrected(out: &mut Fp12, lam: &Fp2, x_t: &Fp2, y_t: &Fp2, x_p: &Fp, y_p: &Fp) {
    *out = Fp12::zero();
    let mut tmp = Fp2::zero();
    bn256_felem_copy(&mut out.c0.c0.c0, y_p);
    bn256_Fp2_mul_fp(&mut tmp, lam, x_p);
    bn256_Fp2_opp(&mut out.c1.c0, &tmp);
    bn256_Fp2_mul(&mut tmp, lam, x_t);
    bn256_Fp2_sub(&mut out.c1.c1, &tmp, y_t);
}

/// f <- f * line(T, (qx, qy))(P); T <- T + (qx, qy).
fn add_line(f: &mut Fp12, t_x: &mut Fp2, t_y: &mut Fp2, qx: &Fp2, qy: &Fp2, p_x: &Fp, p_y: &Fp) {
    let (mut tmp1, mut tmp2, mut lambda, mut line) = (Fp2::zero(), Fp2::zero(), Fp2::zero(), Fp12::zero());
    bn256_Fp2_sub(&mut tmp1, qy, t_y);
    bn256_Fp2_sub(&mut tmp2, qx, t_x);
    let c = tmp2;
    bn256_Fp2_inv(&mut tmp2, &c);
    bn256_Fp2_mul(&mut lambda, &tmp1, &tmp2);
    make_line_corrected(&mut line, &lambda, t_x, t_y, p_x, p_y);
    let c = *f;
    bn256_Fp12_mul_nocopy(f, &c, &line);
    bn256_Fp2_square(&mut tmp1, &lambda);
    let c = tmp1;
    bn256_Fp2_sub(&mut tmp1, &c, t_x);
    bn256_Fp2_sub(&mut tmp2, &tmp1, qx);
    bn256_Fp2_sub(&mut tmp1, t_x, &tmp2);
    let c = tmp1;
    bn256_Fp2_mul(&mut tmp1, &lambda, &c);
    let c = *t_y;
    bn256_Fp2_sub(t_y, &tmp1, &c);
    *t_x = tmp2;
}

pub fn miller_loop_optimal(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut f = Fp12::zero();
    bn256_from_word(&mut f.c0.c0.c0, 1);
    let (mut t_x, mut t_y) = (*q_x, *q_y);
    let (mut tmp1, mut tmp2, mut lambda, mut line) = (Fp2::zero(), Fp2::zero(), Fp2::zero(), Fp12::zero());
    let mut i = U6P2_TOP;
    while i != 0 {
        i -= 1;
        // doubling: lam = 3 Tx^2 / (2 Ty)
        bn256_Fp2_square(&mut tmp1, &t_x);
        bn256_Fp2_add(&mut lambda, &tmp1, &tmp1);
        let c = lambda;
        bn256_Fp2_add(&mut lambda, &c, &tmp1);
        bn256_Fp2_add(&mut tmp1, &t_y, &t_y);
        let c = tmp1;
        bn256_Fp2_inv(&mut tmp1, &c);
        let c = lambda;
        bn256_Fp2_mul(&mut lambda, &c, &tmp1);
        make_line_corrected(&mut line, &lambda, &t_x, &t_y, p_x, p_y);
        let c = f;
        bn256_Fp12_square(&mut f, &c);
        let c = f;
        bn256_Fp12_mul_nocopy(&mut f, &c, &line);
        bn256_Fp2_square(&mut tmp1, &lambda);
        let c = tmp1;
        bn256_Fp2_sub(&mut tmp1, &c, &t_x);
        bn256_Fp2_sub(&mut tmp2, &tmp1, &t_x);
        bn256_Fp2_sub(&mut tmp1, &t_x, &tmp2);
        let c = tmp1;
        bn256_Fp2_mul(&mut tmp1, &lambda, &c);
        let c = t_y;
        bn256_Fp2_sub(&mut t_y, &tmp1, &c);
        t_x = tmp2;
        if (U6P2[(i >> 6) as usize] >> (i & 63)) & 1 != 0 {
            add_line(&mut f, &mut t_x, &mut t_y, q_x, q_y, p_x, p_y);
        }
    }
    // Q1 = pi(Q) = (conj(Qx) gamma1, conj(Qy) xi^((p-1)/2))
    let (mut g1, mut gy, mut g1p2) = (Fp2::zero(), Fp2::zero(), Fp2::zero());
    bn256_load_gamma1(&mut g1);
    load_q1_y_const(&mut gy);
    bn256_load_gamma1_p2(&mut g1p2);
    let (mut q1_x, mut q1_y) = (Fp2::zero(), Fp2::zero());
    bn256_Fp2_conjugate(&mut tmp1, q_x);
    bn256_Fp2_mul(&mut q1_x, &tmp1, &g1);
    bn256_Fp2_conjugate(&mut tmp1, q_y);
    bn256_Fp2_mul(&mut q1_y, &tmp1, &gy);
    add_line(&mut f, &mut t_x, &mut t_y, &q1_x, &q1_y, p_x, p_y);
    // -Q2 = -pi^2(Q) = (Qx gamma1_p2, Qy): xi^((p^2-1)/2) = -1, so no sign change on Qy.
    bn256_Fp2_mul_fp(&mut q1_x, q_x, &g1p2.c0);
    add_line(&mut f, &mut t_x, &mut t_y, &q1_x, q_y, p_x, p_y);
    *out = f;
}

pub fn pairing_optimal(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut ml = Fp12::zero();
    let (mut g1p2, mut g2p2, mut w) = (Fp2::zero(), Fp2::zero(), Fp2::zero());
    bn256_load_gamma1_p2(&mut g1p2);
    bn256_load_gamma2_p2(&mut g2p2);
    bn256_load_w_frob_p2_c1(&mut w);
    miller_loop_optimal(&mut ml, p_x, p_y, q_x, q_y);
    bn256_final_exp_dsd(out, &ml, &g1p2, &g2p2, &w);
}

#[cfg(test)]
mod tests {
    //! e(2 G1, 3 G2) = e(G1, G2)^6, e(G1, G2) != 1, and e(G1, G2) equals the optimal-ate reference
    //! value (a Python reference implementation: lines through Q1 = pi(Q) and -pi^2(Q), exponent (p^12-1)/r) on
    //! canonical coefficients.  G1 = (1, 2); G2 is a point of order r on y^2 = x^3 + 3/xi.
    use super::*;
    const G1X: Fp = Fp([0xe7a35393a1f76999, 0x11a4772edf4a4a61, 0x559013479e7b23de, 0x704afe1cb55c7806]);
    const G1Y: Fp = Fp([0xb6e9fabae5e63ccb, 0x34ed658c9ddedf25, 0x00b039d6db716b9a, 0x50e0fa5620156813]);
    const P2X: Fp = Fp([0x491605451a19c335, 0xcb129a73622120da, 0xff4fc629248e9465, 0x3f1f05a9dfea97ec]);
    const P2Y: Fp = Fp([0x185cac6c5e089667, 0xee5b88d120b5b59e, 0xaa6fecb86184dc21, 0x63b501e34aa387f9]);
    fn g2() -> (Fp2, Fp2) { (Fp2 { c0: Fp([0x7a80be24a6e90a16, 0xfde4755fc2e41f6c, 0x5b6f4a9198763256, 0x72c3004898fba81f]), c1: Fp([0x6f5341c2ca3bc5e0, 0xf6944260e391b942, 0xfcc1f7aea6e35601, 0x4fdc3e4616454d92]) }, Fp2 { c0: Fp([0x382e1937f0c8b7d0, 0x1a29e6e04e875d3d, 0x3fea97d03f272294, 0x2d513bcb93d44a17]), c1: Fp([0x77ebd80dcc8c5a70, 0x068542a09f5e401b, 0x61466977c0734e5d, 0x73517063eb3e9dd9]) }) }
    fn q3() -> (Fp2, Fp2) { (Fp2 { c0: Fp([0xdf5df677f8d3c166, 0xfc3a65c8ef23362c, 0x30653d781e0c7981, 0x3de45ae9cad9d572]), c1: Fp([0xb4365dc62aeb3273, 0xf7b4da203ed487c7, 0xd350a3035213a806, 0x70b1ff5493205d94]) }, Fp2 { c0: Fp([0x279e920af9a51cf7, 0x96569648e5445610, 0x024e1237b107463e, 0x819e31e48803cd75]), c1: Fp([0x278de8c3fc99e7f9, 0x2e76c42a101a5544, 0xf475e3f09f1f15b7, 0x1411fda6cf50b0aa]) }) }
    /// Canonical coefficients of e(G1, G2), tower order c0.c0.c0, c0.c0.c1, c0.c1.c0, ...
    const E_REF: [[u64; 4]; 12] = [
        [0xe4c3412c9c774f46, 0xc1b3a208dce396b3, 0x9863ee68aad6f04d, 0x8be79a291123992b],
        [0x15d19cbfbb8e65c6, 0xf080088bbb49a787, 0xd0640149da2bb8a5, 0x68f8daa221fcc287],
        [0x3515e673fbf7f27a, 0xaeb91fafcb6e7412, 0x302659b80da2f676, 0x6374d0d60442fcaf],
        [0xca9c0936cad8f513, 0x954d56133493f477, 0x69196785192a4a43, 0x5290fdcb32ffa797],
        [0x51c49f11a9c4244d, 0x31343517ce3d62a2, 0x85c8c29aafbd8444, 0x65d0e3b3b247717b],
        [0x3a44183a5c8d950f, 0x0e23b93fc4755355, 0xe4fb3cce828e7ad6, 0x0851a4d847296bf6],
        [0x8b56299185ef7f1e, 0x7573b6c4f9e115a7, 0x7c9c39f3d0c78151, 0x89abca0c39a609e2],
        [0xb3a6b0c85f2eecc7, 0x00f77a824a6092a9, 0xe762a56d368f6a2a, 0x57922a84bb41235e],
        [0xda599938ac70f752, 0x112e1960a0f05d16, 0xa133a5affc4fa480, 0x538ef47dbf1ba2dd],
        [0x3847ad8aa36afbc1, 0x19ed00cba055e012, 0xa0265e0428907f39, 0x42111516aa5d6659],
        [0xf365270517c063a3, 0x73e13f5bc9f28fc2, 0x477290ed3e86b2fa, 0x6af3f63bcbea9d77],
        [0x5e720ee0728828a6, 0x262d6a12c134b0c9, 0xae424809edd62eda, 0x8cb4f65e915d66f7],
    ];
    fn canon(x: &Fp) -> [u64; 4] {
        let mut c = Fp::zero();
        bn256_mul(&mut c, x, &Fp([1, 0, 0, 0]));
        c.0
    }
    fn canon12(f: &Fp12) -> [[u64; 4]; 12] {
        let z = [&f.c0.c0, &f.c0.c1, &f.c0.c2, &f.c1.c0, &f.c1.c1, &f.c1.c2];
        let mut o = [[0u64; 4]; 12];
        for (i, a) in z.iter().enumerate() {
            o[2 * i] = canon(&a.c0);
            o[2 * i + 1] = canon(&a.c1);
        }
        o
    }
    fn pair(f: fn(&mut Fp12, &Fp, &Fp, &Fp2, &Fp2), px: &Fp, py: &Fp, q: &(Fp2, Fp2)) -> Fp12 {
        let mut o = Fp12::zero();
        f(&mut o, px, py, &q.0, &q.1);
        o
    }
    #[test]
    fn optimal_pairing_bilinear_and_reference() {
        let e = pair(pairing_optimal, &G1X, &G1Y, &g2());
        let e6 = pair(pairing_optimal, &P2X, &P2Y, &q3());
        let mut e2 = Fp12::zero();
        bn256_Fp12_square(&mut e2, &e);
        let mut e3 = Fp12::zero();
        bn256_Fp12_mul_nocopy(&mut e3, &e2, &e);
        let mut e6_ = Fp12::zero();
        bn256_Fp12_square(&mut e6_, &e3);
        assert_eq!(canon12(&e6), canon12(&e6_), "e(2P,3Q) = e(P,Q)^6");
        let mut one = Fp12::zero();
        bn256_from_word(&mut one.c0.c0.c0, 1);
        assert_ne!(canon12(&e), canon12(&one), "e(G1,G2) != 1");
        assert_eq!(canon12(&e), E_REF, "e(G1,G2) = reference");
    }
    #[test]
    fn emitted_pairing_dsd_is_not_bilinear() {
        // The emitted tower::bn256_pairing_dsd (wrong line slots, no correction lines).
        let e = pair(bn256_pairing_dsd, &G1X, &G1Y, &g2());
        let e6 = pair(bn256_pairing_dsd, &P2X, &P2Y, &q3());
        let mut e2 = Fp12::zero();
        bn256_Fp12_square(&mut e2, &e);
        let mut e3 = Fp12::zero();
        bn256_Fp12_mul_nocopy(&mut e3, &e2, &e);
        let mut e6_ = Fp12::zero();
        bn256_Fp12_square(&mut e6_, &e3);
        assert_ne!(canon12(&e6), canon12(&e6_));
    }
}
