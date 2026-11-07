//! The Jasmin path (feature `jasmin`): the pairing tower, the G1/G2 group
//! operations and the G1 MSM compiled by jasminc.
//!
//! The modules `generated/bls12_tower_regptr.jazz` and
//! `generated/bls12_group_regptr.jazz` are printed from the bedrock2 functions
//! by `src/Bedrock/ExtractBLS12TowerJasmin.v` / `ExtractBLS12GroupJasmin.v`
//! (translation `Core.tr_func_sized 6` + `AdcChain.polish_func_adc`, printer
//! `src/Bedrock/Jasmin/RegPtrSized.v` with liveness-chosen `#[spill]` hints,
//! slices of pointer parameters passed without staging and conditional
//! moves for the selects) and compiled by `jasminc -auto-spill` in
//! `build.sh`.  Leaves (default, `BLS12_JASMIN_LEAVES=jasmin`): the
//! Montgomery multiply and square, add, sub, copy and select are Jasmin,
//! printed from the fiat-crypto bedrock2 bodies inside the modules (local
//! functions); the inverse is the safegcd `_bls12_inv` of `src/stubs.rs`
//! (whose two multiplies are the live-hint Jasmin leaves of
//! `generated/bls12_leaves_live.jazz`), and `from_word` (constants only) and
//! `opp` are `_bls12_from_word` / `_bls12_opp` of `src/stubs.rs`, all three
//! reached through the dispatcher `__jasmin_syscall_randombytes__` of
//! `generated/jasmin_aliases.s`.  No CryptOpt code is linked.  With
//! `BLS12_JASMIN_LEAVES=cryptopt` the modules are the `*_ffi.jazz` variants,
//! whose multiply and square calls also go through the dispatcher, to
//! CryptOpt's `generated/bls12_{mul,square}_cryptopt.asm`.
//!
//! Hand-written: the `extern` declarations and the safe wrappers below
//! (memory layout only).  The layouts are the `#[repr(C)]` tower structs:
//! an `Fp` is 6 words, `Fp2` 12, `Fp6` 36, `Fp12` 72, a projective G1 point
//! x|y|z 18 words and a G2 point 36 words.

use crate::group::{G1Projective, G2Projective};
use crate::tower::{Fp, Fp2, Fp6, Fp12};

/// Largest MSM the Jasmin `msm_bls12` is compiled for: its point and scalar
/// arrays are `reg ptr u64[6 * MSM_NMAX]` / `u64[4 * MSM_NMAX]`.
pub const MSM_NMAX: usize = 4096;

#[allow(improper_ctypes)]
unsafe extern "C" {
    fn jasmin_bls12_pairing(out: *mut Fp12, px: *const Fp, py: *const Fp, qx: *const Fp2, qy: *const Fp2) -> *mut Fp12;
    fn jasmin_bls12_miller_loop(out: *mut Fp12, px: *const Fp, py: *const Fp, qx: *const Fp2, qy: *const Fp2) -> *mut Fp12;
    fn jasmin_bls12_final_exp(out: *mut Fp12, f: *const Fp12, g1: *const Fp2, g2: *const Fp2, w: *const Fp2) -> *mut Fp12;
    fn jasmin_bls12_Fp12_mul(out: *mut Fp12, x: *const Fp12, y: *const Fp12) -> *mut Fp12;
    fn jasmin_bls12_Fp12_square(out: *mut Fp12, x: *const Fp12) -> *mut Fp12;
    fn jasmin_bls12_Fp12_inv(out: *mut Fp12, x: *const Fp12) -> *mut Fp12;
    fn jasmin_bls12_Fp6_mul(out: *mut Fp6, x: *const Fp6, y: *const Fp6) -> *mut Fp6;
    fn jasmin_bls12_Fp2_mul(out: *mut Fp2, x: *const Fp2, y: *const Fp2) -> *mut Fp2;
    fn jasmin_bls12_Fp2_square(out: *mut Fp2, x: *const Fp2) -> *mut Fp2;
    fn jasmin_bls12_Fp2_inv(out: *mut Fp2, x: *const Fp2) -> *mut Fp2;
    fn jasmin_bls12_add(out: *mut Fp, x: *const Fp, y: *const Fp) -> *mut Fp;
    fn jasmin_bls12_sub(out: *mut Fp, x: *const Fp, y: *const Fp) -> *mut Fp;
}

macro_rules! wrap2 {
    ($name:ident, $sym:ident, $T:ty) => {
        pub fn $name(out: &mut $T, x: &$T, y: &$T) { unsafe { $sym(out, x, y); } }
    };
}
macro_rules! wrap1 {
    ($name:ident, $sym:ident, $T:ty) => {
        pub fn $name(out: &mut $T, x: &$T) { unsafe { $sym(out, x); } }
    };
}

wrap2!(fp12_mul, jasmin_bls12_Fp12_mul, Fp12);
wrap1!(fp12_square, jasmin_bls12_Fp12_square, Fp12);
wrap1!(fp12_inv, jasmin_bls12_Fp12_inv, Fp12);
wrap2!(fp6_mul, jasmin_bls12_Fp6_mul, Fp6);
wrap2!(fp2_mul, jasmin_bls12_Fp2_mul, Fp2);
wrap1!(fp2_square, jasmin_bls12_Fp2_square, Fp2);
wrap1!(fp2_inv, jasmin_bls12_Fp2_inv, Fp2);
wrap2!(fp_add, jasmin_bls12_add, Fp);
wrap2!(fp_sub, jasmin_bls12_sub, Fp);


/// The optimal-ate pairing, as [`crate::pairing`].
pub fn pairing(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    unsafe { jasmin_bls12_pairing(out, p_x, p_y, q_x, q_y); }
}

/// The Miller loop, as [`crate::miller_loop`].
pub fn miller_loop(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    unsafe { jasmin_bls12_miller_loop(out, p_x, p_y, q_x, q_y); }
}

/// The final exponentiation, as [`crate::final_exp`] (same constants).
pub fn final_exp(out: &mut Fp12, f: &Fp12) {
    let mut g1p2 = Fp2::zero();
    let mut g2p2 = Fp2::zero();
    let mut wfp2 = Fp2::zero();
    crate::tower::bls12_load_gamma1_p2(&mut g1p2);
    crate::tower::bls12_load_gamma2_p2(&mut g2p2);
    crate::tower::bls12_load_w_frob_p2_c1(&mut wfp2);
    unsafe { jasmin_bls12_final_exp(out, f, &g1p2, &g2p2, &wfp2); }
}

#[allow(improper_ctypes)]
unsafe extern "C" {
    fn jasmin_bls12_g1_add(out: *mut G1Projective, p: *const G1Projective, q: *const G1Projective) -> *mut G1Projective;
    fn jasmin_bls12_g1_double(out: *mut G1Projective, p: *const G1Projective) -> *mut G1Projective;
    fn jasmin_bls12_g1_scalar_mul(out: *mut G1Projective, k: *const [u64; 4], p: *const G1Projective) -> *mut G1Projective;
    fn jasmin_bls12_g1_msm(out: *mut G1Projective, scalars: *const u64, px: *const u64, py: *const u64,
                           pz: *const u64, n: u64) -> *mut G1Projective;
    fn jasmin_bls12_g2_add(out: *mut G2Projective, p: *const G2Projective, q: *const G2Projective) -> *mut G2Projective;
    fn jasmin_bls12_g2_double(out: *mut G2Projective, p: *const G2Projective) -> *mut G2Projective;
    fn jasmin_bls12_g2_scalar_mul(out: *mut G2Projective, k: *const [u64; 4], p: *const G2Projective) -> *mut G2Projective;
    fn jasmin_bls12_g1_scalar_mul_ct(out: *mut G1Projective, t: *mut G1Projective, k: *const [u64; 4],
                                     p: *const G1Projective) -> *mut G1Projective;
    fn jasmin_bls12_g2_scalar_mul_ct(out: *mut G2Projective, t: *mut G2Projective, k: *const [u64; 4],
                                     p: *const G2Projective) -> *mut G2Projective;
}

/// R = P + Q (emitted `curve_add`, RCB Algorithm 7), as [`crate::group::g1_add`].
pub fn g1_add(r: &mut G1Projective, p: &G1Projective, q: &G1Projective) {
    unsafe { jasmin_bls12_g1_add(r, p, q); }
}
/// R = 2P (emitted `curve_double_a0`), as [`crate::group::g1_double`].
pub fn g1_double(r: &mut G1Projective, p: &G1Projective) {
    unsafe { jasmin_bls12_g1_double(r, p); }
}
/// R = kP (emitted `g1_scalar_mul`), as [`crate::group::g1_scalar_mul`].
pub fn g1_scalar_mul(r: &mut G1Projective, k: &[u64; 4], p: &G1Projective) {
    unsafe { jasmin_bls12_g1_scalar_mul(r, k, p); }
}
/// R = kP, constant-time ladder (emitted `g1_scalar_mul_ct`; scratch point on the stack),
/// as [`crate::group::g1_scalar_mul_ct`].  Its Jasmin text passes `jasmin-ct` with the
/// scalar secret (scripts/check_ct_jasmin.sh); this wrapper copies nothing secret-dependent.
pub fn g1_scalar_mul_ct(r: &mut G1Projective, k: &[u64; 4], p: &G1Projective) {
    let mut t = G1Projective::identity();
    unsafe { jasmin_bls12_g1_scalar_mul_ct(r, &mut t, k, p); }
}
/// R = kP on G2, constant-time ladder (emitted `g2_scalar_mul_ct`), as
/// [`crate::group::g2_scalar_mul_ct`].
pub fn g2_scalar_mul_ct(r: &mut G2Projective, k: &[u64; 4], p: &G2Projective) {
    let mut t = G2Projective::identity();
    unsafe { jasmin_bls12_g2_scalar_mul_ct(r, &mut t, k, p); }
}
/// R = P + Q on G2 (emitted `g2_curve_add`), as [`crate::group::g2_add`].
pub fn g2_add(r: &mut G2Projective, p: &G2Projective, q: &G2Projective) {
    unsafe { jasmin_bls12_g2_add(r, p, q); }
}
/// R = 2P on G2 (emitted `g2_curve_double`), as [`crate::group::g2_double`].
pub fn g2_double(r: &mut G2Projective, p: &G2Projective) {
    unsafe { jasmin_bls12_g2_double(r, p); }
}
/// R = kP on G2 (emitted `g2_scalar_mul`), as [`crate::group::g2_scalar_mul`].
pub fn g2_scalar_mul(r: &mut G2Projective, k: &[u64; 4], p: &G2Projective) {
    unsafe { jasmin_bls12_g2_scalar_mul(r, k, p); }
}

/// Σ scalars[i] · points[i] (emitted Pippenger `msm_bls12`, window 9), as
/// [`crate::group::g1_msm`].  The point coordinates and scalars are copied
/// into arrays of the size the Jasmin function is compiled for.
///
/// Panics if the slices differ in length or hold more than [`MSM_NMAX`] points.
pub fn g1_msm(r: &mut G1Projective, points: &[G1Projective], scalars: &[[u64; 4]]) {
    assert_eq!(points.len(), scalars.len(), "g1_msm: {} points, {} scalars", points.len(), scalars.len());
    assert!(points.len() <= MSM_NMAX, "g1_msm: {} points > MSM_NMAX = {}", points.len(), MSM_NMAX);
    let mut sc = vec![0u64; 4 * MSM_NMAX];
    let mut px = vec![0u64; 6 * MSM_NMAX];
    let mut py = vec![0u64; 6 * MSM_NMAX];
    let mut pz = vec![0u64; 6 * MSM_NMAX];
    for (i, (p, k)) in points.iter().zip(scalars).enumerate() {
        sc[4 * i..4 * i + 4].copy_from_slice(k);
        px[6 * i..6 * i + 6].copy_from_slice(&p.x.0);
        py[6 * i..6 * i + 6].copy_from_slice(&p.y.0);
        pz[6 * i..6 * i + 6].copy_from_slice(&p.z.0);
    }
    unsafe {
        jasmin_bls12_g1_msm(r, sc.as_ptr(), px.as_ptr(), py.as_ptr(), pz.as_ptr(), points.len() as u64);
    }
}
