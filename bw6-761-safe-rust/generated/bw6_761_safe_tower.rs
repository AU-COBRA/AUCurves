#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp(pub [u64; 12]);
impl Fp { #[inline] pub const fn zero() -> Self { Fp([0u64; 12]) } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp3 { pub c0: Fp, pub c1: Fp, pub c2: Fp }
impl Fp3 { #[inline] pub const fn zero() -> Self { Fp3 { c0: Fp::zero(), c1: Fp::zero(), c2: Fp::zero() } } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp6 { pub c0: Fp3, pub c1: Fp3 }
impl Fp6 { #[inline] pub const fn zero() -> Self { Fp6 { c0: Fp3::zero(), c1: Fp3::zero() } } }


unsafe extern "C" {
    fn _bw6_761_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bw6_761_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bw6_761_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bw6_761_square(o: *mut u64, x: *const u64);
    fn _bw6_761_opp(o: *mut u64, x: *const u64);
    fn _bw6_761_felem_copy(o: *mut u64, x: *const u64);
    fn _bw6_761_from_word(o: *mut u64, w: u64);
    fn _bw6_761_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bw6_761_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bw6_761_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bw6_761_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bw6_761_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bw6_761_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bw6_761_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bw6_761_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bw6_761_square(o: &mut Fp, x: &Fp) { unsafe { _bw6_761_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bw6_761_opp(o: &mut Fp, x: &Fp) { unsafe { _bw6_761_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bw6_761_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bw6_761_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bw6_761_from_word(o: &mut Fp, w: u64) { unsafe { _bw6_761_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bw6_761_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bw6_761_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bw6_761_inv(o: &mut Fp, x: &Fp) { unsafe { _bw6_761_inv(o.0.as_mut_ptr(), x.0.as_ptr()) } }
/// Zero out an Fp.  Used by Fp3/Fp6 `_zero` constructors emitted by
/// the verified tower.  No leaf-level `_zero` symbol is generated
/// (fiat-rust doesn't expose one), so we provide it in safe Rust.
#[inline] pub fn bw6_761_zero(o: &mut Fp) { *o = Fp::zero(); }
/// Canonical Montgomery `1` for BW6-761.  Reuses `from_word(1)`
/// (which goes through fiat-rust's `to_montgomery` under the hood).
#[inline] pub fn bw6_761_one(o: &mut Fp) { bw6_761_from_word(o, 1u64); }

/// Constant-time select on Fp3 (3-limb tower over Fp).
/// [GenericCubic.CE_funcs] doesn't emit a `_select_znz` entry, but
/// the `QE_funcs`-generated `bw6_761_Fp6_select_znz` body recurses
/// into it.  Componentwise call to the Fp leaf select.
#[inline] pub fn bw6_761_Fp3_select_znz(out: &mut Fp3, c: u64, x: &Fp3, y: &Fp3) {
    bw6_761_select_znz(&mut out.c0, c, &x.c0, &y.c0);
    bw6_761_select_znz(&mut out.c1, c, &x.c1, &y.c1);
    bw6_761_select_znz(&mut out.c2, c, &x.c2, &y.c2);
}

/// Inverse in Fp6 = Fp3[w]/(w^2 - zeta).  No closed bedrock2 body
/// exists for Fp6_inv (the [GenericQuadratic.QE_funcs] list does not
/// include inv — same constraint as BLS24's Fp2/Fp4/Fp8 layers).
/// We use the standard norm trick over Fp3:
///   inv(a + b·w) = (a − b·w) / (a² − zeta·b²)
/// where zeta is the Fp6 non-residue, encoded by
/// [bw6_761_Fp3_mul_by_zeta] (the verified emitter for "multiply by
/// zeta in Fp3").  Called by the verified [bw6_final_exp_easy] body.
pub fn bw6_761_Fp6_inv(out: &mut Fp6, x: &Fp6) {
    let mut a_sq = Fp3::zero();
    let mut b_sq = Fp3::zero();
    let mut zeta_b_sq = Fp3::zero();
    let mut norm = Fp3::zero();
    let mut norm_inv = Fp3::zero();
    bw6_761_Fp3_square(&mut a_sq, &x.c0);
    bw6_761_Fp3_square(&mut b_sq, &x.c1);
    bw6_761_Fp3_mul_by_zeta(&mut zeta_b_sq, &b_sq);
    bw6_761_Fp3_sub(&mut norm, &a_sq, &zeta_b_sq);
    bw6_761_Fp3_inv(&mut norm_inv, &norm);
    bw6_761_Fp3_mul(&mut out.c0, &x.c0, &norm_inv);
    let mut neg_c1 = Fp3::zero();
    bw6_761_Fp3_opp(&mut neg_c1, &x.c1);
    bw6_761_Fp3_mul(&mut out.c1, &neg_c1, &norm_inv);
}

#[inline]
pub fn bw6_761_mul_by_nr_n4(mut out: &mut Fp, x: &Fp) {
    bw6_761_add(&mut out, &x, &x);
    let __ac0 = out.clone();
    bw6_761_add(&mut out, &__ac0, &__ac0);
    let __ac1 = out.clone();
    bw6_761_opp(&mut out, &__ac1);
}

#[inline]
pub fn bw6_761_Fp3_felem_copy(mut out: &mut Fp3, x: &Fp3) {
    bw6_761_felem_copy(&mut out.c0, &x.c0);
    bw6_761_felem_copy(&mut out.c1, &x.c1);
    bw6_761_felem_copy(&mut out.c2, &x.c2);
}

#[inline]
pub fn bw6_761_Fp3_zero(mut out: &mut Fp3) {
    bw6_761_zero(&mut out.c0, );
    bw6_761_zero(&mut out.c1, );
    bw6_761_zero(&mut out.c2, );
}

#[inline]
pub fn bw6_761_Fp3_one(mut out: &mut Fp3) {
    bw6_761_one(&mut out.c0, );
    bw6_761_zero(&mut out.c1, );
    bw6_761_zero(&mut out.c2, );
}

#[inline]
pub fn bw6_761_Fp3_opp(mut out: &mut Fp3, x: &Fp3) {
    bw6_761_opp(&mut out.c0, &x.c0);
    bw6_761_opp(&mut out.c1, &x.c1);
    bw6_761_opp(&mut out.c2, &x.c2);
}

#[inline]
pub fn bw6_761_Fp3_add(mut out: &mut Fp3, inx: &Fp3, iny: &Fp3) {
    let mut allocx: Fp3 = Fp3::zero();
    let mut allocy: Fp3 = Fp3::zero();
    bw6_761_Fp3_felem_copy(&mut allocx, &inx);
    bw6_761_Fp3_felem_copy(&mut allocy, &iny);
    bw6_761_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bw6_761_add(&mut out.c1, &allocx.c1, &allocy.c1);
    bw6_761_add(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bw6_761_Fp3_sub(mut out: &mut Fp3, inx: &Fp3, iny: &Fp3) {
    let mut allocx: Fp3 = Fp3::zero();
    let mut allocy: Fp3 = Fp3::zero();
    bw6_761_Fp3_felem_copy(&mut allocx, &inx);
    bw6_761_Fp3_felem_copy(&mut allocy, &iny);
    bw6_761_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bw6_761_sub(&mut out.c1, &allocx.c1, &allocy.c1);
    bw6_761_sub(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bw6_761_Fp3_mul(mut out: &mut Fp3, inx: &Fp3, iny: &Fp3) {
    let mut a0b0: Fp = Fp::zero();
    let mut a1b1: Fp = Fp::zero();
    let mut a2b2: Fp = Fp::zero();
    let mut t0: Fp = Fp::zero();
    let mut t1: Fp = Fp::zero();
    let mut t2: Fp = Fp::zero();
    bw6_761_mul(&mut a0b0, &inx.c0, &iny.c0);
    bw6_761_mul(&mut a1b1, &inx.c1, &iny.c1);
    bw6_761_mul(&mut a2b2, &inx.c2, &iny.c2);
    bw6_761_add(&mut t0, &inx.c1, &inx.c2);
    bw6_761_add(&mut t1, &iny.c1, &iny.c2);
    let __ac0 = t0.clone();
    bw6_761_mul(&mut t0, &__ac0, &t1);
    let __ac1 = t0.clone();
    bw6_761_sub(&mut t0, &__ac1, &a1b1);
    let __ac2 = t0.clone();
    bw6_761_sub(&mut t0, &__ac2, &a2b2);
    let __ac3 = t0.clone();
    bw6_761_mul_by_nr_n4(&mut t0, &__ac3);
    bw6_761_add(&mut out.c0, &a0b0, &t0);
    bw6_761_add(&mut t0, &inx.c0, &inx.c1);
    bw6_761_add(&mut t1, &iny.c0, &iny.c1);
    let __ac4 = t0.clone();
    bw6_761_mul(&mut t0, &__ac4, &t1);
    let __ac5 = t0.clone();
    bw6_761_sub(&mut t0, &__ac5, &a0b0);
    let __ac6 = t0.clone();
    bw6_761_sub(&mut t0, &__ac6, &a1b1);
    bw6_761_mul_by_nr_n4(&mut t1, &a2b2);
    bw6_761_add(&mut out.c1, &t0, &t1);
    bw6_761_add(&mut t0, &inx.c0, &inx.c2);
    bw6_761_add(&mut t1, &iny.c0, &iny.c2);
    let __ac7 = t0.clone();
    bw6_761_mul(&mut t0, &__ac7, &t1);
    let __ac8 = t0.clone();
    bw6_761_sub(&mut t0, &__ac8, &a0b0);
    let __ac9 = t0.clone();
    bw6_761_sub(&mut t0, &__ac9, &a2b2);
    bw6_761_add(&mut out.c2, &t0, &a1b1);
}

#[inline]
pub fn bw6_761_Fp3_square(mut out: &mut Fp3, x: &Fp3) {
    let mut s0: Fp = Fp::zero();
    let mut s1: Fp = Fp::zero();
    let mut s2: Fp = Fp::zero();
    let mut s3: Fp = Fp::zero();
    let mut s4: Fp = Fp::zero();
    bw6_761_square(&mut s0, &x.c0);
    bw6_761_mul(&mut s1, &x.c0, &x.c1);
    let __ac0 = s1.clone();
    bw6_761_add(&mut s1, &__ac0, &__ac0);
    bw6_761_sub(&mut s2, &x.c0, &x.c1);
    let __ac1 = s2.clone();
    bw6_761_add(&mut s2, &__ac1, &x.c2);
    let __ac2 = s2.clone();
    bw6_761_square(&mut s2, &__ac2);
    bw6_761_mul(&mut s3, &x.c1, &x.c2);
    let __ac3 = s3.clone();
    bw6_761_add(&mut s3, &__ac3, &__ac3);
    bw6_761_square(&mut s4, &x.c2);
    bw6_761_mul_by_nr_n4(&mut out.c0, &s3);
    let __ac4 = out.c0.clone();
    bw6_761_add(&mut out.c0, &s0, &__ac4);
    bw6_761_mul_by_nr_n4(&mut out.c1, &s4);
    let __ac5 = out.c1.clone();
    bw6_761_add(&mut out.c1, &s1, &__ac5);
    bw6_761_add(&mut out.c2, &s1, &s2);
    let __ac6 = out.c2.clone();
    bw6_761_add(&mut out.c2, &__ac6, &s3);
    let __ac7 = out.c2.clone();
    bw6_761_sub(&mut out.c2, &__ac7, &s0);
    let __ac8 = out.c2.clone();
    bw6_761_sub(&mut out.c2, &__ac8, &s4);
}

#[inline]
pub fn bw6_761_Fp3_inv(mut out: &mut Fp3, x: &Fp3) {
    let mut vA: Fp = Fp::zero();
    let mut vB: Fp = Fp::zero();
    let mut vC: Fp = Fp::zero();
    let mut t0: Fp = Fp::zero();
    let mut t1: Fp = Fp::zero();
    let mut vFF: Fp = Fp::zero();
    let mut vFFi: Fp = Fp::zero();
    bw6_761_square(&mut t0, &x.c0);
    bw6_761_mul(&mut t1, &x.c1, &x.c2);
    let __ac0 = t1.clone();
    bw6_761_mul_by_nr_n4(&mut t1, &__ac0);
    bw6_761_sub(&mut vA, &t0, &t1);
    bw6_761_square(&mut t0, &x.c2);
    let __ac1 = t0.clone();
    bw6_761_mul_by_nr_n4(&mut t0, &__ac1);
    bw6_761_mul(&mut t1, &x.c0, &x.c1);
    bw6_761_sub(&mut vB, &t0, &t1);
    bw6_761_square(&mut t0, &x.c1);
    bw6_761_mul(&mut t1, &x.c0, &x.c2);
    bw6_761_sub(&mut vC, &t0, &t1);
    bw6_761_mul(&mut vFF, &x.c0, &vA);
    bw6_761_mul(&mut t0, &x.c2, &vB);
    bw6_761_mul(&mut t1, &x.c1, &vC);
    let __ac2 = t0.clone();
    bw6_761_add(&mut t0, &__ac2, &t1);
    let __ac3 = t0.clone();
    bw6_761_mul_by_nr_n4(&mut t0, &__ac3);
    let __ac4 = vFF.clone();
    bw6_761_add(&mut vFF, &__ac4, &t0);
    bw6_761_inv(&mut vFFi, &vFF);
    bw6_761_mul(&mut out.c0, &vA, &vFFi);
    bw6_761_mul(&mut out.c1, &vB, &vFFi);
    bw6_761_mul(&mut out.c2, &vC, &vFFi);
}

#[inline]
pub fn bw6_761_Fp6_felem_copy(mut out: &mut Fp6, x: &Fp6) {
    bw6_761_Fp3_felem_copy(&mut out.c0, &x.c0);
    bw6_761_Fp3_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bw6_761_Fp6_zero(mut out: &mut Fp6) {
    bw6_761_Fp3_zero(&mut out.c0, );
    bw6_761_Fp3_zero(&mut out.c1, );
}

#[inline]
pub fn bw6_761_Fp6_one(mut out: &mut Fp6) {
    bw6_761_Fp3_one(&mut out.c0, );
    bw6_761_Fp3_zero(&mut out.c1, );
}

#[inline]
pub fn bw6_761_Fp6_opp(mut out: &mut Fp6, x: &Fp6) {
    bw6_761_Fp3_opp(&mut out.c0, &x.c0);
    bw6_761_Fp3_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bw6_761_Fp6_add(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bw6_761_Fp6_felem_copy(&mut allocx, &inx);
    bw6_761_Fp6_felem_copy(&mut allocy, &iny);
    bw6_761_Fp3_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bw6_761_Fp3_add(&mut out.c1, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bw6_761_Fp6_sub(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bw6_761_Fp6_felem_copy(&mut allocx, &inx);
    bw6_761_Fp6_felem_copy(&mut allocy, &iny);
    bw6_761_Fp3_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bw6_761_Fp3_sub(&mut out.c1, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bw6_761_Fp6_mul(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut v0: Fp3 = Fp3::zero();
    let mut v1: Fp3 = Fp3::zero();
    let mut v2: Fp3 = Fp3::zero();
    bw6_761_Fp3_mul(&mut v0, &inx.c0, &iny.c0);
    bw6_761_Fp3_mul(&mut v1, &inx.c1, &iny.c1);
    bw6_761_Fp3_add(&mut v2, &inx.c0, &inx.c1);
    bw6_761_Fp3_add(&mut out.c1, &iny.c0, &iny.c1);
    let __ac0 = out.c1.clone();
    bw6_761_Fp3_mul(&mut out.c1, &__ac0, &v2);
    let __ac1 = out.c1.clone();
    bw6_761_Fp3_sub(&mut out.c1, &__ac1, &v0);
    let __ac2 = out.c1.clone();
    bw6_761_Fp3_sub(&mut out.c1, &__ac2, &v1);
    bw6_761_Fp3_mul_by_zeta(&mut v2, &v1);
    bw6_761_Fp3_add(&mut out.c0, &v0, &v2);
}

#[inline]
pub fn bw6_761_Fp6_square(mut out: &mut Fp6, x: &Fp6) {
    let mut v0: Fp3 = Fp3::zero();
    let mut v1: Fp3 = Fp3::zero();
    let mut v2: Fp3 = Fp3::zero();
    bw6_761_Fp3_square(&mut v0, &x.c0);
    bw6_761_Fp3_square(&mut v1, &x.c1);
    bw6_761_Fp3_mul(&mut v2, &x.c0, &x.c1);
    bw6_761_Fp3_add(&mut out.c1, &v2, &v2);
    let __ac0 = v1.clone();
    bw6_761_Fp3_mul_by_zeta(&mut v1, &__ac0);
    bw6_761_Fp3_add(&mut out.c0, &v0, &v1);
}

#[inline]
pub fn bw6_761_Fp6_select_znz(mut out: &mut Fp6, c: u64, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bw6_761_Fp6_felem_copy(&mut allocx, &inx);
    bw6_761_Fp6_felem_copy(&mut allocy, &iny);
    bw6_761_Fp3_select_znz(&mut out.c0, c, &allocx.c0, &allocy.c0);
    bw6_761_Fp3_select_znz(&mut out.c1, c, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bw6_761_Fp3_mul_by_zeta(mut out: &mut Fp3, x: &Fp3) {
    let mut ztmp: Fp = Fp::zero();
    let mut btmp: Fp = Fp::zero();
    bw6_761_mul_by_nr_n4(&mut ztmp, &x.c2);
    bw6_761_felem_copy(&mut btmp, &x.c1);
    bw6_761_felem_copy(&mut out.c1, &x.c0);
    bw6_761_felem_copy(&mut out.c0, &ztmp);
    bw6_761_felem_copy(&mut out.c2, &btmp);
}

#[inline]
pub fn bw6_761_Fp3_mul_fp(mut out: &mut Fp3, x: &Fp3, s: &Fp) {
    bw6_761_mul(&mut out.c0, &x.c0, &s);
    bw6_761_mul(&mut out.c1, &x.c1, &s);
    bw6_761_mul(&mut out.c2, &x.c2, &s);
}

#[inline]
pub fn bw6_761_make_line(mut out: &mut Fp6, lam: &Fp3, x_t: &Fp3, y_t: &Fp3, x_p: &Fp, y_p: &Fp) {
    let mut tmp: Fp3 = Fp3::zero();
    bw6_761_Fp3_mul(&mut tmp, &lam, &x_t);
    bw6_761_Fp3_sub(&mut out.c0, &tmp, &y_t);
    bw6_761_Fp3_mul_fp(&mut tmp, &lam, &x_p);
    bw6_761_opp(&mut out.c1.c0, &tmp.c0);
    bw6_761_felem_copy(&mut out.c1.c1, &y_p);
    bw6_761_from_word(&mut out.c1.c2, 0u64);
}

#[inline]
pub fn bw6_761_miller_loop(mut out: &mut Fp6, p_x: &Fp, p_y: &Fp, q_x: &Fp3, q_y: &Fp3) {
    let mut f: Fp6 = Fp6::zero();
    let mut t_x: Fp3 = Fp3::zero();
    let mut t_y: Fp3 = Fp3::zero();
    let mut lambda: Fp3 = Fp3::zero();
    let mut tmp1: Fp3 = Fp3::zero();
    let mut tmp2: Fp3 = Fp3::zero();
    let mut line: Fp6 = Fp6::zero();
    bw6_761_from_word(&mut f.c0.c0, 1u64);
    bw6_761_from_word(&mut f.c0.c1, 0u64);
    bw6_761_from_word(&mut f.c0.c2, 0u64);
    bw6_761_from_word(&mut f.c1.c0, 0u64);
    bw6_761_from_word(&mut f.c1.c1, 0u64);
    bw6_761_from_word(&mut f.c1.c2, 0u64);
    bw6_761_Fp3_felem_copy(&mut t_x, &q_x);
    bw6_761_Fp3_felem_copy(&mut t_y, &q_y);
    let mut i: u64;
    i = 64u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        bw6_761_Fp3_square(&mut tmp1, &t_x);
        bw6_761_Fp3_add(&mut lambda, &tmp1, &tmp1);
        let __ac0 = lambda.clone();
        bw6_761_Fp3_add(&mut lambda, &__ac0, &tmp1);
        bw6_761_Fp3_add(&mut tmp1, &t_y, &t_y);
        let __ac1 = tmp1.clone();
        bw6_761_Fp3_inv(&mut tmp1, &__ac1);
        let __ac2 = lambda.clone();
        bw6_761_Fp3_mul(&mut lambda, &__ac2, &tmp1);
        bw6_761_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
        let __ac3 = f.clone();
        bw6_761_Fp6_square(&mut f, &__ac3);
        let __ac4 = f.clone();
        bw6_761_Fp6_mul(&mut f, &__ac4, &line);
        bw6_761_Fp3_square(&mut tmp1, &lambda);
        let __ac5 = tmp1.clone();
        bw6_761_Fp3_sub(&mut tmp1, &__ac5, &t_x);
        bw6_761_Fp3_sub(&mut tmp2, &tmp1, &t_x);
        bw6_761_Fp3_sub(&mut tmp1, &t_x, &tmp2);
        let __ac6 = tmp1.clone();
        bw6_761_Fp3_mul(&mut tmp1, &lambda, &__ac6);
        let __ac7 = t_y.clone();
        bw6_761_Fp3_sub(&mut t_y, &tmp1, &__ac7);
        bw6_761_Fp3_felem_copy(&mut t_x, &tmp2);
        let mut bit: u64;
        bit = ((9586122913090633729u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            bw6_761_Fp3_sub(&mut tmp1, &q_y, &t_y);
            bw6_761_Fp3_sub(&mut tmp2, &q_x, &t_x);
            let __ac8 = tmp2.clone();
            bw6_761_Fp3_inv(&mut tmp2, &__ac8);
            bw6_761_Fp3_mul(&mut lambda, &tmp1, &tmp2);
            bw6_761_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
            let __ac9 = f.clone();
            bw6_761_Fp6_mul(&mut f, &__ac9, &line);
            bw6_761_Fp3_square(&mut tmp1, &lambda);
            let __ac10 = tmp1.clone();
            bw6_761_Fp3_sub(&mut tmp1, &__ac10, &t_x);
            bw6_761_Fp3_sub(&mut tmp2, &tmp1, &q_x);
            bw6_761_Fp3_sub(&mut tmp1, &t_x, &tmp2);
            let __ac11 = tmp1.clone();
            bw6_761_Fp3_mul(&mut tmp1, &lambda, &__ac11);
            let __ac12 = t_y.clone();
            bw6_761_Fp3_sub(&mut t_y, &tmp1, &__ac12);
            bw6_761_Fp3_felem_copy(&mut t_x, &tmp2);
        } else {
        }
    }
    bw6_761_Fp6_felem_copy(&mut out, &f);
}

#[inline]
pub fn bw6_fp6_conjugate(mut out: &mut Fp6, x: &Fp6) {
    bw6_761_Fp3_felem_copy(&mut out.c0, &x.c0);
    bw6_761_Fp3_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bw6_fp6_pow_abs_u(mut out: &mut Fp6, x: &Fp6) {
    let mut result: Fp6 = Fp6::zero();
    let mut base: Fp6 = Fp6::zero();
    bw6_761_Fp6_felem_copy(&mut base, &x);
    bw6_761_Fp6_felem_copy(&mut result, &base);
    let mut i: u64;
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let __ac0 = result.clone();
        bw6_761_Fp6_square(&mut result, &__ac0);
        let mut bit: u64;
        bit = ((9586122913090633729u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac1 = result.clone();
            bw6_761_Fp6_mul(&mut result, &__ac1, &base);
        } else {
        }
    }
    bw6_761_Fp6_felem_copy(&mut out, &result);
}

#[inline]
pub fn bw6_fp6_pow_u(mut out: &mut Fp6, x: &Fp6) {
    bw6_fp6_pow_abs_u(&mut out, &x);
}

#[inline]
pub fn bw6_fp6_frob(mut out: &mut Fp6, x: &Fp6, gamma_fp3: &Fp3, gamma_fp6: &Fp3) {
    bw6_761_felem_copy(&mut out.c0.c0, &x.c0.c0);
    bw6_761_mul(&mut out.c0.c1, &x.c0.c1, &gamma_fp3.c1);
    bw6_761_mul(&mut out.c0.c2, &x.c0.c2, &gamma_fp3.c2);
    bw6_761_mul(&mut out.c1.c0, &x.c1.c0, &gamma_fp6.c0);
    bw6_761_mul(&mut out.c1.c1, &x.c1.c1, &gamma_fp6.c1);
    bw6_761_mul(&mut out.c1.c2, &x.c1.c2, &gamma_fp6.c2);
}

#[inline]
pub fn bw6_fp6_frob_p2(mut out: &mut Fp6, x: &Fp6, gamma_fp3_p2: &Fp3, gamma_fp6_p2: &Fp3) {
    bw6_761_felem_copy(&mut out.c0.c0, &x.c0.c0);
    bw6_761_mul(&mut out.c0.c1, &x.c0.c1, &gamma_fp3_p2.c1);
    bw6_761_mul(&mut out.c0.c2, &x.c0.c2, &gamma_fp3_p2.c2);
    bw6_761_mul(&mut out.c1.c0, &x.c1.c0, &gamma_fp6_p2.c0);
    bw6_761_mul(&mut out.c1.c1, &x.c1.c1, &gamma_fp6_p2.c1);
    bw6_761_mul(&mut out.c1.c2, &x.c1.c2, &gamma_fp6_p2.c2);
}

#[inline]
pub fn bw6_fp6_frob_p3(mut out: &mut Fp6, x: &Fp6, gamma_fp6_p3: &Fp3) {
    bw6_761_felem_copy(&mut out.c0.c0, &x.c0.c0);
    bw6_761_felem_copy(&mut out.c0.c1, &x.c0.c1);
    bw6_761_felem_copy(&mut out.c0.c2, &x.c0.c2);
    bw6_761_mul(&mut out.c1.c0, &x.c1.c0, &gamma_fp6_p3.c0);
    bw6_761_mul(&mut out.c1.c1, &x.c1.c1, &gamma_fp6_p3.c0);
    bw6_761_mul(&mut out.c1.c2, &x.c1.c2, &gamma_fp6_p3.c0);
}

#[inline]
pub fn bw6_final_exp_easy(mut out: &mut Fp6, f: &Fp6, gamma_fp3: &Fp3, gamma_fp6: &Fp3) {
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    bw6_fp6_conjugate(&mut t0, &f);
    bw6_761_Fp6_inv(&mut t1, &f);
    let __ac0 = t0.clone();
    bw6_761_Fp6_mul(&mut t0, &__ac0, &t1);
    bw6_fp6_frob(&mut t1, &t0, &gamma_fp3, &gamma_fp6);
    bw6_761_Fp6_mul(&mut out, &t1, &t0);
}

#[inline]
pub fn bw6_final_exp_hard(mut out: &mut Fp6, f: &Fp6, gamma_fp3: &Fp3, gamma_fp6: &Fp3, gamma_fp3_p2: &Fp3, gamma_fp6_p2: &Fp3, gamma_fp6_p3: &Fp3) {
    let mut a: Fp6 = Fp6::zero();
    let mut b: Fp6 = Fp6::zero();
    let mut c: Fp6 = Fp6::zero();
    let mut d: Fp6 = Fp6::zero();
    bw6_fp6_pow_u(&mut a, &f);
    bw6_761_Fp6_mul(&mut b, &a, &f);
    bw6_fp6_pow_u(&mut a, &b);
    bw6_fp6_conjugate(&mut c, &b);
    bw6_761_Fp6_mul(&mut b, &a, &c);
    bw6_fp6_frob(&mut c, &b, &gamma_fp3, &gamma_fp6);
    bw6_761_Fp6_mul(&mut d, &b, &c);
    bw6_fp6_pow_u(&mut a, &d);
    bw6_fp6_pow_u(&mut b, &a);
    bw6_fp6_frob_p2(&mut c, &d, &gamma_fp3_p2, &gamma_fp6_p2);
    let __ac0 = a.clone();
    bw6_761_Fp6_mul(&mut a, &__ac0, &c);
    let __ac1 = b.clone();
    bw6_fp6_pow_u(&mut b, &__ac1);
    bw6_fp6_frob_p3(&mut c, &d, &gamma_fp6_p3);
    let __ac2 = b.clone();
    bw6_761_Fp6_mul(&mut b, &__ac2, &c);
    let __ac3 = a.clone();
    bw6_761_Fp6_mul(&mut a, &__ac3, &b);
    bw6_761_Fp6_square(&mut b, &f);
    let __ac4 = b.clone();
    bw6_761_Fp6_mul(&mut b, &__ac4, &f);
    bw6_761_Fp6_mul(&mut out, &a, &b);
}

#[inline]
pub fn bw6_final_exp(mut out: &mut Fp6, f: &Fp6, gamma_fp3: &Fp3, gamma_fp6: &Fp3, gamma_fp3_p2: &Fp3, gamma_fp6_p2: &Fp3, gamma_fp6_p3: &Fp3) {
    let mut easy_result: Fp6 = Fp6::zero();
    bw6_final_exp_easy(&mut easy_result, &f, &gamma_fp3, &gamma_fp6);
    bw6_final_exp_hard(&mut out, &easy_result, &gamma_fp3, &gamma_fp6, &gamma_fp3_p2, &gamma_fp6_p2, &gamma_fp6_p3);
}

