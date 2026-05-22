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
pub fn bw6_761_g2_double_step(mut x: &mut Fp3, mut y: &mut Fp3, mut z: &mut Fp3, mut r0: &mut Fp3, mut r1: &mut Fp3, mut r2: &mut Fp3, half_fp: &Fp) {
    let mut A: Fp3 = Fp3::zero();
    let mut B: Fp3 = Fp3::zero();
    let mut C: Fp3 = Fp3::zero();
    let mut D: Fp3 = Fp3::zero();
    let mut E: Fp3 = Fp3::zero();
    let mut F: Fp3 = Fp3::zero();
    let mut G: Fp3 = Fp3::zero();
    let mut H: Fp3 = Fp3::zero();
    let mut J: Fp3 = Fp3::zero();
    let mut EE: Fp3 = Fp3::zero();
    let mut K: Fp3 = Fp3::zero();
    let mut tmp: Fp3 = Fp3::zero();
    bw6_761_Fp3_mul(&mut A, &x, &y);
    let __ac0 = A.clone();
    bw6_761_Fp3_mul_fp(&mut A, &__ac0, &half_fp);
    bw6_761_Fp3_square(&mut B, &y);
    bw6_761_Fp3_square(&mut C, &z);
    bw6_761_Fp3_add(&mut D, &C, &C);
    let __ac1 = D.clone();
    bw6_761_Fp3_add(&mut D, &__ac1, &C);
    bw6_761_Fp3_add(&mut E, &D, &D);
    let __ac2 = E.clone();
    bw6_761_Fp3_add(&mut E, &__ac2, &__ac2);
    bw6_761_Fp3_add(&mut F, &E, &E);
    let __ac3 = F.clone();
    bw6_761_Fp3_add(&mut F, &__ac3, &E);
    bw6_761_Fp3_add(&mut G, &B, &F);
    let __ac4 = G.clone();
    bw6_761_Fp3_mul_fp(&mut G, &__ac4, &half_fp);
    bw6_761_Fp3_add(&mut H, &y, &z);
    let __ac5 = H.clone();
    bw6_761_Fp3_square(&mut H, &__ac5);
    let __ac6 = H.clone();
    bw6_761_Fp3_sub(&mut H, &__ac6, &B);
    let __ac7 = H.clone();
    bw6_761_Fp3_sub(&mut H, &__ac7, &C);
    bw6_761_Fp3_sub(&mut tmp, &E, &B);
    bw6_761_Fp3_felem_copy(&mut r0, &tmp);
    bw6_761_Fp3_square(&mut J, &x);
    bw6_761_Fp3_square(&mut EE, &E);
    bw6_761_Fp3_add(&mut K, &EE, &EE);
    let __ac8 = K.clone();
    bw6_761_Fp3_add(&mut K, &__ac8, &EE);
    bw6_761_Fp3_sub(&mut tmp, &B, &F);
    bw6_761_Fp3_mul(&mut x, &tmp, &A);
    bw6_761_Fp3_square(&mut tmp, &G);
    bw6_761_Fp3_sub(&mut y, &tmp, &K);
    bw6_761_Fp3_mul(&mut z, &B, &H);
    bw6_761_Fp3_add(&mut r1, &J, &J);
    let __ac9 = r1.clone();
    bw6_761_Fp3_add(&mut r1, &__ac9, &J);
    bw6_761_Fp3_opp(&mut r2, &H);
}

#[inline]
pub fn bw6_761_g2_add_step(mut x: &mut Fp3, mut y: &mut Fp3, mut z: &mut Fp3, mut r0: &mut Fp3, mut r1: &mut Fp3, mut r2: &mut Fp3, ax: &Fp3, ay: &Fp3) {
    let mut Y2Z1: Fp3 = Fp3::zero();
    let mut O: Fp3 = Fp3::zero();
    let mut X2Z1: Fp3 = Fp3::zero();
    let mut L: Fp3 = Fp3::zero();
    let mut C: Fp3 = Fp3::zero();
    let mut D: Fp3 = Fp3::zero();
    let mut E: Fp3 = Fp3::zero();
    let mut F: Fp3 = Fp3::zero();
    let mut G: Fp3 = Fp3::zero();
    let mut H: Fp3 = Fp3::zero();
    let mut t1: Fp3 = Fp3::zero();
    let mut tmp: Fp3 = Fp3::zero();
    bw6_761_Fp3_mul(&mut Y2Z1, &ay, &z);
    bw6_761_Fp3_sub(&mut O, &y, &Y2Z1);
    bw6_761_Fp3_mul(&mut X2Z1, &ax, &z);
    bw6_761_Fp3_sub(&mut L, &x, &X2Z1);
    bw6_761_Fp3_square(&mut C, &O);
    bw6_761_Fp3_square(&mut D, &L);
    bw6_761_Fp3_mul(&mut E, &L, &D);
    bw6_761_Fp3_mul(&mut F, &z, &C);
    bw6_761_Fp3_mul(&mut G, &x, &D);
    bw6_761_Fp3_add(&mut H, &E, &F);
    bw6_761_Fp3_add(&mut tmp, &G, &G);
    let __ac0 = H.clone();
    bw6_761_Fp3_sub(&mut H, &__ac0, &tmp);
    bw6_761_Fp3_mul(&mut t1, &y, &E);
    bw6_761_Fp3_sub(&mut tmp, &G, &H);
    let __ac1 = tmp.clone();
    bw6_761_Fp3_mul(&mut tmp, &__ac1, &O);
    bw6_761_Fp3_sub(&mut y, &tmp, &t1);
    bw6_761_Fp3_mul(&mut x, &L, &H);
    let __ac2 = z.clone();
    bw6_761_Fp3_mul(&mut z, &E, &__ac2);
    bw6_761_Fp3_mul(&mut tmp, &ax, &O);
    bw6_761_Fp3_mul(&mut r0, &ay, &L);
    let __ac3 = r0.clone();
    bw6_761_Fp3_sub(&mut r0, &tmp, &__ac3);
    bw6_761_Fp3_opp(&mut r1, &O);
    bw6_761_Fp3_felem_copy(&mut r2, &L);
}

#[inline]
pub fn bw6_761_g2_line_compute(mut x: &mut Fp3, mut y: &mut Fp3, mut z: &mut Fp3, mut r0: &mut Fp3, mut r1: &mut Fp3, mut r2: &mut Fp3, ax: &Fp3, ay: &Fp3) {
    let mut Y2Z1: Fp3 = Fp3::zero();
    let mut O: Fp3 = Fp3::zero();
    let mut X2Z1: Fp3 = Fp3::zero();
    let mut L: Fp3 = Fp3::zero();
    let mut tmp: Fp3 = Fp3::zero();
    bw6_761_Fp3_mul(&mut Y2Z1, &ay, &z);
    bw6_761_Fp3_sub(&mut O, &y, &Y2Z1);
    bw6_761_Fp3_mul(&mut X2Z1, &ax, &z);
    bw6_761_Fp3_sub(&mut L, &x, &X2Z1);
    bw6_761_Fp3_mul(&mut tmp, &ax, &O);
    bw6_761_Fp3_mul(&mut r0, &ay, &L);
    let __ac0 = r0.clone();
    bw6_761_Fp3_sub(&mut r0, &tmp, &__ac0);
    bw6_761_Fp3_opp(&mut r1, &O);
    bw6_761_Fp3_felem_copy(&mut r2, &L);
}

#[inline]
pub fn bw6_761_sparse_line_eval(mut out: &mut Fp6, r0: &Fp3, r1: &Fp3, r2: &Fp3, p_x: &Fp, p_y: &Fp) {
    let mut r1px: Fp3 = Fp3::zero();
    let mut r2py: Fp3 = Fp3::zero();
    bw6_761_Fp3_mul_fp(&mut r1px, &r1, &p_x);
    bw6_761_Fp3_mul_fp(&mut r2py, &r2, &p_y);
    bw6_761_felem_copy(&mut out.c0.c0, &r0.c0);
    bw6_761_felem_copy(&mut out.c0.c1, &r1px.c0);
    bw6_761_from_word(&mut out.c0.c2, 0u64);
    bw6_761_from_word(&mut out.c1.c0, 0u64);
    bw6_761_felem_copy(&mut out.c1.c1, &r2py.c0);
    bw6_761_from_word(&mut out.c1.c2, 0u64);
}

#[inline]
pub fn bw6_761_miller_loop_optimal(mut out: &mut Fp6, p_x: &Fp, p_y: &Fp, q0x: &Fp3, q0y: &Fp3, q1x: &Fp3, q1y: &Fp3, q0ny: &Fp3, q1ny: &Fp3, half_fp: &Fp) {
    let mut f: Fp6 = Fp6::zero();
    let mut qx: Fp3 = Fp3::zero();
    let mut qy: Fp3 = Fp3::zero();
    let mut qz: Fp3 = Fp3::zero();
    let mut r0d: Fp3 = Fp3::zero();
    let mut r1d: Fp3 = Fp3::zero();
    let mut r2d: Fp3 = Fp3::zero();
    let mut r0a: Fp3 = Fp3::zero();
    let mut r1a: Fp3 = Fp3::zero();
    let mut r2a: Fp3 = Fp3::zero();
    let mut line_d: Fp6 = Fp6::zero();
    let mut line_a: Fp6 = Fp6::zero();
    bw6_761_Fp3_felem_copy(&mut qx, &q1x);
    bw6_761_Fp3_felem_copy(&mut qy, &q1y);
    bw6_761_from_word(&mut qz.c0, 1u64);
    bw6_761_from_word(&mut qz.c1, 0u64);
    bw6_761_from_word(&mut qz.c2, 0u64);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut f, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac0 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac0);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac1 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac1, &line_d);
    let __ac2 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac2);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac3 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac3, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac4 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac4, &line_a);
    let __ac5 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac5);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac6 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac6, &line_d);
    let __ac7 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac7);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac8 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac8, &line_d);
    let __ac9 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac9);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac10 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac10, &line_d);
    let __ac11 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac11);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac12 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac12, &line_d);
    let __ac13 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac13);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac14 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac14, &line_d);
    let __ac15 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac15);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac16 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac16, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac17 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac17, &line_a);
    let __ac18 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac18);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac19 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac19, &line_d);
    let __ac20 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac20);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac21 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac21, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac22 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac22, &line_a);
    let __ac23 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac23);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac24 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac24, &line_d);
    let __ac25 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac25);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac26 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac26, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac27 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac27, &line_a);
    let __ac28 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac28);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac29 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac29, &line_d);
    let __ac30 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac30);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac31 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac31, &line_d);
    let __ac32 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac32);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac33 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac33, &line_d);
    let __ac34 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac34);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac35 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac35, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac36 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac36, &line_a);
    let __ac37 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac37);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac38 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac38, &line_d);
    let __ac39 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac39);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac40 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac40, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac41 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac41, &line_a);
    let __ac42 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac42);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac43 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac43, &line_d);
    let __ac44 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac44);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac45 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac45, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac46 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac46, &line_a);
    let __ac47 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac47);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac48 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac48, &line_d);
    let __ac49 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac49);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac50 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac50, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac51 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac51, &line_a);
    let __ac52 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac52);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac53 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac53, &line_d);
    let __ac54 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac54);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac55 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac55, &line_d);
    let __ac56 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac56);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac57 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac57, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac58 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac58, &line_a);
    let __ac59 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac59);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac60 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac60, &line_d);
    let __ac61 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac61);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac62 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac62, &line_d);
    let __ac63 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac63);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac64 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac64, &line_d);
    let __ac65 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac65);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac66 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac66, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac67 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac67, &line_a);
    let __ac68 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac68);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac69 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac69, &line_d);
    let __ac70 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac70);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac71 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac71, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac72 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac72, &line_a);
    let __ac73 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac73);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac74 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac74, &line_d);
    let __ac75 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac75);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac76 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac76, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac77 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac77, &line_a);
    let __ac78 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac78);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac79 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac79, &line_d);
    let __ac80 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac80);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac81 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac81, &line_d);
    let __ac82 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac82);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac83 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac83, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac84 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac84, &line_a);
    let __ac85 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac85);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac86 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac86, &line_d);
    let __ac87 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac87);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac88 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac88, &line_d);
    let __ac89 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac89);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac90 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac90, &line_d);
    let __ac91 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac91);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac92 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac92, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac93 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac93, &line_a);
    let __ac94 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac94);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac95 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac95, &line_d);
    let __ac96 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac96);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac97 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac97, &line_d);
    let __ac98 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac98);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac99 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac99, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac100 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac100, &line_a);
    let __ac101 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac101);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac102 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac102, &line_d);
    let __ac103 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac103);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac104 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac104, &line_d);
    let __ac105 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac105);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac106 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac106, &line_d);
    let __ac107 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac107);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac108 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac108, &line_d);
    let __ac109 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac109);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac110 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac110, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac111 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac111, &line_a);
    let __ac112 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac112);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac113 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac113, &line_d);
    let __ac114 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac114);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac115 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac115, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac116 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac116, &line_a);
    let __ac117 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac117);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac118 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac118, &line_d);
    let __ac119 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac119);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac120 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac120, &line_d);
    let __ac121 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac121);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac122 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac122, &line_d);
    let __ac123 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac123);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac124 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac124, &line_d);
    let __ac125 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac125);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac126 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac126, &line_d);
    let __ac127 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac127);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac128 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac128, &line_d);
    let __ac129 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac129);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac130 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac130, &line_d);
    let __ac131 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac131);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac132 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac132, &line_d);
    let __ac133 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac133);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac134 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac134, &line_d);
    let __ac135 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac135);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac136 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac136, &line_d);
    let __ac137 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac137);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac138 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac138, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac139 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac139, &line_a);
    let __ac140 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac140);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac141 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac141, &line_d);
    let __ac142 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac142);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac143 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac143, &line_d);
    let __ac144 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac144);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac145 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac145, &line_d);
    let __ac146 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac146);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac147 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac147, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac148 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac148, &line_a);
    let __ac149 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac149);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac150 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac150, &line_d);
    let __ac151 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac151);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac152 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac152, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac153 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac153, &line_a);
    let __ac154 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac154);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac155 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac155, &line_d);
    let __ac156 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac156);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac157 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac157, &line_d);
    let __ac158 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac158);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac159 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac159, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac160 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac160, &line_a);
    let __ac161 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac161);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac162 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac162, &line_d);
    let __ac163 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac163);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac164 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac164, &line_d);
    let __ac165 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac165);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac166 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac166, &line_d);
    let __ac167 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac167);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac168 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac168, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac169 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac169, &line_a);
    let __ac170 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac170);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac171 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac171, &line_d);
    let __ac172 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac172);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac173 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac173, &line_d);
    let __ac174 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac174);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac175 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac175, &line_d);
    let __ac176 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac176);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac177 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac177, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac178 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac178, &line_a);
    let __ac179 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac179);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac180 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac180, &line_d);
    let __ac181 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac181);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac182 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac182, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac183 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac183, &line_a);
    let __ac184 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac184);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac185 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac185, &line_d);
    let __ac186 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac186);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac187 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac187, &line_d);
    let __ac188 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac188);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac189 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac189, &line_d);
    let __ac190 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac190);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac191 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac191, &line_d);
    let __ac192 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac192);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac193 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac193, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac194 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac194, &line_a);
    let __ac195 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac195);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac196 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac196, &line_d);
    let __ac197 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac197);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac198 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac198, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac199 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac199, &line_a);
    let __ac200 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac200);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac201 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac201, &line_d);
    let __ac202 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac202);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac203 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac203, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac204 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac204, &line_a);
    let __ac205 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac205);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac206 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac206, &line_d);
    let __ac207 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac207);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac208 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac208, &line_d);
    let __ac209 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac209);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac210 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac210, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac211 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac211, &line_a);
    let __ac212 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac212);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac213 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac213, &line_d);
    let __ac214 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac214);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac215 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac215, &line_d);
    let __ac216 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac216);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac217 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac217, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac218 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac218, &line_a);
    let __ac219 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac219);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac220 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac220, &line_d);
    let __ac221 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac221);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac222 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac222, &line_d);
    let __ac223 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac223);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac224 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac224, &line_d);
    let __ac225 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac225);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac226 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac226, &line_d);
    let __ac227 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac227);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac228 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac228, &line_d);
    let __ac229 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac229);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac230 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac230, &line_d);
    let __ac231 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac231);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac232 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac232, &line_d);
    let __ac233 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac233);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac234 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac234, &line_d);
    let __ac235 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac235);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac236 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac236, &line_d);
    let __ac237 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac237);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac238 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac238, &line_d);
    let __ac239 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac239);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac240 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac240, &line_d);
    let __ac241 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac241);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac242 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac242, &line_d);
    let __ac243 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac243);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac244 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac244, &line_d);
    let __ac245 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac245);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac246 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac246, &line_d);
    let __ac247 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac247);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac248 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac248, &line_d);
    let __ac249 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac249);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac250 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac250, &line_d);
    let __ac251 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac251);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac252 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac252, &line_d);
    let __ac253 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac253);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac254 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac254, &line_d);
    let __ac255 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac255);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac256 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac256, &line_d);
    let __ac257 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac257);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac258 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac258, &line_d);
    let __ac259 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac259);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac260 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac260, &line_d);
    let __ac261 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac261);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac262 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac262, &line_d);
    let __ac263 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac263);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac264 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac264, &line_d);
    let __ac265 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac265);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac266 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac266, &line_d);
    let __ac267 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac267);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac268 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac268, &line_d);
    let __ac269 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac269);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac270 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac270, &line_d);
    let __ac271 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac271);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac272 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac272, &line_d);
    let __ac273 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac273);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac274 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac274, &line_d);
    let __ac275 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac275);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac276 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac276, &line_d);
    let __ac277 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac277);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac278 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac278, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q0x, &q0y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac279 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac279, &line_a);
    let __ac280 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac280);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac281 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac281, &line_d);
    let __ac282 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac282);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac283 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac283, &line_d);
    let __ac284 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac284);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac285 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac285, &line_d);
    let __ac286 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac286);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac287 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac287, &line_d);
    let __ac288 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac288);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac289 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac289, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q0x, &q0y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac290 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac290, &line_a);
    let __ac291 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac291);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac292 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac292, &line_d);
    let __ac293 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac293);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac294 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac294, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q0x, &q0y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac295 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac295, &line_a);
    let __ac296 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac296);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac297 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac297, &line_d);
    let __ac298 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac298);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac299 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac299, &line_d);
    let __ac300 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac300);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac301 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac301, &line_d);
    let __ac302 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac302);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac303 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac303, &line_d);
    let __ac304 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac304);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac305 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac305, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q0x, &q0y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac306 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac306, &line_a);
    let __ac307 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac307);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac308 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac308, &line_d);
    let __ac309 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac309);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac310 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac310, &line_d);
    let __ac311 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac311);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac312 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac312, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q0x, &q0y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac313 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac313, &line_a);
    let __ac314 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac314);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac315 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac315, &line_d);
    let __ac316 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac316);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac317 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac317, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q0x, &q0ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac318 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac318, &line_a);
    let __ac319 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac319);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac320 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac320, &line_d);
    let __ac321 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac321);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac322 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac322, &line_d);
    let __ac323 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac323);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac324 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac324, &line_d);
    let __ac325 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac325);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac326 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac326, &line_d);
    let __ac327 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac327);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac328 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac328, &line_d);
    let __ac329 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac329);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac330 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac330, &line_d);
    let __ac331 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac331);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac332 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac332, &line_d);
    let __ac333 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac333);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac334 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac334, &line_d);
    let __ac335 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac335);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac336 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac336, &line_d);
    let __ac337 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac337);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac338 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac338, &line_d);
    let __ac339 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac339);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac340 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac340, &line_d);
    let __ac341 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac341);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac342 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac342, &line_d);
    let __ac343 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac343);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac344 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac344, &line_d);
    let __ac345 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac345);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac346 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac346, &line_d);
    let __ac347 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac347);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac348 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac348, &line_d);
    let __ac349 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac349);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac350 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac350, &line_d);
    let __ac351 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac351);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac352 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac352, &line_d);
    let __ac353 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac353);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac354 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac354, &line_d);
    let __ac355 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac355);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac356 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac356, &line_d);
    let __ac357 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac357);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac358 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac358, &line_d);
    let __ac359 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac359);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac360 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac360, &line_d);
    let __ac361 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac361);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac362 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac362, &line_d);
    let __ac363 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac363);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac364 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac364, &line_d);
    let __ac365 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac365);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac366 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac366, &line_d);
    let __ac367 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac367);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac368 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac368, &line_d);
    let __ac369 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac369);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac370 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac370, &line_d);
    let __ac371 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac371);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac372 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac372, &line_d);
    let __ac373 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac373);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac374 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac374, &line_d);
    let __ac375 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac375);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac376 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac376, &line_d);
    let __ac377 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac377);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac378 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac378, &line_d);
    let __ac379 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac379);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac380 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac380, &line_d);
    let __ac381 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac381);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac382 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac382, &line_d);
    let __ac383 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac383);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac384 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac384, &line_d);
    let __ac385 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac385);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac386 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac386, &line_d);
    let __ac387 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac387);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac388 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac388, &line_d);
    let __ac389 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac389);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac390 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac390, &line_d);
    let __ac391 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac391);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac392 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac392, &line_d);
    let __ac393 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac393);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac394 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac394, &line_d);
    let __ac395 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac395);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac396 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac396, &line_d);
    let __ac397 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac397);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac398 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac398, &line_d);
    let __ac399 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac399);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac400 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac400, &line_d);
    let __ac401 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac401);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac402 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac402, &line_d);
    let __ac403 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac403);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac404 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac404, &line_d);
    let __ac405 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac405);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac406 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac406, &line_d);
    let __ac407 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac407);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac408 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac408, &line_d);
    bw6_761_g2_add_step(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q0x, &q0y);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac409 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac409, &line_a);
    let __ac410 = f.clone();
    bw6_761_Fp6_square(&mut f, &__ac410);
    bw6_761_g2_double_step(&mut qx, &mut qy, &mut qz, &mut r0d, &mut r1d, &mut r2d, &half_fp);
    bw6_761_sparse_line_eval(&mut line_d, &r0d, &r1d, &r2d, &p_x, &p_y);
    let __ac411 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac411, &line_d);
    bw6_761_g2_line_compute(&mut qx, &mut qy, &mut qz, &mut r0a, &mut r1a, &mut r2a, &q1x, &q1ny);
    bw6_761_sparse_line_eval(&mut line_a, &r0a, &r1a, &r2a, &p_x, &p_y);
    let __ac412 = f.clone();
    bw6_761_Fp6_mul(&mut f, &__ac412, &line_a);
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

