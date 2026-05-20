#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp(pub [u64; 6]);
impl Fp { #[inline] pub const fn zero() -> Self { Fp([0u64; 6]) } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp2 { pub c0: Fp, pub c1: Fp }
impl Fp2 { #[inline] pub const fn zero() -> Self { Fp2 { c0: Fp::zero(), c1: Fp::zero() } } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp6 { pub c0: Fp2, pub c1: Fp2, pub c2: Fp2 }
impl Fp6 { #[inline] pub const fn zero() -> Self { Fp6 { c0: Fp2::zero(), c1: Fp2::zero(), c2: Fp2::zero() } } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp12 { pub c0: Fp6, pub c1: Fp6 }
impl Fp12 { #[inline] pub const fn zero() -> Self { Fp12 { c0: Fp6::zero(), c1: Fp6::zero() } } }

unsafe extern "C" {
    fn _bls377_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls377_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls377_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls377_square(o: *mut u64, x: *const u64);
    fn _bls377_opp(o: *mut u64, x: *const u64);
    fn _bls377_felem_copy(o: *mut u64, x: *const u64);
    fn _bls377_from_word(o: *mut u64, w: u64);
    fn _bls377_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bls377_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bls377_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls377_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls377_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls377_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls377_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls377_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls377_square(o: &mut Fp, x: &Fp) { unsafe { _bls377_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls377_opp(o: &mut Fp, x: &Fp) { unsafe { _bls377_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls377_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bls377_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls377_from_word(o: &mut Fp, w: u64) { unsafe { _bls377_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bls377_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bls377_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls377_inv(o: &mut Fp, x: &Fp) { unsafe { _bls377_inv(o.0.as_mut_ptr(), x.0.as_ptr()) } }

#[inline]
pub fn bls377_Fp2_felem_copy(mut out: &mut Fp, x: &Fp) {
    bls377_felem_copy(&mut out, &x);
    bls377_felem_copy(&mut out, &x);
}

#[inline]
pub fn bls377_Fp2_add(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    bls377_add(&mut out, &inx, &iny);
    bls377_add(&mut out, &inx, &iny);
}

#[inline]
pub fn bls377_Fp2_sub(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    bls377_sub(&mut out, &inx, &iny);
    bls377_sub(&mut out, &inx, &iny);
}

#[inline]
pub fn bls377_Fp2_mul(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    let mut v2: Fp = Fp::zero();
    bls377_mul(&mut v0, &inx, &iny);
    bls377_mul(&mut v1, &inx, &iny);
    bls377_add(&mut v2, &inx, &inx);
    bls377_add(&mut out, &iny, &iny);
    let __ac0 = out.clone();
    bls377_mul(&mut out, &__ac0, &v2);
    let __ac1 = out.clone();
    bls377_sub(&mut out, &__ac1, &v0);
    let __ac2 = out.clone();
    bls377_sub(&mut out, &__ac2, &v1);
    bls377_add(&mut v2, &v1, &v1);
    let __ac3 = v2.clone();
    bls377_add(&mut v2, &__ac3, &__ac3);
    let __ac4 = v2.clone();
    bls377_add(&mut v2, &__ac4, &v1);
    bls377_sub(&mut out, &v0, &v2);
}

#[inline]
pub fn bls377_Fp2_square(mut out: &mut Fp, inx: &Fp) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    bls377_square(&mut v0, &inx);
    bls377_square(&mut v1, &inx);
    bls377_mul(&mut out, &inx, &inx);
    let __ac0 = out.clone();
    bls377_add(&mut out, &__ac0, &__ac0);
    bls377_add(&mut out, &v1, &v1);
    let __ac1 = out.clone();
    bls377_add(&mut out, &__ac1, &__ac1);
    let __ac2 = out.clone();
    bls377_add(&mut out, &__ac2, &v1);
    let __ac3 = out.clone();
    bls377_sub(&mut out, &v0, &__ac3);
}

#[inline]
pub fn bls377_Fp2_inv(mut out: &mut Fp, inx: &Fp) {
    let mut asq: Fp = Fp::zero();
    let mut bsq: Fp = Fp::zero();
    let mut norm: Fp = Fp::zero();
    bls377_square(&mut asq, &inx);
    bls377_square(&mut bsq, &inx);
    bls377_add(&mut norm, &bsq, &bsq);
    let __ac0 = norm.clone();
    bls377_add(&mut norm, &__ac0, &__ac0);
    let __ac1 = norm.clone();
    bls377_add(&mut norm, &__ac1, &bsq);
    let __ac2 = norm.clone();
    bls377_add(&mut norm, &asq, &__ac2);
    let __ac3 = norm.clone();
    bls377_inv(&mut norm, &__ac3);
    bls377_mul(&mut out, &inx, &norm);
    bls377_sub(&mut asq, &bsq, &bsq);
    let __ac4 = asq.clone();
    bls377_sub(&mut asq, &__ac4, &inx);
    bls377_mul(&mut out, &asq, &norm);
}

#[inline]
pub fn bls377_Fp2_opp(mut out: &mut Fp, x: &Fp) {
    bls377_opp(&mut out, &x);
    bls377_opp(&mut out, &x);
}

#[inline]
pub fn bls377_Fp2_mul_xi(mut out: &mut Fp, x: &Fp) {
    bls377_add(&mut out, &x, &x);
    let __ac0 = out.clone();
    bls377_add(&mut out, &__ac0, &__ac0);
    let __ac1 = out.clone();
    bls377_add(&mut out, &__ac1, &x);
    bls377_felem_copy(&mut out, &x);
    let mut tmp: Fp = Fp::zero();
    let __ac2 = tmp.clone();
    bls377_sub(&mut tmp, &__ac2, &__ac2);
    let __ac3 = out.clone();
    bls377_sub(&mut out, &tmp, &__ac3);
}

#[inline]
pub fn bls377_Fp6_felem_copy(mut out: &mut Fp, x: &Fp) {
    bls377_Fp2_felem_copy(&mut out, &x);
    bls377_Fp2_felem_copy(&mut out, &x);
    bls377_Fp2_felem_copy(&mut out, &x);
}

#[inline]
pub fn bls377_Fp6_add(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bls377_Fp6_felem_copy(&mut allocx.c0.c0, &inx);
    bls377_Fp6_felem_copy(&mut allocy.c0.c0, &iny);
    bls377_Fp2_add(&mut out, &allocx.c0.c0, &allocy.c0.c0);
    bls377_Fp2_add(&mut out, &allocx.c1.c0, &allocy.c1.c0);
    bls377_Fp2_add(&mut out, &allocx.c2.c0, &allocy.c2.c0);
}

#[inline]
pub fn bls377_Fp6_sub(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bls377_Fp6_felem_copy(&mut allocx.c0.c0, &inx);
    bls377_Fp6_felem_copy(&mut allocy.c0.c0, &iny);
    bls377_Fp2_sub(&mut out, &allocx.c0.c0, &allocy.c0.c0);
    bls377_Fp2_sub(&mut out, &allocx.c1.c0, &allocy.c1.c0);
    bls377_Fp2_sub(&mut out, &allocx.c2.c0, &allocy.c2.c0);
}

#[inline]
pub fn bls377_Fp6_opp(mut out: &mut Fp, x: &Fp) {
    let mut allocx: Fp6 = Fp6::zero();
    bls377_Fp6_felem_copy(&mut allocx.c0.c0, &x);
    bls377_Fp2_opp(&mut out, &allocx.c0.c0);
    bls377_Fp2_opp(&mut out, &allocx.c1.c0);
    bls377_Fp2_opp(&mut out, &allocx.c2.c0);
}

#[inline]
pub fn bls377_Fp6_mul(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    let mut a0b0: Fp2 = Fp2::zero();
    let mut a1b1: Fp2 = Fp2::zero();
    let mut a2b2: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    let mut u: Fp2 = Fp2::zero();
    bls377_Fp6_felem_copy(&mut allocx.c0.c0, &inx);
    bls377_Fp6_felem_copy(&mut allocy.c0.c0, &iny);
    bls377_Fp2_mul(&mut a0b0.c0, &allocx.c0.c0, &allocy.c0.c0);
    bls377_Fp2_mul(&mut a1b1.c0, &allocx.c1.c0, &allocy.c1.c0);
    bls377_Fp2_mul(&mut a2b2.c0, &allocx.c2.c0, &allocy.c2.c0);
    bls377_Fp2_add(&mut t.c0, &allocx.c1.c0, &allocx.c2.c0);
    bls377_Fp2_add(&mut u.c0, &allocy.c1.c0, &allocy.c2.c0);
    let __ac0 = t.c0.clone();
    bls377_Fp2_mul(&mut t.c0, &__ac0, &u.c0);
    let __ac1 = t.c0.clone();
    bls377_Fp2_sub(&mut t.c0, &__ac1, &a1b1.c0);
    let __ac2 = t.c0.clone();
    bls377_Fp2_sub(&mut t.c0, &__ac2, &a2b2.c0);
    let __ac3 = t.c0.clone();
    bls377_Fp2_mul_xi(&mut t.c0, &__ac3);
    bls377_Fp2_add(&mut out, &a0b0.c0, &t.c0);
    bls377_Fp2_add(&mut t.c0, &allocx.c0.c0, &allocx.c1.c0);
    bls377_Fp2_add(&mut u.c0, &allocy.c0.c0, &allocy.c1.c0);
    let __ac4 = t.c0.clone();
    bls377_Fp2_mul(&mut t.c0, &__ac4, &u.c0);
    let __ac5 = t.c0.clone();
    bls377_Fp2_sub(&mut t.c0, &__ac5, &a0b0.c0);
    let __ac6 = t.c0.clone();
    bls377_Fp2_sub(&mut t.c0, &__ac6, &a1b1.c0);
    bls377_Fp2_mul_xi(&mut u.c0, &a2b2.c0);
    bls377_Fp2_add(&mut out, &t.c0, &u.c0);
    bls377_Fp2_add(&mut t.c0, &allocx.c0.c0, &allocx.c2.c0);
    bls377_Fp2_add(&mut u.c0, &allocy.c0.c0, &allocy.c2.c0);
    let __ac7 = t.c0.clone();
    bls377_Fp2_mul(&mut t.c0, &__ac7, &u.c0);
    let __ac8 = t.c0.clone();
    bls377_Fp2_sub(&mut t.c0, &__ac8, &a0b0.c0);
    let __ac9 = t.c0.clone();
    bls377_Fp2_sub(&mut t.c0, &__ac9, &a2b2.c0);
    bls377_Fp2_add(&mut out, &t.c0, &a1b1.c0);
}

#[inline]
pub fn bls377_Fp6_square(mut out: &mut Fp, x: &Fp) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut s0: Fp2 = Fp2::zero();
    let mut s1: Fp2 = Fp2::zero();
    let mut s2: Fp2 = Fp2::zero();
    let mut s3: Fp2 = Fp2::zero();
    let mut s4: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    bls377_Fp6_felem_copy(&mut allocx.c0.c0, &x);
    bls377_Fp2_square(&mut s0.c0, &allocx.c0.c0);
    bls377_Fp2_mul(&mut t.c0, &allocx.c0.c0, &allocx.c1.c0);
    bls377_Fp2_add(&mut s1.c0, &t.c0, &t.c0);
    bls377_Fp2_sub(&mut t.c0, &allocx.c0.c0, &allocx.c1.c0);
    let __ac0 = t.c0.clone();
    bls377_Fp2_add(&mut t.c0, &__ac0, &allocx.c2.c0);
    bls377_Fp2_square(&mut s2.c0, &t.c0);
    bls377_Fp2_mul(&mut t.c0, &allocx.c1.c0, &allocx.c2.c0);
    bls377_Fp2_add(&mut s3.c0, &t.c0, &t.c0);
    bls377_Fp2_square(&mut s4.c0, &allocx.c2.c0);
    bls377_Fp2_mul_xi(&mut t.c0, &s3.c0);
    bls377_Fp2_add(&mut out, &s0.c0, &t.c0);
    bls377_Fp2_mul_xi(&mut t.c0, &s4.c0);
    bls377_Fp2_add(&mut out, &s1.c0, &t.c0);
    bls377_Fp2_add(&mut t.c0, &s1.c0, &s2.c0);
    let __ac1 = t.c0.clone();
    bls377_Fp2_add(&mut t.c0, &__ac1, &s3.c0);
    let __ac2 = t.c0.clone();
    bls377_Fp2_sub(&mut t.c0, &__ac2, &s0.c0);
    bls377_Fp2_sub(&mut out, &t.c0, &s4.c0);
}

#[inline]
pub fn bls377_Fp6_inv(mut out: &mut Fp, x: &Fp) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut vA: Fp2 = Fp2::zero();
    let mut vB: Fp2 = Fp2::zero();
    let mut vC: Fp2 = Fp2::zero();
    let mut t1: Fp2 = Fp2::zero();
    let mut t2: Fp2 = Fp2::zero();
    let mut t3: Fp2 = Fp2::zero();
    bls377_Fp6_felem_copy(&mut allocx.c0.c0, &x);
    bls377_Fp2_square(&mut t1.c0, &allocx.c0.c0);
    bls377_Fp2_mul(&mut t2.c0, &allocx.c1.c0, &allocx.c2.c0);
    bls377_Fp2_mul_xi(&mut t3.c0, &t2.c0);
    bls377_Fp2_sub(&mut vA.c0, &t1.c0, &t3.c0);
    bls377_Fp2_square(&mut t1.c0, &allocx.c2.c0);
    bls377_Fp2_mul_xi(&mut t3.c0, &t1.c0);
    bls377_Fp2_mul(&mut t2.c0, &allocx.c0.c0, &allocx.c1.c0);
    bls377_Fp2_sub(&mut vB.c0, &t3.c0, &t2.c0);
    bls377_Fp2_square(&mut t1.c0, &allocx.c1.c0);
    bls377_Fp2_mul(&mut t2.c0, &allocx.c0.c0, &allocx.c2.c0);
    bls377_Fp2_sub(&mut vC.c0, &t1.c0, &t2.c0);
    bls377_Fp2_mul(&mut t1.c0, &allocx.c0.c0, &vA.c0);
    bls377_Fp2_mul(&mut t2.c0, &allocx.c2.c0, &vB.c0);
    bls377_Fp2_mul(&mut t3.c0, &allocx.c1.c0, &vC.c0);
    let __ac0 = t2.c0.clone();
    bls377_Fp2_add(&mut t2.c0, &__ac0, &t3.c0);
    let __ac1 = t2.c0.clone();
    bls377_Fp2_mul_xi(&mut t2.c0, &__ac1);
    let __ac2 = t1.c0.clone();
    bls377_Fp2_add(&mut t1.c0, &__ac2, &t2.c0);
    let __ac3 = t1.c0.clone();
    bls377_Fp2_inv(&mut t1.c0, &__ac3);
    bls377_Fp2_mul(&mut out, &vA.c0, &t1.c0);
    bls377_Fp2_mul(&mut out, &vB.c0, &t1.c0);
    bls377_Fp2_mul(&mut out, &vC.c0, &t1.c0);
}

#[inline]
pub fn bls377_Fp6_add_nocopy(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    bls377_Fp2_add(&mut out, &inx, &iny);
    bls377_Fp2_add(&mut out, &inx, &iny);
    bls377_Fp2_add(&mut out, &inx, &iny);
}

#[inline]
pub fn bls377_Fp6_sub_nocopy(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    bls377_Fp2_sub(&mut out, &inx, &iny);
    bls377_Fp2_sub(&mut out, &inx, &iny);
    bls377_Fp2_sub(&mut out, &inx, &iny);
}

#[inline]
pub fn bls377_Fp6_mul_by_v(mut out: &mut Fp, x: &Fp) {
    let mut tmp: Fp6 = Fp6::zero();
    bls377_Fp6_felem_copy(&mut tmp.c0.c0, &x);
    bls377_Fp2_mul_xi(&mut out, &tmp.c2.c0);
    bls377_Fp2_felem_copy(&mut out, &tmp.c0.c0);
    bls377_Fp2_felem_copy(&mut out, &tmp.c1.c0);
}

#[inline]
pub fn bls377_Fp12_felem_copy(mut out: &mut Fp, x: &Fp) {
    bls377_Fp6_felem_copy(&mut out, &x);
    bls377_Fp6_felem_copy(&mut out, &x);
}

#[inline]
pub fn bls377_Fp12_add(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut ax.c0.c0.c0, &inx);
    bls377_Fp12_felem_copy(&mut ay.c0.c0.c0, &iny);
    bls377_Fp6_add(&mut out, &ax.c0.c0.c0, &ay.c0.c0.c0);
    bls377_Fp6_add(&mut out, &ax.c1.c0.c0, &ay.c1.c0.c0);
}

#[inline]
pub fn bls377_Fp12_sub(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut ax.c0.c0.c0, &inx);
    bls377_Fp12_felem_copy(&mut ay.c0.c0.c0, &iny);
    bls377_Fp6_sub(&mut out, &ax.c0.c0.c0, &ay.c0.c0.c0);
    bls377_Fp6_sub(&mut out, &ax.c1.c0.c0, &ay.c1.c0.c0);
}

#[inline]
pub fn bls377_Fp12_opp(mut out: &mut Fp, x: &Fp) {
    let mut allocx: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut allocx.c0.c0.c0, &x);
    bls377_Fp6_opp(&mut out, &allocx.c0.c0.c0);
    bls377_Fp6_opp(&mut out, &allocx.c1.c0.c0);
}

#[inline]
pub fn bls377_Fp12_conjugate(mut out: &mut Fp, x: &Fp) {
    let mut allocx: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut allocx.c0.c0.c0, &x);
    bls377_Fp6_felem_copy(&mut out, &allocx.c0.c0.c0);
    bls377_Fp6_opp(&mut out, &allocx.c1.c0.c0);
}

#[inline]
pub fn bls377_Fp12_mul(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut ax.c0.c0.c0, &inx);
    bls377_Fp12_felem_copy(&mut ay.c0.c0.c0, &iny);
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bls377_Fp6_mul(&mut v0.c0.c0, &ax.c0.c0.c0, &ay.c0.c0.c0);
    bls377_Fp6_mul(&mut v1.c0.c0, &ax.c1.c0.c0, &ay.c1.c0.c0);
    bls377_Fp6_add(&mut t.c0.c0, &ax.c0.c0.c0, &ax.c1.c0.c0);
    bls377_Fp6_add(&mut u.c0.c0, &ay.c0.c0.c0, &ay.c1.c0.c0);
    let __ac0 = t.c0.c0.clone();
    bls377_Fp6_mul(&mut t.c0.c0, &__ac0, &u.c0.c0);
    bls377_Fp6_mul_by_v(&mut u.c0.c0, &v1.c0.c0);
    bls377_Fp6_add(&mut out, &v0.c0.c0, &u.c0.c0);
    let __ac1 = t.c0.c0.clone();
    bls377_Fp6_sub(&mut t.c0.c0, &__ac1, &v0.c0.c0);
    bls377_Fp6_sub(&mut out, &t.c0.c0, &v1.c0.c0);
}

#[inline]
pub fn bls377_Fp12_square(mut out: &mut Fp, x: &Fp) {
    let mut allocx: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut allocx.c0.c0.c0, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    let mut t2: Fp6 = Fp6::zero();
    bls377_Fp6_square(&mut t0.c0.c0, &allocx.c0.c0.c0);
    bls377_Fp6_square(&mut t1.c0.c0, &allocx.c1.c0.c0);
    bls377_Fp6_mul(&mut t2.c0.c0, &allocx.c0.c0.c0, &allocx.c1.c0.c0);
    let __ac0 = t1.c0.c0.clone();
    bls377_Fp6_mul_by_v(&mut t1.c0.c0, &__ac0);
    bls377_Fp6_add(&mut out, &t0.c0.c0, &t1.c0.c0);
    bls377_Fp6_add(&mut out, &t2.c0.c0, &t2.c0.c0);
}

#[inline]
pub fn bls377_Fp12_inv(mut out: &mut Fp, x: &Fp) {
    let mut allocx: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut allocx.c0.c0.c0, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    bls377_Fp6_square(&mut t0.c0.c0, &allocx.c0.c0.c0);
    bls377_Fp6_square(&mut t1.c0.c0, &allocx.c1.c0.c0);
    let __ac0 = t1.c0.c0.clone();
    bls377_Fp6_mul_by_v(&mut t1.c0.c0, &__ac0);
    let __ac1 = t0.c0.c0.clone();
    bls377_Fp6_sub(&mut t0.c0.c0, &__ac1, &t1.c0.c0);
    let __ac2 = t0.c0.c0.clone();
    bls377_Fp6_inv(&mut t0.c0.c0, &__ac2);
    bls377_Fp6_mul(&mut out, &allocx.c0.c0.c0, &t0.c0.c0);
    bls377_Fp6_mul(&mut out, &allocx.c1.c0.c0, &t0.c0.c0);
    let __ac3 = out.clone();
    bls377_Fp6_opp(&mut out, &__ac3);
}

#[inline]
pub fn bls377_Fp12_add_nocopy(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    bls377_Fp6_add(&mut out, &inx, &iny);
    bls377_Fp6_add(&mut out, &inx, &iny);
}

#[inline]
pub fn bls377_Fp12_sub_nocopy(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    bls377_Fp6_sub(&mut out, &inx, &iny);
    bls377_Fp6_sub(&mut out, &inx, &iny);
}

#[inline]
pub fn bls377_Fp12_mul_nocopy(mut out: &mut Fp, inx: &Fp, iny: &Fp) {
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bls377_Fp6_mul(&mut v0.c0.c0, &inx, &iny);
    bls377_Fp6_mul(&mut v1.c0.c0, &inx, &iny);
    bls377_Fp6_add(&mut t.c0.c0, &inx, &inx);
    bls377_Fp6_add(&mut u.c0.c0, &iny, &iny);
    let __ac0 = t.c0.c0.clone();
    bls377_Fp6_mul(&mut t.c0.c0, &__ac0, &u.c0.c0);
    bls377_Fp6_mul_by_v(&mut u.c0.c0, &v1.c0.c0);
    bls377_Fp6_add(&mut out, &v0.c0.c0, &u.c0.c0);
    let __ac1 = t.c0.c0.clone();
    bls377_Fp6_sub(&mut t.c0.c0, &__ac1, &v0.c0.c0);
    bls377_Fp6_sub(&mut out, &t.c0.c0, &v1.c0.c0);
}

#[inline]
pub fn bls377_Fp2_conjugate(mut out: &mut Fp, x: &Fp) {
    bls377_felem_copy(&mut out, &x);
    bls377_opp(&mut out, &x);
}

#[inline]
pub fn bls377_Fp6_mul_fp2(mut out: &mut Fp, x: &Fp, s: &Fp) {
    let mut s_copy: Fp2 = Fp2::zero();
    bls377_Fp2_felem_copy(&mut s_copy.c0, &s);
    bls377_Fp2_mul(&mut out, &x, &s_copy.c0);
    bls377_Fp2_mul(&mut out, &x, &s_copy.c0);
    bls377_Fp2_mul(&mut out, &x, &s_copy.c0);
}

#[inline]
pub fn bls377_Fp6_frobenius(mut out: &mut Fp, x: &Fp, gamma1: &Fp, gamma2: &Fp) {
    let mut tmp: Fp6 = Fp6::zero();
    bls377_Fp2_conjugate(&mut tmp.c0.c0, &x);
    bls377_Fp2_conjugate(&mut tmp.c1.c0, &x);
    bls377_Fp2_conjugate(&mut tmp.c2.c0, &x);
    bls377_Fp2_felem_copy(&mut out, &tmp.c0.c0);
    bls377_Fp2_mul(&mut out, &tmp.c1.c0, &gamma1);
    bls377_Fp2_mul(&mut out, &tmp.c2.c0, &gamma2);
}

#[inline]
pub fn bls377_Fp6_frobenius_p2(mut out: &mut Fp, x: &Fp, gamma1_p2: &Fp, gamma2_p2: &Fp) {
    bls377_Fp2_felem_copy(&mut out, &x);
    bls377_Fp2_mul(&mut out, &x, &gamma1_p2);
    bls377_Fp2_mul(&mut out, &x, &gamma2_p2);
}

#[inline]
pub fn bls377_Fp12_frobenius(mut out: &mut Fp, x: &Fp, gamma1: &Fp, gamma2: &Fp, w_frob_c1: &Fp) {
    bls377_Fp6_frobenius(&mut out, &x, &gamma1, &gamma2);
    bls377_Fp6_frobenius(&mut out, &x, &gamma1, &gamma2);
    let __ac0 = out.clone();
    bls377_Fp6_mul_fp2(&mut out, &__ac0, &w_frob_c1);
}

#[inline]
pub fn bls377_Fp12_frobenius_p2(mut out: &mut Fp, x: &Fp, gamma1_p2: &Fp, gamma2_p2: &Fp, w_frob_p2_c1: &Fp) {
    bls377_Fp6_frobenius_p2(&mut out, &x, &gamma1_p2, &gamma2_p2);
    bls377_Fp6_frobenius_p2(&mut out, &x, &gamma1_p2, &gamma2_p2);
    let __ac0 = out.clone();
    bls377_Fp6_mul_fp2(&mut out, &__ac0, &w_frob_p2_c1);
}

#[inline]
pub fn bls377_Fp12_frobenius_p3(mut out: &mut Fp, x: &Fp, gamma1: &Fp, gamma2: &Fp, gamma1_p2: &Fp, gamma2_p2: &Fp, w_frob_c1: &Fp, w_frob_p2_c1: &Fp) {
    let mut tmp: Fp12 = Fp12::zero();
    bls377_Fp6_frobenius_p2(&mut tmp.c0.c0.c0, &x, &gamma1_p2, &gamma2_p2);
    bls377_Fp6_frobenius_p2(&mut tmp.c1.c0.c0, &x, &gamma1_p2, &gamma2_p2);
    let __ac0 = tmp.c1.c0.c0.clone();
    bls377_Fp6_mul_fp2(&mut tmp.c1.c0.c0, &__ac0, &w_frob_p2_c1);
    bls377_Fp6_frobenius(&mut out, &tmp.c0.c0.c0, &gamma1, &gamma2);
    bls377_Fp6_frobenius(&mut out, &tmp.c1.c0.c0, &gamma1, &gamma2);
    let __ac1 = out.clone();
    bls377_Fp6_mul_fp2(&mut out, &__ac1, &w_frob_c1);
}

#[inline]
pub fn bls377_Fp2_mul_fp(mut out: &mut Fp, x: &Fp, s: &Fp) {
    bls377_mul(&mut out, &x, &s);
    bls377_mul(&mut out, &x, &s);
}

#[inline]
pub fn bls377_make_line(mut out: &mut Fp, lam: &Fp, x_t: &Fp, y_t: &Fp, x_p: &Fp, y_p: &Fp) {
    let mut tmp: Fp2 = Fp2::zero();
    bls377_Fp2_mul(&mut out, &lam, &x_t);
    let __ac0 = out.clone();
    bls377_Fp2_sub(&mut out, &__ac0, &y_t);
    bls377_Fp2_mul_fp(&mut tmp.c0, &lam, &x_p);
    bls377_Fp2_opp(&mut out, &tmp.c0);
    bls377_from_word(&mut out, 0u64);
    bls377_from_word(&mut out, 0u64);
    bls377_from_word(&mut out, 0u64);
    bls377_from_word(&mut out, 0u64);
    bls377_felem_copy(&mut out, &y_p);
    bls377_from_word(&mut out, 0u64);
    bls377_from_word(&mut out, 0u64);
    bls377_from_word(&mut out, 0u64);
}

#[inline]
pub fn bls377_load_gamma1_p2(mut out: &mut Fp) {
    out.0[0] = 15766275933608376691u64;
    out.0[1] = 15635974902606112666u64;
    out.0[2] = 1934946774703877852u64;
    out.0[3] = 18129354943882397960u64;
    out.0[4] = 15437979634065614942u64;
    out.0[5] = 101285514078273488u64;
    out.0[0] = 0u64;
    out.0[1] = 0u64;
    out.0[2] = 0u64;
    out.0[3] = 0u64;
    out.0[4] = 0u64;
    out.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_gamma2_p2(mut out: &mut Fp) {
    out.0[0] = 3203870859294639911u64;
    out.0[1] = 276961138506029237u64;
    out.0[2] = 9479726329337356593u64;
    out.0[3] = 13645541738420943632u64;
    out.0[4] = 7584832609311778094u64;
    out.0[5] = 101110569012358506u64;
    out.0[0] = 0u64;
    out.0[1] = 0u64;
    out.0[2] = 0u64;
    out.0[3] = 0u64;
    out.0[4] = 0u64;
    out.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_w_frob_p2_c1(mut out: &mut Fp) {
    out.0[0] = 6382252053795993818u64;
    out.0[1] = 1383562296554596171u64;
    out.0[2] = 11197251941974877903u64;
    out.0[3] = 6684509567199238270u64;
    out.0[4] = 6699184357838251020u64;
    out.0[5] = 19987743694136192u64;
    out.0[0] = 0u64;
    out.0[1] = 0u64;
    out.0[2] = 0u64;
    out.0[3] = 0u64;
    out.0[4] = 0u64;
    out.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_gamma1(mut out: &mut Fp) {
    out.0[0] = 6382252053795993818u64;
    out.0[1] = 1383562296554596171u64;
    out.0[2] = 11197251941974877903u64;
    out.0[3] = 6684509567199238270u64;
    out.0[4] = 6699184357838251020u64;
    out.0[5] = 19987743694136192u64;
    out.0[0] = 0u64;
    out.0[1] = 0u64;
    out.0[2] = 0u64;
    out.0[3] = 0u64;
    out.0[4] = 0u64;
    out.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_gamma2(mut out: &mut Fp) {
    out.0[0] = 15766275933608376691u64;
    out.0[1] = 15635974902606112666u64;
    out.0[2] = 1934946774703877852u64;
    out.0[3] = 18129354943882397960u64;
    out.0[4] = 15437979634065614942u64;
    out.0[5] = 101285514078273488u64;
    out.0[0] = 0u64;
    out.0[1] = 0u64;
    out.0[2] = 0u64;
    out.0[3] = 0u64;
    out.0[4] = 0u64;
    out.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_w_frob_c1(mut out: &mut Fp) {
    out.0[0] = 7981638599956744862u64;
    out.0[1] = 11830407261614897732u64;
    out.0[2] = 6308788297503259939u64;
    out.0[3] = 10596665404780565693u64;
    out.0[4] = 11693741422477421038u64;
    out.0[5] = 61545186993886319u64;
    out.0[0] = 0u64;
    out.0[1] = 0u64;
    out.0[2] = 0u64;
    out.0[3] = 0u64;
    out.0[4] = 0u64;
    out.0[5] = 0u64;
}

#[inline]
pub fn bls377_Fp12_pow_u(mut out: &mut Fp, base: &Fp) {
    let mut result: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut result.c0.c0.c0, &base);
    let mut i: u64;
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let __ac0 = result.c0.c0.c0.clone();
        bls377_Fp12_square(&mut result.c0.c0.c0, &__ac0);
        let mut bit: u64;
        bit = ((9586122913090633729u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac1 = result.c0.c0.c0.clone();
            bls377_Fp12_mul(&mut result.c0.c0.c0, &__ac1, &base);
        } else {
        }
    }
    bls377_Fp12_felem_copy(&mut out, &result.c0.c0.c0);
}

#[inline]
pub fn bls377_final_exp_hard_dsd(mut out: &mut Fp, f: &Fp) {
    let mut t0: Fp12 = Fp12::zero();
    let mut t1: Fp12 = Fp12::zero();
    let mut t2: Fp12 = Fp12::zero();
    let mut t3: Fp12 = Fp12::zero();
    let mut gamma1: Fp2 = Fp2::zero();
    let mut gamma2: Fp2 = Fp2::zero();
    let mut w_frob_c1: Fp2 = Fp2::zero();
    bls377_load_gamma1(&mut gamma1.c0, );
    bls377_load_gamma2(&mut gamma2.c0, );
    bls377_load_w_frob_c1(&mut w_frob_c1.c0, );
    bls377_Fp12_pow_u(&mut t0.c0.c0.c0, &f);
    bls377_Fp12_square(&mut t1.c0.c0.c0, &t0.c0.c0.c0);
    bls377_Fp12_pow_u(&mut t2.c0.c0.c0, &t0.c0.c0.c0);
    bls377_Fp12_square(&mut t3.c0.c0.c0, &t2.c0.c0.c0);
    let __ac0 = t1.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut t1.c0.c0.c0, &__ac0, &t2.c0.c0.c0);
    let __ac1 = t2.c0.c0.c0.clone();
    bls377_Fp12_pow_u(&mut t2.c0.c0.c0, &__ac1);
    let __ac2 = t1.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut t1.c0.c0.c0, &__ac2, &t2.c0.c0.c0);
    let __ac3 = t1.c0.c0.c0.clone();
    bls377_Fp12_conjugate(&mut t1.c0.c0.c0, &__ac3);
    let __ac4 = t1.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut t1.c0.c0.c0, &__ac4, &f);
    let __ac5 = t1.c0.c0.c0.clone();
    bls377_Fp12_conjugate(&mut t1.c0.c0.c0, &__ac5);
    bls377_Fp12_conjugate(&mut t0.c0.c0.c0, &f);
    let __ac6 = t1.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut t1.c0.c0.c0, &__ac6, &t0.c0.c0.c0);
    let __ac7 = t2.c0.c0.c0.clone();
    bls377_Fp12_pow_u(&mut t2.c0.c0.c0, &__ac7);
    bls377_Fp12_mul(&mut t0.c0.c0.c0, &t2.c0.c0.c0, &t3.c0.c0.c0);
    let __ac8 = t0.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut t0.c0.c0.c0, &__ac8, &t1.c0.c0.c0);
    bls377_Fp12_frobenius(&mut t1.c0.c0.c0, &f, &gamma1.c0, &gamma2.c0, &w_frob_c1.c0);
    bls377_Fp12_frobenius(&mut t2.c0.c0.c0, &t1.c0.c0.c0, &gamma1.c0, &gamma2.c0, &w_frob_c1.c0);
    bls377_Fp12_frobenius(&mut t3.c0.c0.c0, &t2.c0.c0.c0, &gamma1.c0, &gamma2.c0, &w_frob_c1.c0);
    let __ac9 = t0.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut t0.c0.c0.c0, &__ac9, &t1.c0.c0.c0);
    let __ac10 = t0.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut t0.c0.c0.c0, &__ac10, &t2.c0.c0.c0);
    let __ac11 = t0.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut t0.c0.c0.c0, &__ac11, &t3.c0.c0.c0);
    bls377_Fp12_felem_copy(&mut out, &t0.c0.c0.c0);
}

#[inline]
pub fn bls377_final_exp_dsd(mut out: &mut Fp, f: &Fp, gamma1_p2: &Fp, gamma2_p2: &Fp, w_frob_p2_c1: &Fp) {
    let mut result: Fp12 = Fp12::zero();
    let mut tmp: Fp12 = Fp12::zero();
    bls377_Fp12_conjugate(&mut result.c0.c0.c0, &f);
    bls377_Fp12_inv(&mut tmp.c0.c0.c0, &f);
    let __ac0 = result.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut result.c0.c0.c0, &__ac0, &tmp.c0.c0.c0);
    bls377_Fp12_frobenius_p2(&mut tmp.c0.c0.c0, &result.c0.c0.c0, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
    let __ac1 = result.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut result.c0.c0.c0, &tmp.c0.c0.c0, &__ac1);
    bls377_final_exp_hard_dsd(&mut out, &result.c0.c0.c0);
}

#[inline]
pub fn bls377_miller_loop(mut out: &mut Fp, p_x: &Fp, p_y: &Fp, q_x: &Fp, q_y: &Fp) {
    let mut f: Fp12 = Fp12::zero();
    let mut t_x: Fp2 = Fp2::zero();
    let mut t_y: Fp2 = Fp2::zero();
    let mut lambda: Fp2 = Fp2::zero();
    let mut tmp1: Fp2 = Fp2::zero();
    let mut tmp2: Fp2 = Fp2::zero();
    let mut line: Fp12 = Fp12::zero();
    let mut u6p2: Fp = Fp::zero();
    bls377_from_word(&mut f.c0.c0.c0, 1u64);
    bls377_from_word(&mut f.c0.c0.c1, 0u64);
    bls377_from_word(&mut f.c0.c1.c0, 0u64);
    bls377_from_word(&mut f.c0.c1.c1, 0u64);
    bls377_from_word(&mut f.c0.c2.c0, 0u64);
    bls377_from_word(&mut f.c0.c2.c1, 0u64);
    bls377_from_word(&mut f.c1.c0.c0, 0u64);
    bls377_from_word(&mut f.c1.c0.c1, 0u64);
    bls377_from_word(&mut f.c1.c1.c0, 0u64);
    bls377_from_word(&mut f.c1.c1.c1, 0u64);
    bls377_from_word(&mut f.c1.c2.c0, 0u64);
    bls377_from_word(&mut f.c1.c2.c1, 0u64);
    bls377_Fp2_felem_copy(&mut t_x.c0, &q_x);
    bls377_Fp2_felem_copy(&mut t_y.c0, &q_y);
    u6p2.0[0] = 2176505257415147528u64;
    u6p2.0[1] = 3u64;
    let mut i: u64;
    i = 65u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let mut word: u64;
        word = unsafe { *((u6p2.0.as_ptr() as *const u8).wrapping_add(((i >> (6u64 & 63)) << (3u64 & 63)) as usize) as *const u64) };
        let mut bit: u64;
        bit = ((word >> ((i & 63u64) & 63)) & 1u64);
        bls377_Fp2_square(&mut tmp1.c0, &t_x.c0);
        bls377_Fp2_add(&mut lambda.c0, &tmp1.c0, &tmp1.c0);
        let __ac0 = lambda.c0.clone();
        bls377_Fp2_add(&mut lambda.c0, &__ac0, &tmp1.c0);
        bls377_Fp2_add(&mut tmp1.c0, &t_y.c0, &t_y.c0);
        let __ac1 = tmp1.c0.clone();
        bls377_Fp2_inv(&mut tmp1.c0, &__ac1);
        let __ac2 = lambda.c0.clone();
        bls377_Fp2_mul(&mut lambda.c0, &__ac2, &tmp1.c0);
        bls377_make_line(&mut line.c0.c0.c0, &lambda.c0, &t_x.c0, &t_y.c0, &p_x, &p_y);
        let __ac3 = f.c0.c0.c0.clone();
        bls377_Fp12_square(&mut f.c0.c0.c0, &__ac3);
        let __ac4 = f.c0.c0.c0.clone();
        bls377_Fp12_mul(&mut f.c0.c0.c0, &__ac4, &line.c0.c0.c0);
        bls377_Fp2_square(&mut tmp1.c0, &lambda.c0);
        let __ac5 = tmp1.c0.clone();
        bls377_Fp2_sub(&mut tmp1.c0, &__ac5, &t_x.c0);
        bls377_Fp2_sub(&mut tmp2.c0, &tmp1.c0, &t_x.c0);
        bls377_Fp2_sub(&mut tmp1.c0, &t_x.c0, &tmp2.c0);
        let __ac6 = tmp1.c0.clone();
        bls377_Fp2_mul(&mut tmp1.c0, &lambda.c0, &__ac6);
        let __ac7 = t_y.c0.clone();
        bls377_Fp2_sub(&mut t_y.c0, &tmp1.c0, &__ac7);
        bls377_Fp2_felem_copy(&mut t_x.c0, &tmp2.c0);
        if bit != 0 {
            bls377_Fp2_sub(&mut tmp1.c0, &q_y, &t_y.c0);
            bls377_Fp2_sub(&mut tmp2.c0, &q_x, &t_x.c0);
            let __ac8 = tmp2.c0.clone();
            bls377_Fp2_inv(&mut tmp2.c0, &__ac8);
            bls377_Fp2_mul(&mut lambda.c0, &tmp1.c0, &tmp2.c0);
            bls377_make_line(&mut line.c0.c0.c0, &lambda.c0, &t_x.c0, &t_y.c0, &p_x, &p_y);
            let __ac9 = f.c0.c0.c0.clone();
            bls377_Fp12_mul(&mut f.c0.c0.c0, &__ac9, &line.c0.c0.c0);
            bls377_Fp2_square(&mut tmp1.c0, &lambda.c0);
            let __ac10 = tmp1.c0.clone();
            bls377_Fp2_sub(&mut tmp1.c0, &__ac10, &t_x.c0);
            bls377_Fp2_sub(&mut tmp2.c0, &tmp1.c0, &q_x);
            bls377_Fp2_sub(&mut tmp1.c0, &t_x.c0, &tmp2.c0);
            let __ac11 = tmp1.c0.clone();
            bls377_Fp2_mul(&mut tmp1.c0, &lambda.c0, &__ac11);
            let __ac12 = t_y.c0.clone();
            bls377_Fp2_sub(&mut t_y.c0, &tmp1.c0, &__ac12);
            bls377_Fp2_felem_copy(&mut t_x.c0, &tmp2.c0);
        } else {
        }
    }
    bls377_Fp12_felem_copy(&mut out, &f.c0.c0.c0);
}

#[inline]
pub fn bls377_final_exp(mut out: &mut Fp, f: &Fp, gamma1_p2: &Fp, gamma2_p2: &Fp, w_frob_p2_c1: &Fp) {
    let mut result: Fp12 = Fp12::zero();
    let mut tmp: Fp12 = Fp12::zero();
    let mut base: Fp12 = Fp12::zero();
    let mut h3: Fp = Fp::zero();
    bls377_Fp12_conjugate(&mut result.c0.c0.c0, &f);
    bls377_Fp12_inv(&mut tmp.c0.c0.c0, &f);
    let __ac0 = result.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut result.c0.c0.c0, &__ac0, &tmp.c0.c0.c0);
    bls377_Fp12_frobenius_p2(&mut tmp.c0.c0.c0, &result.c0.c0.c0, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
    let __ac1 = result.c0.c0.c0.clone();
    bls377_Fp12_mul(&mut result.c0.c0.c0, &tmp.c0.c0.c0, &__ac1);
    bls377_Fp12_felem_copy(&mut base.c0.c0.c0, &result.c0.c0.c0);
    bls377_from_word(&mut result.c0.c0.c0, 1u64);
    bls377_from_word(&mut result.c0.c0.c1, 0u64);
    bls377_from_word(&mut result.c0.c1.c0, 0u64);
    bls377_from_word(&mut result.c0.c1.c1, 0u64);
    bls377_from_word(&mut result.c0.c2.c0, 0u64);
    bls377_from_word(&mut result.c0.c2.c1, 0u64);
    bls377_from_word(&mut result.c1.c0.c0, 0u64);
    bls377_from_word(&mut result.c1.c0.c1, 0u64);
    bls377_from_word(&mut result.c1.c1.c0, 0u64);
    bls377_from_word(&mut result.c1.c1.c1, 0u64);
    bls377_from_word(&mut result.c1.c2.c0, 0u64);
    bls377_from_word(&mut result.c1.c2.c1, 0u64);
    h3.0[0] = 1u64;
    h3.0[1] = 3321046870121250816u64;
    h3.0[2] = 7548291286117017600u64;
    h3.0[3] = 8186281107583682183u64;
    h3.0[4] = 17651462139244771879u64;
    h3.0[5] = 2872328226190507877u64;
    h3.0[0] = 12378977276395846840u64;
    h3.0[1] = 853793688127832707u64;
    h3.0[2] = 12312934968565134075u64;
    h3.0[3] = 15127306964635196250u64;
    h3.0[4] = 18217557446542555314u64;
    h3.0[5] = 1913335603792453653u64;
    h3.0[0] = 6095526954025429393u64;
    h3.0[1] = 14728438370357709444u64;
    h3.0[2] = 14215805567152534348u64;
    h3.0[3] = 13761185838313388837u64;
    h3.0[4] = 4269540699915789775u64;
    h3.0[5] = 393627973110973375u64;
    h3.0[0] = 537291578559286239u64;
    h3.0[1] = 469786051442u64;
    let mut started: u64;
    started = 0u64;
    let mut i: u64;
    i = 1280u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let mut word: u64;
        word = unsafe { *((h3.0.as_ptr() as *const u8).wrapping_add(((i >> (6u64 & 63)) << (3u64 & 63)) as usize) as *const u64) };
        let mut bit: u64;
        bit = ((word >> ((i & 63u64) & 63)) & 1u64);
        if started != 0 {
            let __ac2 = result.c0.c0.c0.clone();
            bls377_Fp12_square(&mut result.c0.c0.c0, &__ac2);
        } else {
        }
        if bit != 0 {
            if started != 0 {
                let __ac3 = result.c0.c0.c0.clone();
                bls377_Fp12_mul(&mut result.c0.c0.c0, &__ac3, &base.c0.c0.c0);
            } else {
                bls377_Fp12_felem_copy(&mut result.c0.c0.c0, &base.c0.c0.c0);
                started = 1u64;
            }
        } else {
        }
    }
    bls377_Fp12_felem_copy(&mut out, &result.c0.c0.c0);
}

#[inline]
pub fn bls377_pairing(mut out: &mut Fp, p_x: &Fp, p_y: &Fp, q_x: &Fp, q_y: &Fp) {
    let mut tmp: Fp12 = Fp12::zero();
    let mut gamma1_p2: Fp2 = Fp2::zero();
    let mut gamma2_p2: Fp2 = Fp2::zero();
    let mut w_frob_p2_c1: Fp2 = Fp2::zero();
    bls377_load_gamma1_p2(&mut gamma1_p2.c0, );
    bls377_load_gamma2_p2(&mut gamma2_p2.c0, );
    bls377_load_w_frob_p2_c1(&mut w_frob_p2_c1.c0, );
    bls377_miller_loop(&mut tmp.c0.c0.c0, &p_x, &p_y, &q_x, &q_y);
    bls377_final_exp(&mut out, &tmp.c0.c0.c0, &gamma1_p2.c0, &gamma2_p2.c0, &w_frob_p2_c1.c0);
}

#[inline]
pub fn bls377_pairing_dsd(mut out: &mut Fp, p_x: &Fp, p_y: &Fp, q_x: &Fp, q_y: &Fp) {
    let mut tmp: Fp12 = Fp12::zero();
    let mut gamma1_p2: Fp2 = Fp2::zero();
    let mut gamma2_p2: Fp2 = Fp2::zero();
    let mut w_frob_p2_c1: Fp2 = Fp2::zero();
    bls377_load_gamma1_p2(&mut gamma1_p2.c0, );
    bls377_load_gamma2_p2(&mut gamma2_p2.c0, );
    bls377_load_w_frob_p2_c1(&mut w_frob_p2_c1.c0, );
    bls377_miller_loop(&mut tmp.c0.c0.c0, &p_x, &p_y, &q_x, &q_y);
    bls377_final_exp_dsd(&mut out, &tmp.c0.c0.c0, &gamma1_p2.c0, &gamma2_p2.c0, &w_frob_p2_c1.c0);
}

