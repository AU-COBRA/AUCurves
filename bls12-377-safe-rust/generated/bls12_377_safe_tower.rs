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
pub fn bls377_Fp2_felem_copy(mut out: &mut Fp2, x: &Fp2) {
    bls377_felem_copy(&mut out.c0, &x.c0);
    bls377_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls377_Fp2_add(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    bls377_add(&mut out.c0, &inx.c0, &iny.c0);
    bls377_add(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bls377_Fp2_sub(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    bls377_sub(&mut out.c0, &inx.c0, &iny.c0);
    bls377_sub(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bls377_Fp2_mul(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    let mut v2: Fp = Fp::zero();
    bls377_mul(&mut v0, &inx.c0, &iny.c0);
    bls377_mul(&mut v1, &inx.c1, &iny.c1);
    bls377_add(&mut v2, &inx.c0, &inx.c1);
    bls377_add(&mut out.c1, &iny.c0, &iny.c1);
    let __ac0 = out.c1.clone();
    bls377_mul(&mut out.c1, &__ac0, &v2);
    let __ac1 = out.c1.clone();
    bls377_sub(&mut out.c1, &__ac1, &v0);
    let __ac2 = out.c1.clone();
    bls377_sub(&mut out.c1, &__ac2, &v1);
    bls377_add(&mut v2, &v1, &v1);
    let __ac3 = v2.clone();
    bls377_add(&mut v2, &__ac3, &__ac3);
    let __ac4 = v2.clone();
    bls377_add(&mut v2, &__ac4, &v1);
    bls377_sub(&mut out.c0, &v0, &v2);
}

#[inline]
pub fn bls377_Fp2_square(mut out: &mut Fp2, inx: &Fp2) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    bls377_square(&mut v0, &inx.c0);
    bls377_square(&mut v1, &inx.c1);
    bls377_mul(&mut out.c1, &inx.c0, &inx.c1);
    let __ac0 = out.c1.clone();
    bls377_add(&mut out.c1, &__ac0, &__ac0);
    bls377_add(&mut out.c0, &v1, &v1);
    let __ac1 = out.c0.clone();
    bls377_add(&mut out.c0, &__ac1, &__ac1);
    let __ac2 = out.c0.clone();
    bls377_add(&mut out.c0, &__ac2, &v1);
    let __ac3 = out.c0.clone();
    bls377_sub(&mut out.c0, &v0, &__ac3);
}

#[inline]
pub fn bls377_Fp2_inv(mut out: &mut Fp2, inx: &Fp2) {
    let mut asq: Fp = Fp::zero();
    let mut bsq: Fp = Fp::zero();
    let mut norm: Fp = Fp::zero();
    bls377_square(&mut asq, &inx.c0);
    bls377_square(&mut bsq, &inx.c1);
    bls377_add(&mut norm, &bsq, &bsq);
    let __ac0 = norm.clone();
    bls377_add(&mut norm, &__ac0, &__ac0);
    let __ac1 = norm.clone();
    bls377_add(&mut norm, &__ac1, &bsq);
    let __ac2 = norm.clone();
    bls377_add(&mut norm, &asq, &__ac2);
    let __ac3 = norm.clone();
    bls377_inv(&mut norm, &__ac3);
    bls377_mul(&mut out.c0, &inx.c0, &norm);
    bls377_sub(&mut asq, &bsq, &bsq);
    let __ac4 = asq.clone();
    bls377_sub(&mut asq, &__ac4, &inx.c1);
    bls377_mul(&mut out.c1, &asq, &norm);
}

#[inline]
pub fn bls377_Fp2_opp(mut out: &mut Fp2, x: &Fp2) {
    bls377_opp(&mut out.c0, &x.c0);
    bls377_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls377_Fp2_mul_xi(mut out: &mut Fp2, x: &Fp2) {
    bls377_add(&mut out.c0, &x.c1, &x.c1);
    let __ac0 = out.c0.clone();
    bls377_add(&mut out.c0, &__ac0, &__ac0);
    let __ac1 = out.c0.clone();
    bls377_add(&mut out.c0, &__ac1, &x.c1);
    bls377_felem_copy(&mut out.c1, &x.c0);
    let mut tmp: Fp = Fp::zero();
    let __ac2 = tmp.clone();
    bls377_sub(&mut tmp, &__ac2, &__ac2);
    let __ac3 = out.c0.clone();
    bls377_sub(&mut out.c0, &tmp, &__ac3);
}

#[inline]
pub fn bls377_Fp6_felem_copy(mut out: &mut Fp6, x: &Fp6) {
    bls377_Fp2_felem_copy(&mut out.c0, &x.c0);
    bls377_Fp2_felem_copy(&mut out.c1, &x.c1);
    bls377_Fp2_felem_copy(&mut out.c2, &x.c2);
}

#[inline]
pub fn bls377_Fp6_add(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bls377_Fp6_felem_copy(&mut allocx, &inx);
    bls377_Fp6_felem_copy(&mut allocy, &iny);
    bls377_Fp2_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bls377_Fp2_add(&mut out.c1, &allocx.c1, &allocy.c1);
    bls377_Fp2_add(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bls377_Fp6_sub(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bls377_Fp6_felem_copy(&mut allocx, &inx);
    bls377_Fp6_felem_copy(&mut allocy, &iny);
    bls377_Fp2_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bls377_Fp2_sub(&mut out.c1, &allocx.c1, &allocy.c1);
    bls377_Fp2_sub(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bls377_Fp6_opp(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    bls377_Fp6_felem_copy(&mut allocx, &x);
    bls377_Fp2_opp(&mut out.c0, &allocx.c0);
    bls377_Fp2_opp(&mut out.c1, &allocx.c1);
    bls377_Fp2_opp(&mut out.c2, &allocx.c2);
}

#[inline]
pub fn bls377_Fp6_mul(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    let mut a0b0: Fp2 = Fp2::zero();
    let mut a1b1: Fp2 = Fp2::zero();
    let mut a2b2: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    let mut u: Fp2 = Fp2::zero();
    bls377_Fp6_felem_copy(&mut allocx, &inx);
    bls377_Fp6_felem_copy(&mut allocy, &iny);
    bls377_Fp2_mul(&mut a0b0, &allocx.c0, &allocy.c0);
    bls377_Fp2_mul(&mut a1b1, &allocx.c1, &allocy.c1);
    bls377_Fp2_mul(&mut a2b2, &allocx.c2, &allocy.c2);
    bls377_Fp2_add(&mut t, &allocx.c1, &allocx.c2);
    bls377_Fp2_add(&mut u, &allocy.c1, &allocy.c2);
    let __ac0 = t.clone();
    bls377_Fp2_mul(&mut t, &__ac0, &u);
    let __ac1 = t.clone();
    bls377_Fp2_sub(&mut t, &__ac1, &a1b1);
    let __ac2 = t.clone();
    bls377_Fp2_sub(&mut t, &__ac2, &a2b2);
    let __ac3 = t.clone();
    bls377_Fp2_mul_xi(&mut t, &__ac3);
    bls377_Fp2_add(&mut out.c0, &a0b0, &t);
    bls377_Fp2_add(&mut t, &allocx.c0, &allocx.c1);
    bls377_Fp2_add(&mut u, &allocy.c0, &allocy.c1);
    let __ac4 = t.clone();
    bls377_Fp2_mul(&mut t, &__ac4, &u);
    let __ac5 = t.clone();
    bls377_Fp2_sub(&mut t, &__ac5, &a0b0);
    let __ac6 = t.clone();
    bls377_Fp2_sub(&mut t, &__ac6, &a1b1);
    bls377_Fp2_mul_xi(&mut u, &a2b2);
    bls377_Fp2_add(&mut out.c1, &t, &u);
    bls377_Fp2_add(&mut t, &allocx.c0, &allocx.c2);
    bls377_Fp2_add(&mut u, &allocy.c0, &allocy.c2);
    let __ac7 = t.clone();
    bls377_Fp2_mul(&mut t, &__ac7, &u);
    let __ac8 = t.clone();
    bls377_Fp2_sub(&mut t, &__ac8, &a0b0);
    let __ac9 = t.clone();
    bls377_Fp2_sub(&mut t, &__ac9, &a2b2);
    bls377_Fp2_add(&mut out.c2, &t, &a1b1);
}

#[inline]
pub fn bls377_Fp6_square(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut s0: Fp2 = Fp2::zero();
    let mut s1: Fp2 = Fp2::zero();
    let mut s2: Fp2 = Fp2::zero();
    let mut s3: Fp2 = Fp2::zero();
    let mut s4: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    bls377_Fp6_felem_copy(&mut allocx, &x);
    bls377_Fp2_square(&mut s0, &allocx.c0);
    bls377_Fp2_mul(&mut t, &allocx.c0, &allocx.c1);
    bls377_Fp2_add(&mut s1, &t, &t);
    bls377_Fp2_sub(&mut t, &allocx.c0, &allocx.c1);
    let __ac0 = t.clone();
    bls377_Fp2_add(&mut t, &__ac0, &allocx.c2);
    bls377_Fp2_square(&mut s2, &t);
    bls377_Fp2_mul(&mut t, &allocx.c1, &allocx.c2);
    bls377_Fp2_add(&mut s3, &t, &t);
    bls377_Fp2_square(&mut s4, &allocx.c2);
    bls377_Fp2_mul_xi(&mut t, &s3);
    bls377_Fp2_add(&mut out.c0, &s0, &t);
    bls377_Fp2_mul_xi(&mut t, &s4);
    bls377_Fp2_add(&mut out.c1, &s1, &t);
    bls377_Fp2_add(&mut t, &s1, &s2);
    let __ac1 = t.clone();
    bls377_Fp2_add(&mut t, &__ac1, &s3);
    let __ac2 = t.clone();
    bls377_Fp2_sub(&mut t, &__ac2, &s0);
    bls377_Fp2_sub(&mut out.c2, &t, &s4);
}

#[inline]
pub fn bls377_Fp6_inv(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut vA: Fp2 = Fp2::zero();
    let mut vB: Fp2 = Fp2::zero();
    let mut vC: Fp2 = Fp2::zero();
    let mut t1: Fp2 = Fp2::zero();
    let mut t2: Fp2 = Fp2::zero();
    let mut t3: Fp2 = Fp2::zero();
    bls377_Fp6_felem_copy(&mut allocx, &x);
    bls377_Fp2_square(&mut t1, &allocx.c0);
    bls377_Fp2_mul(&mut t2, &allocx.c1, &allocx.c2);
    bls377_Fp2_mul_xi(&mut t3, &t2);
    bls377_Fp2_sub(&mut vA, &t1, &t3);
    bls377_Fp2_square(&mut t1, &allocx.c2);
    bls377_Fp2_mul_xi(&mut t3, &t1);
    bls377_Fp2_mul(&mut t2, &allocx.c0, &allocx.c1);
    bls377_Fp2_sub(&mut vB, &t3, &t2);
    bls377_Fp2_square(&mut t1, &allocx.c1);
    bls377_Fp2_mul(&mut t2, &allocx.c0, &allocx.c2);
    bls377_Fp2_sub(&mut vC, &t1, &t2);
    bls377_Fp2_mul(&mut t1, &allocx.c0, &vA);
    bls377_Fp2_mul(&mut t2, &allocx.c2, &vB);
    bls377_Fp2_mul(&mut t3, &allocx.c1, &vC);
    let __ac0 = t2.clone();
    bls377_Fp2_add(&mut t2, &__ac0, &t3);
    let __ac1 = t2.clone();
    bls377_Fp2_mul_xi(&mut t2, &__ac1);
    let __ac2 = t1.clone();
    bls377_Fp2_add(&mut t1, &__ac2, &t2);
    let __ac3 = t1.clone();
    bls377_Fp2_inv(&mut t1, &__ac3);
    bls377_Fp2_mul(&mut out.c0, &vA, &t1);
    bls377_Fp2_mul(&mut out.c1, &vB, &t1);
    bls377_Fp2_mul(&mut out.c2, &vC, &t1);
}

#[inline]
pub fn bls377_Fp6_add_nocopy(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    bls377_Fp2_add(&mut out.c0, &inx.c0, &iny.c0);
    bls377_Fp2_add(&mut out.c1, &inx.c1, &iny.c1);
    bls377_Fp2_add(&mut out.c2, &inx.c2, &iny.c2);
}

#[inline]
pub fn bls377_Fp6_sub_nocopy(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    bls377_Fp2_sub(&mut out.c0, &inx.c0, &iny.c0);
    bls377_Fp2_sub(&mut out.c1, &inx.c1, &iny.c1);
    bls377_Fp2_sub(&mut out.c2, &inx.c2, &iny.c2);
}

#[inline]
pub fn bls377_Fp6_mul_by_v(mut out: &mut Fp6, x: &Fp6) {
    let mut tmp: Fp6 = Fp6::zero();
    bls377_Fp6_felem_copy(&mut tmp, &x);
    bls377_Fp2_mul_xi(&mut out.c0, &tmp.c2);
    bls377_Fp2_felem_copy(&mut out.c1, &tmp.c0);
    bls377_Fp2_felem_copy(&mut out.c2, &tmp.c1);
}

#[inline]
pub fn bls377_Fp12_felem_copy(mut out: &mut Fp12, x: &Fp12) {
    bls377_Fp6_felem_copy(&mut out.c0, &x.c0);
    bls377_Fp6_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls377_Fp12_add(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut ax, &inx);
    bls377_Fp12_felem_copy(&mut ay, &iny);
    bls377_Fp6_add_nocopy(&mut out.c0, &ax.c0, &ay.c0);
    bls377_Fp6_add_nocopy(&mut out.c1, &ax.c1, &ay.c1);
}

#[inline]
pub fn bls377_Fp12_sub(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut ax, &inx);
    bls377_Fp12_felem_copy(&mut ay, &iny);
    bls377_Fp6_sub_nocopy(&mut out.c0, &ax.c0, &ay.c0);
    bls377_Fp6_sub_nocopy(&mut out.c1, &ax.c1, &ay.c1);
}

#[inline]
pub fn bls377_Fp12_opp(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut allocx, &x);
    bls377_Fp6_opp(&mut out.c0, &allocx.c0);
    bls377_Fp6_opp(&mut out.c1, &allocx.c1);
}

#[inline]
pub fn bls377_Fp12_conjugate(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut allocx, &x);
    bls377_Fp6_felem_copy(&mut out.c0, &allocx.c0);
    bls377_Fp6_opp(&mut out.c1, &allocx.c1);
}

#[inline]
pub fn bls377_Fp12_mul(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut ax, &inx);
    bls377_Fp12_felem_copy(&mut ay, &iny);
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bls377_Fp6_mul(&mut v0, &ax.c0, &ay.c0);
    bls377_Fp6_mul(&mut v1, &ax.c1, &ay.c1);
    bls377_Fp6_add_nocopy(&mut t, &ax.c0, &ax.c1);
    bls377_Fp6_add_nocopy(&mut u, &ay.c0, &ay.c1);
    let __ac0 = t.clone();
    bls377_Fp6_mul(&mut t, &__ac0, &u);
    bls377_Fp6_mul_by_v(&mut u, &v1);
    bls377_Fp6_add_nocopy(&mut out.c0, &v0, &u);
    let __ac1 = t.clone();
    bls377_Fp6_sub_nocopy(&mut t, &__ac1, &v0);
    bls377_Fp6_sub_nocopy(&mut out.c1, &t, &v1);
}

#[inline]
pub fn bls377_Fp12_square(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut allocx, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    let mut t2: Fp6 = Fp6::zero();
    bls377_Fp6_square(&mut t0, &allocx.c0);
    bls377_Fp6_square(&mut t1, &allocx.c1);
    bls377_Fp6_mul(&mut t2, &allocx.c0, &allocx.c1);
    let __ac0 = t1.clone();
    bls377_Fp6_mul_by_v(&mut t1, &__ac0);
    bls377_Fp6_add_nocopy(&mut out.c0, &t0, &t1);
    bls377_Fp6_add_nocopy(&mut out.c1, &t2, &t2);
}

#[inline]
pub fn bls377_Fp12_inv(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut allocx, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    bls377_Fp6_square(&mut t0, &allocx.c0);
    bls377_Fp6_square(&mut t1, &allocx.c1);
    let __ac0 = t1.clone();
    bls377_Fp6_mul_by_v(&mut t1, &__ac0);
    let __ac1 = t0.clone();
    bls377_Fp6_sub_nocopy(&mut t0, &__ac1, &t1);
    let __ac2 = t0.clone();
    bls377_Fp6_inv(&mut t0, &__ac2);
    bls377_Fp6_mul(&mut out.c0, &allocx.c0, &t0);
    bls377_Fp6_mul(&mut out.c1, &allocx.c1, &t0);
    let __ac3 = out.c1.clone();
    bls377_Fp6_opp(&mut out.c1, &__ac3);
}

#[inline]
pub fn bls377_Fp12_add_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    bls377_Fp6_add_nocopy(&mut out.c0, &inx.c0, &iny.c0);
    bls377_Fp6_add_nocopy(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bls377_Fp12_sub_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    bls377_Fp6_sub_nocopy(&mut out.c0, &inx.c0, &iny.c0);
    bls377_Fp6_sub_nocopy(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bls377_Fp12_mul_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bls377_Fp6_mul(&mut v0, &inx.c0, &iny.c0);
    bls377_Fp6_mul(&mut v1, &inx.c1, &iny.c1);
    bls377_Fp6_add_nocopy(&mut t, &inx.c0, &inx.c1);
    bls377_Fp6_add_nocopy(&mut u, &iny.c0, &iny.c1);
    let __ac0 = t.clone();
    bls377_Fp6_mul(&mut t, &__ac0, &u);
    bls377_Fp6_mul_by_v(&mut u, &v1);
    bls377_Fp6_add_nocopy(&mut out.c0, &v0, &u);
    let __ac1 = t.clone();
    bls377_Fp6_sub_nocopy(&mut t, &__ac1, &v0);
    bls377_Fp6_sub_nocopy(&mut out.c1, &t, &v1);
}

#[inline]
pub fn bls377_Fp2_conjugate(mut out: &mut Fp2, x: &Fp2) {
    bls377_felem_copy(&mut out.c0, &x.c0);
    bls377_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls377_Fp6_mul_fp2(mut out: &mut Fp6, x: &Fp6, s: &Fp2) {
    let mut s_copy: Fp2 = Fp2::zero();
    bls377_Fp2_felem_copy(&mut s_copy, &s);
    bls377_Fp2_mul(&mut out.c0, &x.c0, &s_copy);
    bls377_Fp2_mul(&mut out.c1, &x.c1, &s_copy);
    bls377_Fp2_mul(&mut out.c2, &x.c2, &s_copy);
}

#[inline]
pub fn bls377_Fp6_frobenius(mut out: &mut Fp6, x: &Fp6, gamma1: &Fp2, gamma2: &Fp2) {
    let mut tmp: Fp6 = Fp6::zero();
    bls377_Fp2_conjugate(&mut tmp.c0, &x.c0);
    bls377_Fp2_conjugate(&mut tmp.c1, &x.c1);
    bls377_Fp2_conjugate(&mut tmp.c2, &x.c2);
    bls377_Fp2_felem_copy(&mut out.c0, &tmp.c0);
    bls377_Fp2_mul(&mut out.c1, &tmp.c1, &gamma1);
    bls377_Fp2_mul(&mut out.c2, &tmp.c2, &gamma2);
}

#[inline]
pub fn bls377_Fp6_frobenius_p2(mut out: &mut Fp6, x: &Fp6, gamma1_p2: &Fp2, gamma2_p2: &Fp2) {
    bls377_Fp2_felem_copy(&mut out.c0, &x.c0);
    bls377_Fp2_mul(&mut out.c1, &x.c1, &gamma1_p2);
    bls377_Fp2_mul(&mut out.c2, &x.c2, &gamma2_p2);
}

#[inline]
pub fn bls377_Fp12_frobenius(mut out: &mut Fp12, x: &Fp12, gamma1: &Fp2, gamma2: &Fp2, w_frob_c1: &Fp2) {
    bls377_Fp6_frobenius(&mut out.c0, &x.c0, &gamma1, &gamma2);
    bls377_Fp6_frobenius(&mut out.c1, &x.c1, &gamma1, &gamma2);
    let __ac0 = out.c1.clone();
    bls377_Fp6_mul_fp2(&mut out.c1, &__ac0, &w_frob_c1);
}

#[inline]
pub fn bls377_Fp12_frobenius_p2(mut out: &mut Fp12, x: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    bls377_Fp6_frobenius_p2(&mut out.c0, &x.c0, &gamma1_p2, &gamma2_p2);
    bls377_Fp6_frobenius_p2(&mut out.c1, &x.c1, &gamma1_p2, &gamma2_p2);
    let __ac0 = out.c1.clone();
    bls377_Fp6_mul_fp2(&mut out.c1, &__ac0, &w_frob_p2_c1);
}

#[inline]
pub fn bls377_Fp12_frobenius_p3(mut out: &mut Fp12, x: &Fp12, gamma1: &Fp12, gamma2: &Fp12, gamma1_p2: &Fp12, gamma2_p2: &Fp12, w_frob_c1: &Fp12, w_frob_p2_c1: &Fp12) {
    let mut tmp: Fp12 = Fp12::zero();
    bls377_Fp6_frobenius_p2(&mut tmp.c0, &x.c0, &gamma1_p2.c0.c0, &gamma2_p2.c0.c0);
    bls377_Fp6_frobenius_p2(&mut tmp.c1, &x.c1, &gamma1_p2.c0.c0, &gamma2_p2.c0.c0);
    let __ac0 = tmp.c1.clone();
    bls377_Fp6_mul_fp2(&mut tmp.c1, &__ac0, &w_frob_p2_c1.c0.c0);
    bls377_Fp6_frobenius(&mut out.c0, &tmp.c0, &gamma1.c0.c0, &gamma2.c0.c0);
    bls377_Fp6_frobenius(&mut out.c1, &tmp.c1, &gamma1.c0.c0, &gamma2.c0.c0);
    let __ac1 = out.c1.clone();
    bls377_Fp6_mul_fp2(&mut out.c1, &__ac1, &w_frob_c1.c0.c0);
}

#[inline]
pub fn bls377_Fp2_mul_fp(mut out: &mut Fp2, x: &Fp2, s: &Fp) {
    bls377_mul(&mut out.c0, &x.c0, &s);
    bls377_mul(&mut out.c1, &x.c1, &s);
}

#[inline]
pub fn bls377_make_line(mut out: &mut Fp12, lam: &Fp2, x_t: &Fp2, y_t: &Fp2, x_p: &Fp, y_p: &Fp) {
    let mut tmp: Fp2 = Fp2::zero();
    bls377_Fp2_mul(&mut out.c0.c0, &lam, &x_t);
    let __ac0 = out.c0.c0.clone();
    bls377_Fp2_sub(&mut out.c0.c0, &__ac0, &y_t);
    bls377_Fp2_mul_fp(&mut tmp, &lam, &x_p);
    bls377_Fp2_opp(&mut out.c0.c1, &tmp);
    bls377_from_word(&mut out.c0.c2.c0, 0u64);
    bls377_from_word(&mut out.c0.c2.c1, 0u64);
    bls377_from_word(&mut out.c1.c0.c0, 0u64);
    bls377_from_word(&mut out.c1.c0.c1, 0u64);
    bls377_felem_copy(&mut out.c1.c1.c0, &y_p);
    bls377_from_word(&mut out.c1.c1.c1, 0u64);
    bls377_from_word(&mut out.c1.c2.c0, 0u64);
    bls377_from_word(&mut out.c1.c2.c1, 0u64);
}

#[inline]
pub fn bls377_load_gamma1_p2(mut out: &mut Fp2) {
    out.c0.0[0] = 15766275933608376691u64;
    out.c0.0[1] = 15635974902606112666u64;
    out.c0.0[2] = 1934946774703877852u64;
    out.c0.0[3] = 18129354943882397960u64;
    out.c0.0[4] = 15437979634065614942u64;
    out.c0.0[5] = 101285514078273488u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_gamma2_p2(mut out: &mut Fp2) {
    out.c0.0[0] = 3203870859294639911u64;
    out.c0.0[1] = 276961138506029237u64;
    out.c0.0[2] = 9479726329337356593u64;
    out.c0.0[3] = 13645541738420943632u64;
    out.c0.0[4] = 7584832609311778094u64;
    out.c0.0[5] = 101110569012358506u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_w_frob_p2_c1(mut out: &mut Fp2) {
    out.c0.0[0] = 6382252053795993818u64;
    out.c0.0[1] = 1383562296554596171u64;
    out.c0.0[2] = 11197251941974877903u64;
    out.c0.0[3] = 6684509567199238270u64;
    out.c0.0[4] = 6699184357838251020u64;
    out.c0.0[5] = 19987743694136192u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_gamma1(mut out: &mut Fp2) {
    out.c0.0[0] = 6382252053795993818u64;
    out.c0.0[1] = 1383562296554596171u64;
    out.c0.0[2] = 11197251941974877903u64;
    out.c0.0[3] = 6684509567199238270u64;
    out.c0.0[4] = 6699184357838251020u64;
    out.c0.0[5] = 19987743694136192u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_gamma2(mut out: &mut Fp2) {
    out.c0.0[0] = 15766275933608376691u64;
    out.c0.0[1] = 15635974902606112666u64;
    out.c0.0[2] = 1934946774703877852u64;
    out.c0.0[3] = 18129354943882397960u64;
    out.c0.0[4] = 15437979634065614942u64;
    out.c0.0[5] = 101285514078273488u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls377_load_w_frob_c1(mut out: &mut Fp2) {
    out.c0.0[0] = 7981638599956744862u64;
    out.c0.0[1] = 11830407261614897732u64;
    out.c0.0[2] = 6308788297503259939u64;
    out.c0.0[3] = 10596665404780565693u64;
    out.c0.0[4] = 11693741422477421038u64;
    out.c0.0[5] = 61545186993886319u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls377_Fp12_pow_u(mut out: &mut Fp12, base: &Fp12) {
    let mut result: Fp12 = Fp12::zero();
    bls377_Fp12_felem_copy(&mut result, &base);
    let mut i: u64;
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let __ac0 = result.clone();
        bls377_Fp12_square(&mut result, &__ac0);
        let mut bit: u64;
        bit = ((9586122913090633729u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac1 = result.clone();
            bls377_Fp12_mul_nocopy(&mut result, &__ac1, &base);
        } else {
        }
    }
    bls377_Fp12_felem_copy(&mut out, &result);
}

#[inline]
pub fn bls377_final_exp_hard_dsd(mut out: &mut Fp12, f: &Fp12) {
    let mut t0: Fp12 = Fp12::zero();
    let mut t1: Fp12 = Fp12::zero();
    let mut t2: Fp12 = Fp12::zero();
    let mut t3: Fp12 = Fp12::zero();
    let mut gamma1: Fp2 = Fp2::zero();
    let mut gamma2: Fp2 = Fp2::zero();
    let mut w_frob_c1: Fp2 = Fp2::zero();
    bls377_load_gamma1(&mut gamma1, );
    bls377_load_gamma2(&mut gamma2, );
    bls377_load_w_frob_c1(&mut w_frob_c1, );
    bls377_Fp12_pow_u(&mut t0, &f);
    bls377_Fp12_square(&mut t1, &t0);
    bls377_Fp12_pow_u(&mut t2, &t0);
    bls377_Fp12_square(&mut t3, &t2);
    let __ac0 = t1.clone();
    bls377_Fp12_mul_nocopy(&mut t1, &__ac0, &t2);
    let __ac1 = t2.clone();
    bls377_Fp12_pow_u(&mut t2, &__ac1);
    let __ac2 = t1.clone();
    bls377_Fp12_mul_nocopy(&mut t1, &__ac2, &t2);
    let __ac3 = t1.clone();
    bls377_Fp12_conjugate(&mut t1, &__ac3);
    let __ac4 = t1.clone();
    bls377_Fp12_mul_nocopy(&mut t1, &__ac4, &f);
    let __ac5 = t1.clone();
    bls377_Fp12_conjugate(&mut t1, &__ac5);
    bls377_Fp12_conjugate(&mut t0, &f);
    let __ac6 = t1.clone();
    bls377_Fp12_mul_nocopy(&mut t1, &__ac6, &t0);
    let __ac7 = t2.clone();
    bls377_Fp12_pow_u(&mut t2, &__ac7);
    bls377_Fp12_mul_nocopy(&mut t0, &t2, &t3);
    let __ac8 = t0.clone();
    bls377_Fp12_mul_nocopy(&mut t0, &__ac8, &t1);
    bls377_Fp12_frobenius(&mut t1, &f, &gamma1, &gamma2, &w_frob_c1);
    bls377_Fp12_frobenius(&mut t2, &t1, &gamma1, &gamma2, &w_frob_c1);
    bls377_Fp12_frobenius(&mut t3, &t2, &gamma1, &gamma2, &w_frob_c1);
    let __ac9 = t0.clone();
    bls377_Fp12_mul_nocopy(&mut t0, &__ac9, &t1);
    let __ac10 = t0.clone();
    bls377_Fp12_mul_nocopy(&mut t0, &__ac10, &t2);
    let __ac11 = t0.clone();
    bls377_Fp12_mul_nocopy(&mut t0, &__ac11, &t3);
    bls377_Fp12_felem_copy(&mut out, &t0);
}

#[inline]
pub fn bls377_final_exp_dsd(mut out: &mut Fp12, f: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    let mut result: Fp12 = Fp12::zero();
    let mut tmp: Fp12 = Fp12::zero();
    bls377_Fp12_conjugate(&mut result, &f);
    bls377_Fp12_inv(&mut tmp, &f);
    let __ac0 = result.clone();
    bls377_Fp12_mul_nocopy(&mut result, &__ac0, &tmp);
    bls377_Fp12_frobenius_p2(&mut tmp, &result, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
    let __ac1 = result.clone();
    bls377_Fp12_mul_nocopy(&mut result, &tmp, &__ac1);
    bls377_final_exp_hard_dsd(&mut out, &result);
}

#[inline]
pub fn bls377_miller_loop(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
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
    bls377_Fp2_felem_copy(&mut t_x, &q_x);
    bls377_Fp2_felem_copy(&mut t_y, &q_y);
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
        bls377_Fp2_square(&mut tmp1, &t_x);
        bls377_Fp2_add(&mut lambda, &tmp1, &tmp1);
        let __ac0 = lambda.clone();
        bls377_Fp2_add(&mut lambda, &__ac0, &tmp1);
        bls377_Fp2_add(&mut tmp1, &t_y, &t_y);
        let __ac1 = tmp1.clone();
        bls377_Fp2_inv(&mut tmp1, &__ac1);
        let __ac2 = lambda.clone();
        bls377_Fp2_mul(&mut lambda, &__ac2, &tmp1);
        bls377_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
        let __ac3 = f.clone();
        bls377_Fp12_square(&mut f, &__ac3);
        let __ac4 = f.clone();
        bls377_Fp12_mul_nocopy(&mut f, &__ac4, &line);
        bls377_Fp2_square(&mut tmp1, &lambda);
        let __ac5 = tmp1.clone();
        bls377_Fp2_sub(&mut tmp1, &__ac5, &t_x);
        bls377_Fp2_sub(&mut tmp2, &tmp1, &t_x);
        bls377_Fp2_sub(&mut tmp1, &t_x, &tmp2);
        let __ac6 = tmp1.clone();
        bls377_Fp2_mul(&mut tmp1, &lambda, &__ac6);
        let __ac7 = t_y.clone();
        bls377_Fp2_sub(&mut t_y, &tmp1, &__ac7);
        bls377_Fp2_felem_copy(&mut t_x, &tmp2);
        if bit != 0 {
            bls377_Fp2_sub(&mut tmp1, &q_y, &t_y);
            bls377_Fp2_sub(&mut tmp2, &q_x, &t_x);
            let __ac8 = tmp2.clone();
            bls377_Fp2_inv(&mut tmp2, &__ac8);
            bls377_Fp2_mul(&mut lambda, &tmp1, &tmp2);
            bls377_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
            let __ac9 = f.clone();
            bls377_Fp12_mul_nocopy(&mut f, &__ac9, &line);
            bls377_Fp2_square(&mut tmp1, &lambda);
            let __ac10 = tmp1.clone();
            bls377_Fp2_sub(&mut tmp1, &__ac10, &t_x);
            bls377_Fp2_sub(&mut tmp2, &tmp1, &q_x);
            bls377_Fp2_sub(&mut tmp1, &t_x, &tmp2);
            let __ac11 = tmp1.clone();
            bls377_Fp2_mul(&mut tmp1, &lambda, &__ac11);
            let __ac12 = t_y.clone();
            bls377_Fp2_sub(&mut t_y, &tmp1, &__ac12);
            bls377_Fp2_felem_copy(&mut t_x, &tmp2);
        } else {
        }
    }
    bls377_Fp12_felem_copy(&mut out, &f);
}

#[inline]
pub fn bls377_final_exp(mut out: &mut Fp12, f: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    let mut result: Fp12 = Fp12::zero();
    let mut tmp: Fp12 = Fp12::zero();
    let mut base: Fp12 = Fp12::zero();
    let mut h3: Fp = Fp::zero();
    bls377_Fp12_conjugate(&mut result, &f);
    bls377_Fp12_inv(&mut tmp, &f);
    let __ac0 = result.clone();
    bls377_Fp12_mul_nocopy(&mut result, &__ac0, &tmp);
    bls377_Fp12_frobenius_p2(&mut tmp, &result, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
    let __ac1 = result.clone();
    bls377_Fp12_mul_nocopy(&mut result, &tmp, &__ac1);
    bls377_Fp12_felem_copy(&mut base, &result);
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
            let __ac2 = result.clone();
            bls377_Fp12_square(&mut result, &__ac2);
        } else {
        }
        if bit != 0 {
            if started != 0 {
                let __ac3 = result.clone();
                bls377_Fp12_mul_nocopy(&mut result, &__ac3, &base);
            } else {
                bls377_Fp12_felem_copy(&mut result, &base);
                started = 1u64;
            }
        } else {
        }
    }
    bls377_Fp12_felem_copy(&mut out, &result);
}

#[inline]
pub fn bls377_pairing(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut tmp: Fp12 = Fp12::zero();
    let mut gamma1_p2: Fp2 = Fp2::zero();
    let mut gamma2_p2: Fp2 = Fp2::zero();
    let mut w_frob_p2_c1: Fp2 = Fp2::zero();
    bls377_load_gamma1_p2(&mut gamma1_p2, );
    bls377_load_gamma2_p2(&mut gamma2_p2, );
    bls377_load_w_frob_p2_c1(&mut w_frob_p2_c1, );
    bls377_miller_loop(&mut tmp, &p_x, &p_y, &q_x, &q_y);
    bls377_final_exp(&mut out, &tmp, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
}

#[inline]
pub fn bls377_pairing_dsd(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut tmp: Fp12 = Fp12::zero();
    let mut gamma1_p2: Fp2 = Fp2::zero();
    let mut gamma2_p2: Fp2 = Fp2::zero();
    let mut w_frob_p2_c1: Fp2 = Fp2::zero();
    bls377_load_gamma1_p2(&mut gamma1_p2, );
    bls377_load_gamma2_p2(&mut gamma2_p2, );
    bls377_load_w_frob_p2_c1(&mut w_frob_p2_c1, );
    bls377_miller_loop(&mut tmp, &p_x, &p_y, &q_x, &q_y);
    bls377_final_exp_dsd(&mut out, &tmp, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
}

