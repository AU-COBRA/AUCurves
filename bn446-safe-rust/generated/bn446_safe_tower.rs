#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp(pub [u64; 7]);
impl Fp { #[inline] pub const fn zero() -> Self { Fp([0u64; 7]) } }

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
    fn _bn446_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bn446_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bn446_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bn446_square(o: *mut u64, x: *const u64);
    fn _bn446_opp(o: *mut u64, x: *const u64);
    fn _bn446_felem_copy(o: *mut u64, x: *const u64);
    fn _bn446_from_word(o: *mut u64, w: u64);
    fn _bn446_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bn446_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bn446_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn446_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn446_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn446_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn446_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn446_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn446_square(o: &mut Fp, x: &Fp) { unsafe { _bn446_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn446_opp(o: &mut Fp, x: &Fp) { unsafe { _bn446_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn446_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bn446_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn446_from_word(o: &mut Fp, w: u64) { unsafe { _bn446_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bn446_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bn446_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn446_inv(o: &mut Fp, x: &Fp) { unsafe { _bn446_inv(o.0.as_mut_ptr(), x.0.as_ptr()) } }

#[inline]
pub fn bn446_Fp2_felem_copy(mut out: &mut Fp2, x: &Fp2) {
    bn446_felem_copy(&mut out.c0, &x.c0);
    bn446_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bn446_Fp2_add(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    bn446_add(&mut out.c0, &inx.c0, &iny.c0);
    bn446_add(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bn446_Fp2_sub(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    bn446_sub(&mut out.c0, &inx.c0, &iny.c0);
    bn446_sub(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bn446_Fp2_mul(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    let mut v2: Fp = Fp::zero();
    bn446_mul(&mut v0, &inx.c0, &iny.c0);
    bn446_mul(&mut v1, &inx.c1, &iny.c1);
    bn446_add(&mut v2, &inx.c0, &inx.c1);
    bn446_add(&mut out.c1, &iny.c0, &iny.c1);
    let __ac0 = out.c1.clone();
    bn446_mul(&mut out.c1, &__ac0, &v2);
    let __ac1 = out.c1.clone();
    bn446_sub(&mut out.c1, &__ac1, &v0);
    let __ac2 = out.c1.clone();
    bn446_sub(&mut out.c1, &__ac2, &v1);
    bn446_sub(&mut out.c0, &v0, &v1);
}

#[inline]
pub fn bn446_Fp2_square(mut out: &mut Fp2, inx: &Fp2) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    bn446_square(&mut v0, &inx.c0);
    bn446_square(&mut v1, &inx.c1);
    bn446_mul(&mut out.c1, &inx.c0, &inx.c1);
    let __ac0 = out.c1.clone();
    bn446_add(&mut out.c1, &__ac0, &__ac0);
    bn446_sub(&mut out.c0, &v0, &v1);
}

#[inline]
pub fn bn446_Fp2_inv(mut out: &mut Fp2, inx: &Fp2) {
    let mut asq: Fp = Fp::zero();
    let mut bsq: Fp = Fp::zero();
    let mut norm: Fp = Fp::zero();
    bn446_square(&mut asq, &inx.c0);
    bn446_square(&mut bsq, &inx.c1);
    bn446_add(&mut norm, &asq, &bsq);
    let __ac0 = norm.clone();
    bn446_inv(&mut norm, &__ac0);
    bn446_mul(&mut out.c0, &inx.c0, &norm);
    bn446_opp(&mut asq, &inx.c1);
    bn446_mul(&mut out.c1, &asq, &norm);
}

#[inline]
pub fn bn446_Fp2_opp(mut out: &mut Fp2, x: &Fp2) {
    bn446_opp(&mut out.c0, &x.c0);
    bn446_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bn446_Fp2_mul_xi(mut out: &mut Fp2, x: &Fp2) {
    let mut tmp_a3: Fp = Fp::zero();
    let mut tmp_b3: Fp = Fp::zero();
    bn446_add(&mut tmp_a3, &x.c0, &x.c0);
    let __ac0 = tmp_a3.clone();
    bn446_add(&mut tmp_a3, &__ac0, &x.c0);
    bn446_add(&mut tmp_b3, &x.c1, &x.c1);
    let __ac1 = tmp_b3.clone();
    bn446_add(&mut tmp_b3, &__ac1, &x.c1);
    bn446_add(&mut out.c0, &x.c0, &x.c0);
    let __ac2 = out.c0.clone();
    bn446_sub(&mut out.c0, &__ac2, &tmp_b3);
    bn446_add(&mut out.c1, &x.c1, &x.c1);
    let __ac3 = out.c1.clone();
    bn446_add(&mut out.c1, &tmp_a3, &__ac3);
}

#[inline]
pub fn bn446_Fp6_felem_copy(mut out: &mut Fp6, x: &Fp6) {
    bn446_Fp2_felem_copy(&mut out.c0, &x.c0);
    bn446_Fp2_felem_copy(&mut out.c1, &x.c1);
    bn446_Fp2_felem_copy(&mut out.c2, &x.c2);
}

#[inline]
pub fn bn446_Fp6_add(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bn446_Fp6_felem_copy(&mut allocx, &inx);
    bn446_Fp6_felem_copy(&mut allocy, &iny);
    bn446_Fp2_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bn446_Fp2_add(&mut out.c1, &allocx.c1, &allocy.c1);
    bn446_Fp2_add(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bn446_Fp6_sub(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bn446_Fp6_felem_copy(&mut allocx, &inx);
    bn446_Fp6_felem_copy(&mut allocy, &iny);
    bn446_Fp2_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bn446_Fp2_sub(&mut out.c1, &allocx.c1, &allocy.c1);
    bn446_Fp2_sub(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bn446_Fp6_opp(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    bn446_Fp6_felem_copy(&mut allocx, &x);
    bn446_Fp2_opp(&mut out.c0, &allocx.c0);
    bn446_Fp2_opp(&mut out.c1, &allocx.c1);
    bn446_Fp2_opp(&mut out.c2, &allocx.c2);
}

#[inline]
pub fn bn446_Fp6_mul(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    let mut a0b0: Fp2 = Fp2::zero();
    let mut a1b1: Fp2 = Fp2::zero();
    let mut a2b2: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    let mut u: Fp2 = Fp2::zero();
    bn446_Fp6_felem_copy(&mut allocx, &inx);
    bn446_Fp6_felem_copy(&mut allocy, &iny);
    bn446_Fp2_mul(&mut a0b0, &allocx.c0, &allocy.c0);
    bn446_Fp2_mul(&mut a1b1, &allocx.c1, &allocy.c1);
    bn446_Fp2_mul(&mut a2b2, &allocx.c2, &allocy.c2);
    bn446_Fp2_add(&mut t, &allocx.c1, &allocx.c2);
    bn446_Fp2_add(&mut u, &allocy.c1, &allocy.c2);
    let __ac0 = t.clone();
    bn446_Fp2_mul(&mut t, &__ac0, &u);
    let __ac1 = t.clone();
    bn446_Fp2_sub(&mut t, &__ac1, &a1b1);
    let __ac2 = t.clone();
    bn446_Fp2_sub(&mut t, &__ac2, &a2b2);
    let __ac3 = t.clone();
    bn446_Fp2_mul_xi(&mut t, &__ac3);
    bn446_Fp2_add(&mut out.c0, &a0b0, &t);
    bn446_Fp2_add(&mut t, &allocx.c0, &allocx.c1);
    bn446_Fp2_add(&mut u, &allocy.c0, &allocy.c1);
    let __ac4 = t.clone();
    bn446_Fp2_mul(&mut t, &__ac4, &u);
    let __ac5 = t.clone();
    bn446_Fp2_sub(&mut t, &__ac5, &a0b0);
    let __ac6 = t.clone();
    bn446_Fp2_sub(&mut t, &__ac6, &a1b1);
    bn446_Fp2_mul_xi(&mut u, &a2b2);
    bn446_Fp2_add(&mut out.c1, &t, &u);
    bn446_Fp2_add(&mut t, &allocx.c0, &allocx.c2);
    bn446_Fp2_add(&mut u, &allocy.c0, &allocy.c2);
    let __ac7 = t.clone();
    bn446_Fp2_mul(&mut t, &__ac7, &u);
    let __ac8 = t.clone();
    bn446_Fp2_sub(&mut t, &__ac8, &a0b0);
    let __ac9 = t.clone();
    bn446_Fp2_sub(&mut t, &__ac9, &a2b2);
    bn446_Fp2_add(&mut out.c2, &t, &a1b1);
}

#[inline]
pub fn bn446_Fp6_square(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut s0: Fp2 = Fp2::zero();
    let mut s1: Fp2 = Fp2::zero();
    let mut s2: Fp2 = Fp2::zero();
    let mut s3: Fp2 = Fp2::zero();
    let mut s4: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    bn446_Fp6_felem_copy(&mut allocx, &x);
    bn446_Fp2_square(&mut s0, &allocx.c0);
    bn446_Fp2_mul(&mut t, &allocx.c0, &allocx.c1);
    bn446_Fp2_add(&mut s1, &t, &t);
    bn446_Fp2_sub(&mut t, &allocx.c0, &allocx.c1);
    let __ac0 = t.clone();
    bn446_Fp2_add(&mut t, &__ac0, &allocx.c2);
    bn446_Fp2_square(&mut s2, &t);
    bn446_Fp2_mul(&mut t, &allocx.c1, &allocx.c2);
    bn446_Fp2_add(&mut s3, &t, &t);
    bn446_Fp2_square(&mut s4, &allocx.c2);
    bn446_Fp2_mul_xi(&mut t, &s3);
    bn446_Fp2_add(&mut out.c0, &s0, &t);
    bn446_Fp2_mul_xi(&mut t, &s4);
    bn446_Fp2_add(&mut out.c1, &s1, &t);
    bn446_Fp2_add(&mut t, &s1, &s2);
    let __ac1 = t.clone();
    bn446_Fp2_add(&mut t, &__ac1, &s3);
    let __ac2 = t.clone();
    bn446_Fp2_sub(&mut t, &__ac2, &s0);
    bn446_Fp2_sub(&mut out.c2, &t, &s4);
}

#[inline]
pub fn bn446_Fp6_inv(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut vA: Fp2 = Fp2::zero();
    let mut vB: Fp2 = Fp2::zero();
    let mut vC: Fp2 = Fp2::zero();
    let mut t1: Fp2 = Fp2::zero();
    let mut t2: Fp2 = Fp2::zero();
    let mut t3: Fp2 = Fp2::zero();
    bn446_Fp6_felem_copy(&mut allocx, &x);
    bn446_Fp2_square(&mut t1, &allocx.c0);
    bn446_Fp2_mul(&mut t2, &allocx.c1, &allocx.c2);
    bn446_Fp2_mul_xi(&mut t3, &t2);
    bn446_Fp2_sub(&mut vA, &t1, &t3);
    bn446_Fp2_square(&mut t1, &allocx.c2);
    bn446_Fp2_mul_xi(&mut t3, &t1);
    bn446_Fp2_mul(&mut t2, &allocx.c0, &allocx.c1);
    bn446_Fp2_sub(&mut vB, &t3, &t2);
    bn446_Fp2_square(&mut t1, &allocx.c1);
    bn446_Fp2_mul(&mut t2, &allocx.c0, &allocx.c2);
    bn446_Fp2_sub(&mut vC, &t1, &t2);
    bn446_Fp2_mul(&mut t1, &allocx.c0, &vA);
    bn446_Fp2_mul(&mut t2, &allocx.c2, &vB);
    bn446_Fp2_mul(&mut t3, &allocx.c1, &vC);
    let __ac0 = t2.clone();
    bn446_Fp2_add(&mut t2, &__ac0, &t3);
    let __ac1 = t2.clone();
    bn446_Fp2_mul_xi(&mut t2, &__ac1);
    let __ac2 = t1.clone();
    bn446_Fp2_add(&mut t1, &__ac2, &t2);
    let __ac3 = t1.clone();
    bn446_Fp2_inv(&mut t1, &__ac3);
    bn446_Fp2_mul(&mut out.c0, &vA, &t1);
    bn446_Fp2_mul(&mut out.c1, &vB, &t1);
    bn446_Fp2_mul(&mut out.c2, &vC, &t1);
}

#[inline]
pub fn bn446_Fp6_add_nocopy(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    bn446_Fp2_add(&mut out.c0, &inx.c0, &iny.c0);
    bn446_Fp2_add(&mut out.c1, &inx.c1, &iny.c1);
    bn446_Fp2_add(&mut out.c2, &inx.c2, &iny.c2);
}

#[inline]
pub fn bn446_Fp6_sub_nocopy(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    bn446_Fp2_sub(&mut out.c0, &inx.c0, &iny.c0);
    bn446_Fp2_sub(&mut out.c1, &inx.c1, &iny.c1);
    bn446_Fp2_sub(&mut out.c2, &inx.c2, &iny.c2);
}

#[inline]
pub fn bn446_Fp6_mul_by_v(mut out: &mut Fp6, x: &Fp6) {
    let mut tmp: Fp6 = Fp6::zero();
    bn446_Fp6_felem_copy(&mut tmp, &x);
    bn446_Fp2_mul_xi(&mut out.c0, &tmp.c2);
    bn446_Fp2_felem_copy(&mut out.c1, &tmp.c0);
    bn446_Fp2_felem_copy(&mut out.c2, &tmp.c1);
}

#[inline]
pub fn bn446_Fp12_felem_copy(mut out: &mut Fp12, x: &Fp12) {
    bn446_Fp6_felem_copy(&mut out.c0, &x.c0);
    bn446_Fp6_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bn446_Fp12_add(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bn446_Fp12_felem_copy(&mut ax, &inx);
    bn446_Fp12_felem_copy(&mut ay, &iny);
    bn446_Fp6_add_nocopy(&mut out.c0, &ax.c0, &ay.c0);
    bn446_Fp6_add_nocopy(&mut out.c1, &ax.c1, &ay.c1);
}

#[inline]
pub fn bn446_Fp12_sub(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bn446_Fp12_felem_copy(&mut ax, &inx);
    bn446_Fp12_felem_copy(&mut ay, &iny);
    bn446_Fp6_sub_nocopy(&mut out.c0, &ax.c0, &ay.c0);
    bn446_Fp6_sub_nocopy(&mut out.c1, &ax.c1, &ay.c1);
}

#[inline]
pub fn bn446_Fp12_opp(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bn446_Fp12_felem_copy(&mut allocx, &x);
    bn446_Fp6_opp(&mut out.c0, &allocx.c0);
    bn446_Fp6_opp(&mut out.c1, &allocx.c1);
}

#[inline]
pub fn bn446_Fp12_conjugate(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bn446_Fp12_felem_copy(&mut allocx, &x);
    bn446_Fp6_felem_copy(&mut out.c0, &allocx.c0);
    bn446_Fp6_opp(&mut out.c1, &allocx.c1);
}

#[inline]
pub fn bn446_Fp12_mul(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bn446_Fp12_felem_copy(&mut ax, &inx);
    bn446_Fp12_felem_copy(&mut ay, &iny);
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bn446_Fp6_mul(&mut v0, &ax.c0, &ay.c0);
    bn446_Fp6_mul(&mut v1, &ax.c1, &ay.c1);
    bn446_Fp6_add_nocopy(&mut t, &ax.c0, &ax.c1);
    bn446_Fp6_add_nocopy(&mut u, &ay.c0, &ay.c1);
    let __ac0 = t.clone();
    bn446_Fp6_mul(&mut t, &__ac0, &u);
    bn446_Fp6_mul_by_v(&mut u, &v1);
    bn446_Fp6_add_nocopy(&mut out.c0, &v0, &u);
    let __ac1 = t.clone();
    bn446_Fp6_sub_nocopy(&mut t, &__ac1, &v0);
    bn446_Fp6_sub_nocopy(&mut out.c1, &t, &v1);
}

#[inline]
pub fn bn446_Fp12_square(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bn446_Fp12_felem_copy(&mut allocx, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    let mut t2: Fp6 = Fp6::zero();
    bn446_Fp6_square(&mut t0, &allocx.c0);
    bn446_Fp6_square(&mut t1, &allocx.c1);
    bn446_Fp6_mul(&mut t2, &allocx.c0, &allocx.c1);
    let __ac0 = t1.clone();
    bn446_Fp6_mul_by_v(&mut t1, &__ac0);
    bn446_Fp6_add_nocopy(&mut out.c0, &t0, &t1);
    bn446_Fp6_add_nocopy(&mut out.c1, &t2, &t2);
}

#[inline]
pub fn bn446_Fp12_inv(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bn446_Fp12_felem_copy(&mut allocx, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    bn446_Fp6_square(&mut t0, &allocx.c0);
    bn446_Fp6_square(&mut t1, &allocx.c1);
    let __ac0 = t1.clone();
    bn446_Fp6_mul_by_v(&mut t1, &__ac0);
    let __ac1 = t0.clone();
    bn446_Fp6_sub_nocopy(&mut t0, &__ac1, &t1);
    let __ac2 = t0.clone();
    bn446_Fp6_inv(&mut t0, &__ac2);
    bn446_Fp6_mul(&mut out.c0, &allocx.c0, &t0);
    bn446_Fp6_mul(&mut out.c1, &allocx.c1, &t0);
    let __ac3 = out.c1.clone();
    bn446_Fp6_opp(&mut out.c1, &__ac3);
}

#[inline]
pub fn bn446_Fp12_add_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    bn446_Fp6_add_nocopy(&mut out.c0, &inx.c0, &iny.c0);
    bn446_Fp6_add_nocopy(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bn446_Fp12_sub_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    bn446_Fp6_sub_nocopy(&mut out.c0, &inx.c0, &iny.c0);
    bn446_Fp6_sub_nocopy(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bn446_Fp12_mul_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bn446_Fp6_mul(&mut v0, &inx.c0, &iny.c0);
    bn446_Fp6_mul(&mut v1, &inx.c1, &iny.c1);
    bn446_Fp6_add_nocopy(&mut t, &inx.c0, &inx.c1);
    bn446_Fp6_add_nocopy(&mut u, &iny.c0, &iny.c1);
    let __ac0 = t.clone();
    bn446_Fp6_mul(&mut t, &__ac0, &u);
    bn446_Fp6_mul_by_v(&mut u, &v1);
    bn446_Fp6_add_nocopy(&mut out.c0, &v0, &u);
    let __ac1 = t.clone();
    bn446_Fp6_sub_nocopy(&mut t, &__ac1, &v0);
    bn446_Fp6_sub_nocopy(&mut out.c1, &t, &v1);
}

#[inline]
pub fn bn446_Fp2_conjugate(mut out: &mut Fp2, x: &Fp2) {
    bn446_felem_copy(&mut out.c0, &x.c0);
    bn446_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bn446_Fp6_mul_fp2(mut out: &mut Fp6, x: &Fp6, s: &Fp2) {
    let mut s_copy: Fp2 = Fp2::zero();
    bn446_Fp2_felem_copy(&mut s_copy, &s);
    bn446_Fp2_mul(&mut out.c0, &x.c0, &s_copy);
    bn446_Fp2_mul(&mut out.c1, &x.c1, &s_copy);
    bn446_Fp2_mul(&mut out.c2, &x.c2, &s_copy);
}

#[inline]
pub fn bn446_Fp6_frobenius(mut out: &mut Fp6, x: &Fp6, gamma1: &Fp2, gamma2: &Fp2) {
    let mut tmp: Fp6 = Fp6::zero();
    bn446_Fp2_conjugate(&mut tmp.c0, &x.c0);
    bn446_Fp2_conjugate(&mut tmp.c1, &x.c1);
    bn446_Fp2_conjugate(&mut tmp.c2, &x.c2);
    bn446_Fp2_felem_copy(&mut out.c0, &tmp.c0);
    bn446_Fp2_mul(&mut out.c1, &tmp.c1, &gamma1);
    bn446_Fp2_mul(&mut out.c2, &tmp.c2, &gamma2);
}

#[inline]
pub fn bn446_Fp6_frobenius_p2(mut out: &mut Fp6, x: &Fp6, gamma1_p2: &Fp2, gamma2_p2: &Fp2) {
    bn446_Fp2_felem_copy(&mut out.c0, &x.c0);
    bn446_Fp2_mul(&mut out.c1, &x.c1, &gamma1_p2);
    bn446_Fp2_mul(&mut out.c2, &x.c2, &gamma2_p2);
}

#[inline]
pub fn bn446_Fp12_frobenius(mut out: &mut Fp12, x: &Fp12, gamma1: &Fp2, gamma2: &Fp2, w_frob_c1: &Fp2) {
    bn446_Fp6_frobenius(&mut out.c0, &x.c0, &gamma1, &gamma2);
    bn446_Fp6_frobenius(&mut out.c1, &x.c1, &gamma1, &gamma2);
    let __ac0 = out.c1.clone();
    bn446_Fp6_mul_fp2(&mut out.c1, &__ac0, &w_frob_c1);
}

#[inline]
pub fn bn446_Fp12_frobenius_p2(mut out: &mut Fp12, x: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    bn446_Fp6_frobenius_p2(&mut out.c0, &x.c0, &gamma1_p2, &gamma2_p2);
    bn446_Fp6_frobenius_p2(&mut out.c1, &x.c1, &gamma1_p2, &gamma2_p2);
    let __ac0 = out.c1.clone();
    bn446_Fp6_mul_fp2(&mut out.c1, &__ac0, &w_frob_p2_c1);
}

#[inline]
pub fn bn446_Fp12_frobenius_p3(mut out: &mut Fp12, x: &Fp12, gamma1: &Fp12, gamma2: &Fp12, gamma1_p2: &Fp12, gamma2_p2: &Fp12, w_frob_c1: &Fp12, w_frob_p2_c1: &Fp12) {
    let mut tmp: Fp12 = Fp12::zero();
    bn446_Fp6_frobenius_p2(&mut tmp.c0, &x.c0, &gamma1_p2.c0.c0, &gamma2_p2.c0.c0);
    bn446_Fp6_frobenius_p2(&mut tmp.c1, &x.c1, &gamma1_p2.c0.c0, &gamma2_p2.c0.c0);
    let __ac0 = tmp.c1.clone();
    bn446_Fp6_mul_fp2(&mut tmp.c1, &__ac0, &w_frob_p2_c1.c0.c0);
    bn446_Fp6_frobenius(&mut out.c0, &tmp.c0, &gamma1.c0.c0, &gamma2.c0.c0);
    bn446_Fp6_frobenius(&mut out.c1, &tmp.c1, &gamma1.c0.c0, &gamma2.c0.c0);
    let __ac1 = out.c1.clone();
    bn446_Fp6_mul_fp2(&mut out.c1, &__ac1, &w_frob_c1.c0.c0);
}

#[inline]
pub fn bn446_Fp2_mul_fp(mut out: &mut Fp2, x: &Fp2, s: &Fp) {
    bn446_mul(&mut out.c0, &x.c0, &s);
    bn446_mul(&mut out.c1, &x.c1, &s);
}

#[inline]
pub fn bn446_make_line(mut out: &mut Fp12, lam: &Fp2, x_t: &Fp2, y_t: &Fp2, x_p: &Fp, y_p: &Fp) {
    let mut tmp: Fp2 = Fp2::zero();
    bn446_Fp2_mul(&mut out.c0.c0, &lam, &x_t);
    let __ac0 = out.c0.c0.clone();
    bn446_Fp2_sub(&mut out.c0.c0, &__ac0, &y_t);
    bn446_Fp2_mul_fp(&mut tmp, &lam, &x_p);
    bn446_Fp2_opp(&mut out.c0.c1, &tmp);
    bn446_from_word(&mut out.c0.c2.c0, 0u64);
    bn446_from_word(&mut out.c0.c2.c1, 0u64);
    bn446_from_word(&mut out.c1.c0.c0, 0u64);
    bn446_from_word(&mut out.c1.c0.c1, 0u64);
    bn446_felem_copy(&mut out.c1.c1.c0, &y_p);
    bn446_from_word(&mut out.c1.c1.c1, 0u64);
    bn446_from_word(&mut out.c1.c2.c0, 0u64);
    bn446_from_word(&mut out.c1.c2.c1, 0u64);
}

#[inline]
pub fn bn446_load_gamma1_p2(mut out: &mut Fp2) {
    out.c0.0[0] = 6149474205216094473u64;
    out.c0.0[1] = 1551935740368681301u64;
    out.c0.0[2] = 1224979108002004992u64;
    out.c0.0[3] = 9251359555762u64;
    out.c0.0[4] = 7268321615436420u64;
    out.c0.0[5] = 179018085200080896u64;
    out.c0.0[6] = 2017612638799790080u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
    out.c1.0[6] = 0u64;
}

#[inline]
pub fn bn446_load_gamma2_p2(mut out: &mut Fp2) {
    out.c0.0[0] = 12297438093772507695u64;
    out.c0.0[1] = 17092403766992463530u64;
    out.c0.0[2] = 2810246159600451583u64;
    out.c0.0[3] = 18446735646983716690u64;
    out.c0.0[4] = 18439594499349919323u64;
    out.c0.0[5] = 18348790781803614207u64;
    out.c0.0[6] = 288230370413903871u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
    out.c1.0[6] = 0u64;
}

#[inline]
pub fn bn446_load_w_frob_p2_c1(mut out: &mut Fp2) {
    out.c0.0[0] = 6149327008096925240u64;
    out.c0.0[1] = 1379039735923537237u64;
    out.c0.0[2] = 6917529035704631296u64;
    out.c0.0[3] = 8529805050030u64;
    out.c0.0[4] = 7164417766607808u64;
    out.c0.0[5] = 108086391067705344u64;
    out.c0.0[6] = 2305843014951501824u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
    out.c1.0[6] = 0u64;
}

#[inline]
pub fn bn446_load_gamma1(mut out: &mut Fp2) {
    out.c0.0[0] = 12209398256275365861u64;
    out.c0.0[1] = 7842296303691409873u64;
    out.c0.0[2] = 9501173270238863996u64;
    out.c0.0[3] = 12783437955202041439u64;
    out.c0.0[4] = 17034911413988204631u64;
    out.c0.0[5] = 4423754151726436562u64;
    out.c0.0[6] = 1722183941340302348u64;
    out.c1.0[0] = 17975391155522769930u64;
    out.c1.0[1] = 11280566538380272132u64;
    out.c1.0[2] = 11222099769811107033u64;
    out.c1.0[3] = 10093046316314585396u64;
    out.c1.0[4] = 4387625118621607932u64;
    out.c1.0[5] = 9813819623880021739u64;
    out.c1.0[6] = 2068306683967235630u64;
}

#[inline]
pub fn bn446_load_gamma2(mut out: &mut Fp2) {
    out.c0.0[0] = 5037147883518747009u64;
    out.c0.0[1] = 14173528669391125219u64;
    out.c0.0[2] = 17182540433163135825u64;
    out.c0.0[3] = 8975910526891773865u64;
    out.c0.0[4] = 18009760962701558445u64;
    out.c0.0[5] = 983846956853741188u64;
    out.c0.0[6] = 91564803790053570u64;
    out.c1.0[0] = 13928796049445176281u64;
    out.c1.0[1] = 15776250671056347489u64;
    out.c1.0[2] = 7641289675051423739u64;
    out.c1.0[3] = 9653124817812897671u64;
    out.c1.0[4] = 17125230140318319962u64;
    out.c1.0[5] = 5721541499968494089u64;
    out.c1.0[6] = 1111910146226415790u64;
}

#[inline]
pub fn bn446_load_w_frob_c1(mut out: &mut Fp2) {
    out.c0.0[0] = 5711403354505136847u64;
    out.c0.0[1] = 4730576537507033307u64;
    out.c0.0[2] = 5540697330207023260u64;
    out.c0.0[3] = 12464689765543439216u64;
    out.c0.0[4] = 10260455062453743663u64;
    out.c0.0[5] = 15098547885566967397u64;
    out.c0.0[6] = 911385300611655834u64;
    out.c1.0[0] = 832053348675969698u64;
    out.c1.0[1] = 260336753067723126u64;
    out.c1.0[2] = 15315247090728143227u64;
    out.c1.0[3] = 18264254340091231852u64;
    out.c1.0[4] = 2732174512076115880u64;
    out.c1.0[5] = 4305226335506393757u64;
    out.c1.0[6] = 1885737967067146434u64;
}

#[inline]
pub fn bn446_Fp12_pow_u(mut out: &mut Fp12, base: &Fp12) {
    let mut result: Fp12 = Fp12::zero();
    let mut temp: Fp12 = Fp12::zero();
    bn446_Fp12_felem_copy(&mut result, &base);
    bn446_Fp12_felem_copy(&mut temp, &base);
    let mut i: u64;
    i = 36u64;
    while i != 0 {
        let __ac0 = temp.clone();
        bn446_Fp12_square(&mut temp, &__ac0);
        i = i.wrapping_sub(1u64);
    }
    let __ac1 = result.clone();
    bn446_Fp12_mul_nocopy(&mut result, &__ac1, &temp);
    i = 74u64;
    while i != 0 {
        let __ac2 = temp.clone();
        bn446_Fp12_square(&mut temp, &__ac2);
        i = i.wrapping_sub(1u64);
    }
    let __ac3 = result.clone();
    bn446_Fp12_mul_nocopy(&mut result, &__ac3, &temp);
    bn446_Fp12_felem_copy(&mut out, &result);
}

#[inline]
pub fn bn446_final_exp_hard_dsd(mut out: &mut Fp12, f: &Fp12) {
    let mut t0: Fp12 = Fp12::zero();
    let mut t1: Fp12 = Fp12::zero();
    let mut t2: Fp12 = Fp12::zero();
    let mut t3: Fp12 = Fp12::zero();
    let mut gamma1: Fp2 = Fp2::zero();
    let mut gamma2: Fp2 = Fp2::zero();
    let mut w_frob_c1: Fp2 = Fp2::zero();
    bn446_load_gamma1(&mut gamma1, );
    bn446_load_gamma2(&mut gamma2, );
    bn446_load_w_frob_c1(&mut w_frob_c1, );
    bn446_Fp12_pow_u(&mut t0, &f);
    bn446_Fp12_pow_u(&mut t1, &t0);
    bn446_Fp12_pow_u(&mut t2, &t1);
    bn446_Fp12_frobenius(&mut t3, &t2, &gamma1, &gamma2, &w_frob_c1);
    let __ac0 = t2.clone();
    bn446_Fp12_mul_nocopy(&mut t2, &__ac0, &t3);
    let __ac1 = t2.clone();
    bn446_Fp12_conjugate(&mut t2, &__ac1);
    bn446_Fp12_square(&mut out, &t2);
    bn446_Fp12_frobenius(&mut t3, &t1, &gamma1, &gamma2, &w_frob_c1);
    bn446_Fp12_mul_nocopy(&mut t2, &t0, &t3);
    let __ac2 = t2.clone();
    bn446_Fp12_conjugate(&mut t2, &__ac2);
    let __ac3 = out.clone();
    bn446_Fp12_mul_nocopy(&mut out, &__ac3, &t2);
    let __ac4 = t1.clone();
    bn446_Fp12_conjugate(&mut t1, &__ac4);
    let __ac5 = out.clone();
    bn446_Fp12_mul_nocopy(&mut out, &__ac5, &t1);
    bn446_Fp12_frobenius(&mut t2, &t0, &gamma1, &gamma2, &w_frob_c1);
    let __ac6 = t2.clone();
    bn446_Fp12_conjugate(&mut t2, &__ac6);
    bn446_Fp12_mul_nocopy(&mut t0, &out, &t2);
    let __ac7 = t0.clone();
    bn446_Fp12_mul_nocopy(&mut t0, &__ac7, &t1);
    bn446_Fp12_frobenius(&mut t1, &t3, &gamma1, &gamma2, &w_frob_c1);
    let __ac8 = out.clone();
    bn446_Fp12_mul_nocopy(&mut out, &__ac8, &t1);
    bn446_Fp12_square(&mut t1, &t0);
    let __ac9 = t1.clone();
    bn446_Fp12_mul_nocopy(&mut t1, &__ac9, &out);
    let __ac10 = t1.clone();
    bn446_Fp12_square(&mut t1, &__ac10);
    bn446_Fp12_frobenius(&mut t0, &f, &gamma1, &gamma2, &w_frob_c1);
    bn446_Fp12_frobenius(&mut t2, &t0, &gamma1, &gamma2, &w_frob_c1);
    bn446_Fp12_frobenius(&mut t3, &t2, &gamma1, &gamma2, &w_frob_c1);
    let __ac11 = t0.clone();
    bn446_Fp12_mul_nocopy(&mut t0, &__ac11, &t2);
    let __ac12 = t0.clone();
    bn446_Fp12_mul_nocopy(&mut t0, &__ac12, &t3);
    bn446_Fp12_mul_nocopy(&mut t2, &t1, &t0);
    bn446_Fp12_conjugate(&mut t0, &f);
    let __ac13 = t0.clone();
    bn446_Fp12_mul_nocopy(&mut t0, &t1, &__ac13);
    let __ac14 = t0.clone();
    bn446_Fp12_square(&mut t0, &__ac14);
    bn446_Fp12_mul_nocopy(&mut out, &t0, &t2);
}

#[inline]
pub fn bn446_final_exp_dsd(mut out: &mut Fp12, f: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    let mut result: Fp12 = Fp12::zero();
    let mut tmp: Fp12 = Fp12::zero();
    bn446_Fp12_conjugate(&mut result, &f);
    bn446_Fp12_inv(&mut tmp, &f);
    let __ac0 = result.clone();
    bn446_Fp12_mul_nocopy(&mut result, &__ac0, &tmp);
    bn446_Fp12_frobenius_p2(&mut tmp, &result, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
    let __ac1 = result.clone();
    bn446_Fp12_mul_nocopy(&mut result, &tmp, &__ac1);
    bn446_final_exp_hard_dsd(&mut out, &result);
}

#[inline]
pub fn bn446_miller_loop(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut f: Fp12 = Fp12::zero();
    let mut t_x: Fp2 = Fp2::zero();
    let mut t_y: Fp2 = Fp2::zero();
    let mut lambda: Fp2 = Fp2::zero();
    let mut tmp1: Fp2 = Fp2::zero();
    let mut tmp2: Fp2 = Fp2::zero();
    let mut line: Fp12 = Fp12::zero();
    let mut u6p2: Fp = Fp::zero();
    bn446_from_word(&mut f.c0.c0.c0, 1u64);
    bn446_from_word(&mut f.c0.c0.c1, 0u64);
    bn446_from_word(&mut f.c0.c1.c0, 0u64);
    bn446_from_word(&mut f.c0.c1.c1, 0u64);
    bn446_from_word(&mut f.c0.c2.c0, 0u64);
    bn446_from_word(&mut f.c0.c2.c1, 0u64);
    bn446_from_word(&mut f.c1.c0.c0, 0u64);
    bn446_from_word(&mut f.c1.c0.c1, 0u64);
    bn446_from_word(&mut f.c1.c1.c0, 0u64);
    bn446_from_word(&mut f.c1.c1.c1, 0u64);
    bn446_from_word(&mut f.c1.c2.c0, 0u64);
    bn446_from_word(&mut f.c1.c2.c1, 0u64);
    bn446_Fp2_felem_copy(&mut t_x, &q_x);
    bn446_Fp2_felem_copy(&mut t_y, &q_y);
    u6p2.0[0] = 412316860424u64;
    u6p2.0[1] = 422212465065984u64;
    let mut i: u64;
    i = 112u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let mut word: u64;
        word = unsafe { *((u6p2.0.as_ptr() as *const u8).wrapping_add(((i >> (6u64 & 63)) << (3u64 & 63)) as usize) as *const u64) };
        let mut bit: u64;
        bit = ((word >> ((i & 63u64) & 63)) & 1u64);
        bn446_Fp2_square(&mut tmp1, &t_x);
        bn446_Fp2_add(&mut lambda, &tmp1, &tmp1);
        let __ac0 = lambda.clone();
        bn446_Fp2_add(&mut lambda, &__ac0, &tmp1);
        bn446_Fp2_add(&mut tmp1, &t_y, &t_y);
        let __ac1 = tmp1.clone();
        bn446_Fp2_inv(&mut tmp1, &__ac1);
        let __ac2 = lambda.clone();
        bn446_Fp2_mul(&mut lambda, &__ac2, &tmp1);
        bn446_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
        let __ac3 = f.clone();
        bn446_Fp12_square(&mut f, &__ac3);
        let __ac4 = f.clone();
        bn446_Fp12_mul_nocopy(&mut f, &__ac4, &line);
        bn446_Fp2_square(&mut tmp1, &lambda);
        let __ac5 = tmp1.clone();
        bn446_Fp2_sub(&mut tmp1, &__ac5, &t_x);
        bn446_Fp2_sub(&mut tmp2, &tmp1, &t_x);
        bn446_Fp2_sub(&mut tmp1, &t_x, &tmp2);
        let __ac6 = tmp1.clone();
        bn446_Fp2_mul(&mut tmp1, &lambda, &__ac6);
        let __ac7 = t_y.clone();
        bn446_Fp2_sub(&mut t_y, &tmp1, &__ac7);
        bn446_Fp2_felem_copy(&mut t_x, &tmp2);
        if bit != 0 {
            bn446_Fp2_sub(&mut tmp1, &q_y, &t_y);
            bn446_Fp2_sub(&mut tmp2, &q_x, &t_x);
            let __ac8 = tmp2.clone();
            bn446_Fp2_inv(&mut tmp2, &__ac8);
            bn446_Fp2_mul(&mut lambda, &tmp1, &tmp2);
            bn446_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
            let __ac9 = f.clone();
            bn446_Fp12_mul_nocopy(&mut f, &__ac9, &line);
            bn446_Fp2_square(&mut tmp1, &lambda);
            let __ac10 = tmp1.clone();
            bn446_Fp2_sub(&mut tmp1, &__ac10, &t_x);
            bn446_Fp2_sub(&mut tmp2, &tmp1, &q_x);
            bn446_Fp2_sub(&mut tmp1, &t_x, &tmp2);
            let __ac11 = tmp1.clone();
            bn446_Fp2_mul(&mut tmp1, &lambda, &__ac11);
            let __ac12 = t_y.clone();
            bn446_Fp2_sub(&mut t_y, &tmp1, &__ac12);
            bn446_Fp2_felem_copy(&mut t_x, &tmp2);
        } else {
        }
    }
    bn446_Fp12_felem_copy(&mut out, &f);
}

#[inline]
pub fn bn446_pairing_dsd(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut tmp: Fp12 = Fp12::zero();
    let mut gamma1_p2: Fp2 = Fp2::zero();
    let mut gamma2_p2: Fp2 = Fp2::zero();
    let mut w_frob_p2_c1: Fp2 = Fp2::zero();
    bn446_load_gamma1_p2(&mut gamma1_p2, );
    bn446_load_gamma2_p2(&mut gamma2_p2, );
    bn446_load_w_frob_p2_c1(&mut w_frob_p2_c1, );
    bn446_miller_loop(&mut tmp, &p_x, &p_y, &q_x, &q_y);
    bn446_final_exp_dsd(&mut out, &tmp, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
}

