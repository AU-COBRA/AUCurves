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
    fn _bls12_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls12_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls12_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls12_square(o: *mut u64, x: *const u64);
    fn _bls12_opp(o: *mut u64, x: *const u64);
    fn _bls12_felem_copy(o: *mut u64, x: *const u64);
    fn _bls12_from_word(o: *mut u64, w: u64);
    fn _bls12_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bls12_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bls12_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls12_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls12_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls12_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls12_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls12_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls12_square(o: &mut Fp, x: &Fp) { unsafe { _bls12_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls12_opp(o: &mut Fp, x: &Fp) { unsafe { _bls12_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls12_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bls12_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls12_from_word(o: &mut Fp, w: u64) { unsafe { _bls12_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bls12_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bls12_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls12_Fp2_opp(o: &mut Fp2, x: &Fp2) { bls12_opp(&mut o.c0, &x.c0); bls12_opp(&mut o.c1, &x.c1); }
#[inline] pub fn bls12_Fp2_felem_copy(o: &mut Fp2, x: &Fp2) { bls12_felem_copy(&mut o.c0, &x.c0); bls12_felem_copy(&mut o.c1, &x.c1); }
#[inline] pub fn bls12_Fp2_add(o: &mut Fp2, x: &Fp2, y: &Fp2) { bls12_add(&mut o.c0, &x.c0, &y.c0); bls12_add(&mut o.c1, &x.c1, &y.c1); }
#[inline] pub fn bls12_Fp2_sub(o: &mut Fp2, x: &Fp2, y: &Fp2) { bls12_sub(&mut o.c0, &x.c0, &y.c0); bls12_sub(&mut o.c1, &x.c1, &y.c1); }
#[inline]
pub fn bls12_Fp2_mul(out: &mut Fp2, x: &Fp2, y: &Fp2) {
    // Schoolbook: 4 Fp muls + 2 Fp add/sub.  (See history for Karatsuba
    // / lazy-reduction discussion.)
    //
    // _nocopy: dropped the original `let xv = *x; let yv = *y;` Fp2-level
    // pre-copies (192 bytes each).  Safe because the body's structure is
    // read-all-inputs-then-write-output: all four bls12_mul calls read
    // x/y and write to fresh local Fp temporaries t0..t3; the two final
    // bls12_sub/bls12_add then write to out.c0/out.c1 from those temps.
    // No out write happens until after all x/y reads complete, so even
    // if caller-side aliasing slipped past the borrow checker (it
    // doesn't — &mut out coexisting with &x or &y is rejected at the
    // call site), the algebra would still hold.
    let mut t0 = Fp::zero(); let mut t1 = Fp::zero();
    let mut t2 = Fp::zero(); let mut t3 = Fp::zero();
    bls12_mul(&mut t0, &x.c0, &y.c0);
    bls12_mul(&mut t1, &x.c1, &y.c1);
    bls12_mul(&mut t2, &x.c0, &y.c1);
    bls12_mul(&mut t3, &x.c1, &y.c0);
    bls12_sub(&mut out.c0, &t0, &t1);
    bls12_add(&mut out.c1, &t2, &t3);
}
#[inline]
pub fn bls12_Fp2_square(out: &mut Fp2, x: &Fp2) {
    let xv = *x; bls12_Fp2_mul(out, &xv, &xv);
}
#[inline]
pub fn bls12_Fp2_inv(out: &mut Fp2, x: &Fp2) {
    let mut asq = Fp::zero(); let mut bsq = Fp::zero(); let mut norm = Fp::zero();
    bls12_square(&mut asq, &x.c0); bls12_square(&mut bsq, &x.c1);
    bls12_add(&mut norm, &asq, &bsq);
    let n_copy = norm;
    unsafe { _bls12_inv(norm.0.as_mut_ptr(), n_copy.0.as_ptr()); }
    bls12_mul(&mut out.c0, &x.c0, &norm);
    let mut neg_b = Fp::zero(); bls12_opp(&mut neg_b, &x.c1);
    bls12_mul(&mut out.c1, &neg_b, &norm);
}
#[inline]
pub fn bls12_Fp2_mul_xi(mut out: &mut Fp2, x: &Fp2) {
    let mut tmp: Fp2 = Fp2::zero();
    bls12_felem_copy(&mut tmp.c0, &x.c0);
    bls12_felem_copy(&mut tmp.c1, &x.c1);
    bls12_sub(&mut out.c0, &tmp.c0, &tmp.c1);
    bls12_add(&mut out.c1, &tmp.c0, &tmp.c1);
}

#[inline]
pub fn bls12_Fp6_felem_copy(mut out: &mut Fp6, x: &Fp6) {
    bls12_Fp2_felem_copy(&mut out.c0, &x.c0);
    bls12_Fp2_felem_copy(&mut out.c1, &x.c1);
    bls12_Fp2_felem_copy(&mut out.c2, &x.c2);
}

#[inline]
pub fn bls12_Fp6_add(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bls12_Fp6_felem_copy(&mut allocx, &inx);
    bls12_Fp6_felem_copy(&mut allocy, &iny);
    bls12_Fp2_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bls12_Fp2_add(&mut out.c1, &allocx.c1, &allocy.c1);
    bls12_Fp2_add(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bls12_Fp6_sub(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bls12_Fp6_felem_copy(&mut allocx, &inx);
    bls12_Fp6_felem_copy(&mut allocy, &iny);
    bls12_Fp2_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bls12_Fp2_sub(&mut out.c1, &allocx.c1, &allocy.c1);
    bls12_Fp2_sub(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bls12_Fp6_opp(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    bls12_Fp6_felem_copy(&mut allocx, &x);
    bls12_Fp2_opp(&mut out.c0, &allocx.c0);
    bls12_Fp2_opp(&mut out.c1, &allocx.c1);
    bls12_Fp2_opp(&mut out.c2, &allocx.c2);
}

#[inline]
pub fn bls12_Fp6_mul(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    let mut a0b0: Fp2 = Fp2::zero();
    let mut a1b1: Fp2 = Fp2::zero();
    let mut a2b2: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    let mut u: Fp2 = Fp2::zero();
    bls12_Fp6_felem_copy(&mut allocx, &inx);
    bls12_Fp6_felem_copy(&mut allocy, &iny);
    bls12_Fp2_mul(&mut a0b0, &allocx.c0, &allocy.c0);
    bls12_Fp2_mul(&mut a1b1, &allocx.c1, &allocy.c1);
    bls12_Fp2_mul(&mut a2b2, &allocx.c2, &allocy.c2);
    bls12_Fp2_add(&mut t, &allocx.c1, &allocx.c2);
    bls12_Fp2_add(&mut u, &allocy.c1, &allocy.c2);
    let __ac0 = t.clone();
    bls12_Fp2_mul(&mut t, &__ac0, &u);
    let __ac1 = t.clone();
    bls12_Fp2_sub(&mut t, &__ac1, &a1b1);
    let __ac2 = t.clone();
    bls12_Fp2_sub(&mut t, &__ac2, &a2b2);
    let __ac3 = t.clone();
    bls12_Fp2_mul_xi(&mut t, &__ac3);
    bls12_Fp2_add(&mut out.c0, &a0b0, &t);
    bls12_Fp2_add(&mut t, &allocx.c0, &allocx.c1);
    bls12_Fp2_add(&mut u, &allocy.c0, &allocy.c1);
    let __ac4 = t.clone();
    bls12_Fp2_mul(&mut t, &__ac4, &u);
    let __ac5 = t.clone();
    bls12_Fp2_sub(&mut t, &__ac5, &a0b0);
    let __ac6 = t.clone();
    bls12_Fp2_sub(&mut t, &__ac6, &a1b1);
    bls12_Fp2_mul_xi(&mut u, &a2b2);
    bls12_Fp2_add(&mut out.c1, &t, &u);
    bls12_Fp2_add(&mut t, &allocx.c0, &allocx.c2);
    bls12_Fp2_add(&mut u, &allocy.c0, &allocy.c2);
    let __ac7 = t.clone();
    bls12_Fp2_mul(&mut t, &__ac7, &u);
    let __ac8 = t.clone();
    bls12_Fp2_sub(&mut t, &__ac8, &a0b0);
    let __ac9 = t.clone();
    bls12_Fp2_sub(&mut t, &__ac9, &a2b2);
    bls12_Fp2_add(&mut out.c2, &t, &a1b1);
}

#[inline]
pub fn bls12_Fp6_square(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut s0: Fp2 = Fp2::zero();
    let mut s1: Fp2 = Fp2::zero();
    let mut s2: Fp2 = Fp2::zero();
    let mut s3: Fp2 = Fp2::zero();
    let mut s4: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    bls12_Fp6_felem_copy(&mut allocx, &x);
    bls12_Fp2_square(&mut s0, &allocx.c0);
    bls12_Fp2_mul(&mut t, &allocx.c0, &allocx.c1);
    bls12_Fp2_add(&mut s1, &t, &t);
    bls12_Fp2_sub(&mut t, &allocx.c0, &allocx.c1);
    let __ac0 = t.clone();
    bls12_Fp2_add(&mut t, &__ac0, &allocx.c2);
    bls12_Fp2_square(&mut s2, &t);
    bls12_Fp2_mul(&mut t, &allocx.c1, &allocx.c2);
    bls12_Fp2_add(&mut s3, &t, &t);
    bls12_Fp2_square(&mut s4, &allocx.c2);
    bls12_Fp2_mul_xi(&mut t, &s3);
    bls12_Fp2_add(&mut out.c0, &s0, &t);
    bls12_Fp2_mul_xi(&mut t, &s4);
    bls12_Fp2_add(&mut out.c1, &s1, &t);
    bls12_Fp2_add(&mut t, &s1, &s2);
    let __ac1 = t.clone();
    bls12_Fp2_add(&mut t, &__ac1, &s3);
    let __ac2 = t.clone();
    bls12_Fp2_sub(&mut t, &__ac2, &s0);
    bls12_Fp2_sub(&mut out.c2, &t, &s4);
}

#[inline]
pub fn bls12_Fp6_inv(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut vA: Fp2 = Fp2::zero();
    let mut vB: Fp2 = Fp2::zero();
    let mut vC: Fp2 = Fp2::zero();
    let mut t1: Fp2 = Fp2::zero();
    let mut t2: Fp2 = Fp2::zero();
    let mut t3: Fp2 = Fp2::zero();
    bls12_Fp6_felem_copy(&mut allocx, &x);
    bls12_Fp2_square(&mut t1, &allocx.c0);
    bls12_Fp2_mul(&mut t2, &allocx.c1, &allocx.c2);
    bls12_Fp2_mul_xi(&mut t3, &t2);
    bls12_Fp2_sub(&mut vA, &t1, &t3);
    bls12_Fp2_square(&mut t1, &allocx.c2);
    bls12_Fp2_mul_xi(&mut t3, &t1);
    bls12_Fp2_mul(&mut t2, &allocx.c0, &allocx.c1);
    bls12_Fp2_sub(&mut vB, &t3, &t2);
    bls12_Fp2_square(&mut t1, &allocx.c1);
    bls12_Fp2_mul(&mut t2, &allocx.c0, &allocx.c2);
    bls12_Fp2_sub(&mut vC, &t1, &t2);
    bls12_Fp2_mul(&mut t1, &allocx.c0, &vA);
    bls12_Fp2_mul(&mut t2, &allocx.c2, &vB);
    bls12_Fp2_mul(&mut t3, &allocx.c1, &vC);
    let __ac0 = t2.clone();
    bls12_Fp2_add(&mut t2, &__ac0, &t3);
    let __ac1 = t2.clone();
    bls12_Fp2_mul_xi(&mut t2, &__ac1);
    let __ac2 = t1.clone();
    bls12_Fp2_add(&mut t1, &__ac2, &t2);
    let __ac3 = t1.clone();
    bls12_Fp2_inv(&mut t1, &__ac3);
    bls12_Fp2_mul(&mut out.c0, &vA, &t1);
    bls12_Fp2_mul(&mut out.c1, &vB, &t1);
    bls12_Fp2_mul(&mut out.c2, &vC, &t1);
}

#[inline]
pub fn bls12_Fp6_add_nocopy(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    bls12_Fp2_add(&mut out.c0, &inx.c0, &iny.c0);
    bls12_Fp2_add(&mut out.c1, &inx.c1, &iny.c1);
    bls12_Fp2_add(&mut out.c2, &inx.c2, &iny.c2);
}

#[inline]
pub fn bls12_Fp6_sub_nocopy(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    bls12_Fp2_sub(&mut out.c0, &inx.c0, &iny.c0);
    bls12_Fp2_sub(&mut out.c1, &inx.c1, &iny.c1);
    bls12_Fp2_sub(&mut out.c2, &inx.c2, &iny.c2);
}

#[inline]
pub fn bls12_Fp6_mul_by_v(mut out: &mut Fp6, x: &Fp6) {
    let mut tmp: Fp6 = Fp6::zero();
    bls12_Fp6_felem_copy(&mut tmp, &x);
    bls12_Fp2_mul_xi(&mut out.c0, &tmp.c2);
    bls12_Fp2_felem_copy(&mut out.c1, &tmp.c0);
    bls12_Fp2_felem_copy(&mut out.c2, &tmp.c1);
}

#[inline]
pub fn bls12_Fp12_felem_copy(mut out: &mut Fp12, x: &Fp12) {
    bls12_Fp6_felem_copy(&mut out.c0, &x.c0);
    bls12_Fp6_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls12_Fp12_add(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bls12_Fp12_felem_copy(&mut ax, &inx);
    bls12_Fp12_felem_copy(&mut ay, &iny);
    bls12_Fp6_add_nocopy(&mut out.c0, &ax.c0, &ay.c0);
    bls12_Fp6_add_nocopy(&mut out.c1, &ax.c1, &ay.c1);
}

#[inline]
pub fn bls12_Fp12_sub(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bls12_Fp12_felem_copy(&mut ax, &inx);
    bls12_Fp12_felem_copy(&mut ay, &iny);
    bls12_Fp6_sub_nocopy(&mut out.c0, &ax.c0, &ay.c0);
    bls12_Fp6_sub_nocopy(&mut out.c1, &ax.c1, &ay.c1);
}

#[inline]
pub fn bls12_Fp12_opp(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bls12_Fp12_felem_copy(&mut allocx, &x);
    bls12_Fp6_opp(&mut out.c0, &allocx.c0);
    bls12_Fp6_opp(&mut out.c1, &allocx.c1);
}

#[inline]
pub fn bls12_Fp12_conjugate(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bls12_Fp12_felem_copy(&mut allocx, &x);
    bls12_Fp6_felem_copy(&mut out.c0, &allocx.c0);
    bls12_Fp6_opp(&mut out.c1, &allocx.c1);
}

#[inline]
pub fn bls12_Fp12_mul(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bls12_Fp12_felem_copy(&mut ax, &inx);
    bls12_Fp12_felem_copy(&mut ay, &iny);
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bls12_Fp6_mul(&mut v0, &ax.c0, &ay.c0);
    bls12_Fp6_mul(&mut v1, &ax.c1, &ay.c1);
    bls12_Fp6_add_nocopy(&mut t, &ax.c0, &ax.c1);
    bls12_Fp6_add_nocopy(&mut u, &ay.c0, &ay.c1);
    let __ac0 = t.clone();
    bls12_Fp6_mul(&mut t, &__ac0, &u);
    bls12_Fp6_mul_by_v(&mut u, &v1);
    bls12_Fp6_add_nocopy(&mut out.c0, &v0, &u);
    let __ac1 = t.clone();
    bls12_Fp6_sub_nocopy(&mut t, &__ac1, &v0);
    bls12_Fp6_sub_nocopy(&mut out.c1, &t, &v1);
}

#[inline]
pub fn bls12_Fp12_square(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bls12_Fp12_felem_copy(&mut allocx, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    let mut t2: Fp6 = Fp6::zero();
    bls12_Fp6_square(&mut t0, &allocx.c0);
    bls12_Fp6_square(&mut t1, &allocx.c1);
    bls12_Fp6_mul(&mut t2, &allocx.c0, &allocx.c1);
    let __ac0 = t1.clone();
    bls12_Fp6_mul_by_v(&mut t1, &__ac0);
    bls12_Fp6_add_nocopy(&mut out.c0, &t0, &t1);
    bls12_Fp6_add_nocopy(&mut out.c1, &t2, &t2);
}

#[inline]
pub fn bls12_Fp12_inv(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bls12_Fp12_felem_copy(&mut allocx, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    bls12_Fp6_square(&mut t0, &allocx.c0);
    bls12_Fp6_square(&mut t1, &allocx.c1);
    let __ac0 = t1.clone();
    bls12_Fp6_mul_by_v(&mut t1, &__ac0);
    let __ac1 = t0.clone();
    bls12_Fp6_sub_nocopy(&mut t0, &__ac1, &t1);
    let __ac2 = t0.clone();
    bls12_Fp6_inv(&mut t0, &__ac2);
    bls12_Fp6_mul(&mut out.c0, &allocx.c0, &t0);
    bls12_Fp6_mul(&mut out.c1, &allocx.c1, &t0);
    let __ac3 = out.c1.clone();
    bls12_Fp6_opp(&mut out.c1, &__ac3);
}

#[inline]
pub fn bls12_Fp12_add_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    bls12_Fp6_add_nocopy(&mut out.c0, &inx.c0, &iny.c0);
    bls12_Fp6_add_nocopy(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bls12_Fp12_sub_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    bls12_Fp6_sub_nocopy(&mut out.c0, &inx.c0, &iny.c0);
    bls12_Fp6_sub_nocopy(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bls12_Fp12_mul_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bls12_Fp6_mul(&mut v0, &inx.c0, &iny.c0);
    bls12_Fp6_mul(&mut v1, &inx.c1, &iny.c1);
    bls12_Fp6_add_nocopy(&mut t, &inx.c0, &inx.c1);
    bls12_Fp6_add_nocopy(&mut u, &iny.c0, &iny.c1);
    let __ac0 = t.clone();
    bls12_Fp6_mul(&mut t, &__ac0, &u);
    bls12_Fp6_mul_by_v(&mut u, &v1);
    bls12_Fp6_add_nocopy(&mut out.c0, &v0, &u);
    let __ac1 = t.clone();
    bls12_Fp6_sub_nocopy(&mut t, &__ac1, &v0);
    bls12_Fp6_sub_nocopy(&mut out.c1, &t, &v1);
}

#[inline]
pub fn bls12_Fp2_conjugate(mut out: &mut Fp2, x: &Fp2) {
    bls12_felem_copy(&mut out.c0, &x.c0);
    bls12_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls12_Fp6_mul_fp2(mut out: &mut Fp6, x: &Fp6, s: &Fp2) {
    let mut s_copy: Fp2 = Fp2::zero();
    bls12_Fp2_felem_copy(&mut s_copy, &s);
    bls12_Fp2_mul(&mut out.c0, &x.c0, &s_copy);
    bls12_Fp2_mul(&mut out.c1, &x.c1, &s_copy);
    bls12_Fp2_mul(&mut out.c2, &x.c2, &s_copy);
}

#[inline]
pub fn bls12_Fp6_frobenius(mut out: &mut Fp6, x: &Fp6, gamma1: &Fp2, gamma2: &Fp2) {
    let mut tmp: Fp6 = Fp6::zero();
    bls12_Fp2_conjugate(&mut tmp.c0, &x.c0);
    bls12_Fp2_conjugate(&mut tmp.c1, &x.c1);
    bls12_Fp2_conjugate(&mut tmp.c2, &x.c2);
    bls12_Fp2_felem_copy(&mut out.c0, &tmp.c0);
    bls12_Fp2_mul(&mut out.c1, &tmp.c1, &gamma1);
    bls12_Fp2_mul(&mut out.c2, &tmp.c2, &gamma2);
}

#[inline]
pub fn bls12_Fp6_frobenius_p2(mut out: &mut Fp6, x: &Fp6, gamma1_p2: &Fp2, gamma2_p2: &Fp2) {
    bls12_Fp2_felem_copy(&mut out.c0, &x.c0);
    bls12_Fp2_mul(&mut out.c1, &x.c1, &gamma1_p2);
    bls12_Fp2_mul(&mut out.c2, &x.c2, &gamma2_p2);
}

#[inline]
pub fn bls12_Fp12_frobenius(mut out: &mut Fp12, x: &Fp12, gamma1: &Fp2, gamma2: &Fp2, w_frob_c1: &Fp2) {
    bls12_Fp6_frobenius(&mut out.c0, &x.c0, &gamma1, &gamma2);
    bls12_Fp6_frobenius(&mut out.c1, &x.c1, &gamma1, &gamma2);
    let __ac0 = out.c1.clone();
    bls12_Fp6_mul_fp2(&mut out.c1, &__ac0, &w_frob_c1);
}

#[inline]
pub fn bls12_Fp12_frobenius_p2(mut out: &mut Fp12, x: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    bls12_Fp6_frobenius_p2(&mut out.c0, &x.c0, &gamma1_p2, &gamma2_p2);
    bls12_Fp6_frobenius_p2(&mut out.c1, &x.c1, &gamma1_p2, &gamma2_p2);
    let __ac0 = out.c1.clone();
    bls12_Fp6_mul_fp2(&mut out.c1, &__ac0, &w_frob_p2_c1);
}

#[inline]
pub fn bls12_Fp12_frobenius_p3(mut out: &mut Fp12, x: &Fp12, gamma1: &Fp12, gamma2: &Fp12, gamma1_p2: &Fp12, gamma2_p2: &Fp12, w_frob_c1: &Fp12, w_frob_p2_c1: &Fp12) {
    let mut tmp: Fp12 = Fp12::zero();
    bls12_Fp6_frobenius_p2(&mut tmp.c0, &x.c0, &gamma1_p2.c0.c0, &gamma2_p2.c0.c0);
    bls12_Fp6_frobenius_p2(&mut tmp.c1, &x.c1, &gamma1_p2.c0.c0, &gamma2_p2.c0.c0);
    let __ac0 = tmp.c1.clone();
    bls12_Fp6_mul_fp2(&mut tmp.c1, &__ac0, &w_frob_p2_c1.c0.c0);
    bls12_Fp6_frobenius(&mut out.c0, &tmp.c0, &gamma1.c0.c0, &gamma2.c0.c0);
    bls12_Fp6_frobenius(&mut out.c1, &tmp.c1, &gamma1.c0.c0, &gamma2.c0.c0);
    let __ac1 = out.c1.clone();
    bls12_Fp6_mul_fp2(&mut out.c1, &__ac1, &w_frob_c1.c0.c0);
}

#[inline]
pub fn bls12_Fp2_mul_fp(mut out: &mut Fp2, x: &Fp2, s: &Fp) {
    bls12_mul(&mut out.c0, &x.c0, &s);
    bls12_mul(&mut out.c1, &x.c1, &s);
}

#[inline]
pub fn bls12_make_line(mut out: &mut Fp12, lam: &Fp2, x_t: &Fp2, y_t: &Fp2, x_p: &Fp, y_p: &Fp) {
    let mut tmp: Fp2 = Fp2::zero();
    bls12_Fp2_mul(&mut out.c0.c0, &lam, &x_t);
    let __ac0 = out.c0.c0.clone();
    bls12_Fp2_sub(&mut out.c0.c0, &__ac0, &y_t);
    bls12_Fp2_mul_fp(&mut tmp, &lam, &x_p);
    bls12_Fp2_opp(&mut out.c0.c1, &tmp);
    bls12_from_word(&mut out.c0.c2.c0, 0u64);
    bls12_from_word(&mut out.c0.c2.c1, 0u64);
    bls12_from_word(&mut out.c1.c0.c0, 0u64);
    bls12_from_word(&mut out.c1.c0.c1, 0u64);
    bls12_felem_copy(&mut out.c1.c1.c0, &y_p);
    bls12_from_word(&mut out.c1.c1.c1, 0u64);
    bls12_from_word(&mut out.c1.c2.c0, 0u64);
    bls12_from_word(&mut out.c1.c2.c1, 0u64);
}

#[inline]
pub fn bls12_load_gamma1_p2(mut out: &mut Fp2) {
    out.c0.0[0] = 3526659474838938856u64;
    out.c0.0[1] = 17562030475567847978u64;
    out.c0.0[2] = 1632777218702014455u64;
    out.c0.0[3] = 14009062335050482331u64;
    out.c0.0[4] = 3906511377122991214u64;
    out.c0.0[5] = 368068849512964448u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls12_load_gamma2_p2(mut out: &mut Fp2) {
    out.c0.0[0] = 14772873186050699377u64;
    out.c0.0[1] = 6749526151121446354u64;
    out.c0.0[2] = 6372666795664677781u64;
    out.c0.0[3] = 10283423008382700446u64;
    out.c0.0[4] = 286397964926079186u64;
    out.c0.0[5] = 1796971870900422465u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls12_load_w_frob_p2_c1(mut out: &mut Fp2) {
    out.c0.0[0] = 17076301903736715834u64;
    out.c0.0[1] = 13907359434105313836u64;
    out.c0.0[2] = 1063007777899403918u64;
    out.c0.0[3] = 15402659025741563681u64;
    out.c0.0[4] = 5125705813544623108u64;
    out.c0.0[5] = 76826746747117401u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls12_load_gamma1(mut out: &mut Fp2) {
    out.c0.0[0] = 0u64;
    out.c0.0[1] = 0u64;
    out.c0.0[2] = 0u64;
    out.c0.0[3] = 0u64;
    out.c0.0[4] = 0u64;
    out.c0.0[5] = 0u64;
    out.c1.0[0] = 14772873186050699377u64;
    out.c1.0[1] = 6749526151121446354u64;
    out.c1.0[2] = 6372666795664677781u64;
    out.c1.0[3] = 10283423008382700446u64;
    out.c1.0[4] = 286397964926079186u64;
    out.c1.0[5] = 1796971870900422465u64;
}

#[inline]
pub fn bls12_load_gamma2(mut out: &mut Fp2) {
    out.c0.0[0] = 9875771541238924739u64;
    out.c0.0[1] = 3094855109658912213u64;
    out.c0.0[2] = 5802897354862067244u64;
    out.c0.0[3] = 11677019699073781796u64;
    out.c0.0[4] = 1505592401347711080u64;
    out.c0.0[5] = 1505729768134575418u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
    out.c1.0[4] = 0u64;
    out.c1.0[5] = 0u64;
}

#[inline]
pub fn bls12_load_w_frob_c1(mut out: &mut Fp2) {
    out.c0.0[0] = 506819140503852133u64;
    out.c0.0[1] = 14297063575771579155u64;
    out.c0.0[2] = 10946065744702939791u64;
    out.c0.0[3] = 11771194236670323182u64;
    out.c0.0[4] = 2081670087578406477u64;
    out.c0.0[5] = 644615147456521963u64;
    out.c1.0[0] = 12895611875574011462u64;
    out.c1.0[1] = 6359822009455181036u64;
    out.c1.0[2] = 14936352902570693524u64;
    out.c1.0[3] = 13914887797453940944u64;
    out.c1.0[4] = 3330433690892295817u64;
    out.c1.0[5] = 1229183470191017903u64;
}

#[inline]
pub fn bls12_load_w_frob_p3_c1(mut out: &mut Fp2) {
    out.c0.0[0] = 4480897313486445265u64;
    out.c0.0[1] = 4797496051193971075u64;
    out.c0.0[2] = 4046559893315008306u64;
    out.c0.0[3] = 10569151167044009496u64;
    out.c0.0[4] = 2123814803385151673u64;
    out.c0.0[5] = 852749317591686856u64;
    out.c1.0[0] = 8921533702591418330u64;
    out.c1.0[1] = 15859389534032789116u64;
    out.c1.0[2] = 3389114680249073393u64;
    out.c1.0[3] = 15116930867080254631u64;
    out.c1.0[4] = 3288288975085550621u64;
    out.c1.0[5] = 1021049300055853010u64;
}

#[inline]
pub fn bls12_Fp12_pow_x(mut out: &mut Fp12, base: &Fp12) {
    let mut result: Fp12 = Fp12::zero();
    bls12_Fp12_felem_copy(&mut result, &base);
    let mut i: u64;
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let __ac0 = result.clone();
        bls12_Fp12_square(&mut result, &__ac0);
        let mut bit: u64;
        bit = ((15132376222941642752u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac1 = result.clone();
            bls12_Fp12_mul_nocopy(&mut result, &__ac1, &base);
        } else {
        }
    }
    bls12_Fp12_felem_copy(&mut out, &result);
}

#[inline]
pub fn bls12_final_exp_hard_dsd(mut out: &mut Fp12, f: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    let mut t0: Fp12 = Fp12::zero();
    let mut t1: Fp12 = Fp12::zero();
    let mut t2: Fp12 = Fp12::zero();
    let mut t3: Fp12 = Fp12::zero();
    let mut result: Fp12 = Fp12::zero();
    let mut base: Fp12 = Fp12::zero();
    let mut gamma1: Fp2 = Fp2::zero();
    let mut gamma2: Fp2 = Fp2::zero();
    let mut w_frob_c1: Fp2 = Fp2::zero();
    let mut cyc_t0: Fp6 = Fp6::zero();
    let mut cyc_t1: Fp6 = Fp6::zero();
    let mut cyc_one: Fp = Fp::zero();
    bls12_from_word(&mut cyc_one, 1u64);
    bls12_load_gamma1(&mut gamma1, );
    bls12_load_gamma2(&mut gamma2, );
    bls12_load_w_frob_c1(&mut w_frob_c1, );
    bls12_Fp12_square(&mut t0, &f);
    bls12_from_word(&mut result.c0.c0.c0, 1u64);
    bls12_from_word(&mut result.c0.c0.c1, 0u64);
    bls12_from_word(&mut result.c0.c1.c0, 0u64);
    bls12_from_word(&mut result.c0.c1.c1, 0u64);
    bls12_from_word(&mut result.c0.c2.c0, 0u64);
    bls12_from_word(&mut result.c0.c2.c1, 0u64);
    bls12_from_word(&mut result.c1.c0.c0, 0u64);
    bls12_from_word(&mut result.c1.c0.c1, 0u64);
    bls12_from_word(&mut result.c1.c1.c0, 0u64);
    bls12_from_word(&mut result.c1.c1.c1, 0u64);
    bls12_from_word(&mut result.c1.c2.c0, 0u64);
    bls12_from_word(&mut result.c1.c2.c1, 0u64);
    bls12_Fp12_felem_copy(&mut base, &t0);
    let mut i: u64;
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        bls12_Fp6_mul(&mut cyc_t0, &result.c1, &result.c1);
        bls12_Fp6_mul(&mut cyc_t1, &result.c0, &result.c1);
        let __ac0 = cyc_t0.clone();
        bls12_Fp6_mul_by_v(&mut cyc_t0, &__ac0);
        bls12_Fp6_add_nocopy(&mut result.c0, &cyc_t0, &cyc_t0);
        let __ac1 = result.c0.c0.c0.clone();
        bls12_add(&mut result.c0.c0.c0, &__ac1, &cyc_one);
        bls12_Fp6_add_nocopy(&mut result.c1, &cyc_t1, &cyc_t1);
        let mut bit: u64;
        bit = ((7566188111470821376u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac2 = result.clone();
            bls12_Fp12_mul_nocopy(&mut result, &__ac2, &base);
        } else {
        }
    }
    bls12_Fp12_conjugate(&mut t1, &result);
    bls12_Fp12_conjugate(&mut t2, &f);
    let __ac3 = t1.clone();
    bls12_Fp12_mul_nocopy(&mut t1, &__ac3, &t2);
    bls12_Fp12_felem_copy(&mut result, &t1);
    bls12_Fp12_felem_copy(&mut base, &t1);
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        bls12_Fp6_mul(&mut cyc_t0, &result.c1, &result.c1);
        bls12_Fp6_mul(&mut cyc_t1, &result.c0, &result.c1);
        let __ac4 = cyc_t0.clone();
        bls12_Fp6_mul_by_v(&mut cyc_t0, &__ac4);
        bls12_Fp6_add_nocopy(&mut result.c0, &cyc_t0, &cyc_t0);
        let __ac5 = result.c0.c0.c0.clone();
        bls12_add(&mut result.c0.c0.c0, &__ac5, &cyc_one);
        bls12_Fp6_add_nocopy(&mut result.c1, &cyc_t1, &cyc_t1);
        let mut bit: u64;
        bit = ((15132376222941642752u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac6 = result.clone();
            bls12_Fp12_mul_nocopy(&mut result, &__ac6, &base);
        } else {
        }
    }
    bls12_Fp12_conjugate(&mut t2, &result);
    let __ac7 = t1.clone();
    bls12_Fp12_conjugate(&mut t1, &__ac7);
    let __ac8 = t1.clone();
    bls12_Fp12_mul_nocopy(&mut t1, &__ac8, &t2);
    bls12_Fp12_felem_copy(&mut result, &t1);
    bls12_Fp12_felem_copy(&mut base, &t1);
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        bls12_Fp6_mul(&mut cyc_t0, &result.c1, &result.c1);
        bls12_Fp6_mul(&mut cyc_t1, &result.c0, &result.c1);
        let __ac9 = cyc_t0.clone();
        bls12_Fp6_mul_by_v(&mut cyc_t0, &__ac9);
        bls12_Fp6_add_nocopy(&mut result.c0, &cyc_t0, &cyc_t0);
        let __ac10 = result.c0.c0.c0.clone();
        bls12_add(&mut result.c0.c0.c0, &__ac10, &cyc_one);
        bls12_Fp6_add_nocopy(&mut result.c1, &cyc_t1, &cyc_t1);
        let mut bit: u64;
        bit = ((15132376222941642752u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac11 = result.clone();
            bls12_Fp12_mul_nocopy(&mut result, &__ac11, &base);
        } else {
        }
    }
    bls12_Fp12_conjugate(&mut t2, &result);
    let __ac12 = t1.clone();
    bls12_Fp12_frobenius(&mut t1, &__ac12, &gamma1, &gamma2, &w_frob_c1);
    let __ac13 = t1.clone();
    bls12_Fp12_mul_nocopy(&mut t1, &__ac13, &t2);
    bls12_Fp12_mul_nocopy(&mut t3, &f, &t0);
    bls12_Fp12_felem_copy(&mut result, &t1);
    bls12_Fp12_felem_copy(&mut base, &t1);
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        bls12_Fp6_mul(&mut cyc_t0, &result.c1, &result.c1);
        bls12_Fp6_mul(&mut cyc_t1, &result.c0, &result.c1);
        let __ac14 = cyc_t0.clone();
        bls12_Fp6_mul_by_v(&mut cyc_t0, &__ac14);
        bls12_Fp6_add_nocopy(&mut result.c0, &cyc_t0, &cyc_t0);
        let __ac15 = result.c0.c0.c0.clone();
        bls12_add(&mut result.c0.c0.c0, &__ac15, &cyc_one);
        bls12_Fp6_add_nocopy(&mut result.c1, &cyc_t1, &cyc_t1);
        let mut bit: u64;
        bit = ((15132376222941642752u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac16 = result.clone();
            bls12_Fp12_mul_nocopy(&mut result, &__ac16, &base);
        } else {
        }
    }
    bls12_Fp12_conjugate(&mut t0, &result);
    bls12_Fp12_felem_copy(&mut result, &t0);
    bls12_Fp12_felem_copy(&mut base, &t0);
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        bls12_Fp6_mul(&mut cyc_t0, &result.c1, &result.c1);
        bls12_Fp6_mul(&mut cyc_t1, &result.c0, &result.c1);
        let __ac17 = cyc_t0.clone();
        bls12_Fp6_mul_by_v(&mut cyc_t0, &__ac17);
        bls12_Fp6_add_nocopy(&mut result.c0, &cyc_t0, &cyc_t0);
        let __ac18 = result.c0.c0.c0.clone();
        bls12_add(&mut result.c0.c0.c0, &__ac18, &cyc_one);
        bls12_Fp6_add_nocopy(&mut result.c1, &cyc_t1, &cyc_t1);
        let mut bit: u64;
        bit = ((15132376222941642752u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac19 = result.clone();
            bls12_Fp12_mul_nocopy(&mut result, &__ac19, &base);
        } else {
        }
    }
    bls12_Fp12_conjugate(&mut t2, &result);
    bls12_Fp12_frobenius_p2(&mut t0, &t1, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
    let __ac20 = t1.clone();
    bls12_Fp12_conjugate(&mut t1, &__ac20);
    let __ac21 = t1.clone();
    bls12_Fp12_mul_nocopy(&mut t1, &__ac21, &t2);
    let __ac22 = t1.clone();
    bls12_Fp12_mul_nocopy(&mut t1, &__ac22, &t0);
    bls12_Fp12_mul_nocopy(&mut out, &t3, &t1);
}

#[inline]
pub fn bls12_miller_loop(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut f: Fp12 = Fp12::zero();
    let mut t_x: Fp2 = Fp2::zero();
    let mut t_y: Fp2 = Fp2::zero();
    let mut lambda: Fp2 = Fp2::zero();
    let mut tmp1: Fp2 = Fp2::zero();
    let mut tmp2: Fp2 = Fp2::zero();
    let mut line: Fp12 = Fp12::zero();
    bls12_from_word(&mut f.c0.c0.c0, 1u64);
    bls12_from_word(&mut f.c0.c0.c1, 0u64);
    bls12_from_word(&mut f.c0.c1.c0, 0u64);
    bls12_from_word(&mut f.c0.c1.c1, 0u64);
    bls12_from_word(&mut f.c0.c2.c0, 0u64);
    bls12_from_word(&mut f.c0.c2.c1, 0u64);
    bls12_from_word(&mut f.c1.c0.c0, 0u64);
    bls12_from_word(&mut f.c1.c0.c1, 0u64);
    bls12_from_word(&mut f.c1.c1.c0, 0u64);
    bls12_from_word(&mut f.c1.c1.c1, 0u64);
    bls12_from_word(&mut f.c1.c2.c0, 0u64);
    bls12_from_word(&mut f.c1.c2.c1, 0u64);
    bls12_Fp2_felem_copy(&mut t_x, &q_x);
    bls12_Fp2_felem_copy(&mut t_y, &q_y);
    let mut i: u64;
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        bls12_Fp2_square(&mut tmp1, &t_x);
        bls12_Fp2_add(&mut lambda, &tmp1, &tmp1);
        let __ac0 = lambda.clone();
        bls12_Fp2_add(&mut lambda, &__ac0, &tmp1);
        bls12_Fp2_add(&mut tmp1, &t_y, &t_y);
        let __ac1 = tmp1.clone();
        bls12_Fp2_inv(&mut tmp1, &__ac1);
        let __ac2 = lambda.clone();
        bls12_Fp2_mul(&mut lambda, &__ac2, &tmp1);
        bls12_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
        let __ac3 = f.clone();
        bls12_Fp12_square(&mut f, &__ac3);
        let __ac4 = f.clone();
        bls12_Fp12_mul_nocopy(&mut f, &__ac4, &line);
        bls12_Fp2_square(&mut tmp1, &lambda);
        let __ac5 = tmp1.clone();
        bls12_Fp2_sub(&mut tmp1, &__ac5, &t_x);
        bls12_Fp2_sub(&mut tmp2, &tmp1, &t_x);
        bls12_Fp2_sub(&mut tmp1, &t_x, &tmp2);
        let __ac6 = tmp1.clone();
        bls12_Fp2_mul(&mut tmp1, &lambda, &__ac6);
        let __ac7 = t_y.clone();
        bls12_Fp2_sub(&mut t_y, &tmp1, &__ac7);
        bls12_Fp2_felem_copy(&mut t_x, &tmp2);
        let mut bit: u64;
        bit = ((15132376222941642752u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            bls12_Fp2_sub(&mut tmp1, &q_y, &t_y);
            bls12_Fp2_sub(&mut tmp2, &q_x, &t_x);
            let __ac8 = tmp2.clone();
            bls12_Fp2_inv(&mut tmp2, &__ac8);
            bls12_Fp2_mul(&mut lambda, &tmp1, &tmp2);
            bls12_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
            let __ac9 = f.clone();
            bls12_Fp12_mul_nocopy(&mut f, &__ac9, &line);
            bls12_Fp2_square(&mut tmp1, &lambda);
            let __ac10 = tmp1.clone();
            bls12_Fp2_sub(&mut tmp1, &__ac10, &t_x);
            bls12_Fp2_sub(&mut tmp2, &tmp1, &q_x);
            bls12_Fp2_sub(&mut tmp1, &t_x, &tmp2);
            let __ac11 = tmp1.clone();
            bls12_Fp2_mul(&mut tmp1, &lambda, &__ac11);
            let __ac12 = t_y.clone();
            bls12_Fp2_sub(&mut t_y, &tmp1, &__ac12);
            bls12_Fp2_felem_copy(&mut t_x, &tmp2);
        } else {
        }
    }
    bls12_Fp12_felem_copy(&mut out, &f);
}

#[inline]
pub fn bls12_final_exp(mut out: &mut Fp12, f: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    let mut result: Fp12 = Fp12::zero();
    let mut tmp: Fp12 = Fp12::zero();
    bls12_Fp12_conjugate(&mut result, &f);
    bls12_Fp12_inv(&mut tmp, &f);
    let __ac0 = result.clone();
    bls12_Fp12_mul_nocopy(&mut result, &__ac0, &tmp);
    bls12_Fp12_frobenius_p2(&mut tmp, &result, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
    let __ac1 = result.clone();
    bls12_Fp12_mul_nocopy(&mut result, &tmp, &__ac1);
    bls12_final_exp_hard_dsd(&mut out, &result, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
}

#[inline]
pub fn bls12_Fp12_mul_by_024(mut out: &mut Fp12, a: &Fp12, ell0: &Fp2, ell2: &Fp2, ell4: &Fp2) {
    let mut b: Fp6 = Fp6::zero();
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    let mut t2: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bls12_Fp2_felem_copy(&mut b.c0, &ell0);
    bls12_Fp2_felem_copy(&mut b.c1, &ell2);
    bls12_from_word(&mut b.c2.c0, 0u64);
    bls12_from_word(&mut b.c2.c1, 0u64);
    bls12_Fp6_mul(&mut t0, &a.c0, &b);
    bls12_Fp6_mul_fp2(&mut t1, &a.c1, &ell4);
    bls12_Fp6_mul_by_v(&mut u, &t1);
    bls12_Fp6_add_nocopy(&mut out.c0, &t0, &u);
    bls12_Fp6_mul(&mut t2, &a.c1, &b);
    bls12_Fp6_mul_fp2(&mut t1, &a.c0, &ell4);
    bls12_Fp6_add_nocopy(&mut out.c1, &t2, &t1);
}

#[inline]
pub fn bls12_miller_loop_proj(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut f: Fp12 = Fp12::zero();
    let mut t_x: Fp2 = Fp2::zero();
    let mut t_y: Fp2 = Fp2::zero();
    let mut t_z: Fp2 = Fp2::zero();
    let mut ell0: Fp2 = Fp2::zero();
    let mut ellVW: Fp2 = Fp2::zero();
    let mut ellVV: Fp2 = Fp2::zero();
    let mut tmp1: Fp2 = Fp2::zero();
    let mut tmp2: Fp2 = Fp2::zero();
    let mut A: Fp2 = Fp2::zero();
    let mut B: Fp2 = Fp2::zero();
    let mut C: Fp2 = Fp2::zero();
    let mut D: Fp2 = Fp2::zero();
    let mut E: Fp2 = Fp2::zero();
    bls12_from_word(&mut f.c0.c0.c0, 1u64);
    bls12_from_word(&mut f.c0.c0.c1, 0u64);
    bls12_from_word(&mut f.c0.c1.c0, 0u64);
    bls12_from_word(&mut f.c0.c1.c1, 0u64);
    bls12_from_word(&mut f.c0.c2.c0, 0u64);
    bls12_from_word(&mut f.c0.c2.c1, 0u64);
    bls12_from_word(&mut f.c1.c0.c0, 0u64);
    bls12_from_word(&mut f.c1.c0.c1, 0u64);
    bls12_from_word(&mut f.c1.c1.c0, 0u64);
    bls12_from_word(&mut f.c1.c1.c1, 0u64);
    bls12_from_word(&mut f.c1.c2.c0, 0u64);
    bls12_from_word(&mut f.c1.c2.c1, 0u64);
    bls12_Fp2_felem_copy(&mut t_x, &q_x);
    bls12_Fp2_felem_copy(&mut t_y, &q_y);
    bls12_from_word(&mut t_z.c0, 1u64);
    bls12_from_word(&mut t_z.c1, 0u64);
    let mut i: u64;
    i = 63u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        bls12_Fp2_square(&mut A, &t_x);
        bls12_Fp2_square(&mut B, &t_y);
        bls12_Fp2_square(&mut C, &B);
        bls12_Fp2_mul(&mut D, &t_x, &B);
        let __ac0 = D.clone();
        bls12_Fp2_add(&mut D, &__ac0, &__ac0);
        let __ac1 = D.clone();
        bls12_Fp2_add(&mut D, &__ac1, &__ac1);
        bls12_Fp2_add(&mut E, &A, &A);
        let __ac2 = E.clone();
        bls12_Fp2_add(&mut E, &__ac2, &A);
        bls12_Fp2_mul(&mut ell0, &E, &t_x);
        bls12_Fp2_add(&mut tmp1, &B, &B);
        let __ac3 = ell0.clone();
        bls12_Fp2_sub(&mut ell0, &__ac3, &tmp1);
        bls12_Fp2_mul_fp(&mut tmp1, &E, &p_x);
        let __ac4 = tmp1.clone();
        bls12_Fp2_mul(&mut tmp1, &__ac4, &t_z);
        bls12_Fp2_opp(&mut ellVV, &tmp1);
        bls12_Fp2_square(&mut tmp1, &E);
        bls12_Fp2_add(&mut tmp2, &D, &D);
        let __ac5 = tmp2.clone();
        bls12_Fp2_sub(&mut tmp2, &tmp1, &__ac5);
        bls12_Fp2_sub(&mut tmp1, &D, &tmp2);
        let __ac6 = tmp1.clone();
        bls12_Fp2_mul(&mut tmp1, &E, &__ac6);
        let __ac7 = C.clone();
        bls12_Fp2_add(&mut C, &__ac7, &__ac7);
        let __ac8 = C.clone();
        bls12_Fp2_add(&mut C, &__ac8, &__ac8);
        let __ac9 = C.clone();
        bls12_Fp2_add(&mut C, &__ac9, &__ac9);
        bls12_Fp2_sub(&mut A, &tmp1, &C);
        bls12_Fp2_add(&mut tmp1, &t_y, &t_z);
        let __ac10 = tmp1.clone();
        bls12_Fp2_square(&mut tmp1, &__ac10);
        let __ac11 = tmp1.clone();
        bls12_Fp2_sub(&mut tmp1, &__ac11, &B);
        bls12_Fp2_square(&mut C, &t_z);
        let __ac12 = C.clone();
        bls12_Fp2_sub(&mut C, &tmp1, &__ac12);
        bls12_Fp2_mul_fp(&mut ellVW, &C, &p_y);
        bls12_Fp2_felem_copy(&mut t_x, &tmp2);
        bls12_Fp2_felem_copy(&mut t_y, &A);
        bls12_Fp2_felem_copy(&mut t_z, &C);
        let __ac13 = f.clone();
        bls12_Fp12_square(&mut f, &__ac13);
        let __ac14 = f.clone();
        bls12_Fp12_mul_by_024(&mut f, &__ac14, &ell0, &ellVW, &ellVV);
        let mut bit: u64;
        bit = ((15132376222941642752u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            bls12_Fp2_square(&mut A, &t_z);
            bls12_Fp2_mul(&mut B, &q_x, &A);
            bls12_Fp2_mul(&mut C, &A, &t_z);
            let __ac15 = C.clone();
            bls12_Fp2_mul(&mut C, &q_y, &__ac15);
            bls12_Fp2_sub(&mut D, &B, &t_x);
            bls12_Fp2_sub(&mut E, &C, &t_y);
            bls12_Fp2_mul(&mut ell0, &E, &q_x);
            let __ac16 = ell0.clone();
            bls12_Fp2_sub(&mut ell0, &__ac16, &t_y);
            bls12_Fp2_mul_fp(&mut tmp1, &E, &p_x);
            bls12_Fp2_opp(&mut ellVV, &tmp1);
            bls12_Fp2_square(&mut A, &D);
            bls12_Fp2_mul(&mut B, &t_x, &A);
            let __ac17 = A.clone();
            bls12_Fp2_mul(&mut A, &__ac17, &D);
            bls12_Fp2_square(&mut tmp1, &E);
            let __ac18 = tmp1.clone();
            bls12_Fp2_sub(&mut tmp1, &__ac18, &A);
            bls12_Fp2_add(&mut tmp2, &B, &B);
            let __ac19 = tmp2.clone();
            bls12_Fp2_sub(&mut tmp2, &tmp1, &__ac19);
            bls12_Fp2_sub(&mut tmp1, &B, &tmp2);
            let __ac20 = tmp1.clone();
            bls12_Fp2_mul(&mut tmp1, &E, &__ac20);
            bls12_Fp2_mul(&mut C, &t_y, &A);
            let __ac21 = C.clone();
            bls12_Fp2_sub(&mut C, &tmp1, &__ac21);
            bls12_Fp2_mul(&mut A, &D, &t_z);
            bls12_Fp2_mul_fp(&mut ellVW, &A, &p_y);
            bls12_Fp2_felem_copy(&mut t_x, &tmp2);
            bls12_Fp2_felem_copy(&mut t_y, &C);
            bls12_Fp2_felem_copy(&mut t_z, &A);
            let __ac22 = f.clone();
            bls12_Fp12_mul_by_024(&mut f, &__ac22, &ell0, &ellVW, &ellVV);
        } else {
        }
    }
    bls12_Fp12_felem_copy(&mut out, &f);
}

#[inline]
pub fn bls12_pairing(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut tmp: Fp12 = Fp12::zero();
    let mut gamma1_p2: Fp2 = Fp2::zero();
    let mut gamma2_p2: Fp2 = Fp2::zero();
    let mut w_frob_p2_c1: Fp2 = Fp2::zero();
    bls12_load_gamma1_p2(&mut gamma1_p2, );
    bls12_load_gamma2_p2(&mut gamma2_p2, );
    bls12_load_w_frob_p2_c1(&mut w_frob_p2_c1, );
    bls12_miller_loop(&mut tmp, &p_x, &p_y, &q_x, &q_y);
    bls12_final_exp(&mut out, &tmp, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
}

