#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp(pub [u64; 4]);
impl Fp { #[inline] pub const fn zero() -> Self { Fp([0u64; 4]) } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp2 { pub c0: Fp, pub c1: Fp }
impl Fp2 { #[inline] pub const fn zero() -> Self { Fp2 { c0: Fp::zero(), c1: Fp::zero() } } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp6 { pub c0: Fp2, pub c1: Fp2, pub c2: Fp2 }
impl Fp6 { #[inline] pub const fn zero() -> Self { Fp6 { c0: Fp2::zero(), c1: Fp2::zero(), c2: Fp2::zero() } } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp12 { pub c0: Fp6, pub c1: Fp6 }
impl Fp12 { #[inline] pub const fn zero() -> Self { Fp12 { c0: Fp6::zero(), c1: Fp6::zero() } } }

extern "C" {
    fn _bn254_add(out: *mut u64, x: *const u64, y: *const u64);
    fn _bn254_sub(out: *mut u64, x: *const u64, y: *const u64);
    fn _bn254_mul(out: *mut u64, x: *const u64, y: *const u64);
    fn _bn254_square(out: *mut u64, x: *const u64);
    fn _bn254_opp(out: *mut u64, x: *const u64);
    fn _bn254_felem_copy(out: *mut u64, x: *const u64);
    fn _bn254_from_word(out: *mut u64, w: u64);
    fn _bn254_select_znz(out: *mut u64, c: u64, x: *const u64, y: *const u64);
}
#[inline] pub fn bn254_add(out: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_add(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn254_sub(out: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_sub(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn254_mul(out: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_mul(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn254_square(out: &mut Fp, x: &Fp) { unsafe { _bn254_square(out.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn254_opp(out: &mut Fp, x: &Fp) { unsafe { _bn254_opp(out.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn254_felem_copy(out: &mut Fp, x: &Fp) { unsafe { _bn254_felem_copy(out.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn254_from_word(out: &mut Fp, w: u64) { unsafe { _bn254_from_word(out.0.as_mut_ptr(), w) } }
#[inline] pub fn bn254_select_znz(out: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bn254_select_znz(out.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }

#[inline] pub fn bn254_Fp2_opp(out: &mut Fp2, x: &Fp2) { bn254_opp(&mut out.c0, &x.c0); bn254_opp(&mut out.c1, &x.c1); }

#[inline] pub fn bn254_Fp2_inv(out: &mut Fp2, x: &Fp2) {
    let mut asq = Fp::zero();
    let mut bsq = Fp::zero();
    let mut norm = Fp::zero();
    bn254_square(&mut asq, &x.c0);
    bn254_square(&mut bsq, &x.c1);
    bn254_add(&mut norm, &asq, &bsq);
    let mut base = norm;
    let p_minus_2: [u64; 4] = [0x3c208c16d87cfd45, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029];
    let mut result = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    for limb_idx in 0..4 {
        let mut bits = p_minus_2[limb_idx];
        for _ in 0..64 {
            if bits & 1 == 1 { let r = result; bn254_mul(&mut result, &r, &base); }
            let b = base; bn254_square(&mut base, &b);
            bits >>= 1;
        }
    }
    norm = result;
    bn254_mul(&mut out.c0, &x.c0, &norm);
    let mut neg_b = Fp::zero();
    bn254_opp(&mut neg_b, &x.c1);
    bn254_mul(&mut out.c1, &neg_b, &norm);
}


#[inline]
pub fn bn254_Fp2_felem_copy(mut out: &mut Fp2, x: &Fp2) {
    bn254_felem_copy(&mut out.c0, &x.c0);
    bn254_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bn254_Fp2_add(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    bn254_add(&mut out.c0, &inx.c0, &iny.c0);
    bn254_add(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bn254_Fp2_sub(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    bn254_sub(&mut out.c0, &inx.c0, &iny.c0);
    bn254_sub(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bn254_Fp2_mul(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    let mut v2: Fp = Fp::zero();
    bn254_mul(&mut v0, &inx.c0, &iny.c0);
    bn254_mul(&mut v1, &inx.c1, &iny.c1);
    bn254_add(&mut v2, &inx.c0, &inx.c1);
    bn254_add(&mut out.c1, &iny.c0, &iny.c1);
    let __ac0 = out.c1.clone();
    bn254_mul(&mut out.c1, &__ac0, &v2);
    let __ac1 = out.c1.clone();
    bn254_sub(&mut out.c1, &__ac1, &v0);
    let __ac2 = out.c1.clone();
    bn254_sub(&mut out.c1, &__ac2, &v1);
    bn254_sub(&mut out.c0, &v0, &v1);
}

#[inline]
pub fn bn254_Fp2_square(mut out: &mut Fp2, inx: &Fp2) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    bn254_square(&mut v0, &inx.c0);
    bn254_square(&mut v1, &inx.c1);
    bn254_mul(&mut out.c1, &inx.c0, &inx.c1);
    let __ac0 = out.c1.clone();
    bn254_add(&mut out.c1, &__ac0, &__ac0);
    bn254_sub(&mut out.c0, &v0, &v1);
}

#[inline]
pub fn bn254_Fp2_mul_xi(mut out: &mut Fp2, x: &Fp2) {
    let mut tmp_a9: Fp = Fp::zero();
    let mut tmp_b9: Fp = Fp::zero();
    bn254_add(&mut tmp_a9, &x.c0, &x.c0);
    let __ac0 = tmp_a9.clone();
    bn254_add(&mut tmp_a9, &__ac0, &__ac0);
    let __ac1 = tmp_a9.clone();
    bn254_add(&mut tmp_a9, &__ac1, &__ac1);
    let __ac2 = tmp_a9.clone();
    bn254_add(&mut tmp_a9, &__ac2, &x.c0);
    bn254_add(&mut tmp_b9, &x.c1, &x.c1);
    let __ac3 = tmp_b9.clone();
    bn254_add(&mut tmp_b9, &__ac3, &__ac3);
    let __ac4 = tmp_b9.clone();
    bn254_add(&mut tmp_b9, &__ac4, &__ac4);
    let __ac5 = tmp_b9.clone();
    bn254_add(&mut tmp_b9, &__ac5, &x.c1);
    bn254_sub(&mut out.c0, &tmp_a9, &x.c1);
    bn254_add(&mut out.c1, &x.c0, &tmp_b9);
}

#[inline]
pub fn bn254_Fp6_felem_copy(mut out: &mut Fp6, x: &Fp6) {
    bn254_Fp2_felem_copy(&mut out.c0, &x.c0);
    bn254_Fp2_felem_copy(&mut out.c1, &x.c1);
    bn254_Fp2_felem_copy(&mut out.c2, &x.c2);
}

#[inline]
pub fn bn254_Fp6_add(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bn254_Fp6_felem_copy(&mut allocx, &inx);
    bn254_Fp6_felem_copy(&mut allocy, &iny);
    bn254_Fp2_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bn254_Fp2_add(&mut out.c1, &allocx.c1, &allocy.c1);
    bn254_Fp2_add(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bn254_Fp6_sub(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    bn254_Fp6_felem_copy(&mut allocx, &inx);
    bn254_Fp6_felem_copy(&mut allocy, &iny);
    bn254_Fp2_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bn254_Fp2_sub(&mut out.c1, &allocx.c1, &allocy.c1);
    bn254_Fp2_sub(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bn254_Fp6_opp(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    bn254_Fp6_felem_copy(&mut allocx, &x);
    bn254_Fp2_opp(&mut out.c0, &allocx.c0);
    bn254_Fp2_opp(&mut out.c1, &allocx.c1);
    bn254_Fp2_opp(&mut out.c2, &allocx.c2);
}

#[inline]
pub fn bn254_Fp6_mul(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut allocy: Fp6 = Fp6::zero();
    let mut a0b0: Fp2 = Fp2::zero();
    let mut a1b1: Fp2 = Fp2::zero();
    let mut a2b2: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    let mut u: Fp2 = Fp2::zero();
    bn254_Fp6_felem_copy(&mut allocx, &inx);
    bn254_Fp6_felem_copy(&mut allocy, &iny);
    bn254_Fp2_mul(&mut a0b0, &allocx.c0, &allocy.c0);
    bn254_Fp2_mul(&mut a1b1, &allocx.c1, &allocy.c1);
    bn254_Fp2_mul(&mut a2b2, &allocx.c2, &allocy.c2);
    bn254_Fp2_add(&mut t, &allocx.c1, &allocx.c2);
    bn254_Fp2_add(&mut u, &allocy.c1, &allocy.c2);
    let __ac0 = t.clone();
    bn254_Fp2_mul(&mut t, &__ac0, &u);
    let __ac1 = t.clone();
    bn254_Fp2_sub(&mut t, &__ac1, &a1b1);
    let __ac2 = t.clone();
    bn254_Fp2_sub(&mut t, &__ac2, &a2b2);
    let __ac3 = t.clone();
    bn254_Fp2_mul_xi(&mut t, &__ac3);
    bn254_Fp2_add(&mut out.c0, &a0b0, &t);
    bn254_Fp2_add(&mut t, &allocx.c0, &allocx.c1);
    bn254_Fp2_add(&mut u, &allocy.c0, &allocy.c1);
    let __ac4 = t.clone();
    bn254_Fp2_mul(&mut t, &__ac4, &u);
    let __ac5 = t.clone();
    bn254_Fp2_sub(&mut t, &__ac5, &a0b0);
    let __ac6 = t.clone();
    bn254_Fp2_sub(&mut t, &__ac6, &a1b1);
    bn254_Fp2_mul_xi(&mut u, &a2b2);
    bn254_Fp2_add(&mut out.c1, &t, &u);
    bn254_Fp2_add(&mut t, &allocx.c0, &allocx.c2);
    bn254_Fp2_add(&mut u, &allocy.c0, &allocy.c2);
    let __ac7 = t.clone();
    bn254_Fp2_mul(&mut t, &__ac7, &u);
    let __ac8 = t.clone();
    bn254_Fp2_sub(&mut t, &__ac8, &a0b0);
    let __ac9 = t.clone();
    bn254_Fp2_sub(&mut t, &__ac9, &a2b2);
    bn254_Fp2_add(&mut out.c2, &t, &a1b1);
}

#[inline]
pub fn bn254_Fp6_square(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut s0: Fp2 = Fp2::zero();
    let mut s1: Fp2 = Fp2::zero();
    let mut s2: Fp2 = Fp2::zero();
    let mut s3: Fp2 = Fp2::zero();
    let mut s4: Fp2 = Fp2::zero();
    let mut t: Fp2 = Fp2::zero();
    bn254_Fp6_felem_copy(&mut allocx, &x);
    bn254_Fp2_square(&mut s0, &allocx.c0);
    bn254_Fp2_mul(&mut t, &allocx.c0, &allocx.c1);
    bn254_Fp2_add(&mut s1, &t, &t);
    bn254_Fp2_sub(&mut t, &allocx.c0, &allocx.c1);
    let __ac0 = t.clone();
    bn254_Fp2_add(&mut t, &__ac0, &allocx.c2);
    bn254_Fp2_square(&mut s2, &t);
    bn254_Fp2_mul(&mut t, &allocx.c1, &allocx.c2);
    bn254_Fp2_add(&mut s3, &t, &t);
    bn254_Fp2_square(&mut s4, &allocx.c2);
    bn254_Fp2_mul_xi(&mut t, &s3);
    bn254_Fp2_add(&mut out.c0, &s0, &t);
    bn254_Fp2_mul_xi(&mut t, &s4);
    bn254_Fp2_add(&mut out.c1, &s1, &t);
    bn254_Fp2_add(&mut t, &s1, &s2);
    let __ac1 = t.clone();
    bn254_Fp2_add(&mut t, &__ac1, &s3);
    let __ac2 = t.clone();
    bn254_Fp2_sub(&mut t, &__ac2, &s0);
    bn254_Fp2_sub(&mut out.c2, &t, &s4);
}

#[inline]
pub fn bn254_Fp6_inv(mut out: &mut Fp6, x: &Fp6) {
    let mut allocx: Fp6 = Fp6::zero();
    let mut vA: Fp2 = Fp2::zero();
    let mut vB: Fp2 = Fp2::zero();
    let mut vC: Fp2 = Fp2::zero();
    let mut t1: Fp2 = Fp2::zero();
    let mut t2: Fp2 = Fp2::zero();
    let mut t3: Fp2 = Fp2::zero();
    bn254_Fp6_felem_copy(&mut allocx, &x);
    bn254_Fp2_square(&mut t1, &allocx.c0);
    bn254_Fp2_mul(&mut t2, &allocx.c1, &allocx.c2);
    bn254_Fp2_mul_xi(&mut t3, &t2);
    bn254_Fp2_sub(&mut vA, &t1, &t3);
    bn254_Fp2_square(&mut t1, &allocx.c2);
    bn254_Fp2_mul_xi(&mut t3, &t1);
    bn254_Fp2_mul(&mut t2, &allocx.c0, &allocx.c1);
    bn254_Fp2_sub(&mut vB, &t3, &t2);
    bn254_Fp2_square(&mut t1, &allocx.c1);
    bn254_Fp2_mul(&mut t2, &allocx.c0, &allocx.c2);
    bn254_Fp2_sub(&mut vC, &t1, &t2);
    bn254_Fp2_mul(&mut t1, &allocx.c0, &vA);
    bn254_Fp2_mul(&mut t2, &allocx.c2, &vB);
    bn254_Fp2_mul(&mut t3, &allocx.c1, &vC);
    let __ac0 = t2.clone();
    bn254_Fp2_add(&mut t2, &__ac0, &t3);
    let __ac1 = t2.clone();
    bn254_Fp2_mul_xi(&mut t2, &__ac1);
    let __ac2 = t1.clone();
    bn254_Fp2_add(&mut t1, &__ac2, &t2);
    let __ac3 = t1.clone();
    bn254_Fp2_inv(&mut t1, &__ac3);
    bn254_Fp2_mul(&mut out.c0, &vA, &t1);
    bn254_Fp2_mul(&mut out.c1, &vB, &t1);
    bn254_Fp2_mul(&mut out.c2, &vC, &t1);
}

#[inline]
pub fn bn254_Fp6_add_nocopy(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    bn254_Fp2_add(&mut out.c0, &inx.c0, &iny.c0);
    bn254_Fp2_add(&mut out.c1, &inx.c1, &iny.c1);
    bn254_Fp2_add(&mut out.c2, &inx.c2, &iny.c2);
}

#[inline]
pub fn bn254_Fp6_sub_nocopy(mut out: &mut Fp6, inx: &Fp6, iny: &Fp6) {
    bn254_Fp2_sub(&mut out.c0, &inx.c0, &iny.c0);
    bn254_Fp2_sub(&mut out.c1, &inx.c1, &iny.c1);
    bn254_Fp2_sub(&mut out.c2, &inx.c2, &iny.c2);
}

#[inline]
pub fn bn254_Fp6_mul_by_v(mut out: &mut Fp6, x: &Fp6) {
    let mut tmp: Fp6 = Fp6::zero();
    bn254_Fp6_felem_copy(&mut tmp, &x);
    bn254_Fp2_mul_xi(&mut out.c0, &tmp.c2);
    bn254_Fp2_felem_copy(&mut out.c1, &tmp.c0);
    bn254_Fp2_felem_copy(&mut out.c2, &tmp.c1);
}

#[inline]
pub fn bn254_Fp12_felem_copy(mut out: &mut Fp12, x: &Fp12) {
    bn254_Fp6_felem_copy(&mut out.c0, &x.c0);
    bn254_Fp6_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bn254_Fp12_add(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bn254_Fp12_felem_copy(&mut ax, &inx);
    bn254_Fp12_felem_copy(&mut ay, &iny);
    bn254_Fp6_add(&mut out.c0, &ax.c0, &ay.c0);
    bn254_Fp6_add(&mut out.c1, &ax.c1, &ay.c1);
}

#[inline]
pub fn bn254_Fp12_sub(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bn254_Fp12_felem_copy(&mut ax, &inx);
    bn254_Fp12_felem_copy(&mut ay, &iny);
    bn254_Fp6_sub(&mut out.c0, &ax.c0, &ay.c0);
    bn254_Fp6_sub(&mut out.c1, &ax.c1, &ay.c1);
}

#[inline]
pub fn bn254_Fp12_opp(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bn254_Fp12_felem_copy(&mut allocx, &x);
    bn254_Fp6_opp(&mut out.c0, &allocx.c0);
    bn254_Fp6_opp(&mut out.c1, &allocx.c1);
}

#[inline]
pub fn bn254_Fp12_conjugate(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bn254_Fp12_felem_copy(&mut allocx, &x);
    bn254_Fp6_felem_copy(&mut out.c0, &allocx.c0);
    bn254_Fp6_opp(&mut out.c1, &allocx.c1);
}

#[inline]
pub fn bn254_Fp12_mul(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut ax: Fp12 = Fp12::zero();
    let mut ay: Fp12 = Fp12::zero();
    bn254_Fp12_felem_copy(&mut ax, &inx);
    bn254_Fp12_felem_copy(&mut ay, &iny);
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bn254_Fp6_mul(&mut v0, &ax.c0, &ay.c0);
    bn254_Fp6_mul(&mut v1, &ax.c1, &ay.c1);
    bn254_Fp6_add(&mut t, &ax.c0, &ax.c1);
    bn254_Fp6_add(&mut u, &ay.c0, &ay.c1);
    let __ac0 = t.clone();
    bn254_Fp6_mul(&mut t, &__ac0, &u);
    bn254_Fp6_mul_by_v(&mut u, &v1);
    bn254_Fp6_add(&mut out.c0, &v0, &u);
    let __ac1 = t.clone();
    bn254_Fp6_sub(&mut t, &__ac1, &v0);
    bn254_Fp6_sub(&mut out.c1, &t, &v1);
}

#[inline]
pub fn bn254_Fp12_square(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bn254_Fp12_felem_copy(&mut allocx, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    let mut t2: Fp6 = Fp6::zero();
    bn254_Fp6_square(&mut t0, &allocx.c0);
    bn254_Fp6_square(&mut t1, &allocx.c1);
    bn254_Fp6_mul(&mut t2, &allocx.c0, &allocx.c1);
    let __ac0 = t1.clone();
    bn254_Fp6_mul_by_v(&mut t1, &__ac0);
    bn254_Fp6_add(&mut out.c0, &t0, &t1);
    bn254_Fp6_add(&mut out.c1, &t2, &t2);
}

#[inline]
pub fn bn254_Fp12_inv(mut out: &mut Fp12, x: &Fp12) {
    let mut allocx: Fp12 = Fp12::zero();
    bn254_Fp12_felem_copy(&mut allocx, &x);
    let mut t0: Fp6 = Fp6::zero();
    let mut t1: Fp6 = Fp6::zero();
    bn254_Fp6_square(&mut t0, &allocx.c0);
    bn254_Fp6_square(&mut t1, &allocx.c1);
    let __ac0 = t1.clone();
    bn254_Fp6_mul_by_v(&mut t1, &__ac0);
    let __ac1 = t0.clone();
    bn254_Fp6_sub(&mut t0, &__ac1, &t1);
    let __ac2 = t0.clone();
    bn254_Fp6_inv(&mut t0, &__ac2);
    bn254_Fp6_mul(&mut out.c0, &allocx.c0, &t0);
    bn254_Fp6_mul(&mut out.c1, &allocx.c1, &t0);
    let __ac3 = out.c1.clone();
    bn254_Fp6_opp(&mut out.c1, &__ac3);
}

#[inline]
pub fn bn254_Fp12_add_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    bn254_Fp6_add(&mut out.c0, &inx.c0, &iny.c0);
    bn254_Fp6_add(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bn254_Fp12_sub_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    bn254_Fp6_sub(&mut out.c0, &inx.c0, &iny.c0);
    bn254_Fp6_sub(&mut out.c1, &inx.c1, &iny.c1);
}

#[inline]
pub fn bn254_Fp12_mul_nocopy(mut out: &mut Fp12, inx: &Fp12, iny: &Fp12) {
    let mut v0: Fp6 = Fp6::zero();
    let mut v1: Fp6 = Fp6::zero();
    let mut t: Fp6 = Fp6::zero();
    let mut u: Fp6 = Fp6::zero();
    bn254_Fp6_mul(&mut v0, &inx.c0, &iny.c0);
    bn254_Fp6_mul(&mut v1, &inx.c1, &iny.c1);
    bn254_Fp6_add(&mut t, &inx.c0, &inx.c1);
    bn254_Fp6_add(&mut u, &iny.c0, &iny.c1);
    let __ac0 = t.clone();
    bn254_Fp6_mul(&mut t, &__ac0, &u);
    bn254_Fp6_mul_by_v(&mut u, &v1);
    bn254_Fp6_add(&mut out.c0, &v0, &u);
    let __ac1 = t.clone();
    bn254_Fp6_sub(&mut t, &__ac1, &v0);
    bn254_Fp6_sub(&mut out.c1, &t, &v1);
}

#[inline]
pub fn bn254_Fp2_conjugate(mut out: &mut Fp2, x: &Fp2) {
    bn254_felem_copy(&mut out.c0, &x.c0);
    bn254_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bn254_Fp6_mul_fp2(mut out: &mut Fp6, x: &Fp6, s: &Fp2) {
    let mut s_copy: Fp2 = Fp2::zero();
    bn254_Fp2_felem_copy(&mut s_copy, &s);
    bn254_Fp2_mul(&mut out.c0, &x.c0, &s_copy);
    bn254_Fp2_mul(&mut out.c1, &x.c1, &s_copy);
    bn254_Fp2_mul(&mut out.c2, &x.c2, &s_copy);
}

#[inline]
pub fn bn254_Fp6_frobenius(mut out: &mut Fp6, x: &Fp6, gamma1: &Fp2, gamma2: &Fp2) {
    let mut tmp: Fp6 = Fp6::zero();
    bn254_Fp2_conjugate(&mut tmp.c0, &x.c0);
    bn254_Fp2_conjugate(&mut tmp.c1, &x.c1);
    bn254_Fp2_conjugate(&mut tmp.c2, &x.c2);
    bn254_Fp2_felem_copy(&mut out.c0, &tmp.c0);
    bn254_Fp2_mul(&mut out.c1, &tmp.c1, &gamma1);
    bn254_Fp2_mul(&mut out.c2, &tmp.c2, &gamma2);
}

#[inline]
pub fn bn254_Fp6_frobenius_p2(mut out: &mut Fp6, x: &Fp6, gamma1_p2: &Fp2, gamma2_p2: &Fp2) {
    bn254_Fp2_felem_copy(&mut out.c0, &x.c0);
    bn254_Fp2_mul(&mut out.c1, &x.c1, &gamma1_p2);
    bn254_Fp2_mul(&mut out.c2, &x.c2, &gamma2_p2);
}

#[inline]
pub fn bn254_Fp12_frobenius(mut out: &mut Fp12, x: &Fp12, gamma1: &Fp2, gamma2: &Fp2, w_frob_c1: &Fp2) {
    bn254_Fp6_frobenius(&mut out.c0, &x.c0, &gamma1, &gamma2);
    bn254_Fp6_frobenius(&mut out.c1, &x.c1, &gamma1, &gamma2);
    let __ac0 = out.c1.clone();
    bn254_Fp6_mul_fp2(&mut out.c1, &__ac0, &w_frob_c1);
}

#[inline]
pub fn bn254_Fp12_frobenius_p2(mut out: &mut Fp12, x: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    bn254_Fp6_frobenius_p2(&mut out.c0, &x.c0, &gamma1_p2, &gamma2_p2);
    bn254_Fp6_frobenius_p2(&mut out.c1, &x.c1, &gamma1_p2, &gamma2_p2);
    let __ac0 = out.c1.clone();
    bn254_Fp6_mul_fp2(&mut out.c1, &__ac0, &w_frob_p2_c1);
}

#[inline]
pub fn bn254_Fp12_frobenius_p3(mut out: &mut Fp12, x: &Fp12, gamma1: &Fp12, gamma2: &Fp12, gamma1_p2: &Fp12, gamma2_p2: &Fp12, w_frob_c1: &Fp12, w_frob_p2_c1: &Fp12) {
    let mut tmp: Fp12 = Fp12::zero();
    bn254_Fp6_frobenius_p2(&mut tmp.c0, &x.c0, &gamma1_p2.c0.c0, &gamma2_p2.c0.c0);
    bn254_Fp6_frobenius_p2(&mut tmp.c1, &x.c1, &gamma1_p2.c0.c0, &gamma2_p2.c0.c0);
    let __ac0 = tmp.c1.clone();
    bn254_Fp6_mul_fp2(&mut tmp.c1, &__ac0, &w_frob_p2_c1.c0.c0);
    bn254_Fp6_frobenius(&mut out.c0, &tmp.c0, &gamma1.c0.c0, &gamma2.c0.c0);
    bn254_Fp6_frobenius(&mut out.c1, &tmp.c1, &gamma1.c0.c0, &gamma2.c0.c0);
    let __ac1 = out.c1.clone();
    bn254_Fp6_mul_fp2(&mut out.c1, &__ac1, &w_frob_c1.c0.c0);
}

#[inline]
pub fn bn254_Fp2_mul_fp(mut out: &mut Fp2, x: &Fp2, s: &Fp) {
    bn254_mul(&mut out.c0, &x.c0, &s);
    bn254_mul(&mut out.c1, &x.c1, &s);
}

#[inline]
pub fn bn254_make_line(mut out: &mut Fp12, lam: &Fp2, x_t: &Fp2, y_t: &Fp2, x_p: &Fp, y_p: &Fp) {
    let mut tmp: Fp2 = Fp2::zero();
    bn254_Fp2_mul(&mut out.c0.c0, &lam, &x_t);
    let __ac0 = out.c0.c0.clone();
    bn254_Fp2_sub(&mut out.c0.c0, &__ac0, &y_t);
    bn254_Fp2_mul_fp(&mut tmp, &lam, &x_p);
    bn254_Fp2_opp(&mut out.c0.c1, &tmp);
    bn254_from_word(&mut out.c0.c2.c0, 0u64);
    bn254_from_word(&mut out.c0.c2.c1, 0u64);
    bn254_from_word(&mut out.c1.c0.c0, 0u64);
    bn254_from_word(&mut out.c1.c0.c1, 0u64);
    bn254_felem_copy(&mut out.c1.c1.c0, &y_p);
    bn254_from_word(&mut out.c1.c1.c1, 0u64);
    bn254_from_word(&mut out.c1.c2.c0, 0u64);
    bn254_from_word(&mut out.c1.c2.c1, 0u64);
}

#[inline]
pub fn bn254_make_line_corrected(mut out: &mut Fp12, lam: &Fp2, x_t: &Fp2, y_t: &Fp2, x_p: &Fp, y_p: &Fp) {
    let mut tmp: Fp2 = Fp2::zero();
    bn254_felem_copy(&mut out.c0.c0.c0, &y_p);
    bn254_from_word(&mut out.c0.c0.c1, 0u64);
    bn254_from_word(&mut out.c0.c1.c0, 0u64);
    bn254_from_word(&mut out.c0.c1.c1, 0u64);
    bn254_from_word(&mut out.c0.c2.c0, 0u64);
    bn254_from_word(&mut out.c0.c2.c1, 0u64);
    bn254_Fp2_mul_fp(&mut tmp, &lam, &x_p);
    bn254_Fp2_opp(&mut out.c1.c0, &tmp);
    bn254_Fp2_mul(&mut out.c1.c1, &lam, &x_t);
    let __ac0 = out.c1.c1.clone();
    bn254_Fp2_sub(&mut out.c1.c1, &__ac0, &y_t);
    bn254_from_word(&mut out.c1.c2.c0, 0u64);
    bn254_from_word(&mut out.c1.c2.c1, 0u64);
}

#[inline]
pub fn bn254_load_gamma1_p2(mut out: &mut Fp2) {
    out.c0.0[0] = 3697675806616062876u64;
    out.c0.0[1] = 9065277094688085689u64;
    out.c0.0[2] = 6918009208039626314u64;
    out.c0.0[3] = 2775033306905974752u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
}

#[inline]
pub fn bn254_load_gamma2_p2(mut out: &mut Fp2) {
    out.c0.0[0] = 8183898218631979349u64;
    out.c0.0[1] = 12014359695528440611u64;
    out.c0.0[2] = 12263358156045030468u64;
    out.c0.0[3] = 3187210487005268291u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
}

#[inline]
pub fn bn254_load_w_frob_p2_c1(mut out: &mut Fp2) {
    out.c0.0[0] = 14595462726357228530u64;
    out.c0.0[1] = 17349508522658994025u64;
    out.c0.0[2] = 1017833795229664280u64;
    out.c0.0[3] = 299787779797702374u64;
    out.c1.0[0] = 0u64;
    out.c1.0[1] = 0u64;
    out.c1.0[2] = 0u64;
    out.c1.0[3] = 0u64;
}

#[inline]
pub fn bn254_load_gamma1(mut out: &mut Fp2) {
    out.c0.0[0] = 13075984984163199792u64;
    out.c0.0[1] = 3782902503040509012u64;
    out.c0.0[2] = 8791150885551868305u64;
    out.c0.0[3] = 1825854335138010348u64;
    out.c1.0[0] = 7963664994991228759u64;
    out.c1.0[1] = 12257807996192067905u64;
    out.c1.0[2] = 13179524609921305146u64;
    out.c1.0[3] = 2767831111890561987u64;
}

#[inline]
pub fn bn254_load_gamma2(mut out: &mut Fp2) {
    out.c0.0[0] = 8314163329781907090u64;
    out.c0.0[1] = 11942187022798819835u64;
    out.c0.0[2] = 11282677263046157209u64;
    out.c0.0[3] = 1576150870752482284u64;
    out.c1.0[0] = 6763840483288992073u64;
    out.c1.0[1] = 7118829427391486816u64;
    out.c1.0[2] = 4016233444936635065u64;
    out.c1.0[3] = 2630958277570195709u64;
}

#[inline]
pub fn bn254_load_w_frob_c1(mut out: &mut Fp2) {
    out.c0.0[0] = 12653890742059813127u64;
    out.c0.0[1] = 14585784200204367754u64;
    out.c0.0[2] = 1278438861261381767u64;
    out.c0.0[3] = 212598772761311868u64;
    out.c1.0[0] = 11683091849979440498u64;
    out.c1.0[1] = 14992204589386555739u64;
    out.c1.0[2] = 15866167890766973222u64;
    out.c1.0[3] = 1200023580730561873u64;
}

#[inline]
pub fn bn254_load_q1_y_const(mut out: &mut Fp2) {
    out.c0.0[0] = 16482010305593259561u64;
    out.c0.0[1] = 13488546290961988299u64;
    out.c0.0[2] = 3578621962720924518u64;
    out.c0.0[3] = 2681173117283399901u64;
    out.c1.0[0] = 11661927080404088775u64;
    out.c1.0[1] = 553939530661941723u64;
    out.c1.0[2] = 7860678177968807019u64;
    out.c1.0[3] = 3208568454732775116u64;
}

#[inline]
pub fn bn254_Fp12_pow_u(mut out: &mut Fp12, base: &Fp12) {
    let mut result: Fp12 = Fp12::zero();
    bn254_Fp12_felem_copy(&mut result, &base);
    let mut i: u64;
    i = 62u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let __ac0 = result.clone();
        bn254_Fp12_square(&mut result, &__ac0);
        let mut bit: u64;
        bit = ((4965661367192848881u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac1 = result.clone();
            bn254_Fp12_mul(&mut result, &__ac1, &base);
        } else {
        }
    }
    bn254_Fp12_felem_copy(&mut out, &result);
}

#[inline]
pub fn bn254_final_exp_hard_dsd(mut out: &mut Fp12, f: &Fp12) {
    let mut t0: Fp12 = Fp12::zero();
    let mut t1: Fp12 = Fp12::zero();
    let mut t2: Fp12 = Fp12::zero();
    let mut t3: Fp12 = Fp12::zero();
    let mut gamma1: Fp2 = Fp2::zero();
    let mut gamma2: Fp2 = Fp2::zero();
    let mut w_frob_c1: Fp2 = Fp2::zero();
    bn254_load_gamma1(&mut gamma1, );
    bn254_load_gamma2(&mut gamma2, );
    bn254_load_w_frob_c1(&mut w_frob_c1, );
    bn254_Fp12_pow_u(&mut t0, &f);
    bn254_Fp12_pow_u(&mut t1, &t0);
    bn254_Fp12_pow_u(&mut t2, &t1);
    bn254_Fp12_frobenius(&mut t3, &t2, &gamma1, &gamma2, &w_frob_c1);
    let __ac0 = t2.clone();
    bn254_Fp12_mul(&mut t2, &__ac0, &t3);
    let __ac1 = t2.clone();
    bn254_Fp12_conjugate(&mut t2, &__ac1);
    bn254_Fp12_square(&mut out, &t2);
    bn254_Fp12_frobenius(&mut t3, &t1, &gamma1, &gamma2, &w_frob_c1);
    bn254_Fp12_mul(&mut t2, &t0, &t3);
    let __ac2 = t2.clone();
    bn254_Fp12_conjugate(&mut t2, &__ac2);
    let __ac3 = out.clone();
    bn254_Fp12_mul(&mut out, &__ac3, &t2);
    let __ac4 = t1.clone();
    bn254_Fp12_conjugate(&mut t1, &__ac4);
    let __ac5 = out.clone();
    bn254_Fp12_mul(&mut out, &__ac5, &t1);
    bn254_Fp12_frobenius(&mut t2, &t0, &gamma1, &gamma2, &w_frob_c1);
    let __ac6 = t2.clone();
    bn254_Fp12_conjugate(&mut t2, &__ac6);
    bn254_Fp12_mul(&mut t0, &out, &t2);
    let __ac7 = t0.clone();
    bn254_Fp12_mul(&mut t0, &__ac7, &t1);
    bn254_Fp12_frobenius(&mut t1, &t3, &gamma1, &gamma2, &w_frob_c1);
    let __ac8 = out.clone();
    bn254_Fp12_mul(&mut out, &__ac8, &t1);
    bn254_Fp12_square(&mut t1, &t0);
    let __ac9 = t1.clone();
    bn254_Fp12_mul(&mut t1, &__ac9, &out);
    let __ac10 = t1.clone();
    bn254_Fp12_square(&mut t1, &__ac10);
    bn254_Fp12_frobenius(&mut t0, &f, &gamma1, &gamma2, &w_frob_c1);
    bn254_Fp12_frobenius(&mut t2, &t0, &gamma1, &gamma2, &w_frob_c1);
    bn254_Fp12_frobenius(&mut t3, &t2, &gamma1, &gamma2, &w_frob_c1);
    let __ac11 = t0.clone();
    bn254_Fp12_mul(&mut t0, &__ac11, &t2);
    let __ac12 = t0.clone();
    bn254_Fp12_mul(&mut t0, &__ac12, &t3);
    bn254_Fp12_mul(&mut t2, &t1, &t0);
    bn254_Fp12_conjugate(&mut t0, &f);
    let __ac13 = t0.clone();
    bn254_Fp12_mul(&mut t0, &t1, &__ac13);
    let __ac14 = t0.clone();
    bn254_Fp12_square(&mut t0, &__ac14);
    bn254_Fp12_mul(&mut out, &t0, &t2);
}

#[inline]
pub fn bn254_final_exp_dsd(mut out: &mut Fp12, f: &Fp12, gamma1_p2: &Fp2, gamma2_p2: &Fp2, w_frob_p2_c1: &Fp2) {
    let mut result: Fp12 = Fp12::zero();
    let mut tmp: Fp12 = Fp12::zero();
    bn254_Fp12_conjugate(&mut result, &f);
    bn254_Fp12_inv(&mut tmp, &f);
    let __ac0 = result.clone();
    bn254_Fp12_mul(&mut result, &__ac0, &tmp);
    bn254_Fp12_frobenius_p2(&mut tmp, &result, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
    let __ac1 = result.clone();
    bn254_Fp12_mul(&mut result, &tmp, &__ac1);
    bn254_final_exp_hard_dsd(&mut out, &result);
}

#[inline]
pub fn bn254_miller_loop(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut f: Fp12 = Fp12::zero();
    let mut t_x: Fp2 = Fp2::zero();
    let mut t_y: Fp2 = Fp2::zero();
    let mut lambda: Fp2 = Fp2::zero();
    let mut tmp1: Fp2 = Fp2::zero();
    let mut tmp2: Fp2 = Fp2::zero();
    let mut line: Fp12 = Fp12::zero();
    let mut u6p2: u64 = 0u64;
    bn254_from_word(&mut f.c0.c0.c0, 1u64);
    bn254_from_word(&mut f.c0.c0.c1, 0u64);
    bn254_from_word(&mut f.c0.c1.c0, 0u64);
    bn254_from_word(&mut f.c0.c1.c1, 0u64);
    bn254_from_word(&mut f.c0.c2.c0, 0u64);
    bn254_from_word(&mut f.c0.c2.c1, 0u64);
    bn254_from_word(&mut f.c1.c0.c0, 0u64);
    bn254_from_word(&mut f.c1.c0.c1, 0u64);
    bn254_from_word(&mut f.c1.c1.c0, 0u64);
    bn254_from_word(&mut f.c1.c1.c1, 0u64);
    bn254_from_word(&mut f.c1.c2.c0, 0u64);
    bn254_from_word(&mut f.c1.c2.c1, 0u64);
    bn254_Fp2_felem_copy(&mut t_x, &q_x);
    bn254_Fp2_felem_copy(&mut t_y, &q_y);
    u6p2 = 11347224129447541672u64;
    let mut i: u64;
    i = 64u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let mut word: u64;
        word = u6p2;
        let mut bit: u64;
        bit = ((word >> (i & 63)) & 1u64);
        bn254_Fp2_square(&mut tmp1, &t_x);
        bn254_Fp2_add(&mut lambda, &tmp1, &tmp1);
        let __ac0 = lambda.clone();
        bn254_Fp2_add(&mut lambda, &__ac0, &tmp1);
        bn254_Fp2_add(&mut tmp1, &t_y, &t_y);
        let __ac1 = tmp1.clone();
        bn254_Fp2_inv(&mut tmp1, &__ac1);
        let __ac2 = lambda.clone();
        bn254_Fp2_mul(&mut lambda, &__ac2, &tmp1);
        bn254_make_line_corrected(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
        let __ac3 = f.clone();
        bn254_Fp12_square(&mut f, &__ac3);
        let __ac4 = f.clone();
        bn254_Fp12_mul(&mut f, &__ac4, &line);
        bn254_Fp2_square(&mut tmp1, &lambda);
        let __ac5 = tmp1.clone();
        bn254_Fp2_sub(&mut tmp1, &__ac5, &t_x);
        bn254_Fp2_sub(&mut tmp2, &tmp1, &t_x);
        bn254_Fp2_sub(&mut tmp1, &t_x, &tmp2);
        let __ac6 = tmp1.clone();
        bn254_Fp2_mul(&mut tmp1, &lambda, &__ac6);
        let __ac7 = t_y.clone();
        bn254_Fp2_sub(&mut t_y, &tmp1, &__ac7);
        bn254_Fp2_felem_copy(&mut t_x, &tmp2);
        if bit != 0 {
            bn254_Fp2_sub(&mut tmp1, &q_y, &t_y);
            bn254_Fp2_sub(&mut tmp2, &q_x, &t_x);
            let __ac8 = tmp2.clone();
            bn254_Fp2_inv(&mut tmp2, &__ac8);
            bn254_Fp2_mul(&mut lambda, &tmp1, &tmp2);
            bn254_make_line_corrected(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
            let __ac9 = f.clone();
            bn254_Fp12_mul(&mut f, &__ac9, &line);
            bn254_Fp2_square(&mut tmp1, &lambda);
            let __ac10 = tmp1.clone();
            bn254_Fp2_sub(&mut tmp1, &__ac10, &t_x);
            bn254_Fp2_sub(&mut tmp2, &tmp1, &q_x);
            bn254_Fp2_sub(&mut tmp1, &t_x, &tmp2);
            let __ac11 = tmp1.clone();
            bn254_Fp2_mul(&mut tmp1, &lambda, &__ac11);
            let __ac12 = t_y.clone();
            bn254_Fp2_sub(&mut t_y, &tmp1, &__ac12);
            bn254_Fp2_felem_copy(&mut t_x, &tmp2);
        } else {
        }
    }
    bn254_Fp12_felem_copy(&mut out, &f);
}

#[inline]
pub fn bn254_miller_loop_optimal(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut f: Fp12 = Fp12::zero();
    let mut t_x: Fp2 = Fp2::zero();
    let mut t_y: Fp2 = Fp2::zero();
    let mut lambda: Fp2 = Fp2::zero();
    let mut tmp1: Fp2 = Fp2::zero();
    let mut tmp2: Fp2 = Fp2::zero();
    let mut line: Fp12 = Fp12::zero();
    let mut u6p2: u64 = 0u64;
    let mut q1_x: Fp2 = Fp2::zero();
    let mut q1_y: Fp2 = Fp2::zero();
    let mut const_g1: Fp2 = Fp2::zero();
    let mut const_g_y: Fp2 = Fp2::zero();
    let mut const_g1p2: Fp2 = Fp2::zero();
    bn254_from_word(&mut f.c0.c0.c0, 1u64);
    bn254_from_word(&mut f.c0.c0.c1, 0u64);
    bn254_from_word(&mut f.c0.c1.c0, 0u64);
    bn254_from_word(&mut f.c0.c1.c1, 0u64);
    bn254_from_word(&mut f.c0.c2.c0, 0u64);
    bn254_from_word(&mut f.c0.c2.c1, 0u64);
    bn254_from_word(&mut f.c1.c0.c0, 0u64);
    bn254_from_word(&mut f.c1.c0.c1, 0u64);
    bn254_from_word(&mut f.c1.c1.c0, 0u64);
    bn254_from_word(&mut f.c1.c1.c1, 0u64);
    bn254_from_word(&mut f.c1.c2.c0, 0u64);
    bn254_from_word(&mut f.c1.c2.c1, 0u64);
    bn254_Fp2_felem_copy(&mut t_x, &q_x);
    bn254_Fp2_felem_copy(&mut t_y, &q_y);
    u6p2 = 11347224129447541672u64;
    let mut i: u64;
    i = 64u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let mut word: u64;
        word = u6p2;
        let mut bit: u64;
        bit = ((word >> (i & 63)) & 1u64);
        bn254_Fp2_square(&mut tmp1, &t_x);
        bn254_Fp2_add(&mut lambda, &tmp1, &tmp1);
        let __ac0 = lambda.clone();
        bn254_Fp2_add(&mut lambda, &__ac0, &tmp1);
        bn254_Fp2_add(&mut tmp1, &t_y, &t_y);
        let __ac1 = tmp1.clone();
        bn254_Fp2_inv(&mut tmp1, &__ac1);
        let __ac2 = lambda.clone();
        bn254_Fp2_mul(&mut lambda, &__ac2, &tmp1);
        bn254_make_line_corrected(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
        let __ac3 = f.clone();
        bn254_Fp12_square(&mut f, &__ac3);
        let __ac4 = f.clone();
        bn254_Fp12_mul(&mut f, &__ac4, &line);
        bn254_Fp2_square(&mut tmp1, &lambda);
        let __ac5 = tmp1.clone();
        bn254_Fp2_sub(&mut tmp1, &__ac5, &t_x);
        bn254_Fp2_sub(&mut tmp2, &tmp1, &t_x);
        bn254_Fp2_sub(&mut tmp1, &t_x, &tmp2);
        let __ac6 = tmp1.clone();
        bn254_Fp2_mul(&mut tmp1, &lambda, &__ac6);
        let __ac7 = t_y.clone();
        bn254_Fp2_sub(&mut t_y, &tmp1, &__ac7);
        bn254_Fp2_felem_copy(&mut t_x, &tmp2);
        if bit != 0 {
            bn254_Fp2_sub(&mut tmp1, &q_y, &t_y);
            bn254_Fp2_sub(&mut tmp2, &q_x, &t_x);
            let __ac8 = tmp2.clone();
            bn254_Fp2_inv(&mut tmp2, &__ac8);
            bn254_Fp2_mul(&mut lambda, &tmp1, &tmp2);
            bn254_make_line_corrected(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
            let __ac9 = f.clone();
            bn254_Fp12_mul(&mut f, &__ac9, &line);
            bn254_Fp2_square(&mut tmp1, &lambda);
            let __ac10 = tmp1.clone();
            bn254_Fp2_sub(&mut tmp1, &__ac10, &t_x);
            bn254_Fp2_sub(&mut tmp2, &tmp1, &q_x);
            bn254_Fp2_sub(&mut tmp1, &t_x, &tmp2);
            let __ac11 = tmp1.clone();
            bn254_Fp2_mul(&mut tmp1, &lambda, &__ac11);
            let __ac12 = t_y.clone();
            bn254_Fp2_sub(&mut t_y, &tmp1, &__ac12);
            bn254_Fp2_felem_copy(&mut t_x, &tmp2);
        } else {
        }
    }
    bn254_load_gamma1(&mut const_g1, );
    bn254_load_q1_y_const(&mut const_g_y, );
    bn254_load_gamma1_p2(&mut const_g1p2, );
    bn254_Fp2_conjugate(&mut tmp1, &q_x);
    bn254_Fp2_mul(&mut q1_x, &tmp1, &const_g1);
    bn254_Fp2_conjugate(&mut tmp1, &q_y);
    bn254_Fp2_mul(&mut q1_y, &tmp1, &const_g_y);
    bn254_Fp2_sub(&mut tmp1, &q1_y, &t_y);
    bn254_Fp2_sub(&mut tmp2, &q1_x, &t_x);
    let __ac13 = tmp2.clone();
    bn254_Fp2_inv(&mut tmp2, &__ac13);
    bn254_Fp2_mul(&mut lambda, &tmp1, &tmp2);
    bn254_make_line_corrected(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
    let __ac14 = f.clone();
    bn254_Fp12_mul(&mut f, &__ac14, &line);
    bn254_Fp2_square(&mut tmp1, &lambda);
    let __ac15 = tmp1.clone();
    bn254_Fp2_sub(&mut tmp1, &__ac15, &t_x);
    bn254_Fp2_sub(&mut tmp2, &tmp1, &q1_x);
    bn254_Fp2_sub(&mut tmp1, &t_x, &tmp2);
    let __ac16 = tmp1.clone();
    bn254_Fp2_mul(&mut tmp1, &lambda, &__ac16);
    let __ac17 = t_y.clone();
    bn254_Fp2_sub(&mut t_y, &tmp1, &__ac17);
    bn254_Fp2_felem_copy(&mut t_x, &tmp2);
    bn254_Fp2_mul_fp(&mut q1_x, &q_x, &const_g1p2.c0);
    bn254_Fp2_sub(&mut tmp1, &q_y, &t_y);
    bn254_Fp2_sub(&mut tmp2, &q1_x, &t_x);
    let __ac18 = tmp2.clone();
    bn254_Fp2_inv(&mut tmp2, &__ac18);
    bn254_Fp2_mul(&mut lambda, &tmp1, &tmp2);
    bn254_make_line_corrected(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
    let __ac19 = f.clone();
    bn254_Fp12_mul(&mut f, &__ac19, &line);
    bn254_Fp12_felem_copy(&mut out, &f);
}

#[inline]
pub fn bn254_pairing_dsd(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut tmp: Fp12 = Fp12::zero();
    let mut gamma1_p2: Fp2 = Fp2::zero();
    let mut gamma2_p2: Fp2 = Fp2::zero();
    let mut w_frob_p2_c1: Fp2 = Fp2::zero();
    bn254_load_gamma1_p2(&mut gamma1_p2, );
    bn254_load_gamma2_p2(&mut gamma2_p2, );
    bn254_load_w_frob_p2_c1(&mut w_frob_p2_c1, );
    bn254_miller_loop(&mut tmp, &p_x, &p_y, &q_x, &q_y);
    bn254_final_exp_dsd(&mut out, &tmp, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
}

#[inline]
pub fn bn254_pairing_dsd_optimal(mut out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut tmp: Fp12 = Fp12::zero();
    let mut gamma1_p2: Fp2 = Fp2::zero();
    let mut gamma2_p2: Fp2 = Fp2::zero();
    let mut w_frob_p2_c1: Fp2 = Fp2::zero();
    bn254_load_gamma1_p2(&mut gamma1_p2, );
    bn254_load_gamma2_p2(&mut gamma2_p2, );
    bn254_load_w_frob_p2_c1(&mut w_frob_p2_c1, );
    bn254_miller_loop_optimal(&mut tmp, &p_x, &p_y, &q_x, &q_y);
    bn254_final_exp_dsd(&mut out, &tmp, &gamma1_p2, &gamma2_p2, &w_frob_p2_c1);
}

