#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp(pub [u64; 8]);
impl Fp { #[inline] pub const fn zero() -> Self { Fp([0u64; 8]) } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp2 { pub c0: Fp, pub c1: Fp }
impl Fp2 { #[inline] pub const fn zero() -> Self { Fp2 { c0: Fp::zero(), c1: Fp::zero() } } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp4 { pub c0: Fp2, pub c1: Fp2 }
impl Fp4 { #[inline] pub const fn zero() -> Self { Fp4 { c0: Fp2::zero(), c1: Fp2::zero() } } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp8 { pub c0: Fp4, pub c1: Fp4 }
impl Fp8 { #[inline] pub const fn zero() -> Self { Fp8 { c0: Fp4::zero(), c1: Fp4::zero() } } }

#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp24 { pub c0: Fp8, pub c1: Fp8, pub c2: Fp8 }
impl Fp24 { #[inline] pub const fn zero() -> Self { Fp24 { c0: Fp8::zero(), c1: Fp8::zero(), c2: Fp8::zero() } } }


unsafe extern "C" {
    fn _bls24_509_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls24_509_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls24_509_mul(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls24_509_square(o: *mut u64, x: *const u64);
    fn _bls24_509_opp(o: *mut u64, x: *const u64);
    fn _bls24_509_felem_copy(o: *mut u64, x: *const u64);
    fn _bls24_509_from_word(o: *mut u64, w: u64);
    fn _bls24_509_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
    fn _bls24_509_inv(o: *mut u64, x: *const u64);
}
#[inline] pub fn bls24_509_add(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls24_509_add(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls24_509_sub(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls24_509_sub(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls24_509_mul(o: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bls24_509_mul(o.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls24_509_square(o: &mut Fp, x: &Fp) { unsafe { _bls24_509_square(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls24_509_opp(o: &mut Fp, x: &Fp) { unsafe { _bls24_509_opp(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls24_509_felem_copy(o: &mut Fp, x: &Fp) { unsafe { _bls24_509_felem_copy(o.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bls24_509_from_word(o: &mut Fp, w: u64) { unsafe { _bls24_509_from_word(o.0.as_mut_ptr(), w) } }
#[inline] pub fn bls24_509_select_znz(o: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bls24_509_select_znz(o.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bls24_509_inv(o: &mut Fp, x: &Fp) { unsafe { _bls24_509_inv(o.0.as_mut_ptr(), x.0.as_ptr()) } }
/// Zero out an Fp.  Used by Fp2/.../Fp24 `_zero` constructors emitted
/// by the verified tower.  Not in the extern-C leaf set (Jasmin
/// doesn't generate a `_zero` symbol — it just emits the [u64;n] of
/// zeros), so we provide it as a safe-Rust definition here.
#[inline] pub fn bls24_509_zero(o: &mut Fp) { *o = Fp::zero(); }
/// Canonical Montgomery `1` for BLS24-509.  Reuses `from_word(1)`
/// (which goes through Jasmin's `to_montgomery` if needed).
#[inline] pub fn bls24_509_one(o: &mut Fp) { bls24_509_from_word(o, 1u64); }

/// Inverse in Fp2.  No closed bedrock2 body exists for BLS24's Fp2
/// (the [BLS24_509_MillerLoop_proof.v] only ships a [spec_of_]
/// instance).  We use the standard norm trick:
///   inv(a + b·u) = (a − b·u) / (a² − β·b²)
/// where β is the Fp2 non-residue (encoded in the bedrock2 emission
/// of `bls24_Fp2_mul_by_nr`: that helper computes `out := β · in` in
/// the base field Fp).
pub fn bls24_Fp2_inv(out: &mut Fp2, x: &Fp2) {
    let mut a_sq = Fp::zero();
    let mut b_sq = Fp::zero();
    let mut nr_b_sq = Fp::zero();
    let mut norm = Fp::zero();
    let mut norm_inv = Fp::zero();
    bls24_509_square(&mut a_sq, &x.c0);
    bls24_509_square(&mut b_sq, &x.c1);
    // β · b² (uses the verified `bls24_Fp2_mul_by_nr` body emitted above).
    bls24_Fp2_mul_by_nr(&mut nr_b_sq, &b_sq);
    bls24_509_sub(&mut norm, &a_sq, &nr_b_sq);
    bls24_509_inv(&mut norm_inv, &norm);
    bls24_509_mul(&mut out.c0, &x.c0, &norm_inv);
    let mut neg_c1 = Fp::zero();
    bls24_509_opp(&mut neg_c1, &x.c1);
    bls24_509_mul(&mut out.c1, &neg_c1, &norm_inv);
}

/// Inverse in Fp4 = Fp2[v]/(v² − ξ).  Norm trick over Fp2 with the
/// non-residue mul by ξ (= `bls24_Fp2_mul_xi`).
pub fn bls24_Fp4_inv(out: &mut Fp4, x: &Fp4) {
    let mut c0_sq = Fp2::zero();
    let mut c1_sq = Fp2::zero();
    let mut xi_c1_sq = Fp2::zero();
    let mut norm = Fp2::zero();
    let mut norm_inv = Fp2::zero();
    bls24_Fp2_mul(&mut c0_sq, &x.c0, &x.c0);
    bls24_Fp2_mul(&mut c1_sq, &x.c1, &x.c1);
    bls24_Fp2_mul_xi(&mut xi_c1_sq, &c1_sq);
    bls24_Fp2_sub(&mut norm, &c0_sq, &xi_c1_sq);
    bls24_Fp2_inv(&mut norm_inv, &norm);
    bls24_Fp2_mul(&mut out.c0, &x.c0, &norm_inv);
    let mut neg_c1 = Fp2::zero();
    bls24_Fp2_opp(&mut neg_c1, &x.c1);
    bls24_Fp2_mul(&mut out.c1, &neg_c1, &norm_inv);
}

/// Inverse in Fp8 = Fp4[v']/(v'² − v).  Norm trick over Fp4 with the
/// non-residue mul by v (= `bls24_Fp4_mul_by_v`).
pub fn bls24_Fp8_inv(out: &mut Fp8, x: &Fp8) {
    let mut c0_sq = Fp4::zero();
    let mut c1_sq = Fp4::zero();
    let mut v_c1_sq = Fp4::zero();
    let mut norm = Fp4::zero();
    let mut norm_inv = Fp4::zero();
    bls24_Fp4_mul(&mut c0_sq, &x.c0, &x.c0);
    bls24_Fp4_mul(&mut c1_sq, &x.c1, &x.c1);
    bls24_Fp4_mul_by_v(&mut v_c1_sq, &c1_sq);
    bls24_Fp4_sub(&mut norm, &c0_sq, &v_c1_sq);
    bls24_Fp4_inv(&mut norm_inv, &norm);
    bls24_Fp4_mul(&mut out.c0, &x.c0, &norm_inv);
    let mut neg_c1 = Fp4::zero();
    bls24_Fp4_opp(&mut neg_c1, &x.c1);
    bls24_Fp4_mul(&mut out.c1, &neg_c1, &norm_inv);
}

#[inline]
pub fn bls24_Fp2_felem_copy(mut out: &mut Fp2, x: &Fp2) {
    bls24_509_felem_copy(&mut out.c0, &x.c0);
    bls24_509_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls24_Fp2_zero(mut out: &mut Fp2) {
    bls24_509_zero(&mut out.c0, );
    bls24_509_zero(&mut out.c1, );
}

#[inline]
pub fn bls24_Fp2_one(mut out: &mut Fp2) {
    bls24_509_one(&mut out.c0, );
    bls24_509_zero(&mut out.c1, );
}

#[inline]
pub fn bls24_Fp2_opp(mut out: &mut Fp2, x: &Fp2) {
    bls24_509_opp(&mut out.c0, &x.c0);
    bls24_509_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls24_Fp2_add(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    let mut allocx: Fp2 = Fp2::zero();
    let mut allocy: Fp2 = Fp2::zero();
    bls24_Fp2_felem_copy(&mut allocx, &inx);
    bls24_Fp2_felem_copy(&mut allocy, &iny);
    bls24_509_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bls24_509_add(&mut out.c1, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bls24_Fp2_sub(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    let mut allocx: Fp2 = Fp2::zero();
    let mut allocy: Fp2 = Fp2::zero();
    bls24_Fp2_felem_copy(&mut allocx, &inx);
    bls24_Fp2_felem_copy(&mut allocy, &iny);
    bls24_509_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bls24_509_sub(&mut out.c1, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bls24_Fp2_mul(mut out: &mut Fp2, inx: &Fp2, iny: &Fp2) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    let mut v2: Fp = Fp::zero();
    bls24_509_mul(&mut v0, &inx.c0, &iny.c0);
    bls24_509_mul(&mut v1, &inx.c1, &iny.c1);
    bls24_509_add(&mut v2, &inx.c0, &inx.c1);
    bls24_509_add(&mut out.c1, &iny.c0, &iny.c1);
    let __ac0 = out.c1.clone();
    bls24_509_mul(&mut out.c1, &__ac0, &v2);
    let __ac1 = out.c1.clone();
    bls24_509_sub(&mut out.c1, &__ac1, &v0);
    let __ac2 = out.c1.clone();
    bls24_509_sub(&mut out.c1, &__ac2, &v1);
    bls24_Fp2_mul_by_nr(&mut v2, &v1);
    bls24_509_add(&mut out.c0, &v0, &v2);
}

#[inline]
pub fn bls24_Fp2_square(mut out: &mut Fp2, x: &Fp2) {
    let mut v0: Fp = Fp::zero();
    let mut v1: Fp = Fp::zero();
    let mut v2: Fp = Fp::zero();
    bls24_509_square(&mut v0, &x.c0);
    bls24_509_square(&mut v1, &x.c1);
    bls24_509_mul(&mut v2, &x.c0, &x.c1);
    bls24_509_add(&mut out.c1, &v2, &v2);
    let __ac0 = v1.clone();
    bls24_Fp2_mul_by_nr(&mut v1, &__ac0);
    bls24_509_add(&mut out.c0, &v0, &v1);
}

#[inline]
pub fn bls24_Fp2_select_znz(mut out: &mut Fp2, c: u64, inx: &Fp2, iny: &Fp2) {
    let mut allocx: Fp2 = Fp2::zero();
    let mut allocy: Fp2 = Fp2::zero();
    bls24_Fp2_felem_copy(&mut allocx, &inx);
    bls24_Fp2_felem_copy(&mut allocy, &iny);
    bls24_509_select_znz(&mut out.c0, c, &allocx.c0, &allocy.c0);
    bls24_509_select_znz(&mut out.c1, c, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bls24_Fp4_felem_copy(mut out: &mut Fp4, x: &Fp4) {
    bls24_Fp2_felem_copy(&mut out.c0, &x.c0);
    bls24_Fp2_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls24_Fp4_zero(mut out: &mut Fp4) {
    bls24_Fp2_zero(&mut out.c0, );
    bls24_Fp2_zero(&mut out.c1, );
}

#[inline]
pub fn bls24_Fp4_one(mut out: &mut Fp4) {
    bls24_Fp2_one(&mut out.c0, );
    bls24_Fp2_zero(&mut out.c1, );
}

#[inline]
pub fn bls24_Fp4_opp(mut out: &mut Fp4, x: &Fp4) {
    bls24_Fp2_opp(&mut out.c0, &x.c0);
    bls24_Fp2_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls24_Fp4_add(mut out: &mut Fp4, inx: &Fp4, iny: &Fp4) {
    let mut allocx: Fp4 = Fp4::zero();
    let mut allocy: Fp4 = Fp4::zero();
    bls24_Fp4_felem_copy(&mut allocx, &inx);
    bls24_Fp4_felem_copy(&mut allocy, &iny);
    bls24_Fp2_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bls24_Fp2_add(&mut out.c1, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bls24_Fp4_sub(mut out: &mut Fp4, inx: &Fp4, iny: &Fp4) {
    let mut allocx: Fp4 = Fp4::zero();
    let mut allocy: Fp4 = Fp4::zero();
    bls24_Fp4_felem_copy(&mut allocx, &inx);
    bls24_Fp4_felem_copy(&mut allocy, &iny);
    bls24_Fp2_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bls24_Fp2_sub(&mut out.c1, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bls24_Fp4_mul(mut out: &mut Fp4, inx: &Fp4, iny: &Fp4) {
    let mut v0: Fp2 = Fp2::zero();
    let mut v1: Fp2 = Fp2::zero();
    let mut v2: Fp2 = Fp2::zero();
    bls24_Fp2_mul(&mut v0, &inx.c0, &iny.c0);
    bls24_Fp2_mul(&mut v1, &inx.c1, &iny.c1);
    bls24_Fp2_add(&mut v2, &inx.c0, &inx.c1);
    bls24_Fp2_add(&mut out.c1, &iny.c0, &iny.c1);
    let __ac0 = out.c1.clone();
    bls24_Fp2_mul(&mut out.c1, &__ac0, &v2);
    let __ac1 = out.c1.clone();
    bls24_Fp2_sub(&mut out.c1, &__ac1, &v0);
    let __ac2 = out.c1.clone();
    bls24_Fp2_sub(&mut out.c1, &__ac2, &v1);
    bls24_Fp2_mul_xi(&mut v2, &v1);
    bls24_Fp2_add(&mut out.c0, &v0, &v2);
}

#[inline]
pub fn bls24_Fp4_square(mut out: &mut Fp4, x: &Fp4) {
    let mut v0: Fp2 = Fp2::zero();
    let mut v1: Fp2 = Fp2::zero();
    let mut v2: Fp2 = Fp2::zero();
    bls24_Fp2_square(&mut v0, &x.c0);
    bls24_Fp2_square(&mut v1, &x.c1);
    bls24_Fp2_mul(&mut v2, &x.c0, &x.c1);
    bls24_Fp2_add(&mut out.c1, &v2, &v2);
    let __ac0 = v1.clone();
    bls24_Fp2_mul_xi(&mut v1, &__ac0);
    bls24_Fp2_add(&mut out.c0, &v0, &v1);
}

#[inline]
pub fn bls24_Fp4_select_znz(mut out: &mut Fp4, c: u64, inx: &Fp4, iny: &Fp4) {
    let mut allocx: Fp4 = Fp4::zero();
    let mut allocy: Fp4 = Fp4::zero();
    bls24_Fp4_felem_copy(&mut allocx, &inx);
    bls24_Fp4_felem_copy(&mut allocy, &iny);
    bls24_Fp2_select_znz(&mut out.c0, c, &allocx.c0, &allocy.c0);
    bls24_Fp2_select_znz(&mut out.c1, c, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bls24_Fp8_felem_copy(mut out: &mut Fp8, x: &Fp8) {
    bls24_Fp4_felem_copy(&mut out.c0, &x.c0);
    bls24_Fp4_felem_copy(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls24_Fp8_zero(mut out: &mut Fp8) {
    bls24_Fp4_zero(&mut out.c0, );
    bls24_Fp4_zero(&mut out.c1, );
}

#[inline]
pub fn bls24_Fp8_one(mut out: &mut Fp8) {
    bls24_Fp4_one(&mut out.c0, );
    bls24_Fp4_zero(&mut out.c1, );
}

#[inline]
pub fn bls24_Fp8_opp(mut out: &mut Fp8, x: &Fp8) {
    bls24_Fp4_opp(&mut out.c0, &x.c0);
    bls24_Fp4_opp(&mut out.c1, &x.c1);
}

#[inline]
pub fn bls24_Fp8_add(mut out: &mut Fp8, inx: &Fp8, iny: &Fp8) {
    let mut allocx: Fp8 = Fp8::zero();
    let mut allocy: Fp8 = Fp8::zero();
    bls24_Fp8_felem_copy(&mut allocx, &inx);
    bls24_Fp8_felem_copy(&mut allocy, &iny);
    bls24_Fp4_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bls24_Fp4_add(&mut out.c1, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bls24_Fp8_sub(mut out: &mut Fp8, inx: &Fp8, iny: &Fp8) {
    let mut allocx: Fp8 = Fp8::zero();
    let mut allocy: Fp8 = Fp8::zero();
    bls24_Fp8_felem_copy(&mut allocx, &inx);
    bls24_Fp8_felem_copy(&mut allocy, &iny);
    bls24_Fp4_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bls24_Fp4_sub(&mut out.c1, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bls24_Fp8_mul(mut out: &mut Fp8, inx: &Fp8, iny: &Fp8) {
    let mut v0: Fp4 = Fp4::zero();
    let mut v1: Fp4 = Fp4::zero();
    let mut v2: Fp4 = Fp4::zero();
    bls24_Fp4_mul(&mut v0, &inx.c0, &iny.c0);
    bls24_Fp4_mul(&mut v1, &inx.c1, &iny.c1);
    bls24_Fp4_add(&mut v2, &inx.c0, &inx.c1);
    bls24_Fp4_add(&mut out.c1, &iny.c0, &iny.c1);
    let __ac0 = out.c1.clone();
    bls24_Fp4_mul(&mut out.c1, &__ac0, &v2);
    let __ac1 = out.c1.clone();
    bls24_Fp4_sub(&mut out.c1, &__ac1, &v0);
    let __ac2 = out.c1.clone();
    bls24_Fp4_sub(&mut out.c1, &__ac2, &v1);
    bls24_Fp4_mul_by_v(&mut v2, &v1);
    bls24_Fp4_add(&mut out.c0, &v0, &v2);
}

#[inline]
pub fn bls24_Fp8_square(mut out: &mut Fp8, x: &Fp8) {
    let mut v0: Fp4 = Fp4::zero();
    let mut v1: Fp4 = Fp4::zero();
    let mut v2: Fp4 = Fp4::zero();
    bls24_Fp4_square(&mut v0, &x.c0);
    bls24_Fp4_square(&mut v1, &x.c1);
    bls24_Fp4_mul(&mut v2, &x.c0, &x.c1);
    bls24_Fp4_add(&mut out.c1, &v2, &v2);
    let __ac0 = v1.clone();
    bls24_Fp4_mul_by_v(&mut v1, &__ac0);
    bls24_Fp4_add(&mut out.c0, &v0, &v1);
}

#[inline]
pub fn bls24_Fp8_select_znz(mut out: &mut Fp8, c: u64, inx: &Fp8, iny: &Fp8) {
    let mut allocx: Fp8 = Fp8::zero();
    let mut allocy: Fp8 = Fp8::zero();
    bls24_Fp8_felem_copy(&mut allocx, &inx);
    bls24_Fp8_felem_copy(&mut allocy, &iny);
    bls24_Fp4_select_znz(&mut out.c0, c, &allocx.c0, &allocy.c0);
    bls24_Fp4_select_znz(&mut out.c1, c, &allocx.c1, &allocy.c1);
}

#[inline]
pub fn bls24_Fp8_mul_by_w(mut out: &mut Fp8, x: &Fp8) {
    let mut wtmp: Fp4 = Fp4::zero();
    bls24_Fp4_mul_by_v(&mut wtmp, &x.c1);
    bls24_Fp4_felem_copy(&mut out.c1, &x.c0);
    bls24_Fp4_felem_copy(&mut out.c0, &wtmp);
}

#[inline]
pub fn bls24_Fp24_felem_copy(mut out: &mut Fp24, x: &Fp24) {
    bls24_Fp8_felem_copy(&mut out.c0, &x.c0);
    bls24_Fp8_felem_copy(&mut out.c1, &x.c1);
    bls24_Fp8_felem_copy(&mut out.c2, &x.c2);
}

#[inline]
pub fn bls24_Fp24_zero(mut out: &mut Fp24) {
    bls24_Fp8_zero(&mut out.c0, );
    bls24_Fp8_zero(&mut out.c1, );
    bls24_Fp8_zero(&mut out.c2, );
}

#[inline]
pub fn bls24_Fp24_one(mut out: &mut Fp24) {
    bls24_Fp8_one(&mut out.c0, );
    bls24_Fp8_zero(&mut out.c1, );
    bls24_Fp8_zero(&mut out.c2, );
}

#[inline]
pub fn bls24_Fp24_opp(mut out: &mut Fp24, x: &Fp24) {
    bls24_Fp8_opp(&mut out.c0, &x.c0);
    bls24_Fp8_opp(&mut out.c1, &x.c1);
    bls24_Fp8_opp(&mut out.c2, &x.c2);
}

#[inline]
pub fn bls24_Fp24_add(mut out: &mut Fp24, inx: &Fp24, iny: &Fp24) {
    let mut allocx: Fp24 = Fp24::zero();
    let mut allocy: Fp24 = Fp24::zero();
    bls24_Fp24_felem_copy(&mut allocx, &inx);
    bls24_Fp24_felem_copy(&mut allocy, &iny);
    bls24_Fp8_add(&mut out.c0, &allocx.c0, &allocy.c0);
    bls24_Fp8_add(&mut out.c1, &allocx.c1, &allocy.c1);
    bls24_Fp8_add(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bls24_Fp24_sub(mut out: &mut Fp24, inx: &Fp24, iny: &Fp24) {
    let mut allocx: Fp24 = Fp24::zero();
    let mut allocy: Fp24 = Fp24::zero();
    bls24_Fp24_felem_copy(&mut allocx, &inx);
    bls24_Fp24_felem_copy(&mut allocy, &iny);
    bls24_Fp8_sub(&mut out.c0, &allocx.c0, &allocy.c0);
    bls24_Fp8_sub(&mut out.c1, &allocx.c1, &allocy.c1);
    bls24_Fp8_sub(&mut out.c2, &allocx.c2, &allocy.c2);
}

#[inline]
pub fn bls24_Fp24_mul(mut out: &mut Fp24, inx: &Fp24, iny: &Fp24) {
    let mut a0b0: Fp8 = Fp8::zero();
    let mut a1b1: Fp8 = Fp8::zero();
    let mut a2b2: Fp8 = Fp8::zero();
    let mut t0: Fp8 = Fp8::zero();
    let mut t1: Fp8 = Fp8::zero();
    let mut t2: Fp8 = Fp8::zero();
    bls24_Fp8_mul(&mut a0b0, &inx.c0, &iny.c0);
    bls24_Fp8_mul(&mut a1b1, &inx.c1, &iny.c1);
    bls24_Fp8_mul(&mut a2b2, &inx.c2, &iny.c2);
    bls24_Fp8_add(&mut t0, &inx.c1, &inx.c2);
    bls24_Fp8_add(&mut t1, &iny.c1, &iny.c2);
    let __ac0 = t0.clone();
    bls24_Fp8_mul(&mut t0, &__ac0, &t1);
    let __ac1 = t0.clone();
    bls24_Fp8_sub(&mut t0, &__ac1, &a1b1);
    let __ac2 = t0.clone();
    bls24_Fp8_sub(&mut t0, &__ac2, &a2b2);
    let __ac3 = t0.clone();
    bls24_Fp8_mul_by_w(&mut t0, &__ac3);
    bls24_Fp8_add(&mut out.c0, &a0b0, &t0);
    bls24_Fp8_add(&mut t0, &inx.c0, &inx.c1);
    bls24_Fp8_add(&mut t1, &iny.c0, &iny.c1);
    let __ac4 = t0.clone();
    bls24_Fp8_mul(&mut t0, &__ac4, &t1);
    let __ac5 = t0.clone();
    bls24_Fp8_sub(&mut t0, &__ac5, &a0b0);
    let __ac6 = t0.clone();
    bls24_Fp8_sub(&mut t0, &__ac6, &a1b1);
    bls24_Fp8_mul_by_w(&mut t1, &a2b2);
    bls24_Fp8_add(&mut out.c1, &t0, &t1);
    bls24_Fp8_add(&mut t0, &inx.c0, &inx.c2);
    bls24_Fp8_add(&mut t1, &iny.c0, &iny.c2);
    let __ac7 = t0.clone();
    bls24_Fp8_mul(&mut t0, &__ac7, &t1);
    let __ac8 = t0.clone();
    bls24_Fp8_sub(&mut t0, &__ac8, &a0b0);
    let __ac9 = t0.clone();
    bls24_Fp8_sub(&mut t0, &__ac9, &a2b2);
    bls24_Fp8_add(&mut out.c2, &t0, &a1b1);
}

#[inline]
pub fn bls24_Fp24_square(mut out: &mut Fp24, x: &Fp24) {
    let mut s0: Fp8 = Fp8::zero();
    let mut s1: Fp8 = Fp8::zero();
    let mut s2: Fp8 = Fp8::zero();
    let mut s3: Fp8 = Fp8::zero();
    let mut s4: Fp8 = Fp8::zero();
    bls24_Fp8_square(&mut s0, &x.c0);
    bls24_Fp8_mul(&mut s1, &x.c0, &x.c1);
    let __ac0 = s1.clone();
    bls24_Fp8_add(&mut s1, &__ac0, &__ac0);
    bls24_Fp8_sub(&mut s2, &x.c0, &x.c1);
    let __ac1 = s2.clone();
    bls24_Fp8_add(&mut s2, &__ac1, &x.c2);
    let __ac2 = s2.clone();
    bls24_Fp8_square(&mut s2, &__ac2);
    bls24_Fp8_mul(&mut s3, &x.c1, &x.c2);
    let __ac3 = s3.clone();
    bls24_Fp8_add(&mut s3, &__ac3, &__ac3);
    bls24_Fp8_square(&mut s4, &x.c2);
    bls24_Fp8_mul_by_w(&mut out.c0, &s3);
    let __ac4 = out.c0.clone();
    bls24_Fp8_add(&mut out.c0, &s0, &__ac4);
    bls24_Fp8_mul_by_w(&mut out.c1, &s4);
    let __ac5 = out.c1.clone();
    bls24_Fp8_add(&mut out.c1, &s1, &__ac5);
    bls24_Fp8_add(&mut out.c2, &s1, &s2);
    let __ac6 = out.c2.clone();
    bls24_Fp8_add(&mut out.c2, &__ac6, &s3);
    let __ac7 = out.c2.clone();
    bls24_Fp8_sub(&mut out.c2, &__ac7, &s0);
    let __ac8 = out.c2.clone();
    bls24_Fp8_sub(&mut out.c2, &__ac8, &s4);
}

#[inline]
pub fn bls24_Fp24_inv(mut out: &mut Fp24, x: &Fp24) {
    let mut vA: Fp8 = Fp8::zero();
    let mut vB: Fp8 = Fp8::zero();
    let mut vC: Fp8 = Fp8::zero();
    let mut t0: Fp8 = Fp8::zero();
    let mut t1: Fp8 = Fp8::zero();
    let mut vFF: Fp8 = Fp8::zero();
    let mut vFFi: Fp8 = Fp8::zero();
    bls24_Fp8_square(&mut t0, &x.c0);
    bls24_Fp8_mul(&mut t1, &x.c1, &x.c2);
    let __ac0 = t1.clone();
    bls24_Fp8_mul_by_w(&mut t1, &__ac0);
    bls24_Fp8_sub(&mut vA, &t0, &t1);
    bls24_Fp8_square(&mut t0, &x.c2);
    let __ac1 = t0.clone();
    bls24_Fp8_mul_by_w(&mut t0, &__ac1);
    bls24_Fp8_mul(&mut t1, &x.c0, &x.c1);
    bls24_Fp8_sub(&mut vB, &t0, &t1);
    bls24_Fp8_square(&mut t0, &x.c1);
    bls24_Fp8_mul(&mut t1, &x.c0, &x.c2);
    bls24_Fp8_sub(&mut vC, &t0, &t1);
    bls24_Fp8_mul(&mut vFF, &x.c0, &vA);
    bls24_Fp8_mul(&mut t0, &x.c2, &vB);
    bls24_Fp8_mul(&mut t1, &x.c1, &vC);
    let __ac2 = t0.clone();
    bls24_Fp8_add(&mut t0, &__ac2, &t1);
    let __ac3 = t0.clone();
    bls24_Fp8_mul_by_w(&mut t0, &__ac3);
    let __ac4 = vFF.clone();
    bls24_Fp8_add(&mut vFF, &__ac4, &t0);
    bls24_Fp8_inv(&mut vFFi, &vFF);
    bls24_Fp8_mul(&mut out.c0, &vA, &vFFi);
    bls24_Fp8_mul(&mut out.c1, &vB, &vFFi);
    bls24_Fp8_mul(&mut out.c2, &vC, &vFFi);
}

#[inline]
pub fn bls24_Fp2_mul_by_nr(mut out: &mut Fp, x: &Fp) {
    bls24_509_opp(&mut out, &x);
}

#[inline]
pub fn bls24_Fp2_mul_xi(mut out: &mut Fp2, x: &Fp2) {
    let mut atmp: Fp = Fp::zero();
    bls24_509_add(&mut atmp, &x.c0, &x.c1);
    bls24_509_sub(&mut out.c0, &x.c0, &x.c1);
    bls24_509_felem_copy(&mut out.c1, &atmp);
}

#[inline]
pub fn bls24_Fp4_mul_by_v(mut out: &mut Fp4, x: &Fp4) {
    let mut vtmp: Fp2 = Fp2::zero();
    bls24_Fp2_mul_xi(&mut vtmp, &x.c1);
    bls24_Fp2_felem_copy(&mut out.c1, &x.c0);
    bls24_Fp2_felem_copy(&mut out.c0, &vtmp);
}

#[inline]
pub fn bls24_Fp4_mul_fp(mut out: &mut Fp4, x: &Fp4, s: &Fp) {
    bls24_509_mul(&mut out.c0.c0, &x.c0.c0, &s);
    bls24_509_mul(&mut out.c0.c1, &x.c0.c1, &s);
    bls24_509_mul(&mut out.c1.c0, &x.c1.c0, &s);
    bls24_509_mul(&mut out.c1.c1, &x.c1.c1, &s);
}

#[inline]
pub fn bls24_make_line(mut out: &mut Fp24, lam: &Fp4, x_t: &Fp4, y_t: &Fp4, x_p: &Fp, y_p: &Fp) {
    let mut tmp: Fp4 = Fp4::zero();
    bls24_Fp4_mul(&mut tmp, &lam, &x_t);
    bls24_Fp4_sub(&mut out.c0.c0, &tmp, &y_t);
    bls24_509_from_word(&mut out.c0.c1.c0.c0, 0u64);
    bls24_509_from_word(&mut out.c0.c1.c0.c1, 0u64);
    bls24_509_from_word(&mut out.c0.c1.c1.c0, 0u64);
    bls24_509_from_word(&mut out.c0.c1.c1.c1, 0u64);
    bls24_Fp4_mul_fp(&mut tmp, &lam, &x_p);
    bls24_Fp4_opp(&mut out.c1.c0, &tmp);
    bls24_509_from_word(&mut out.c1.c1.c0.c0, 0u64);
    bls24_509_from_word(&mut out.c1.c1.c0.c1, 0u64);
    bls24_509_from_word(&mut out.c1.c1.c1.c0, 0u64);
    bls24_509_from_word(&mut out.c1.c1.c1.c1, 0u64);
    bls24_509_felem_copy(&mut out.c2.c0.c0.c0, &y_p);
    bls24_509_from_word(&mut out.c2.c0.c0.c1, 0u64);
    bls24_509_from_word(&mut out.c2.c0.c1.c0, 0u64);
    bls24_509_from_word(&mut out.c2.c0.c1.c1, 0u64);
    bls24_509_from_word(&mut out.c2.c1.c0.c0, 0u64);
    bls24_509_from_word(&mut out.c2.c1.c0.c1, 0u64);
    bls24_509_from_word(&mut out.c2.c1.c1.c0, 0u64);
    bls24_509_from_word(&mut out.c2.c1.c1.c1, 0u64);
}

#[inline]
pub fn bls24_miller_loop(mut out: &mut Fp24, p_x: &Fp, p_y: &Fp, q_x: &Fp4, q_y: &Fp4) {
    let mut f: Fp24 = Fp24::zero();
    let mut t_x: Fp4 = Fp4::zero();
    let mut t_y: Fp4 = Fp4::zero();
    let mut lambda: Fp4 = Fp4::zero();
    let mut tmp1: Fp4 = Fp4::zero();
    let mut tmp2: Fp4 = Fp4::zero();
    let mut line: Fp24 = Fp24::zero();
    bls24_509_from_word(&mut f.c0.c0.c0.c0, 1u64);
    bls24_509_from_word(&mut f.c0.c0.c0.c1, 0u64);
    bls24_509_from_word(&mut f.c0.c0.c1.c0, 0u64);
    bls24_509_from_word(&mut f.c0.c0.c1.c1, 0u64);
    bls24_509_from_word(&mut f.c0.c1.c0.c0, 0u64);
    bls24_509_from_word(&mut f.c0.c1.c0.c1, 0u64);
    bls24_509_from_word(&mut f.c0.c1.c1.c0, 0u64);
    bls24_509_from_word(&mut f.c0.c1.c1.c1, 0u64);
    bls24_509_from_word(&mut f.c1.c0.c0.c0, 0u64);
    bls24_509_from_word(&mut f.c1.c0.c0.c1, 0u64);
    bls24_509_from_word(&mut f.c1.c0.c1.c0, 0u64);
    bls24_509_from_word(&mut f.c1.c0.c1.c1, 0u64);
    bls24_509_from_word(&mut f.c1.c1.c0.c0, 0u64);
    bls24_509_from_word(&mut f.c1.c1.c0.c1, 0u64);
    bls24_509_from_word(&mut f.c1.c1.c1.c0, 0u64);
    bls24_509_from_word(&mut f.c1.c1.c1.c1, 0u64);
    bls24_509_from_word(&mut f.c2.c0.c0.c0, 0u64);
    bls24_509_from_word(&mut f.c2.c0.c0.c1, 0u64);
    bls24_509_from_word(&mut f.c2.c0.c1.c0, 0u64);
    bls24_509_from_word(&mut f.c2.c0.c1.c1, 0u64);
    bls24_509_from_word(&mut f.c2.c1.c0.c0, 0u64);
    bls24_509_from_word(&mut f.c2.c1.c0.c1, 0u64);
    bls24_509_from_word(&mut f.c2.c1.c1.c0, 0u64);
    bls24_509_from_word(&mut f.c2.c1.c1.c1, 0u64);
    bls24_Fp4_felem_copy(&mut t_x, &q_x);
    bls24_Fp4_felem_copy(&mut t_y, &q_y);
    let mut i: u64;
    i = 52u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        bls24_Fp4_square(&mut tmp1, &t_x);
        bls24_Fp4_add(&mut lambda, &tmp1, &tmp1);
        let __ac0 = lambda.clone();
        bls24_Fp4_add(&mut lambda, &__ac0, &tmp1);
        bls24_Fp4_add(&mut tmp1, &t_y, &t_y);
        let __ac1 = tmp1.clone();
        bls24_Fp4_inv(&mut tmp1, &__ac1);
        let __ac2 = lambda.clone();
        bls24_Fp4_mul(&mut lambda, &__ac2, &tmp1);
        bls24_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
        let __ac3 = f.clone();
        bls24_Fp24_square(&mut f, &__ac3);
        let __ac4 = f.clone();
        bls24_Fp24_mul(&mut f, &__ac4, &line);
        bls24_Fp4_square(&mut tmp1, &lambda);
        let __ac5 = tmp1.clone();
        bls24_Fp4_sub(&mut tmp1, &__ac5, &t_x);
        bls24_Fp4_sub(&mut tmp2, &tmp1, &t_x);
        bls24_Fp4_sub(&mut tmp1, &t_x, &tmp2);
        let __ac6 = tmp1.clone();
        bls24_Fp4_mul(&mut tmp1, &lambda, &__ac6);
        let __ac7 = t_y.clone();
        bls24_Fp4_sub(&mut t_y, &tmp1, &__ac7);
        bls24_Fp4_felem_copy(&mut t_x, &tmp2);
        let mut bit: u64;
        bit = ((2251800082118657u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            bls24_Fp4_sub(&mut tmp1, &q_y, &t_y);
            bls24_Fp4_sub(&mut tmp2, &q_x, &t_x);
            let __ac8 = tmp2.clone();
            bls24_Fp4_inv(&mut tmp2, &__ac8);
            bls24_Fp4_mul(&mut lambda, &tmp1, &tmp2);
            bls24_make_line(&mut line, &lambda, &t_x, &t_y, &p_x, &p_y);
            let __ac9 = f.clone();
            bls24_Fp24_mul(&mut f, &__ac9, &line);
            bls24_Fp4_square(&mut tmp1, &lambda);
            let __ac10 = tmp1.clone();
            bls24_Fp4_sub(&mut tmp1, &__ac10, &t_x);
            bls24_Fp4_sub(&mut tmp2, &tmp1, &q_x);
            bls24_Fp4_sub(&mut tmp1, &t_x, &tmp2);
            let __ac11 = tmp1.clone();
            bls24_Fp4_mul(&mut tmp1, &lambda, &__ac11);
            let __ac12 = t_y.clone();
            bls24_Fp4_sub(&mut t_y, &tmp1, &__ac12);
            bls24_Fp4_felem_copy(&mut t_x, &tmp2);
        } else {
        }
    }
    let __ac13 = t_y.clone();
    bls24_Fp4_opp(&mut t_y, &__ac13);
    let __ac14 = f.c1.clone();
    bls24_Fp8_opp(&mut f.c1, &__ac14);
    bls24_Fp24_felem_copy(&mut out, &f);
}

#[inline]
pub fn bls24_fp24_conjugate(mut out: &mut Fp24, x: &Fp24) {
    bls24_Fp8_felem_copy(&mut out.c0, &x.c0);
    bls24_Fp8_opp(&mut out.c1, &x.c1);
    bls24_Fp8_felem_copy(&mut out.c2, &x.c2);
}

#[inline]
pub fn bls24_fp24_pow_abs_z(mut out: &mut Fp24, x: &Fp24) {
    let mut result: Fp24 = Fp24::zero();
    let mut base: Fp24 = Fp24::zero();
    bls24_Fp24_felem_copy(&mut base, &x);
    bls24_Fp24_felem_copy(&mut result, &base);
    let mut i: u64;
    i = 51u64;
    while i != 0 {
        i = i.wrapping_sub(1u64);
        let __ac0 = result.clone();
        bls24_Fp24_square(&mut result, &__ac0);
        let mut bit: u64;
        bit = ((2251800082118657u64 >> (i & 63)) & 1u64);
        if bit != 0 {
            let __ac1 = result.clone();
            bls24_Fp24_mul(&mut result, &__ac1, &base);
        } else {
        }
    }
    bls24_Fp24_felem_copy(&mut out, &result);
}

#[inline]
pub fn bls24_fp24_pow_z(mut out: &mut Fp24, x: &Fp24) {
    let mut tmp: Fp24 = Fp24::zero();
    bls24_fp24_pow_abs_z(&mut tmp, &x);
    bls24_fp24_conjugate(&mut out, &tmp);
}

#[inline]
pub fn bls24_fp24_frob(mut out: &mut Fp24, x: &Fp24, gamma_fp4: &Fp2, gamma_fp8: &Fp4, gamma_fp24_1: &Fp8, gamma_fp24_2: &Fp8) {
    let mut tmp_fp2: Fp2 = Fp2::zero();
    let mut tmp_fp4: Fp4 = Fp4::zero();
    let mut tmp_fp8: Fp8 = Fp8::zero();
    bls24_509_felem_copy(&mut out.c0.c0.c0.c0, &x.c0.c0.c0.c0);
    bls24_509_opp(&mut out.c0.c0.c0.c1, &x.c0.c0.c0.c1);
    bls24_509_felem_copy(&mut tmp_fp2.c0, &x.c0.c0.c1.c0);
    bls24_509_opp(&mut tmp_fp2.c1, &x.c0.c0.c1.c1);
    bls24_Fp2_mul(&mut out.c0.c0.c1, &tmp_fp2, &gamma_fp4);
    bls24_509_felem_copy(&mut tmp_fp4.c0.c0, &x.c0.c1.c0.c0);
    bls24_509_opp(&mut tmp_fp4.c0.c1, &x.c0.c1.c0.c1);
    bls24_509_felem_copy(&mut tmp_fp2.c0, &x.c0.c1.c1.c0);
    bls24_509_opp(&mut tmp_fp2.c1, &x.c0.c1.c1.c1);
    bls24_Fp2_mul(&mut tmp_fp4.c1, &tmp_fp2, &gamma_fp4);
    bls24_Fp4_mul(&mut out.c0.c1, &tmp_fp4, &gamma_fp8);
    bls24_509_felem_copy(&mut tmp_fp8.c0.c0.c0, &x.c1.c0.c0.c0);
    bls24_509_opp(&mut tmp_fp8.c0.c0.c1, &x.c1.c0.c0.c1);
    bls24_509_felem_copy(&mut tmp_fp2.c0, &x.c1.c0.c1.c0);
    bls24_509_opp(&mut tmp_fp2.c1, &x.c1.c0.c1.c1);
    bls24_Fp2_mul(&mut tmp_fp8.c0.c1, &tmp_fp2, &gamma_fp4);
    bls24_509_felem_copy(&mut tmp_fp4.c0.c0, &x.c1.c1.c0.c0);
    bls24_509_opp(&mut tmp_fp4.c0.c1, &x.c1.c1.c0.c1);
    bls24_509_felem_copy(&mut tmp_fp2.c0, &x.c1.c1.c1.c0);
    bls24_509_opp(&mut tmp_fp2.c1, &x.c1.c1.c1.c1);
    bls24_Fp2_mul(&mut tmp_fp4.c1, &tmp_fp2, &gamma_fp4);
    bls24_Fp4_mul(&mut tmp_fp8.c1, &tmp_fp4, &gamma_fp8);
    bls24_Fp8_mul(&mut out.c1, &tmp_fp8, &gamma_fp24_1);
    bls24_509_felem_copy(&mut tmp_fp8.c0.c0.c0, &x.c2.c0.c0.c0);
    bls24_509_opp(&mut tmp_fp8.c0.c0.c1, &x.c2.c0.c0.c1);
    bls24_509_felem_copy(&mut tmp_fp2.c0, &x.c2.c0.c1.c0);
    bls24_509_opp(&mut tmp_fp2.c1, &x.c2.c0.c1.c1);
    bls24_Fp2_mul(&mut tmp_fp8.c0.c1, &tmp_fp2, &gamma_fp4);
    bls24_509_felem_copy(&mut tmp_fp4.c0.c0, &x.c2.c1.c0.c0);
    bls24_509_opp(&mut tmp_fp4.c0.c1, &x.c2.c1.c0.c1);
    bls24_509_felem_copy(&mut tmp_fp2.c0, &x.c2.c1.c1.c0);
    bls24_509_opp(&mut tmp_fp2.c1, &x.c2.c1.c1.c1);
    bls24_Fp2_mul(&mut tmp_fp4.c1, &tmp_fp2, &gamma_fp4);
    bls24_Fp4_mul(&mut tmp_fp8.c1, &tmp_fp4, &gamma_fp8);
    bls24_Fp8_mul(&mut out.c2, &tmp_fp8, &gamma_fp24_2);
}

#[inline]
pub fn bls24_fp24_frob_p2(mut out: &mut Fp24, x: &Fp24, gamma_fp4_p2: &Fp2, gamma_fp8_p2: &Fp4, gamma_fp24_p2_1: &Fp8, gamma_fp24_p2_2: &Fp8) {
    let mut tmp_fp4: Fp4 = Fp4::zero();
    let mut tmp_fp8: Fp8 = Fp8::zero();
    bls24_Fp2_felem_copy(&mut out.c0.c0.c0, &x.c0.c0.c0);
    bls24_Fp2_mul(&mut out.c0.c0.c1, &x.c0.c0.c1, &gamma_fp4_p2);
    bls24_Fp2_felem_copy(&mut tmp_fp4.c0, &x.c0.c1.c0);
    bls24_Fp2_mul(&mut tmp_fp4.c1, &x.c0.c1.c1, &gamma_fp4_p2);
    bls24_Fp4_mul(&mut out.c0.c1, &tmp_fp4, &gamma_fp8_p2);
    bls24_Fp2_felem_copy(&mut tmp_fp8.c0.c0, &x.c1.c0.c0);
    bls24_Fp2_mul(&mut tmp_fp8.c0.c1, &x.c1.c0.c1, &gamma_fp4_p2);
    bls24_Fp2_felem_copy(&mut tmp_fp4.c0, &x.c1.c1.c0);
    bls24_Fp2_mul(&mut tmp_fp4.c1, &x.c1.c1.c1, &gamma_fp4_p2);
    bls24_Fp4_mul(&mut tmp_fp8.c1, &tmp_fp4, &gamma_fp8_p2);
    bls24_Fp8_mul(&mut out.c1, &tmp_fp8, &gamma_fp24_p2_1);
    bls24_Fp2_felem_copy(&mut tmp_fp8.c0.c0, &x.c2.c0.c0);
    bls24_Fp2_mul(&mut tmp_fp8.c0.c1, &x.c2.c0.c1, &gamma_fp4_p2);
    bls24_Fp2_felem_copy(&mut tmp_fp4.c0, &x.c2.c1.c0);
    bls24_Fp2_mul(&mut tmp_fp4.c1, &x.c2.c1.c1, &gamma_fp4_p2);
    bls24_Fp4_mul(&mut tmp_fp8.c1, &tmp_fp4, &gamma_fp8_p2);
    bls24_Fp8_mul(&mut out.c2, &tmp_fp8, &gamma_fp24_p2_2);
}

#[inline]
pub fn bls24_fp24_frob_p4(mut out: &mut Fp24, x: &Fp24, gamma_fp4_p4: &Fp2, gamma_fp8_p4: &Fp4, gamma_fp24_p4_1: &Fp8, gamma_fp24_p4_2: &Fp8) {
    let mut tmp_fp4: Fp4 = Fp4::zero();
    let mut tmp_fp8: Fp8 = Fp8::zero();
    bls24_Fp2_felem_copy(&mut out.c0.c0.c0, &x.c0.c0.c0);
    bls24_Fp2_mul(&mut out.c0.c0.c1, &x.c0.c0.c1, &gamma_fp4_p4);
    bls24_Fp2_felem_copy(&mut tmp_fp4.c0, &x.c0.c1.c0);
    bls24_Fp2_mul(&mut tmp_fp4.c1, &x.c0.c1.c1, &gamma_fp4_p4);
    bls24_Fp4_mul(&mut out.c0.c1, &tmp_fp4, &gamma_fp8_p4);
    bls24_Fp2_felem_copy(&mut tmp_fp8.c0.c0, &x.c1.c0.c0);
    bls24_Fp2_mul(&mut tmp_fp8.c0.c1, &x.c1.c0.c1, &gamma_fp4_p4);
    bls24_Fp2_felem_copy(&mut tmp_fp4.c0, &x.c1.c1.c0);
    bls24_Fp2_mul(&mut tmp_fp4.c1, &x.c1.c1.c1, &gamma_fp4_p4);
    bls24_Fp4_mul(&mut tmp_fp8.c1, &tmp_fp4, &gamma_fp8_p4);
    bls24_Fp8_mul(&mut out.c1, &tmp_fp8, &gamma_fp24_p4_1);
    bls24_Fp2_felem_copy(&mut tmp_fp8.c0.c0, &x.c2.c0.c0);
    bls24_Fp2_mul(&mut tmp_fp8.c0.c1, &x.c2.c0.c1, &gamma_fp4_p4);
    bls24_Fp2_felem_copy(&mut tmp_fp4.c0, &x.c2.c1.c0);
    bls24_Fp2_mul(&mut tmp_fp4.c1, &x.c2.c1.c1, &gamma_fp4_p4);
    bls24_Fp4_mul(&mut tmp_fp8.c1, &tmp_fp4, &gamma_fp8_p4);
    bls24_Fp8_mul(&mut out.c2, &tmp_fp8, &gamma_fp24_p4_2);
}

#[inline]
pub fn bls24_final_exp_easy(mut out: &mut Fp24, f: &Fp24, gamma_fp4_p4: &Fp2, gamma_fp8_p4: &Fp4, gamma_fp24_p4_1: &Fp8, gamma_fp24_p4_2: &Fp8) {
    let mut t0: Fp24 = Fp24::zero();
    let mut t1: Fp24 = Fp24::zero();
    bls24_fp24_conjugate(&mut t0, &f);
    bls24_Fp24_inv(&mut t1, &f);
    let __ac0 = t0.clone();
    bls24_Fp24_mul(&mut t0, &__ac0, &t1);
    bls24_fp24_frob_p4(&mut t1, &t0, &gamma_fp4_p4, &gamma_fp8_p4, &gamma_fp24_p4_1, &gamma_fp24_p4_2);
    bls24_Fp24_mul(&mut out, &t1, &t0);
}

#[inline]
pub fn bls24_final_exp_hard(mut out: &mut Fp24, f: &Fp24, gamma_fp4: &Fp2, gamma_fp8: &Fp4, gamma_fp24_1: &Fp8, gamma_fp24_2: &Fp8, gamma_fp4_p2: &Fp2, gamma_fp8_p2: &Fp4, gamma_fp24_p2_1: &Fp8, gamma_fp24_p2_2: &Fp8, gamma_fp4_p4: &Fp2, gamma_fp8_p4: &Fp4, gamma_fp24_p4_1: &Fp8, gamma_fp24_p4_2: &Fp8) {
    let mut a: Fp24 = Fp24::zero();
    let mut b: Fp24 = Fp24::zero();
    let mut c: Fp24 = Fp24::zero();
    let mut d: Fp24 = Fp24::zero();
    let mut e: Fp24 = Fp24::zero();
    bls24_fp24_pow_z(&mut a, &f);
    bls24_fp24_conjugate(&mut b, &f);
    let __ac0 = b.clone();
    bls24_Fp24_mul(&mut b, &a, &__ac0);
    bls24_fp24_pow_z(&mut a, &b);
    bls24_fp24_conjugate(&mut c, &b);
    let __ac1 = c.clone();
    bls24_Fp24_mul(&mut c, &a, &__ac1);
    bls24_fp24_pow_z(&mut a, &c);
    bls24_fp24_frob(&mut b, &c, &gamma_fp4, &gamma_fp8, &gamma_fp24_1, &gamma_fp24_2);
    bls24_Fp24_mul(&mut d, &a, &b);
    bls24_fp24_pow_z(&mut a, &d);
    let __ac2 = a.clone();
    bls24_fp24_pow_z(&mut a, &__ac2);
    bls24_fp24_frob_p2(&mut b, &d, &gamma_fp4_p2, &gamma_fp8_p2, &gamma_fp24_p2_1, &gamma_fp24_p2_2);
    bls24_Fp24_mul(&mut e, &a, &b);
    bls24_fp24_pow_z(&mut a, &e);
    let __ac3 = a.clone();
    bls24_fp24_pow_z(&mut a, &__ac3);
    let __ac4 = a.clone();
    bls24_fp24_pow_z(&mut a, &__ac4);
    let __ac5 = a.clone();
    bls24_fp24_pow_z(&mut a, &__ac5);
    bls24_fp24_frob_p4(&mut b, &e, &gamma_fp4_p4, &gamma_fp8_p4, &gamma_fp24_p4_1, &gamma_fp24_p4_2);
    let __ac6 = a.clone();
    bls24_Fp24_mul(&mut a, &__ac6, &b);
    bls24_fp24_conjugate(&mut c, &e);
    let __ac7 = a.clone();
    bls24_Fp24_mul(&mut a, &__ac7, &c);
    bls24_Fp24_square(&mut b, &f);
    let __ac8 = b.clone();
    bls24_Fp24_mul(&mut b, &__ac8, &f);
    bls24_Fp24_mul(&mut out, &a, &b);
}

#[inline]
pub fn bls24_final_exp(mut out: &mut Fp24, f: &Fp24, gamma_fp4: &Fp2, gamma_fp8: &Fp4, gamma_fp24_1: &Fp8, gamma_fp24_2: &Fp8, gamma_fp4_p2: &Fp2, gamma_fp8_p2: &Fp4, gamma_fp24_p2_1: &Fp8, gamma_fp24_p2_2: &Fp8, gamma_fp4_p4: &Fp2, gamma_fp8_p4: &Fp4, gamma_fp24_p4_1: &Fp8, gamma_fp24_p4_2: &Fp8) {
    let mut easy_result: Fp24 = Fp24::zero();
    bls24_final_exp_easy(&mut easy_result, &f, &gamma_fp4_p4, &gamma_fp8_p4, &gamma_fp24_p4_1, &gamma_fp24_p4_2);
    bls24_final_exp_hard(&mut out, &easy_result, &gamma_fp4, &gamma_fp8, &gamma_fp24_1, &gamma_fp24_2, &gamma_fp4_p2, &gamma_fp8_p2, &gamma_fp24_p2_1, &gamma_fp24_p2_2, &gamma_fp4_p4, &gamma_fp8_p4, &gamma_fp24_p4_1, &gamma_fp24_p4_2);
}

