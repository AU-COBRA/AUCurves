//! Runtime for the Rocq-emitted bedrock2 functions (`g1_msm_extracted.rs`,
//! `g2_extracted.rs`).
//!
//! Hand-written, safe Rust.  The printer `src/Bedrock/ToSafeRustArena.v`
//! keeps bedrock2's memory model: a bedrock2 pointer is a `u64` byte
//! address into one [`Mem`], every load/store goes through it, and
//! `stackalloc` is a LIFO bump allocation.  A wrong address is a
//! bounds-check panic, never undefined behaviour.
//!
//! Also here: the word operations whose bedrock2 (coqutil `Naive` word)
//! semantics Rust does not match directly, and the field leaves the
//! emitted code calls by name.  The leaves are the crate's own verified
//! tower leaves (`tower::bls12_{mul,add,sub,from_word}`), lifted to
//! operate on felems stored in [`Mem`] (6 little-endian u64 Montgomery
//! limbs, 48 bytes — the bedrock2 `FElem` layout of `bls12_frep`).
//! The G2 code calls the Fp2 leaves `bls12_Fp2_{mul,add,sub}`, lifted the
//! same way from `tower::bls12_Fp2_{mul,add,sub}`: an Fp2 element is 12
//! words, c0 then c1 (the layout of `QuadraticFieldExtensionsSpecs.
//! Fp2_field_representation`: `fst_felem` / `snd_felem`).

use crate::tower::{self, Fp, Fp2};

/// Lowest address of [`Mem`]; nonzero so that no live pointer is 0.
pub const BASE: u64 = 0x1000;
/// Bytes per felem (6 limbs).
pub const FE: u64 = 48;
/// Bytes per Fp2 element (12 limbs, c0 then c1).
pub const FE2: u64 = 96;

/// Word-addressed little-endian memory, addressed by bedrock2 byte
/// addresses `BASE..BASE + 8 * len`.  Grows on demand.
pub struct Mem {
    w: Vec<u64>,
    top: u64,
}

impl Mem {
    /// An empty memory with room for `bytes` bytes before it grows.
    pub fn with_capacity(bytes: usize) -> Mem {
        Mem { w: Vec::with_capacity(bytes / 8 + 1), top: BASE }
    }

    #[inline(always)]
    fn idx(&self, a: u64) -> usize {
        assert!(a >= BASE && a % 8 == 0, "bedrock2 address {:#x} out of range or unaligned", a);
        ((a - BASE) / 8) as usize
    }

    /// `stackalloc n`: `n` fresh zeroed bytes (bedrock2 leaves them
    /// arbitrary; zero is one choice).  `n` must be a multiple of 8.
    #[inline]
    pub fn alloc(&mut self, n: u64) -> u64 {
        assert!(n % 8 == 0, "stackalloc of {} bytes", n);
        let a = self.top;
        self.top += n;
        let need = ((self.top - BASE) / 8) as usize;
        if self.w.len() < need {
            self.w.resize(need, 0);
        } else {
            let i = ((a - BASE) / 8) as usize;
            self.w[i..need].fill(0);
        }
        a
    }

    /// End of the `stackalloc n` scope most recently opened.
    #[inline]
    pub fn free(&mut self, n: u64) {
        assert!(self.top - BASE >= n);
        self.top -= n;
    }

    #[inline(always)]
    pub fn load64(&self, a: u64) -> u64 { self.w[self.idx(a)] }
    #[inline(always)]
    pub fn store64(&mut self, a: u64, v: u64) { let i = self.idx(a); self.w[i] = v; }

    fn load_sub(&self, a: u64, bytes: u64) -> u64 {
        let off = a % 8;
        assert!(off + bytes <= 8, "unaligned {}-byte access at {:#x}", bytes, a);
        let w = self.w[self.idx(a - off)];
        (w >> (8 * off)) & (u64::MAX >> (64 - 8 * bytes))
    }
    fn store_sub(&mut self, a: u64, bytes: u64, v: u64) {
        let off = a % 8;
        assert!(off + bytes <= 8, "unaligned {}-byte access at {:#x}", bytes, a);
        let i = self.idx(a - off);
        let mask = (u64::MAX >> (64 - 8 * bytes)) << (8 * off);
        self.w[i] = (self.w[i] & !mask) | ((v << (8 * off)) & mask);
    }
    pub fn load8(&self, a: u64) -> u64 { self.load_sub(a, 1) }
    pub fn load16(&self, a: u64) -> u64 { self.load_sub(a, 2) }
    pub fn load32(&self, a: u64) -> u64 { self.load_sub(a, 4) }
    pub fn store8(&mut self, a: u64, v: u64) { self.store_sub(a, 1, v) }
    pub fn store16(&mut self, a: u64, v: u64) { self.store_sub(a, 2, v) }
    pub fn store32(&mut self, a: u64, v: u64) { self.store_sub(a, 4, v) }

    #[inline(always)]
    pub fn read_fp(&self, a: u64) -> Fp {
        let i = self.idx(a);
        let mut l = [0u64; 6];
        l.copy_from_slice(&self.w[i..i + 6]);
        Fp(l)
    }
    #[inline(always)]
    pub fn write_fp(&mut self, a: u64, x: &Fp) {
        let i = self.idx(a);
        self.w[i..i + 6].copy_from_slice(&x.0);
    }
    #[inline(always)]
    pub fn read_fp2(&self, a: u64) -> Fp2 {
        Fp2 { c0: self.read_fp(a), c1: self.read_fp(a + FE) }
    }
    #[inline(always)]
    pub fn write_fp2(&mut self, a: u64, x: &Fp2) {
        self.write_fp(a, &x.c0);
        self.write_fp(a + FE, &x.c1);
    }
}

// ---- word operations (coqutil Naive word semantics, width 64) ----

#[inline(always)] pub fn rt_sru(a: u64, b: u64) -> u64 { if b < 64 { a >> b } else { 0 } }
#[inline(always)] pub fn rt_slu(a: u64, b: u64) -> u64 { if b < 64 { a << b } else { 0 } }
#[inline(always)] pub fn rt_srs(a: u64, b: u64) -> u64 {
    if b < 64 { ((a as i64) >> b) as u64 } else if (a as i64) < 0 { u64::MAX } else { 0 }
}
#[inline(always)] pub fn rt_divu(a: u64, b: u64) -> u64 { if b == 0 { 0 } else { a / b } }
#[inline(always)] pub fn rt_remu(a: u64, b: u64) -> u64 { if b == 0 { a } else { a % b } }
#[inline(always)] pub fn rt_lts(a: u64, b: u64) -> u64 { ((a as i64) < (b as i64)) as u64 }
#[inline(always)] pub fn rt_mulhuu(a: u64, b: u64) -> u64 { (((a as u128) * (b as u128)) >> 64) as u64 }
pub fn rt_table8(t: &[u8], i: u64) -> u64 { t[i as usize] as u64 }
pub fn rt_table64(t: &[u8], i: u64) -> u64 {
    let i = i as usize;
    let mut b = [0u8; 8];
    b.copy_from_slice(&t[i..i + 8]);
    u64::from_le_bytes(b)
}

// ---- field leaves, by the bedrock2 names of bls12_field_parameters ----

#[inline(always)]
pub fn bls12_mul(m: &mut Mem, o: u64, x: u64, y: u64) {
    let (a, b) = (m.read_fp(x), m.read_fp(y));
    let mut r = Fp::zero();
    tower::bls12_mul(&mut r, &a, &b);
    m.write_fp(o, &r);
}
#[inline(always)]
pub fn bls12_add(m: &mut Mem, o: u64, x: u64, y: u64) {
    let (a, b) = (m.read_fp(x), m.read_fp(y));
    let mut r = Fp::zero();
    tower::bls12_add(&mut r, &a, &b);
    m.write_fp(o, &r);
}
#[inline(always)]
pub fn bls12_sub(m: &mut Mem, o: u64, x: u64, y: u64) {
    let (a, b) = (m.read_fp(x), m.read_fp(y));
    let mut r = Fp::zero();
    tower::bls12_sub(&mut r, &a, &b);
    m.write_fp(o, &r);
}
#[inline(always)]
pub fn bls12_square(m: &mut Mem, o: u64, x: u64) {
    let a = m.read_fp(x);
    let mut r = Fp::zero();
    tower::bls12_square(&mut r, &a);
    m.write_fp(o, &r);
}
/// `store_zero`'s zero: the felem 0.
pub fn bls12_zero(m: &mut Mem, o: u64) {
    let mut r = Fp::zero();
    tower::bls12_from_word(&mut r, 0);
    m.write_fp(o, &r);
}
/// `store_zero`'s one: the felem 1 (Montgomery form R mod p).
pub fn bls12_one(m: &mut Mem, o: u64) {
    let mut r = Fp::zero();
    tower::bls12_from_word(&mut r, 1);
    m.write_fp(o, &r);
}

// ---- Fp2 leaves, by the bedrock2 names of bls12_Fp2_field_parameters ----
// Inputs are read before the output is written, so the in-place calls of the
// emitted code (output pointer = an input pointer) are well defined.

#[inline(always)]
pub fn bls12_Fp2_mul(m: &mut Mem, o: u64, x: u64, y: u64) {
    let (a, b) = (m.read_fp2(x), m.read_fp2(y));
    let mut r = Fp2::zero();
    tower::bls12_Fp2_mul(&mut r, &a, &b);
    m.write_fp2(o, &r);
}
#[inline(always)]
pub fn bls12_Fp2_add(m: &mut Mem, o: u64, x: u64, y: u64) {
    let (a, b) = (m.read_fp2(x), m.read_fp2(y));
    let mut r = Fp2::zero();
    tower::bls12_Fp2_add(&mut r, &a, &b);
    m.write_fp2(o, &r);
}
#[inline(always)]
pub fn bls12_Fp2_sub(m: &mut Mem, o: u64, x: u64, y: u64) {
    let (a, b) = (m.read_fp2(x), m.read_fp2(y));
    let mut r = Fp2::zero();
    tower::bls12_Fp2_sub(&mut r, &a, &b);
    m.write_fp2(o, &r);
}
