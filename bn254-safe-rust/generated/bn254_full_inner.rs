// Auto-generated unsafe Rust from bedrock2.
// Memory accesses go through [_br2_load]/[_br2_store] helpers.
// #![allow(non_snake_case)]
// #![allow(unused_assignments)]
// #![allow(unused_variables)]
// #![allow(unused_mut)]
// #![allow(unused_parens)]
// #![allow(dead_code)]

#[inline(always)]
pub unsafe fn _br2_load(p: *const usize) -> u64 {
    *p as u64
}

#[inline(always)]
pub unsafe fn _br2_store(p: *mut usize, v: u64) {
    *p = v as usize;
}

const BN254_P: [u64; 4] = [0x3c208c16d87cfd47, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029];

#[no_mangle]
pub unsafe extern "C" fn bn254_opp(out: u64, x: u64) {
    let mut borrow: u64 = 0;
    for i in 0..4 {
        let pi = BN254_P[i];
        let xi = _br2_load((x as *const u8).wrapping_add((i * 8) as usize) as *const usize);
        let (d, b1) = pi.overflowing_sub(xi);
        let (d2, b2) = d.overflowing_sub(borrow);
        _br2_store((out as *const u8).wrapping_add((i * 8) as usize) as *mut usize, d2);
        borrow = (b1 as u64) + (b2 as u64);
    }
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_opp(out: u64, x: u64) {
    bn254_opp(out, x);
    bn254_opp(out.wrapping_add(32), x.wrapping_add(32));
}

/// Store a single u64 word into limb 0, zero the rest (4-limb field element).
#[no_mangle]
pub unsafe extern "C" fn bn254_from_word(out: u64, w: u64) {
    _br2_store(out as *mut usize, w);
    _br2_store((out as *const u8).wrapping_add(8) as *mut usize, 0);
    _br2_store((out as *const u8).wrapping_add(16) as *mut usize, 0);
    _br2_store((out as *const u8).wrapping_add(24) as *mut usize, 0);
}

/// Fp inversion via Fermat's little theorem: x^(p-2) mod p.
/// Uses a simple square-and-multiply chain with bn254_mul/bn254_square.
#[no_mangle]
pub unsafe extern "C" fn bn254_inv(out: u64, x: u64) {
    // p-2 as big-endian bit string (254 bits).
    // We use a right-to-left binary method.
    let p_minus_2: [u64; 4] = [0x3c208c16d87cfd45, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029];
    let mut base = [0u64; 4];
    let mut result = [0u64; 4];
    // Copy x into base
    for i in 0..4 { base[i] = _br2_load((x as *const u8).wrapping_add((i*8) as usize) as *const usize); }
    // result = 1 (Montgomery form: to_mont(1)). Actually start with x and adjust.
    // Simpler: result = x, then do p-3 more squarings. But Fermat needs exact p-2.
    // Use bn254_from_word to set result = 1 (NOT Montgomery form — this is raw 1).
    // For Montgomery: 1_mont = R mod p. We need the Montgomery representation.
    // R = 2^256 mod p for BN254 = 0xe0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb
    result = [0xac96341c4ffffffb, 0x36fc76959f60cd29, 0x666ea36f7879462e, 0x0e0a77c19a07df2f];
    let bp = base.as_ptr() as u64;
    let rp = result.as_mut_ptr() as u64;
    for limb_idx in 0..4 {
        let mut bits = p_minus_2[limb_idx];
        for _ in 0..64 {
            if bits & 1 == 1 {
                bn254_mul(rp, rp, bp);
            }
            bn254_square(bp, bp);
            bits >>= 1;
        }
    }
    // Copy result to out
    for i in 0..4 { _br2_store((out as *const u8).wrapping_add((i*8) as usize) as *mut usize, result[i]); }
}

/// Fp2 inversion: (a+bu)^(-1) = conj / norm, norm = a^2 + b^2 (beta=-1).
#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_inv(out: u64, x: u64) {
    let mut asq = [0u64; 4];
    let mut bsq = [0u64; 4];
    let mut norm = [0u64; 4];
    let ap = asq.as_mut_ptr() as u64;
    let bp = bsq.as_mut_ptr() as u64;
    let np = norm.as_mut_ptr() as u64;
    bn254_square(ap, x);
    bn254_square(bp, x.wrapping_add(32));
    bn254_add(np, ap, bp);
    bn254_inv(np, np);
    bn254_mul(out, x, np);
    bn254_opp(ap, x.wrapping_add(32));
    bn254_mul(out.wrapping_add(32), ap, np);
}

#[no_mangle]
pub unsafe extern "C" fn bn254_add(out0 : u64, in0 : u64, in1 : u64) {
  let mut x4 : u64;
  let mut x0 : u64;
  let mut x9 : u64;
  let mut x1 : u64;
  let mut x5 : u64;
  let mut x11 : u64;
  let mut x2 : u64;
  let mut x6 : u64;
  let mut x13 : u64;
  let mut x3 : u64;
  let mut x7 : u64;
  let mut x17 : u64;
  let mut x19 : u64;
  let mut x15 : u64;
  let mut x21 : u64;
  let mut x8 : u64;
  let mut x24 : u64;
  let mut x16 : u64;
  let mut x25 : u64;
  let mut x10 : u64;
  let mut x27 : u64;
  let mut x18 : u64;
  let mut x28 : u64;
  let mut x12 : u64;
  let mut x30 : u64;
  let mut x20 : u64;
  let mut x31 : u64;
  let mut x23 : u64;
  let mut x14 : u64;
  let mut x33 : u64;
  let mut x22 : u64;
  let mut x34 : u64;
  let mut x26 : u64;
  let mut x29 : u64;
  let mut x32 : u64;
  let mut x35 : u64;
  let mut x36 : u64;
  let mut x37 : u64;
  let mut x38 : u64;
  let mut x39 : u64;
  x0 = _br2_load((in0 as *const u8).wrapping_add((0u64) as usize) as *const usize);
  x1 = _br2_load((in0 as *const u8).wrapping_add((8u64) as usize) as *const usize);
  x2 = _br2_load((in0 as *const u8).wrapping_add((16u64) as usize) as *const usize);
  x3 = _br2_load((in0 as *const u8).wrapping_add((24u64) as usize) as *const usize);
  /*skip*/
  x4 = _br2_load((in1 as *const u8).wrapping_add((0u64) as usize) as *const usize);
  x5 = _br2_load((in1 as *const u8).wrapping_add((8u64) as usize) as *const usize);
  x6 = _br2_load((in1 as *const u8).wrapping_add((16u64) as usize) as *const usize);
  x7 = _br2_load((in1 as *const u8).wrapping_add((24u64) as usize) as *const usize);
  /*skip*/
  /*skip*/
  x8 = (x0).wrapping_add((x4));
  x9 = (if (x8) < (x0) { 1u64 } else { 0u64 }).wrapping_add((x1));
  x10 = (x9).wrapping_add((x5));
  x11 = ((if (x9) < (x1) { 1u64 } else { 0u64 }).wrapping_add((if (x10) < (x5) { 1u64 } else { 0u64 }))).wrapping_add((x2));
  x12 = (x11).wrapping_add((x6));
  x13 = ((if (x11) < (x2) { 1u64 } else { 0u64 }).wrapping_add((if (x12) < (x6) { 1u64 } else { 0u64 }))).wrapping_add((x3));
  x14 = (x13).wrapping_add((x7));
  x15 = (if (x13) < (x3) { 1u64 } else { 0u64 }).wrapping_add((if (x14) < (x7) { 1u64 } else { 0u64 }));
  x16 = (x8).wrapping_sub((4332616871279656263u64));
  x17 = (x10).wrapping_sub((10917124144477883021u64));
  x18 = (x17).wrapping_sub((if (x8) < (x16) { 1u64 } else { 0u64 }));
  x19 = (x12).wrapping_sub((13281191951274694749u64));
  x20 = (x19).wrapping_sub(((if (x10) < (x17) { 1u64 } else { 0u64 }).wrapping_add((if (x17) < (x18) { 1u64 } else { 0u64 }))));
  x21 = (x14).wrapping_sub((3486998266802970665u64));
  x22 = (x21).wrapping_sub(((if (x12) < (x19) { 1u64 } else { 0u64 }).wrapping_add((if (x19) < (x20) { 1u64 } else { 0u64 }))));
  x23 = if (x15) < ((x15).wrapping_sub(((if (x14) < (x21) { 1u64 } else { 0u64 }).wrapping_add((if (x21) < (x22) { 1u64 } else { 0u64 }))))) { 1u64 } else { 0u64 };
  x24 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x23) == (0u64) { 1u64 } else { 0u64 }));
  x25 = (x24) ^ (18446744073709551615u64);
  x26 = ((x8) & (x24)) | ((x16) & (x25));
  x27 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x23) == (0u64) { 1u64 } else { 0u64 }));
  x28 = (x27) ^ (18446744073709551615u64);
  x29 = ((x10) & (x27)) | ((x18) & (x28));
  x30 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x23) == (0u64) { 1u64 } else { 0u64 }));
  x31 = (x30) ^ (18446744073709551615u64);
  x32 = ((x12) & (x30)) | ((x20) & (x31));
  x33 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x23) == (0u64) { 1u64 } else { 0u64 }));
  x34 = (x33) ^ (18446744073709551615u64);
  x35 = ((x14) & (x33)) | ((x22) & (x34));
  x36 = x26;
  x37 = x29;
  x38 = x32;
  x39 = x35;
  /*skip*/
  _br2_store((out0 as *const u8).wrapping_add((0u64) as usize) as *mut usize, x36);
  _br2_store((out0 as *const u8).wrapping_add((8u64) as usize) as *mut usize, x37);
  _br2_store((out0 as *const u8).wrapping_add((16u64) as usize) as *mut usize, x38);
  _br2_store((out0 as *const u8).wrapping_add((24u64) as usize) as *mut usize, x39);
  /*skip*/
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_sub(out0 : u64, in0 : u64, in1 : u64) {
  let mut x4 : u64;
  let mut x5 : u64;
  let mut x0 : u64;
  let mut x6 : u64;
  let mut x1 : u64;
  let mut x9 : u64;
  let mut x7 : u64;
  let mut x2 : u64;
  let mut x11 : u64;
  let mut x3 : u64;
  let mut x13 : u64;
  let mut x8 : u64;
  let mut x17 : u64;
  let mut x10 : u64;
  let mut x19 : u64;
  let mut x12 : u64;
  let mut x14 : u64;
  let mut x15 : u64;
  let mut x16 : u64;
  let mut x18 : u64;
  let mut x20 : u64;
  let mut x21 : u64;
  let mut x22 : u64;
  let mut x23 : u64;
  let mut x24 : u64;
  let mut x25 : u64;
  x0 = _br2_load((in0 as *const u8).wrapping_add((0u64) as usize) as *const usize);
  x1 = _br2_load((in0 as *const u8).wrapping_add((8u64) as usize) as *const usize);
  x2 = _br2_load((in0 as *const u8).wrapping_add((16u64) as usize) as *const usize);
  x3 = _br2_load((in0 as *const u8).wrapping_add((24u64) as usize) as *const usize);
  /*skip*/
  x4 = _br2_load((in1 as *const u8).wrapping_add((0u64) as usize) as *const usize);
  x5 = _br2_load((in1 as *const u8).wrapping_add((8u64) as usize) as *const usize);
  x6 = _br2_load((in1 as *const u8).wrapping_add((16u64) as usize) as *const usize);
  x7 = _br2_load((in1 as *const u8).wrapping_add((24u64) as usize) as *const usize);
  /*skip*/
  /*skip*/
  x8 = (x0).wrapping_sub((x4));
  x9 = (x1).wrapping_sub((x5));
  x10 = (x9).wrapping_sub((if (x0) < (x8) { 1u64 } else { 0u64 }));
  x11 = (x2).wrapping_sub((x6));
  x12 = (x11).wrapping_sub(((if (x1) < (x9) { 1u64 } else { 0u64 }).wrapping_add((if (x9) < (x10) { 1u64 } else { 0u64 }))));
  x13 = (x3).wrapping_sub((x7));
  x14 = (x13).wrapping_sub(((if (x2) < (x11) { 1u64 } else { 0u64 }).wrapping_add((if (x11) < (x12) { 1u64 } else { 0u64 }))));
  x15 = ((0u64.wrapping_sub(1u64))).wrapping_add((if ((if (x3) < (x13) { 1u64 } else { 0u64 }).wrapping_add((if (x13) < (x14) { 1u64 } else { 0u64 }))) == (0u64) { 1u64 } else { 0u64 }));
  x16 = (x8).wrapping_add(((x15) & (4332616871279656263u64)));
  x17 = (if (x16) < (x8) { 1u64 } else { 0u64 }).wrapping_add((x10));
  x18 = (x17).wrapping_add(((x15) & (10917124144477883021u64)));
  x19 = ((if (x17) < (x10) { 1u64 } else { 0u64 }).wrapping_add((if (x18) < ((x15) & (10917124144477883021u64)) { 1u64 } else { 0u64 }))).wrapping_add((x12));
  x20 = (x19).wrapping_add(((x15) & (13281191951274694749u64)));
  x21 = (((if (x19) < (x12) { 1u64 } else { 0u64 }).wrapping_add((if (x20) < ((x15) & (13281191951274694749u64)) { 1u64 } else { 0u64 }))).wrapping_add((x14))).wrapping_add(((x15) & (3486998266802970665u64)));
  x22 = x16;
  x23 = x18;
  x24 = x20;
  x25 = x21;
  /*skip*/
  _br2_store((out0 as *const u8).wrapping_add((0u64) as usize) as *mut usize, x22);
  _br2_store((out0 as *const u8).wrapping_add((8u64) as usize) as *mut usize, x23);
  _br2_store((out0 as *const u8).wrapping_add((16u64) as usize) as *mut usize, x24);
  _br2_store((out0 as *const u8).wrapping_add((24u64) as usize) as *mut usize, x25);
  /*skip*/
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_mul(out0 : u64, in0 : u64, in1 : u64) {
  let mut x1 : u64;
  let mut x2 : u64;
  let mut x3 : u64;
  let mut x0 : u64;
  let mut x11 : u64;
  let mut x16 : u64;
  let mut x19 : u64;
  let mut x21 : u64;
  let mut x17 : u64;
  let mut x22 : u64;
  let mut x14 : u64;
  let mut x23 : u64;
  let mut x25 : u64;
  let mut x26 : u64;
  let mut x15 : u64;
  let mut x27 : u64;
  let mut x12 : u64;
  let mut x28 : u64;
  let mut x30 : u64;
  let mut x31 : u64;
  let mut x13 : u64;
  let mut x33 : u64;
  let mut x38 : u64;
  let mut x41 : u64;
  let mut x43 : u64;
  let mut x39 : u64;
  let mut x44 : u64;
  let mut x36 : u64;
  let mut x45 : u64;
  let mut x47 : u64;
  let mut x48 : u64;
  let mut x37 : u64;
  let mut x49 : u64;
  let mut x34 : u64;
  let mut x50 : u64;
  let mut x52 : u64;
  let mut x53 : u64;
  let mut x35 : u64;
  let mut x40 : u64;
  let mut x55 : u64;
  let mut x18 : u64;
  let mut x56 : u64;
  let mut x20 : u64;
  let mut x57 : u64;
  let mut x42 : u64;
  let mut x58 : u64;
  let mut x60 : u64;
  let mut x61 : u64;
  let mut x24 : u64;
  let mut x62 : u64;
  let mut x46 : u64;
  let mut x63 : u64;
  let mut x65 : u64;
  let mut x66 : u64;
  let mut x29 : u64;
  let mut x67 : u64;
  let mut x51 : u64;
  let mut x68 : u64;
  let mut x70 : u64;
  let mut x71 : u64;
  let mut x32 : u64;
  let mut x72 : u64;
  let mut x54 : u64;
  let mut x73 : u64;
  let mut x75 : u64;
  let mut x8 : u64;
  let mut x81 : u64;
  let mut x84 : u64;
  let mut x86 : u64;
  let mut x82 : u64;
  let mut x87 : u64;
  let mut x79 : u64;
  let mut x88 : u64;
  let mut x90 : u64;
  let mut x91 : u64;
  let mut x80 : u64;
  let mut x92 : u64;
  let mut x77 : u64;
  let mut x93 : u64;
  let mut x95 : u64;
  let mut x96 : u64;
  let mut x78 : u64;
  let mut x83 : u64;
  let mut x59 : u64;
  let mut x99 : u64;
  let mut x64 : u64;
  let mut x100 : u64;
  let mut x85 : u64;
  let mut x101 : u64;
  let mut x103 : u64;
  let mut x104 : u64;
  let mut x69 : u64;
  let mut x105 : u64;
  let mut x89 : u64;
  let mut x106 : u64;
  let mut x108 : u64;
  let mut x109 : u64;
  let mut x74 : u64;
  let mut x110 : u64;
  let mut x94 : u64;
  let mut x111 : u64;
  let mut x113 : u64;
  let mut x114 : u64;
  let mut x76 : u64;
  let mut x115 : u64;
  let mut x97 : u64;
  let mut x116 : u64;
  let mut x118 : u64;
  let mut x120 : u64;
  let mut x125 : u64;
  let mut x128 : u64;
  let mut x130 : u64;
  let mut x126 : u64;
  let mut x131 : u64;
  let mut x123 : u64;
  let mut x132 : u64;
  let mut x134 : u64;
  let mut x135 : u64;
  let mut x124 : u64;
  let mut x136 : u64;
  let mut x121 : u64;
  let mut x137 : u64;
  let mut x139 : u64;
  let mut x140 : u64;
  let mut x122 : u64;
  let mut x127 : u64;
  let mut x142 : u64;
  let mut x98 : u64;
  let mut x143 : u64;
  let mut x102 : u64;
  let mut x144 : u64;
  let mut x129 : u64;
  let mut x145 : u64;
  let mut x147 : u64;
  let mut x148 : u64;
  let mut x107 : u64;
  let mut x149 : u64;
  let mut x133 : u64;
  let mut x150 : u64;
  let mut x152 : u64;
  let mut x153 : u64;
  let mut x112 : u64;
  let mut x154 : u64;
  let mut x138 : u64;
  let mut x155 : u64;
  let mut x157 : u64;
  let mut x158 : u64;
  let mut x117 : u64;
  let mut x159 : u64;
  let mut x141 : u64;
  let mut x160 : u64;
  let mut x162 : u64;
  let mut x163 : u64;
  let mut x119 : u64;
  let mut x9 : u64;
  let mut x169 : u64;
  let mut x172 : u64;
  let mut x174 : u64;
  let mut x170 : u64;
  let mut x175 : u64;
  let mut x167 : u64;
  let mut x176 : u64;
  let mut x178 : u64;
  let mut x179 : u64;
  let mut x168 : u64;
  let mut x180 : u64;
  let mut x165 : u64;
  let mut x181 : u64;
  let mut x183 : u64;
  let mut x184 : u64;
  let mut x166 : u64;
  let mut x171 : u64;
  let mut x146 : u64;
  let mut x187 : u64;
  let mut x151 : u64;
  let mut x188 : u64;
  let mut x173 : u64;
  let mut x189 : u64;
  let mut x191 : u64;
  let mut x192 : u64;
  let mut x156 : u64;
  let mut x193 : u64;
  let mut x177 : u64;
  let mut x194 : u64;
  let mut x196 : u64;
  let mut x197 : u64;
  let mut x161 : u64;
  let mut x198 : u64;
  let mut x182 : u64;
  let mut x199 : u64;
  let mut x201 : u64;
  let mut x202 : u64;
  let mut x164 : u64;
  let mut x203 : u64;
  let mut x185 : u64;
  let mut x204 : u64;
  let mut x206 : u64;
  let mut x208 : u64;
  let mut x213 : u64;
  let mut x216 : u64;
  let mut x218 : u64;
  let mut x214 : u64;
  let mut x219 : u64;
  let mut x211 : u64;
  let mut x220 : u64;
  let mut x222 : u64;
  let mut x223 : u64;
  let mut x212 : u64;
  let mut x224 : u64;
  let mut x209 : u64;
  let mut x225 : u64;
  let mut x227 : u64;
  let mut x228 : u64;
  let mut x210 : u64;
  let mut x215 : u64;
  let mut x230 : u64;
  let mut x186 : u64;
  let mut x231 : u64;
  let mut x190 : u64;
  let mut x232 : u64;
  let mut x217 : u64;
  let mut x233 : u64;
  let mut x235 : u64;
  let mut x236 : u64;
  let mut x195 : u64;
  let mut x237 : u64;
  let mut x221 : u64;
  let mut x238 : u64;
  let mut x240 : u64;
  let mut x241 : u64;
  let mut x200 : u64;
  let mut x242 : u64;
  let mut x226 : u64;
  let mut x243 : u64;
  let mut x245 : u64;
  let mut x246 : u64;
  let mut x205 : u64;
  let mut x247 : u64;
  let mut x229 : u64;
  let mut x248 : u64;
  let mut x250 : u64;
  let mut x251 : u64;
  let mut x207 : u64;
  let mut x7 : u64;
  let mut x6 : u64;
  let mut x5 : u64;
  let mut x10 : u64;
  let mut x4 : u64;
  let mut x257 : u64;
  let mut x260 : u64;
  let mut x262 : u64;
  let mut x258 : u64;
  let mut x263 : u64;
  let mut x255 : u64;
  let mut x264 : u64;
  let mut x266 : u64;
  let mut x267 : u64;
  let mut x256 : u64;
  let mut x268 : u64;
  let mut x253 : u64;
  let mut x269 : u64;
  let mut x271 : u64;
  let mut x272 : u64;
  let mut x254 : u64;
  let mut x259 : u64;
  let mut x234 : u64;
  let mut x275 : u64;
  let mut x239 : u64;
  let mut x276 : u64;
  let mut x261 : u64;
  let mut x277 : u64;
  let mut x279 : u64;
  let mut x280 : u64;
  let mut x244 : u64;
  let mut x281 : u64;
  let mut x265 : u64;
  let mut x282 : u64;
  let mut x284 : u64;
  let mut x285 : u64;
  let mut x249 : u64;
  let mut x286 : u64;
  let mut x270 : u64;
  let mut x287 : u64;
  let mut x289 : u64;
  let mut x290 : u64;
  let mut x252 : u64;
  let mut x291 : u64;
  let mut x273 : u64;
  let mut x292 : u64;
  let mut x294 : u64;
  let mut x296 : u64;
  let mut x301 : u64;
  let mut x304 : u64;
  let mut x306 : u64;
  let mut x302 : u64;
  let mut x307 : u64;
  let mut x299 : u64;
  let mut x308 : u64;
  let mut x310 : u64;
  let mut x311 : u64;
  let mut x300 : u64;
  let mut x312 : u64;
  let mut x297 : u64;
  let mut x313 : u64;
  let mut x315 : u64;
  let mut x316 : u64;
  let mut x298 : u64;
  let mut x303 : u64;
  let mut x318 : u64;
  let mut x274 : u64;
  let mut x319 : u64;
  let mut x278 : u64;
  let mut x320 : u64;
  let mut x305 : u64;
  let mut x321 : u64;
  let mut x323 : u64;
  let mut x324 : u64;
  let mut x283 : u64;
  let mut x325 : u64;
  let mut x309 : u64;
  let mut x326 : u64;
  let mut x328 : u64;
  let mut x329 : u64;
  let mut x288 : u64;
  let mut x330 : u64;
  let mut x314 : u64;
  let mut x331 : u64;
  let mut x333 : u64;
  let mut x334 : u64;
  let mut x293 : u64;
  let mut x335 : u64;
  let mut x317 : u64;
  let mut x336 : u64;
  let mut x338 : u64;
  let mut x339 : u64;
  let mut x295 : u64;
  let mut x342 : u64;
  let mut x343 : u64;
  let mut x344 : u64;
  let mut x346 : u64;
  let mut x347 : u64;
  let mut x348 : u64;
  let mut x349 : u64;
  let mut x351 : u64;
  let mut x352 : u64;
  let mut x353 : u64;
  let mut x354 : u64;
  let mut x356 : u64;
  let mut x357 : u64;
  let mut x340 : u64;
  let mut x358 : u64;
  let mut x322 : u64;
  let mut x360 : u64;
  let mut x341 : u64;
  let mut x361 : u64;
  let mut x327 : u64;
  let mut x363 : u64;
  let mut x345 : u64;
  let mut x364 : u64;
  let mut x332 : u64;
  let mut x366 : u64;
  let mut x350 : u64;
  let mut x367 : u64;
  let mut x359 : u64;
  let mut x337 : u64;
  let mut x369 : u64;
  let mut x355 : u64;
  let mut x370 : u64;
  let mut x362 : u64;
  let mut x365 : u64;
  let mut x368 : u64;
  let mut x371 : u64;
  let mut x372 : u64;
  let mut x373 : u64;
  let mut x374 : u64;
  let mut x375 : u64;
  x0 = _br2_load((in0 as *const u8).wrapping_add((0u64) as usize) as *const usize);
  x1 = _br2_load((in0 as *const u8).wrapping_add((8u64) as usize) as *const usize);
  x2 = _br2_load((in0 as *const u8).wrapping_add((16u64) as usize) as *const usize);
  x3 = _br2_load((in0 as *const u8).wrapping_add((24u64) as usize) as *const usize);
  /*skip*/
  x4 = _br2_load((in1 as *const u8).wrapping_add((0u64) as usize) as *const usize);
  x5 = _br2_load((in1 as *const u8).wrapping_add((8u64) as usize) as *const usize);
  x6 = _br2_load((in1 as *const u8).wrapping_add((16u64) as usize) as *const usize);
  x7 = _br2_load((in1 as *const u8).wrapping_add((24u64) as usize) as *const usize);
  /*skip*/
  /*skip*/
  x8 = x1;
  x9 = x2;
  x10 = x3;
  x11 = x0;
  x12 = (x11).wrapping_mul((x7));
  x13 = (((x11) as u128).wrapping_mul((x7) as u128) >> 64) as u64;
  x14 = (x11).wrapping_mul((x6));
  x15 = (((x11) as u128).wrapping_mul((x6) as u128) >> 64) as u64;
  x16 = (x11).wrapping_mul((x5));
  x17 = (((x11) as u128).wrapping_mul((x5) as u128) >> 64) as u64;
  x18 = (x11).wrapping_mul((x4));
  x19 = (((x11) as u128).wrapping_mul((x4) as u128) >> 64) as u64;
  x20 = (x19).wrapping_add((x16));
  x21 = if (x20) < (x19) { 1u64 } else { 0u64 };
  x22 = (x21).wrapping_add((x17));
  x23 = if (x22) < (x17) { 1u64 } else { 0u64 };
  x24 = (x22).wrapping_add((x14));
  x25 = if (x24) < (x14) { 1u64 } else { 0u64 };
  x26 = (x23).wrapping_add((x25));
  x27 = (x26).wrapping_add((x15));
  x28 = if (x27) < (x15) { 1u64 } else { 0u64 };
  x29 = (x27).wrapping_add((x12));
  x30 = if (x29) < (x12) { 1u64 } else { 0u64 };
  x31 = (x28).wrapping_add((x30));
  x32 = (x31).wrapping_add((x13));
  x33 = (x18).wrapping_mul((9786893198990664585u64));
  x34 = (x33).wrapping_mul((3486998266802970665u64));
  x35 = (((x33) as u128).wrapping_mul((3486998266802970665u64) as u128) >> 64) as u64;
  x36 = (x33).wrapping_mul((13281191951274694749u64));
  x37 = (((x33) as u128).wrapping_mul((13281191951274694749u64) as u128) >> 64) as u64;
  x38 = (x33).wrapping_mul((10917124144477883021u64));
  x39 = (((x33) as u128).wrapping_mul((10917124144477883021u64) as u128) >> 64) as u64;
  x40 = (x33).wrapping_mul((4332616871279656263u64));
  x41 = (((x33) as u128).wrapping_mul((4332616871279656263u64) as u128) >> 64) as u64;
  x42 = (x41).wrapping_add((x38));
  x43 = if (x42) < (x41) { 1u64 } else { 0u64 };
  x44 = (x43).wrapping_add((x39));
  x45 = if (x44) < (x39) { 1u64 } else { 0u64 };
  x46 = (x44).wrapping_add((x36));
  x47 = if (x46) < (x36) { 1u64 } else { 0u64 };
  x48 = (x45).wrapping_add((x47));
  x49 = (x48).wrapping_add((x37));
  x50 = if (x49) < (x37) { 1u64 } else { 0u64 };
  x51 = (x49).wrapping_add((x34));
  x52 = if (x51) < (x34) { 1u64 } else { 0u64 };
  x53 = (x50).wrapping_add((x52));
  x54 = (x53).wrapping_add((x35));
  x55 = (x18).wrapping_add((x40));
  x56 = if (x55) < (x18) { 1u64 } else { 0u64 };
  x57 = (x56).wrapping_add((x20));
  x58 = if (x57) < (x20) { 1u64 } else { 0u64 };
  x59 = (x57).wrapping_add((x42));
  x60 = if (x59) < (x42) { 1u64 } else { 0u64 };
  x61 = (x58).wrapping_add((x60));
  x62 = (x61).wrapping_add((x24));
  x63 = if (x62) < (x24) { 1u64 } else { 0u64 };
  x64 = (x62).wrapping_add((x46));
  x65 = if (x64) < (x46) { 1u64 } else { 0u64 };
  x66 = (x63).wrapping_add((x65));
  x67 = (x66).wrapping_add((x29));
  x68 = if (x67) < (x29) { 1u64 } else { 0u64 };
  x69 = (x67).wrapping_add((x51));
  x70 = if (x69) < (x51) { 1u64 } else { 0u64 };
  x71 = (x68).wrapping_add((x70));
  x72 = (x71).wrapping_add((x32));
  x73 = if (x72) < (x32) { 1u64 } else { 0u64 };
  x74 = (x72).wrapping_add((x54));
  x75 = if (x74) < (x54) { 1u64 } else { 0u64 };
  x76 = (x73).wrapping_add((x75));
  x77 = (x8).wrapping_mul((x7));
  x78 = (((x8) as u128).wrapping_mul((x7) as u128) >> 64) as u64;
  x79 = (x8).wrapping_mul((x6));
  x80 = (((x8) as u128).wrapping_mul((x6) as u128) >> 64) as u64;
  x81 = (x8).wrapping_mul((x5));
  x82 = (((x8) as u128).wrapping_mul((x5) as u128) >> 64) as u64;
  x83 = (x8).wrapping_mul((x4));
  x84 = (((x8) as u128).wrapping_mul((x4) as u128) >> 64) as u64;
  x85 = (x84).wrapping_add((x81));
  x86 = if (x85) < (x84) { 1u64 } else { 0u64 };
  x87 = (x86).wrapping_add((x82));
  x88 = if (x87) < (x82) { 1u64 } else { 0u64 };
  x89 = (x87).wrapping_add((x79));
  x90 = if (x89) < (x79) { 1u64 } else { 0u64 };
  x91 = (x88).wrapping_add((x90));
  x92 = (x91).wrapping_add((x80));
  x93 = if (x92) < (x80) { 1u64 } else { 0u64 };
  x94 = (x92).wrapping_add((x77));
  x95 = if (x94) < (x77) { 1u64 } else { 0u64 };
  x96 = (x93).wrapping_add((x95));
  x97 = (x96).wrapping_add((x78));
  x98 = (x59).wrapping_add((x83));
  x99 = if (x98) < (x59) { 1u64 } else { 0u64 };
  x100 = (x99).wrapping_add((x64));
  x101 = if (x100) < (x64) { 1u64 } else { 0u64 };
  x102 = (x100).wrapping_add((x85));
  x103 = if (x102) < (x85) { 1u64 } else { 0u64 };
  x104 = (x101).wrapping_add((x103));
  x105 = (x104).wrapping_add((x69));
  x106 = if (x105) < (x69) { 1u64 } else { 0u64 };
  x107 = (x105).wrapping_add((x89));
  x108 = if (x107) < (x89) { 1u64 } else { 0u64 };
  x109 = (x106).wrapping_add((x108));
  x110 = (x109).wrapping_add((x74));
  x111 = if (x110) < (x74) { 1u64 } else { 0u64 };
  x112 = (x110).wrapping_add((x94));
  x113 = if (x112) < (x94) { 1u64 } else { 0u64 };
  x114 = (x111).wrapping_add((x113));
  x115 = (x114).wrapping_add((x76));
  x116 = if (x115) < (x76) { 1u64 } else { 0u64 };
  x117 = (x115).wrapping_add((x97));
  x118 = if (x117) < (x97) { 1u64 } else { 0u64 };
  x119 = (x116).wrapping_add((x118));
  x120 = (x98).wrapping_mul((9786893198990664585u64));
  x121 = (x120).wrapping_mul((3486998266802970665u64));
  x122 = (((x120) as u128).wrapping_mul((3486998266802970665u64) as u128) >> 64) as u64;
  x123 = (x120).wrapping_mul((13281191951274694749u64));
  x124 = (((x120) as u128).wrapping_mul((13281191951274694749u64) as u128) >> 64) as u64;
  x125 = (x120).wrapping_mul((10917124144477883021u64));
  x126 = (((x120) as u128).wrapping_mul((10917124144477883021u64) as u128) >> 64) as u64;
  x127 = (x120).wrapping_mul((4332616871279656263u64));
  x128 = (((x120) as u128).wrapping_mul((4332616871279656263u64) as u128) >> 64) as u64;
  x129 = (x128).wrapping_add((x125));
  x130 = if (x129) < (x128) { 1u64 } else { 0u64 };
  x131 = (x130).wrapping_add((x126));
  x132 = if (x131) < (x126) { 1u64 } else { 0u64 };
  x133 = (x131).wrapping_add((x123));
  x134 = if (x133) < (x123) { 1u64 } else { 0u64 };
  x135 = (x132).wrapping_add((x134));
  x136 = (x135).wrapping_add((x124));
  x137 = if (x136) < (x124) { 1u64 } else { 0u64 };
  x138 = (x136).wrapping_add((x121));
  x139 = if (x138) < (x121) { 1u64 } else { 0u64 };
  x140 = (x137).wrapping_add((x139));
  x141 = (x140).wrapping_add((x122));
  x142 = (x98).wrapping_add((x127));
  x143 = if (x142) < (x98) { 1u64 } else { 0u64 };
  x144 = (x143).wrapping_add((x102));
  x145 = if (x144) < (x102) { 1u64 } else { 0u64 };
  x146 = (x144).wrapping_add((x129));
  x147 = if (x146) < (x129) { 1u64 } else { 0u64 };
  x148 = (x145).wrapping_add((x147));
  x149 = (x148).wrapping_add((x107));
  x150 = if (x149) < (x107) { 1u64 } else { 0u64 };
  x151 = (x149).wrapping_add((x133));
  x152 = if (x151) < (x133) { 1u64 } else { 0u64 };
  x153 = (x150).wrapping_add((x152));
  x154 = (x153).wrapping_add((x112));
  x155 = if (x154) < (x112) { 1u64 } else { 0u64 };
  x156 = (x154).wrapping_add((x138));
  x157 = if (x156) < (x138) { 1u64 } else { 0u64 };
  x158 = (x155).wrapping_add((x157));
  x159 = (x158).wrapping_add((x117));
  x160 = if (x159) < (x117) { 1u64 } else { 0u64 };
  x161 = (x159).wrapping_add((x141));
  x162 = if (x161) < (x141) { 1u64 } else { 0u64 };
  x163 = (x160).wrapping_add((x162));
  x164 = (x163).wrapping_add((x119));
  x165 = (x9).wrapping_mul((x7));
  x166 = (((x9) as u128).wrapping_mul((x7) as u128) >> 64) as u64;
  x167 = (x9).wrapping_mul((x6));
  x168 = (((x9) as u128).wrapping_mul((x6) as u128) >> 64) as u64;
  x169 = (x9).wrapping_mul((x5));
  x170 = (((x9) as u128).wrapping_mul((x5) as u128) >> 64) as u64;
  x171 = (x9).wrapping_mul((x4));
  x172 = (((x9) as u128).wrapping_mul((x4) as u128) >> 64) as u64;
  x173 = (x172).wrapping_add((x169));
  x174 = if (x173) < (x172) { 1u64 } else { 0u64 };
  x175 = (x174).wrapping_add((x170));
  x176 = if (x175) < (x170) { 1u64 } else { 0u64 };
  x177 = (x175).wrapping_add((x167));
  x178 = if (x177) < (x167) { 1u64 } else { 0u64 };
  x179 = (x176).wrapping_add((x178));
  x180 = (x179).wrapping_add((x168));
  x181 = if (x180) < (x168) { 1u64 } else { 0u64 };
  x182 = (x180).wrapping_add((x165));
  x183 = if (x182) < (x165) { 1u64 } else { 0u64 };
  x184 = (x181).wrapping_add((x183));
  x185 = (x184).wrapping_add((x166));
  x186 = (x146).wrapping_add((x171));
  x187 = if (x186) < (x146) { 1u64 } else { 0u64 };
  x188 = (x187).wrapping_add((x151));
  x189 = if (x188) < (x151) { 1u64 } else { 0u64 };
  x190 = (x188).wrapping_add((x173));
  x191 = if (x190) < (x173) { 1u64 } else { 0u64 };
  x192 = (x189).wrapping_add((x191));
  x193 = (x192).wrapping_add((x156));
  x194 = if (x193) < (x156) { 1u64 } else { 0u64 };
  x195 = (x193).wrapping_add((x177));
  x196 = if (x195) < (x177) { 1u64 } else { 0u64 };
  x197 = (x194).wrapping_add((x196));
  x198 = (x197).wrapping_add((x161));
  x199 = if (x198) < (x161) { 1u64 } else { 0u64 };
  x200 = (x198).wrapping_add((x182));
  x201 = if (x200) < (x182) { 1u64 } else { 0u64 };
  x202 = (x199).wrapping_add((x201));
  x203 = (x202).wrapping_add((x164));
  x204 = if (x203) < (x164) { 1u64 } else { 0u64 };
  x205 = (x203).wrapping_add((x185));
  x206 = if (x205) < (x185) { 1u64 } else { 0u64 };
  x207 = (x204).wrapping_add((x206));
  x208 = (x186).wrapping_mul((9786893198990664585u64));
  x209 = (x208).wrapping_mul((3486998266802970665u64));
  x210 = (((x208) as u128).wrapping_mul((3486998266802970665u64) as u128) >> 64) as u64;
  x211 = (x208).wrapping_mul((13281191951274694749u64));
  x212 = (((x208) as u128).wrapping_mul((13281191951274694749u64) as u128) >> 64) as u64;
  x213 = (x208).wrapping_mul((10917124144477883021u64));
  x214 = (((x208) as u128).wrapping_mul((10917124144477883021u64) as u128) >> 64) as u64;
  x215 = (x208).wrapping_mul((4332616871279656263u64));
  x216 = (((x208) as u128).wrapping_mul((4332616871279656263u64) as u128) >> 64) as u64;
  x217 = (x216).wrapping_add((x213));
  x218 = if (x217) < (x216) { 1u64 } else { 0u64 };
  x219 = (x218).wrapping_add((x214));
  x220 = if (x219) < (x214) { 1u64 } else { 0u64 };
  x221 = (x219).wrapping_add((x211));
  x222 = if (x221) < (x211) { 1u64 } else { 0u64 };
  x223 = (x220).wrapping_add((x222));
  x224 = (x223).wrapping_add((x212));
  x225 = if (x224) < (x212) { 1u64 } else { 0u64 };
  x226 = (x224).wrapping_add((x209));
  x227 = if (x226) < (x209) { 1u64 } else { 0u64 };
  x228 = (x225).wrapping_add((x227));
  x229 = (x228).wrapping_add((x210));
  x230 = (x186).wrapping_add((x215));
  x231 = if (x230) < (x186) { 1u64 } else { 0u64 };
  x232 = (x231).wrapping_add((x190));
  x233 = if (x232) < (x190) { 1u64 } else { 0u64 };
  x234 = (x232).wrapping_add((x217));
  x235 = if (x234) < (x217) { 1u64 } else { 0u64 };
  x236 = (x233).wrapping_add((x235));
  x237 = (x236).wrapping_add((x195));
  x238 = if (x237) < (x195) { 1u64 } else { 0u64 };
  x239 = (x237).wrapping_add((x221));
  x240 = if (x239) < (x221) { 1u64 } else { 0u64 };
  x241 = (x238).wrapping_add((x240));
  x242 = (x241).wrapping_add((x200));
  x243 = if (x242) < (x200) { 1u64 } else { 0u64 };
  x244 = (x242).wrapping_add((x226));
  x245 = if (x244) < (x226) { 1u64 } else { 0u64 };
  x246 = (x243).wrapping_add((x245));
  x247 = (x246).wrapping_add((x205));
  x248 = if (x247) < (x205) { 1u64 } else { 0u64 };
  x249 = (x247).wrapping_add((x229));
  x250 = if (x249) < (x229) { 1u64 } else { 0u64 };
  x251 = (x248).wrapping_add((x250));
  x252 = (x251).wrapping_add((x207));
  x253 = (x10).wrapping_mul((x7));
  x254 = (((x10) as u128).wrapping_mul((x7) as u128) >> 64) as u64;
  x255 = (x10).wrapping_mul((x6));
  x256 = (((x10) as u128).wrapping_mul((x6) as u128) >> 64) as u64;
  x257 = (x10).wrapping_mul((x5));
  x258 = (((x10) as u128).wrapping_mul((x5) as u128) >> 64) as u64;
  x259 = (x10).wrapping_mul((x4));
  x260 = (((x10) as u128).wrapping_mul((x4) as u128) >> 64) as u64;
  x261 = (x260).wrapping_add((x257));
  x262 = if (x261) < (x260) { 1u64 } else { 0u64 };
  x263 = (x262).wrapping_add((x258));
  x264 = if (x263) < (x258) { 1u64 } else { 0u64 };
  x265 = (x263).wrapping_add((x255));
  x266 = if (x265) < (x255) { 1u64 } else { 0u64 };
  x267 = (x264).wrapping_add((x266));
  x268 = (x267).wrapping_add((x256));
  x269 = if (x268) < (x256) { 1u64 } else { 0u64 };
  x270 = (x268).wrapping_add((x253));
  x271 = if (x270) < (x253) { 1u64 } else { 0u64 };
  x272 = (x269).wrapping_add((x271));
  x273 = (x272).wrapping_add((x254));
  x274 = (x234).wrapping_add((x259));
  x275 = if (x274) < (x234) { 1u64 } else { 0u64 };
  x276 = (x275).wrapping_add((x239));
  x277 = if (x276) < (x239) { 1u64 } else { 0u64 };
  x278 = (x276).wrapping_add((x261));
  x279 = if (x278) < (x261) { 1u64 } else { 0u64 };
  x280 = (x277).wrapping_add((x279));
  x281 = (x280).wrapping_add((x244));
  x282 = if (x281) < (x244) { 1u64 } else { 0u64 };
  x283 = (x281).wrapping_add((x265));
  x284 = if (x283) < (x265) { 1u64 } else { 0u64 };
  x285 = (x282).wrapping_add((x284));
  x286 = (x285).wrapping_add((x249));
  x287 = if (x286) < (x249) { 1u64 } else { 0u64 };
  x288 = (x286).wrapping_add((x270));
  x289 = if (x288) < (x270) { 1u64 } else { 0u64 };
  x290 = (x287).wrapping_add((x289));
  x291 = (x290).wrapping_add((x252));
  x292 = if (x291) < (x252) { 1u64 } else { 0u64 };
  x293 = (x291).wrapping_add((x273));
  x294 = if (x293) < (x273) { 1u64 } else { 0u64 };
  x295 = (x292).wrapping_add((x294));
  x296 = (x274).wrapping_mul((9786893198990664585u64));
  x297 = (x296).wrapping_mul((3486998266802970665u64));
  x298 = (((x296) as u128).wrapping_mul((3486998266802970665u64) as u128) >> 64) as u64;
  x299 = (x296).wrapping_mul((13281191951274694749u64));
  x300 = (((x296) as u128).wrapping_mul((13281191951274694749u64) as u128) >> 64) as u64;
  x301 = (x296).wrapping_mul((10917124144477883021u64));
  x302 = (((x296) as u128).wrapping_mul((10917124144477883021u64) as u128) >> 64) as u64;
  x303 = (x296).wrapping_mul((4332616871279656263u64));
  x304 = (((x296) as u128).wrapping_mul((4332616871279656263u64) as u128) >> 64) as u64;
  x305 = (x304).wrapping_add((x301));
  x306 = if (x305) < (x304) { 1u64 } else { 0u64 };
  x307 = (x306).wrapping_add((x302));
  x308 = if (x307) < (x302) { 1u64 } else { 0u64 };
  x309 = (x307).wrapping_add((x299));
  x310 = if (x309) < (x299) { 1u64 } else { 0u64 };
  x311 = (x308).wrapping_add((x310));
  x312 = (x311).wrapping_add((x300));
  x313 = if (x312) < (x300) { 1u64 } else { 0u64 };
  x314 = (x312).wrapping_add((x297));
  x315 = if (x314) < (x297) { 1u64 } else { 0u64 };
  x316 = (x313).wrapping_add((x315));
  x317 = (x316).wrapping_add((x298));
  x318 = (x274).wrapping_add((x303));
  x319 = if (x318) < (x274) { 1u64 } else { 0u64 };
  x320 = (x319).wrapping_add((x278));
  x321 = if (x320) < (x278) { 1u64 } else { 0u64 };
  x322 = (x320).wrapping_add((x305));
  x323 = if (x322) < (x305) { 1u64 } else { 0u64 };
  x324 = (x321).wrapping_add((x323));
  x325 = (x324).wrapping_add((x283));
  x326 = if (x325) < (x283) { 1u64 } else { 0u64 };
  x327 = (x325).wrapping_add((x309));
  x328 = if (x327) < (x309) { 1u64 } else { 0u64 };
  x329 = (x326).wrapping_add((x328));
  x330 = (x329).wrapping_add((x288));
  x331 = if (x330) < (x288) { 1u64 } else { 0u64 };
  x332 = (x330).wrapping_add((x314));
  x333 = if (x332) < (x314) { 1u64 } else { 0u64 };
  x334 = (x331).wrapping_add((x333));
  x335 = (x334).wrapping_add((x293));
  x336 = if (x335) < (x293) { 1u64 } else { 0u64 };
  x337 = (x335).wrapping_add((x317));
  x338 = if (x337) < (x317) { 1u64 } else { 0u64 };
  x339 = (x336).wrapping_add((x338));
  x340 = (x339).wrapping_add((x295));
  x341 = (x322).wrapping_sub((4332616871279656263u64));
  x342 = if (x322) < (x341) { 1u64 } else { 0u64 };
  x343 = (x327).wrapping_sub((10917124144477883021u64));
  x344 = if (x327) < (x343) { 1u64 } else { 0u64 };
  x345 = (x343).wrapping_sub((x342));
  x346 = if (x343) < (x345) { 1u64 } else { 0u64 };
  x347 = (x344).wrapping_add((x346));
  x348 = (x332).wrapping_sub((13281191951274694749u64));
  x349 = if (x332) < (x348) { 1u64 } else { 0u64 };
  x350 = (x348).wrapping_sub((x347));
  x351 = if (x348) < (x350) { 1u64 } else { 0u64 };
  x352 = (x349).wrapping_add((x351));
  x353 = (x337).wrapping_sub((3486998266802970665u64));
  x354 = if (x337) < (x353) { 1u64 } else { 0u64 };
  x355 = (x353).wrapping_sub((x352));
  x356 = if (x353) < (x355) { 1u64 } else { 0u64 };
  x357 = (x354).wrapping_add((x356));
  x358 = (x340).wrapping_sub((x357));
  x359 = if (x340) < (x358) { 1u64 } else { 0u64 };
  x360 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x359) == (0u64) { 1u64 } else { 0u64 }));
  x361 = (x360) ^ (18446744073709551615u64);
  x362 = ((x322) & (x360)) | ((x341) & (x361));
  x363 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x359) == (0u64) { 1u64 } else { 0u64 }));
  x364 = (x363) ^ (18446744073709551615u64);
  x365 = ((x327) & (x363)) | ((x345) & (x364));
  x366 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x359) == (0u64) { 1u64 } else { 0u64 }));
  x367 = (x366) ^ (18446744073709551615u64);
  x368 = ((x332) & (x366)) | ((x350) & (x367));
  x369 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x359) == (0u64) { 1u64 } else { 0u64 }));
  x370 = (x369) ^ (18446744073709551615u64);
  x371 = ((x337) & (x369)) | ((x355) & (x370));
  x372 = x362;
  x373 = x365;
  x374 = x368;
  x375 = x371;
  /*skip*/
  _br2_store((out0 as *const u8).wrapping_add((0u64) as usize) as *mut usize, x372);
  _br2_store((out0 as *const u8).wrapping_add((8u64) as usize) as *mut usize, x373);
  _br2_store((out0 as *const u8).wrapping_add((16u64) as usize) as *mut usize, x374);
  _br2_store((out0 as *const u8).wrapping_add((24u64) as usize) as *mut usize, x375);
  /*skip*/
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_square(out0 : u64, in0 : u64) {
  let mut x7 : u64;
  let mut x12 : u64;
  let mut x15 : u64;
  let mut x17 : u64;
  let mut x13 : u64;
  let mut x18 : u64;
  let mut x10 : u64;
  let mut x19 : u64;
  let mut x21 : u64;
  let mut x22 : u64;
  let mut x11 : u64;
  let mut x23 : u64;
  let mut x8 : u64;
  let mut x24 : u64;
  let mut x26 : u64;
  let mut x27 : u64;
  let mut x9 : u64;
  let mut x29 : u64;
  let mut x34 : u64;
  let mut x37 : u64;
  let mut x39 : u64;
  let mut x35 : u64;
  let mut x40 : u64;
  let mut x32 : u64;
  let mut x41 : u64;
  let mut x43 : u64;
  let mut x44 : u64;
  let mut x33 : u64;
  let mut x45 : u64;
  let mut x30 : u64;
  let mut x46 : u64;
  let mut x48 : u64;
  let mut x49 : u64;
  let mut x31 : u64;
  let mut x36 : u64;
  let mut x51 : u64;
  let mut x14 : u64;
  let mut x52 : u64;
  let mut x16 : u64;
  let mut x53 : u64;
  let mut x38 : u64;
  let mut x54 : u64;
  let mut x56 : u64;
  let mut x57 : u64;
  let mut x20 : u64;
  let mut x58 : u64;
  let mut x42 : u64;
  let mut x59 : u64;
  let mut x61 : u64;
  let mut x62 : u64;
  let mut x25 : u64;
  let mut x63 : u64;
  let mut x47 : u64;
  let mut x64 : u64;
  let mut x66 : u64;
  let mut x67 : u64;
  let mut x28 : u64;
  let mut x68 : u64;
  let mut x50 : u64;
  let mut x69 : u64;
  let mut x71 : u64;
  let mut x4 : u64;
  let mut x77 : u64;
  let mut x80 : u64;
  let mut x82 : u64;
  let mut x78 : u64;
  let mut x83 : u64;
  let mut x75 : u64;
  let mut x84 : u64;
  let mut x86 : u64;
  let mut x87 : u64;
  let mut x76 : u64;
  let mut x88 : u64;
  let mut x73 : u64;
  let mut x89 : u64;
  let mut x91 : u64;
  let mut x92 : u64;
  let mut x74 : u64;
  let mut x79 : u64;
  let mut x55 : u64;
  let mut x95 : u64;
  let mut x60 : u64;
  let mut x96 : u64;
  let mut x81 : u64;
  let mut x97 : u64;
  let mut x99 : u64;
  let mut x100 : u64;
  let mut x65 : u64;
  let mut x101 : u64;
  let mut x85 : u64;
  let mut x102 : u64;
  let mut x104 : u64;
  let mut x105 : u64;
  let mut x70 : u64;
  let mut x106 : u64;
  let mut x90 : u64;
  let mut x107 : u64;
  let mut x109 : u64;
  let mut x110 : u64;
  let mut x72 : u64;
  let mut x111 : u64;
  let mut x93 : u64;
  let mut x112 : u64;
  let mut x114 : u64;
  let mut x116 : u64;
  let mut x121 : u64;
  let mut x124 : u64;
  let mut x126 : u64;
  let mut x122 : u64;
  let mut x127 : u64;
  let mut x119 : u64;
  let mut x128 : u64;
  let mut x130 : u64;
  let mut x131 : u64;
  let mut x120 : u64;
  let mut x132 : u64;
  let mut x117 : u64;
  let mut x133 : u64;
  let mut x135 : u64;
  let mut x136 : u64;
  let mut x118 : u64;
  let mut x123 : u64;
  let mut x138 : u64;
  let mut x94 : u64;
  let mut x139 : u64;
  let mut x98 : u64;
  let mut x140 : u64;
  let mut x125 : u64;
  let mut x141 : u64;
  let mut x143 : u64;
  let mut x144 : u64;
  let mut x103 : u64;
  let mut x145 : u64;
  let mut x129 : u64;
  let mut x146 : u64;
  let mut x148 : u64;
  let mut x149 : u64;
  let mut x108 : u64;
  let mut x150 : u64;
  let mut x134 : u64;
  let mut x151 : u64;
  let mut x153 : u64;
  let mut x154 : u64;
  let mut x113 : u64;
  let mut x155 : u64;
  let mut x137 : u64;
  let mut x156 : u64;
  let mut x158 : u64;
  let mut x159 : u64;
  let mut x115 : u64;
  let mut x5 : u64;
  let mut x165 : u64;
  let mut x168 : u64;
  let mut x170 : u64;
  let mut x166 : u64;
  let mut x171 : u64;
  let mut x163 : u64;
  let mut x172 : u64;
  let mut x174 : u64;
  let mut x175 : u64;
  let mut x164 : u64;
  let mut x176 : u64;
  let mut x161 : u64;
  let mut x177 : u64;
  let mut x179 : u64;
  let mut x180 : u64;
  let mut x162 : u64;
  let mut x167 : u64;
  let mut x142 : u64;
  let mut x183 : u64;
  let mut x147 : u64;
  let mut x184 : u64;
  let mut x169 : u64;
  let mut x185 : u64;
  let mut x187 : u64;
  let mut x188 : u64;
  let mut x152 : u64;
  let mut x189 : u64;
  let mut x173 : u64;
  let mut x190 : u64;
  let mut x192 : u64;
  let mut x193 : u64;
  let mut x157 : u64;
  let mut x194 : u64;
  let mut x178 : u64;
  let mut x195 : u64;
  let mut x197 : u64;
  let mut x198 : u64;
  let mut x160 : u64;
  let mut x199 : u64;
  let mut x181 : u64;
  let mut x200 : u64;
  let mut x202 : u64;
  let mut x204 : u64;
  let mut x209 : u64;
  let mut x212 : u64;
  let mut x214 : u64;
  let mut x210 : u64;
  let mut x215 : u64;
  let mut x207 : u64;
  let mut x216 : u64;
  let mut x218 : u64;
  let mut x219 : u64;
  let mut x208 : u64;
  let mut x220 : u64;
  let mut x205 : u64;
  let mut x221 : u64;
  let mut x223 : u64;
  let mut x224 : u64;
  let mut x206 : u64;
  let mut x211 : u64;
  let mut x226 : u64;
  let mut x182 : u64;
  let mut x227 : u64;
  let mut x186 : u64;
  let mut x228 : u64;
  let mut x213 : u64;
  let mut x229 : u64;
  let mut x231 : u64;
  let mut x232 : u64;
  let mut x191 : u64;
  let mut x233 : u64;
  let mut x217 : u64;
  let mut x234 : u64;
  let mut x236 : u64;
  let mut x237 : u64;
  let mut x196 : u64;
  let mut x238 : u64;
  let mut x222 : u64;
  let mut x239 : u64;
  let mut x241 : u64;
  let mut x242 : u64;
  let mut x201 : u64;
  let mut x243 : u64;
  let mut x225 : u64;
  let mut x244 : u64;
  let mut x246 : u64;
  let mut x247 : u64;
  let mut x203 : u64;
  let mut x3 : u64;
  let mut x2 : u64;
  let mut x1 : u64;
  let mut x6 : u64;
  let mut x0 : u64;
  let mut x253 : u64;
  let mut x256 : u64;
  let mut x258 : u64;
  let mut x254 : u64;
  let mut x259 : u64;
  let mut x251 : u64;
  let mut x260 : u64;
  let mut x262 : u64;
  let mut x263 : u64;
  let mut x252 : u64;
  let mut x264 : u64;
  let mut x249 : u64;
  let mut x265 : u64;
  let mut x267 : u64;
  let mut x268 : u64;
  let mut x250 : u64;
  let mut x255 : u64;
  let mut x230 : u64;
  let mut x271 : u64;
  let mut x235 : u64;
  let mut x272 : u64;
  let mut x257 : u64;
  let mut x273 : u64;
  let mut x275 : u64;
  let mut x276 : u64;
  let mut x240 : u64;
  let mut x277 : u64;
  let mut x261 : u64;
  let mut x278 : u64;
  let mut x280 : u64;
  let mut x281 : u64;
  let mut x245 : u64;
  let mut x282 : u64;
  let mut x266 : u64;
  let mut x283 : u64;
  let mut x285 : u64;
  let mut x286 : u64;
  let mut x248 : u64;
  let mut x287 : u64;
  let mut x269 : u64;
  let mut x288 : u64;
  let mut x290 : u64;
  let mut x292 : u64;
  let mut x297 : u64;
  let mut x300 : u64;
  let mut x302 : u64;
  let mut x298 : u64;
  let mut x303 : u64;
  let mut x295 : u64;
  let mut x304 : u64;
  let mut x306 : u64;
  let mut x307 : u64;
  let mut x296 : u64;
  let mut x308 : u64;
  let mut x293 : u64;
  let mut x309 : u64;
  let mut x311 : u64;
  let mut x312 : u64;
  let mut x294 : u64;
  let mut x299 : u64;
  let mut x314 : u64;
  let mut x270 : u64;
  let mut x315 : u64;
  let mut x274 : u64;
  let mut x316 : u64;
  let mut x301 : u64;
  let mut x317 : u64;
  let mut x319 : u64;
  let mut x320 : u64;
  let mut x279 : u64;
  let mut x321 : u64;
  let mut x305 : u64;
  let mut x322 : u64;
  let mut x324 : u64;
  let mut x325 : u64;
  let mut x284 : u64;
  let mut x326 : u64;
  let mut x310 : u64;
  let mut x327 : u64;
  let mut x329 : u64;
  let mut x330 : u64;
  let mut x289 : u64;
  let mut x331 : u64;
  let mut x313 : u64;
  let mut x332 : u64;
  let mut x334 : u64;
  let mut x335 : u64;
  let mut x291 : u64;
  let mut x338 : u64;
  let mut x339 : u64;
  let mut x340 : u64;
  let mut x342 : u64;
  let mut x343 : u64;
  let mut x344 : u64;
  let mut x345 : u64;
  let mut x347 : u64;
  let mut x348 : u64;
  let mut x349 : u64;
  let mut x350 : u64;
  let mut x352 : u64;
  let mut x353 : u64;
  let mut x336 : u64;
  let mut x354 : u64;
  let mut x318 : u64;
  let mut x356 : u64;
  let mut x337 : u64;
  let mut x357 : u64;
  let mut x323 : u64;
  let mut x359 : u64;
  let mut x341 : u64;
  let mut x360 : u64;
  let mut x328 : u64;
  let mut x362 : u64;
  let mut x346 : u64;
  let mut x363 : u64;
  let mut x355 : u64;
  let mut x333 : u64;
  let mut x365 : u64;
  let mut x351 : u64;
  let mut x366 : u64;
  let mut x358 : u64;
  let mut x361 : u64;
  let mut x364 : u64;
  let mut x367 : u64;
  let mut x368 : u64;
  let mut x369 : u64;
  let mut x370 : u64;
  let mut x371 : u64;
  x0 = _br2_load((in0 as *const u8).wrapping_add((0u64) as usize) as *const usize);
  x1 = _br2_load((in0 as *const u8).wrapping_add((8u64) as usize) as *const usize);
  x2 = _br2_load((in0 as *const u8).wrapping_add((16u64) as usize) as *const usize);
  x3 = _br2_load((in0 as *const u8).wrapping_add((24u64) as usize) as *const usize);
  /*skip*/
  /*skip*/
  x4 = x1;
  x5 = x2;
  x6 = x3;
  x7 = x0;
  x8 = (x7).wrapping_mul((x3));
  x9 = (((x7) as u128).wrapping_mul((x3) as u128) >> 64) as u64;
  x10 = (x7).wrapping_mul((x2));
  x11 = (((x7) as u128).wrapping_mul((x2) as u128) >> 64) as u64;
  x12 = (x7).wrapping_mul((x1));
  x13 = (((x7) as u128).wrapping_mul((x1) as u128) >> 64) as u64;
  x14 = (x7).wrapping_mul((x0));
  x15 = (((x7) as u128).wrapping_mul((x0) as u128) >> 64) as u64;
  x16 = (x15).wrapping_add((x12));
  x17 = if (x16) < (x15) { 1u64 } else { 0u64 };
  x18 = (x17).wrapping_add((x13));
  x19 = if (x18) < (x13) { 1u64 } else { 0u64 };
  x20 = (x18).wrapping_add((x10));
  x21 = if (x20) < (x10) { 1u64 } else { 0u64 };
  x22 = (x19).wrapping_add((x21));
  x23 = (x22).wrapping_add((x11));
  x24 = if (x23) < (x11) { 1u64 } else { 0u64 };
  x25 = (x23).wrapping_add((x8));
  x26 = if (x25) < (x8) { 1u64 } else { 0u64 };
  x27 = (x24).wrapping_add((x26));
  x28 = (x27).wrapping_add((x9));
  x29 = (x14).wrapping_mul((9786893198990664585u64));
  x30 = (x29).wrapping_mul((3486998266802970665u64));
  x31 = (((x29) as u128).wrapping_mul((3486998266802970665u64) as u128) >> 64) as u64;
  x32 = (x29).wrapping_mul((13281191951274694749u64));
  x33 = (((x29) as u128).wrapping_mul((13281191951274694749u64) as u128) >> 64) as u64;
  x34 = (x29).wrapping_mul((10917124144477883021u64));
  x35 = (((x29) as u128).wrapping_mul((10917124144477883021u64) as u128) >> 64) as u64;
  x36 = (x29).wrapping_mul((4332616871279656263u64));
  x37 = (((x29) as u128).wrapping_mul((4332616871279656263u64) as u128) >> 64) as u64;
  x38 = (x37).wrapping_add((x34));
  x39 = if (x38) < (x37) { 1u64 } else { 0u64 };
  x40 = (x39).wrapping_add((x35));
  x41 = if (x40) < (x35) { 1u64 } else { 0u64 };
  x42 = (x40).wrapping_add((x32));
  x43 = if (x42) < (x32) { 1u64 } else { 0u64 };
  x44 = (x41).wrapping_add((x43));
  x45 = (x44).wrapping_add((x33));
  x46 = if (x45) < (x33) { 1u64 } else { 0u64 };
  x47 = (x45).wrapping_add((x30));
  x48 = if (x47) < (x30) { 1u64 } else { 0u64 };
  x49 = (x46).wrapping_add((x48));
  x50 = (x49).wrapping_add((x31));
  x51 = (x14).wrapping_add((x36));
  x52 = if (x51) < (x14) { 1u64 } else { 0u64 };
  x53 = (x52).wrapping_add((x16));
  x54 = if (x53) < (x16) { 1u64 } else { 0u64 };
  x55 = (x53).wrapping_add((x38));
  x56 = if (x55) < (x38) { 1u64 } else { 0u64 };
  x57 = (x54).wrapping_add((x56));
  x58 = (x57).wrapping_add((x20));
  x59 = if (x58) < (x20) { 1u64 } else { 0u64 };
  x60 = (x58).wrapping_add((x42));
  x61 = if (x60) < (x42) { 1u64 } else { 0u64 };
  x62 = (x59).wrapping_add((x61));
  x63 = (x62).wrapping_add((x25));
  x64 = if (x63) < (x25) { 1u64 } else { 0u64 };
  x65 = (x63).wrapping_add((x47));
  x66 = if (x65) < (x47) { 1u64 } else { 0u64 };
  x67 = (x64).wrapping_add((x66));
  x68 = (x67).wrapping_add((x28));
  x69 = if (x68) < (x28) { 1u64 } else { 0u64 };
  x70 = (x68).wrapping_add((x50));
  x71 = if (x70) < (x50) { 1u64 } else { 0u64 };
  x72 = (x69).wrapping_add((x71));
  x73 = (x4).wrapping_mul((x3));
  x74 = (((x4) as u128).wrapping_mul((x3) as u128) >> 64) as u64;
  x75 = (x4).wrapping_mul((x2));
  x76 = (((x4) as u128).wrapping_mul((x2) as u128) >> 64) as u64;
  x77 = (x4).wrapping_mul((x1));
  x78 = (((x4) as u128).wrapping_mul((x1) as u128) >> 64) as u64;
  x79 = (x4).wrapping_mul((x0));
  x80 = (((x4) as u128).wrapping_mul((x0) as u128) >> 64) as u64;
  x81 = (x80).wrapping_add((x77));
  x82 = if (x81) < (x80) { 1u64 } else { 0u64 };
  x83 = (x82).wrapping_add((x78));
  x84 = if (x83) < (x78) { 1u64 } else { 0u64 };
  x85 = (x83).wrapping_add((x75));
  x86 = if (x85) < (x75) { 1u64 } else { 0u64 };
  x87 = (x84).wrapping_add((x86));
  x88 = (x87).wrapping_add((x76));
  x89 = if (x88) < (x76) { 1u64 } else { 0u64 };
  x90 = (x88).wrapping_add((x73));
  x91 = if (x90) < (x73) { 1u64 } else { 0u64 };
  x92 = (x89).wrapping_add((x91));
  x93 = (x92).wrapping_add((x74));
  x94 = (x55).wrapping_add((x79));
  x95 = if (x94) < (x55) { 1u64 } else { 0u64 };
  x96 = (x95).wrapping_add((x60));
  x97 = if (x96) < (x60) { 1u64 } else { 0u64 };
  x98 = (x96).wrapping_add((x81));
  x99 = if (x98) < (x81) { 1u64 } else { 0u64 };
  x100 = (x97).wrapping_add((x99));
  x101 = (x100).wrapping_add((x65));
  x102 = if (x101) < (x65) { 1u64 } else { 0u64 };
  x103 = (x101).wrapping_add((x85));
  x104 = if (x103) < (x85) { 1u64 } else { 0u64 };
  x105 = (x102).wrapping_add((x104));
  x106 = (x105).wrapping_add((x70));
  x107 = if (x106) < (x70) { 1u64 } else { 0u64 };
  x108 = (x106).wrapping_add((x90));
  x109 = if (x108) < (x90) { 1u64 } else { 0u64 };
  x110 = (x107).wrapping_add((x109));
  x111 = (x110).wrapping_add((x72));
  x112 = if (x111) < (x72) { 1u64 } else { 0u64 };
  x113 = (x111).wrapping_add((x93));
  x114 = if (x113) < (x93) { 1u64 } else { 0u64 };
  x115 = (x112).wrapping_add((x114));
  x116 = (x94).wrapping_mul((9786893198990664585u64));
  x117 = (x116).wrapping_mul((3486998266802970665u64));
  x118 = (((x116) as u128).wrapping_mul((3486998266802970665u64) as u128) >> 64) as u64;
  x119 = (x116).wrapping_mul((13281191951274694749u64));
  x120 = (((x116) as u128).wrapping_mul((13281191951274694749u64) as u128) >> 64) as u64;
  x121 = (x116).wrapping_mul((10917124144477883021u64));
  x122 = (((x116) as u128).wrapping_mul((10917124144477883021u64) as u128) >> 64) as u64;
  x123 = (x116).wrapping_mul((4332616871279656263u64));
  x124 = (((x116) as u128).wrapping_mul((4332616871279656263u64) as u128) >> 64) as u64;
  x125 = (x124).wrapping_add((x121));
  x126 = if (x125) < (x124) { 1u64 } else { 0u64 };
  x127 = (x126).wrapping_add((x122));
  x128 = if (x127) < (x122) { 1u64 } else { 0u64 };
  x129 = (x127).wrapping_add((x119));
  x130 = if (x129) < (x119) { 1u64 } else { 0u64 };
  x131 = (x128).wrapping_add((x130));
  x132 = (x131).wrapping_add((x120));
  x133 = if (x132) < (x120) { 1u64 } else { 0u64 };
  x134 = (x132).wrapping_add((x117));
  x135 = if (x134) < (x117) { 1u64 } else { 0u64 };
  x136 = (x133).wrapping_add((x135));
  x137 = (x136).wrapping_add((x118));
  x138 = (x94).wrapping_add((x123));
  x139 = if (x138) < (x94) { 1u64 } else { 0u64 };
  x140 = (x139).wrapping_add((x98));
  x141 = if (x140) < (x98) { 1u64 } else { 0u64 };
  x142 = (x140).wrapping_add((x125));
  x143 = if (x142) < (x125) { 1u64 } else { 0u64 };
  x144 = (x141).wrapping_add((x143));
  x145 = (x144).wrapping_add((x103));
  x146 = if (x145) < (x103) { 1u64 } else { 0u64 };
  x147 = (x145).wrapping_add((x129));
  x148 = if (x147) < (x129) { 1u64 } else { 0u64 };
  x149 = (x146).wrapping_add((x148));
  x150 = (x149).wrapping_add((x108));
  x151 = if (x150) < (x108) { 1u64 } else { 0u64 };
  x152 = (x150).wrapping_add((x134));
  x153 = if (x152) < (x134) { 1u64 } else { 0u64 };
  x154 = (x151).wrapping_add((x153));
  x155 = (x154).wrapping_add((x113));
  x156 = if (x155) < (x113) { 1u64 } else { 0u64 };
  x157 = (x155).wrapping_add((x137));
  x158 = if (x157) < (x137) { 1u64 } else { 0u64 };
  x159 = (x156).wrapping_add((x158));
  x160 = (x159).wrapping_add((x115));
  x161 = (x5).wrapping_mul((x3));
  x162 = (((x5) as u128).wrapping_mul((x3) as u128) >> 64) as u64;
  x163 = (x5).wrapping_mul((x2));
  x164 = (((x5) as u128).wrapping_mul((x2) as u128) >> 64) as u64;
  x165 = (x5).wrapping_mul((x1));
  x166 = (((x5) as u128).wrapping_mul((x1) as u128) >> 64) as u64;
  x167 = (x5).wrapping_mul((x0));
  x168 = (((x5) as u128).wrapping_mul((x0) as u128) >> 64) as u64;
  x169 = (x168).wrapping_add((x165));
  x170 = if (x169) < (x168) { 1u64 } else { 0u64 };
  x171 = (x170).wrapping_add((x166));
  x172 = if (x171) < (x166) { 1u64 } else { 0u64 };
  x173 = (x171).wrapping_add((x163));
  x174 = if (x173) < (x163) { 1u64 } else { 0u64 };
  x175 = (x172).wrapping_add((x174));
  x176 = (x175).wrapping_add((x164));
  x177 = if (x176) < (x164) { 1u64 } else { 0u64 };
  x178 = (x176).wrapping_add((x161));
  x179 = if (x178) < (x161) { 1u64 } else { 0u64 };
  x180 = (x177).wrapping_add((x179));
  x181 = (x180).wrapping_add((x162));
  x182 = (x142).wrapping_add((x167));
  x183 = if (x182) < (x142) { 1u64 } else { 0u64 };
  x184 = (x183).wrapping_add((x147));
  x185 = if (x184) < (x147) { 1u64 } else { 0u64 };
  x186 = (x184).wrapping_add((x169));
  x187 = if (x186) < (x169) { 1u64 } else { 0u64 };
  x188 = (x185).wrapping_add((x187));
  x189 = (x188).wrapping_add((x152));
  x190 = if (x189) < (x152) { 1u64 } else { 0u64 };
  x191 = (x189).wrapping_add((x173));
  x192 = if (x191) < (x173) { 1u64 } else { 0u64 };
  x193 = (x190).wrapping_add((x192));
  x194 = (x193).wrapping_add((x157));
  x195 = if (x194) < (x157) { 1u64 } else { 0u64 };
  x196 = (x194).wrapping_add((x178));
  x197 = if (x196) < (x178) { 1u64 } else { 0u64 };
  x198 = (x195).wrapping_add((x197));
  x199 = (x198).wrapping_add((x160));
  x200 = if (x199) < (x160) { 1u64 } else { 0u64 };
  x201 = (x199).wrapping_add((x181));
  x202 = if (x201) < (x181) { 1u64 } else { 0u64 };
  x203 = (x200).wrapping_add((x202));
  x204 = (x182).wrapping_mul((9786893198990664585u64));
  x205 = (x204).wrapping_mul((3486998266802970665u64));
  x206 = (((x204) as u128).wrapping_mul((3486998266802970665u64) as u128) >> 64) as u64;
  x207 = (x204).wrapping_mul((13281191951274694749u64));
  x208 = (((x204) as u128).wrapping_mul((13281191951274694749u64) as u128) >> 64) as u64;
  x209 = (x204).wrapping_mul((10917124144477883021u64));
  x210 = (((x204) as u128).wrapping_mul((10917124144477883021u64) as u128) >> 64) as u64;
  x211 = (x204).wrapping_mul((4332616871279656263u64));
  x212 = (((x204) as u128).wrapping_mul((4332616871279656263u64) as u128) >> 64) as u64;
  x213 = (x212).wrapping_add((x209));
  x214 = if (x213) < (x212) { 1u64 } else { 0u64 };
  x215 = (x214).wrapping_add((x210));
  x216 = if (x215) < (x210) { 1u64 } else { 0u64 };
  x217 = (x215).wrapping_add((x207));
  x218 = if (x217) < (x207) { 1u64 } else { 0u64 };
  x219 = (x216).wrapping_add((x218));
  x220 = (x219).wrapping_add((x208));
  x221 = if (x220) < (x208) { 1u64 } else { 0u64 };
  x222 = (x220).wrapping_add((x205));
  x223 = if (x222) < (x205) { 1u64 } else { 0u64 };
  x224 = (x221).wrapping_add((x223));
  x225 = (x224).wrapping_add((x206));
  x226 = (x182).wrapping_add((x211));
  x227 = if (x226) < (x182) { 1u64 } else { 0u64 };
  x228 = (x227).wrapping_add((x186));
  x229 = if (x228) < (x186) { 1u64 } else { 0u64 };
  x230 = (x228).wrapping_add((x213));
  x231 = if (x230) < (x213) { 1u64 } else { 0u64 };
  x232 = (x229).wrapping_add((x231));
  x233 = (x232).wrapping_add((x191));
  x234 = if (x233) < (x191) { 1u64 } else { 0u64 };
  x235 = (x233).wrapping_add((x217));
  x236 = if (x235) < (x217) { 1u64 } else { 0u64 };
  x237 = (x234).wrapping_add((x236));
  x238 = (x237).wrapping_add((x196));
  x239 = if (x238) < (x196) { 1u64 } else { 0u64 };
  x240 = (x238).wrapping_add((x222));
  x241 = if (x240) < (x222) { 1u64 } else { 0u64 };
  x242 = (x239).wrapping_add((x241));
  x243 = (x242).wrapping_add((x201));
  x244 = if (x243) < (x201) { 1u64 } else { 0u64 };
  x245 = (x243).wrapping_add((x225));
  x246 = if (x245) < (x225) { 1u64 } else { 0u64 };
  x247 = (x244).wrapping_add((x246));
  x248 = (x247).wrapping_add((x203));
  x249 = (x6).wrapping_mul((x3));
  x250 = (((x6) as u128).wrapping_mul((x3) as u128) >> 64) as u64;
  x251 = (x6).wrapping_mul((x2));
  x252 = (((x6) as u128).wrapping_mul((x2) as u128) >> 64) as u64;
  x253 = (x6).wrapping_mul((x1));
  x254 = (((x6) as u128).wrapping_mul((x1) as u128) >> 64) as u64;
  x255 = (x6).wrapping_mul((x0));
  x256 = (((x6) as u128).wrapping_mul((x0) as u128) >> 64) as u64;
  x257 = (x256).wrapping_add((x253));
  x258 = if (x257) < (x256) { 1u64 } else { 0u64 };
  x259 = (x258).wrapping_add((x254));
  x260 = if (x259) < (x254) { 1u64 } else { 0u64 };
  x261 = (x259).wrapping_add((x251));
  x262 = if (x261) < (x251) { 1u64 } else { 0u64 };
  x263 = (x260).wrapping_add((x262));
  x264 = (x263).wrapping_add((x252));
  x265 = if (x264) < (x252) { 1u64 } else { 0u64 };
  x266 = (x264).wrapping_add((x249));
  x267 = if (x266) < (x249) { 1u64 } else { 0u64 };
  x268 = (x265).wrapping_add((x267));
  x269 = (x268).wrapping_add((x250));
  x270 = (x230).wrapping_add((x255));
  x271 = if (x270) < (x230) { 1u64 } else { 0u64 };
  x272 = (x271).wrapping_add((x235));
  x273 = if (x272) < (x235) { 1u64 } else { 0u64 };
  x274 = (x272).wrapping_add((x257));
  x275 = if (x274) < (x257) { 1u64 } else { 0u64 };
  x276 = (x273).wrapping_add((x275));
  x277 = (x276).wrapping_add((x240));
  x278 = if (x277) < (x240) { 1u64 } else { 0u64 };
  x279 = (x277).wrapping_add((x261));
  x280 = if (x279) < (x261) { 1u64 } else { 0u64 };
  x281 = (x278).wrapping_add((x280));
  x282 = (x281).wrapping_add((x245));
  x283 = if (x282) < (x245) { 1u64 } else { 0u64 };
  x284 = (x282).wrapping_add((x266));
  x285 = if (x284) < (x266) { 1u64 } else { 0u64 };
  x286 = (x283).wrapping_add((x285));
  x287 = (x286).wrapping_add((x248));
  x288 = if (x287) < (x248) { 1u64 } else { 0u64 };
  x289 = (x287).wrapping_add((x269));
  x290 = if (x289) < (x269) { 1u64 } else { 0u64 };
  x291 = (x288).wrapping_add((x290));
  x292 = (x270).wrapping_mul((9786893198990664585u64));
  x293 = (x292).wrapping_mul((3486998266802970665u64));
  x294 = (((x292) as u128).wrapping_mul((3486998266802970665u64) as u128) >> 64) as u64;
  x295 = (x292).wrapping_mul((13281191951274694749u64));
  x296 = (((x292) as u128).wrapping_mul((13281191951274694749u64) as u128) >> 64) as u64;
  x297 = (x292).wrapping_mul((10917124144477883021u64));
  x298 = (((x292) as u128).wrapping_mul((10917124144477883021u64) as u128) >> 64) as u64;
  x299 = (x292).wrapping_mul((4332616871279656263u64));
  x300 = (((x292) as u128).wrapping_mul((4332616871279656263u64) as u128) >> 64) as u64;
  x301 = (x300).wrapping_add((x297));
  x302 = if (x301) < (x300) { 1u64 } else { 0u64 };
  x303 = (x302).wrapping_add((x298));
  x304 = if (x303) < (x298) { 1u64 } else { 0u64 };
  x305 = (x303).wrapping_add((x295));
  x306 = if (x305) < (x295) { 1u64 } else { 0u64 };
  x307 = (x304).wrapping_add((x306));
  x308 = (x307).wrapping_add((x296));
  x309 = if (x308) < (x296) { 1u64 } else { 0u64 };
  x310 = (x308).wrapping_add((x293));
  x311 = if (x310) < (x293) { 1u64 } else { 0u64 };
  x312 = (x309).wrapping_add((x311));
  x313 = (x312).wrapping_add((x294));
  x314 = (x270).wrapping_add((x299));
  x315 = if (x314) < (x270) { 1u64 } else { 0u64 };
  x316 = (x315).wrapping_add((x274));
  x317 = if (x316) < (x274) { 1u64 } else { 0u64 };
  x318 = (x316).wrapping_add((x301));
  x319 = if (x318) < (x301) { 1u64 } else { 0u64 };
  x320 = (x317).wrapping_add((x319));
  x321 = (x320).wrapping_add((x279));
  x322 = if (x321) < (x279) { 1u64 } else { 0u64 };
  x323 = (x321).wrapping_add((x305));
  x324 = if (x323) < (x305) { 1u64 } else { 0u64 };
  x325 = (x322).wrapping_add((x324));
  x326 = (x325).wrapping_add((x284));
  x327 = if (x326) < (x284) { 1u64 } else { 0u64 };
  x328 = (x326).wrapping_add((x310));
  x329 = if (x328) < (x310) { 1u64 } else { 0u64 };
  x330 = (x327).wrapping_add((x329));
  x331 = (x330).wrapping_add((x289));
  x332 = if (x331) < (x289) { 1u64 } else { 0u64 };
  x333 = (x331).wrapping_add((x313));
  x334 = if (x333) < (x313) { 1u64 } else { 0u64 };
  x335 = (x332).wrapping_add((x334));
  x336 = (x335).wrapping_add((x291));
  x337 = (x318).wrapping_sub((4332616871279656263u64));
  x338 = if (x318) < (x337) { 1u64 } else { 0u64 };
  x339 = (x323).wrapping_sub((10917124144477883021u64));
  x340 = if (x323) < (x339) { 1u64 } else { 0u64 };
  x341 = (x339).wrapping_sub((x338));
  x342 = if (x339) < (x341) { 1u64 } else { 0u64 };
  x343 = (x340).wrapping_add((x342));
  x344 = (x328).wrapping_sub((13281191951274694749u64));
  x345 = if (x328) < (x344) { 1u64 } else { 0u64 };
  x346 = (x344).wrapping_sub((x343));
  x347 = if (x344) < (x346) { 1u64 } else { 0u64 };
  x348 = (x345).wrapping_add((x347));
  x349 = (x333).wrapping_sub((3486998266802970665u64));
  x350 = if (x333) < (x349) { 1u64 } else { 0u64 };
  x351 = (x349).wrapping_sub((x348));
  x352 = if (x349) < (x351) { 1u64 } else { 0u64 };
  x353 = (x350).wrapping_add((x352));
  x354 = (x336).wrapping_sub((x353));
  x355 = if (x336) < (x354) { 1u64 } else { 0u64 };
  x356 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x355) == (0u64) { 1u64 } else { 0u64 }));
  x357 = (x356) ^ (18446744073709551615u64);
  x358 = ((x318) & (x356)) | ((x337) & (x357));
  x359 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x355) == (0u64) { 1u64 } else { 0u64 }));
  x360 = (x359) ^ (18446744073709551615u64);
  x361 = ((x323) & (x359)) | ((x341) & (x360));
  x362 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x355) == (0u64) { 1u64 } else { 0u64 }));
  x363 = (x362) ^ (18446744073709551615u64);
  x364 = ((x328) & (x362)) | ((x346) & (x363));
  x365 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (x355) == (0u64) { 1u64 } else { 0u64 }));
  x366 = (x365) ^ (18446744073709551615u64);
  x367 = ((x333) & (x365)) | ((x351) & (x366));
  x368 = x358;
  x369 = x361;
  x370 = x364;
  x371 = x367;
  /*skip*/
  _br2_store((out0 as *const u8).wrapping_add((0u64) as usize) as *mut usize, x368);
  _br2_store((out0 as *const u8).wrapping_add((8u64) as usize) as *mut usize, x369);
  _br2_store((out0 as *const u8).wrapping_add((16u64) as usize) as *mut usize, x370);
  _br2_store((out0 as *const u8).wrapping_add((24u64) as usize) as *mut usize, x371);
  /*skip*/
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_select_znz(out0 : u64, in0 : u64, in1 : u64, in2 : u64) {
  let mut x4 : u64;
  let mut x8 : u64;
  let mut x0 : u64;
  let mut x9 : u64;
  let mut x5 : u64;
  let mut x11 : u64;
  let mut x1 : u64;
  let mut x12 : u64;
  let mut x6 : u64;
  let mut x14 : u64;
  let mut x2 : u64;
  let mut x15 : u64;
  let mut x7 : u64;
  let mut x17 : u64;
  let mut x3 : u64;
  let mut x18 : u64;
  let mut x10 : u64;
  let mut x13 : u64;
  let mut x16 : u64;
  let mut x19 : u64;
  let mut x20 : u64;
  let mut x21 : u64;
  let mut x22 : u64;
  let mut x23 : u64;
  /*skip*/
  x0 = _br2_load((in1 as *const u8).wrapping_add((0u64) as usize) as *const usize);
  x1 = _br2_load((in1 as *const u8).wrapping_add((8u64) as usize) as *const usize);
  x2 = _br2_load((in1 as *const u8).wrapping_add((16u64) as usize) as *const usize);
  x3 = _br2_load((in1 as *const u8).wrapping_add((24u64) as usize) as *const usize);
  /*skip*/
  x4 = _br2_load((in2 as *const u8).wrapping_add((0u64) as usize) as *const usize);
  x5 = _br2_load((in2 as *const u8).wrapping_add((8u64) as usize) as *const usize);
  x6 = _br2_load((in2 as *const u8).wrapping_add((16u64) as usize) as *const usize);
  x7 = _br2_load((in2 as *const u8).wrapping_add((24u64) as usize) as *const usize);
  /*skip*/
  /*skip*/
  x8 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (in0) == (0u64) { 1u64 } else { 0u64 }));
  x9 = (x8) ^ (18446744073709551615u64);
  x10 = ((x4) & (x8)) | ((x0) & (x9));
  x11 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (in0) == (0u64) { 1u64 } else { 0u64 }));
  x12 = (x11) ^ (18446744073709551615u64);
  x13 = ((x5) & (x11)) | ((x1) & (x12));
  x14 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (in0) == (0u64) { 1u64 } else { 0u64 }));
  x15 = (x14) ^ (18446744073709551615u64);
  x16 = ((x6) & (x14)) | ((x2) & (x15));
  x17 = ((0u64.wrapping_sub(1u64))).wrapping_add((if (in0) == (0u64) { 1u64 } else { 0u64 }));
  x18 = (x17) ^ (18446744073709551615u64);
  x19 = ((x7) & (x17)) | ((x3) & (x18));
  x20 = x10;
  x21 = x13;
  x22 = x16;
  x23 = x19;
  /*skip*/
  _br2_store((out0 as *const u8).wrapping_add((0u64) as usize) as *mut usize, x20);
  _br2_store((out0 as *const u8).wrapping_add((8u64) as usize) as *mut usize, x21);
  _br2_store((out0 as *const u8).wrapping_add((16u64) as usize) as *mut usize, x22);
  _br2_store((out0 as *const u8).wrapping_add((24u64) as usize) as *mut usize, x23);
  /*skip*/
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_felem_copy(out : u64, in_ : u64) {
  _br2_store(out as *mut usize, _br2_load(in_ as *const usize));
  _br2_store((out as *const u8).wrapping_add((8u64) as usize) as *mut usize, _br2_load((in_ as *const u8).wrapping_add((8u64) as usize) as *const usize));
  _br2_store((out as *const u8).wrapping_add((16u64) as usize) as *mut usize, _br2_load((in_ as *const u8).wrapping_add((16u64) as usize) as *const usize));
  _br2_store((out as *const u8).wrapping_add((24u64) as usize) as *mut usize, _br2_load((in_ as *const u8).wrapping_add((24u64) as usize) as *const usize));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_felem_copy(out : u64, x : u64) {
  bn254_felem_copy(out, x);
  bn254_felem_copy((out).wrapping_add((32u64)), (x).wrapping_add((32u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_add(out : u64, inx : u64, iny : u64) {
  bn254_add(out, inx, iny);
  bn254_add((out).wrapping_add((32u64)), (inx).wrapping_add((32u64)), (iny).wrapping_add((32u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_sub(out : u64, inx : u64, iny : u64) {
  bn254_sub(out, inx, iny);
  bn254_sub((out).wrapping_add((32u64)), (inx).wrapping_add((32u64)), (iny).wrapping_add((32u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_mul(out : u64, inx : u64, iny : u64) {
  let mut v2 : u64;
  let mut v0 : u64;
  let mut v1 : u64;
  let mut v0_arr = [0u64; 4];
  let v0 = v0_arr.as_mut_ptr() as u64;
  let mut v1_arr = [0u64; 4];
  let v1 = v1_arr.as_mut_ptr() as u64;
  let mut v2_arr = [0u64; 4];
  let v2 = v2_arr.as_mut_ptr() as u64;
  bn254_mul(v0, inx, iny);
  bn254_mul(v1, (inx).wrapping_add((32u64)), (iny).wrapping_add((32u64)));
  bn254_add(v2, inx, (inx).wrapping_add((32u64)));
  bn254_add((out).wrapping_add((32u64)), iny, (iny).wrapping_add((32u64)));
  bn254_mul((out).wrapping_add((32u64)), (out).wrapping_add((32u64)), v2);
  bn254_sub((out).wrapping_add((32u64)), (out).wrapping_add((32u64)), v0);
  bn254_sub((out).wrapping_add((32u64)), (out).wrapping_add((32u64)), v1);
  bn254_sub(out, v0, v1);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_square(out : u64, inx : u64) {
  let mut v0 : u64;
  let mut v1 : u64;
  let mut v0_arr = [0u64; 4];
  let v0 = v0_arr.as_mut_ptr() as u64;
  let mut v1_arr = [0u64; 4];
  let v1 = v1_arr.as_mut_ptr() as u64;
  bn254_square(v0, inx);
  bn254_square(v1, (inx).wrapping_add((32u64)));
  bn254_mul((out).wrapping_add((32u64)), inx, (inx).wrapping_add((32u64)));
  bn254_add((out).wrapping_add((32u64)), (out).wrapping_add((32u64)), (out).wrapping_add((32u64)));
  bn254_sub(out, v0, v1);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_mul_xi(out : u64, x : u64) {
  let mut tmp_a9 : u64;
  let mut tmp_b9 : u64;
  let mut tmp_a9_arr = [0u64; 4];
  let tmp_a9 = tmp_a9_arr.as_mut_ptr() as u64;
  let mut tmp_b9_arr = [0u64; 4];
  let tmp_b9 = tmp_b9_arr.as_mut_ptr() as u64;
  bn254_add(tmp_a9, x, x);
  bn254_add(tmp_a9, tmp_a9, tmp_a9);
  bn254_add(tmp_a9, tmp_a9, tmp_a9);
  bn254_add(tmp_a9, tmp_a9, x);
  bn254_add(tmp_b9, (x).wrapping_add((32u64)), (x).wrapping_add((32u64)));
  bn254_add(tmp_b9, tmp_b9, tmp_b9);
  bn254_add(tmp_b9, tmp_b9, tmp_b9);
  bn254_add(tmp_b9, tmp_b9, (x).wrapping_add((32u64)));
  bn254_sub(out, tmp_a9, (x).wrapping_add((32u64)));
  bn254_add((out).wrapping_add((32u64)), x, tmp_b9);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_felem_copy(out : u64, x : u64) {
  bn254_Fp2_felem_copy(out, x);
  bn254_Fp2_felem_copy((out).wrapping_add((64u64)), (x).wrapping_add((64u64)));
  bn254_Fp2_felem_copy((out).wrapping_add((128u64)), (x).wrapping_add((128u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_add(out : u64, inx : u64, iny : u64) {
  let mut allocx : u64;
  let mut allocy : u64;
  let mut allocx_arr = [0u64; 24];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  let mut allocy_arr = [0u64; 24];
  let allocy = allocy_arr.as_mut_ptr() as u64;
  bn254_Fp6_felem_copy(allocx, inx);
  bn254_Fp6_felem_copy(allocy, iny);
  bn254_Fp2_add(out, allocx, allocy);
  bn254_Fp2_add((out).wrapping_add((64u64)), (allocx).wrapping_add((64u64)), (allocy).wrapping_add((64u64)));
  bn254_Fp2_add((out).wrapping_add((128u64)), (allocx).wrapping_add((128u64)), (allocy).wrapping_add((128u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_sub(out : u64, inx : u64, iny : u64) {
  let mut allocx : u64;
  let mut allocy : u64;
  let mut allocx_arr = [0u64; 24];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  let mut allocy_arr = [0u64; 24];
  let allocy = allocy_arr.as_mut_ptr() as u64;
  bn254_Fp6_felem_copy(allocx, inx);
  bn254_Fp6_felem_copy(allocy, iny);
  bn254_Fp2_sub(out, allocx, allocy);
  bn254_Fp2_sub((out).wrapping_add((64u64)), (allocx).wrapping_add((64u64)), (allocy).wrapping_add((64u64)));
  bn254_Fp2_sub((out).wrapping_add((128u64)), (allocx).wrapping_add((128u64)), (allocy).wrapping_add((128u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_opp(out : u64, x : u64) {
  let mut allocx : u64;
  let mut allocx_arr = [0u64; 24];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  bn254_Fp6_felem_copy(allocx, x);
  bn254_Fp2_opp(out, allocx);
  bn254_Fp2_opp((out).wrapping_add((64u64)), (allocx).wrapping_add((64u64)));
  bn254_Fp2_opp((out).wrapping_add((128u64)), (allocx).wrapping_add((128u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_mul(out : u64, inx : u64, iny : u64) {
  let mut allocx : u64;
  let mut allocy : u64;
  let mut u : u64;
  let mut a0b0 : u64;
  let mut a2b2 : u64;
  let mut t : u64;
  let mut a1b1 : u64;
  let mut allocx_arr = [0u64; 24];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  let mut allocy_arr = [0u64; 24];
  let allocy = allocy_arr.as_mut_ptr() as u64;
  let mut a0b0_arr = [0u64; 8];
  let a0b0 = a0b0_arr.as_mut_ptr() as u64;
  let mut a1b1_arr = [0u64; 8];
  let a1b1 = a1b1_arr.as_mut_ptr() as u64;
  let mut a2b2_arr = [0u64; 8];
  let a2b2 = a2b2_arr.as_mut_ptr() as u64;
  let mut t_arr = [0u64; 8];
  let t = t_arr.as_mut_ptr() as u64;
  let mut u_arr = [0u64; 8];
  let u = u_arr.as_mut_ptr() as u64;
  bn254_Fp6_felem_copy(allocx, inx);
  bn254_Fp6_felem_copy(allocy, iny);
  bn254_Fp2_mul(a0b0, allocx, allocy);
  bn254_Fp2_mul(a1b1, (allocx).wrapping_add((64u64)), (allocy).wrapping_add((64u64)));
  bn254_Fp2_mul(a2b2, (allocx).wrapping_add((128u64)), (allocy).wrapping_add((128u64)));
  bn254_Fp2_add(t, (allocx).wrapping_add((64u64)), (allocx).wrapping_add((128u64)));
  bn254_Fp2_add(u, (allocy).wrapping_add((64u64)), (allocy).wrapping_add((128u64)));
  bn254_Fp2_mul(t, t, u);
  bn254_Fp2_sub(t, t, a1b1);
  bn254_Fp2_sub(t, t, a2b2);
  bn254_Fp2_mul_xi(t, t);
  bn254_Fp2_add(out, a0b0, t);
  bn254_Fp2_add(t, allocx, (allocx).wrapping_add((64u64)));
  bn254_Fp2_add(u, allocy, (allocy).wrapping_add((64u64)));
  bn254_Fp2_mul(t, t, u);
  bn254_Fp2_sub(t, t, a0b0);
  bn254_Fp2_sub(t, t, a1b1);
  bn254_Fp2_mul_xi(u, a2b2);
  bn254_Fp2_add((out).wrapping_add((64u64)), t, u);
  bn254_Fp2_add(t, allocx, (allocx).wrapping_add((128u64)));
  bn254_Fp2_add(u, allocy, (allocy).wrapping_add((128u64)));
  bn254_Fp2_mul(t, t, u);
  bn254_Fp2_sub(t, t, a0b0);
  bn254_Fp2_sub(t, t, a2b2);
  bn254_Fp2_add((out).wrapping_add((128u64)), t, a1b1);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_square(out : u64, x : u64) {
  let mut allocx : u64;
  let mut s1 : u64;
  let mut s2 : u64;
  let mut s3 : u64;
  let mut s0 : u64;
  let mut t : u64;
  let mut s4 : u64;
  let mut allocx_arr = [0u64; 24];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  let mut s0_arr = [0u64; 8];
  let s0 = s0_arr.as_mut_ptr() as u64;
  let mut s1_arr = [0u64; 8];
  let s1 = s1_arr.as_mut_ptr() as u64;
  let mut s2_arr = [0u64; 8];
  let s2 = s2_arr.as_mut_ptr() as u64;
  let mut s3_arr = [0u64; 8];
  let s3 = s3_arr.as_mut_ptr() as u64;
  let mut s4_arr = [0u64; 8];
  let s4 = s4_arr.as_mut_ptr() as u64;
  let mut t_arr = [0u64; 8];
  let t = t_arr.as_mut_ptr() as u64;
  bn254_Fp6_felem_copy(allocx, x);
  bn254_Fp2_square(s0, allocx);
  bn254_Fp2_mul(t, allocx, (allocx).wrapping_add((64u64)));
  bn254_Fp2_add(s1, t, t);
  bn254_Fp2_sub(t, allocx, (allocx).wrapping_add((64u64)));
  bn254_Fp2_add(t, t, (allocx).wrapping_add((128u64)));
  bn254_Fp2_square(s2, t);
  bn254_Fp2_mul(t, (allocx).wrapping_add((64u64)), (allocx).wrapping_add((128u64)));
  bn254_Fp2_add(s3, t, t);
  bn254_Fp2_square(s4, (allocx).wrapping_add((128u64)));
  bn254_Fp2_mul_xi(t, s3);
  bn254_Fp2_add(out, s0, t);
  bn254_Fp2_mul_xi(t, s4);
  bn254_Fp2_add((out).wrapping_add((64u64)), s1, t);
  bn254_Fp2_add(t, s1, s2);
  bn254_Fp2_add(t, t, s3);
  bn254_Fp2_sub(t, t, s0);
  bn254_Fp2_sub((out).wrapping_add((128u64)), t, s4);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_inv(out : u64, x : u64) {
  let mut allocx : u64;
  let mut t3 : u64;
  let mut t2 : u64;
  let mut vA : u64;
  let mut vB : u64;
  let mut vC : u64;
  let mut t1 : u64;
  let mut allocx_arr = [0u64; 24];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  let mut vA_arr = [0u64; 8];
  let vA = vA_arr.as_mut_ptr() as u64;
  let mut vB_arr = [0u64; 8];
  let vB = vB_arr.as_mut_ptr() as u64;
  let mut vC_arr = [0u64; 8];
  let vC = vC_arr.as_mut_ptr() as u64;
  let mut t1_arr = [0u64; 8];
  let t1 = t1_arr.as_mut_ptr() as u64;
  let mut t2_arr = [0u64; 8];
  let t2 = t2_arr.as_mut_ptr() as u64;
  let mut t3_arr = [0u64; 8];
  let t3 = t3_arr.as_mut_ptr() as u64;
  bn254_Fp6_felem_copy(allocx, x);
  bn254_Fp2_square(t1, allocx);
  bn254_Fp2_mul(t2, (allocx).wrapping_add((64u64)), (allocx).wrapping_add((128u64)));
  bn254_Fp2_mul_xi(t3, t2);
  bn254_Fp2_sub(vA, t1, t3);
  bn254_Fp2_square(t1, (allocx).wrapping_add((128u64)));
  bn254_Fp2_mul_xi(t3, t1);
  bn254_Fp2_mul(t2, allocx, (allocx).wrapping_add((64u64)));
  bn254_Fp2_sub(vB, t3, t2);
  bn254_Fp2_square(t1, (allocx).wrapping_add((64u64)));
  bn254_Fp2_mul(t2, allocx, (allocx).wrapping_add((128u64)));
  bn254_Fp2_sub(vC, t1, t2);
  bn254_Fp2_mul(t1, allocx, vA);
  bn254_Fp2_mul(t2, (allocx).wrapping_add((128u64)), vB);
  bn254_Fp2_mul(t3, (allocx).wrapping_add((64u64)), vC);
  bn254_Fp2_add(t2, t2, t3);
  bn254_Fp2_mul_xi(t2, t2);
  bn254_Fp2_add(t1, t1, t2);
  bn254_Fp2_inv(t1, t1);
  bn254_Fp2_mul(out, vA, t1);
  bn254_Fp2_mul((out).wrapping_add((64u64)), vB, t1);
  bn254_Fp2_mul((out).wrapping_add((128u64)), vC, t1);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_add_nocopy(out : u64, inx : u64, iny : u64) {
  bn254_Fp2_add(out, inx, iny);
  bn254_Fp2_add((out).wrapping_add((64u64)), (inx).wrapping_add((64u64)), (iny).wrapping_add((64u64)));
  bn254_Fp2_add((out).wrapping_add((128u64)), (inx).wrapping_add((128u64)), (iny).wrapping_add((128u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_sub_nocopy(out : u64, inx : u64, iny : u64) {
  bn254_Fp2_sub(out, inx, iny);
  bn254_Fp2_sub((out).wrapping_add((64u64)), (inx).wrapping_add((64u64)), (iny).wrapping_add((64u64)));
  bn254_Fp2_sub((out).wrapping_add((128u64)), (inx).wrapping_add((128u64)), (iny).wrapping_add((128u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_mul_by_v(out : u64, x : u64) {
  let mut tmp : u64;
  let mut tmp_arr = [0u64; 24];
  let tmp = tmp_arr.as_mut_ptr() as u64;
  bn254_Fp6_felem_copy(tmp, x);
  bn254_Fp2_mul_xi(out, (tmp).wrapping_add((128u64)));
  bn254_Fp2_felem_copy((out).wrapping_add((64u64)), tmp);
  bn254_Fp2_felem_copy((out).wrapping_add((128u64)), (tmp).wrapping_add((64u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_felem_copy(out : u64, x : u64) {
  bn254_Fp6_felem_copy(out, x);
  bn254_Fp6_felem_copy((out).wrapping_add((192u64)), (x).wrapping_add((192u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_add(out : u64, inx : u64, iny : u64) {
  let mut ax : u64;
  let mut ay : u64;
  let mut ax_arr = [0u64; 48];
  let ax = ax_arr.as_mut_ptr() as u64;
  let mut ay_arr = [0u64; 48];
  let ay = ay_arr.as_mut_ptr() as u64;
  bn254_Fp12_felem_copy(ax, inx);
  bn254_Fp12_felem_copy(ay, iny);
  bn254_Fp6_add(out, ax, ay);
  bn254_Fp6_add((out).wrapping_add((192u64)), (ax).wrapping_add((192u64)), (ay).wrapping_add((192u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_sub(out : u64, inx : u64, iny : u64) {
  let mut ax : u64;
  let mut ay : u64;
  let mut ax_arr = [0u64; 48];
  let ax = ax_arr.as_mut_ptr() as u64;
  let mut ay_arr = [0u64; 48];
  let ay = ay_arr.as_mut_ptr() as u64;
  bn254_Fp12_felem_copy(ax, inx);
  bn254_Fp12_felem_copy(ay, iny);
  bn254_Fp6_sub(out, ax, ay);
  bn254_Fp6_sub((out).wrapping_add((192u64)), (ax).wrapping_add((192u64)), (ay).wrapping_add((192u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_opp(out : u64, x : u64) {
  let mut allocx : u64;
  let mut allocx_arr = [0u64; 48];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  bn254_Fp12_felem_copy(allocx, x);
  bn254_Fp6_opp(out, allocx);
  bn254_Fp6_opp((out).wrapping_add((192u64)), (allocx).wrapping_add((192u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_conjugate(out : u64, x : u64) {
  let mut allocx : u64;
  let mut allocx_arr = [0u64; 48];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  bn254_Fp12_felem_copy(allocx, x);
  bn254_Fp6_felem_copy(out, allocx);
  bn254_Fp6_opp((out).wrapping_add((192u64)), (allocx).wrapping_add((192u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_mul(out : u64, inx : u64, iny : u64) {
  let mut ax : u64;
  let mut ay : u64;
  let mut u : u64;
  let mut v0 : u64;
  let mut t : u64;
  let mut v1 : u64;
  let mut ax_arr = [0u64; 48];
  let ax = ax_arr.as_mut_ptr() as u64;
  let mut ay_arr = [0u64; 48];
  let ay = ay_arr.as_mut_ptr() as u64;
  bn254_Fp12_felem_copy(ax, inx);
  bn254_Fp12_felem_copy(ay, iny);
  let mut v0_arr = [0u64; 24];
  let v0 = v0_arr.as_mut_ptr() as u64;
  let mut v1_arr = [0u64; 24];
  let v1 = v1_arr.as_mut_ptr() as u64;
  let mut t_arr = [0u64; 24];
  let t = t_arr.as_mut_ptr() as u64;
  let mut u_arr = [0u64; 24];
  let u = u_arr.as_mut_ptr() as u64;
  bn254_Fp6_mul(v0, ax, ay);
  bn254_Fp6_mul(v1, (ax).wrapping_add((192u64)), (ay).wrapping_add((192u64)));
  bn254_Fp6_add(t, ax, (ax).wrapping_add((192u64)));
  bn254_Fp6_add(u, ay, (ay).wrapping_add((192u64)));
  bn254_Fp6_mul(t, t, u);
  bn254_Fp6_mul_by_v(u, v1);
  bn254_Fp6_add(out, v0, u);
  bn254_Fp6_sub(t, t, v0);
  bn254_Fp6_sub((out).wrapping_add((192u64)), t, v1);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_square(out : u64, x : u64) {
  let mut allocx : u64;
  let mut t0 : u64;
  let mut t1 : u64;
  let mut t2 : u64;
  let mut allocx_arr = [0u64; 48];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  bn254_Fp12_felem_copy(allocx, x);
  let mut t0_arr = [0u64; 24];
  let t0 = t0_arr.as_mut_ptr() as u64;
  let mut t1_arr = [0u64; 24];
  let t1 = t1_arr.as_mut_ptr() as u64;
  let mut t2_arr = [0u64; 24];
  let t2 = t2_arr.as_mut_ptr() as u64;
  bn254_Fp6_square(t0, allocx);
  bn254_Fp6_square(t1, (allocx).wrapping_add((192u64)));
  bn254_Fp6_mul(t2, allocx, (allocx).wrapping_add((192u64)));
  bn254_Fp6_mul_by_v(t1, t1);
  bn254_Fp6_add(out, t0, t1);
  bn254_Fp6_add((out).wrapping_add((192u64)), t2, t2);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_inv(out : u64, x : u64) {
  let mut t1 : u64;
  let mut allocx : u64;
  let mut t0 : u64;
  let mut allocx_arr = [0u64; 48];
  let allocx = allocx_arr.as_mut_ptr() as u64;
  bn254_Fp12_felem_copy(allocx, x);
  let mut t0_arr = [0u64; 24];
  let t0 = t0_arr.as_mut_ptr() as u64;
  let mut t1_arr = [0u64; 24];
  let t1 = t1_arr.as_mut_ptr() as u64;
  bn254_Fp6_square(t0, allocx);
  bn254_Fp6_square(t1, (allocx).wrapping_add((192u64)));
  bn254_Fp6_mul_by_v(t1, t1);
  bn254_Fp6_sub(t0, t0, t1);
  bn254_Fp6_inv(t0, t0);
  bn254_Fp6_mul(out, allocx, t0);
  bn254_Fp6_mul((out).wrapping_add((192u64)), (allocx).wrapping_add((192u64)), t0);
  bn254_Fp6_opp((out).wrapping_add((192u64)), (out).wrapping_add((192u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_add_nocopy(out : u64, inx : u64, iny : u64) {
  bn254_Fp6_add(out, inx, iny);
  bn254_Fp6_add((out).wrapping_add((192u64)), (inx).wrapping_add((192u64)), (iny).wrapping_add((192u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_sub_nocopy(out : u64, inx : u64, iny : u64) {
  bn254_Fp6_sub(out, inx, iny);
  bn254_Fp6_sub((out).wrapping_add((192u64)), (inx).wrapping_add((192u64)), (iny).wrapping_add((192u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_mul_nocopy(out : u64, inx : u64, iny : u64) {
  let mut u : u64;
  let mut v0 : u64;
  let mut t : u64;
  let mut v1 : u64;
  let mut v0_arr = [0u64; 24];
  let v0 = v0_arr.as_mut_ptr() as u64;
  let mut v1_arr = [0u64; 24];
  let v1 = v1_arr.as_mut_ptr() as u64;
  let mut t_arr = [0u64; 24];
  let t = t_arr.as_mut_ptr() as u64;
  let mut u_arr = [0u64; 24];
  let u = u_arr.as_mut_ptr() as u64;
  bn254_Fp6_mul(v0, inx, iny);
  bn254_Fp6_mul(v1, (inx).wrapping_add((192u64)), (iny).wrapping_add((192u64)));
  bn254_Fp6_add(t, inx, (inx).wrapping_add((192u64)));
  bn254_Fp6_add(u, iny, (iny).wrapping_add((192u64)));
  bn254_Fp6_mul(t, t, u);
  bn254_Fp6_mul_by_v(u, v1);
  bn254_Fp6_add(out, v0, u);
  bn254_Fp6_sub(t, t, v0);
  bn254_Fp6_sub((out).wrapping_add((192u64)), t, v1);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_conjugate(out : u64, x : u64) {
  bn254_felem_copy(out, x);
  bn254_opp((out).wrapping_add((32u64)), (x).wrapping_add((32u64)));
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_mul_fp2(out : u64, x : u64, s : u64) {
  let mut s_copy : u64;
  let mut s_copy_arr = [0u64; 8];
  let s_copy = s_copy_arr.as_mut_ptr() as u64;
  bn254_Fp2_felem_copy(s_copy, s);
  bn254_Fp2_mul(out, x, s_copy);
  bn254_Fp2_mul((out).wrapping_add((64u64)), (x).wrapping_add((64u64)), s_copy);
  bn254_Fp2_mul((out).wrapping_add((128u64)), (x).wrapping_add((128u64)), s_copy);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_frobenius(out : u64, x : u64, gamma1 : u64, gamma2 : u64) {
  let mut tmp : u64;
  let mut tmp_arr = [0u64; 24];
  let tmp = tmp_arr.as_mut_ptr() as u64;
  bn254_Fp2_conjugate(tmp, x);
  bn254_Fp2_conjugate((tmp).wrapping_add((64u64)), (x).wrapping_add((64u64)));
  bn254_Fp2_conjugate((tmp).wrapping_add((128u64)), (x).wrapping_add((128u64)));
  bn254_Fp2_felem_copy(out, tmp);
  bn254_Fp2_mul((out).wrapping_add((64u64)), (tmp).wrapping_add((64u64)), gamma1);
  bn254_Fp2_mul((out).wrapping_add((128u64)), (tmp).wrapping_add((128u64)), gamma2);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp6_frobenius_p2(out : u64, x : u64, gamma1_p2 : u64, gamma2_p2 : u64) {
  bn254_Fp2_felem_copy(out, x);
  bn254_Fp2_mul((out).wrapping_add((64u64)), (x).wrapping_add((64u64)), gamma1_p2);
  bn254_Fp2_mul((out).wrapping_add((128u64)), (x).wrapping_add((128u64)), gamma2_p2);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_frobenius(out : u64, x : u64, gamma1 : u64, gamma2 : u64, w_frob_c1 : u64) {
  bn254_Fp6_frobenius(out, x, gamma1, gamma2);
  bn254_Fp6_frobenius((out).wrapping_add((192u64)), (x).wrapping_add((192u64)), gamma1, gamma2);
  bn254_Fp6_mul_fp2((out).wrapping_add((192u64)), (out).wrapping_add((192u64)), w_frob_c1);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_frobenius_p2(out : u64, x : u64, gamma1_p2 : u64, gamma2_p2 : u64, w_frob_p2_c1 : u64) {
  bn254_Fp6_frobenius_p2(out, x, gamma1_p2, gamma2_p2);
  bn254_Fp6_frobenius_p2((out).wrapping_add((192u64)), (x).wrapping_add((192u64)), gamma1_p2, gamma2_p2);
  bn254_Fp6_mul_fp2((out).wrapping_add((192u64)), (out).wrapping_add((192u64)), w_frob_p2_c1);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_frobenius_p3(out : u64, x : u64, gamma1 : u64, gamma2 : u64, gamma1_p2 : u64, gamma2_p2 : u64, w_frob_c1 : u64, w_frob_p2_c1 : u64) {
  let mut tmp : u64;
  let mut tmp_arr = [0u64; 48];
  let tmp = tmp_arr.as_mut_ptr() as u64;
  bn254_Fp6_frobenius_p2(tmp, x, gamma1_p2, gamma2_p2);
  bn254_Fp6_frobenius_p2((tmp).wrapping_add((192u64)), (x).wrapping_add((192u64)), gamma1_p2, gamma2_p2);
  bn254_Fp6_mul_fp2((tmp).wrapping_add((192u64)), (tmp).wrapping_add((192u64)), w_frob_p2_c1);
  bn254_Fp6_frobenius(out, tmp, gamma1, gamma2);
  bn254_Fp6_frobenius((out).wrapping_add((192u64)), (tmp).wrapping_add((192u64)), gamma1, gamma2);
  bn254_Fp6_mul_fp2((out).wrapping_add((192u64)), (out).wrapping_add((192u64)), w_frob_c1);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp2_mul_fp(out : u64, x : u64, s : u64) {
  bn254_mul(out, x, s);
  bn254_mul((out).wrapping_add((32u64)), (x).wrapping_add((32u64)), s);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_make_line(out : u64, lam : u64, x_t : u64, y_t : u64, x_p : u64, y_p : u64) {
  let mut tmp : u64;
  let mut tmp_arr = [0u64; 8];
  let tmp = tmp_arr.as_mut_ptr() as u64;
  bn254_Fp2_mul(out, lam, x_t);
  bn254_Fp2_sub(out, out, y_t);
  bn254_Fp2_mul_fp(tmp, lam, x_p);
  bn254_Fp2_opp((out).wrapping_add((64u64)), tmp);
  bn254_from_word((out).wrapping_add((128u64)), 0u64);
  bn254_from_word(((out).wrapping_add((128u64))).wrapping_add((32u64)), 0u64);
  bn254_from_word((out).wrapping_add((192u64)), 0u64);
  bn254_from_word(((out).wrapping_add((192u64))).wrapping_add((32u64)), 0u64);
  bn254_felem_copy(((out).wrapping_add((192u64))).wrapping_add((64u64)), y_p);
  bn254_from_word((((out).wrapping_add((192u64))).wrapping_add((64u64))).wrapping_add((32u64)), 0u64);
  bn254_from_word(((out).wrapping_add((192u64))).wrapping_add((128u64)), 0u64);
  bn254_from_word((((out).wrapping_add((192u64))).wrapping_add((128u64))).wrapping_add((32u64)), 0u64);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_load_gamma1_p2(out : u64) {
  _br2_store(out as *mut usize, 3697675806616062876u64);
  _br2_store((out as *const u8).wrapping_add((8u64) as usize) as *mut usize, 9065277094688085689u64);
  _br2_store((out as *const u8).wrapping_add((16u64) as usize) as *mut usize, 6918009208039626314u64);
  _br2_store((out as *const u8).wrapping_add((24u64) as usize) as *mut usize, 2775033306905974752u64);
  _br2_store((out as *const u8).wrapping_add((32u64) as usize) as *mut usize, 0u64);
  _br2_store((out as *const u8).wrapping_add((40u64) as usize) as *mut usize, 0u64);
  _br2_store((out as *const u8).wrapping_add((48u64) as usize) as *mut usize, 0u64);
  _br2_store((out as *const u8).wrapping_add((56u64) as usize) as *mut usize, 0u64);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_load_gamma2_p2(out : u64) {
  _br2_store(out as *mut usize, 8183898218631979349u64);
  _br2_store((out as *const u8).wrapping_add((8u64) as usize) as *mut usize, 12014359695528440611u64);
  _br2_store((out as *const u8).wrapping_add((16u64) as usize) as *mut usize, 12263358156045030468u64);
  _br2_store((out as *const u8).wrapping_add((24u64) as usize) as *mut usize, 3187210487005268291u64);
  _br2_store((out as *const u8).wrapping_add((32u64) as usize) as *mut usize, 0u64);
  _br2_store((out as *const u8).wrapping_add((40u64) as usize) as *mut usize, 0u64);
  _br2_store((out as *const u8).wrapping_add((48u64) as usize) as *mut usize, 0u64);
  _br2_store((out as *const u8).wrapping_add((56u64) as usize) as *mut usize, 0u64);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_load_w_frob_p2_c1(out : u64) {
  _br2_store(out as *mut usize, 14595462726357228530u64);
  _br2_store((out as *const u8).wrapping_add((8u64) as usize) as *mut usize, 17349508522658994025u64);
  _br2_store((out as *const u8).wrapping_add((16u64) as usize) as *mut usize, 1017833795229664280u64);
  _br2_store((out as *const u8).wrapping_add((24u64) as usize) as *mut usize, 299787779797702374u64);
  _br2_store((out as *const u8).wrapping_add((32u64) as usize) as *mut usize, 0u64);
  _br2_store((out as *const u8).wrapping_add((40u64) as usize) as *mut usize, 0u64);
  _br2_store((out as *const u8).wrapping_add((48u64) as usize) as *mut usize, 0u64);
  _br2_store((out as *const u8).wrapping_add((56u64) as usize) as *mut usize, 0u64);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_load_gamma1(out : u64) {
  _br2_store(out as *mut usize, 13075984984163199792u64);
  _br2_store((out as *const u8).wrapping_add((8u64) as usize) as *mut usize, 3782902503040509012u64);
  _br2_store((out as *const u8).wrapping_add((16u64) as usize) as *mut usize, 8791150885551868305u64);
  _br2_store((out as *const u8).wrapping_add((24u64) as usize) as *mut usize, 1825854335138010348u64);
  _br2_store((out as *const u8).wrapping_add((32u64) as usize) as *mut usize, 7963664994991228759u64);
  _br2_store((out as *const u8).wrapping_add((40u64) as usize) as *mut usize, 12257807996192067905u64);
  _br2_store((out as *const u8).wrapping_add((48u64) as usize) as *mut usize, 13179524609921305146u64);
  _br2_store((out as *const u8).wrapping_add((56u64) as usize) as *mut usize, 2767831111890561987u64);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_load_gamma2(out : u64) {
  _br2_store(out as *mut usize, 8314163329781907090u64);
  _br2_store((out as *const u8).wrapping_add((8u64) as usize) as *mut usize, 11942187022798819835u64);
  _br2_store((out as *const u8).wrapping_add((16u64) as usize) as *mut usize, 11282677263046157209u64);
  _br2_store((out as *const u8).wrapping_add((24u64) as usize) as *mut usize, 1576150870752482284u64);
  _br2_store((out as *const u8).wrapping_add((32u64) as usize) as *mut usize, 6763840483288992073u64);
  _br2_store((out as *const u8).wrapping_add((40u64) as usize) as *mut usize, 7118829427391486816u64);
  _br2_store((out as *const u8).wrapping_add((48u64) as usize) as *mut usize, 4016233444936635065u64);
  _br2_store((out as *const u8).wrapping_add((56u64) as usize) as *mut usize, 2630958277570195709u64);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_load_w_frob_c1(out : u64) {
  _br2_store(out as *mut usize, 12653890742059813127u64);
  _br2_store((out as *const u8).wrapping_add((8u64) as usize) as *mut usize, 14585784200204367754u64);
  _br2_store((out as *const u8).wrapping_add((16u64) as usize) as *mut usize, 1278438861261381767u64);
  _br2_store((out as *const u8).wrapping_add((24u64) as usize) as *mut usize, 212598772761311868u64);
  _br2_store((out as *const u8).wrapping_add((32u64) as usize) as *mut usize, 11683091849979440498u64);
  _br2_store((out as *const u8).wrapping_add((40u64) as usize) as *mut usize, 14992204589386555739u64);
  _br2_store((out as *const u8).wrapping_add((48u64) as usize) as *mut usize, 15866167890766973222u64);
  _br2_store((out as *const u8).wrapping_add((56u64) as usize) as *mut usize, 1200023580730561873u64);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_Fp12_pow_u(out : u64, base : u64) {
  let mut i : u64;
  let mut bit : u64;
  let mut result : u64;
  let mut result_arr = [0u64; 48];
  let result = result_arr.as_mut_ptr() as u64;
  bn254_Fp12_felem_copy(result, base);
  i = 62u64;
  while (i) != 0 {
    i = (i).wrapping_sub((1u64));
    bn254_Fp12_square(result, result);
    bit = ((4965661367192848881u64) >> (i)) & (1u64);
    if (bit) != 0 {
      bn254_Fp12_mul(result, result, base);
    } else {
      /*skip*/
    }
  }
  bn254_Fp12_felem_copy(out, result);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_final_exp_hard_dsd(out : u64, f : u64) {
  let mut gamma1 : u64;
  let mut gamma2 : u64;
  let mut w_frob_c1 : u64;
  let mut t3 : u64;
  let mut t1 : u64;
  let mut t0 : u64;
  let mut t2 : u64;
  let mut t0_arr = [0u64; 48];
  let t0 = t0_arr.as_mut_ptr() as u64;
  let mut t1_arr = [0u64; 48];
  let t1 = t1_arr.as_mut_ptr() as u64;
  let mut t2_arr = [0u64; 48];
  let t2 = t2_arr.as_mut_ptr() as u64;
  let mut t3_arr = [0u64; 48];
  let t3 = t3_arr.as_mut_ptr() as u64;
  let mut gamma1_arr = [0u64; 8];
  let gamma1 = gamma1_arr.as_mut_ptr() as u64;
  let mut gamma2_arr = [0u64; 8];
  let gamma2 = gamma2_arr.as_mut_ptr() as u64;
  let mut w_frob_c1_arr = [0u64; 8];
  let w_frob_c1 = w_frob_c1_arr.as_mut_ptr() as u64;
  bn254_load_gamma1(gamma1);
  bn254_load_gamma2(gamma2);
  bn254_load_w_frob_c1(w_frob_c1);
  bn254_Fp12_pow_u(t0, f);
  bn254_Fp12_pow_u(t1, t0);
  bn254_Fp12_pow_u(t2, t1);
  bn254_Fp12_frobenius(t3, t2, gamma1, gamma2, w_frob_c1);
  bn254_Fp12_mul(t2, t2, t3);
  bn254_Fp12_conjugate(t2, t2);
  bn254_Fp12_square(out, t2);
  bn254_Fp12_frobenius(t3, t1, gamma1, gamma2, w_frob_c1);
  bn254_Fp12_mul(t2, t0, t3);
  bn254_Fp12_conjugate(t2, t2);
  bn254_Fp12_mul(out, out, t2);
  bn254_Fp12_conjugate(t1, t1);
  bn254_Fp12_mul(out, out, t1);
  bn254_Fp12_frobenius(t2, t0, gamma1, gamma2, w_frob_c1);
  bn254_Fp12_conjugate(t2, t2);
  bn254_Fp12_mul(t0, out, t2);
  bn254_Fp12_mul(t0, t0, t1);
  bn254_Fp12_frobenius(t1, t3, gamma1, gamma2, w_frob_c1);
  bn254_Fp12_mul(out, out, t1);
  bn254_Fp12_square(t1, t0);
  bn254_Fp12_mul(t1, t1, out);
  bn254_Fp12_square(t1, t1);
  bn254_Fp12_frobenius(t0, f, gamma1, gamma2, w_frob_c1);
  bn254_Fp12_frobenius(t2, t0, gamma1, gamma2, w_frob_c1);
  bn254_Fp12_frobenius(t3, t2, gamma1, gamma2, w_frob_c1);
  bn254_Fp12_mul(t0, t0, t2);
  bn254_Fp12_mul(t0, t0, t3);
  bn254_Fp12_mul(t2, t1, t0);
  bn254_Fp12_conjugate(t0, f);
  bn254_Fp12_mul(t0, t1, t0);
  bn254_Fp12_square(t0, t0);
  bn254_Fp12_mul(out, t0, t2);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_final_exp_dsd(out : u64, f : u64, gamma1_p2 : u64, gamma2_p2 : u64, w_frob_p2_c1 : u64) {
  let mut tmp : u64;
  let mut result : u64;
  let mut result_arr = [0u64; 48];
  let result = result_arr.as_mut_ptr() as u64;
  let mut tmp_arr = [0u64; 48];
  let tmp = tmp_arr.as_mut_ptr() as u64;
  bn254_Fp12_conjugate(result, f);
  bn254_Fp12_inv(tmp, f);
  bn254_Fp12_mul(result, result, tmp);
  bn254_Fp12_frobenius_p2(tmp, result, gamma1_p2, gamma2_p2, w_frob_p2_c1);
  bn254_Fp12_mul(result, tmp, result);
  bn254_final_exp_hard_dsd(out, result);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_miller_loop(out : u64, p_x : u64, p_y : u64, q_x : u64, q_y : u64) {
  let mut u6p2 : u64;
  let mut word : u64;
  let mut i : u64;
  let mut bit : u64;
  let mut line : u64;
  let mut lambda : u64;
  let mut tmp1 : u64;
  let mut t_y : u64;
  let mut t_x : u64;
  let mut tmp2 : u64;
  let mut f : u64;
  let mut f_arr = [0u64; 48];
  let f = f_arr.as_mut_ptr() as u64;
  let mut t_x_arr = [0u64; 8];
  let t_x = t_x_arr.as_mut_ptr() as u64;
  let mut t_y_arr = [0u64; 8];
  let t_y = t_y_arr.as_mut_ptr() as u64;
  let mut lambda_arr = [0u64; 8];
  let lambda = lambda_arr.as_mut_ptr() as u64;
  let mut tmp1_arr = [0u64; 8];
  let tmp1 = tmp1_arr.as_mut_ptr() as u64;
  let mut tmp2_arr = [0u64; 8];
  let tmp2 = tmp2_arr.as_mut_ptr() as u64;
  let mut line_arr = [0u64; 48];
  let line = line_arr.as_mut_ptr() as u64;
  let mut u6p2_arr = [0u64; 1];
  let u6p2 = u6p2_arr.as_mut_ptr() as u64;
  bn254_from_word(f, 1u64);
  bn254_from_word((f).wrapping_add((32u64)), 0u64);
  bn254_from_word((f).wrapping_add((64u64)), 0u64);
  bn254_from_word(((f).wrapping_add((64u64))).wrapping_add((32u64)), 0u64);
  bn254_from_word((f).wrapping_add((128u64)), 0u64);
  bn254_from_word(((f).wrapping_add((128u64))).wrapping_add((32u64)), 0u64);
  bn254_from_word((f).wrapping_add((192u64)), 0u64);
  bn254_from_word(((f).wrapping_add((192u64))).wrapping_add((32u64)), 0u64);
  bn254_from_word(((f).wrapping_add((192u64))).wrapping_add((64u64)), 0u64);
  bn254_from_word((((f).wrapping_add((192u64))).wrapping_add((64u64))).wrapping_add((32u64)), 0u64);
  bn254_from_word(((f).wrapping_add((192u64))).wrapping_add((128u64)), 0u64);
  bn254_from_word((((f).wrapping_add((192u64))).wrapping_add((128u64))).wrapping_add((32u64)), 0u64);
  bn254_Fp2_felem_copy(t_x, q_x);
  bn254_Fp2_felem_copy(t_y, q_y);
  _br2_store(u6p2 as *mut usize, 11347224129447541672u64);
  i = 64u64;
  while (i) != 0 {
    i = (i).wrapping_sub((1u64));
    word = _br2_load(u6p2 as *const usize);
    bit = ((word) >> (i)) & (1u64);
    bn254_Fp2_square(tmp1, t_x);
    bn254_Fp2_add(lambda, tmp1, tmp1);
    bn254_Fp2_add(lambda, lambda, tmp1);
    bn254_Fp2_add(tmp1, t_y, t_y);
    bn254_Fp2_inv(tmp1, tmp1);
    bn254_Fp2_mul(lambda, lambda, tmp1);
    bn254_make_line(line, lambda, t_x, t_y, p_x, p_y);
    bn254_Fp12_square(f, f);
    bn254_Fp12_mul(f, f, line);
    bn254_Fp2_square(tmp1, lambda);
    bn254_Fp2_sub(tmp1, tmp1, t_x);
    bn254_Fp2_sub(tmp2, tmp1, t_x);
    bn254_Fp2_sub(tmp1, t_x, tmp2);
    bn254_Fp2_mul(tmp1, lambda, tmp1);
    bn254_Fp2_sub(t_y, tmp1, t_y);
    bn254_Fp2_felem_copy(t_x, tmp2);
    if (bit) != 0 {
      bn254_Fp2_sub(tmp1, q_y, t_y);
      bn254_Fp2_sub(tmp2, q_x, t_x);
      bn254_Fp2_inv(tmp2, tmp2);
      bn254_Fp2_mul(lambda, tmp1, tmp2);
      bn254_make_line(line, lambda, t_x, t_y, p_x, p_y);
      bn254_Fp12_mul(f, f, line);
      bn254_Fp2_square(tmp1, lambda);
      bn254_Fp2_sub(tmp1, tmp1, t_x);
      bn254_Fp2_sub(tmp2, tmp1, q_x);
      bn254_Fp2_sub(tmp1, t_x, tmp2);
      bn254_Fp2_mul(tmp1, lambda, tmp1);
      bn254_Fp2_sub(t_y, tmp1, t_y);
      bn254_Fp2_felem_copy(t_x, tmp2);
    } else {
      /*skip*/
    }
  }
  bn254_Fp12_felem_copy(out, f);
  return;
}

#[no_mangle]
pub unsafe extern "C" fn bn254_pairing_dsd(out : u64, p_x : u64, p_y : u64, q_x : u64, q_y : u64) {
  let mut tmp : u64;
  let mut gamma1_p2 : u64;
  let mut gamma2_p2 : u64;
  let mut w_frob_p2_c1 : u64;
  let mut tmp_arr = [0u64; 48];
  let tmp = tmp_arr.as_mut_ptr() as u64;
  let mut gamma1_p2_arr = [0u64; 8];
  let gamma1_p2 = gamma1_p2_arr.as_mut_ptr() as u64;
  let mut gamma2_p2_arr = [0u64; 8];
  let gamma2_p2 = gamma2_p2_arr.as_mut_ptr() as u64;
  let mut w_frob_p2_c1_arr = [0u64; 8];
  let w_frob_p2_c1 = w_frob_p2_c1_arr.as_mut_ptr() as u64;
  bn254_load_gamma1_p2(gamma1_p2);
  bn254_load_gamma2_p2(gamma2_p2);
  bn254_load_w_frob_p2_c1(w_frob_p2_c1);
  bn254_miller_loop(tmp, p_x, p_y, q_x, q_y);
  bn254_final_exp_dsd(out, tmp, gamma1_p2, gamma2_p2, w_frob_p2_c1);
  return;
}

