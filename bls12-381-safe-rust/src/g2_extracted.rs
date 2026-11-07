//! Rocq-EMITTED safe Rust: BLS12-381 G2 scalar multiplication and complete
//! projective group law over Fp2 (bedrock2), printed by src/Bedrock/ToSafeRustArena.v from the
//! function list [bls12_g2_funcs] of src/Bedrock/BLS12_G2ArenaRust.v.
//!
//! DO NOT EDIT.  Regenerate with scripts/emit_bls12_g2_rust.sh;
//! scripts/check_bls12_g2_extraction.sh checks it byte for byte.
//! Only the Rocq string quoting has been stripped.
//!
//! See src/Bedrock/BLS12_G2ArenaRust.v for the theorem behind each
//! function and for what is not proved.

#![allow(unused_mut, unused_variables, unused_assignments, unused_braces, non_snake_case)]

use crate::bedrock_rt::*;

pub fn g2_scalar_mul(m: &mut Mem, mut v_outx: u64, mut v_outy: u64, mut v_outz: u64, mut v_scalar: u64, mut v_px: u64, mut v_py: u64, mut v_pz: u64) {
    let mut v_i: u64 = 0;
    let mut v_a: u64 = 0;
    let mut v_bit: u64 = 0;
    {
        let a0: u64 = v_outx;
        let a1: u64 = v_px;
        let a2: u64 = v_px;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_outz;
        let a1: u64 = v_px;
        let a2: u64 = v_px;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_outy;
        bls12_Fp2_three_b(m, a0);
    }
    v_i = 256u64;
    while v_i != 0 {
        v_i = (v_i).wrapping_sub(1u64);
        {
            let a0: u64 = v_outx;
            let a1: u64 = v_outy;
            let a2: u64 = v_outz;
            g2_curve_double_ip(m, a0, a1, a2);
        }
        v_a = (v_scalar).wrapping_add(rt_slu(rt_sru(v_i, 6u64), 3u64));
        v_bit = (rt_sru(m.load64(v_a), (v_i & 63u64)) & 1u64);
        if v_bit != 0 {
            {
                let a0: u64 = v_outx;
                let a1: u64 = v_px;
                let a2: u64 = v_outy;
                let a3: u64 = v_py;
                let a4: u64 = v_outz;
                let a5: u64 = v_pz;
                g2_curve_add_ip(m, a0, a1, a2, a3, a4, a5);
            }
        } else {
        }
    }
}

pub fn g2_curve_add_ip(m: &mut Mem, mut v_X1: u64, mut v_X2: u64, mut v_Y1: u64, mut v_Y2: u64, mut v_Z1: u64, mut v_Z2: u64) {
    let mut v_three_b: u64 = 0;
    let mut v_t0: u64 = 0;
    let mut v_t1: u64 = 0;
    let mut v_t2: u64 = 0;
    let mut v_t3: u64 = 0;
    let mut v_t4: u64 = 0;
    let mut v_t5: u64 = 0;
    v_three_b = m.alloc(96);
    {
        let a0: u64 = v_three_b;
        bls12_Fp2_three_b(m, a0);
    }
    v_t0 = m.alloc(96);
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_X1;
        let a2: u64 = v_X2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t1 = m.alloc(96);
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_Y1;
        let a2: u64 = v_Y2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t2 = m.alloc(96);
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_Z1;
        let a2: u64 = v_Z2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t3 = m.alloc(96);
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_X1;
        let a2: u64 = v_Y1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    v_t4 = m.alloc(96);
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_X2;
        let a2: u64 = v_Y2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_t3;
        let a2: u64 = v_t4;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_t0;
        let a2: u64 = v_t1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_t3;
        let a2: u64 = v_t4;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_X1;
        let a2: u64 = v_Z1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    v_t5 = m.alloc(96);
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_X2;
        let a2: u64 = v_Z2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_t4;
        let a2: u64 = v_t5;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_t0;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_t4;
        let a2: u64 = v_t5;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_Y1;
        let a2: u64 = v_Z1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_X1;
        let a1: u64 = v_Y2;
        let a2: u64 = v_Z2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_t5;
        let a2: u64 = v_X1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_X1;
        let a1: u64 = v_t1;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_t5;
        let a2: u64 = v_X1;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Z1;
        let a1: u64 = v_three_b;
        let a2: u64 = v_t2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_X1;
        let a1: u64 = v_t1;
        let a2: u64 = v_Z1;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Z1;
        let a1: u64 = v_Z1;
        let a2: u64 = v_t1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Y1;
        let a1: u64 = v_X1;
        let a2: u64 = v_Z1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_t0;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_t1;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_three_b;
        let a2: u64 = v_t4;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t1;
        let a2: u64 = v_t4;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Y1;
        let a1: u64 = v_Y1;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t5;
        let a2: u64 = v_t4;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_X1;
        let a1: u64 = v_t3;
        let a2: u64 = v_X1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_X1;
        let a1: u64 = v_X1;
        let a2: u64 = v_t0;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t3;
        let a2: u64 = v_t1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Z1;
        let a1: u64 = v_t5;
        let a2: u64 = v_Z1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Z1;
        let a1: u64 = v_Z1;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
}

pub fn g2_curve_double_ip(m: &mut Mem, mut v_X1: u64, mut v_Y1: u64, mut v_Z1: u64) {
    let mut v_three_b: u64 = 0;
    let mut v_t0: u64 = 0;
    let mut v_t1: u64 = 0;
    let mut v_t2: u64 = 0;
    let mut v_t3: u64 = 0;
    v_three_b = m.alloc(96);
    {
        let a0: u64 = v_three_b;
        bls12_Fp2_three_b(m, a0);
    }
    v_t0 = m.alloc(96);
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_Y1;
        let a2: u64 = v_Y1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t1 = m.alloc(96);
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_Y1;
        let a2: u64 = v_Z1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t2 = m.alloc(96);
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_Z1;
        let a2: u64 = v_Z1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t3 = m.alloc(96);
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_X1;
        let a2: u64 = v_Y1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Z1;
        let a1: u64 = v_t0;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Z1;
        let a1: u64 = v_Z1;
        let a2: u64 = v_Z1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Z1;
        let a1: u64 = v_Z1;
        let a2: u64 = v_Z1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_three_b;
        let a2: u64 = v_t2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_X1;
        let a1: u64 = v_t2;
        let a2: u64 = v_Z1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Y1;
        let a1: u64 = v_t0;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Z1;
        let a1: u64 = v_t1;
        let a2: u64 = v_Z1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_t2;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_t1;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t0;
        let a2: u64 = v_t2;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Y1;
        let a1: u64 = v_t0;
        let a2: u64 = v_Y1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Y1;
        let a1: u64 = v_X1;
        let a2: u64 = v_Y1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_X1;
        let a1: u64 = v_t0;
        let a2: u64 = v_t3;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_X1;
        let a1: u64 = v_X1;
        let a2: u64 = v_X1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
}

pub fn g2_curve_add(m: &mut Mem, mut v_X1: u64, mut v_X2: u64, mut v_Y1: u64, mut v_Y2: u64, mut v_Z1: u64, mut v_Z2: u64, mut v_Xout: u64, mut v_Yout: u64, mut v_Zout: u64) {
    let mut v_three_b: u64 = 0;
    let mut v_t0: u64 = 0;
    let mut v_t1: u64 = 0;
    let mut v_t2: u64 = 0;
    let mut v_t3: u64 = 0;
    let mut v_t4: u64 = 0;
    let mut v_t5: u64 = 0;
    v_three_b = m.alloc(96);
    {
        let a0: u64 = v_three_b;
        bls12_Fp2_three_b(m, a0);
    }
    v_t0 = m.alloc(96);
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_X1;
        let a2: u64 = v_X2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t1 = m.alloc(96);
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_Y1;
        let a2: u64 = v_Y2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t2 = m.alloc(96);
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_Z1;
        let a2: u64 = v_Z2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t3 = m.alloc(96);
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_X1;
        let a2: u64 = v_Y1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    v_t4 = m.alloc(96);
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_X2;
        let a2: u64 = v_Y2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_t3;
        let a2: u64 = v_t4;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_t0;
        let a2: u64 = v_t1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_t3;
        let a2: u64 = v_t4;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_X1;
        let a2: u64 = v_Z1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    v_t5 = m.alloc(96);
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_X2;
        let a2: u64 = v_Z2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_t4;
        let a2: u64 = v_t5;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_t0;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_t4;
        let a2: u64 = v_t5;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_Y1;
        let a2: u64 = v_Z1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_Y2;
        let a2: u64 = v_Z2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_t5;
        let a2: u64 = v_Xout;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t1;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_t5;
        let a2: u64 = v_Xout;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_three_b;
        let a2: u64 = v_t2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t1;
        let a2: u64 = v_Zout;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_Zout;
        let a2: u64 = v_t1;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_Xout;
        let a2: u64 = v_Zout;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_t0;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_t1;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_three_b;
        let a2: u64 = v_t4;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t1;
        let a2: u64 = v_t4;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_Yout;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t5;
        let a2: u64 = v_t4;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t3;
        let a2: u64 = v_Xout;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_Xout;
        let a2: u64 = v_t0;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t3;
        let a2: u64 = v_t1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_t5;
        let a2: u64 = v_Zout;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_Zout;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
}

pub fn g2_curve_double(m: &mut Mem, mut v_Xin: u64, mut v_Yin: u64, mut v_Zin: u64, mut v_Xout: u64, mut v_Yout: u64, mut v_Zout: u64) {
    let mut v_three_b: u64 = 0;
    let mut v_t0: u64 = 0;
    let mut v_t1: u64 = 0;
    let mut v_t2: u64 = 0;
    v_three_b = m.alloc(96);
    {
        let a0: u64 = v_three_b;
        bls12_Fp2_three_b(m, a0);
    }
    v_t0 = m.alloc(96);
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_Yin;
        let a2: u64 = v_Yin;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_t0;
        let a2: u64 = v_t0;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_Zout;
        let a2: u64 = v_Zout;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_Zout;
        let a2: u64 = v_Zout;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    v_t1 = m.alloc(96);
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_Yin;
        let a2: u64 = v_Zin;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    v_t2 = m.alloc(96);
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_Zin;
        let a2: u64 = v_Zin;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_three_b;
        let a2: u64 = v_t2;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t2;
        let a2: u64 = v_Zout;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_t0;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_t1;
        let a2: u64 = v_Zout;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_t2;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_t1;
        let a2: u64 = v_t2;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t0;
        let a2: u64 = v_t2;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_t0;
        let a2: u64 = v_Yout;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_Xout;
        let a2: u64 = v_Yout;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_Xin;
        let a2: u64 = v_Yin;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t0;
        let a2: u64 = v_t1;
        bls12_Fp2_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_Xout;
        let a2: u64 = v_Xout;
        bls12_Fp2_add(m, a0, a1, a2);
    }
    m.free(96);
    m.free(96);
    m.free(96);
    m.free(96);
}

pub fn bls12_Fp2_three_b(m: &mut Mem, mut v_out: u64) {
    { let a: u64 = v_out; let v: u64 = 4933130441833534766u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(8u64); let v: u64 = 15904462746612662304u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(16u64); let v: u64 = 8034115857496836953u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(24u64); let v: u64 = 12755092135412849606u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(32u64); let v: u64 = 7007796720291435703u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(40u64); let v: u64 = 252692002104915169u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(48u64); let v: u64 = 4933130441833534766u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(56u64); let v: u64 = 15904462746612662304u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(64u64); let v: u64 = 8034115857496836953u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(72u64); let v: u64 = 12755092135412849606u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(80u64); let v: u64 = 7007796720291435703u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(88u64); let v: u64 = 252692002104915169u64; m.store64(a, v); }
}

pub fn g2_scalar_mul_ct(m: &mut Mem, mut v_outx: u64, mut v_outy: u64, mut v_outz: u64, mut v_tx: u64, mut v_ty: u64, mut v_tz: u64, mut v_scalar: u64, mut v_px: u64, mut v_py: u64, mut v_pz: u64) {
    let mut v_i: u64 = 0;
    let mut v_a: u64 = 0;
    let mut v_bit: u64 = 0;
    {
        let a0: u64 = v_outx;
        let a1: u64 = v_px;
        let a2: u64 = v_px;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_outz;
        let a1: u64 = v_px;
        let a2: u64 = v_px;
        bls12_Fp2_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_outy;
        bls12_Fp2_three_b(m, a0);
    }
    v_i = 256u64;
    while v_i != 0 {
        v_i = (v_i).wrapping_sub(1u64);
        {
            let a0: u64 = v_outx;
            let a1: u64 = v_outy;
            let a2: u64 = v_outz;
            g2_curve_double_ip(m, a0, a1, a2);
        }
        v_a = (v_scalar).wrapping_add(rt_slu(rt_sru(v_i, 6u64), 3u64));
        v_bit = (rt_sru(m.load64(v_a), (v_i & 63u64)) & 1u64);
        {
            let a0: u64 = v_outx;
            let a1: u64 = v_px;
            let a2: u64 = v_outy;
            let a3: u64 = v_py;
            let a4: u64 = v_outz;
            let a5: u64 = v_pz;
            let a6: u64 = v_tx;
            let a7: u64 = v_ty;
            let a8: u64 = v_tz;
            g2_curve_add(m, a0, a1, a2, a3, a4, a5, a6, a7, a8);
        }
        {
            let a0: u64 = v_bit;
            let a1: u64 = v_outx;
            let a2: u64 = v_tx;
            ct_cswap(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_bit;
            let a1: u64 = v_outy;
            let a2: u64 = v_ty;
            ct_cswap(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_bit;
            let a1: u64 = v_outz;
            let a2: u64 = v_tz;
            ct_cswap(m, a0, a1, a2);
        }
    }
}

pub fn ct_cswap(m: &mut Mem, mut v_mask: u64, mut v_a1: u64, mut v_a2: u64) {
    let mut v_nmask: u64 = 0;
    let mut v__gs_from0: u64 = 0;
    let mut v__gs_to0: u64 = 0;
    let mut v_v1: u64 = 0;
    let mut v_v2: u64 = 0;
    let mut v_r1: u64 = 0;
    let mut v_r2: u64 = 0;
    v_nmask = (0u64).wrapping_sub(v_mask);
    v_mask = (v_nmask ^ 18446744073709551615u64);
    v__gs_from0 = 0u64;
    v__gs_to0 = 12u64;
    while ((v__gs_from0 < v__gs_to0) as u64) != 0 {
        v_v1 = m.load64((v_a1).wrapping_add((8u64).wrapping_mul(v__gs_from0)));
        v_v2 = m.load64((v_a2).wrapping_add((8u64).wrapping_mul(v__gs_from0)));
        v_r1 = ((v_mask & v_v1) | (v_nmask & v_v2));
        v_r2 = ((v_mask & v_v2) | (v_nmask & v_v1));
        { let a: u64 = (v_a1).wrapping_add((8u64).wrapping_mul(v__gs_from0)); let v: u64 = v_r1; m.store64(a, v); }
        { let a: u64 = (v_a2).wrapping_add((8u64).wrapping_mul(v__gs_from0)); let v: u64 = v_r2; m.store64(a, v); }
        v__gs_from0 = (v__gs_from0).wrapping_add(1u64);
    }
}
