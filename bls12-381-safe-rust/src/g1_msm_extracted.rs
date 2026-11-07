//! Rocq-EMITTED safe Rust: BLS12-381 G1 Pippenger MSM, scalar
//! multiplication and complete projective group law (bedrock2), printed by
//! src/Bedrock/ToSafeRustArena.v from the function list
//! [bls12_g1_funcs] of src/Bedrock/BLS12_G1ArenaRust.v.
//!
//! DO NOT EDIT.  Regenerate with scripts/emit_bls12_g1_rust.sh;
//! scripts/check_bls12_g1_extraction.sh checks it byte for byte.
//! Only the Rocq string quoting has been stripped.
//!
//! See src/Bedrock/BLS12_G1ArenaRust.v for the theorem behind each
//! function and for what is not proved.

#![allow(unused_mut, unused_variables, unused_assignments, unused_braces, non_snake_case)]

use crate::bedrock_rt::*;

pub fn msm_bls12(m: &mut Mem, mut v_outx: u64, mut v_outy: u64, mut v_outz: u64, mut v_scalars: u64, mut v_pointsx: u64, mut v_pointsy: u64, mut v_pointsz: u64, mut v_n: u64) {
    let mut v_buckets_x: u64 = 0;
    let mut v_buckets_y: u64 = 0;
    let mut v_buckets_z: u64 = 0;
    let mut v_runx: u64 = 0;
    let mut v_runy: u64 = 0;
    let mut v_runz: u64 = 0;
    let mut v_wsx: u64 = 0;
    let mut v_wsy: u64 = 0;
    let mut v_wsz: u64 = 0;
    let mut v_w: u64 = 0;
    let mut v_i: u64 = 0;
    let mut v_bpx: u64 = 0;
    let mut v_bpy: u64 = 0;
    let mut v_bpz: u64 = 0;
    let mut v_bit_offset: u64 = 0;
    let mut v_limb: u64 = 0;
    let mut v_shift: u64 = 0;
    let mut v_mask: u64 = 0;
    let mut v_scalar_ptr: u64 = 0;
    let mut v_load_off1: u64 = 0;
    let mut v_load_addr1: u64 = 0;
    let mut v_val: u64 = 0;
    let mut v_load_off2: u64 = 0;
    let mut v_load_addr2: u64 = 0;
    let mut v_idx: u64 = 0;
    let mut v_bucket_index: u64 = 0;
    let mut v_ppx: u64 = 0;
    let mut v_ppy: u64 = 0;
    let mut v_ppz: u64 = 0;
    v_buckets_x = m.alloc(24528);
    v_buckets_y = m.alloc(24528);
    v_buckets_z = m.alloc(24528);
    v_runx = m.alloc(48);
    v_runy = m.alloc(48);
    v_runz = m.alloc(48);
    v_wsx = m.alloc(48);
    v_wsy = m.alloc(48);
    v_wsz = m.alloc(48);
    {
        let a0: u64 = v_outx;
        let a1: u64 = v_outy;
        let a2: u64 = v_outz;
        store_zero(m, a0, a1, a2);
    }
    v_w = 29u64;
    while v_w != 0 {
        v_w = (v_w).wrapping_sub(1u64);
        v_i = 9u64;
        while v_i != 0 {
            v_i = (v_i).wrapping_sub(1u64);
            {
                let a0: u64 = v_outx;
                let a1: u64 = v_outy;
                let a2: u64 = v_outz;
                let a3: u64 = v_outx;
                let a4: u64 = v_outy;
                let a5: u64 = v_outz;
                msm_curve_double(m, a0, a1, a2, a3, a4, a5);
            }
        }
        v_i = 511u64;
        while v_i != 0 {
            v_i = (v_i).wrapping_sub(1u64);
            v_bpx = (v_buckets_x).wrapping_add((v_i).wrapping_mul(48u64));
            v_bpy = (v_buckets_y).wrapping_add((v_i).wrapping_mul(48u64));
            v_bpz = (v_buckets_z).wrapping_add((v_i).wrapping_mul(48u64));
            {
                let a0: u64 = v_bpx;
                let a1: u64 = v_bpy;
                let a2: u64 = v_bpz;
                store_zero(m, a0, a1, a2);
            }
        }
        v_i = v_n;
        while v_i != 0 {
            v_i = (v_i).wrapping_sub(1u64);
            v_bit_offset = (v_w).wrapping_mul(9u64);
            v_limb = rt_sru(v_bit_offset, 6u64);
            v_shift = (v_bit_offset & 63u64);
            v_mask = (rt_slu(1u64, 9u64)).wrapping_sub(1u64);
            v_scalar_ptr = (v_scalars).wrapping_add((v_i).wrapping_mul(32u64));
            v_load_off1 = (v_limb).wrapping_mul(8u64);
            v_load_addr1 = (v_scalar_ptr).wrapping_add(v_load_off1);
            v_val = rt_sru(m.load64(v_load_addr1), v_shift);
            if ((64u64 < (v_shift).wrapping_add(9u64)) as u64) != 0 {
                if ((v_limb < 3u64) as u64) != 0 {
                    v_load_off2 = ((v_limb).wrapping_add(1u64)).wrapping_mul(8u64);
                    v_load_addr2 = (v_scalar_ptr).wrapping_add(v_load_off2);
                    v_val = (v_val | rt_slu(m.load64(v_load_addr2), (64u64).wrapping_sub(v_shift)));
                } else {
                }
            } else {
            }
            v_idx = (v_val & v_mask);
            if v_idx != 0 {
                v_bucket_index = (v_idx).wrapping_sub(1u64);
                v_bpx = (v_buckets_x).wrapping_add((v_bucket_index).wrapping_mul(48u64));
                v_bpy = (v_buckets_y).wrapping_add((v_bucket_index).wrapping_mul(48u64));
                v_bpz = (v_buckets_z).wrapping_add((v_bucket_index).wrapping_mul(48u64));
                v_ppx = (v_pointsx).wrapping_add((v_i).wrapping_mul(48u64));
                v_ppy = (v_pointsy).wrapping_add((v_i).wrapping_mul(48u64));
                v_ppz = (v_pointsz).wrapping_add((v_i).wrapping_mul(48u64));
                {
                    let a0: u64 = v_bpx;
                    let a1: u64 = v_ppx;
                    let a2: u64 = v_bpy;
                    let a3: u64 = v_ppy;
                    let a4: u64 = v_bpz;
                    let a5: u64 = v_ppz;
                    let a6: u64 = v_bpx;
                    let a7: u64 = v_bpy;
                    let a8: u64 = v_bpz;
                    msm_curve_add(m, a0, a1, a2, a3, a4, a5, a6, a7, a8);
                }
            } else {
            }
        }
        {
            let a0: u64 = v_runx;
            let a1: u64 = v_runy;
            let a2: u64 = v_runz;
            store_zero(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_wsx;
            let a1: u64 = v_wsy;
            let a2: u64 = v_wsz;
            store_zero(m, a0, a1, a2);
        }
        v_i = 511u64;
        while v_i != 0 {
            v_i = (v_i).wrapping_sub(1u64);
            v_bpx = (v_buckets_x).wrapping_add((v_i).wrapping_mul(48u64));
            v_bpy = (v_buckets_y).wrapping_add((v_i).wrapping_mul(48u64));
            v_bpz = (v_buckets_z).wrapping_add((v_i).wrapping_mul(48u64));
            {
                let a0: u64 = v_runx;
                let a1: u64 = v_bpx;
                let a2: u64 = v_runy;
                let a3: u64 = v_bpy;
                let a4: u64 = v_runz;
                let a5: u64 = v_bpz;
                let a6: u64 = v_runx;
                let a7: u64 = v_runy;
                let a8: u64 = v_runz;
                msm_curve_add(m, a0, a1, a2, a3, a4, a5, a6, a7, a8);
            }
            {
                let a0: u64 = v_wsx;
                let a1: u64 = v_runx;
                let a2: u64 = v_wsy;
                let a3: u64 = v_runy;
                let a4: u64 = v_wsz;
                let a5: u64 = v_runz;
                let a6: u64 = v_wsx;
                let a7: u64 = v_wsy;
                let a8: u64 = v_wsz;
                msm_curve_add(m, a0, a1, a2, a3, a4, a5, a6, a7, a8);
            }
        }
        {
            let a0: u64 = v_outx;
            let a1: u64 = v_wsx;
            let a2: u64 = v_outy;
            let a3: u64 = v_wsy;
            let a4: u64 = v_outz;
            let a5: u64 = v_wsz;
            let a6: u64 = v_outx;
            let a7: u64 = v_outy;
            let a8: u64 = v_outz;
            msm_curve_add(m, a0, a1, a2, a3, a4, a5, a6, a7, a8);
        }
    }
    m.free(48);
    m.free(48);
    m.free(48);
    m.free(48);
    m.free(48);
    m.free(48);
    m.free(24528);
    m.free(24528);
    m.free(24528);
}

pub fn g1_scalar_mul(m: &mut Mem, mut v_outx: u64, mut v_outy: u64, mut v_outz: u64, mut v_scalar: u64, mut v_px: u64, mut v_py: u64, mut v_pz: u64) {
    let mut v_i: u64 = 0;
    let mut v_a: u64 = 0;
    let mut v_bit: u64 = 0;
    {
        let a0: u64 = v_outx;
        let a1: u64 = v_outy;
        let a2: u64 = v_outz;
        store_zero(m, a0, a1, a2);
    }
    v_i = 256u64;
    while v_i != 0 {
        v_i = (v_i).wrapping_sub(1u64);
        {
            let a0: u64 = v_outx;
            let a1: u64 = v_outy;
            let a2: u64 = v_outz;
            let a3: u64 = v_outx;
            let a4: u64 = v_outy;
            let a5: u64 = v_outz;
            msm_curve_double(m, a0, a1, a2, a3, a4, a5);
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
                let a6: u64 = v_outx;
                let a7: u64 = v_outy;
                let a8: u64 = v_outz;
                msm_curve_add(m, a0, a1, a2, a3, a4, a5, a6, a7, a8);
            }
        } else {
        }
    }
}

pub fn msm_curve_add(m: &mut Mem, mut v_X1: u64, mut v_X2: u64, mut v_Y1: u64, mut v_Y2: u64, mut v_Z1: u64, mut v_Z2: u64, mut v_Xout: u64, mut v_Yout: u64, mut v_Zout: u64) {
    let mut v_e: u64 = 0;
    let mut v_t5: u64 = 0;
    let mut v_t0: u64 = 0;
    let mut v_t1: u64 = 0;
    let mut v_t3: u64 = 0;
    let mut v_t4: u64 = 0;
    let mut v_y3: u64 = 0;
    let mut v_t2: u64 = 0;
    let mut v_z3: u64 = 0;
    let mut v_tx: u64 = 0;
    let mut v_ty: u64 = 0;
    let mut v_tz: u64 = 0;
    v_e = 1u64;
    v_e = (v_e & ((m.load64((v_Z2).wrapping_add(0u64)) == 8505329371266088957u64) as u64));
    v_e = (v_e & ((m.load64((v_Z2).wrapping_add(8u64)) == 17002214543764226050u64) as u64));
    v_e = (v_e & ((m.load64((v_Z2).wrapping_add(16u64)) == 6865905132761471162u64) as u64));
    v_e = (v_e & ((m.load64((v_Z2).wrapping_add(24u64)) == 8632934651105793861u64) as u64));
    v_e = (v_e & ((m.load64((v_Z2).wrapping_add(32u64)) == 6631298214892334189u64) as u64));
    v_e = (v_e & ((m.load64((v_Z2).wrapping_add(40u64)) == 1582556514881692819u64) as u64));
    if v_e != 0 {
        v_t5 = m.alloc(48);
        {
            let a0: u64 = v_t5;
            bls12_three_b(m, a0);
        }
        v_t0 = m.alloc(48);
        {
            let a0: u64 = v_t0;
            let a1: u64 = v_X1;
            let a2: u64 = v_X2;
            bls12_mul(m, a0, a1, a2);
        }
        v_t1 = m.alloc(48);
        {
            let a0: u64 = v_t1;
            let a1: u64 = v_Y1;
            let a2: u64 = v_Y2;
            bls12_mul(m, a0, a1, a2);
        }
        v_t3 = m.alloc(48);
        {
            let a0: u64 = v_t3;
            let a1: u64 = v_X2;
            let a2: u64 = v_Y2;
            bls12_add(m, a0, a1, a2);
        }
        v_t4 = m.alloc(48);
        {
            let a0: u64 = v_t4;
            let a1: u64 = v_X1;
            let a2: u64 = v_Y1;
            bls12_add(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t3;
            let a1: u64 = v_t3;
            let a2: u64 = v_t4;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t4;
            let a1: u64 = v_t0;
            let a2: u64 = v_t1;
            bls12_add(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t3;
            let a1: u64 = v_t3;
            let a2: u64 = v_t4;
            bls12_sub(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t4;
            let a1: u64 = v_Y2;
            let a2: u64 = v_Z1;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t4;
            let a1: u64 = v_t4;
            let a2: u64 = v_Y1;
            bls12_add(m, a0, a1, a2);
        }
        v_y3 = m.alloc(48);
        {
            let a0: u64 = v_y3;
            let a1: u64 = v_X2;
            let a2: u64 = v_Z1;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_y3;
            let a1: u64 = v_y3;
            let a2: u64 = v_X1;
            bls12_add(m, a0, a1, a2);
        }
        v_t2 = m.alloc(48);
        {
            let a0: u64 = v_t2;
            let a1: u64 = v_t0;
            let a2: u64 = v_t0;
            bls12_add(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t0;
            let a1: u64 = v_t2;
            let a2: u64 = v_t0;
            bls12_add(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t2;
            let a1: u64 = v_t5;
            let a2: u64 = v_Z1;
            bls12_mul(m, a0, a1, a2);
        }
        v_z3 = m.alloc(48);
        {
            let a0: u64 = v_z3;
            let a1: u64 = v_t1;
            let a2: u64 = v_t2;
            bls12_add(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t1;
            let a1: u64 = v_t1;
            let a2: u64 = v_t2;
            bls12_sub(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_y3;
            let a1: u64 = v_t5;
            let a2: u64 = v_y3;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t5;
            let a1: u64 = v_t4;
            let a2: u64 = v_y3;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t2;
            let a1: u64 = v_t3;
            let a2: u64 = v_t1;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_Xout;
            let a1: u64 = v_t2;
            let a2: u64 = v_t5;
            bls12_sub(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_y3;
            let a1: u64 = v_y3;
            let a2: u64 = v_t0;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t1;
            let a1: u64 = v_t1;
            let a2: u64 = v_z3;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_Yout;
            let a1: u64 = v_t1;
            let a2: u64 = v_y3;
            bls12_add(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_t0;
            let a1: u64 = v_t0;
            let a2: u64 = v_t3;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_z3;
            let a1: u64 = v_z3;
            let a2: u64 = v_t4;
            bls12_mul(m, a0, a1, a2);
        }
        {
            let a0: u64 = v_Zout;
            let a1: u64 = v_z3;
            let a2: u64 = v_t0;
            bls12_add(m, a0, a1, a2);
        }
        m.free(48);
        m.free(48);
        m.free(48);
        m.free(48);
        m.free(48);
        m.free(48);
        m.free(48);
        m.free(48);
    } else {
        v_tx = m.alloc(48);
        v_ty = m.alloc(48);
        v_tz = m.alloc(48);
        {
            let a0: u64 = v_X1;
            let a1: u64 = v_X2;
            let a2: u64 = v_Y1;
            let a3: u64 = v_Y2;
            let a4: u64 = v_Z1;
            let a5: u64 = v_Z2;
            let a6: u64 = v_tx;
            let a7: u64 = v_ty;
            let a8: u64 = v_tz;
            curve_add(m, a0, a1, a2, a3, a4, a5, a6, a7, a8);
        }
        {
            let a0: u64 = v_Xout;
            let a1: u64 = v_tx;
            bls12_felem_copy(m, a0, a1);
        }
        {
            let a0: u64 = v_Yout;
            let a1: u64 = v_ty;
            bls12_felem_copy(m, a0, a1);
        }
        {
            let a0: u64 = v_Zout;
            let a1: u64 = v_tz;
            bls12_felem_copy(m, a0, a1);
        }
        m.free(48);
        m.free(48);
        m.free(48);
    }
}

pub fn msm_curve_double(m: &mut Mem, mut v_Xin: u64, mut v_Yin: u64, mut v_Zin: u64, mut v_Xout: u64, mut v_Yout: u64, mut v_Zout: u64) {
    let mut v_tx: u64 = 0;
    let mut v_ty: u64 = 0;
    let mut v_tz: u64 = 0;
    v_tx = m.alloc(48);
    v_ty = m.alloc(48);
    v_tz = m.alloc(48);
    {
        let a0: u64 = v_Xin;
        let a1: u64 = v_Yin;
        let a2: u64 = v_Zin;
        let a3: u64 = v_tx;
        let a4: u64 = v_ty;
        let a5: u64 = v_tz;
        curve_double_a0(m, a0, a1, a2, a3, a4, a5);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_tx;
        bls12_felem_copy(m, a0, a1);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_ty;
        bls12_felem_copy(m, a0, a1);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_tz;
        bls12_felem_copy(m, a0, a1);
    }
    m.free(48);
    m.free(48);
    m.free(48);
}

pub fn curve_add(m: &mut Mem, mut v_X1: u64, mut v_X2: u64, mut v_Y1: u64, mut v_Y2: u64, mut v_Z1: u64, mut v_Z2: u64, mut v_Xout: u64, mut v_Yout: u64, mut v_Zout: u64) {
    let mut v_three_b: u64 = 0;
    let mut v_t0: u64 = 0;
    let mut v_t1: u64 = 0;
    let mut v_t2: u64 = 0;
    let mut v_t3: u64 = 0;
    let mut v_t4: u64 = 0;
    let mut v_t5: u64 = 0;
    v_three_b = m.alloc(48);
    {
        let a0: u64 = v_three_b;
        bls12_three_b(m, a0);
    }
    v_t0 = m.alloc(48);
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_X1;
        let a2: u64 = v_X2;
        bls12_mul(m, a0, a1, a2);
    }
    v_t1 = m.alloc(48);
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_Y1;
        let a2: u64 = v_Y2;
        bls12_mul(m, a0, a1, a2);
    }
    v_t2 = m.alloc(48);
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_Z1;
        let a2: u64 = v_Z2;
        bls12_mul(m, a0, a1, a2);
    }
    v_t3 = m.alloc(48);
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_X1;
        let a2: u64 = v_Y1;
        bls12_add(m, a0, a1, a2);
    }
    v_t4 = m.alloc(48);
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_X2;
        let a2: u64 = v_Y2;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_t3;
        let a2: u64 = v_t4;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_t0;
        let a2: u64 = v_t1;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t3;
        let a1: u64 = v_t3;
        let a2: u64 = v_t4;
        bls12_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_X1;
        let a2: u64 = v_Z1;
        bls12_add(m, a0, a1, a2);
    }
    v_t5 = m.alloc(48);
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_X2;
        let a2: u64 = v_Z2;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_t4;
        let a2: u64 = v_t5;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_t0;
        let a2: u64 = v_t2;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_t4;
        let a2: u64 = v_t5;
        bls12_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_Y1;
        let a2: u64 = v_Z1;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_Y2;
        let a2: u64 = v_Z2;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_t5;
        let a2: u64 = v_Xout;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t1;
        let a2: u64 = v_t2;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t5;
        let a1: u64 = v_t5;
        let a2: u64 = v_Xout;
        bls12_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_three_b;
        let a2: u64 = v_t2;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t1;
        let a2: u64 = v_Zout;
        bls12_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_Zout;
        let a2: u64 = v_t1;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_Xout;
        let a2: u64 = v_Zout;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_t0;
        let a2: u64 = v_t0;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_t1;
        let a2: u64 = v_t0;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t4;
        let a1: u64 = v_three_b;
        let a2: u64 = v_t4;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t1;
        let a2: u64 = v_t4;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_Yout;
        let a2: u64 = v_t0;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t5;
        let a2: u64 = v_t4;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t3;
        let a2: u64 = v_Xout;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_Xout;
        let a2: u64 = v_t0;
        bls12_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t3;
        let a2: u64 = v_t1;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_t5;
        let a2: u64 = v_Zout;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_Zout;
        let a2: u64 = v_t0;
        bls12_add(m, a0, a1, a2);
    }
    m.free(48);
    m.free(48);
    m.free(48);
    m.free(48);
    m.free(48);
    m.free(48);
    m.free(48);
}

pub fn curve_double_a0(m: &mut Mem, mut v_Xin: u64, mut v_Yin: u64, mut v_Zin: u64, mut v_Xout: u64, mut v_Yout: u64, mut v_Zout: u64) {
    let mut v_three_b: u64 = 0;
    let mut v_t0: u64 = 0;
    let mut v_t1: u64 = 0;
    let mut v_t2: u64 = 0;
    v_three_b = m.alloc(48);
    {
        let a0: u64 = v_three_b;
        bls12_three_b(m, a0);
    }
    v_t0 = m.alloc(48);
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_Yin;
        let a2: u64 = v_Yin;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_t0;
        let a2: u64 = v_t0;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_Zout;
        let a2: u64 = v_Zout;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_Zout;
        let a2: u64 = v_Zout;
        bls12_add(m, a0, a1, a2);
    }
    v_t1 = m.alloc(48);
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_Yin;
        let a2: u64 = v_Zin;
        bls12_mul(m, a0, a1, a2);
    }
    v_t2 = m.alloc(48);
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_Zin;
        let a2: u64 = v_Zin;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_three_b;
        let a2: u64 = v_t2;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t2;
        let a2: u64 = v_Zout;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_t0;
        let a2: u64 = v_t2;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Zout;
        let a1: u64 = v_t1;
        let a2: u64 = v_Zout;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_t2;
        let a2: u64 = v_t2;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t2;
        let a1: u64 = v_t1;
        let a2: u64 = v_t2;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t0;
        let a1: u64 = v_t0;
        let a2: u64 = v_t2;
        bls12_sub(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_t0;
        let a2: u64 = v_Yout;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Yout;
        let a1: u64 = v_Xout;
        let a2: u64 = v_Yout;
        bls12_add(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_t1;
        let a1: u64 = v_Xin;
        let a2: u64 = v_Yin;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_t0;
        let a2: u64 = v_t1;
        bls12_mul(m, a0, a1, a2);
    }
    {
        let a0: u64 = v_Xout;
        let a1: u64 = v_Xout;
        let a2: u64 = v_Xout;
        bls12_add(m, a0, a1, a2);
    }
    m.free(48);
    m.free(48);
    m.free(48);
    m.free(48);
}

pub fn store_zero(m: &mut Mem, mut v_outx: u64, mut v_outy: u64, mut v_outz: u64) {
    {
        let a0: u64 = v_outx;
        bls12_zero(m, a0);
    }
    {
        let a0: u64 = v_outy;
        bls12_one(m, a0);
    }
    {
        let a0: u64 = v_outz;
        bls12_zero(m, a0);
    }
}

pub fn bls12_three_b(m: &mut Mem, mut v_out: u64) {
    { let a: u64 = v_out; let v: u64 = 4933130441833534766u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(8u64); let v: u64 = 15904462746612662304u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(16u64); let v: u64 = 8034115857496836953u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(24u64); let v: u64 = 12755092135412849606u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(32u64); let v: u64 = 7007796720291435703u64; m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(40u64); let v: u64 = 252692002104915169u64; m.store64(a, v); }
}

pub fn bls12_felem_copy(m: &mut Mem, mut v_out: u64, mut v_in: u64) {
    { let a: u64 = v_out; let v: u64 = m.load64(v_in); m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(8u64); let v: u64 = m.load64((v_in).wrapping_add(8u64)); m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(16u64); let v: u64 = m.load64((v_in).wrapping_add(16u64)); m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(24u64); let v: u64 = m.load64((v_in).wrapping_add(24u64)); m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(32u64); let v: u64 = m.load64((v_in).wrapping_add(32u64)); m.store64(a, v); }
    { let a: u64 = (v_out).wrapping_add(40u64); let v: u64 = m.load64((v_in).wrapping_add(40u64)); m.store64(a, v); }
}

pub fn g1_scalar_mul_ct(m: &mut Mem, mut v_outx: u64, mut v_outy: u64, mut v_outz: u64, mut v_tx: u64, mut v_ty: u64, mut v_tz: u64, mut v_scalar: u64, mut v_px: u64, mut v_py: u64, mut v_pz: u64) {
    let mut v_i: u64 = 0;
    let mut v_a: u64 = 0;
    let mut v_bit: u64 = 0;
    {
        let a0: u64 = v_outx;
        let a1: u64 = v_outy;
        let a2: u64 = v_outz;
        store_zero(m, a0, a1, a2);
    }
    v_i = 256u64;
    while v_i != 0 {
        v_i = (v_i).wrapping_sub(1u64);
        {
            let a0: u64 = v_outx;
            let a1: u64 = v_outy;
            let a2: u64 = v_outz;
            let a3: u64 = v_outx;
            let a4: u64 = v_outy;
            let a5: u64 = v_outz;
            msm_curve_double(m, a0, a1, a2, a3, a4, a5);
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
            curve_add(m, a0, a1, a2, a3, a4, a5, a6, a7, a8);
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
    v__gs_to0 = 6u64;
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
