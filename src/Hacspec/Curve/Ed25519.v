(** This file was automatically generated using Hacspec **)
Require Import Hacspec.Util.Lib.
Require Import Hacspec.Util.MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.


Definition field_canvas_t := nseq (int8) (32).
Definition ed25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_scalar_canvas_t := nseq (int8) (64).
Definition big_scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_integer_canvas_t := nseq (int8) (32).
Definition big_integer_t :=
  nat_mod 0x8000000000000000000000000000000080000000000000000000000000000000.

Notation "'ed_point_t'" := ((
  ed25519_field_element_t ×
  ed25519_field_element_t ×
  ed25519_field_element_t ×
  ed25519_field_element_t
)) : hacspec_scope.

Definition compressed_ed_point_t := nseq (uint8) (usize 32).

Definition serialized_scalar_t := nseq (uint8) (usize 32).

Definition signature_t := nseq (uint8) (usize 64).

Notation "'public_key_t'" := (compressed_ed_point_t) : hacspec_scope.

Notation "'secret_key_t'" := (serialized_scalar_t) : hacspec_scope.

Inductive error_t :=
| InvalidPublickey : error_t
| InvalidSignature : error_t
| InvalidS : error_t
| InvalidR : error_t
| SmallOrderPoint : error_t
| NotEnoughRandomness : error_t.

Notation "'verify_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition base_v : compressed_ed_point_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8
      ] in  l).

Definition constant_p_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 237) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 127) : int8
      ] in  l).

Definition constant_l_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 237) : int8;
        secret (@repr WORDSIZE8 211) : int8;
        secret (@repr WORDSIZE8 245) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 26) : int8;
        secret (@repr WORDSIZE8 99) : int8;
        secret (@repr WORDSIZE8 18) : int8;
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 214) : int8;
        secret (@repr WORDSIZE8 156) : int8;
        secret (@repr WORDSIZE8 247) : int8;
        secret (@repr WORDSIZE8 162) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 249) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 20) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 16) : int8
      ] in  l).

Definition constant_p3_8_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 254) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 15) : int8
      ] in  l).

Definition constant_p1_4_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 251) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 31) : int8
      ] in  l).

Definition constant_d_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 163) : int8;
        secret (@repr WORDSIZE8 120) : int8;
        secret (@repr WORDSIZE8 89) : int8;
        secret (@repr WORDSIZE8 19) : int8;
        secret (@repr WORDSIZE8 202) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 117) : int8;
        secret (@repr WORDSIZE8 171) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 10) : int8;
        secret (@repr WORDSIZE8 112) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 232) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 119) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 199) : int8;
        secret (@repr WORDSIZE8 140) : int8;
        secret (@repr WORDSIZE8 115) : int8;
        secret (@repr WORDSIZE8 254) : int8;
        secret (@repr WORDSIZE8 111) : int8;
        secret (@repr WORDSIZE8 43) : int8;
        secret (@repr WORDSIZE8 238) : int8;
        secret (@repr WORDSIZE8 108) : int8;
        secret (@repr WORDSIZE8 3) : int8;
        secret (@repr WORDSIZE8 82) : int8
      ] in  l).

Definition is_negative (x_0 : ed25519_field_element_t) : uint8 :=
  (if (nat_mod_bit (x_0) (usize 0)):bool then (secret (
        @repr WORDSIZE8 1) : int8) else (secret (@repr WORDSIZE8 0) : int8)).

Definition compress (p_1 : ed_point_t) : compressed_ed_point_t :=
  let '(x_2, y_3, z_4, _) :=
    p_1 in 
  let z_inv_5 : ed25519_field_element_t :=
    nat_mod_inv (z_4) in 
  let x_6 : ed25519_field_element_t :=
    (x_2) *% (z_inv_5) in 
  let y_7 : ed25519_field_element_t :=
    (y_3) *% (z_inv_5) in 
  let s_8 : byte_seq :=
    nat_mod_to_byte_seq_le (y_7) in 
  let s_8 :=
    seq_upd s_8 (usize 31) ((seq_index (s_8) (usize 31)) .^ ((is_negative (
            x_6)) shift_left (usize 7))) in 
  array_from_slice (default) (32) (s_8) (usize 0) (usize 32).

Definition sqrt
  (a_9 : ed25519_field_element_t)
  : (option ed25519_field_element_t) :=
  let p3_8_10 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (constant_p3_8_v) : ed25519_field_element_t in 
  let p1_4_11 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (constant_p1_4_v) : ed25519_field_element_t in 
  let x_c_12 : ed25519_field_element_t :=
    nat_mod_pow_self (a_9) (p3_8_10) in 
  let result_13 : (option ed25519_field_element_t) :=
    @None ed25519_field_element_t in 
  let '(result_13) :=
    if ((x_c_12) *% (x_c_12)) =.? (a_9):bool then (let result_13 :=
        Some (x_c_12) in 
      (result_13)) else ((result_13)) in 
  let '(result_13) :=
    if ((x_c_12) *% (x_c_12)) =.? ((nat_mod_zero ) -% (a_9)):bool then (
      let x_14 : ed25519_field_element_t :=
        (nat_mod_pow_self (nat_mod_two ) (p1_4_11)) *% (x_c_12) in 
      let result_13 :=
        Some (x_14) in 
      (result_13)) else ((result_13)) in 
  result_13.

Definition check_canonical_point (x_15 : compressed_ed_point_t) : bool :=
  let x_15 :=
    array_upd x_15 (usize 31) ((array_index (x_15) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let x_16 : big_integer_t :=
    nat_mod_from_byte_seq_le (x_15) : big_integer_t in 
  (x_16) <.? (nat_mod_from_byte_seq_le (constant_p_v) : big_integer_t).

Definition decompress (q_17 : compressed_ed_point_t) : (option ed_point_t) :=
  let d_18 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (constant_d_v) : ed25519_field_element_t in 
  let x_s_19 : uint8 :=
    ((array_index (q_17) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_20 : compressed_ed_point_t :=
    q_17 in 
  let y_s_20 :=
    array_upd y_s_20 (usize 31) ((array_index (y_s_20) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  ifbnd negb (check_canonical_point (y_s_20)) : bool
  thenbnd (bind (@None ed_point_t) (fun _ => Some (tt)))
  else (tt) >> (fun 'tt =>
  let y_21 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (y_s_20) : ed25519_field_element_t in 
  let z_22 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_23 : ed25519_field_element_t :=
    (y_21) *% (y_21) in 
  let u_24 : ed25519_field_element_t :=
    (yy_23) -% (z_22) in 
  let v_25 : ed25519_field_element_t :=
    ((d_18) *% (yy_23)) +% (z_22) in 
  let xx_26 : ed25519_field_element_t :=
    (u_24) *% (nat_mod_inv (v_25)) in 
  bind (sqrt (xx_26)) (fun x_27 => let x_r_28 : uint8 :=
      is_negative (x_27) in 
    ifbnd ((x_27) =.? (nat_mod_zero )) && ((uint8_declassify (x_s_19)) =.? (
        @repr WORDSIZE8 1)) : bool
    thenbnd (bind (@None ed_point_t) (fun _ => Some (tt)))
    else (tt) >> (fun 'tt =>
    let '(x_27) :=
      if (uint8_declassify (x_r_28)) !=.? (uint8_declassify (
          x_s_19)):bool then (let x_27 :=
          (nat_mod_zero ) -% (x_27) in 
        (x_27)) else ((x_27)) in 
    Some ((x_27, y_21, z_22, (x_27) *% (y_21)))))).

Definition decompress_non_canonical
  (p_29 : compressed_ed_point_t)
  : (option ed_point_t) :=
  let d_30 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (constant_d_v) : ed25519_field_element_t in 
  let x_s_31 : uint8 :=
    ((array_index (p_29) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_32 : compressed_ed_point_t :=
    p_29 in 
  let y_s_32 :=
    array_upd y_s_32 (usize 31) ((array_index (y_s_32) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let y_33 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (y_s_32) : ed25519_field_element_t in 
  let z_34 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_35 : ed25519_field_element_t :=
    (y_33) *% (y_33) in 
  let u_36 : ed25519_field_element_t :=
    (yy_35) -% (z_34) in 
  let v_37 : ed25519_field_element_t :=
    ((d_30) *% (yy_35)) +% (z_34) in 
  let xx_38 : ed25519_field_element_t :=
    (u_36) *% (nat_mod_inv (v_37)) in 
  bind (sqrt (xx_38)) (fun x_39 => let x_r_40 : uint8 :=
      is_negative (x_39) in 
    let '(x_39) :=
      if (uint8_declassify (x_r_40)) !=.? (uint8_declassify (
          x_s_31)):bool then (let x_39 :=
          (nat_mod_zero ) -% (x_39) in 
        (x_39)) else ((x_39)) in 
    Some ((x_39, y_33, z_34, (x_39) *% (y_33)))).

Definition point_add (p_41 : ed_point_t) (q_42 : ed_point_t) : ed_point_t :=
  let d_c_43 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (constant_d_v) : ed25519_field_element_t in 
  let two_44 : ed25519_field_element_t :=
    nat_mod_two  in 
  let '(x1_45, y1_46, z1_47, t1_48) :=
    p_41 in 
  let '(x2_49, y2_50, z2_51, t2_52) :=
    q_42 in 
  let a_53 : ed25519_field_element_t :=
    ((y1_46) -% (x1_45)) *% ((y2_50) -% (x2_49)) in 
  let b_54 : ed25519_field_element_t :=
    ((y1_46) +% (x1_45)) *% ((y2_50) +% (x2_49)) in 
  let c_55 : ed25519_field_element_t :=
    (((t1_48) *% (two_44)) *% (d_c_43)) *% (t2_52) in 
  let d_56 : ed25519_field_element_t :=
    ((z1_47) *% (two_44)) *% (z2_51) in 
  let e_57 : ed25519_field_element_t :=
    (b_54) -% (a_53) in 
  let f_58 : ed25519_field_element_t :=
    (d_56) -% (c_55) in 
  let g_59 : ed25519_field_element_t :=
    (d_56) +% (c_55) in 
  let h_60 : ed25519_field_element_t :=
    (b_54) +% (a_53) in 
  let x3_61 : ed25519_field_element_t :=
    (e_57) *% (f_58) in 
  let y3_62 : ed25519_field_element_t :=
    (g_59) *% (h_60) in 
  let t3_63 : ed25519_field_element_t :=
    (e_57) *% (h_60) in 
  let z3_64 : ed25519_field_element_t :=
    (f_58) *% (g_59) in 
  (x3_61, y3_62, z3_64, t3_63).

Definition point_identity  : ed_point_t :=
  (nat_mod_zero , nat_mod_one , nat_mod_one , nat_mod_zero ).

Definition point_mul (s_65 : scalar_t) (p_66 : ed_point_t) : ed_point_t :=
  let p_67 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    p_66 in 
  let q_68 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(p_67, q_68) :=
    foldi (usize 0) (usize 256) (fun i_69 '(p_67, q_68) =>
      let '(q_68) :=
        if nat_mod_bit (s_65) (i_69):bool then (let q_68 :=
            point_add (q_68) (p_67) in 
          (q_68)) else ((q_68)) in 
      let p_67 :=
        point_add (p_67) (p_67) in 
      (p_67, q_68))
    (p_67, q_68) in 
  q_68.

Definition point_mul_by_cofactor (p_70 : ed_point_t) : ed_point_t :=
  let p2_71 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p_70) (p_70) in 
  let p4_72 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p2_71) (p2_71) in 
  let p8_73 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p4_72) (p4_72) in 
  p8_73.

Definition point_neg (p_74 : ed_point_t) : ed_point_t :=
  let '(x_75, y_76, z_77, t_78) :=
    p_74 in 
  ((nat_mod_zero ) -% (x_75), y_76, z_77, (nat_mod_zero ) -% (t_78)).

Definition point_eq (p_79 : ed_point_t) (q_80 : ed_point_t) : bool :=
  let '(x1_81, y1_82, z1_83, _) :=
    p_79 in 
  let '(x2_84, y2_85, z2_86, _) :=
    q_80 in 
  (((x1_81) *% (z2_86)) =.? ((x2_84) *% (z1_83))) && (((y1_82) *% (z2_86)) =.? (
      (y2_85) *% (z1_83))).
