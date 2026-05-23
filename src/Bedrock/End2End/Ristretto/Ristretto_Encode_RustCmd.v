(** * Ristretto_Encode_RustCmd — ristretto255 ENCODER as [rust_cmd_ed].
 *
 *  Mirror of [Ristretto_RustCmd.ristretto_decode_rs] for the ENCODE
 *  direction (RFC 9496 §4.3.2 / draft-irtf-cfrg-ristretto255 §3.2.2).
 *
 *  GOAL: produce [ristretto_encode_rs : rust_cmd_ed] and a functional
 *  simulation against the Gallina spec
 *  [End2End/Lizard/RistrettoEncode.ristretto_encode_gallina].
 *
 *  Input  : 200-byte xyzt slot ("xyzt_var"), extended-twisted-Edwards
 *           coordinates (X, Y, Z, Ta, Tb).
 *  Output : 32-byte canonical Ristretto255 encoding ("out_var").
 *
 *  Strategy (same as the decoder):
 *   1. Wrap the existing Gallina with [nlet_red] markup
 *      ([ristretto_encode_gallina_nlet]).  Semantically equal to
 *      [ristretto_encode_gallina] by [eq_refl] after unfolding
 *      [nlet_red] / [stack].
 *   2. Hand-author the [rust_cmd_ed] AST ([ristretto_encode_rs]) using
 *      the same constructor toolkit the decoder uses:
 *        REdLetZero (slot allocs), REdSetBytes (verified constants),
 *        REdCall / REdCallN (felem ops + structured leaves),
 *        REdByteLoad + REdSelect (is_negative tests + CT cmov).
 *   3. Provide a [spec_of_ed] instance whose post pins the output slot
 *      to [ristretto_encode_gallina_nlet xyzt].
 *
 *  Two encode-specific leaves are needed beyond the shared
 *  [strong_callee_post_ristretto] dispatch (which already covers
 *  fe25519_{mul,add,sub,sq}, ristretto_sqrt_ratio_m1,
 *  ristretto_pack_canonical_felem, ristretto_canonical_negate):
 *    - [unpack_xyzt5]  : 5-output split of the 200-byte input into the
 *                        five 32-byte felems (REdCallN).
 *    - [fe25519_inv]   : modular inverse [z^(p-2) mod p], used for
 *                        [extended_T ta tb z = (ta*tb*z^(p-2)) mod p].
 *  Both branches are added in the local composite dispatchers
 *  [strong_callee_post_encode] / [strong_callee_post_n_encode] below.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdRupicola.
Require Import Bedrock.RustCmdRupicolaDefn.
Require Import Bedrock.RustCmdRupicolaGallina.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.  (* slot_holds, frames_except *)
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Lizard.RistrettoConsts.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Require Import Bedrock.End2End.Lizard.RistrettoEncode.
Require Import Bedrock.End2End.Ristretto.RistrettoBridges.
Require Import Bedrock.End2End.Ristretto.Ristretto_RustCmd.  (* LE_TBytes_r, const_*_zs *)
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ========================================================================
   Section 1: nlet-annotated Gallina encoder.

   Pure markup over [ristretto_encode_gallina].  Each algorithmic step
   becomes [nlet_red [name] (stack v) (fun name => ...)].  Semantically
   identical to [ristretto_encode_gallina] (only the 200-length branch
   is wrapped; the else-branch is verbatim).
   ======================================================================== *)

Definition ristretto_encode_gallina_nlet (xyzt : list Byte.byte) : list Byte.byte :=
  if Nat.eqb (length xyzt) 200 then
    let '(x, y, z, ta, tb) := parse_xyzt5 xyzt in
    nlet_red ["t"]       (stack (extended_T ta tb z))                  (fun t =>
    nlet_red ["u1"]      (stack (((z + y) * (z - y)) mod ed25519_p))   (fun u1 =>
    nlet_red ["u2"]      (stack ((x * y) mod ed25519_p))               (fun u2 =>
    nlet_red ["u2_sq"]   (stack ((u2 * u2) mod ed25519_p))             (fun u2_sq =>
    nlet_red ["den"]     (stack ((u1 * u2_sq) mod ed25519_p))          (fun den =>
    let '(_, invsqrt) := ristretto_sqrt_ratio_m1 1 den in
    nlet_red ["D1"]      (stack ((invsqrt * u1) mod ed25519_p))        (fun D1 =>
    nlet_red ["D2"]      (stack ((invsqrt * u2) mod ed25519_p))        (fun D2 =>
    nlet_red ["Zinv"]    (stack ((D1 * D2 * t) mod ed25519_p))         (fun Zinv =>
    nlet_red ["ix"]      (stack ((x * ristretto_SQRT_M1) mod ed25519_p)) (fun ix =>
    nlet_red ["iy"]      (stack ((y * ristretto_SQRT_M1) mod ed25519_p)) (fun iy =>
    nlet_red ["eden"]    (stack ((D1 * ristretto_INVSQRT_A_MINUS_D) mod ed25519_p)) (fun eden =>
    nlet_red ["tZinv"]   (stack ((t * Zinv) mod ed25519_p))            (fun tZinv =>
    let rotate := ristretto_is_negative tZinv in
    nlet_red ["x'"]      (stack (if rotate then iy else x))            (fun x' =>
    nlet_red ["y'"]      (stack (if rotate then ix else y))            (fun y' =>
    nlet_red ["den_inv"] (stack (if rotate then eden else D2))         (fun den_inv =>
    nlet_red ["x_z_inv"] (stack ((x' * Zinv) mod ed25519_p))           (fun x_z_inv =>
    nlet_red ["y''"]     (stack (if ristretto_is_negative x_z_inv
                                  then ristretto_canonical_negate y'
                                  else (y' mod ed25519_p)))            (fun y'' =>
    nlet_red ["s_raw"]   (stack ((den_inv * ((z - y'') mod ed25519_p)) mod ed25519_p)) (fun s_raw =>
    nlet_red ["s"]       (stack (if ristretto_is_negative s_raw
                                  then ristretto_canonical_negate s_raw
                                  else s_raw))                          (fun s =>
      ristretto_pack_canonical_felem s
    )))))))))))))))))))
  else
    List.repeat Byte.x00 32.

Lemma ristretto_encode_gallina_nlet_eq :
  forall xyzt, ristretto_encode_gallina_nlet xyzt
             = ristretto_encode_gallina xyzt.
Proof.
  intros xyzt.
  unfold ristretto_encode_gallina_nlet, ristretto_encode_gallina,
         nlet_red, RustCmdRupicolaGallina.stack.
  reflexivity.
Qed.

(* ========================================================================
   Section 2: Encode-specific leaf specs + composite callee_post.

   The two new leaves (unpack_xyzt5 + fe25519_inv) are not in
   [RistrettoBridges.strong_callee_post_ristretto].  We define their
   [strong_callee_post] branches here and compose with the shared
   ristretto dispatch.
   ======================================================================== *)

(** [fe25519_inv_spec a] = the canonical 32-byte LE encoding of
    [a^(p-2) mod p] = [pow_mod (le_combine a) (p-2) p]. *)
Definition fe25519_inv_spec (a : list Byte.byte) : list Byte.byte :=
  le_split 32 (pow_mod (le_combine a) (ed25519_p - 2) ed25519_p).

Lemma fe25519_inv_spec_len : forall a, length (fe25519_inv_spec a) = 32%nat.
Proof. intros; apply length_le_split. Qed.

Definition strong_callee_post_fe25519_inv
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match args with
  | [a] =>
      exists a_bs,
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs2 dst.(loc_var) (fe25519_inv_spec a_bs)
  | _ => True
  end.

(** [unpack_xyzt5_*_spec xyzt] = the 32-byte LE re-encoding of the
    corresponding [parse_xyzt5] field.  [parse_felem] reduces its
    40-byte input mod p (via [le_combine] then implicit reduction in
    the consuming arithmetic), but the Gallina [parse_xyzt5] component
    is itself an unreduced [Z] — the leaf re-encodes
    [le_split 32 (parse_xyzt5 component)].  Since the encode body only
    ever uses each component inside a [mod ed25519_p] arithmetic op,
    carrying the canonical 32-byte encoding of the *reduced* component
    is sound. *)
Definition unpack_x_spec  (xyzt : list Byte.byte) : list Byte.byte :=
  le_split 32 ((fst (fst (fst (fst (parse_xyzt5 xyzt))))) mod ed25519_p).
Definition unpack_y_spec  (xyzt : list Byte.byte) : list Byte.byte :=
  le_split 32 ((snd (fst (fst (fst (parse_xyzt5 xyzt))))) mod ed25519_p).
Definition unpack_z_spec  (xyzt : list Byte.byte) : list Byte.byte :=
  le_split 32 ((snd (fst (fst (parse_xyzt5 xyzt)))) mod ed25519_p).
Definition unpack_ta_spec (xyzt : list Byte.byte) : list Byte.byte :=
  le_split 32 ((snd (fst (parse_xyzt5 xyzt))) mod ed25519_p).
Definition unpack_tb_spec (xyzt : list Byte.byte) : list Byte.byte :=
  le_split 32 ((snd (parse_xyzt5 xyzt)) mod ed25519_p).

Lemma unpack_x_spec_len  : forall xyzt, length (unpack_x_spec xyzt)  = 32%nat.
Proof. intros; apply length_le_split. Qed.
Lemma unpack_y_spec_len  : forall xyzt, length (unpack_y_spec xyzt)  = 32%nat.
Proof. intros; apply length_le_split. Qed.
Lemma unpack_z_spec_len  : forall xyzt, length (unpack_z_spec xyzt)  = 32%nat.
Proof. intros; apply length_le_split. Qed.
Lemma unpack_ta_spec_len : forall xyzt, length (unpack_ta_spec xyzt) = 32%nat.
Proof. intros; apply length_le_split. Qed.
Lemma unpack_tb_spec_len : forall xyzt, length (unpack_tb_spec xyzt) = 32%nat.
Proof. intros; apply length_le_split. Qed.

(** [unpack_xyzt5]: 1-input (the 200-byte slot), 5-output
    (x,y,z,ta,tb).  Modeled via [REdCallN] / the 2-output-style
    [callee_post_n] schema extended to five destinations. *)
Definition strong_callee_post_unpack_xyzt5
           (args : list located_ed)
           (dsts : list located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  match dsts, args with
  | [xd; yd; zd; tad; tbd], [xyzt] =>
      frames_except rs1 rs2 xd.(loc_var) /\
      frames_except rs1 rs2 yd.(loc_var) /\
      frames_except rs1 rs2 zd.(loc_var) /\
      frames_except rs1 rs2 tad.(loc_var) /\
      frames_except rs1 rs2 tbd.(loc_var) /\
      exists xyzt_bs,
        slot_holds rs1 xyzt.(loc_var) xyzt_bs /\
        slot_holds rs2 xd.(loc_var)  (unpack_x_spec  xyzt_bs) /\
        slot_holds rs2 yd.(loc_var)  (unpack_y_spec  xyzt_bs) /\
        slot_holds rs2 zd.(loc_var)  (unpack_z_spec  xyzt_bs) /\
        slot_holds rs2 tad.(loc_var) (unpack_ta_spec xyzt_bs) /\
        slot_holds rs2 tbd.(loc_var) (unpack_tb_spec xyzt_bs)
  | _, _ => True
  end.

(** Single-output composite: delegate to the shared ristretto dispatch
    for the felem ops + pack + negate, add the [fe25519_inv] branch. *)
Definition strong_callee_post_encode
           (fname : String.string)
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  match fname with
  | "fe25519_inv" => strong_callee_post_fe25519_inv args dst rs1 rs2
  | _ => strong_callee_post_ristretto fname args dst rs1 rs2
  end.

(** Multi-output composite: delegate to the shared ristretto dispatch
    for sqrt_ratio_m1, add the [unpack_xyzt5] branch. *)
Definition strong_callee_post_n_encode
           (fname : String.string)
           (dsts args : list located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  match fname with
  | "unpack_xyzt5" => strong_callee_post_unpack_xyzt5 args dsts rs1 rs2
  | _ => strong_callee_post_n_ristretto fname dsts args rs1 rs2
  end.

(* ========================================================================
   Section 3: Constant byte lists (for REdSetBytes).
   ======================================================================== *)

(** SQRT_M1 / INVSQRT_A_MINUS_D as 32-byte LE [list Z], derived from the
    canonical [le_split] encodings so the simulation lemma
    [map Z_to_byte const_* = le_split 32 ristretto_*] holds by
    [vm_compute]. *)
Definition const_sqrt_m1_zs : list Z :=
  List.map byte.unsigned (le_split 32 ristretto_SQRT_M1).
Definition const_invsqrt_amd_zs : list Z :=
  List.map byte.unsigned (le_split 32 ristretto_INVSQRT_A_MINUS_D).
(** The prime [p] (reuse the decoder's [const_p_zs] via re-import). *)

(* ========================================================================
   Section 4: Slot-name definitions for the encoder AST.
   ======================================================================== *)

Definition v_re_xyzt    := "xyzt_var".
Definition v_re_out     := "out_var".
(* unpacked input felems *)
Definition v_re_x       := "x_var".
Definition v_re_y       := "y_var".
Definition v_re_z       := "z_var".
Definition v_re_ta      := "ta_var".
Definition v_re_tb      := "tb_var".
(* constants *)
Definition v_re_one     := "one_var".
Definition v_re_p       := "p_var".
Definition v_re_sqrtm1  := "sqrtm1_var".
Definition v_re_invad   := "invad_var".
(* extended T *)
Definition v_re_zinv    := "zinv_var".
Definition v_re_tatb    := "tatb_var".
Definition v_re_t       := "t_var".
(* main chain *)
Definition v_re_zpy     := "zpy_var".
Definition v_re_zmy     := "zmy_var".
Definition v_re_u1      := "u1_var".
Definition v_re_u2      := "u2_var".
Definition v_re_u2sq    := "u2sq_var".
Definition v_re_den     := "den_var".
Definition v_re_ws      := "ws_var".
Definition v_re_invsqrt := "invsqrt_var".
Definition v_re_D1      := "D1_var".
Definition v_re_D2      := "D2_var".
Definition v_re_D1D2    := "D1D2_var".
Definition v_re_Zinv    := "Zinv_var".
Definition v_re_ix      := "ix_var".
Definition v_re_iy      := "iy_var".
Definition v_re_eden    := "eden_var".
Definition v_re_tZinv   := "tZinv_var".
Definition v_re_xp      := "xp_var".
Definition v_re_yp      := "yp_var".
Definition v_re_deninv  := "deninv_var".
Definition v_re_xzinv   := "xzinv_var".
Definition v_re_ypp     := "ypp_var".
Definition v_re_ypneg   := "ypneg_var".
Definition v_re_zmypp   := "zmypp_var".
Definition v_re_sraw    := "sraw_var".
Definition v_re_sneg    := "sneg_var".
Definition v_re_s       := "s_var".
(* scalar slots for the is_negative tests *)
Definition v_re_rotbit  := "rotbit_s".
Definition v_re_xzbit   := "xzbit_s".
Definition v_re_sbit    := "sbit_s".

(* ========================================================================
   Section 5: The encoder AST.

   Step-for-step against [ristretto_encode_gallina_nlet]:

     unpack_xyzt5(xyzt) -> (x, y, z, ta, tb)
     one, p, sqrtm1, invad := REdSetBytes constants
     zinv  := fe25519_inv z                  (= z^(p-2))
     tatb  := fe25519_mul ta tb
     t     := fe25519_mul tatb zinv          (= extended_T ta tb z)
     zpy   := fe25519_add z y
     zmy   := fe25519_sub z y
     u1    := fe25519_mul zpy zmy            (= (z+y)(z-y))
     u2    := fe25519_mul x y
     u2sq  := fe25519_sq  u2
     den   := fe25519_mul u1 u2sq
     (ws, invsqrt) := sqrt_ratio_m1(one, den)
     D1    := fe25519_mul invsqrt u1
     D2    := fe25519_mul invsqrt u2
     D1D2  := fe25519_mul D1 D2
     Zinv  := fe25519_mul D1D2 t
     ix    := fe25519_mul x sqrtm1
     iy    := fe25519_mul y sqrtm1
     eden  := fe25519_mul D1 invad
     tZinv := fe25519_mul t Zinv
     rotbit := bit0(tZinv)
     xp     := select rotbit ? iy : x
     yp     := select rotbit ? ix : y
     deninv := select rotbit ? eden : D2
     xzinv  := fe25519_mul xp Zinv
     xzbit  := bit0(xzinv)
     ypneg  := fe25519_sub p yp              (= canonical_negate yp)
     ypp    := select xzbit ? ypneg : yp
     zmypp  := fe25519_sub z ypp
     sraw   := fe25519_mul deninv zmypp
     sbit   := bit0(sraw)
     sneg   := fe25519_sub p sraw            (= canonical_negate sraw)
     s      := select sbit ? sneg : sraw
     out    := ristretto_pack_canonical_felem s
   ======================================================================== *)
Definition ristretto_encode_rs : rust_cmd_ed :=
  REdLetZero v_re_x       (TBytes 32) (
  REdLetZero v_re_y       (TBytes 32) (
  REdLetZero v_re_z       (TBytes 32) (
  REdLetZero v_re_ta      (TBytes 32) (
  REdLetZero v_re_tb      (TBytes 32) (
  REdLetZero v_re_one     (TBytes 32) (
  REdLetZero v_re_p       (TBytes 32) (
  REdLetZero v_re_sqrtm1  (TBytes 32) (
  REdLetZero v_re_invad   (TBytes 32) (
  REdLetZero v_re_zinv    (TBytes 32) (
  REdLetZero v_re_tatb    (TBytes 32) (
  REdLetZero v_re_t       (TBytes 32) (
  REdLetZero v_re_zpy     (TBytes 32) (
  REdLetZero v_re_zmy     (TBytes 32) (
  REdLetZero v_re_u1      (TBytes 32) (
  REdLetZero v_re_u2      (TBytes 32) (
  REdLetZero v_re_u2sq    (TBytes 32) (
  REdLetZero v_re_den     (TBytes 32) (
  REdLetZero v_re_ws      (TBytes 1)  (
  REdLetZero v_re_invsqrt (TBytes 32) (
  REdLetZero v_re_D1      (TBytes 32) (
  REdLetZero v_re_D2      (TBytes 32) (
  REdLetZero v_re_D1D2    (TBytes 32) (
  REdLetZero v_re_Zinv    (TBytes 32) (
  REdLetZero v_re_ix      (TBytes 32) (
  REdLetZero v_re_iy      (TBytes 32) (
  REdLetZero v_re_eden    (TBytes 32) (
  REdLetZero v_re_tZinv   (TBytes 32) (
  REdLetZero v_re_xp      (TBytes 32) (
  REdLetZero v_re_yp      (TBytes 32) (
  REdLetZero v_re_deninv  (TBytes 32) (
  REdLetZero v_re_xzinv   (TBytes 32) (
  REdLetZero v_re_ypneg   (TBytes 32) (
  REdLetZero v_re_ypp     (TBytes 32) (
  REdLetZero v_re_zmypp   (TBytes 32) (
  REdLetZero v_re_sraw    (TBytes 32) (
  REdLetZero v_re_sneg    (TBytes 32) (
  REdLetZero v_re_s       (TBytes 32) (
  (* unpack 200-byte input -> 5 felems *)
  REdSeq (REdCallN "unpack_xyzt5"
            [LE_TBytes_r v_re_x  32; LE_TBytes_r v_re_y  32;
             LE_TBytes_r v_re_z  32; LE_TBytes_r v_re_ta 32;
             LE_TBytes_r v_re_tb 32]
            [LE_TBytes_r v_re_xyzt 32])
  (* constants *)
  (REdSeq (REdSetBytes (LE_TBytes_r v_re_one    32) const_one_zs)
  (REdSeq (REdSetBytes (LE_TBytes_r v_re_p      32) const_p_zs)
  (REdSeq (REdSetBytes (LE_TBytes_r v_re_sqrtm1 32) const_sqrt_m1_zs)
  (REdSeq (REdSetBytes (LE_TBytes_r v_re_invad  32) const_invsqrt_amd_zs)
  (* t = extended_T ta tb z = ta*tb*z^(p-2) *)
  (REdSeq (REdCall "fe25519_inv" (LE_TBytes_r v_re_zinv 32)
                                  [LE_TBytes_r v_re_z 32])
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_tatb 32)
                                  [LE_TBytes_r v_re_ta 32; LE_TBytes_r v_re_tb 32])
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_t 32)
                                  [LE_TBytes_r v_re_tatb 32; LE_TBytes_r v_re_zinv 32])
  (* u1 = (z+y)*(z-y) *)
  (REdSeq (REdCall "fe25519_add" (LE_TBytes_r v_re_zpy 32)
                                  [LE_TBytes_r v_re_z 32; LE_TBytes_r v_re_y 32])
  (REdSeq (REdCall "fe25519_sub" (LE_TBytes_r v_re_zmy 32)
                                  [LE_TBytes_r v_re_z 32; LE_TBytes_r v_re_y 32])
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_u1 32)
                                  [LE_TBytes_r v_re_zpy 32; LE_TBytes_r v_re_zmy 32])
  (* u2 = x*y *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_u2 32)
                                  [LE_TBytes_r v_re_x 32; LE_TBytes_r v_re_y 32])
  (* u2_sq = u2*u2 *)
  (REdSeq (REdCall "fe25519_sq" (LE_TBytes_r v_re_u2sq 32)
                                 [LE_TBytes_r v_re_u2 32])
  (* den = u1*u2_sq *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_den 32)
                                  [LE_TBytes_r v_re_u1 32; LE_TBytes_r v_re_u2sq 32])
  (* (ws, invsqrt) = sqrt_ratio_m1(one, den) *)
  (REdSeq (REdCallN "ristretto_sqrt_ratio_m1"
            [LE_TBytes_r v_re_ws 1; LE_TBytes_r v_re_invsqrt 32]
            [LE_TBytes_r v_re_one 32; LE_TBytes_r v_re_den 32])
  (* D1 = invsqrt*u1 *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_D1 32)
                                  [LE_TBytes_r v_re_invsqrt 32; LE_TBytes_r v_re_u1 32])
  (* D2 = invsqrt*u2 *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_D2 32)
                                  [LE_TBytes_r v_re_invsqrt 32; LE_TBytes_r v_re_u2 32])
  (* D1D2 = D1*D2 *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_D1D2 32)
                                  [LE_TBytes_r v_re_D1 32; LE_TBytes_r v_re_D2 32])
  (* Zinv = D1D2*t  (= D1*D2*t) *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_Zinv 32)
                                  [LE_TBytes_r v_re_D1D2 32; LE_TBytes_r v_re_t 32])
  (* ix = x*sqrtm1 *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_ix 32)
                                  [LE_TBytes_r v_re_x 32; LE_TBytes_r v_re_sqrtm1 32])
  (* iy = y*sqrtm1 *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_iy 32)
                                  [LE_TBytes_r v_re_y 32; LE_TBytes_r v_re_sqrtm1 32])
  (* eden = D1*invad *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_eden 32)
                                  [LE_TBytes_r v_re_D1 32; LE_TBytes_r v_re_invad 32])
  (* tZinv = t*Zinv *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_tZinv 32)
                                  [LE_TBytes_r v_re_t 32; LE_TBytes_r v_re_Zinv 32])
  (* rotate = bit0(tZinv) *)
  (REdSeq (REdByteLoad v_re_rotbit (LE_TBytes_r v_re_tZinv 32) (SLit 0))
  (* x' = rotate ? iy : x *)
  (REdSeq (REdSelect (SAnd (SVar v_re_rotbit) (SLit 1))
             (LE_TBytes_r v_re_iy 32) (LE_TBytes_r v_re_x 32) (LE_TBytes_r v_re_xp 32))
  (* y' = rotate ? ix : y *)
  (REdSeq (REdSelect (SAnd (SVar v_re_rotbit) (SLit 1))
             (LE_TBytes_r v_re_ix 32) (LE_TBytes_r v_re_y 32) (LE_TBytes_r v_re_yp 32))
  (* den_inv = rotate ? eden : D2 *)
  (REdSeq (REdSelect (SAnd (SVar v_re_rotbit) (SLit 1))
             (LE_TBytes_r v_re_eden 32) (LE_TBytes_r v_re_D2 32) (LE_TBytes_r v_re_deninv 32))
  (* x_z_inv = x'*Zinv *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_xzinv 32)
                                  [LE_TBytes_r v_re_xp 32; LE_TBytes_r v_re_Zinv 32])
  (* yp_neg = p - y' *)
  (REdSeq (REdCall "fe25519_sub" (LE_TBytes_r v_re_ypneg 32)
                                  [LE_TBytes_r v_re_p 32; LE_TBytes_r v_re_yp 32])
  (* xzbit = bit0(x_z_inv) *)
  (REdSeq (REdByteLoad v_re_xzbit (LE_TBytes_r v_re_xzinv 32) (SLit 0))
  (* y'' = is_negative(x_z_inv) ? -y' : y' *)
  (REdSeq (REdSelect (SAnd (SVar v_re_xzbit) (SLit 1))
             (LE_TBytes_r v_re_ypneg 32) (LE_TBytes_r v_re_yp 32) (LE_TBytes_r v_re_ypp 32))
  (* z - y'' *)
  (REdSeq (REdCall "fe25519_sub" (LE_TBytes_r v_re_zmypp 32)
                                  [LE_TBytes_r v_re_z 32; LE_TBytes_r v_re_ypp 32])
  (* s_raw = den_inv*(z - y'') *)
  (REdSeq (REdCall "fe25519_mul" (LE_TBytes_r v_re_sraw 32)
                                  [LE_TBytes_r v_re_deninv 32; LE_TBytes_r v_re_zmypp 32])
  (* s_neg = p - s_raw *)
  (REdSeq (REdCall "fe25519_sub" (LE_TBytes_r v_re_sneg 32)
                                  [LE_TBytes_r v_re_p 32; LE_TBytes_r v_re_sraw 32])
  (* sbit = bit0(s_raw) *)
  (REdSeq (REdByteLoad v_re_sbit (LE_TBytes_r v_re_sraw 32) (SLit 0))
  (* s = is_negative(s_raw) ? -s_raw : s_raw *)
  (REdSeq (REdSelect (SAnd (SVar v_re_sbit) (SLit 1))
             (LE_TBytes_r v_re_sneg 32) (LE_TBytes_r v_re_sraw 32) (LE_TBytes_r v_re_s 32))
  (* out = pack_canonical(s) *)
  (REdCall "ristretto_pack_canonical_felem" (LE_TBytes_r v_re_out 32)
           [LE_TBytes_r v_re_s 32])
  )))))))))))))))))))))))))))))))))
  )))))))))))))))))))))))))))))))))))))))).

(* ========================================================================
   Section 6: [spec_of_ed] instance.
   ======================================================================== *)

(** Slot precondition: caller-supplied "xyzt_var" holds the 200-byte
    input.  Slot postcondition: "out_var" holds the 32-byte encoding,
    equal to [ristretto_encode_gallina_nlet xyzt]. *)
Instance spec_of_ed_ristretto_encode : spec_of_ed "ristretto_encode" :=
  fnspec_ed! "ristretto_encode" (xyzt : list Byte.byte) ~> out,
  { requires rs := slot_holds rs "xyzt_var" xyzt;
    ensures  rs' := slot_holds rs' "out_var" out /\
                    out = ristretto_encode_gallina_nlet xyzt }.
