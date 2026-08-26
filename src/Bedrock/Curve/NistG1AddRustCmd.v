(** * NistG1AddRustCmd — verified-AST safe-Rust emission of NIST P-curve
 *    G1 point addition (P-224 / P-256 / P-384 / P-521).
 *
 *  One curve-generic [rust_cmd_ed] body implements the complete
 *  projective addition of Renes–Costello–Batina 2015 for general a≠0
 *  (40 field operations), in SSA form (every call writes a fresh slot,
 *  so [borrow_ok_ed] holds and the emitted Rust respects &mut aliasing
 *  rules without raw-pointer tricks at the leaf boundary).
 *
 *  The op sequence is the same dataflow as the Qed-proved bedrock2
 *  function [P256_G1_add] in [P256_G1_Add_Spec.v] (its 40 field-op
 *  calls, steps S1–S40 in the comments below), rewritten to fresh
 *  destinations.  The bedrock2 in-place buffer reuse (e.g.
 *  [$mul (t3, t3, t4)]) is replaced by new slots; the value computed
 *  at each step is unchanged.
 *
 *  Point ABI: a projective point is one [TBytes (3*fbytes)] buffer
 *  holding X ‖ Y ‖ Z, each felem being [fbytes] bytes in the curve's
 *  leaf representation:
 *    - P-224 / P-256:  32 bytes = 4×u64 LE Montgomery limbs
 *    - P-384:          48 bytes = 6×u64 LE Montgomery limbs
 *    - P-521:          66 bytes = canonical LE bytes (Solinas; the
 *                      leaf shims do from_bytes/op/to_bytes)
 *  The a and 3b curve constants are baked in via [REdSetBytes] in the
 *  same representation ((v·R) mod m for the Montgomery curves, plain
 *  canonical bytes for P-521), computed below by [vm_compute] from
 *  the curve equation constants.
 *
 *  Trust chain: [borrow_ok_ed] (reflexivity, below) + the rust_cmd_ed
 *  printer simulation ([RustCmdToRustSimulates.print_module_preserves_
 *  semantics] / the single [RustcExec_correct] axiom) + per-leaf
 *  contracts discharged by fiat-crypto's verified field ops in each
 *  crate.  The functional correctness of the 40-op dataflow against
 *  the Gallina RCB spec is inherited step-for-step from
 *  [P256_G1_add_func_ok]; a self-contained rhoare proof in the
 *  [callees_honoured] style of [XyztAddBodyDecomposed.v] is the
 *  designated follow-up.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.SafeRustEd25519BorrowCheck.
Require Import Bedrock.RustCmdToRust.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0. Little-endian byte serialization of Z constants               *)
(* ================================================================ *)

Fixpoint z_le_bytes (len : nat) (z : Z) : list Z :=
  match len with
  | O => []
  | S k => Z.land z 255 :: z_le_bytes k (Z.shiftr z 8)
  end.

Lemma z_le_bytes_length : forall len z, length (z_le_bytes len z) = len.
Proof. induction len; intros; simpl; congruence. Qed.

(* ================================================================ *)
(* §1. The curve-generic SSA body                                    *)
(* ================================================================ *)

Section NistG1Add.

  (** Felem byte size and the three leaf names. *)
  Context (fbytes : nat).
  Context (mul_name add_name sub_name : string).
  (** Curve constants, in leaf representation, [fbytes] bytes each. *)
  Context (a_bytes threeb_bytes : list Z).

  Local Definition FEL (v : string) : located_ed :=
    {| loc_var := v; loc_type := TBytes fbytes |}.

  Local Definition CMul (d a b : string) : rust_cmd_ed :=
    REdCall mul_name (FEL d) [FEL a; FEL b].
  Local Definition CAdd (d a b : string) : rust_cmd_ed :=
    REdCall add_name (FEL d) [FEL a; FEL b].
  Local Definition CSub (d a b : string) : rust_cmd_ed :=
    REdCall sub_name (FEL d) [FEL a; FEL b].

  Fixpoint seq_all (l : list rust_cmd_ed) : rust_cmd_ed :=
    match l with
    | [] => REdSkip
    | [c] => c
    | c :: r => REdSeq c (seq_all r)
    end.

  (** Copy [fbytes] bytes from [src] at offset [off] into felem slot
      [dst] (offset 0). *)
  Local Definition unpack1 (dst : string) (src : located_ed) (off : nat)
    : rust_cmd_ed :=
    REdFor "i" fbytes
      (REdSeq
        (REdByteLoad "bv" src (SAdd (SVar "i") (SLit (Z.of_nat off))))
        (REdByteStore (FEL dst) (SVar "i") (SVar "bv"))).

  (** Copy felem slot [src] into [dst] at offset [off]. *)
  Local Definition pack1 (dst : located_ed) (src : string) (off : nat)
    : rust_cmd_ed :=
    REdFor "i" fbytes
      (REdSeq
        (REdByteLoad "bv" (FEL src) (SVar "i"))
        (REdByteStore dst (SAdd (SVar "i") (SLit (Z.of_nat off))) (SVar "bv"))).

  (** All felem scratch slots used by the SSA chain. *)
  Local Definition slot_names : list string :=
    ["X1"; "Y1"; "Z1"; "X2"; "Y2"; "Z2"; "cA"; "cB3";
     "t0"; "t1"; "t2";
     "m1"; "m2"; "m3"; "m4"; "t3f";
     "m5"; "m6"; "m7"; "m8"; "t4m";
     "m9"; "m10"; "m11"; "m12"; "t5f";
     "za"; "zb"; "zc"; "xv"; "zv"; "yv";
     "d1"; "d2"; "v1"; "w2"; "ta"; "v2"; "v3"; "w3";
     "q1"; "q2"; "q3"; "x2"; "z4"; "X3"; "Y3"; "Z3"].

  Fixpoint let_slots (ns : list string) (body : rust_cmd_ed) : rust_cmd_ed :=
    match ns with
    | [] => body
    | n :: r => REdLetZero n (TBytes fbytes) (let_slots r body)
    end.

  (** The 40-op RCB general-a complete addition, SSA form.
      Sn markers reference the bedrock2 [P256_G1_add] step numbers. *)
  Local Definition rcb_ops : list rust_cmd_ed :=
    [ CMul "t0" "X1" "X2"        (* S1  t0 = X1·X2 *)
    ; CMul "t1" "Y1" "Y2"        (* S2  t1 = Y1·Y2 *)
    ; CMul "t2" "Z1" "Z2"        (* S3  t2 = Z1·Z2 *)
    ; CAdd "m1" "X1" "Y1"        (* S4 *)
    ; CAdd "m2" "X2" "Y2"        (* S5 *)
    ; CMul "m3" "m1" "m2"        (* S6 *)
    ; CAdd "m4" "t0" "t1"        (* S7 *)
    ; CSub "t3f" "m3" "m4"       (* S8  t3f = (X1+Y1)(X2+Y2) − t0 − t1 *)
    ; CAdd "m5" "X1" "Z1"        (* S9 *)
    ; CAdd "m6" "X2" "Z2"        (* S10 *)
    ; CMul "m7" "m5" "m6"        (* S11 *)
    ; CAdd "m8" "t0" "t2"        (* S12 *)
    ; CSub "t4m" "m7" "m8"       (* S13 t4m = (X1+Z1)(X2+Z2) − t0 − t2 *)
    ; CAdd "m9" "Y1" "Z1"        (* S14 *)
    ; CAdd "m10" "Y2" "Z2"       (* S15 *)
    ; CMul "m11" "m9" "m10"      (* S16 *)
    ; CAdd "m12" "t1" "t2"       (* S17 *)
    ; CSub "t5f" "m11" "m12"     (* S18 t5f = (Y1+Z1)(Y2+Z2) − t1 − t2 *)
    ; CMul "za" "cA" "t4m"       (* S19 za = a·t4m *)
    ; CMul "zb" "cB3" "t2"       (* S20 zb = 3b·t2 *)
    ; CAdd "zc" "zb" "za"        (* S21 zc = zb + za *)
    ; CSub "xv" "t1" "zc"        (* S22 xv = t1 − zc *)
    ; CAdd "zv" "zc" "t1"        (* S23 zv = zc + t1 *)
    ; CMul "yv" "xv" "zv"        (* S24 yv = xv·zv *)
    ; CAdd "d1" "t0" "t0"        (* S25 *)
    ; CAdd "d2" "d1" "t0"        (* S26 d2 = 3·t0 *)
    ; CMul "v1" "cA" "t2"        (* S27 v1 = a·t2 *)
    ; CMul "w2" "cB3" "t4m"      (* S28 w2 = 3b·t4m *)
    ; CAdd "ta" "d2" "v1"        (* S29 ta = 3t0 + a·t2 *)
    ; CSub "v2" "t0" "v1"        (* S30 v2 = t0 − a·t2 *)
    ; CMul "v3" "cA" "v2"        (* S31 v3 = a·v2 *)
    ; CAdd "w3" "w2" "v3"        (* S32 w3 = w2 + v3 *)
    ; CMul "q1" "ta" "w3"        (* S33 *)
    ; CAdd "Y3" "yv" "q1"        (* S34 Y3 = yv + ta·w3 *)
    ; CMul "q2" "t5f" "w3"       (* S35 *)
    ; CMul "x2" "t3f" "xv"       (* S36 *)
    ; CSub "X3" "x2" "q2"        (* S37 X3 = t3f·xv − t5f·w3 *)
    ; CMul "q3" "t3f" "ta"       (* S38 *)
    ; CMul "z4" "t5f" "zv"       (* S39 *)
    ; CAdd "Z3" "z4" "q3"        (* S40 Z3 = t5f·zv + t3f·ta *)
    ].

  (** The full body: allocate slots, unpack both points, set constants,
      run the 40 ops, pack the result. *)
  Definition nist_g1_add_body : function_body_ed :=
    fun dest args =>
      match args with
      | [P1; P2] =>
          let_slots slot_names
            (seq_all
              ([ unpack1 "X1" P1 0
               ; unpack1 "Y1" P1 fbytes
               ; unpack1 "Z1" P1 (2 * fbytes)
               ; unpack1 "X2" P2 0
               ; unpack1 "Y2" P2 fbytes
               ; unpack1 "Z2" P2 (2 * fbytes)
               ; REdSetBytes (FEL "cA") a_bytes
               ; REdSetBytes (FEL "cB3") threeb_bytes
               ]
               ++ rcb_ops
               ++ [ pack1 dest "X3" 0
                  ; pack1 dest "Y3" fbytes
                  ; pack1 dest "Z3" (2 * fbytes)
                  ]))
      | _ => REdSkip
      end.

End NistG1Add.

(* ================================================================ *)
(* §2. Curve constants                                               *)
(* ================================================================ *)

(** Base-field primes. *)
Definition p224_m : Z := Eval vm_compute in (2^224 - 2^96 + 1).
Definition p256_m : Z :=
  Eval vm_compute in (2^256 - 2^224 + 2^192 + 2^96 - 1).
Definition p384_m : Z :=
  Eval vm_compute in (2^384 - 2^128 - 2^96 + 2^32 - 1).
Definition p521_m : Z := Eval vm_compute in (2^521 - 1).

(** Curve b coefficients (FIPS 186-4 / SEC 2; the P-256 value equals
    [b_val] in [P256_G1_Add_Spec.v], and each value is byte-identical
    to the test-validated constant in the corresponding
    [p*-safe-rust/src/group.rs]). *)
Definition p224_b : Z :=
  0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4.
Definition p256_b : Z :=
  0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b.
Definition p384_b : Z :=
  0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef.
Definition p521_b : Z :=
  0x0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00.

(** Montgomery encodings: value · 2^(64·limbs) mod m, serialized to
    LE limb bytes.  P-521 uses plain canonical bytes (no Montgomery). *)
Definition mont_bytes (limbs : nat) (m v : Z) : list Z :=
  z_le_bytes (limbs * 8) ((v * 2^(64 * Z.of_nat limbs)) mod m).

Definition p224_a_bytes : list Z :=
  Eval vm_compute in mont_bytes 4 p224_m (p224_m - 3).
Definition p224_threeb_bytes : list Z :=
  Eval vm_compute in mont_bytes 4 p224_m ((3 * p224_b) mod p224_m).

Definition p256_a_bytes : list Z :=
  Eval vm_compute in mont_bytes 4 p256_m (p256_m - 3).
Definition p256_threeb_bytes : list Z :=
  Eval vm_compute in mont_bytes 4 p256_m ((3 * p256_b) mod p256_m).

Definition p384_a_bytes : list Z :=
  Eval vm_compute in mont_bytes 6 p384_m (p384_m - 3).
Definition p384_threeb_bytes : list Z :=
  Eval vm_compute in mont_bytes 6 p384_m ((3 * p384_b) mod p384_m).

Definition p521_a_bytes : list Z :=
  Eval vm_compute in z_le_bytes 66 (p521_m - 3).
Definition p521_threeb_bytes : list Z :=
  Eval vm_compute in z_le_bytes 66 ((3 * p521_b) mod p521_m).

(* ================================================================ *)
(* §3. Per-curve bodies + borrow-check certificates                  *)
(* ================================================================ *)

Definition p224_g1_add_body : function_body_ed :=
  nist_g1_add_body 32 "p224_fp_mul" "p224_fp_add" "p224_fp_sub"
                   p224_a_bytes p224_threeb_bytes.
Definition p256_g1_add_body : function_body_ed :=
  nist_g1_add_body 32 "p256_fp_mul" "p256_fp_add" "p256_fp_sub"
                   p256_a_bytes p256_threeb_bytes.
Definition p384_g1_add_body : function_body_ed :=
  nist_g1_add_body 48 "p384_fp_mul" "p384_fp_add" "p384_fp_sub"
                   p384_a_bytes p384_threeb_bytes.
Definition p521_g1_add_body : function_body_ed :=
  nist_g1_add_body 66 "p521_fp_mul" "p521_fp_add" "p521_fp_sub"
                   p521_a_bytes p521_threeb_bytes.

(** Sentinel locators matching [rs_body_extract]. *)
Definition pt_loc (n : nat) (v : string) : located_ed :=
  {| loc_var := v; loc_type := TBytes (3 * n) |}.

Example p224_g1_add_borrow_ok :
  borrow_ok_ed (p224_g1_add_body (pt_loc 32 "out")
                 [pt_loc 32 "arg0"; pt_loc 32 "arg1"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p256_g1_add_borrow_ok :
  borrow_ok_ed (p256_g1_add_body (pt_loc 32 "out")
                 [pt_loc 32 "arg0"; pt_loc 32 "arg1"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p384_g1_add_borrow_ok :
  borrow_ok_ed (p384_g1_add_body (pt_loc 48 "out")
                 [pt_loc 48 "arg0"; pt_loc 48 "arg1"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p521_g1_add_borrow_ok :
  borrow_ok_ed (p521_g1_add_body (pt_loc 66 "out")
                 [pt_loc 66 "arg0"; pt_loc 66 "arg1"]) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §4. Rust emission                                                 *)
(* ================================================================ *)

Definition p224_g1_add_rs : string :=
  rs_body_extract
    {| bes_name := "p224_g1_add_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96; TBytes 96];
       bes_body := p224_g1_add_body |}.

Definition p256_g1_add_rs : string :=
  rs_body_extract
    {| bes_name := "p256_g1_add_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96; TBytes 96];
       bes_body := p256_g1_add_body |}.

Definition p384_g1_add_rs : string :=
  rs_body_extract
    {| bes_name := "p384_g1_add_extracted";
       bes_dest_type := TBytes 144;
       bes_arg_types := [TBytes 144; TBytes 144];
       bes_body := p384_g1_add_body |}.

Definition p521_g1_add_rs : string :=
  rs_body_extract
    {| bes_name := "p521_g1_add_extracted";
       bes_dest_type := TBytes 198;
       bes_arg_types := [TBytes 198; TBytes 198];
       bes_body := p521_g1_add_body |}.

(** Emission: evaluate [Eval vm_compute in pXXX_g1_add_rs] (e.g. via
    rocq_query or a Redirect in a local driver file) and drop the
    resulting string into [pXXX-safe-rust/src/g1_add_extracted.rs]. *)
