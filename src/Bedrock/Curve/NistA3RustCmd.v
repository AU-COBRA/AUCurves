(** * NistA3RustCmd — verified-AST safe-Rust emission of the a = -3
 *    specialised NIST P-curve G1 point operations
 *    (P-224 / P-256 / P-384 / P-521).
 *
 *  Companion of [NistG1AddRustCmd.v], which emits the general-a
 *  Renes–Costello–Batina Algorithm 1 addition (40 ops, two stack
 *  constants a and 3b).  Every NIST prime curve has a = -3, so the
 *  specialised algorithms apply:
 *
 *    Algorithm 4 (addition, this file's [a3_add_ops])
 *        43 ops = 12 M + 2 m_b + 29 add/sub  (14 multiplications)
 *    Algorithm 6 (doubling, this file's [a3_dbl_ops])
 *        34 ops = 11 M + 2 m_b + 21 add/sub  (13 multiplications)
 *
 *  against 40 ops / 17 multiplications for the general-a addition, and
 *  a doubling the crates otherwise obtain as [g1_add(p, p)], i.e. at
 *  the full 40-op addition cost.  Three multiplications are
 *  traded for six additions in the addition; the doubling is a strict
 *  saving.  Only ONE curve constant is baked in ([cB] = b in the leaf
 *  representation), where the general-a body bakes in two.
 *
 *  Provenance of the op sequences: the Rupicola derivations
 *    [CurveAddA3.rcb_add_a3_gallina]      (steps A1–A43)
 *    [CurveDoubleA3.rcb_double_a3_gallina] (steps E1–E34)
 *  rewritten to SSA form (every call writes a fresh slot, so
 *  [borrow_ok_ed] holds by computation and the emitted Rust respects
 *  &mut aliasing without raw-pointer tricks above the leaf boundary).
 *  The paper's in-place buffer reuse (e.g. [outx := outx +F outz]) is
 *  replaced by new slots; the value computed at each step is unchanged.
 *  [CurveA3Equiv.v] proves both chains equal to the corresponding
 *  general-a chains at a = -3 as polynomial identities, so the
 *  correctness, the [RcbProjectiveLaws] group laws and the wNAF
 *  instances transfer unchanged.
 *
 *  Point ABI, felem sizes, Montgomery encoding of the constant and the
 *  trust chain are exactly as documented in the header of
 *  [NistG1AddRustCmd.v]; this file reuses that file's [z_le_bytes],
 *  [mont_bytes], the base-field primes and the curve b coefficients.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.SafeRustEd25519BorrowCheck.
Require Import Bedrock.RustCmdToRust.
Require Import Bedrock.Curve.NistG1AddRustCmd.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. The curve-generic SSA bodies                                  *)
(* ================================================================ *)

Section NistA3.

  (** Felem byte size and the three leaf names. *)
  Context (fbytes : nat).
  Context (mul_name add_name sub_name : string).
  (** The single curve constant b, in leaf representation,
      [fbytes] bytes. *)
  Context (b_bytes : list Z).

  Local Definition A3FEL (v : string) : located_ed :=
    {| loc_var := v; loc_type := TBytes fbytes |}.

  Local Definition A3Mul (d a b : string) : rust_cmd_ed :=
    REdCall mul_name (A3FEL d) [A3FEL a; A3FEL b].
  Local Definition A3Add (d a b : string) : rust_cmd_ed :=
    REdCall add_name (A3FEL d) [A3FEL a; A3FEL b].
  Local Definition A3Sub (d a b : string) : rust_cmd_ed :=
    REdCall sub_name (A3FEL d) [A3FEL a; A3FEL b].

  Fixpoint a3_seq_all (l : list rust_cmd_ed) : rust_cmd_ed :=
    match l with
    | [] => REdSkip
    | [c] => c
    | c :: r => REdSeq c (a3_seq_all r)
    end.

  (** Copy [fbytes] bytes from [src] at offset [off] into felem slot
      [dst] (offset 0). *)
  Local Definition a3_unpack1 (dst : string) (src : located_ed) (off : nat)
    : rust_cmd_ed :=
    REdFor "i" fbytes
      (REdSeq
        (REdByteLoad "bv" src (SAdd (SVar "i") (SLit (Z.of_nat off))))
        (REdByteStore (A3FEL dst) (SVar "i") (SVar "bv"))).

  (** Copy felem slot [src] into [dst] at offset [off]. *)
  Local Definition a3_pack1 (dst : located_ed) (src : string) (off : nat)
    : rust_cmd_ed :=
    REdFor "i" fbytes
      (REdSeq
        (REdByteLoad "bv" (A3FEL src) (SVar "i"))
        (REdByteStore dst (SAdd (SVar "i") (SLit (Z.of_nat off))) (SVar "bv"))).

  Fixpoint a3_let_slots (ns : list string) (body : rust_cmd_ed) : rust_cmd_ed :=
    match ns with
    | [] => body
    | n :: r => REdLetZero n (TBytes fbytes) (a3_let_slots r body)
    end.

  (* ---------------------------------------------------------------- *)
  (* §1a. Algorithm 4 — complete addition at a = -3, 43 ops            *)
  (* ---------------------------------------------------------------- *)

  Local Definition a3_add_slots : list string :=
    ["X1"; "Y1"; "Z1"; "X2"; "Y2"; "Z2"; "cB";
     "t0"; "t1"; "t2";
     "m1"; "m2"; "m3"; "m4"; "t3f";
     "m5"; "m6"; "m7"; "m8"; "t4m";
     "m9"; "m10"; "m11"; "m12"; "xz";
     "bz"; "u0"; "u1"; "wv"; "uu"; "vv"; "bx";
     "z2a"; "z3b"; "s0"; "s1"; "s2"; "s3";
     "x2a"; "x3b"; "dd";
     "p1"; "p2"; "p3"; "p4"; "p5"; "p6";
     "X3"; "Y3"; "Z3"].

  (** The A-markers are the line numbers of RCB 2015 Algorithm 4 and the
      step names of [CurveAddA3.rcb_add_a3_gallina].  Where a step ends a
      group, the comment names the paper temporary the SSA slot holds. *)
  Local Definition a3_add_ops : list rust_cmd_ed :=
    [ A3Mul "t0" "X1" "X2"        (* A1  t0 = X1X2 *)
    ; A3Mul "t1" "Y1" "Y2"        (* A2  t1 = Y1Y2 *)
    ; A3Mul "t2" "Z1" "Z2"        (* A3  t2 = Z1Z2 *)
    ; A3Add "m1" "X1" "Y1"        (* A4 *)
    ; A3Add "m2" "X2" "Y2"        (* A5 *)
    ; A3Mul "m3" "m1" "m2"        (* A6 *)
    ; A3Add "m4" "t0" "t1"        (* A7 *)
    ; A3Sub "t3f" "m3" "m4"       (* A8  t3 = X1Y2 + Y1X2 *)
    ; A3Add "m5" "Y1" "Z1"        (* A9 *)
    ; A3Add "m6" "Y2" "Z2"        (* A10 *)
    ; A3Mul "m7" "m5" "m6"        (* A11 *)
    ; A3Add "m8" "t1" "t2"        (* A12 *)
    ; A3Sub "t4m" "m7" "m8"       (* A13 t4 = Y1Z2 + Z1Y2 *)
    ; A3Add "m9" "X1" "Z1"        (* A14 *)
    ; A3Add "m10" "X2" "Z2"       (* A15 *)
    ; A3Mul "m11" "m9" "m10"      (* A16 *)
    ; A3Add "m12" "t0" "t2"       (* A17 *)
    ; A3Sub "xz" "m11" "m12"      (* A18 outy = X1Z2 + Z1X2 *)
    ; A3Mul "bz" "cB" "t2"        (* A19 outz = b*Z1Z2 *)
    ; A3Sub "u0" "xz" "bz"        (* A20 *)
    ; A3Add "u1" "u0" "u0"        (* A21 *)
    ; A3Add "wv" "u0" "u1"        (* A22 outx = 3(xz - b*zz) *)
    ; A3Sub "uu" "t1" "wv"        (* A23 outz = yy - 3(xz - b*zz) *)
    ; A3Add "vv" "t1" "wv"        (* A24 outx = yy + 3(xz - b*zz) *)
    ; A3Mul "bx" "cB" "xz"        (* A25 outy = b*xz *)
    ; A3Add "z2a" "t2" "t2"       (* A26 *)
    ; A3Add "z3b" "z2a" "t2"      (* A27 t2 = 3*zz *)
    ; A3Sub "s0" "bx" "z3b"       (* A28 *)
    ; A3Sub "s1" "s0" "t0"        (* A29 outy = b*xz - 3zz - xx *)
    ; A3Add "s2" "s1" "s1"        (* A30 *)
    ; A3Add "s3" "s2" "s1"        (* A31 outy = 3(b*xz - 3zz - xx) *)
    ; A3Add "x2a" "t0" "t0"       (* A32 *)
    ; A3Add "x3b" "x2a" "t0"      (* A33 t0 = 3*xx *)
    ; A3Sub "dd" "x3b" "z3b"      (* A34 t0 = 3xx - 3zz *)
    ; A3Mul "p1" "t4m" "s3"       (* A35 *)
    ; A3Mul "p2" "dd" "s3"        (* A36 *)
    ; A3Mul "p3" "vv" "uu"        (* A37 *)
    ; A3Add "Y3" "p3" "p2"        (* A38 Y3 *)
    ; A3Mul "p4" "t3f" "vv"       (* A39 *)
    ; A3Sub "X3" "p4" "p1"        (* A40 X3 *)
    ; A3Mul "p5" "t4m" "uu"       (* A41 *)
    ; A3Mul "p6" "t3f" "dd"       (* A42 *)
    ; A3Add "Z3" "p5" "p6"        (* A43 Z3 *)
    ].

  Definition nist_g1_add_a3_body : function_body_ed :=
    fun dest args =>
      match args with
      | [P1; P2] =>
          a3_let_slots a3_add_slots
            (a3_seq_all
              ([ a3_unpack1 "X1" P1 0
               ; a3_unpack1 "Y1" P1 fbytes
               ; a3_unpack1 "Z1" P1 (2 * fbytes)
               ; a3_unpack1 "X2" P2 0
               ; a3_unpack1 "Y2" P2 fbytes
               ; a3_unpack1 "Z2" P2 (2 * fbytes)
               ; REdSetBytes (A3FEL "cB") b_bytes
               ]
               ++ a3_add_ops
               ++ [ a3_pack1 dest "X3" 0
                  ; a3_pack1 dest "Y3" fbytes
                  ; a3_pack1 dest "Z3" (2 * fbytes)
                  ]))
      | _ => REdSkip
      end.

  (* ---------------------------------------------------------------- *)
  (* §1b. Algorithm 6 — complete doubling at a = -3, 34 ops            *)
  (* ---------------------------------------------------------------- *)

  Local Definition a3_dbl_slots : list string :=
    ["X1"; "Y1"; "Z1"; "cB";
     "t0"; "t1"; "t2"; "m1"; "t3"; "m2"; "zxz";
     "bz"; "y0"; "y1"; "y2"; "x0"; "y3v"; "y4"; "x1v";
     "z2a"; "z3b"; "bz2"; "w0"; "w1"; "w2"; "w3";
     "x2a"; "x3b"; "dd"; "p1";
     "m3"; "yz2"; "p2"; "p3"; "p4";
     "X3"; "Y3"; "Z3"].

  (** The E-markers are the line numbers of RCB 2015 Algorithm 6 and the
      step names of [CurveDoubleA3.rcb_double_a3_gallina].  Squarings
      are emitted as [mul_name x x]: the leaf ABI of the emitted crates
      exposes mul/add/sub only, and the general-a body already relies on
      that (its S25 [add t0 t0] passes one slot twice). *)
  Local Definition a3_dbl_ops : list rust_cmd_ed :=
    [ A3Mul "t0" "X1" "X1"        (* E1  t0 = X^2 *)
    ; A3Mul "t1" "Y1" "Y1"        (* E2  t1 = Y^2 *)
    ; A3Mul "t2" "Z1" "Z1"        (* E3  t2 = Z^2 *)
    ; A3Mul "m1" "X1" "Y1"        (* E4 *)
    ; A3Add "t3" "m1" "m1"        (* E5  t3 = 2XY *)
    ; A3Mul "m2" "X1" "Z1"        (* E6 *)
    ; A3Add "zxz" "m2" "m2"       (* E7  outz = 2XZ *)
    ; A3Mul "bz" "cB" "t2"        (* E8  outy = b*Z^2 *)
    ; A3Sub "y0" "bz" "zxz"       (* E9  outy = b*Z^2 - 2XZ *)
    ; A3Add "y1" "y0" "y0"        (* E10 *)
    ; A3Add "y2" "y1" "y0"        (* E11 outy = 3(bZ^2 - 2XZ) *)
    ; A3Sub "x0" "t1" "y2"        (* E12 outx = Y^2 - that *)
    ; A3Add "y3v" "t1" "y2"       (* E13 outy = Y^2 + that *)
    ; A3Mul "y4" "x0" "y3v"       (* E14 *)
    ; A3Mul "x1v" "x0" "t3"       (* E15 *)
    ; A3Add "z2a" "t2" "t2"       (* E16 *)
    ; A3Add "z3b" "t2" "z2a"      (* E17 t2 = 3Z^2 *)
    ; A3Mul "bz2" "cB" "zxz"      (* E18 outz = b*2XZ *)
    ; A3Sub "w0" "bz2" "z3b"      (* E19 *)
    ; A3Sub "w1" "w0" "t0"        (* E20 outz = b*2XZ - 3Z^2 - X^2 *)
    ; A3Add "w2" "w1" "w1"        (* E21 *)
    ; A3Add "w3" "w1" "w2"        (* E22 outz = 3*that *)
    ; A3Add "x2a" "t0" "t0"       (* E23 *)
    ; A3Add "x3b" "x2a" "t0"      (* E24 t0 = 3X^2 *)
    ; A3Sub "dd" "x3b" "z3b"      (* E25 t0 = 3X^2 - 3Z^2 *)
    ; A3Mul "p1" "dd" "w3"        (* E26 *)
    ; A3Add "Y3" "y4" "p1"        (* E27 Y3 *)
    ; A3Mul "m3" "Y1" "Z1"        (* E28 *)
    ; A3Add "yz2" "m3" "m3"       (* E29 t0 = 2YZ *)
    ; A3Mul "p2" "yz2" "w3"       (* E30 *)
    ; A3Sub "X3" "x1v" "p2"       (* E31 X3 *)
    ; A3Mul "p3" "yz2" "t1"       (* E32 outz = 2Y^3 Z *)
    ; A3Add "p4" "p3" "p3"        (* E33 *)
    ; A3Add "Z3" "p4" "p4"        (* E34 Z3 = 8Y^3 Z *)
    ].

  Definition nist_g1_double_a3_body : function_body_ed :=
    fun dest args =>
      match args with
      | [P1] =>
          a3_let_slots a3_dbl_slots
            (a3_seq_all
              ([ a3_unpack1 "X1" P1 0
               ; a3_unpack1 "Y1" P1 fbytes
               ; a3_unpack1 "Z1" P1 (2 * fbytes)
               ; REdSetBytes (A3FEL "cB") b_bytes
               ]
               ++ a3_dbl_ops
               ++ [ a3_pack1 dest "X3" 0
                  ; a3_pack1 dest "Y3" fbytes
                  ; a3_pack1 dest "Z3" (2 * fbytes)
                  ]))
      | _ => REdSkip
      end.

End NistA3.

(* ================================================================ *)
(* §2. The b constants                                               *)
(* ================================================================ *)

(** [mont_bytes], the primes and the b coefficients come from
    [NistG1AddRustCmd.v].  Each value below is byte-identical to the
    test-validated [B_MONT] literal of the corresponding
    [p*-safe-rust/src/group.rs], read as little-endian u64 limbs. *)

Definition p224_b_bytes : list Z :=
  Eval vm_compute in mont_bytes 4 p224_m p224_b.
Definition p256_b_bytes : list Z :=
  Eval vm_compute in mont_bytes 4 p256_m p256_b.
Definition p384_b_bytes : list Z :=
  Eval vm_compute in mont_bytes 6 p384_m p384_b.
Definition p521_b_bytes : list Z :=
  Eval vm_compute in z_le_bytes 66 (p521_b mod p521_m).

(* ================================================================ *)
(* §3. Per-curve bodies + borrow-check certificates                  *)
(* ================================================================ *)

Definition p224_g1_add_a3_body : function_body_ed :=
  nist_g1_add_a3_body 32 "p224_fp_mul" "p224_fp_add" "p224_fp_sub"
                      p224_b_bytes.
Definition p224_g1_double_a3_body : function_body_ed :=
  nist_g1_double_a3_body 32 "p224_fp_mul" "p224_fp_add" "p224_fp_sub"
                         p224_b_bytes.

Definition p256_g1_add_a3_body : function_body_ed :=
  nist_g1_add_a3_body 32 "p256_fp_mul" "p256_fp_add" "p256_fp_sub"
                      p256_b_bytes.
Definition p256_g1_double_a3_body : function_body_ed :=
  nist_g1_double_a3_body 32 "p256_fp_mul" "p256_fp_add" "p256_fp_sub"
                         p256_b_bytes.

Definition p384_g1_add_a3_body : function_body_ed :=
  nist_g1_add_a3_body 48 "p384_fp_mul" "p384_fp_add" "p384_fp_sub"
                      p384_b_bytes.
Definition p384_g1_double_a3_body : function_body_ed :=
  nist_g1_double_a3_body 48 "p384_fp_mul" "p384_fp_add" "p384_fp_sub"
                         p384_b_bytes.

Definition p521_g1_add_a3_body : function_body_ed :=
  nist_g1_add_a3_body 66 "p521_fp_mul" "p521_fp_add" "p521_fp_sub"
                      p521_b_bytes.
Definition p521_g1_double_a3_body : function_body_ed :=
  nist_g1_double_a3_body 66 "p521_fp_mul" "p521_fp_add" "p521_fp_sub"
                         p521_b_bytes.

(** [pt_loc] is the sentinel locator of [NistG1AddRustCmd.v], matching
    [rs_body_extract]. *)

Example p224_g1_add_a3_borrow_ok :
  borrow_ok_ed (p224_g1_add_a3_body (pt_loc 32 "out")
                 [pt_loc 32 "arg0"; pt_loc 32 "arg1"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p224_g1_double_a3_borrow_ok :
  borrow_ok_ed (p224_g1_double_a3_body (pt_loc 32 "out")
                 [pt_loc 32 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p256_g1_add_a3_borrow_ok :
  borrow_ok_ed (p256_g1_add_a3_body (pt_loc 32 "out")
                 [pt_loc 32 "arg0"; pt_loc 32 "arg1"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p256_g1_double_a3_borrow_ok :
  borrow_ok_ed (p256_g1_double_a3_body (pt_loc 32 "out")
                 [pt_loc 32 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p384_g1_add_a3_borrow_ok :
  borrow_ok_ed (p384_g1_add_a3_body (pt_loc 48 "out")
                 [pt_loc 48 "arg0"; pt_loc 48 "arg1"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p384_g1_double_a3_borrow_ok :
  borrow_ok_ed (p384_g1_double_a3_body (pt_loc 48 "out")
                 [pt_loc 48 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p521_g1_add_a3_borrow_ok :
  borrow_ok_ed (p521_g1_add_a3_body (pt_loc 66 "out")
                 [pt_loc 66 "arg0"; pt_loc 66 "arg1"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example p521_g1_double_a3_borrow_ok :
  borrow_ok_ed (p521_g1_double_a3_body (pt_loc 66 "out")
                 [pt_loc 66 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §4. Rust emission                                                 *)
(* ================================================================ *)

Definition p224_g1_add_a3_rs : string :=
  rs_body_extract
    {| bes_name := "p224_g1_add_a3_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96; TBytes 96];
       bes_body := p224_g1_add_a3_body |}.

Definition p224_g1_double_a3_rs : string :=
  rs_body_extract
    {| bes_name := "p224_g1_double_a3_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96];
       bes_body := p224_g1_double_a3_body |}.

Definition p256_g1_add_a3_rs : string :=
  rs_body_extract
    {| bes_name := "p256_g1_add_a3_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96; TBytes 96];
       bes_body := p256_g1_add_a3_body |}.

Definition p256_g1_double_a3_rs : string :=
  rs_body_extract
    {| bes_name := "p256_g1_double_a3_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96];
       bes_body := p256_g1_double_a3_body |}.

Definition p384_g1_add_a3_rs : string :=
  rs_body_extract
    {| bes_name := "p384_g1_add_a3_extracted";
       bes_dest_type := TBytes 144;
       bes_arg_types := [TBytes 144; TBytes 144];
       bes_body := p384_g1_add_a3_body |}.

Definition p384_g1_double_a3_rs : string :=
  rs_body_extract
    {| bes_name := "p384_g1_double_a3_extracted";
       bes_dest_type := TBytes 144;
       bes_arg_types := [TBytes 144];
       bes_body := p384_g1_double_a3_body |}.

Definition p521_g1_add_a3_rs : string :=
  rs_body_extract
    {| bes_name := "p521_g1_add_a3_extracted";
       bes_dest_type := TBytes 198;
       bes_arg_types := [TBytes 198; TBytes 198];
       bes_body := p521_g1_add_a3_body |}.

Definition p521_g1_double_a3_rs : string :=
  rs_body_extract
    {| bes_name := "p521_g1_double_a3_extracted";
       bes_dest_type := TBytes 198;
       bes_arg_types := [TBytes 198];
       bes_body := p521_g1_double_a3_body |}.

(** Emission: evaluate [Eval vm_compute in pXXX_g1_{add,double}_a3_rs]
    and concatenate the two strings into
    [pXXX-safe-rust/src/g1_a3_extracted.rs] under the fixed header of
    that file.  P-224 / P-256 / P-384 are shipped; P-521 is emitted here
    for parity with [NistG1AddRustCmd.v] but its crate has no
    [g1_a3_extracted.rs] module yet. *)
