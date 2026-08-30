(** * CurveDoubleA0RustCmd — verified-AST safe-Rust emission of the
 *    a = 0 specialised complete point DOUBLING (RCB 2015, Algorithm 9)
 *    for the pairing-friendly curves whose G1 has a = 0.
 *
 *  This is the a = 0 counterpart of [NistA3RustCmd.v]'s
 *  [a3_dbl_ops] (Algorithm 6, a = -3).  It stands to
 *  [CurveAdd.ladderstep_gallina] (Algorithm 7, the a = 0 complete
 *  addition) exactly as [a3_dbl_ops] stands to [CurveAddA3].
 *
 *  ** Op counts **
 *
 *    Algorithm 7 (a = 0, addition)  33 ops = 12 M + 2 m_3b + 19 add
 *                                          = 14 multiplications
 *    Algorithm 9 (a = 0, doubling)  18 ops =  8 M + 1 m_3b +  9 add
 *                                          =  9 multiplications
 *
 *  Fifteen operations and five multiplications saved against
 *  [g1_add(P, P)].  Measured on BW6-761 over the verified Fp leaves
 *  (`bw6-761-safe-rust/examples/bench_g1.rs`): doubling 3.2 us ->
 *  2.2 us, 377-bit scalar multiplication 2.0 ms -> 1.5 ms.
 *
 *  ** Provenance of the op sequence **
 *
 *  [PointDoubleA0.rcb_double_a0_gallina], steps D1-D18, rewritten to
 *  SSA form (every call writes a fresh slot, so [borrow_ok_ed] holds
 *  by computation and the emitted Rust respects &mut aliasing without
 *  raw-pointer tricks above the leaf boundary).  The paper's in-place
 *  buffer reuse (e.g. [Zout := Zout +F Zout]) is replaced by new
 *  slots; the value computed at each step is unchanged.  The
 *  D-marker on each op below names the [let/n] binding of
 *  [rcb_double_a0_gallina] it transcribes, and the SSA-version map
 *  is spelled out in §1b so the transcription can be checked line by
 *  line against that file.
 *
 *  [PointDoubleA0.rcb_double_a0_eq_ladderstep] proves the Gallina
 *  body equal to [ladderstep_gallina three_b X X Y Y Z Z] coordinate
 *  for coordinate -- a Leibniz equality rather than projective --
 *  for every ON-CURVE input, and
 *  [PointDoubleA0.rcb_double_a0_correct] is the Qed Rupicola
 *  derivation of a bedrock2 body implementing it.  Both report
 *  "Closed under the global context".
 *
 *  ** Squarings **
 *
 *  D1 and D6 are squarings, emitted as [mul_name x x].  The leaf ABI
 *  of the emitted crates exposes mul/add/sub only, and this keeps the
 *  callee list at [mul; add; sub] plus the 3b loader -- a SUBSET of
 *  what [CurveAdd.v]'s addition needs, so any curve with a complete
 *  addition already has every leaf this body needs.  It also costs
 *  nothing on BW6-761, whose [fp_square] leaf measures 230 ns against
 *  [fp_mul]'s 203 ns.
 *
 *  ** Curve constant **
 *
 *  Exactly ONE constant, [cB3] = 3b in the leaf (Montgomery) byte
 *  representation, baked in via [REdSetBytes], where the a = -3 body
 *  of [NistA3RustCmd.v] bakes in b and the general-a body of
 *  [NistG1AddRustCmd.v] bakes in two (a and 3b).
 *
 *  ** Point ABI **
 *
 *  As in [NistG1AddRustCmd.v]: a projective point is one
 *  [TBytes (3*fbytes)] buffer holding X || Y || Z, each felem being
 *  [fbytes] bytes = [limbs] little-endian u64 Montgomery limbs.
 *
 *  ** Leaf ABI: the crates need a byte-ABI shim **
 *
 *  The a = 0 crates ship their leaves as
 *  [extern "C" fn _<prefix>_{mul,add,sub}(o: *mut u64, x: *const u64,
 *  y: *const u64)] (see e.g.
 *  `bw6-761-safe-rust/generated/bw6_761_safe_tower.rs`), whereas
 *  [RustCmdToRust.rs_emit] emits [f(dest.as_mut_ptr(), a.as_ptr(),
 *  b.as_ptr())] over [ [u8; fbytes] ] slots, i.e. [*mut u8] /
 *  [*const u8].  The names below are therefore the byte-ABI SHIM
 *  names [<prefix>_fp_{mul,add,sub}], following the convention of
 *  `p256-safe-rust/src/extracted_leaves.rs`.  Each a = 0 crate needs
 *  such a shim module before the emitted body links; none has one
 *  today.  The prefix is NOT uniform across the crates -- BLS12-381
 *  uses [bls12], BLS12-377 uses [bls377], BW6-761 uses [bw6_761] --
 *  so it is spelled out per curve in §3.
 *
 *  Trust chain: [borrow_ok_ed] (vm_compute, below) + the rust_cmd_ed
 *  printer simulation + the per-leaf contracts, exactly as for
 *  [NistA3RustCmd.v].
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
(* §1. The curve-generic SSA body                                    *)
(* ================================================================ *)

Section CurveDoubleA0.

  (** Felem byte size and the three leaf names. *)
  Context (fbytes : nat).
  Context (mul_name add_name sub_name : string).
  (** The single curve constant 3b, in leaf representation,
      [fbytes] bytes. *)
  Context (threeb_bytes : list Z).

  Local Definition A0FEL (v : string) : located_ed :=
    {| loc_var := v; loc_type := TBytes fbytes |}.

  Local Definition A0Mul (d a b : string) : rust_cmd_ed :=
    REdCall mul_name (A0FEL d) [A0FEL a; A0FEL b].
  Local Definition A0Add (d a b : string) : rust_cmd_ed :=
    REdCall add_name (A0FEL d) [A0FEL a; A0FEL b].
  Local Definition A0Sub (d a b : string) : rust_cmd_ed :=
    REdCall sub_name (A0FEL d) [A0FEL a; A0FEL b].

  Fixpoint a0_seq_all (l : list rust_cmd_ed) : rust_cmd_ed :=
    match l with
    | [] => REdSkip
    | [c] => c
    | c :: r => REdSeq c (a0_seq_all r)
    end.

  (** Copy [fbytes] bytes from [src] at offset [off] into felem slot
      [dst] (offset 0). *)
  Local Definition a0_unpack1 (dst : string) (src : located_ed) (off : nat)
    : rust_cmd_ed :=
    REdFor "i" fbytes
      (REdSeq
        (REdByteLoad "bv" src (SAdd (SVar "i") (SLit (Z.of_nat off))))
        (REdByteStore (A0FEL dst) (SVar "i") (SVar "bv"))).

  (** Copy felem slot [src] into [dst] at offset [off]. *)
  Local Definition a0_pack1 (dst : located_ed) (src : string) (off : nat)
    : rust_cmd_ed :=
    REdFor "i" fbytes
      (REdSeq
        (REdByteLoad "bv" (A0FEL src) (SVar "i"))
        (REdByteStore dst (SAdd (SVar "i") (SLit (Z.of_nat off))) (SVar "bv"))).

  Fixpoint a0_let_slots (ns : list string) (body : rust_cmd_ed) : rust_cmd_ed :=
    match ns with
    | [] => body
    | n :: r => REdLetZero n (TBytes fbytes) (a0_let_slots r body)
    end.

  (* ---------------------------------------------------------------- *)
  (* §1b. Algorithm 9 — complete doubling at a = 0, 18 ops             *)
  (* ---------------------------------------------------------------- *)

  Local Definition a0_dbl_slots : list string :=
    ["X1"; "Y1"; "Z1"; "cB3";
     "t0"; "za"; "zb"; "zc"; "t1"; "t2"; "t2b";
     "xa"; "ya"; "t1b"; "t2c"; "t0b"; "yb"; "t1c"; "xb";
     "X3"; "Y3"; "Z3"].

  (** SSA-version map against [PointDoubleA0.rcb_double_a0_gallina].
      The Gallina body reuses four names (t0, t1, t2 and the three
      output buffers Xout/Yout/Zout); the left column is the paper /
      Gallina name at that point in the chain, the right column the
      SSA slot holding it here.

        D1   t0    := Y1 *F Y1                 -> t0
        D2   Zout  := t0 +F t0                 -> za
        D3   Zout  := Zout +F Zout             -> zb
        D4   Zout  := Zout +F Zout   (= 8Y^2)  -> zc
        D5   t1    := Y1 *F Z1                 -> t1
        D6   t2    := Z1 *F Z1                 -> t2
        D7   t2    := three_b *F t2 (= 3bZ^2)  -> t2b
        D8   Xout  := t2 *F Zout               -> xa
        D9   Yout  := t0 +F t2                 -> ya
        D10  Zout  := t1 *F Zout    (= 8Y^3Z)  -> Z3   [final Z3]
        D11  t1    := t2 +F t2       (= 6bZ^2) -> t1b
        D12  t2    := t1 +F t2       (= 9bZ^2) -> t2c
        D13  t0    := t0 -F t2                 -> t0b
        D14  Yout  := t0 *F Yout               -> yb
        D15  Yout  := Xout +F Yout             -> Y3   [final Y3]
        D16  t1    := X1 *F Y1                 -> t1c
        D17  Xout  := t0 *F t1                 -> xb
        D18  Xout  := Xout +F Xout             -> X3   [final X3]

      The three reads that the in-place chain resolves by "last
      write wins", and which the SSA form has to get right, are:

        * D8 and D10 both read Zout AT ITS D4 VALUE (8Y^2): D9 writes
          Yout, not Zout, so [zc] feeds both.  D10 is the write that
          turns Zout into the final Z3.
        * D11 and D12 read t2 AT ITS D7 VALUE (3bZ^2) -- nothing
          between D7 and D11 writes t2 -- so both read [t2b], and D12
          is [t1b +F t2b], not [t1b +F t2c].
        * D13 reads t0 AT ITS D1 VALUE (Y^2): D1 is the only write to
          t0 before it, so [t0b := t0 -F t2c].  D14 and D17 then read
          t0 at its D13 value, i.e. [t0b].
        * D14 reads Yout at its D9 value ([ya]); D15 reads Xout at its
          D8 value ([xa]).

      Verification performed: (i) each op below was matched against
      the corresponding [let/n] line of [rcb_double_a0_gallina] by
      operator and by the Gallina-name-to-SSA-slot table above;
      (ii) for every operand, the most recent preceding write to that
      Gallina name was located and the SSA slot it produced was
      checked to be the one used; (iii) the same 18 lines were checked
      against the numbered comments (* 1 *) .. (* 18 *) of the
      independently hand-transcribed
      `bw6-761-safe-rust/src/lib.rs::g1_proj_double`, which agrees
      step for step. *)
  Local Definition a0_dbl_ops : list rust_cmd_ed :=
    [ A0Mul "t0"  "Y1"  "Y1"       (* D1  t0 = Y^2 *)
    ; A0Add "za"  "t0"  "t0"       (* D2  = 2Y^2 *)
    ; A0Add "zb"  "za"  "za"       (* D3  = 4Y^2 *)
    ; A0Add "zc"  "zb"  "zb"       (* D4  Zout = 8Y^2 *)
    ; A0Mul "t1"  "Y1"  "Z1"       (* D5  t1 = YZ *)
    ; A0Mul "t2"  "Z1"  "Z1"       (* D6  t2 = Z^2 *)
    ; A0Mul "t2b" "cB3" "t2"       (* D7  t2 = 3b Z^2 *)
    ; A0Mul "xa"  "t2b" "zc"       (* D8  Xout = 3b Z^2 * 8Y^2 *)
    ; A0Add "ya"  "t0"  "t2b"      (* D9  Yout = Y^2 + 3b Z^2 *)
    ; A0Mul "Z3"  "t1"  "zc"       (* D10 Zout = 8 Y^3 Z  -> Z3 *)
    ; A0Add "t1b" "t2b" "t2b"      (* D11 t1 = 6b Z^2 *)
    ; A0Add "t2c" "t1b" "t2b"      (* D12 t2 = 9b Z^2 *)
    ; A0Sub "t0b" "t0"  "t2c"      (* D13 t0 = Y^2 - 9b Z^2 *)
    ; A0Mul "yb"  "t0b" "ya"       (* D14 Yout = t0 * Yout *)
    ; A0Add "Y3"  "xa"  "yb"       (* D15 Yout = Xout + Yout -> Y3 *)
    ; A0Mul "t1c" "X1"  "Y1"       (* D16 t1 = XY *)
    ; A0Mul "xb"  "t0b" "t1c"      (* D17 Xout = t0 * t1 *)
    ; A0Add "X3"  "xb"  "xb"       (* D18 Xout = 2 Xout -> X3 *)
    ].

  Definition g1_double_a0_body : function_body_ed :=
    fun dest args =>
      match args with
      | [P1] =>
          a0_let_slots a0_dbl_slots
            (a0_seq_all
              ([ a0_unpack1 "X1" P1 0
               ; a0_unpack1 "Y1" P1 fbytes
               ; a0_unpack1 "Z1" P1 (2 * fbytes)
               ; REdSetBytes (A0FEL "cB3") threeb_bytes
               ]
               ++ a0_dbl_ops
               ++ [ a0_pack1 dest "X3" 0
                  ; a0_pack1 dest "Y3" fbytes
                  ; a0_pack1 dest "Z3" (2 * fbytes)
                  ]))
      | _ => REdSkip
      end.

End CurveDoubleA0.

(* ================================================================ *)
(* §2. The a = 0 base-field primes and 3b constants                  *)
(* ================================================================ *)

(** The primes are restated here (rather than imported) so that this
    file's dependency footprint stays exactly [NistG1AddRustCmd.v]'s
    -- the per-curve [*_prime.v] files pull in the whole fiat-crypto
    synthesis pipeline.  Each definition is a verbatim copy of the
    tree's own, cited by file and line. *)

(** BN254 (alt_bn128), [bn254_prime_certif.v:13,15-19]. *)
Definition bn254_u : Z := 0x44E992B44A6909F1.
Definition bn254_m : Z :=
  Eval vm_compute in
    (36 * bn254_u^4 + 36 * bn254_u^3 + 24 * bn254_u^2 + 6 * bn254_u + 1).

(** BN256, [bn256_prime_certif.v:13,15-19]. *)
Definition bn256_u : Z := 0x5A76AE9AEC588301.
Definition bn256_m : Z :=
  Eval vm_compute in
    (36 * bn256_u^4 + 36 * bn256_u^3 + 24 * bn256_u^2 + 6 * bn256_u + 1).

(** BN446, [bn446_prime_certif.v:13,15-19]. *)
Definition bn446_u : Z := 0x4000000000000000001000000001.
Definition bn446_m : Z :=
  Eval vm_compute in
    (36 * bn446_u^4 + 36 * bn446_u^3 + 24 * bn446_u^2 + 6 * bn446_u + 1).

(** BLS12-381, [bls12_prime.v:33-35]. *)
Definition bls12_381_u : Z := -0xd201000000010000.
Definition bls12_381_m : Z :=
  Eval vm_compute in
    ((((bls12_381_u - 1)^2 * (bls12_381_u^4 - bls12_381_u^2 + 1)) / 3)
     + bls12_381_u).

(** BLS12-377, [bls12_377_prime.v:33-35]. *)
Definition bls12_377_u : Z := 0x8508c00000000001.
Definition bls12_377_m : Z :=
  Eval vm_compute in
    ((((bls12_377_u - 1)^2 * (bls12_377_u^4 - bls12_377_u^2 + 1)) / 3)
     + bls12_377_u).

(** BW6-761, [bw6_761_prime_certif.v:8-9]. *)
Definition bw6_761_m : Z :=
  Eval vm_compute in
    0x122e824fb83ce0ad187c94004faff3eb926186a81d14688528275ef8087be41707ba638e584e91903cebaff25b423048689c8ed12f9fd9071dcd3dc73ebff2e98a116c25667a8f8160cf8aeeaf0a437e6913e6870000082f49d00000000008b.

(** Curve b coefficients of y^2 = x^3 + b, each cited to the tree's
    own [three_b] file, which also carries the [three_b_mont]
    Montgomery limb list that [three_b_mont_valid] certifies:

      BN254      [bn254_three_b.v:34-36]      b = 3,   3b = 9
      BN256      [bn256_three_b.v:34-36]      b = 3,   3b = 9
      BN446      [bn446_three_b.v:34-36]      b = 257, 3b = 771
      BLS12-381  [bls12_three_b.v:35-36]      b = 4,   3b = 12
      BLS12-377  [bls12_377_three_b.v:34-36]  b = 1,   3b = 3
      BW6-761    [BW6_761Curve_G1.v:25]       b = -1,  3b = m - 3

    BW6-761 is the one written as [m - 1] rather than a small
    literal, so that [(3 * b) mod m] below reproduces
    [BW6_761Curve_G1.three_b = m - 3] by the same formula as the
    others.  It matches `bw6-761-safe-rust/src/lib.rs::g1_three_b()`,
    which computes [opp(from_word 3)]. *)

Definition bn254_b     : Z := 3.
Definition bn256_b     : Z := 3.
Definition bn446_b     : Z := 257.
Definition bls12_381_b : Z := 4.
Definition bls12_377_b : Z := 1.
Definition bw6_761_b   : Z := Eval vm_compute in (bw6_761_m - 1).

(** [mont_bytes limbs m v = z_le_bytes (limbs*8) ((v * 2^(64*limbs))
    mod m)] comes from [NistG1AddRustCmd.v].  It is the same encoding
    as [WordByWordMontgomery.to_montgomerymod 64 n M m'] applied to
    [Partition.partition (uweight 64) n v] and then serialized
    little-endian -- i.e. the [three_b_mont] limb list of the
    per-curve [*_three_b.v] file, read as bytes.  Limb counts are the
    [Fp(pub [u64; k])] of each crate's
    `generated/<curve>_safe_tower.rs`:

      BN254 4, BN256 4, BN446 7, BLS12-381 6, BLS12-377 6, BW6-761 12. *)

Definition bn254_threeb_bytes : list Z :=
  Eval vm_compute in mont_bytes 4 bn254_m ((3 * bn254_b) mod bn254_m).
Definition bn256_threeb_bytes : list Z :=
  Eval vm_compute in mont_bytes 4 bn256_m ((3 * bn256_b) mod bn256_m).
Definition bn446_threeb_bytes : list Z :=
  Eval vm_compute in mont_bytes 7 bn446_m ((3 * bn446_b) mod bn446_m).
Definition bls12_381_threeb_bytes : list Z :=
  Eval vm_compute in
    mont_bytes 6 bls12_381_m ((3 * bls12_381_b) mod bls12_381_m).
Definition bls12_377_threeb_bytes : list Z :=
  Eval vm_compute in
    mont_bytes 6 bls12_377_m ((3 * bls12_377_b) mod bls12_377_m).
Definition bw6_761_threeb_bytes : list Z :=
  Eval vm_compute in
    mont_bytes 12 bw6_761_m ((3 * bw6_761_b) mod bw6_761_m).

(* ================================================================ *)
(* §3. Per-curve bodies + borrow-check certificates                  *)
(* ================================================================ *)

(** Leaf names.  The prefix is the crate's OWN leaf prefix, taken from
    the [extern "C"] block of `generated/<curve>_safe_tower.rs`, and
    it is NOT uniform:

      bn254-safe-rust      _bn254_{mul,add,sub}      -> bn254_fp_*
      bn256-safe-rust      _bn256_{mul,add,sub}      -> bn256_fp_*
      bn446-safe-rust      _bn446_{mul,add,sub}      -> bn446_fp_*
      bls12-381-safe-rust  _bls12_{mul,add,sub}      -> bls12_fp_*
      bls12-377-safe-rust  _bls377_{mul,add,sub}     -> bls377_fp_*
      bw6-761-safe-rust    _bw6_761_{mul,add,sub}    -> bw6_761_fp_*

    The names below are the byte-ABI SHIMS the emitted body calls
    ([*mut u8] / [*const u8] over [ [u8; fbytes] ] slots), not those
    extern symbols ([*mut u64] / [*const u64]).  See the header. *)

Definition bn254_g1_double_a0_body : function_body_ed :=
  g1_double_a0_body 32 "bn254_fp_mul" "bn254_fp_add" "bn254_fp_sub"
                    bn254_threeb_bytes.

Definition bn256_g1_double_a0_body : function_body_ed :=
  g1_double_a0_body 32 "bn256_fp_mul" "bn256_fp_add" "bn256_fp_sub"
                    bn256_threeb_bytes.

Definition bn446_g1_double_a0_body : function_body_ed :=
  g1_double_a0_body 56 "bn446_fp_mul" "bn446_fp_add" "bn446_fp_sub"
                    bn446_threeb_bytes.

Definition bls12_381_g1_double_a0_body : function_body_ed :=
  g1_double_a0_body 48 "bls12_fp_mul" "bls12_fp_add" "bls12_fp_sub"
                    bls12_381_threeb_bytes.

Definition bls12_377_g1_double_a0_body : function_body_ed :=
  g1_double_a0_body 48 "bls377_fp_mul" "bls377_fp_add" "bls377_fp_sub"
                    bls12_377_threeb_bytes.

Definition bw6_761_g1_double_a0_body : function_body_ed :=
  g1_double_a0_body 96 "bw6_761_fp_mul" "bw6_761_fp_add" "bw6_761_fp_sub"
                    bw6_761_threeb_bytes.

(** [pt_loc] is the sentinel locator of [NistG1AddRustCmd.v], matching
    [rs_body_extract]. *)

Example bn254_g1_double_a0_borrow_ok :
  borrow_ok_ed (bn254_g1_double_a0_body (pt_loc 32 "out")
                 [pt_loc 32 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example bn256_g1_double_a0_borrow_ok :
  borrow_ok_ed (bn256_g1_double_a0_body (pt_loc 32 "out")
                 [pt_loc 32 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example bn446_g1_double_a0_borrow_ok :
  borrow_ok_ed (bn446_g1_double_a0_body (pt_loc 56 "out")
                 [pt_loc 56 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example bls12_381_g1_double_a0_borrow_ok :
  borrow_ok_ed (bls12_381_g1_double_a0_body (pt_loc 48 "out")
                 [pt_loc 48 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example bls12_377_g1_double_a0_borrow_ok :
  borrow_ok_ed (bls12_377_g1_double_a0_body (pt_loc 48 "out")
                 [pt_loc 48 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

Example bw6_761_g1_double_a0_borrow_ok :
  borrow_ok_ed (bw6_761_g1_double_a0_body (pt_loc 96 "out")
                 [pt_loc 96 "arg0"]) = true.
Proof. vm_compute. reflexivity. Qed.

(** Sanity: the constant really is [fbytes] bytes wide, so the
    [REdSetBytes] does not truncate or overrun the [cB3] slot. *)

Example bn254_threeb_bytes_len : length bn254_threeb_bytes = 32%nat.
Proof. vm_compute. reflexivity. Qed.
Example bn256_threeb_bytes_len : length bn256_threeb_bytes = 32%nat.
Proof. vm_compute. reflexivity. Qed.
Example bn446_threeb_bytes_len : length bn446_threeb_bytes = 56%nat.
Proof. vm_compute. reflexivity. Qed.
Example bls12_381_threeb_bytes_len : length bls12_381_threeb_bytes = 48%nat.
Proof. vm_compute. reflexivity. Qed.
Example bls12_377_threeb_bytes_len : length bls12_377_threeb_bytes = 48%nat.
Proof. vm_compute. reflexivity. Qed.
Example bw6_761_threeb_bytes_len : length bw6_761_threeb_bytes = 96%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §4. Rust emission                                                 *)
(* ================================================================ *)

Definition bn254_g1_double_a0_rs : string :=
  rs_body_extract
    {| bes_name := "bn254_g1_double_a0_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96];
       bes_body := bn254_g1_double_a0_body |}.

Definition bn256_g1_double_a0_rs : string :=
  rs_body_extract
    {| bes_name := "bn256_g1_double_a0_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96];
       bes_body := bn256_g1_double_a0_body |}.

Definition bn446_g1_double_a0_rs : string :=
  rs_body_extract
    {| bes_name := "bn446_g1_double_a0_extracted";
       bes_dest_type := TBytes 168;
       bes_arg_types := [TBytes 168];
       bes_body := bn446_g1_double_a0_body |}.

Definition bls12_381_g1_double_a0_rs : string :=
  rs_body_extract
    {| bes_name := "bls12_381_g1_double_a0_extracted";
       bes_dest_type := TBytes 144;
       bes_arg_types := [TBytes 144];
       bes_body := bls12_381_g1_double_a0_body |}.

Definition bls12_377_g1_double_a0_rs : string :=
  rs_body_extract
    {| bes_name := "bls12_377_g1_double_a0_extracted";
       bes_dest_type := TBytes 144;
       bes_arg_types := [TBytes 144];
       bes_body := bls12_377_g1_double_a0_body |}.

Definition bw6_761_g1_double_a0_rs : string :=
  rs_body_extract
    {| bes_name := "bw6_761_g1_double_a0_extracted";
       bes_dest_type := TBytes 288;
       bes_arg_types := [TBytes 288];
       bes_body := bw6_761_g1_double_a0_body |}.

(** Emission: [EmitDoubleA0Rust.v] evaluates each of the six strings
    under [Redirect].  BLS24-509 is deliberately absent: the tree has
    no [bls24_509_three_b.v] and no G1 curve-add instantiation for it,
    so its 3b cannot be sourced from a verified constant (the only
    record of b = 1 is the [curve_b] field of the [CurveParams]
    record in [BLS24_509_params.v]); its crate also has no
    definition for the [_bls24_509_*] extern leaves it declares. *)
