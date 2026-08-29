(** * NistWnafScalarMultRustCmd — verified-AST safe-Rust emission of the
 *    NIST P-curve single-scalar wNAF scalar multiplication
 *    (P-224 / P-256 / P-384), w = 4.
 *
 *  This is the scalar-multiplication companion of [NistG1AddRustCmd.v]:
 *  the same [rust_cmd_ed] IR, the same printer ([RustCmdToRust]), and
 *  the same borrow-certificate discipline, applied to the wNAF driver
 *  that [Bedrock.Group.ScalarMult.P256_wNAF_Instance] proves correct
 *  ([p256_wnaf_single_full], Qed).
 *
 *  ** What this transcribes
 *
 *  The bedrock2 source is [wNAF_GLV_Func.wnaf_single_func_body]
 *  instantiated at (curve_add, curve_double, store_zero, felem_copy,
 *  opp_inplace, num_digits, felem_size_in_bytes), i.e. the body of
 *  [P256_wNAF_Instance.p256_wnaf_single_func]:
 *
 *      store_zero(outx, outy, outz);
 *      iter = 257;
 *      while (0 < iter) {
 *        iter = iter - 1;
 *        curve_double(out, out);
 *        d = digits[iter];
 *        if (d) {
 *          lookup_d = (d <s 0) ? 0 - d : d;
 *          tab_idx  = (lookup_d - 1) >>u 1;
 *          tab_off  = tab_idx * (3 * felem_size);
 *          felem_copy(auxx, table + tab_off + 0);
 *          felem_copy(auxy, table + tab_off + felem_size);
 *          felem_copy(auxz, table + tab_off + 2*felem_size);
 *          if (d <s 0) { opp_inplace(auxy, auxy) };
 *          curve_add(out, aux, out)
 *        }
 *      }
 *
 *  ** Where the transcription differs, and why each step is faithful
 *
 *  1. POINT ABI.  bedrock2 carries a projective point as three separate
 *     felem pointers (outx, outy, outz); here a point is ONE
 *     [TBytes (3*fbytes)] buffer holding X ‖ Y ‖ Z, exactly the ABI of
 *     [NistG1AddRustCmd]'s emitted addition and byte-for-byte the memory
 *     image that [BLS12_wNAF_ProcessDigits.TablePoint] lays down
 *     (X at +0, Y at +fbytes, Z at +2*fbytes).
 *
 *  2. TABLE.  [Table4 base entries] places entry i at
 *     [base + i * (3 * felem_size_in_bytes)], so the whole table is a
 *     [TArr 4 (TBytes (3*fbytes))] — an [[u8; 3*fbytes]; 4] in Rust.
 *     The bedrock2 [tab_off = tab_idx * 3 * felem_size] pointer
 *     arithmetic becomes the array index [tab_idx] itself; the emitted
 *     [REdArrLoad] is the three [felem_copy] calls fused into one
 *     whole-point copy.
 *
 *  3. DIGIT ARRAY.  [DigitArray base dk] is an [array scalar] at stride
 *     [bytes_per_word] = 8, holding [word.of_Z d] — a two's-complement
 *     64-bit encoding of each signed digit.  That is a [TArr n TU64],
 *     an [[u64; n]] in Rust, and [d = digits[iter]] is [REdArrLoad].
 *
 *  4. SIGN TEST.  bedrock2 uses [bopname.lts d 0] (signed less-than on
 *     a 64-bit word).  [sexpr_ed] has no signed comparison, so the test
 *     is written as the sign bit, [(d >> 63) & 1], which for a 64-bit
 *     two's-complement word is the same predicate.  Everything else in
 *     the digit path — [0 - d], [(lookup_d - 1) >>u 1] — maps to
 *     [SSub] / [SShr], which the printer emits as [wrapping_sub] and
 *     the (unsigned) [>>], matching bedrock2's word semantics.
 *
 *  5. store_zero.  The bedrock2 wrapper is three [from_word] calls
 *     loading 0, 1, 0.  Here the identity point is a compile-time
 *     [REdSetBytes] constant: X = 0, Y = Montgomery(1) = R mod m,
 *     Z = 0, in the same leaf byte representation the addition uses.
 *     (Constant-folding of the three [from_word] calls; the byte
 *     lists below are computed by [vm_compute] from the modulus.)
 *
 *  6. curve_add / curve_double.  The bedrock2 wrappers
 *     ([NistWnafWrappers.curve_add_inplace_general_func] and
 *     [curve_double_general_func]) exist only to make the aliased calls
 *     [add(P,Q,P)] and [double(P,P)] legal: their bodies stack-allocate
 *     temporaries, [felem_copy] the inputs in, call the non-aliasing
 *     [curve_add_general], and copy back.  Here the same copies are
 *     explicit ([copy_pt] into [t1] / [t2]) and the call goes straight
 *     to the emitted addition [add_name].  As a result NO call site in
 *     the emitted Rust passes the same buffer twice, so the emitted
 *     code has no overlapping [&mut] and [borrow_ok_ed] holds.
 *
 *  7. TABLE CONSTRUCTION is done INSIDE the emitted body (§1c below),
 *     as [WnafTableBuild.build_odd_table_gen add 4 P] specifies:
 *     entry i = P + i·(2P), i.e. [P; 3P; 5P; 7P].  This is stronger
 *     than the chain's G7 hypothesis, which merely ASSUMES a caller-
 *     supplied table; [P256_wNAF_Table.p256_table_ok_of_oncurve] (Qed)
 *     says this exact construction discharges it.
 *
 *  ** Constant time: NO.
 *
 *  The proved driver branches on the digit ([if (d)], [if (d <s 0)])
 *  and indexes the table at a secret-dependent [tab_idx].  The comment
 *  on [wNAF_GLV_Func.process_one_digit] says as much ("Uses branching
 *  (not constant-time) for simplicity").  The emitted Rust inherits
 *  this exactly.  It is therefore appropriate for PUBLIC scalars only;
 *  the constant-time double-and-add-always ladder in each crate's
 *  group.rs remains the secret-scalar path.
 *
 *  ** Trust chain
 *
 *  [borrow_ok_ed] (vm_compute, below) + the rust_cmd_ed printer
 *  simulation + the emitted addition of [NistG1AddRustCmd] + the
 *  per-leaf contracts of fiat-crypto's field ops.  Functional
 *  correctness of the dataflow is the Gallina content of
 *  [P256_wNAF_Instance.p256_wnaf_single_full] and
 *  [P256_wNAF_Table.p256_table_ok_of_oncurve]; as in
 *  [NistG1AddRustCmd.v], a self-contained rhoare proof relating THIS
 *  AST to that bedrock2 body is the designated follow-up and is not
 *  claimed here.
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
(* §1. The curve-generic wNAF driver body                            *)
(* ================================================================ *)

Section NistWnafDriver.

  (** Bytes per field element (32 for P-224/P-256, 48 for P-384). *)
  Context (fbytes : nat).
  (** The emitted complete addition of [NistG1AddRustCmd] for this
      curve, e.g. "p256_g1_add_extracted".  Called via [REdCallFn]
      (a Rocq-emitted helper), not [REdCall] (an axiomatized leaf). *)
  Context (add_name : string).
  (** The field negation leaf, e.g. "p256_fp_opp". *)
  Context (opp_name : string).
  (** Number of wNAF digits: 257 (P-256), 385 (P-384), 225 (P-224). *)
  Context (num_digits : nat).
  (** The identity point (0 : 1 : 0) in leaf byte representation:
      [3*fbytes] bytes, X ‖ Y ‖ Z. *)
  Context (id_bytes : list Z).

  Local Notation ptbytes := (3 * fbytes)%nat.

  Local Definition PT (v : string) : located_ed :=
    {| loc_var := v; loc_type := TBytes ptbytes |}.
  Local Definition FE (v : string) : located_ed :=
    {| loc_var := v; loc_type := TBytes fbytes |}.
  Local Definition U64L (v : string) : located_ed :=
    {| loc_var := v; loc_type := TU64 |}.

  Fixpoint wseq (l : list rust_cmd_ed) : rust_cmd_ed :=
    match l with
    | [] => REdSkip
    | [c] => c
    | c :: r => REdSeq c (wseq r)
    end.

  (** Whole-point copy [dst := src] ([3*fbytes] bytes). *)
  Local Definition copy_pt (dst src : located_ed) : rust_cmd_ed :=
    REdFor "ci" ptbytes
      (REdSeq
        (REdByteLoad "cb" src (SVar "ci"))
        (REdByteStore dst (SVar "ci") (SVar "cb"))).

  (** [dst := src[off .. off+fbytes)] — read one felem out of a point. *)
  Local Definition get_fe (dst src : located_ed) (off : nat) : rust_cmd_ed :=
    REdFor "yi" fbytes
      (REdSeq
        (REdByteLoad "yb" src (SAdd (SVar "yi") (SLit (Z.of_nat off))))
        (REdByteStore dst (SVar "yi") (SVar "yb"))).

  (** [dst[off .. off+fbytes) := src] — write one felem into a point. *)
  Local Definition put_fe (dst : located_ed) (off : nat) (src : located_ed)
    : rust_cmd_ed :=
    REdFor "yi" fbytes
      (REdSeq
        (REdByteLoad "yb" src (SVar "yi"))
        (REdByteStore dst (SAdd (SVar "yi") (SLit (Z.of_nat off))) (SVar "yb"))).

  (** The sign bit of the two's-complement digit word: bedrock2's
      [bopname.lts d 0] at width 64. *)
  Local Definition d_is_neg : sexpr_ed :=
    SAnd (SShr (SVar "d") (SLit 63)) (SLit 1).

  (* ---------------------------------------------------------------- *)
  (* §1a. One loop iteration                                           *)
  (* ---------------------------------------------------------------- *)

  (** [process_one_digit] of wNAF_GLV_Func.v, at the packed point ABI.
      [acc] is the accumulator slot, [tbl] the 4-entry table. *)
  Local Definition process_digit (acc tbl : located_ed) : rust_cmd_ed :=
    wseq
      [ (* lookup_d = (d <s 0) ? 0 - d : d *)
        REdIfNz d_is_neg
          (REdScalarSet "ld" (SSub (SLit 0) (SVar "d")))
          (REdScalarSet "ld" (SVar "d"))
        (* tab_idx = (lookup_d - 1) >>u 1 *)
      ; REdScalarSet "ti" (SShr (SSub (SVar "ld") (SLit 1)) (SLit 1))
        (* the three felem_copy calls, fused: aux = table[tab_idx] *)
      ; REdArrLoad (PT "aux") tbl (SVar "ti")
        (* if (d <s 0) { opp_inplace(auxy, auxy) } *)
      ; REdIfNz d_is_neg
          (wseq
            [ get_fe (FE "auy") (PT "aux") fbytes
            ; REdCall opp_name (FE "auyn") [FE "auy"]
            ; put_fe (PT "aux") fbytes (FE "auyn") ])
          REdSkip
        (* curve_add(out, aux, out): the wrapper's felem_copy-in /
           felem_copy-out made explicit, so dest and args are distinct *)
      ; copy_pt (PT "t1") acc
      ; REdCallFn add_name acc [PT "t1"; PT "aux"]
      ].

  Local Definition loop_body (acc tbl dig : located_ed) : rust_cmd_ed :=
    wseq
      [ REdScalarSet "iter" (SSub (SVar "iter") (SLit 1))
        (* curve_double(out, out) — the wrapper's two input copies *)
      ; copy_pt (PT "t1") acc
      ; copy_pt (PT "t2") acc
      ; REdCallFn add_name acc [PT "t1"; PT "t2"]
        (* d = digits[iter] *)
      ; REdArrLoad (U64L "d") dig (SVar "iter")
      ; REdIfNz (SVar "d") (process_digit acc tbl) REdSkip
      ].

  (* ---------------------------------------------------------------- *)
  (* §1c. Table construction: [P; 3P; 5P; 7P]                          *)
  (* ---------------------------------------------------------------- *)

  (** [WnafTableBuild.build_odd_table_gen add 4 P] = [build_aux add 4 P (P+P)],
      whose entry i is [addn add i P (P+P)] = P + i·(2P).  Written out:
        e0 = P;  dbl = P + P;
        e1 = e0 + dbl;  e2 = e1 + dbl;  e3 = e2 + dbl. *)
  Local Definition build_table (src tbl : located_ed) : rust_cmd_ed :=
    wseq
      [ copy_pt (PT "e0") src
      ; REdArrStore tbl (SLit 0) (PT "e0")
      ; copy_pt (PT "t1") (PT "e0")
      ; REdCallFn add_name (PT "dbl") [PT "e0"; PT "t1"]
      ; REdCallFn add_name (PT "e1") [PT "e0"; PT "dbl"]
      ; REdArrStore tbl (SLit 1) (PT "e1")
      ; REdCallFn add_name (PT "e2") [PT "e1"; PT "dbl"]
      ; REdArrStore tbl (SLit 2) (PT "e2")
      ; REdCallFn add_name (PT "e3") [PT "e2"; PT "dbl"]
      ; REdArrStore tbl (SLit 3) (PT "e3")
      ].

  (* ---------------------------------------------------------------- *)
  (* §1d. The full body                                                *)
  (* ---------------------------------------------------------------- *)

  Local Definition pt_slots : list string :=
    ["e0"; "e1"; "e2"; "e3"; "dbl"; "t1"; "t2"; "aux"].

  Fixpoint let_pts (ns : list string) (body : rust_cmd_ed) : rust_cmd_ed :=
    match ns with
    | [] => body
    | n :: r => REdLetZero n (TBytes ptbytes) (let_pts r body)
    end.

  (** Arguments: [arg0] the base point, [arg1] the 4-entry table
      scratch buffer, [arg2] the digit array.  Destination [out] is the
      accumulator and the result. *)
  Definition nist_wnaf_body : function_body_ed :=
    fun dest args =>
      match args with
      | [Pin; tbl; dig] =>
          let_pts pt_slots
            (REdLetZero "auy" (TBytes fbytes)
            (REdLetZero "auyn" (TBytes fbytes)
            (REdLetZero "d" TU64
            (REdLetU64 "ld" (SLit 0)
            (REdLetU64 "ti" (SLit 0)
            (REdLetU64 "iter" (SLit (Z.of_nat num_digits))
              (wseq
                [ build_table Pin tbl
                ; REdSetBytes dest id_bytes
                ; REdWhileNz (SLt (SLit 0) (SVar "iter"))
                    (loop_body dest tbl dig)
                ])))))))
      | _ => REdSkip
      end.

End NistWnafDriver.

(* ================================================================ *)
(* §2. Identity-point constants                                      *)
(* ================================================================ *)

(** X = 0, Y = Montgomery(1) = R mod m, Z = 0, in the same leaf byte
    representation [NistG1AddRustCmd.mont_bytes] uses for a and 3b.
    This is the constant-folded value of the three [from_word] calls in
    [NistWnafWrappers.store_zero_from_word_func]. *)
Definition ident_bytes (limbs : nat) (m : Z) : list Z :=
  mont_bytes limbs m 0 ++ mont_bytes limbs m 1 ++ mont_bytes limbs m 0.

Definition p224_ident_bytes : list Z :=
  Eval vm_compute in ident_bytes 4 p224_m.
Definition p256_ident_bytes : list Z :=
  Eval vm_compute in ident_bytes 4 p256_m.
Definition p384_ident_bytes : list Z :=
  Eval vm_compute in ident_bytes 6 p384_m.

(* ================================================================ *)
(* §3. Per-curve bodies + borrow-check certificates                  *)
(* ================================================================ *)

Definition p224_wnaf_body : function_body_ed :=
  nist_wnaf_body 32 "p224_g1_add_extracted" "p224_fp_opp" 225
                 p224_ident_bytes.
Definition p256_wnaf_body : function_body_ed :=
  nist_wnaf_body 32 "p256_g1_add_extracted" "p256_fp_opp" 257
                 p256_ident_bytes.
Definition p384_wnaf_body : function_body_ed :=
  nist_wnaf_body 48 "p384_g1_add_extracted" "p384_fp_opp" 385
                 p384_ident_bytes.

(** Sentinel locators matching [rs_body_extract_inline]. *)
Definition wnaf_locs (fb nd : nat)
  : located_ed * list located_ed :=
  ({| loc_var := "out"; loc_type := TBytes (3 * fb) |},
   [ {| loc_var := "arg0"; loc_type := TBytes (3 * fb) |}
   ; {| loc_var := "arg1"; loc_type := TArr 4 (TBytes (3 * fb)) |}
   ; {| loc_var := "arg2"; loc_type := TArr nd TU64 |} ]).

Example p224_wnaf_borrow_ok :
  borrow_ok_ed (p224_wnaf_body (fst (wnaf_locs 32 225))
                               (snd (wnaf_locs 32 225))) = true.
Proof. vm_compute. reflexivity. Qed.

Example p256_wnaf_borrow_ok :
  borrow_ok_ed (p256_wnaf_body (fst (wnaf_locs 32 257))
                               (snd (wnaf_locs 32 257))) = true.
Proof. vm_compute. reflexivity. Qed.

Example p384_wnaf_borrow_ok :
  borrow_ok_ed (p384_wnaf_body (fst (wnaf_locs 48 385))
                               (snd (wnaf_locs 48 385))) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §4. Rust emission                                                 *)
(* ================================================================ *)

(** [rs_body_extract_inline] (not [rs_body_extract]): the driver calls
    the emitted addition through [REdCallFn], which in the inline
    printer becomes a direct typed call to
    [pXXX_g1_add_extracted(&mut [u8; 3*fbytes], ...)] — the signature
    [NistG1AddRustCmd]'s emission already produces.  The [REdCall] site
    for [opp_name] still uses the raw-pointer FFI form, matching the
    leaf shims in [pXXX-safe-rust/src/extracted_leaves.rs]. *)

Definition p224_wnaf_rs : string :=
  rs_body_extract_inline
    {| bes_name := "p224_wnaf_scalar_mul_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96; TArr 4 (TBytes 96); TArr 225 TU64];
       bes_body := p224_wnaf_body |}.

Definition p256_wnaf_rs : string :=
  rs_body_extract_inline
    {| bes_name := "p256_wnaf_scalar_mul_extracted";
       bes_dest_type := TBytes 96;
       bes_arg_types := [TBytes 96; TArr 4 (TBytes 96); TArr 257 TU64];
       bes_body := p256_wnaf_body |}.

Definition p384_wnaf_rs : string :=
  rs_body_extract_inline
    {| bes_name := "p384_wnaf_scalar_mul_extracted";
       bes_dest_type := TBytes 144;
       bes_arg_types := [TBytes 144; TArr 4 (TBytes 144); TArr 385 TU64];
       bes_body := p384_wnaf_body |}.

(** Emission: evaluate [Eval vm_compute in p256_wnaf_rs] and drop the
    resulting string into
    [p256-safe-rust/src/scalar_mul_extracted.rs] (below the hand-written
    header and the digit encoder), likewise for the other two curves. *)
