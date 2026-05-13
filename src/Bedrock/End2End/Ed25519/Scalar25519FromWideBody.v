(** * Scalar25519FromWideBody — rust_cmd_ed AST for
 *    Scalar25519::from_bytes_mod_order_wide.
 *
 *  Wide reduction: given 64 LE bytes [wide], compute
 *      wide mod L   where   L = 2^252 + L_extra.
 *
 *  Algorithm (mirrors [curve25519-jasmin-rs/src/scalar25519.rs::
 *  from_bytes_mod_order_wide]):
 *
 *      lo      := from_bytes_mod_order(wide[0..32])      (low half)
 *      hi      := from_bytes_mod_order(wide[32..64])     (high half)
 *      c256    := negate(L_extra · 16)                   (= 2^256 mod L)
 *      out     := hi · c256 + lo
 *
 *  The identity [2^256 ≡ -16 · L_extra (mod L)] comes from
 *  [L = 2^252 + L_extra], so [2^256 = 16 · 2^252 = 16 · (L - L_extra)
 *  ≡ -16 · L_extra]. This identity is supplied as an algebraic
 *  Hypothesis in [Scalar25519FromWideCorrect.v].
 *
 *  Leaves (declared external — [REdCall]; their semantics is
 *  supplied by the caller's [callee_post] oracle):
 *    - scalar25519_from_bytes_mod_order  : (out, src_bytes)
 *    - scalar25519_set_bytes (REdSetBytes) : initialise const tables
 *    - scalar25519_mul   : (out, a, b)
 *    - scalar25519_add   : (out, a, b)
 *    - scalar25519_negate: (out, a)
 *
 *  Phase 2.A of "extend the IR": Part A of the three-chain prompt.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Helpers                                                       *)
(* ================================================================ *)

(** A 32-byte slot (low or high half of the 64-byte input). *)
Definition LBytes32 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 32 |}.

(** A scalar-field slot. *)
Definition LFpL (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFpL25519 |}.

(** L_extra = L - 2^252 = 27742317777372353535851937790883648493.
    32-byte little-endian encoding (taken verbatim from
    [curve25519-jasmin-rs/src/scalar25519.rs]). *)
Definition L_EXTRA_LE : list Z :=
  [ 0xed; 0xd3; 0xf5; 0x5c; 0x1a; 0x63; 0x12; 0x58
  ; 0xd6; 0x9c; 0xf7; 0xa2; 0xde; 0xf9; 0xde; 0x14
  ; 0;     0;    0;    0;    0;    0;    0;    0
  ; 0;     0;    0;    0;    0;    0;    0;    0 ].

(** Sixteen (1×u64), 32-byte little-endian. *)
Definition SIXTEEN_LE : list Z :=
  [ 16; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0
  ;  0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0 ].

(** Sequence helper. *)
Fixpoint seqN (l : list rust_cmd_ed) : rust_cmd_ed :=
  match l with
  | [] => REdSkip
  | [c] => c
  | c :: cs => REdSeq c (seqN cs)
  end.

(* ================================================================ *)
(* §2. Body                                                          *)
(* ================================================================ *)

(** [scalar25519_from_bytes_mod_order_wide] body.
    Inputs:  [lo_bytes : TBytes 32]   (low half of the 64-byte input)
             [hi_bytes : TBytes 32]   (high half).
    Output:  [dest : TFpL25519]       (result = wide mod L).
    Internal slots:
             [lo, hi, l_extra, sixteen, c256_pre, c256, hc256
             : TFpL25519]
             [le_bytes, sx_bytes      : TBytes 32]   (constant tables)

    We take the two halves as separate 32-byte slots rather than a
    single 64-byte buffer; the splitting is performed by the caller
    (XEdDSA-sign / EdDSA-sign). This keeps the AST flat: it matches
    the Rust implementation after the [copy_from_slice] step.

    Constants [L_EXTRA_LE] and [SIXTEEN_LE] are initialised via
    [REdSetBytes] just before [scalar25519_from_bytes_mod_order]
    consumes them. *)
Definition from_wide_body : function_body_ed :=
  fun dest args =>
    match args with
    | [lo_bytes_loc; hi_bytes_loc] =>
        REdLetZero "lo"        TFpL25519 (
        REdLetZero "hi"        TFpL25519 (
        REdLetZero "l_extra"   TFpL25519 (
        REdLetZero "sixteen"   TFpL25519 (
        REdLetZero "c256_pre"  TFpL25519 (
        REdLetZero "c256"      TFpL25519 (
        REdLetZero "hc256"     TFpL25519 (
        REdLetZero "le_bytes"  (TBytes 32) (
        REdLetZero "sx_bytes"  (TBytes 32) (
        seqN
          [ (* lo := from_bytes_mod_order(lo_bytes) *)
            REdCall "scalar25519_from_bytes_mod_order"
                    (LFpL "lo") [lo_bytes_loc]
          (* hi := from_bytes_mod_order(hi_bytes) *)
          ; REdCall "scalar25519_from_bytes_mod_order"
                    (LFpL "hi") [hi_bytes_loc]
          (* Initialise constant tables. *)
          ; REdSetBytes (LBytes32 "le_bytes") L_EXTRA_LE
          ; REdSetBytes (LBytes32 "sx_bytes") SIXTEEN_LE
          (* l_extra := from_bytes_mod_order(le_bytes) *)
          ; REdCall "scalar25519_from_bytes_mod_order"
                    (LFpL "l_extra") [LBytes32 "le_bytes"]
          (* sixteen := from_bytes_mod_order(sx_bytes) *)
          ; REdCall "scalar25519_from_bytes_mod_order"
                    (LFpL "sixteen") [LBytes32 "sx_bytes"]
          (* c256_pre := l_extra · sixteen   (= 16 · L_extra mod L) *)
          ; REdCall "scalar25519_mul"
                    (LFpL "c256_pre") [LFpL "l_extra"; LFpL "sixteen"]
          (* c256 := -(c256_pre) = -16·L_extra mod L = 2^256 mod L *)
          ; REdCall "scalar25519_negate"
                    (LFpL "c256") [LFpL "c256_pre"]
          (* hc256 := hi · c256 *)
          ; REdCall "scalar25519_mul"
                    (LFpL "hc256") [LFpL "hi"; LFpL "c256"]
          (* dest := hc256 + lo *)
          ; REdCall "scalar25519_add"
                    dest [LFpL "hc256"; LFpL "lo"]
          ]
        )))))))))
    | _ => REdSkip
    end.
