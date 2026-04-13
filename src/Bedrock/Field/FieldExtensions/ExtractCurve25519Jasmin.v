(** * OCaml extraction of Curve25519 field ops for Jasmin compilation.

    Extracts the X25519 / ristretto255 field operations together with
    [to_jasmin_sized] so the OCaml driver can emit .jazz files.

    Two field size options:
    - field_size = 10: 10 × 32-bit unsaturated Solinas (RV32IM target)
    - field_size = 5:  5 × 64-bit unsaturated Solinas (x86-64 target)
    - field_size = 4:  4 × 64-bit saturated Solinas (x86-64, matches CryptOpt)

    Default: field_size = 5 for x86-64 (matches fiat-bedrock2 curve25519_64.c).

    Build:
      make EXTERNAL_DEPENDENCIES=1 \
        src/Bedrock/Field/FieldExtensions/ExtractCurve25519Jasmin.vo

    Output:
      src/Bedrock/Field/FieldExtensions/curve25519_jasmin_extracted.ml *)

From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
From Stdlib Require Import ZArith String Ascii.
Require Import bedrock2.Syntax.

Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadder.
Require Import Crypto.Bedrock.End2End.X25519.clamp.

Require Import Crypto.Bedrock.Field.FieldExtensions.ToJasmin.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** * Curve25519 field operations (from Field25519.v).

    These are the bedrock2 cmd ASTs for the field arithmetic:
    - fe25519_mul, fe25519_square, fe25519_add, fe25519_sub
    - fe25519_carry, fe25519_copy, fe25519_select_znz
    - fe25519_to_bytes, fe25519_from_bytes, fe25519_from_word
    - fe25519_scmula24 (multiply by a24 = 121665)
    - fe25519_inv (Bernstein's addition chain)

    Plus the X25519 functions:
    - ladderstep (Montgomery ladder step)
    - montladder (full 255-bit scalar multiplication)
    - x25519, x25519_base (API entry points)
    - clamp (scalar clamping) *)

Definition curve25519_field_funcs : list function_t :=
  Eval vm_compute in
    [ fe25519_mul; fe25519_square; fe25519_add; fe25519_sub;
      fe25519_carry; fe25519_carry_add; fe25519_carry_sub;
      fe25519_copy; fe25519_select_znz;
      fe25519_to_bytes; fe25519_from_bytes; fe25519_from_word;
      fe25519_scmula24; fe25519_inv ].

Definition curve25519_x25519_funcs : list function_t :=
  Eval vm_compute in
    [ ladderstep; montladder; ("x25519", x25519); ("x25519_base", x25519_base);
      ("clamp", clamp) ].

Definition curve25519_all_funcs : list function_t :=
  curve25519_field_funcs ++ curve25519_x25519_funcs.

(** Field size for Jasmin translation.

    For the 10-limb (32-bit) representation from Field25519.v:
      field_size = 10, each limb is 4 bytes, felem = 40 bytes

    For a 5-limb (64-bit) unsaturated representation:
      field_size = 5, each limb is 8 bytes, felem = 40 bytes

    For a 4-limb (64-bit) saturated representation (CryptOpt-compatible):
      field_size = 4, each limb is 8 bytes, felem = 32 bytes *)

Definition curve25519_field_size_32bit : Z := 10.  (** RV32IM target *)
Definition curve25519_field_size_64bit : Z := 5.   (** x86-64 unsaturated *)
Definition curve25519_field_size_saturated : Z := 4. (** x86-64 CryptOpt *)

(** * Extraction *)

Extraction "curve25519_jasmin_extracted"
  curve25519_all_funcs
  curve25519_field_size_32bit
  curve25519_field_size_64bit
  curve25519_field_size_saturated
  to_jasmin to_jasmin_sized
  tr_func tr_func_sized
  pp_func pp_module.
