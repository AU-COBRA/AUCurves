(** * BLS12-377 h3 exponent for final exponentiation hard part.
    h3 = (p^4 - p^2 + 1) / r, 1255 bits, 20 × 64-bit limbs. *)

From Stdlib Require Import ZArith.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Word.Interface.
Require Import bedrock2.BasicC64Semantics.
Import BinInt.

Local Open Scope Z_scope.

Section H3.
  Existing Instance Bitwidth64.BW64.

  (* h3 exponent in little-endian 64-bit limbs *)
  Import List.ListNotations.
  Local Open Scope list_scope.
  Definition bls377_h3_words : list (@word.rep 64 BasicC64Semantics.word) :=
    [ @word.of_Z 64 BasicC64Semantics.word 0x0000000000000001;
      @word.of_Z 64 BasicC64Semantics.word 0x2e16ba8860000000;
      @word.of_Z 64 BasicC64Semantics.word 0x68c0eaeea22e6800;
      @word.of_Z 64 BasicC64Semantics.word 0x719b834b69044687;
      @word.of_Z 64 BasicC64Semantics.word 0xf4f6974b4ff0fa27;
      @word.of_Z 64 BasicC64Semantics.word 0x27dc8f4db069bf65;
      @word.of_Z 64 BasicC64Semantics.word 0xabcaf63f0a34fcb8;
      @word.of_Z 64 BasicC64Semantics.word 0x0bd948d5f4548283;
      @word.of_Z 64 BasicC64Semantics.word 0xaae0551dffcf72fb;
      @word.of_Z 64 BasicC64Semantics.word 0xd1eefd89535f9b5a;
      @word.of_Z 64 BasicC64Semantics.word 0xfcd1c3fa1470f8b2;
      @word.of_Z 64 BasicC64Semantics.word 0x1a8d889828282015;
      @word.of_Z 64 BasicC64Semantics.word 0x5497a9781d812991;
      @word.of_Z 64 BasicC64Semantics.word 0xcc65eca9c9678a84;
      @word.of_Z 64 BasicC64Semantics.word 0xc548afd84225b34c;
      @word.of_Z 64 BasicC64Semantics.word 0xbef98d9c2cce3b25;
      @word.of_Z 64 BasicC64Semantics.word 0x3b4074a5448da5cf;
      @word.of_Z 64 BasicC64Semantics.word 0x0576728e56efc3bf;
      @word.of_Z 64 BasicC64Semantics.word 0x0774d7d810d5cbdf;
      @word.of_Z 64 BasicC64Semantics.word 0x0000006d616e4372 ].

  Definition bls377_h3_num_limbs := 20%nat.

  (* BLS12-377 parameter u *)
  Definition bls377_u : Z := 0x8508c00000000001.
  Definition bls377_u_pos : positive := 0x8508c00000000001%positive.

  (* 6u+2 bit decomposition for Miller loop (MSB to LSB, skip leading 1) *)
  (* 6u+2 = 0x31e34800000000008, 66 bits, hamming weight 11 *)
  Definition bls377_6u2_bits : list bool :=
    [ true; false; false; false; true; true; true; true;
      false; false; false; true; true; false; true; false;
      false; true; false; false; false; false; false; false;
      false; false; false; false; false; false; false; false;
      false; false; false; false; false; false; false; false;
      false; false; false; false; false; false; false; false;
      false; false; false; false; false; false; false; false;
      false; false; false; false; false; true; false; false;
      false ].

End H3.
