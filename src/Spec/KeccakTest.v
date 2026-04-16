(** * SHAKE-128 test vector validation. *)

From Stdlib Require Import ZArith NArith Lists.List Strings.Byte.
Import ListNotations.
Require Import Crypto.Spec.Keccak.

(** NIST test vector: SHAKE128("", 32).
    Expected: 7f 9c 2b a4 e8 8f 82 7d 61 60 45 50 76 05 85 3e
              d7 3b 80 93 f6 ef bc 88 eb 1a 6e ac fa 66 ef 26 *)
Definition expected_first_byte : N := 0x7f.
Definition expected_last_byte : N := 0x26.

Definition test_output := Eval vm_compute in SHAKE128 [] 32.

Definition first_byte := Eval vm_compute in Byte.to_N (List.hd Byte.x00 test_output).
Definition last_byte := Eval vm_compute in Byte.to_N (List.last test_output Byte.x00).
Definition output_len := Eval vm_compute in List.length test_output.

Lemma shake128_empty_length : output_len = 32%nat.
Proof. reflexivity. Qed.

Lemma shake128_empty_first_byte : first_byte = 0x7f%N.
Proof. reflexivity. Qed.

Lemma shake128_empty_last_byte : last_byte = 0x26%N.
Proof. reflexivity. Qed.
