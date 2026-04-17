(** * BN254 Frobenius constant verification.
    Uses BN_FrobeniusGeneric for shared infrastructure (fp2 ops, packing). *)

Require Import Coq.ZArith.ZArith.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.BN_FrobeniusGeneric.

Local Open Scope Z_scope.

Definition p : Z := bn254_modulus.
Definition xi : Z * Z := (9, 1).  (* BN254 nonresidue *)

(* === p^1 Frobenius constants === *)

Lemma bn254_w_frob_c1_correct :
  let val := fp2_pow p xi ((p - 1) / 6) in
  to_mont256 p (fst val) = pack4 0xaf9ba69633144907 0xca6b1d7387afb78a
                                 0x11bded5ef08a2087 0x02f34d751a1f3a7c /\
  to_mont256 p (snd val) = pack4 0xa222ae234c492d72 0xd00f02a4565de15b
                                 0xdc2ff3a253dfc926 0x10a75716b3899551.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn254_gamma1_correct :
  let val := fp2_pow p xi ((p - 1) / 3) in
  to_mont256 p (fst val) = pack4 0xb5773b104563ab30 0x347f91c8a9aa6454
                                 0x7a007127242e0991 0x1956bcd8118214ec /\
  to_mont256 p (snd val) = pack4 0x6e849f1ea0aa4757 0xaa1c7b6d89f89141
                                 0xb6e713cdfae0ca3a 0x26694fbb4e82ebc3.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn254_gamma2_correct :
  let val := fp2_pow p xi ((2 * (p - 1)) / 3) in
  to_mont256 p (fst val) = pack4 0x7361d77f843abe92 0xa5bb2bd3273411fb
                                 0x9c941f314b3e2399 0x15df9cddbb9fd3ec /\
  to_mont256 p (snd val) = pack4 0x5dddfd154bd8c949 0x62cb29a5a4445b60
                                 0x37bc870a0c7dd2b9 0x24830a9d3171f0fd.
Proof. vm_compute. split; reflexivity. Qed.

(* === p^2 Frobenius constants (real-only) === *)

Lemma bn254_w_frob_p2_c1_correct :
  let val := fp2_pow p xi ((p*p - 1) / 6) in
  to_mont256 p (fst val) = pack4 0xca8d800500fa1bf2 0xf0c5d61468b39769
                                 0x0e201271ad0d4418 0x04290f65bad856e6 /\
  snd val = 0.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn254_gamma1_p2_correct :
  let val := fp2_pow p xi ((p*p - 1) / 3) in
  to_mont256 p (fst val) = pack4 0x3350c88e13e80b9c 0x7dce557cdb5e56b9
                                 0x6001b4b8b615564a 0x2682e617020217e0 /\
  snd val = 0.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn254_gamma2_p2_correct :
  let val := fp2_pow p xi ((2 * (p*p - 1)) / 3) in
  to_mont256 p (fst val) = pack4 0x71930c11d782e155 0xa6bb947cffbe3323
                                 0xaa303344d4741444 0x2c3b3f0d26594943 /\
  snd val = 0.
Proof. vm_compute. split; reflexivity. Qed.
