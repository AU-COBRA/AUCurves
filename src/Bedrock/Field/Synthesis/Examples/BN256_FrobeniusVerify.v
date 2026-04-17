(** * BN256 Frobenius constant verification.
    Uses BN_FrobeniusGeneric for shared infrastructure. *)

Require Import Coq.ZArith.ZArith.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.BN_FrobeniusGeneric.

Local Open Scope Z_scope.

Definition p : Z := bn256_modulus.
Definition xi : Z * Z := (3, 1).  (* BN256 nonresidue *)

Lemma bn256_w_frob_c1_correct :
  let val := fp2_pow p xi ((p - 1) / 6) in
  to_mont256 p (fst val) = pack4 0x7407634dd9cca958 0x36d5bd6c7afb8f26
                                 0xf4b1c32cebd880fa 0x06aa7869306f455f /\
  to_mont256 p (snd val) = pack4 0x25af52988477cdb7 0x3d81a455ddced86a
                                 0x227d012e872c2431 0x0179198d3ea65d05.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn256_gamma1_correct :
  let val := fp2_pow p xi ((p - 1) / 3) in
  to_mont256 p (fst val) = pack4 0xf8606916d3816f2c 0x1e5c0d7926de927e
                                 0xbc45f3946d81185e 0x80752a25aa738091 /\
  to_mont256 p (snd val) = pack4 0x4f59e37c01832e57 0xae6be39ac2bbbfe4
                                 0xe04ea1bb697512f8 0x3097caa8fc40e10e.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn256_gamma2_correct :
  let val := fp2_pow p xi ((2 * (p - 1)) / 3) in
  to_mont256 p (fst val) = pack4 0x4d2ea218872f3d2c 0x2fcb27fc4abe7b69
                                 0xd31d972f0e88ced9 0x53adc04a00a73b15 /\
  to_mont256 p (snd val) = pack4 0x51678e7469b3c52a 0x4fb98f8b13319fc9
                                 0x29b2254db3f1df75 0x1c044935a3d22fb2.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn256_w_frob_p2_c1_correct :
  let val := fp2_pow p xi ((p*p - 1) / 6) in
  to_mont256 p (fst val) = pack4 0xe21a761d259c78af 0x06358fa3f5e84f7e
                                 0xb7c444d01ac33f0d 0x35a9333f6e50d058 /\
  snd val = 0.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn256_gamma1_p2_correct :
  let val := fp2_pow p xi ((p*p - 1) / 3) in
  to_mont256 p (fst val) = pack4 0x12d3cef5e1ada57d 0xe2eca1463753babb
                                 0x0ca41e40ddccf750 0x551337060397e04c /\
  snd val = 0.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn256_gamma2_p2_correct :
  let val := fp2_pow p xi ((2 * (p*p - 1)) / 3) in
  to_mont256 p (fst val) = pack4 0x3642364f386c1db8 0xe825f92d2acd661f
                                 0xf2aba7e846c19d14 0x5a0bcea3dc52b7a0 /\
  snd val = 0.
Proof. vm_compute. split; reflexivity. Qed.
