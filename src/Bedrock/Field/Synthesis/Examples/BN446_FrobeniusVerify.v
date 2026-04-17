(** * BN446 Frobenius constant verification.
    Uses BN_FrobeniusGeneric. BN446 has 7-limb Fp elements and xi = (2, 3). *)

Require Import Coq.ZArith.ZArith.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.BN_FrobeniusGeneric.

Local Open Scope Z_scope.

Definition p : Z := bn446_modulus.
Definition xi : Z * Z := (2, 3).  (* BN446 nonresidue *)

Lemma bn446_w_frob_c1_correct :
  let val := fp2_pow p xi ((p - 1) / 6) in
  to_mont448 p (fst val) = pack7 0x4F42FB173240CACF 0x41A6624C14E770DB 0x4CE482DDAEF1E09C
                                 0xACFB794D0EA9EB70 0x8E6475845F69F02F 0xD188D14E6F71BE65
                                 0x0CA5E41A2878689A /\
  to_mont448 p (snd val) = pack7 0x0B8C0C1CBA0162A2 0x039CE6E5C8948976 0xD48AB015DA2F897B
                                 0xFD77AA8DDC863E6C 0x25EAA23E38AC4FA8 0x3BBF3C8AC583EA9D
                                 0x1A2B7CB0A28128C2.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn446_gamma1_correct :
  let val := fp2_pow p xi ((p - 1) / 3) in
  to_mont448 p (fst val) = pack7 0xA9707F06A2911FE5 0x6CD56EF01CE2A9D1 0x83DAF2BFFA06227C
                                 0xB167E5173810465F 0xEC6829AD1B03A057 0x3D6454F6835050D2
                                 0x17E66D2B8D788C0C /\
  to_mont448 p (snd val) = pack7 0xF9756B04ABA2140A 0x9C8C9F7FE9506204 0x9BBCE8488D957CD9
                                 0x8C11B426417EE934 0x3CE3F9CC7B05A7FC 0x8831B0F3BB2056EB
                                 0x1CB419F8806EE62E.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn446_gamma2_correct :
  let val := fp2_pow p xi ((2 * (p - 1)) / 3) in
  to_mont448 p (fst val) = pack7 0x45E78B4FE63EE181 0xC4B27D3AF0DF7AE3 0xEE74A57CA979AB51
                                 0x7C90D7115B12CFA9 0xF9EF862CFF8602AD 0x0DA75398389DC684
                                 0x01454DB433D5A0C2 /\
  to_mont448 p (snd val) = pack7 0xC14D0635840B43D9 0xDAF080662FD4E161 0x6A0B5079634CD7FB
                                 0x85F6C9E09A3EBF87 0xEDA90A144A7C855A 0x4F66FFAE21471A09
                                 0x0F6E4C6307FA68AE.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn446_w_frob_p2_c1_correct :
  let val := fp2_pow p xi ((p*p - 1) / 6) in
  to_mont448 p (fst val) = pack7 0x5556CC5555553638 0x1323555556DEF555 0x60000001E0A00000
                                 0x000007C2000000AE 0x0019740000004BC0 0x0180000000A50000
                                 0x2000000156000000 /\
  snd val = 0.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn446_gamma1_p2_correct :
  let val := fp2_pow p xi ((p*p - 1) / 3) in
  to_mont448 p (fst val) = pack7 0x5557523555553909 0x1589955556E87955 0x110000022DBC0000
                                 0x0000086A000000B2 0x0019D28000005A84 0x027C000000B8B000
                                 0x1C00000156000000 /\
  snd val = 0.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bn446_gamma2_p2_correct :
  let val := fp2_pow p xi ((2 * (p*p - 1)) / 3) in
  to_mont448 p (fst val) = pack7 0xAAA946CAAAAACA2F 0xED346AAAA92266AA 0x26FFFFFE2A63FFFF
                                 0xFFFFF855FFFFFF52 0xFFE6997FFFFFB65B 0xFEA3FFFFFF5DCFFF
                                 0x03FFFFFEA9FFFFFF /\
  snd val = 0.
Proof. vm_compute. split; reflexivity. Qed.
