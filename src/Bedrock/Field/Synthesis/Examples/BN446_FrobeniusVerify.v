(** * BN446 Frobenius constant verification.
    Uses BN_FrobeniusGeneric. BN446 has 7-limb Fp elements and xi = (1, 9).
    The limbs are those of the loaders in BN446_Pairing.v.  Each lemma is one
    kernel-checked native computation ([native_cast_no_check]). *)

Require Import Coq.ZArith.ZArith.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.BN_FrobeniusGeneric.

Local Open Scope Z_scope.

Definition p : Z := bn446_modulus.
Definition xi : Z * Z := (1, 9).  (* BN446 nonresidue, Curves/BN446_params.v *)

Lemma bn446_w_frob_c1_correct :
  let val := fp2_pow p xi ((p - 1) / 6) in
  to_mont448 p (fst val) = pack7 0x2A07FE15CBD3B798 0x01225DB01DB5A838 0x9994312142903A3D
                                 0x2BFC47EE50AF84EE 0x5023EEB37F74D04B 0xDA8DABD847F6A920
                                 0x0A18FEE90B4A4762 /\
  to_mont448 p (snd val) = pack7 0x31F8B1977554D2A4 0xC8C8F5131A405EB5 0x1919B9FCD2E3DB2E
                                 0x610830B9AD9891E6 0x8DAF70EE964EFF37 0xBA1308A4535F56B6
                                 0x1F9196DA43055B76.
Proof. native_cast_no_check (conj (eq_refl (pack7 0x2A07FE15CBD3B798 0x01225DB01DB5A838 0x9994312142903A3D
                                 0x2BFC47EE50AF84EE 0x5023EEB37F74D04B 0xDA8DABD847F6A920
                                 0x0A18FEE90B4A4762)) (eq_refl (pack7 0x31F8B1977554D2A4 0xC8C8F5131A405EB5 0x1919B9FCD2E3DB2E
                                 0x610830B9AD9891E6 0x8DAF70EE964EFF37 0xBA1308A4535F56B6
                                 0x1F9196DA43055B76))). Qed.

Lemma bn446_gamma1_correct :
  let val := fp2_pow p xi ((p - 1) / 3) in
  to_mont448 p (fst val) = pack7 0x130F067A5B034C8C 0xB5F72CD40D296C56 0x2F984093C44F9285
                                 0x3033252A4A04F8DC 0x748F6D0A09371944 0x6C600C0F7A588D05
                                 0x195319F251A4B209 /\
  to_mont448 p (snd val) = pack7 0x093497F3AB410B23 0x846BBDA6C65D14EF 0x70A818D84F6DC6C9
                                 0x896AF0D1313903D1 0x28B3FD6131E29DED 0x33A80BD42B0FF2DB
                                 0x1D089B7A773DCE17.
Proof. native_cast_no_check (conj (eq_refl (pack7 0x130F067A5B034C8C 0xB5F72CD40D296C56 0x2F984093C44F9285
                                 0x3033252A4A04F8DC 0x748F6D0A09371944 0x6C600C0F7A588D05
                                 0x195319F251A4B209)) (eq_refl (pack7 0x093497F3AB410B23 0x846BBDA6C65D14EF 0x70A818D84F6DC6C9
                                 0x896AF0D1313903D1 0x28B3FD6131E29DED 0x33A80BD42B0FF2DB
                                 0x1D089B7A773DCE17))). Qed.

Lemma bn446_gamma2_correct :
  let val := fp2_pow p xi ((2 * (p - 1)) / 3) in
  to_mont448 p (fst val) = pack7 0x03BFD8E9F657C7C1 0xD1B2007299E015ED 0x66E1EDB333F452D7
                                 0x1F29FC5B04CEA7D1 0xDD080B866BE24717 0x9F86F63310BFBE40
                                 0x0DF07F06892CA535 /\
  to_mont448 p (snd val) = pack7 0xACECC09B3A45E11E 0x2AD0BCEB3BA09E13 0xD879CECB4E98633B
                                 0xCBE3C5EE3A4DC56F 0xF3CC12149C07D88E 0x85EF00A51E52F06F
                                 0x19D41F8EE2C196D1.
Proof. native_cast_no_check (conj (eq_refl (pack7 0x03BFD8E9F657C7C1 0xD1B2007299E015ED 0x66E1EDB333F452D7
                                 0x1F29FC5B04CEA7D1 0xDD080B866BE24717 0x9F86F63310BFBE40
                                 0x0DF07F06892CA535)) (eq_refl (pack7 0xACECC09B3A45E11E 0x2AD0BCEB3BA09E13 0xD879CECB4E98633B
                                 0xCBE3C5EE3A4DC56F 0xF3CC12149C07D88E 0x85EF00A51E52F06F
                                 0x19D41F8EE2C196D1))). Qed.

Lemma bn446_w_frob_p2_c1_correct :
  let val := fp2_pow p xi ((p*p - 1) / 6) in
  to_mont448 p (fst val) = pack7 0xAAA8C0EAAAAAC75E 0xEACE2AAAA918E2AA 0x75FFFFFDDD47FFFF
                                 0xFFFFF7ADFFFFFF4E 0xFFE63AFFFFFFA797 0xFDA7FFFFFF4A1FFF
                                 0x07FFFFFEA9FFFFFF /\
  snd val = 0.
Proof. native_cast_no_check (conj (eq_refl (pack7 0xAAA8C0EAAAAAC75E 0xEACE2AAAA918E2AA 0x75FFFFFDDD47FFFF
                                 0xFFFFF7ADFFFFFF4E 0xFFE63AFFFFFFA797 0xFDA7FFFFFF4A1FFF
                                 0x07FFFFFEA9FFFFFF)) (eq_refl 0)). Qed.

Lemma bn446_gamma1_p2_correct :
  let val := fp2_pow p xi ((p*p - 1) / 3) in
  to_mont448 p (fst val) = pack7 0xAAA946CAAAAACA2F 0xED346AAAA92266AA 0x26FFFFFE2A63FFFF
                                 0xFFFFF855FFFFFF52 0xFFE6997FFFFFB65B 0xFEA3FFFFFF5DCFFF
                                 0x03FFFFFEA9FFFFFF /\
  snd val = 0.
Proof. native_cast_no_check (conj (eq_refl (pack7 0xAAA946CAAAAACA2F 0xED346AAAA92266AA 0x26FFFFFE2A63FFFF
                                 0xFFFFF855FFFFFF52 0xFFE6997FFFFFB65B 0xFEA3FFFFFF5DCFFF
                                 0x03FFFFFEA9FFFFFF)) (eq_refl 0)). Qed.

Lemma bn446_gamma2_p2_correct :
  let val := fp2_pow p xi ((2 * (p*p - 1)) / 3) in
  to_mont448 p (fst val) = pack7 0x5557523555553909 0x1589955556E87955 0x110000022DBC0000
                                 0x0000086A000000B2 0x0019D28000005A84 0x027C000000B8B000
                                 0x1C00000156000000 /\
  snd val = 0.
Proof. native_cast_no_check (conj (eq_refl (pack7 0x5557523555553909 0x1589955556E87955 0x110000022DBC0000
                                 0x0000086A000000B2 0x0019D28000005A84 0x027C000000B8B000
                                 0x1C00000156000000)) (eq_refl 0)). Qed.

Lemma bn446_q1_y_const_correct :
  let val := fp2_pow p xi ((p - 1) / 2) in
  to_mont448 p (fst val) = pack7 0x1B9A8C176F4F9149 0x2BE2F595B319EF56 0xAD7C18C7ADD00FFA
                                 0x526DC47E7108CA75 0x675EE5CB05F4550D 0x70490B9E04F21723
                                 0x00DCB7CA19A14D2A /\
  to_mont448 p (snd val) = pack7 0x3BF4BE7B7E25491F 0x21659B4985ADD9B4 0x14D4E64F15C2AC71
                                 0x0928A41361E48846 0x99B538FA1D1B265D 0x7E49014A725469AE
                                 0x08188632E6674176.
Proof. native_cast_no_check (conj (eq_refl (pack7 0x1B9A8C176F4F9149 0x2BE2F595B319EF56 0xAD7C18C7ADD00FFA
                                 0x526DC47E7108CA75 0x675EE5CB05F4550D 0x70490B9E04F21723
                                 0x00DCB7CA19A14D2A)) (eq_refl (pack7 0x3BF4BE7B7E25491F 0x21659B4985ADD9B4 0x14D4E64F15C2AC71
                                 0x0928A41361E48846 0x99B538FA1D1B265D 0x7E49014A725469AE
                                 0x08188632E6674176))). Qed.
