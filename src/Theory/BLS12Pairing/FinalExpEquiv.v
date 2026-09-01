(** * Final exponentiation: h3 = (p^4 - p^2 + 1) / r.
 *
 * Proves that the h3 exponent used in the BLS12-381 final exponentiation
 * equals (p^4 - p^2 + 1) / r, the hard-part cofactor.
 *
 * NOTE: The DSD-optimized Gallina model [final_exp_hard_dsd] in Pairing.v
 * computes the WRONG exponent. The exponent
 *   p + p^2 + p^3 - x^4 + x^3 - 3x^2 - 2x - 2
 * does NOT equal h3 (it's ~1143 bits vs h3's ~1268 bits), and they
 * are not congruent mod r or mod Phi_12(p). The actual C code uses
 * the correct h3 array via square-and-multiply (bls12_final_exp),
 * NOT the DSD decomposition. A correct DSD implementation would need
 * the multi-scalar decomposition h3 = l0 + l1*p + l2*p^2 + l3*p^3.
 *)

From Stdlib Require Import ZArith.
Import BinInt.

Local Open Scope Z_scope.

Section BLS12_381_h3.

  (** BLS12-381 curve parameter (unsigned). *)
  Definition bls_x_abs : Z := 0xd201000000010000.

  (** BLS12-381 prime: p(x) = (x-1)^2 * (x^4-x^2+1) / 3 + x, x = -bls_x_abs. *)
  Definition bls_p : Z :=
    0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

  (** BLS12-381 subgroup order: r(x) = x^4 - x^2 + 1. *)
  Definition bls_r : Z :=
    0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001.

  (** Hard-part exponent h3 = (p^4 - p^2 + 1) / r.
      This is the 1268-bit value used in the square-and-multiply final exp. *)
  Definition h3_exp : Z :=
        0xe516c3f438e3ba79
      + 0xfa9912aae208ccf1 * 2^64
      + 0x905ce937335d5b68 * 2^128
      + 0xc71a2629b0dea236 * 2^192
      + 0x83774940996754c8 * 2^256
      + 0x21d160aeb6a1e799 * 2^320
      + 0x2ed0b283ed237db4 * 2^384
      + 0x915c97f36c6f1821 * 2^448
      + 0x67f17fcbde783765 * 2^512
      + 0x2378b9039096d1b7 * 2^576
      + 0x7988f8761bdc51dc * 2^640
      + 0x2076995003fc77a1 * 2^704
      + 0x827eca0ba621315b * 2^768
      + 0xe5a72bce8d63cb9f * 2^832
      + 0xf68f7764c28b6f8a * 2^896
      + 0x2f230063cf081517 * 2^960
      + 0x94506632528d6a9a * 2^1024
      + 0xd3cde88eeb996ca3 * 2^1088
      + 0xc0bd38c3195c899e * 2^1152
      + 0x000f686b3d807d01 * 2^1216.

  (** The prime satisfies the BLS12 parameterization. *)
  Lemma bls_p_param : bls_p = ((-bls_x_abs) - 1)^2 * ((-bls_x_abs)^4 - (-bls_x_abs)^2 + 1) / 3 + (-bls_x_abs).
  Proof. vm_compute. reflexivity. Qed.

  (** r satisfies the cyclotomic parameterization. *)
  Lemma bls_r_param : bls_r = (-bls_x_abs)^4 - (-bls_x_abs)^2 + 1.
  Proof. vm_compute. reflexivity. Qed.

  (** h3 is the hard-part cofactor (p^4 - p^2 + 1) / r. *)
  Lemma h3_is_cofactor : h3_exp = (bls_p^4 - bls_p^2 + 1) / bls_r.
  Proof. vm_compute. reflexivity. Qed.

  (** The division is exact. *)
  Lemma h3_exact_division : (bls_p^4 - bls_p^2 + 1) mod bls_r = 0.
  Proof. vm_compute. reflexivity. Qed.

  (** The corrected DSD (Hayashida-Hayasaka-Teruya, eprint 2020/875)
      computes f^{3*h3}. The gnark algorithm's exponent trace:
        3 + (|x|²-1+p²) * (|x|+1)² * (p-|x|) = 3*h3
      Verified numerically: *)
  Lemma dsd_corrected_computes_3h3 :
    let u := bls_x_abs in
    3 * h3_exp = 3 + (u^2 - 1 + bls_p^2) * (u + 1)^2 * (bls_p - u).
  Proof. native_compute. reflexivity. Qed.

End BLS12_381_h3.
