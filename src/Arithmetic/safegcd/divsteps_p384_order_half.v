(** * O'Connor convex-hull certificate for the NIST P-384 group order, δ₀ = 1/2.

    Companion of [divsteps_p384_half.v], which carries the same certificate for
    the P-384 base field prime.  Inversion modulo the group order is what ECDSA
    signing and verification need; inversion modulo the base field prime is what
    point arithmetic needs.

    Iteration count [N = 885]: paper Theorem 1 gives ⌈(9437·384 + 1)/4096⌉ = 885
    as a function of the bit length alone, so the base field prime and the group
    order — both 384-bit — share it.  For this modulus the bound is tight: the
    extracted framework ([multi_curve_half_driver], OCaml/Zarith) reports the
    state still non-empty after 875 divsteps and empty after 885. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

(** Order of the NIST P-384 base point (FIPS 186-4, D.1.2.4). *)
Definition p384_n : Z :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973.

Definition p384_order_M : Z := p384_n.

(** The numeral is the P-384 group order: its top 192 bits are all ones, and
    the low 192 bits are the value FIPS 186-4 D.1.2.4 tabulates. *)
Lemma p384_n_correct :
  p384_n
  = 2^384 - 2^192
    + 0xc7634d81f4372ddf581a0db248b0a77aecec196accc52973.
Proof. vm_compute. reflexivity. Qed.

(** Decimal expansion, as printed in FIPS 186-4 D.1.2.4. *)
Lemma p384_n_decimal :
  p384_n
  = 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643.
Proof. vm_compute. reflexivity. Qed.

(** **Certificate**: the convex-hull algorithm converges to the empty state in
    885 divsteps for the P-384 group order under δ₀ = 1/2.

    Status: the kernel conversion below has not been run to completion in this
    tree.  [vm_cast_no_check] emits a [VMcast], which the kernel discharges with
    the bytecode VM whatever [-native-compiler] is set to; the native path needs
    [native_cast_no_check] instead.  Truncating the computation to its first N
    iterations at this width costs 5.6 s (N=50), 120 s (N=100) and over 1800 s
    (N=200) under the VM, and 1.9 s, 30 s, 790 s under [native_cast_no_check],
    while the extracted framework does the whole 885 in 317 s.  Carrying that
    overhead ratio forward puts a monolithic kernel check at hours to days, in
    line with the 2-7 days recorded for the 381-bit δ₀ = 1 certificate in
    [OPTIMIZATION.md]; the checkpointed and extraction-assisted routes described
    there are what make this size tractable. *)
Lemma p384_order_half_certificate :
  ZMap.Empty (N.iter 885 (processDivstep_half p384_order_M) state0_half).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Definition p384_order_half_iters : N := 885.
