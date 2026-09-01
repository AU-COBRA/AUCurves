(** Same statement as [divsteps590.v] but proved via [native_compute] +
    [reflexivity], avoiding the [Qed] kernel re-check.  Backup file:
    if [divsteps590.v]'s [vm_cast_no_check] route is too slow at [Qed],
    use this one. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Definition p25519 : Z :=
  0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Lemma p25519_certificate_590_native :
  ZMap.Empty (N.iter 590 (processDivstep_half p25519) state0_half).
Proof.
apply ZMap.is_empty_2.
Time native_compute.
reflexivity.
Time Qed.

Definition p25519_iters_native : N := 590.
