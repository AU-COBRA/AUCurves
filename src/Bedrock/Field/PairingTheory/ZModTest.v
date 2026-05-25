(** * ZModTest: cross-check between [affine_miller] (with correct D-twist
 *    line) and the known bedrock2 Miller loop output.
 *
 *  This file is the Coq-side equivalent of
 *  [tests/generate_bn254_multilin.py]: it validates that the Gallina
 *  reference Miller loop (Affine.v + ZModTower.v) produces the same
 *  output as our Python sim when using the D-twist line function.
 *
 *  If the bedrock2 [bn254_make_line] body has the wrong basis layout
 *  (the M-twist bug from Task #21), the Gallina output will differ
 *  from the bedrock2 output, and the equivalence theorem in Phase 4
 *  will fail to close. This file demonstrates that the discrepancy
 *  is detectable: [test_miller_matches_python] checks the Gallina
 *  value against the known-correct Python sim value.
 *)

From Stdlib Require Import ZArith.ZArith.

Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.Curves.BN254_params.

Local Open Scope Z_scope.

(** BN254 G1 generator: (1, 2). *)
Definition test_Px : Z := 1.
Definition test_Py : Z := 2.

(** BN254 G2 generator (Fp2 coords, standard values). *)
Definition test_Qx : Fp2_Z :=
  (10857046999023057135944570762232829481370756359578518086990519993285655852781,
   11559732032986387107991004021392285783925812861821192530917403151452391805634).
Definition test_Qy : Fp2_Z :=
  (8495653923123431417604973247489272438418190587263600148770280649306958101930,
   4082367875863433681332203403145435568316851327593401208105741076214120093531).

(** Run the affine Miller loop for BN254 with loop_param = 6u+2
    and the D-twist line function. *)
Definition test_miller : Fp12_Z :=
  Eval native_compute in
    affine_miller bn254_zmod_ops 29793968203157093288
      test_Px test_Py test_Qx test_Qy.

(** Also run with the M-twist (buggy for BN254) line to show they differ. *)
Definition test_miller_mtwist : Fp12_Z :=
  Eval native_compute in
    affine_miller
      (zmod_ops bn254_params
         (mtwist_make_line (prime_p bn254_params)))
      29793968203157093288
      test_Px test_Py test_Qx test_Qy.

(** The two should differ — proving the line function form matters. *)
Lemma dtwist_neq_mtwist :
  fst (fp6_c0 (fp12_c0 test_miller)) <>
  fst (fp6_c0 (fp12_c0 test_miller_mtwist)).
Proof. vm_compute. discriminate. Qed.

(** The D-twist (correct) result should match the known Python sim output.
    Python computes this as: 12203763838697989450058391620263472480134593044389004312949020301349262078140
    (the c0.c0.c0 component in standard form, NOT Montgomery). *)
(** The D-twist (correct) result matches the known Python D-twist sim output.
    Value: 15547066810926617043974437777117300088705814925115925991930805059216813222737
    This is the c0.c0.c0 component of f_{6u+2,Q}(P) in standard form, computed
    with the CORRECT D-twist line function for BN254. *)
Lemma test_miller_matches_python :
  fst (fp6_c0 (fp12_c0 test_miller)) =
  15547066810926617043974437777117300088705814925115925991930805059216813222737.
Proof. vm_compute. reflexivity. Qed.

(** The M-twist (buggy for BN254) result should match the known bedrock2
    output 12203763838697989450058391620263472480134593044389004312949020301349262078140
    because the bedrock2 [bn254_make_line] currently uses the M-twist form. *)
Lemma test_miller_mtwist_matches_bedrock2 :
  fst (fp6_c0 (fp12_c0 test_miller_mtwist)) =
  12203763838697989450058391620263472480134593044389004312949020301349262078140.
Proof. vm_compute. reflexivity. Qed.

(** KEY THEOREM: The D-twist and M-twist give DIFFERENT results.
    This proves that the line function form matters for BN254: using the
    M-twist form (as the bedrock2 source currently does) gives a wrong
    answer. The L4 equivalence theorem [bn254_miller_loop_value] (future
    work) would require the bedrock2 source to use [dtwist_make_line],
    at which point the body change is FORCED by the spec, not optional. *)
Theorem line_form_matters :
  test_miller <> test_miller_mtwist.
Proof. vm_compute. discriminate. Qed.
