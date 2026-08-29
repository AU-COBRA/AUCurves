(** * CheckBNDouble — axiom check for the Algorithm 9 rebinding.

    Driver only, no theorems of its own.  Confirms that rebinding
    "curve_double" from [PointDouble.point_double_body] (the Jacobian
    dbl-2009-l body) to [PointDoubleA0.rcb_double_a0_body] introduced no
    axiom, on all three BN curves, and reports what each per-curve
    correctness theorem now rests on.

    Excluded from the dune build; run by hand. *)

Require Import Bedrock.Field.Synthesis.Examples.BN254_CurveOps.
Require Import Bedrock.Field.Synthesis.Examples.BN256_CurveOps.
Require Import Bedrock.Field.Synthesis.Examples.BN446_CurveOps.

Print Assumptions bn254_point_double_correct.
Print Assumptions bn256_point_double_correct.
Print Assumptions bn446_point_double_correct.

Print Assumptions bn254_double_is_curve_add.
Print Assumptions bn256_double_is_curve_add.
Print Assumptions bn446_double_is_curve_add.
