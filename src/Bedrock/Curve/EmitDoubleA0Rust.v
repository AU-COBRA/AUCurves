(** * EmitDoubleA0Rust — write the a = 0 G1 doubling Rust bodies to disk.

    Driver only: no theorems.  Uses [Redirect] exactly as
    [Bedrock.Curve.EmitA3Rust] and [Bedrock.ExtractSafeRust] do.
    Excluded from the dune build (it writes files outside the build
    tree); run it by hand with

      rocq compile -R src/Bedrock Bedrock -Q fiat-crypto/src Crypto ... \
        src/Bedrock/Curve/EmitDoubleA0Rust.v

    Each output is the body of RCB 2015 Algorithm 9 (the a = 0
    complete doubling) for one curve, transcribed from
    [PointDoubleA0.rcb_double_a0_gallina] by
    [Bedrock.Curve.CurveDoubleA0RustCmd]. *)

Require Import Stdlib.Strings.String.
Require Import Bedrock.Curve.CurveDoubleA0RustCmd.

(* Without [string_scope] the result prints as [String.String (Ascii.Ascii
   ...)] cons cells; without the depth/width bumps it is elided with
   "...".  Both are needed for the output to be the Rust text. *)
Open Scope string_scope.
Set Printing Depth 1000000.
Set Printing Width 1000000.

Redirect "/tmp/a0emit/bn254_double"     Eval vm_compute in bn254_g1_double_a0_rs.
Redirect "/tmp/a0emit/bn256_double"     Eval vm_compute in bn256_g1_double_a0_rs.
Redirect "/tmp/a0emit/bn446_double"     Eval vm_compute in bn446_g1_double_a0_rs.
Redirect "/tmp/a0emit/bls12_381_double" Eval vm_compute in bls12_381_g1_double_a0_rs.
Redirect "/tmp/a0emit/bls12_377_double" Eval vm_compute in bls12_377_g1_double_a0_rs.
Redirect "/tmp/a0emit/bw6_761_double"   Eval vm_compute in bw6_761_g1_double_a0_rs.
