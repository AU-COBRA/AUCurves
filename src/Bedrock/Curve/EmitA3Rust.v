(** * EmitA3Rust — write the A3 (a = -3) G1 add/double Rust bodies to disk.

    Driver only: no theorems.  Uses [Redirect] exactly as
    [Bedrock.ExtractSafeRust] does.  Excluded from the dune build (it
    writes files into the source tree); run it by hand with

      rocq compile -R src/Bedrock Bedrock -Q fiat-crypto/src Crypto ... \
        src/Bedrock/Curve/EmitA3Rust.v

    The emitted text is compared byte-for-byte against the shipped
    [p{224,256,384}-safe-rust/src/g1_a3_extracted.rs]. *)

Require Import Stdlib.Strings.String.
Require Import Bedrock.Curve.NistA3RustCmd.

(* Without [string_scope] the result prints as [String.String (Ascii.Ascii
   ...)] cons cells; without the depth/width bumps it is elided with
   "...".  Both are needed for the output to be the Rust text. *)
Open Scope string_scope.
Set Printing Depth 1000000.
Set Printing Width 1000000.

Redirect "/tmp/a3emit/p224_add"    Eval vm_compute in p224_g1_add_a3_rs.
Redirect "/tmp/a3emit/p224_double" Eval vm_compute in p224_g1_double_a3_rs.
Redirect "/tmp/a3emit/p256_add"    Eval vm_compute in p256_g1_add_a3_rs.
Redirect "/tmp/a3emit/p256_double" Eval vm_compute in p256_g1_double_a3_rs.
Redirect "/tmp/a3emit/p384_add"    Eval vm_compute in p384_g1_add_a3_rs.
Redirect "/tmp/a3emit/p384_double" Eval vm_compute in p384_g1_double_a3_rs.
