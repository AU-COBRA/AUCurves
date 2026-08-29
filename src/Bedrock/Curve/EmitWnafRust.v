(** * EmitWnafRust — write the w=4 wNAF scalar-multiplication Rust
      drivers to disk.

    Driver only: no theorems.  Companion to [Curve.EmitA3Rust]; both are
    excluded from the dune build because they write files via [Redirect].
    The emitted text is compared byte-for-byte against the shipped
    [p{224,256,384}-safe-rust/src/scalar_mul_extracted.rs]. *)

Require Import Stdlib.Strings.String.
Require Import Bedrock.Curve.NistWnafScalarMultRustCmd.

Open Scope string_scope.
Set Printing Depth 1000000.
Set Printing Width 1000000.

Redirect "/tmp/wnafemit/p224" Eval vm_compute in p224_wnaf_rs.
Redirect "/tmp/wnafemit/p256" Eval vm_compute in p256_wnaf_rs.
Redirect "/tmp/wnafemit/p384" Eval vm_compute in p384_wnaf_rs.
