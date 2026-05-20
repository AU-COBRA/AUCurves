(** Fe25519-leaves driver: pipe the 5 wrapped leaf programs through
    [Ocaml_compile.compile_funcs] to emit x86-64 assembly.

    Mirrors [ed25519_sign_main.ml] / [x25519_64_main.ml].

    STATUS (2026-05-20): structural mismatch flagged.  The existing
    [Ocaml_compile.compile_funcs] consumes the AUCurves IR
    [Bedrock.Jasmin.Core.jasmin_func] (bedrock2-Syntax-flavoured
    intermediate produced by [tr_func_sized] + [polish_func]).  Our
    [Fe25519_Leaves.v] emits Jasmin's NATIVE types
    [seq (funname * _fundef unit)] directly via [WrapFundef.wrap_prog].
    These are STRUCTURALLY DIFFERENT records — Obj.magic compiles but
    breaks at runtime.

    Three ways to bridge (the [Obj.magic] line below is the
    placeholder for the proper fix):

      (a)  Re-route Fe25519_Leaves.v through the bedrock2-Syntax IR:
           [to_bedrock_cmd] from RustCmdToC, then build a function_t
           list and apply [tr_func_sized 5 + polish_func] — matches
           the bls12/x25519 pattern exactly.  Existing driver works
           unchanged.  Recommended.

      (b)  Extend [ocaml_compile.ml] with a new entry point
           [compile_native_fundefs : (funname * _fundef unit) list →
           unit] that takes Jasmin's native types directly.

      (c)  Write a structural map from [(funname * _fundef) list] to
           [jasmin_func list] in OCaml.  Equivalent to (b) but as a
           separate file.

    Usage (after fix):
      fe25519_leaves_main <output.s> [--verbose]
      fe25519_leaves_main <output.s> --func fe25519_mul [--verbose]

    Build (after `dune build src/Jasmin/extractions/Fe25519_Leaves.vo`):
      ocamlfind ocamlopt -package jasmin -linkpkg \
        fe25519_leaves_jasmin_extracted.ml \
        bls12_jasmin_extracted.ml \
        ocaml_compile.ml \
        fe25519_leaves_main.ml \
        -o fe25519_leaves_main
*)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  let funcs : Bls12_jasmin_extracted.jasmin_func list =
    (* STRUCTURAL MISMATCH (see header).  This Obj.magic does NOT
       work because Fe25519_Leaves.v emits seq (funname * _fundef)
       not list jasmin_func.  Path (a) above is the correct fix.   *)
    Obj.magic Fe25519_leaves_jasmin_extracted.fe25519_all_jasmin in
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose ~funcs
