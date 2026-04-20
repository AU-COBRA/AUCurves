(** BLS12-381 driver: thin wrapper around [Ocaml_compile.compile_funcs].
 *
 * Replaces the legacy entry point at the bottom of the old
 * [compile_direct.ml].
 *
 * Usage:
 *   bls12_main <output.s> [--func <name>] [--verbose]
 *
 * Build:
 *   ocamlfind ocamlopt -package jasmin -linkpkg \
 *     bls12_jasmin_extracted.ml \
 *     ocaml_compile.ml \
 *     bls12_main.ml \
 *     -o bls12_main *)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose
    ~funcs:Bls12_jasmin_extracted.bls12_all_jasmin
