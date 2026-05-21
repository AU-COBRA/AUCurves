(** BLS12-377 driver: thin wrapper around [Ocaml_compile.compile_funcs].
 *
 * Mirrors [bls12_main.ml] for the 377 curve.  Consumes 6 Fp leaves
 * (add/sub/mul/square/select_znz/felem_copy) from
 * [bls377_jasmin_extracted].  Same 6-limb wordsize as BLS12-381.
 *
 * Usage:
 *   bls377_main <output.s> [--func <name>] [--verbose]
 *
 * Build via build_drivers.sh bls377 (uses the bls12 alias trick to
 * present the source jasmin_func type to ocaml_compile.ml's typed
 * pipeline). *)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  let funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Bls377_jasmin_extracted.bls377_all_jasmin in
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose ~funcs
