(** BW6-761 driver: thin wrapper around [Ocaml_compile.compile_funcs].
 *
 * Mirrors [bls377_main.ml] for the 12-limb BW6-761 outer-curve field.
 * Consumes 5 Fp leaves (add/sub/mul/square/select_znz).
 *
 * Usage:
 *   bw6_761_main <output.s> [--func <name>] [--verbose]
 *
 * Build via build_drivers.sh bw6_761. *)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  let funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Bw6_761_jasmin_extracted.bw6_761_all_jasmin in
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose ~funcs
