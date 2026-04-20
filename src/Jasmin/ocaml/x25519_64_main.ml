(** X25519-64 driver: thin wrapper around [Ocaml_compile.compile_funcs].
 *
 * The [X25519_64_jasmin_extracted.x25519_64_all_jasmin] type is structurally
 * identical to [Bls12_jasmin_extracted.bls12_all_jasmin] (both are
 * [jasmin_func list] from independent extractions of the same Coq type).
 * We use [Obj.magic] to coerce between them — the same trick the
 * universe-shim drivers ([ast_bridge_main.ml]) use, for the same reason
 * (two extractions can't share a type without the universe shim).
 *
 * Usage:
 *   x25519_64_main <output.s> [--verbose]
 *
 * Build:
 *   ocamlfind ocamlopt -package jasmin -linkpkg \
 *     x25519_64_jasmin_extracted.ml \
 *     bls12_jasmin_extracted.ml \
 *     ocaml_compile.ml \
 *     x25519_64_main.ml \
 *     -o x25519_64_main *)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  let funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic X25519_64_jasmin_extracted.x25519_64_all_jasmin in
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose ~funcs
