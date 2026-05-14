(** Lizard-extract driver.
 *
 *  Inverse-direction sibling of [lizard_inject_main.ml]: pipes
 *  [lizard_extract_inlined_func] (from [Lizard_Extract_Inlined.v])
 *  through [Ocaml_compile.compile_funcs], prepending the 3 extract-side
 *  FFI leaf stubs.
 *
 *  Usage:
 *    lizard_extract_main <output.s> [--func lizard_extract] [--verbose]
 *
 *  Build:
 *    ./build_drivers.sh lizard_extract
 *)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  let body_funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Lizard_extract_jasmin_extracted.lizard_extract_all_jasmin in
  let stub_funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Lizard_stubs_jasmin_extracted.lizard_extract_stubs in
  let funcs = body_funcs @ stub_funcs in
  Printf.eprintf "[lizard_extract_driver] body funcs: %d, stub funcs: %d, total: %d\n%!"
    (List.length body_funcs) (List.length stub_funcs) (List.length funcs);
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose ~funcs
