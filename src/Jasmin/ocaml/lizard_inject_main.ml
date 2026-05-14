(** Lizard-inject driver.
 *
 *  Pipes [lizard_inject_inlined_func] (from [Lizard_Inject_Inlined.v])
 *  through [Ocaml_compile.compile_funcs], prepending the 3 inject-side
 *  FFI leaf stubs (from [Lizard_StubLeaves.v]) so jasminc's
 *  MakeReferenceArguments pass (16/30) finds every callee.
 *
 *  Mirror of [ed25519_sign_stubbed_main.ml] for the simpler Lizard
 *  protocol — only 2 stack locals + 3 FFI calls vs. Ed25519 sign's
 *  13 + 14.  Expected to reach the same point in the jasminc pipeline
 *  as Ed25519 sign (or further, since register pressure is lower).
 *
 *  Usage:
 *    lizard_inject_main <output.s> [--func lizard_inject] [--verbose]
 *
 *  Build:
 *    ./build_drivers.sh lizard_inject
 *)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  let body_funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Lizard_inject_jasmin_extracted.lizard_inject_all_jasmin in
  let stub_funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Lizard_stubs_jasmin_extracted.lizard_inject_stubs in
  let funcs = body_funcs @ stub_funcs in
  Printf.eprintf "[lizard_inject_driver] body funcs: %d, stub funcs: %d, total: %d\n%!"
    (List.length body_funcs) (List.length stub_funcs) (List.length funcs);
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose ~funcs
