(** Ed25519-sign with-stubs driver.
 *
 *  Tier 4 / roadmap §9 path (b): feed jasminc the inlined sign body
 *  (from [Ed25519_Sign_Inlined.v], A6 commit c88a2f9) PLUS minimal
 *  empty-body stub [jasmin_func] entries for every FFI symbol the
 *  body references (from [Ed25519_Sign_StubLeaves.v]).
 *
 *  Expected outcome: jasminc's MakeReferenceArguments pass (16/30)
 *  finds every callee in the program, so the chain progresses past
 *  pass 15 (A6's empirical gate) and emits .s.
 *
 *  Usage:
 *    ed25519_sign_stubbed_main <output.s> [--func ed25519_sign] [--verbose]
 *
 *  Build:
 *    ./build_drivers.sh ed25519_sign_stubbed
 *)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  (* Sign body (from A6's Ed25519_Sign_Inlined extraction). *)
  let sign_funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Ed25519_sign_jasmin_extracted.ed25519_sign_all_jasmin in
  (* FFI leaf stubs. *)
  let stub_funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Ed25519_sign_stubs_jasmin_extracted.ed25519_sign_stubs in
  let funcs = sign_funcs @ stub_funcs in
  Printf.eprintf "[stubbed_driver] sign funcs: %d, stub funcs: %d, total: %d\n%!"
    (List.length sign_funcs) (List.length stub_funcs) (List.length funcs);
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose ~funcs
