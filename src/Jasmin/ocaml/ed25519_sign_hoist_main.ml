(** Ed25519-sign-hoist driver: pipe the inlined sign body whose stack-array
    decls have been HOISTED from the body into [jf_locals] by the Rocq-side
    [hoist_stack_decls_func] pass (src/Bedrock/Jasmin/Core.v).  This driver
    is the OCaml-side counterpart to Blocker A: it consumes [jf_locals]
    and materializes each [(name, JTstack n)] entry as a [Stack Direct]
    Jasmin var of type [Arr (U64, n)].

    Like [ed25519_sign_main.ml], it uses [Obj.magic] to bridge the
    structurally-identical [jasmin_func] types between the
    [Ed25519_sign_hoist_jasmin_extracted] extraction and the
    [Bls12_jasmin_extracted] extraction that [ocaml_compile.ml] is bound to.

    Usage:
      ed25519_sign_hoist_main <output.s> [--verbose]
      ed25519_sign_hoist_main <output.s> --func ed25519_sign [--verbose]
*)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  (* Hoisted sign body (Rocq-side [hoist_stack_decls_func] pass — A105). *)
  let sign_funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Ed25519_sign_hoist_jasmin_extracted.ed25519_sign_hoist_all_jasmin in
  (* FFI leaf stubs (same set the [ed25519_sign_stubbed] driver loads).
     Without these, jasminc's MakeReferenceArguments pass fails with
     "unknown function" — every JCcall in the sign body needs a callee
     declaration in the program. *)
  let stub_funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Ed25519_sign_stubs_jasmin_extracted.ed25519_sign_stubs in
  let funcs = sign_funcs @ stub_funcs in
  Printf.eprintf "[hoist_driver] sign funcs: %d, stub funcs: %d, total: %d\n%!"
    (List.length sign_funcs) (List.length stub_funcs) (List.length funcs);
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose ~funcs
