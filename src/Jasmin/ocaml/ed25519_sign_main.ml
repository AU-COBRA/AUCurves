(** Ed25519-sign driver: pipe the inlined sign body through
    [Ocaml_compile.compile_funcs].

    Like [x25519_64_main.ml], this uses [Obj.magic] to bridge the
    structurally-identical [jasmin_func] types between the
    [Ed25519_sign_jasmin_extracted] extraction and the
    [Bls12_jasmin_extracted] extraction that [ocaml_compile.ml]
    is type-bound to.

    Usage:
      ed25519_sign_main <output.s> [--verbose]
      ed25519_sign_main <output.s> --func ed25519_sign [--verbose]

    Build (after `dune build src/Jasmin/extractions/Ed25519_Sign_Inlined.vo`):
      ocamlfind ocamlopt -package jasmin -linkpkg \
        ed25519_sign_jasmin_extracted.ml \
        bls12_jasmin_extracted.ml \
        ocaml_compile.ml \
        ed25519_sign_main.ml \
        -o ed25519_sign_main
*)

let () =
  let outfile, func_filter, verbose = Ocaml_compile.parse_args () in
  let funcs : Bls12_jasmin_extracted.jasmin_func list =
    Obj.magic Ed25519_sign_jasmin_extracted.ed25519_sign_all_jasmin in
  Ocaml_compile.compile_funcs ~outfile ~func_filter ~verbose ~funcs
