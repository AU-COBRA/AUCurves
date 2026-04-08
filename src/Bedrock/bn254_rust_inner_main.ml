(** * Driver: emit bn254_leaves_inner.rs from extracted [rust_func]. *)

open Bn254_rust_extracted

(** Coq's [char list] -> OCaml [string]. *)
let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let lf = "\n"

let () =
  let outfile =
    if Array.length Sys.argv > 1 then Sys.argv.(1)
    else "bn254_leaves_inner.rs"
  in
  let prelude = ocaml_string rust_prelude in
  let bodies =
    Stdlib.List.map (fun f -> ocaml_string (rust_func f)) bn254_leaf_funcs
  in
  let n = Stdlib.List.length bodies in
  Printf.eprintf "[bn254_rust_inner] %d functions\n" n;
  let text = prelude ^ String.concat lf bodies ^ lf in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[bn254_rust_inner] wrote %d bytes to %s\n"
    (String.length text) outfile
