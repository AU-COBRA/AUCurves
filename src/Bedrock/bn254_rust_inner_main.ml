(** * Driver: emit bn254 inner Rust from extracted [rust_func].
 *
 * Usage:
 *   ./bn254_rust_inner_main <output.rs> [--full]
 *
 * Without --full: emits only the 6 leaf Fp ops (bn254_add/sub/mul/...).
 * With --full: emits the complete tower (Fp + Fp2 + Fp6 + Fp12 + pairing).
 *)

open Bn254_rust_extracted

let ocaml_string (cs : char list) : string =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let lf = "\n"

let () =
  let args = Array.to_list Sys.argv in
  let outfile, full =
    match args with
    | [_; out; "--full"] -> (out, true)
    | [_; out] -> (out, false)
    | _ ->
        Printf.eprintf "usage: %s <output.rs> [--full]\n" Sys.argv.(0);
        exit 2
  in
  let funcs = if full then bn254_all_funcs else bn254_leaf_funcs in
  let prelude = ocaml_string rust_prelude ^
    (if full then ocaml_string bn254_opp_prelude else "") in
  let bodies =
    Stdlib.List.map (fun f -> ocaml_string (rust_func f)) funcs
  in
  let n = Stdlib.List.length bodies in
  Printf.eprintf "[bn254_rust_inner] %d functions (full=%b)\n" n full;
  let text = prelude ^ String.concat lf bodies ^ lf in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[bn254_rust_inner] wrote %d bytes to %s\n"
    (String.length text) outfile
