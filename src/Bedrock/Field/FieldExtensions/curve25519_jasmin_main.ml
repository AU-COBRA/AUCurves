(* OCaml driver: emit Jasmin .jazz files from extracted curve25519 functions.

   Usage:
     ocamlfind ocamlopt -package str \
       curve25519_jasmin_extracted.ml curve25519_jasmin_main.ml \
       -o curve25519_jasmin_main

     ./curve25519_jasmin_main [field_size]

   field_size: 10 (RV32, default), 5 (x86-64 unsaturated), 4 (x86-64 CryptOpt)

   Output: curve25519_all.jazz (single file with all functions) *)

open Curve25519_jasmin_extracted

let field_size = ref 10  (* default: 10 limbs for RV32 *)

let () =
  if Array.length Sys.argv > 1 then
    field_size := int_of_string Sys.argv.(1);
  Printf.eprintf "[curve25519_jasmin] field size = %d limbs\n%!" !field_size;

  (* Get the function list *)
  let funcs = curve25519_all_funcs in

  (* Convert each function to Jasmin AST *)
  let field_sz = Z.of_sint !field_size in
  let jazz_funcs = List.map (fun (name, (args, rets, body)) ->
    let jazz_body = tr_func_sized field_sz (args, rets, body) in
    (name, jazz_body)
  ) funcs in

  (* Pretty-print to a single .jazz module *)
  let jazz_text = pp_module jazz_funcs in

  (* Output *)
  let filename = Printf.sprintf "curve25519_%d.jazz" !field_size in
  let oc = open_out filename in
  output_string oc jazz_text;
  close_out oc;
  Printf.eprintf "[curve25519_jasmin] wrote %s (%d functions)\n%!"
    filename (List.length funcs)
