(** BLS12-381 safe-Rust tower printer — 6 limbs. *)
open Bls12_rust_extracted

let ocaml_string cs =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs;
  Buffer.contents buf

let () =
  let outfile = match Array.to_list Sys.argv with [_;o] -> o | _ -> exit 2 in
  let funcs = bls12_tower_funcs in
  let n = Stdlib.List.length funcs in
  Printf.eprintf "[bls12_safe_tower] %d tower functions, 6 limbs\n" n;
  let decls = ocaml_string (type_decls (Zpos (XO (XI XH)))) in (* 6 = Zpos (XO (XI XH)) *)
  let body = ocaml_string (safe_rust_module (Zpos (XO (XI XH))) funcs) in
  let text = decls ^ body ^ "\n" in
  let oc = open_out outfile in
  output_string oc text;
  close_out oc;
  Printf.eprintf "[bls12_safe_tower] wrote %d bytes to %s\n"
    (String.length text) outfile
