(* Driver: print the extracted Jasmin module for X25519-64 *)
open X25519_64_extracted

(* Convert Coq char list to OCaml string *)
let rec coq_string_to_ocaml = function
  | [] -> ""
  | c :: rest ->
    let s = String.make 1 c in
    s ^ coq_string_to_ocaml rest

let () =
  let jasmin = coq_string_to_ocaml x25519_jasmin_module in
  print_string jasmin;
  print_newline ()
