(* Print the ToCString C module for X25519-64 *)
open X25519_64_extracted

let rec coq_string_to_ocaml = function
  | [] -> ""
  | c :: rest -> String.make 1 c ^ coq_string_to_ocaml rest

let () =
  let c_code = coq_string_to_ocaml x25519_c_module in
  print_string c_code
