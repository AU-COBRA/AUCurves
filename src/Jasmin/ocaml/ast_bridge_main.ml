(* AST-to-AST driver: bedrock2 → jasmin_cmd → Jasmin cmd
 *
 * UNVERIFIED GLUE: only this file (~15 lines).
 * Types jasmin_cmd/jasmin_expr/jasmin_type are structurally identical
 * between both extractions (verified by comparison). Obj.magic casts
 * between the two module namespaces.
 *)

let implode cs =
  String.init (List.length cs) (fun i -> List.nth cs i)

let () =
  let funcs = Bls12_jasmin_extracted.bls12_all_jasmin in
  Printf.printf "[ast2ast] %d functions\n" (List.length funcs);
  List.iter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
    let name = implode f.jf_name in
    (* Types match structurally — safe cast between module namespaces *)
    let body : Bridge_simple_v2.jasmin_cmd = Obj.magic f.jf_body in
    let jasmin_instrs = Bridge_simple_v2.to_jasmin_cmd
      (Obj.magic ()) (Obj.magic ()) body in
    Printf.printf "  %-30s -> %d Jasmin instrs\n" name (List.length jasmin_instrs)
  ) funcs;
  Printf.printf "[ast2ast] All functions translated via verified bridge.\n"
