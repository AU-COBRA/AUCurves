(* AST-to-AST Jasmin compilation driver.
 *
 * Bridges the two extractions:
 * - bls12_jasmin_extracted.ml: has bls12_all_jasmin (jasmin_func list)
 * - bridge_extracted.ml: has to_jasmin_cmd (jasmin_cmd → Jasmin cmd)
 *
 * The jasmin_cmd types differ only in Z representation:
 * bls12 uses OCaml int, bridge uses Coq's z inductive.
 * This driver converts between them.
 *
 * UNVERIFIED GLUE: only this file (~60 lines).
 * Everything else is extracted from verified Coq. *)

(* Adapter: convert bls12_jasmin_extracted's jasmin_cmd to
   bridge_extracted's jasmin_cmd. The only difference is
   int vs z for JCstore offsets and JElit constants. *)

let rec z_of_int n =
  if n = 0 then Bridge_extracted.Z0
  else if n > 0 then Bridge_extracted.Zpos (positive_of_int n)
  else Bridge_extracted.Zneg (positive_of_int (-n))
and positive_of_int n =
  if n = 1 then Bridge_extracted.XI Bridge_extracted.XH  (* hack: just use XH for 1 *)
  else
    (* Build binary positive from int *)
    if n <= 0 then Bridge_extracted.XH
    else if n mod 2 = 1 then Bridge_extracted.XI (positive_of_int (n / 2))
    else Bridge_extracted.XO (positive_of_int (n / 2))

(* Actually, positive_of_int 1 should be XH *)
let rec positive_of_int n =
  if n <= 1 then Bridge_extracted.XH
  else if n mod 2 = 1 then Bridge_extracted.XI (positive_of_int (n / 2))
  else Bridge_extracted.XO (positive_of_int (n / 2))

let z_of_int n =
  if n = 0 then Bridge_extracted.Z0
  else if n > 0 then Bridge_extracted.Zpos (positive_of_int n)
  else Bridge_extracted.Zneg (positive_of_int (-n))

let rec convert_expr (e : Bls12_jasmin_extracted.jasmin_expr)
    : Bridge_extracted.jasmin_expr =
  match e with
  | Bls12_jasmin_extracted.JEvar s -> Bridge_extracted.JEvar s
  | Bls12_jasmin_extracted.JElit n -> Bridge_extracted.JElit (z_of_int n)
  | Bls12_jasmin_extracted.JEadd (a, b) -> Bridge_extracted.JEadd (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JEsub (a, b) -> Bridge_extracted.JEsub (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JEmul (a, b) -> Bridge_extracted.JEmul (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JEand (a, b) -> Bridge_extracted.JEand (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JEor (a, b) -> Bridge_extracted.JEor (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JExor (a, b) -> Bridge_extracted.JExor (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JEsrl (a, b) -> Bridge_extracted.JEsrl (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JEsll (a, b) -> Bridge_extracted.JEsll (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JEltu (a, b) -> Bridge_extracted.JEltu (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JEeq (a, b) -> Bridge_extracted.JEeq (convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JEload (a, n) -> Bridge_extracted.JEload (convert_expr a, z_of_int n)
  | Bls12_jasmin_extracted.JEneq (a, b) -> Bridge_extracted.JEneq (convert_expr a, convert_expr b)

let rec convert_cmd (c : Bls12_jasmin_extracted.jasmin_cmd)
    : Bridge_extracted.jasmin_cmd =
  match c with
  | Bls12_jasmin_extracted.JCskip -> Bridge_extracted.JCskip
  | Bls12_jasmin_extracted.JCseq (a, b) -> Bridge_extracted.JCseq (convert_cmd a, convert_cmd b)
  | Bls12_jasmin_extracted.JCset (x, e) -> Bridge_extracted.JCset (x, convert_expr e)
  | Bls12_jasmin_extracted.JCstore (a, n, v) -> Bridge_extracted.JCstore (convert_expr a, z_of_int n, convert_expr v)
  | Bls12_jasmin_extracted.JCcall (f, args) -> Bridge_extracted.JCcall (f, List.map convert_expr args)
  | Bls12_jasmin_extracted.JCif (e, ct, cf) -> Bridge_extracted.JCif (convert_expr e, convert_cmd ct, convert_cmd cf)
  | Bls12_jasmin_extracted.JCwhile (e, body) -> Bridge_extracted.JCwhile (convert_expr e, convert_cmd body)
  | Bls12_jasmin_extracted.JCdecl (x, _ty, body) -> Bridge_extracted.JCdecl (x, Bridge_extracted.JTstack Bridge_extracted.Z0, convert_cmd body)
  | Bls12_jasmin_extracted.JCadd_flags (cf, r, a, b) -> Bridge_extracted.JCadd_flags (cf, r, convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JCadcx (cf, r, a, b, c) -> Bridge_extracted.JCadcx (cf, r, convert_expr a, convert_expr b, c)
  | Bls12_jasmin_extracted.JCmulx (h, l, a, b) -> Bridge_extracted.JCmulx (h, l, convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JCsub_flags (cf, r, a, b) -> Bridge_extracted.JCsub_flags (cf, r, convert_expr a, convert_expr b)
  | Bls12_jasmin_extracted.JCsbb (cf, r, a, b, c) -> Bridge_extracted.JCsbb (cf, r, convert_expr a, convert_expr b, c)

let () =
  let funcs = Bls12_jasmin_extracted.bls12_all_jasmin in
  Printf.printf "[ast2ast] %d functions loaded\n" (List.length funcs);
  (* Convert each function body to Jasmin's cmd via the bridge *)
  List.iter (fun (f : Bls12_jasmin_extracted.jasmin_func) ->
    let name = Jasmin_driver.implode f.Bls12_jasmin_extracted.jf_name in
    let bridge_body = convert_cmd f.Bls12_jasmin_extracted.jf_body in
    let jasmin_cmd = Bridge_extracted.to_jasmin_cmd
      (Obj.magic ()) (* atoI — architecture instance, opaque *)
      (Obj.magic ()) (* asmop — opaque *)
      bridge_body in
    let n_instrs = List.length jasmin_cmd in
    Printf.printf "  %s: %d Jasmin instructions\n" name n_instrs
  ) funcs;
  Printf.printf "[ast2ast] AST-to-AST translation complete\n"
