(** * Safe Rust body printer for BN254 tower functions. *)

open Bn254_rust_extracted

let fp_bytes = 32
let fp2_bytes = 64
let fp6_bytes = 192

let type_of_size n =
  if n = fp_bytes then "Fp" else if n = fp2_bytes then "Fp2"
  else if n = fp6_bytes then "Fp6" else if n = fp_bytes * 12 then "Fp12"
  else if n = 8 then "u64" (* scalar loop counter *)
  else Printf.sprintf "/*unknown_%d*/" n

let resolve_field parent_type offset =
  match parent_type with
  | "Fp" -> "" | "Fp2" -> Printf.sprintf ".c%d" (offset / fp_bytes)
  | "Fp6" -> let i = offset / fp2_bytes in let r = offset mod fp2_bytes in
    if r = 0 then Printf.sprintf ".c%d" i else Printf.sprintf ".c%d.c%d" i (r / fp_bytes)
  | "Fp12" -> let i = offset / fp6_bytes in let r = offset mod fp6_bytes in
    let j = r / fp2_bytes in let r2 = r mod fp2_bytes in
    if r = 0 then Printf.sprintf ".c%d" i
    else if r2 = 0 then Printf.sprintf ".c%d.c%d" i j
    else Printf.sprintf ".c%d.c%d.c%d" i j (r2 / fp_bytes)
  | _ -> ""

let ocaml_string cs =
  let buf = Buffer.create (Stdlib.List.length cs) in
  Stdlib.List.iter (Buffer.add_char buf) cs; Buffer.contents buf

let rec z_to_int = function
  | Z0 -> 0 | Zpos p -> pos_to_int p | Zneg p -> -(pos_to_int p)
and pos_to_int = function
  | XI p -> 2 * pos_to_int p + 1 | XO p -> 2 * pos_to_int p | XH -> 1

(* Convert Z to unsigned 64-bit Rust literal string, handling the full
   0..2^64-1 range. Bedrock2 encodes word-sized values as Z which may
   be negative (for values >= 2^63) or exceed OCaml's int range.
   Uses Int64 to stay in 64-bit range without depending on Zarith. *)
let rec pos_to_int64 = function
  | XI p -> Int64.add (Int64.mul 2L (pos_to_int64 p)) 1L
  | XO p -> Int64.mul 2L (pos_to_int64 p)
  | XH -> 1L

let z_to_u64_str z =
  let v = match z with
    | Z0 -> 0L
    | Zpos p -> pos_to_int64 p
    | Zneg p -> Int64.neg (pos_to_int64 p) in
  Printf.sprintf "0x%016Lx" v

let esc s = if s = "in" then "in_" else if s = "fn" then "fn_"
  else if s = "type" then "type_" else if s = "loop" then "loop_"
  else if s = "self" then "self_" else s

let escape_var x = esc (ocaml_string x)

(* arg resolution result *)
type rarg = Ref of string * string (* var, field_path *)
          | Lit of int              (* literal value *)

let rec resolve_expr e =
  match e with
  | Coq_expr.Coq_var x -> Ref (escape_var x, "")
  | Coq_expr.Coq_literal z -> Lit (z_to_int z)
  | Coq_expr.Coq_op (_, e1, Coq_expr.Coq_literal z) ->
    (match resolve_expr e1 with
     | Ref (v, p) -> Ref (v, p) (* offset will be added below *)
     | x -> x)
  | _ -> Lit 0

let rec resolve_with_ctx ctx e =
  match e with
  | Coq_expr.Coq_literal z -> Lit (z_to_int z)
  | Coq_expr.Coq_var x ->
    let v = escape_var x in Ref (v, "")
  | Coq_expr.Coq_op (_, e1, Coq_expr.Coq_literal z) ->
    (match e1 with
     | Coq_expr.Coq_var x ->
       let v = escape_var x in
       let off = z_to_int z in
       let vt = try Stdlib.List.assoc v ctx with Not_found -> "Fp" in
       Ref (v, resolve_field vt off)
     | _ -> Lit 0)
  | Coq_expr.Coq_op (_, Coq_expr.Coq_literal z, e2) ->
    resolve_with_ctx ctx (Coq_expr.Coq_op (Coq_bopname.Coq_add, e2, Coq_expr.Coq_literal z))
  | _ -> Lit 0

(* Per-function parameter type table *)
let explicit_param_types_early = [
  ("bn254_Fp2_felem_copy",["Fp2";"Fp2"]); ("bn254_Fp2_add",["Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp2_sub",["Fp2";"Fp2";"Fp2"]); ("bn254_Fp2_mul",["Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp2_square",["Fp2";"Fp2"]); ("bn254_Fp2_mul_xi",["Fp2";"Fp2"]);
  ("bn254_Fp2_conjugate",["Fp2";"Fp2"]); ("bn254_Fp2_mul_fp",["Fp2";"Fp2";"Fp"]);
  ("bn254_Fp2_opp",["Fp2";"Fp2"]); ("bn254_Fp2_inv",["Fp2";"Fp2"]);
  ("bn254_Fp6_felem_copy",["Fp6";"Fp6"]); ("bn254_Fp6_add",["Fp6";"Fp6";"Fp6"]);
  ("bn254_Fp6_sub",["Fp6";"Fp6";"Fp6"]); ("bn254_Fp6_opp",["Fp6";"Fp6"]);
  ("bn254_Fp6_mul",["Fp6";"Fp6";"Fp6"]); ("bn254_Fp6_square",["Fp6";"Fp6"]);
  ("bn254_Fp6_inv",["Fp6";"Fp6"]); ("bn254_Fp6_add_nocopy",["Fp6";"Fp6";"Fp6"]);
  ("bn254_Fp6_sub_nocopy",["Fp6";"Fp6";"Fp6"]); ("bn254_Fp6_mul_by_v",["Fp6";"Fp6"]);
  ("bn254_Fp6_mul_fp2",["Fp6";"Fp6";"Fp2"]);
  ("bn254_Fp6_frobenius",["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bn254_Fp6_frobenius_p2",["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bn254_Fp12_felem_copy",["Fp12";"Fp12"]); ("bn254_Fp12_add",["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_sub",["Fp12";"Fp12";"Fp12"]); ("bn254_Fp12_opp",["Fp12";"Fp12"]);
  ("bn254_Fp12_mul",["Fp12";"Fp12";"Fp12"]); ("bn254_Fp12_square",["Fp12";"Fp12"]);
  ("bn254_Fp12_inv",["Fp12";"Fp12"]); ("bn254_Fp12_conjugate",["Fp12";"Fp12"]);
  ("bn254_Fp12_mul_by_w",["Fp12";"Fp12"]);
  ("bn254_Fp12_frobenius",["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp12_frobenius_p2",["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn254_make_line",["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bn254_load_gamma1_p2",["Fp2"]); ("bn254_load_gamma2_p2",["Fp2"]);
  ("bn254_load_w_frob_p2_c1",["Fp2"]); ("bn254_load_gamma1",["Fp2"]);
  ("bn254_load_gamma2",["Fp2"]); ("bn254_load_w_frob_c1",["Fp2"]);
  ("bn254_Fp12_pow_u",["Fp12";"Fp12"]); ("bn254_final_exp_hard_dsd",["Fp12";"Fp12"]);
  ("bn254_final_exp_dsd",["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn254_make_line_corrected",["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bn254_load_q1_y_const",["Fp2"]);
  ("bn254_miller_loop",["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_miller_loop_optimal",["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_pairing_dsd",["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_pairing_dsd_optimal",["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  (* Leaf ops *)
  ("bn254_add",["Fp";"Fp";"Fp"]); ("bn254_sub",["Fp";"Fp";"Fp"]);
  ("bn254_mul",["Fp";"Fp";"Fp"]); ("bn254_square",["Fp";"Fp"]);
  ("bn254_opp",["Fp";"Fp"]); ("bn254_felem_copy",["Fp";"Fp"]);
  ("bn254_from_word",["Fp"]); ("bn254_select_znz",["Fp";"Fp";"Fp";"Fp"]);
]

let callee_param_types fname nargs =
  let name = ocaml_string fname in
  match Stdlib.List.assoc_opt name explicit_param_types_early with
  | Some ptypes ->
    let n = Stdlib.List.length ptypes in
    if n >= nargs then Stdlib.List.filteri (fun i _ -> i < nargs) ptypes
    else ptypes @ Stdlib.List.init (nargs - n) (fun _ -> "Fp")
  | None ->
    let t =
      if String.length name >= 12 && String.sub name 6 4 = "Fp12" then "Fp12"
      else if String.length name >= 10 && String.sub name 6 3 = "Fp6" then "Fp6"
      else if String.length name >= 10 && String.sub name 6 3 = "Fp2" then "Fp2"
      else "Fp" in
    Stdlib.List.init nargs (fun _ -> t)

(* Legacy single-type callee_type for type inference *)
let callee_type fname =
  let s = ocaml_string fname in
  if String.length s >= 12 && String.sub s 6 4 = "Fp12" then "Fp12"
  else if String.length s >= 10 && String.sub s 6 3 = "Fp6" then "Fp6"
  else if String.length s >= 10 && String.sub s 6 3 = "Fp2" then "Fp2"
  else "Fp"

let type_rank_early = function "Fp12" -> 4 | "Fp6" -> 3 | "Fp2" -> 2 | "Fp" -> 1 | _ -> 0

(* Drill down: add .c0 suffixes ONLY when source type is strictly larger
   than target type. When source <= target, return "" (no drilling needed). *)
let drill_down pt tt =
  if type_rank_early pt <= type_rank_early tt then ""
  else if pt = "Fp2" && tt = "Fp" then ".c0"
  else if pt = "Fp6" && tt = "Fp2" then ".c0"
  else if pt = "Fp6" && tt = "Fp" then ".c0.c0"
  else if pt = "Fp12" && tt = "Fp6" then ".c0"
  else if pt = "Fp12" && tt = "Fp2" then ".c0.c0"
  else if pt = "Fp12" && tt = "Fp" then ".c0.c0.c0"
  else ""

let rec expr_uses_var x e =
  match e with
  | Coq_expr.Coq_var y -> escape_var y = x
  | Coq_expr.Coq_op (_, e1, e2) -> expr_uses_var x e1 || expr_uses_var x e2
  | _ -> false

let fmt_src_arg ctx ct a =
  match a with
  | Lit n -> Printf.sprintf "%d" n
  | Ref (v, p) ->
    let vt = try Stdlib.List.assoc v ctx with Not_found -> "Fp" in
    let dd = if p = "" then drill_down vt ct else "" in
    Printf.sprintf "&%s%s%s" v p dd

(* Recursive bedrock2 expression -> Rust expression string *)
let rec expr_to_rust ctx e =
  match e with
  | Coq_expr.Coq_literal z -> z_to_u64_str z
  | Coq_expr.Coq_var x -> escape_var x
  | Coq_expr.Coq_op (Coq_bopname.Coq_sub, e1, e2) ->
    Printf.sprintf "%s.wrapping_sub(%s)" (expr_to_rust ctx e1) (expr_to_rust ctx e2)
  | Coq_expr.Coq_op (Coq_bopname.Coq_add, e1, e2) ->
    Printf.sprintf "%s.wrapping_add(%s)" (expr_to_rust ctx e1) (expr_to_rust ctx e2)
  | Coq_expr.Coq_op (Coq_bopname.Coq_and, e1, e2) ->
    Printf.sprintf "(%s & %s)" (expr_to_rust ctx e1) (expr_to_rust ctx e2)
  | Coq_expr.Coq_op (Coq_bopname.Coq_sru, e1, e2) ->
    Printf.sprintf "(%s >> %s)" (expr_to_rust ctx e1) (expr_to_rust ctx e2)
  | Coq_expr.Coq_load (_, addr) -> expr_to_rust ctx addr
  | _ ->
    match resolve_with_ctx ctx e with Lit n -> string_of_int n | Ref (v,p) -> v^p

let safe_body ctx0 buf ind cmd =
  let ci = ref 0 in
  let ctx = ref ctx0 in
  let rec go ind c =
    match c with
    | Coq_cmd.Coq_skip -> ()
    | Coq_cmd.Coq_seq (c1, c2) -> go ind c1; go ind c2
    | Coq_cmd.Coq_stackalloc (x, nb, body) ->
      let xn = escape_var x in
      let t = type_of_size (z_to_int nb) in
      let init = if t = "u64" then "0u64" else t ^ "::zero()" in
      Buffer.add_string buf (ind ^ Printf.sprintf "let mut %s: %s = %s;\n" xn t init);
      ctx := (xn, t) :: !ctx;
      go ind body
    | Coq_cmd.Coq_call (_, fname, args) ->
      let fn = ocaml_string fname in
      let nargs = Stdlib.List.length args in
      let ptypes = callee_param_types fname nargs in
      let dest_ct = if nargs > 0 then Stdlib.List.hd ptypes else "Fp" in
      (match args with
       | dest_e :: src_es ->
         let src_cts = if nargs > 1 then Stdlib.List.tl ptypes else [] in
         let da = resolve_with_ctx !ctx dest_e in
         (match da with
          | Ref (dv, dp) ->
            let dvt = try Stdlib.List.assoc dv !ctx with Not_found -> "Fp" in
            (* Determine the type at the resolved path *)
            let resolved_type =
              if dp = "" then dvt
              else (* infer from the resolved path depth *)
                let depth = Stdlib.List.length (String.split_on_char '.' dp) - 1 in
                let rec descend t d = if d <= 0 then t else match t with
                  | "Fp12" -> descend "Fp6" (d-1) | "Fp6" -> descend "Fp2" (d-1)
                  | "Fp2" -> descend "Fp" (d-1) | x -> x in
                descend dvt depth in
            let dd = drill_down resolved_type dest_ct in
            let dest_full = dv ^ dp ^ dd in
            let aliased = Stdlib.List.exists (expr_uses_var dv) src_es in
            let fmt_src ct_i e =
              let a = resolve_with_ctx !ctx e in
              match a with
              | Lit n -> Printf.sprintf "%d" n
              | Ref (sv, sp) ->
                let svt = try Stdlib.List.assoc sv !ctx with Not_found -> "Fp" in
                let resolved_t =
                  if sp = "" then svt
                  else let depth = Stdlib.List.length (String.split_on_char '.' sp) - 1 in
                    let rec descend t d = if d <= 0 then t else match t with
                      | "Fp12" -> descend "Fp6" (d-1) | "Fp6" -> descend "Fp2" (d-1)
                      | "Fp2" -> descend "Fp" (d-1) | x -> x in
                    descend svt depth in
                let sdd = drill_down resolved_t ct_i in
                Printf.sprintf "&%s%s%s" sv sp sdd
            in
            if aliased then begin
              let cn = Printf.sprintf "__ac%d" !ci in incr ci;
              (* Copy the value, not the reference — avoids moving &mut *)
              Buffer.add_string buf (ind ^ Printf.sprintf "let %s = %s.clone();\n" cn dest_full);
              let srcs = Stdlib.List.map2 (fun ct_i e ->
                let a = resolve_with_ctx !ctx e in
                match a with
                | Ref (sv, sp) when sv = dv ->
                  let svt = try Stdlib.List.assoc sv !ctx with Not_found -> "Fp" in
                  let sdd = if sp = "" then drill_down svt ct_i else "" in
                  let src_full = sv ^ sp ^ sdd in
                  if src_full = dest_full then Printf.sprintf "&%s" cn
                  else fmt_src ct_i e
                | _ -> fmt_src ct_i e
              ) src_cts src_es in
              Buffer.add_string buf (ind ^ Printf.sprintf "%s(&mut %s, %s);\n"
                fn dest_full (String.concat ", " srcs))
            end else begin
              let srcs = Stdlib.List.map2 (fun ct_i e -> fmt_src ct_i e) src_cts src_es in
              Buffer.add_string buf (ind ^ Printf.sprintf "%s(&mut %s, %s);\n"
                fn dest_full (String.concat ", " srcs))
            end
          | Lit _ -> Buffer.add_string buf (ind ^ "/* literal dest? */\n"))
       | [] -> Buffer.add_string buf (ind ^ fn ^ "();\n"))
    | Coq_cmd.Coq_set (x, e) ->
      let xn = escape_var x in
      (* Track which scalar vars have been declared. First occurrence uses
         "let mut", subsequent uses plain assignment (avoids shadowing in loops). *)
      let is_new = not (Stdlib.List.mem_assoc xn !ctx) in
      if is_new then ctx := (xn, "u64") :: !ctx;
      let decl = if is_new then "let mut " else "" in
      let ty = if is_new then ": u64" else "" in
      let emit_expr_str () = expr_to_rust !ctx e in
      Buffer.add_string buf (ind ^ Printf.sprintf "%s%s%s = %s;\n" decl xn ty (emit_expr_str ()))
    | Coq_cmd.Coq_cond (e, ct, cf) ->
      let cond_str = Printf.sprintf "%s != 0" (expr_to_rust !ctx e) in
      Buffer.add_string buf (ind ^ Printf.sprintf "if %s {\n" cond_str);
      go (ind ^ "    ") ct;
      Buffer.add_string buf (ind ^ "} else {\n");
      go (ind ^ "    ") cf;
      Buffer.add_string buf (ind ^ "}\n")
    | Coq_cmd.Coq_while (e, body) ->
      let cond_str = Printf.sprintf "%s != 0" (expr_to_rust !ctx e) in
      Buffer.add_string buf (ind ^ Printf.sprintf "while %s {\n" cond_str);
      go (ind ^ "    ") body;
      Buffer.add_string buf (ind ^ "}\n")
    | Coq_cmd.Coq_store (_, ea, ev) ->
      (* Store: *addr = value. For u64 scalars (u6p2), direct assignment.
         Uses z_to_u64_str for literals to handle the full u64 range. *)
      let val_str = match ev with
        | Coq_expr.Coq_literal z -> z_to_u64_str z ^ "u64"
        | _ -> (match resolve_with_ctx !ctx ev with Lit n -> string_of_int n | Ref (v,p) -> v^p)
      in
      (match resolve_with_ctx !ctx ea with
       | Ref (v, "") -> Buffer.add_string buf (ind ^ Printf.sprintf "%s = %s;\n" v val_str)
       | _ -> Buffer.add_string buf (ind ^ Printf.sprintf "/* store %s */\n" val_str))
    | Coq_cmd.Coq_unset _ -> ()
    | _ -> ()
  in go ind cmd

let safe_func ptypes (name, ((args, _rets), body)) =
  let buf = Buffer.create 1024 in
  let ns = ocaml_string name in
  let as_ = Stdlib.List.map ocaml_string args in
  let params = Stdlib.List.combine as_ ptypes in
  let ps = match params with
    | (a,t)::r -> (Printf.sprintf "mut %s: &mut %s" (esc a) t) ::
        Stdlib.List.map (fun (a,t) -> Printf.sprintf "%s: &%s" (esc a) t) r
    | [] -> [] in
  let ctx = Stdlib.List.map (fun (a,t) -> (esc a, t)) params in
  Buffer.add_string buf (Printf.sprintf "#[inline]\npub fn %s(%s) {\n" ns (String.concat ", " ps));
  safe_body ctx buf "    " body;
  Buffer.add_string buf "}\n";
  Buffer.contents buf

let type_decls = {|#![allow(non_snake_case, dead_code, unused_mut, unused_variables)]

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp(pub [u64; 4]);
impl Fp { #[inline] pub const fn zero() -> Self { Fp([0u64; 4]) } }

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp2 { pub c0: Fp, pub c1: Fp }
impl Fp2 { #[inline] pub const fn zero() -> Self { Fp2 { c0: Fp::zero(), c1: Fp::zero() } } }

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp6 { pub c0: Fp2, pub c1: Fp2, pub c2: Fp2 }
impl Fp6 { #[inline] pub const fn zero() -> Self { Fp6 { c0: Fp2::zero(), c1: Fp2::zero(), c2: Fp2::zero() } } }

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp12 { pub c0: Fp6, pub c1: Fp6 }
impl Fp12 { #[inline] pub const fn zero() -> Self { Fp12 { c0: Fp6::zero(), c1: Fp6::zero() } } }

|}

let leaf_wrappers = {|extern "C" {
    fn _bn254_add(out: *mut u64, x: *const u64, y: *const u64);
    fn _bn254_sub(out: *mut u64, x: *const u64, y: *const u64);
    fn _bn254_mul(out: *mut u64, x: *const u64, y: *const u64);
    fn _bn254_square(out: *mut u64, x: *const u64);
    fn _bn254_opp(out: *mut u64, x: *const u64);
    fn _bn254_felem_copy(out: *mut u64, x: *const u64);
    fn _bn254_from_word(out: *mut u64, w: u64);
    fn _bn254_select_znz(out: *mut u64, c: u64, x: *const u64, y: *const u64);
}
#[inline] pub fn bn254_add(out: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_add(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn254_sub(out: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_sub(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn254_mul(out: &mut Fp, x: &Fp, y: &Fp) { unsafe { _bn254_mul(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr()) } }
#[inline] pub fn bn254_square(out: &mut Fp, x: &Fp) { unsafe { _bn254_square(out.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn254_opp(out: &mut Fp, x: &Fp) { unsafe { _bn254_opp(out.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn254_felem_copy(out: &mut Fp, x: &Fp) { unsafe { _bn254_felem_copy(out.0.as_mut_ptr(), x.0.as_ptr()) } }
#[inline] pub fn bn254_from_word(out: &mut Fp, w: u64) { unsafe { _bn254_from_word(out.0.as_mut_ptr(), w) } }
#[inline] pub fn bn254_select_znz(out: &mut Fp, c: u64, x: &Fp, y: &Fp) { unsafe { _bn254_select_znz(out.0.as_mut_ptr(), c, x.0.as_ptr(), y.0.as_ptr()) } }

#[inline] pub fn bn254_Fp2_opp(out: &mut Fp2, x: &Fp2) { bn254_opp(&mut out.c0, &x.c0); bn254_opp(&mut out.c1, &x.c1); }

#[inline] pub fn bn254_Fp2_inv(out: &mut Fp2, x: &Fp2) {
    let mut asq = Fp::zero();
    let mut bsq = Fp::zero();
    let mut norm = Fp::zero();
    bn254_square(&mut asq, &x.c0);
    bn254_square(&mut bsq, &x.c1);
    bn254_add(&mut norm, &asq, &bsq);
    // Fermat's little theorem: norm^(p-2)
    let mut base = norm;
    let p_minus_2: [u64; 4] = [0x3c208c16d87cfd45, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029];
    let mut result = Fp([0xac96341c4ffffffb, 0x36fc76959f60cd29, 0x666ea36f7879462e, 0x0e0a77c19a07df2f]);
    for limb_idx in 0..4 {
        let mut bits = p_minus_2[limb_idx];
        for _ in 0..64 {
            if bits & 1 == 1 { let r2 = result; bn254_mul(&mut result, &r2, &base); }
            let b2 = base; bn254_square(&mut base, &b2);
            bits >>= 1;
        }
    }
    norm = result;
    bn254_mul(&mut out.c0, &x.c0, &norm);
    let mut neg_b = Fp::zero();
    bn254_opp(&mut neg_b, &x.c1);
    bn254_mul(&mut out.c1, &neg_b, &norm);
}

|}

(* Infer parameter type from how they're used in function calls.
   Two sources: (1) max byte offset, (2) callee expected type.
   Use whichever gives the LARGER type. *)
let type_rank = function "Fp12" -> 4 | "Fp6" -> 3 | "Fp2" -> 2 | "Fp" -> 1 | _ -> 0
let max_type a b = if type_rank a >= type_rank b then a else b

let rec max_offset_for_var vname cmd =
  match cmd with
  | Coq_cmd.Coq_skip -> 0
  | Coq_cmd.Coq_seq (c1, c2) -> max (max_offset_for_var vname c1) (max_offset_for_var vname c2)
  | Coq_cmd.Coq_stackalloc (_, _, body) -> max_offset_for_var vname body
  | Coq_cmd.Coq_cond (_, ct, cf) -> max (max_offset_for_var vname ct) (max_offset_for_var vname cf)
  | Coq_cmd.Coq_call (_, _, args) ->
    Stdlib.List.fold_left (fun acc e -> max acc (max_offset_in_expr vname e)) 0 args
  | Coq_cmd.Coq_store (_, ea, ev) ->
    max (max_offset_in_expr vname ea) (max_offset_in_expr vname ev)
  | _ -> 0
and max_offset_in_expr vname e =
  match e with
  | Coq_expr.Coq_var x -> if escape_var x = vname then 0 else -1
  | Coq_expr.Coq_op (_, e1, Coq_expr.Coq_literal z) ->
    let base = max_offset_in_expr vname e1 in
    if base >= 0 then base + z_to_int z else -1
  | Coq_expr.Coq_op (_, Coq_expr.Coq_literal z, e2) ->
    let base = max_offset_in_expr vname e2 in
    if base >= 0 then base + z_to_int z else -1
  | _ -> -1

let type_from_max_offset off =
  if off >= fp6_bytes then "Fp12"
  else if off >= fp2_bytes then "Fp6"
  else if off >= fp_bytes then "Fp2"
  else "Fp"

(* Also infer from callee types: if var is passed to bn254_Fp6_mul, it's at least Fp6 *)
let rec callee_type_for_var vname cmd =
  match cmd with
  | Coq_cmd.Coq_skip -> "Fp"
  | Coq_cmd.Coq_seq (c1, c2) -> max_type (callee_type_for_var vname c1) (callee_type_for_var vname c2)
  | Coq_cmd.Coq_stackalloc (_, _, body) -> callee_type_for_var vname body
  | Coq_cmd.Coq_cond (_, ct, cf) -> max_type (callee_type_for_var vname ct) (callee_type_for_var vname cf)
  | Coq_cmd.Coq_call (_, fname, args) ->
    let ct = callee_type fname in
    let used = Stdlib.List.exists (fun e ->
      match e with
      | Coq_expr.Coq_var x -> escape_var x = vname
      | Coq_expr.Coq_op (_, Coq_expr.Coq_var x, _) -> escape_var x = vname
      | Coq_expr.Coq_op (_, _, Coq_expr.Coq_var x) -> escape_var x = vname
      | _ -> false
    ) args in
    if used then ct else "Fp"
  | _ -> "Fp"

(* Hardcoded parameter type table for functions with mixed types.
   Functions not listed here use the inference fallback. *)
let explicit_param_types = [
  (* Fp2 level *)
  ("bn254_Fp2_felem_copy", ["Fp2";"Fp2"]);
  ("bn254_Fp2_add", ["Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp2_sub", ["Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp2_mul", ["Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp2_square", ["Fp2";"Fp2"]);
  ("bn254_Fp2_mul_xi", ["Fp2";"Fp2"]);
  ("bn254_Fp2_conjugate", ["Fp2";"Fp2"]);
  ("bn254_Fp2_mul_fp", ["Fp2";"Fp2";"Fp"]);
  (* Fp6 level *)
  ("bn254_Fp6_felem_copy", ["Fp6";"Fp6"]);
  ("bn254_Fp6_add", ["Fp6";"Fp6";"Fp6"]);
  ("bn254_Fp6_sub", ["Fp6";"Fp6";"Fp6"]);
  ("bn254_Fp6_opp", ["Fp6";"Fp6"]);
  ("bn254_Fp6_mul", ["Fp6";"Fp6";"Fp6"]);
  ("bn254_Fp6_square", ["Fp6";"Fp6"]);
  ("bn254_Fp6_inv", ["Fp6";"Fp6"]);
  ("bn254_Fp6_add_nocopy", ["Fp6";"Fp6";"Fp6"]);
  ("bn254_Fp6_sub_nocopy", ["Fp6";"Fp6";"Fp6"]);
  ("bn254_Fp6_mul_by_v", ["Fp6";"Fp6"]);
  ("bn254_Fp6_mul_fp2", ["Fp6";"Fp6";"Fp2"]);
  ("bn254_Fp6_frobenius", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  ("bn254_Fp6_frobenius_p2", ["Fp6";"Fp6";"Fp2";"Fp2"]);
  (* Fp12 level *)
  ("bn254_Fp12_felem_copy", ["Fp12";"Fp12"]);
  ("bn254_Fp12_add", ["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_sub", ["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_opp", ["Fp12";"Fp12"]);
  ("bn254_Fp12_mul", ["Fp12";"Fp12";"Fp12"]);
  ("bn254_Fp12_square", ["Fp12";"Fp12"]);
  ("bn254_Fp12_inv", ["Fp12";"Fp12"]);
  ("bn254_Fp12_conjugate", ["Fp12";"Fp12"]);
  ("bn254_Fp12_mul_by_w", ["Fp12";"Fp12"]);
  ("bn254_Fp12_frobenius", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn254_Fp12_frobenius_p2", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  (* Special pairing functions *)
  ("bn254_make_line", ["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bn254_load_gamma1_p2", ["Fp2"]);
  ("bn254_load_gamma2_p2", ["Fp2"]);
  ("bn254_load_w_frob_p2_c1", ["Fp2"]);
  ("bn254_load_gamma1", ["Fp2"]);
  ("bn254_load_gamma2", ["Fp2"]);
  ("bn254_load_w_frob_c1", ["Fp2"]);
  ("bn254_Fp12_pow_u", ["Fp12";"Fp12"]);
  ("bn254_final_exp_hard_dsd", ["Fp12";"Fp12"]);
  ("bn254_final_exp_dsd", ["Fp12";"Fp12";"Fp2";"Fp2";"Fp2"]);
  ("bn254_make_line_corrected", ["Fp12";"Fp2";"Fp2";"Fp2";"Fp";"Fp"]);
  ("bn254_load_q1_y_const", ["Fp2"]);
  ("bn254_miller_loop", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_miller_loop_optimal", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_pairing_dsd", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
  ("bn254_pairing_dsd_optimal", ["Fp12";"Fp";"Fp";"Fp2";"Fp2"]);
]

let infer_param_types fname args body =
  let name = ocaml_string fname in
  match Stdlib.List.assoc_opt name explicit_param_types with
  | Some ptypes ->
    let n = Stdlib.List.length args in
    if Stdlib.List.length ptypes >= n then
      Stdlib.List.filteri (fun i _ -> i < n) ptypes
    else ptypes @ Stdlib.List.init (n - Stdlib.List.length ptypes) (fun _ -> "Fp")
  | None ->
    (* Fallback: use offset + callee inference *)
    Stdlib.List.map (fun a ->
      let vname = esc (ocaml_string a) in
      let off_type = type_from_max_offset (max_offset_for_var vname body) in
      let call_type = callee_type_for_var vname body in
      max_type off_type call_type
    ) args

let () =
  let outfile = match Array.to_list Sys.argv with [_;o] -> o | _ -> exit 2 in
  let leaf_names = Stdlib.List.map (fun (n,_) -> ocaml_string n) bn254_leaf_funcs in
  let tower = Stdlib.List.filter (fun (n,_) -> not (Stdlib.List.mem (ocaml_string n) leaf_names)) bn254_all_funcs in
  Printf.eprintf "[safe_tower] %d tower functions\n" (Stdlib.List.length tower);
  let bodies = Stdlib.List.map (fun ((name, ((args, _), body)) as f) ->
    let ptypes = infer_param_types name args body in
    safe_func ptypes f
  ) tower in
  let text = type_decls ^ leaf_wrappers ^ String.concat "\n" bodies ^ "\n" in
  let oc = open_out outfile in output_string oc text; close_out oc;
  Printf.eprintf "[safe_tower] wrote %d bytes to %s\n" (String.length text) outfile
