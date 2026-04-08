(*Rust Backend for Bedrock2 project. We mirror the approach of Bedrock2/src/bedrock2/ToCString.v*)
Require Import bedrock2.Syntax bedrock2.Variables. Import bopname.
Require Import coqutil.Datatypes.ListSet.
Require Import Coq.ZArith.BinIntDef Coq.Numbers.BinNums Coq.Numbers.DecimalString.
Require Import Coq.Strings.String. Local Open Scope string_scope.

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

(** Escape bedrock2 variable names that collide with Rust keywords. *)
Definition rust_var (x : string) : string :=
  if String.eqb x "in" then "in_"
  else if String.eqb x "fn" then "fn_"
  else if String.eqb x "let" then "let_"
  else if String.eqb x "mut" then "mut_"
  else if String.eqb x "ref" then "ref_"
  else if String.eqb x "type" then "type_"
  else if String.eqb x "match" then "match_"
  else if String.eqb x "loop" then "loop_"
  else if String.eqb x "move" then "move_"
  else if String.eqb x "self" then "self_"
  else if String.eqb x "use" then "use_"
  else if String.eqb x "mod" then "mod_"
  else if String.eqb x "box" then "box_"
  else x.

Definition rust_fun := @id string.

Definition rust_lit' w := DecimalString.NilZero.string_of_int (BinInt.Z.to_int w) ++ "u64".

Definition rust_lit w :=
  match w with
    | Z.pos _ => rust_lit' w
    | Z.neg p => "(0u64.wrapping_sub(" ++ rust_lit' (Z.pos p) ++ "))"
    | _ => rust_lit' w
  end.

Definition rust_bop e1 op e2 :=
  match op with
  | add => e1++".wrapping_add("++ e2 ++")"
  | sub => e1++".wrapping_sub("++ e2 ++")"
  | mul => e1++".wrapping_mul("++ e2 ++")"
  | mulhuu => "((" ++ e1 ++ " as u128).wrapping_mul(" ++ e2 ++ " as u128) >> 64) as u64"
  | divu => e1++" / "++e2
  | remu => e1++" % "++e2
  | and => e1++" & "++e2
  | or => e1++" | "++e2
  | xor => e1++" ^ "++e2
  | sru => e1++" >> "++e2
  | slu => e1++" << "++e2
  | srs => "((" ++ e1 ++ " as i64) >> " ++ e2 ++ ") as u64"
  | ltu => "if " ++ e1 ++ " < " ++ e2 ++ " { 1u64 } else { 0u64 }"
  | lts => "if (" ++ e1 ++ " as i64) < (" ++ e2 ++ " as i64) { 1u64 } else { 0u64 }"
  | eq => "if " ++ e1 ++ " == " ++ e2 ++ " { 1u64 } else { 0u64 }"
  end%string.

  Definition rust_size (s : access_size) : string :=
  match s with
  | access_size.one => "1"
  | access_size.two => "2"
  | access_size.four => "4"
  | access_size.word => "8" (* 64-bit targets *)
  end.

  Definition rust_size_type (s : access_size) : string :=
  match s with
  | access_size.one => "u8"
  | access_size.two => "u16"
  | access_size.four => "u32"
  | access_size.word => "u64"
  end.

(*Idea: use Vec instead of unsafe pointer arithmetic?*)
(*syntax for pointer arithmetic and arithmetic of ints/uints is similar in C, and by extension in bedrock2.
  the three following functions are used when performing pointer arithmetic in Rust*)

Definition rust_ptr_varlit (e : expr) : string :=
  match e with
  | expr.literal v => rust_lit v
  | expr.var x => rust_var x
  | _ => ""
  end.

Definition rust_ptr_op e1 op e2 : string :=
  match op with
  | add => "_br2_load((" ++ rust_ptr_varlit e1 ++ " as *const u8).wrapping_add((" ++ rust_ptr_varlit e2 ++ ") as usize) as *const usize)"
  | _ => ""
  end.

  Definition rust_store_ptr_op e1 op e2 : string :=
  match op with
  | add => "_br2_store((" ++ rust_ptr_varlit e1 ++ " as *const u8).wrapping_add((" ++ rust_ptr_varlit e2 ++ ") as usize) as *mut usize, "
  | _ => ""
  end.
  Definition rust_store_ptr_expr (e : expr) : string :=
  match e with
  | expr.op op e1 e2 => rust_store_ptr_op e1 op e2
  | expr.var x => "_br2_store(" ++ rust_var x ++ " as *mut usize, "
  | _ => ""
  end.

  
Fixpoint rust_store_expr (e : expr) : string :=
match e with
| expr.literal v => rust_lit v
| expr.var x => rust_var x
| expr.load s ea =>  rust_store_ptr_expr ea
| expr.inlinetable _ _ _ => "/*inlinetable: unsupported*/"
| expr.op op e1 e2 => rust_bop ("(" ++ rust_store_expr e1 ++ ")") op ("(" ++ rust_store_expr e2 ++ ")")
| expr.op1 op e =>
    match op with
    | op1.opp => "(0u64.wrapping_sub(" ++ rust_store_expr e ++ "))"
    | op1.not => "(!(" ++ rust_store_expr e ++ "))"
    end
| expr.ite _ _ _ => "/*ite: unsupported*/"
end.

Definition rust_ptr_expr (e : expr) : string :=
  match e with
  | expr.op op e1 e2 => rust_ptr_op e1 op e2
  | expr.var x => "_br2_load(" ++ rust_var x ++ " as *const usize)"
  | _ => ""
  end.

  
Fixpoint rust_expr (e : expr) : string :=
match e with
| expr.literal v => rust_lit v
| expr.var x => rust_var x
| expr.load s ea =>  rust_ptr_expr ea
| expr.inlinetable _ _ _ => "/*inlinetable: unsupported*/"
| expr.op op e1 e2 => rust_bop ("(" ++ rust_expr e1 ++ ")") op ("(" ++ rust_expr e2 ++ ")")
| expr.op1 op e =>
    match op with
    | op1.opp => "(0u64.wrapping_sub(" ++ rust_expr e ++ "))"
    | op1.not => "(!(" ++ rust_expr e ++ "))"
    end
| expr.ite _ _ _ => "/*ite: unsupported*/"
end.

Fixpoint List_uniq {A} (eqb : A -> A -> bool) (l : list A) :=
match l with
| nil => nil
| cons a l' =>
  if List.existsb (eqb a ) l'
  then List_uniq eqb l'
  else cons a (List_uniq eqb l')
end.

Definition List_minus {A} (eqb : A -> A -> bool) (X Y : list A) :=
  List.filter (fun x => negb (List.existsb (eqb x) Y)) X.

Definition rust_call (args : list string) (f : string) (es : list string) :=
  match args with
  | nil =>
    f ++ "(" ++ concat ", " es ++ ");" ++ LF
  | ((x::_)%list as binds)  =>
    List.last binds x ++ " = " ++ f ++ "(" ++ concat ", " (es ++ List.map (fun x => "&"++x) (List.removelast binds)) ++ ");" ++ LF
  end.

  Local Open Scope Z_scope.
  Definition bytes_to_words n := Z.div n 8.


  Fixpoint rust_cmd (indent : string) (c : cmd) : string :=
  match c with
  | cmd.store s ea ev
    => indent ++ rust_store_ptr_expr ea ++ rust_expr ev ++ ");" ++ LF
  | cmd.stackalloc x n body =>
    indent ++ "let mut " ++ rust_var x ++ "_arr = [0u64; " ++ DecimalString.NilZero.string_of_int (BinInt.Z.to_int (bytes_to_words n)) ++ "];" ++ LF ++
    indent ++ "let " ++ rust_var x ++ " = " ++ rust_var x ++ "_arr.as_mut_ptr() as u64;" ++ LF ++
    rust_cmd indent body
  | cmd.set x ev =>
    indent ++ rust_var x ++ " = " ++ rust_expr ev ++ ";" ++ LF
  | cmd.cond eb t f =>
    indent ++ "if (" ++ rust_expr eb ++ ") != 0 {" ++ LF ++
      rust_cmd ("  "++indent) t ++
    indent ++ "} else {" ++ LF ++
      rust_cmd ("  "++indent) f ++
    indent ++ "}" ++ LF
  | cmd.while eb body =>
    indent ++ "while (" ++ rust_expr eb ++ ") != 0 {" ++ LF ++
      rust_cmd ("  "++indent) body ++
    indent ++ "}" ++ LF
  | cmd.seq c1 c2 =>
    rust_cmd indent c1 ++
    rust_cmd indent c2
  | cmd.skip =>
    indent ++ "/*skip*/" ++ LF
  | cmd.call args f es =>
    indent ++ rust_call (List.map rust_var args) (rust_fun f) (List.map rust_expr es)
  | _ => ""
  end.

  Definition DQUOTE : string :=
    String (Coq.Strings.Ascii.Ascii false true false false false true false false) "".

  Definition fmt_c_decl (rett : string) (args : list String.string) (name : String.string) (retptrs : list String.string) : string :=
    ("#[no_mangle]" ++ LF ++
     "pub unsafe extern " ++ DQUOTE ++ "C" ++ DQUOTE ++ " fn " ++ rust_fun name ++ "(" ++ concat ", " (
                    List.map (fun a => rust_var a ++ " : u64") args ++
                    List.map (fun r => rust_var r ++ " : &mut u64") retptrs) ++
                  ")" ++
     match rett with
     | "void" => ""
     | _ => " -> u64"
     end).

Definition c_decl (f : String.string * (list String.string * list String.string * cmd)) :=
  let '(name, (args, rets, body)) := f in
  match rets with
  | nil => fmt_c_decl "void" args name nil
  | cons _ _ => fmt_c_decl "uintptr_t" args name (List.removelast rets)
  end ++ ";".

  Definition rename_away_from x xs :=
  let x' := "_" ++ x in
  if List.existsb (String.eqb x') xs
  then "#error rename_away_from '" ++ x ++"' = '" ++ x' ++"'"
  else x'.

  Fixpoint rename_outs (outs : list String.string) (used : list String.string) : list (String.string*String.string) * list String.string :=
  match outs with
  | cons o outs' =>
    let rec := rename_outs outs' used in
    let (outrenames, used) := (fst rec, snd rec) in
    let optr := rename_away_from o used in
    (cons (o, optr) outrenames, cons o used)
  | nil => (nil, used)
  end.


Definition variable_declaration indent  (local_vars : list String.string) : String.string := indent ++ "".
  (* indent ++ "let " ++ (concat (" : usize;" ++ LF ++ indent ++ "let ") local_vars) ++ " : usize;" ++ LF. *)

  Definition variable_declaration' indent  (local_vars : list String.string) : String.string :=
  indent ++ "let mut " ++ (concat (" : u64;" ++ LF ++ indent ++ "let mut ") local_vars) ++ " : u64;" ++ LF.

Definition rust_func '(name, (args, rets, body)) :=
  let decl_retvar_retrenames : string * option String.string * list (String.string * String.string) :=
  match rets with
  | nil => (fmt_c_decl "void" args name nil, None, nil)
  | cons r0 _ => (*return values not supported; only here for Coq type checker*)
  let r0 := List.last rets r0 in
  let rets' := List.removelast rets in
  let retrenames := fst (rename_outs rets' (cmd.vars body)) in
  (fmt_c_decl "uintptr_t" args name (List.map snd retrenames), Some r0, retrenames)
  end in
  let decl := fst (fst decl_retvar_retrenames) in
  let retvar := snd (fst decl_retvar_retrenames) in
  let retrenames := snd decl_retvar_retrenames in
  let localvars : list String.string := List_uniq String.eqb (
      let allvars := (List.app (match retvar with None => nil | Some v => cons v nil end) (cmd.vars body)) in
      (List_minus String.eqb allvars args)) in 
  decl ++ " {" ++ LF ++
    let indent := "  " in
    (match localvars with nil => "" | _ => (variable_declaration' indent (List.map rust_var localvars)) end) ++
    rust_cmd indent body ++
    concat "" (List.map (fun '(o, optr) => indent ++ "*" ++ rust_var optr ++ " = " ++ rust_var o ++ ";" ++ LF) retrenames) ++
    indent ++ "return" ++ (match retvar with None => "" | Some rv => " "++ rust_var rv end) ++ ";" ++ LF ++
    "}" ++ LF.

Definition rust_func_no_decl '(name, (args, rets, body)) :=
  let decl_retvar_retrenames : string * option String.string * list (String.string * String.string) :=
  match rets with
  | nil => (fmt_c_decl "void" args name nil, None, nil)
  | cons r0 _ => (*return values not supported; only here for Coq type checker*)
  let r0 := List.last rets r0 in
  let rets' := List.removelast rets in
  let retrenames := fst (rename_outs rets' (cmd.vars body)) in
  (fmt_c_decl "uintptr_t" args name (List.map snd retrenames), Some r0, retrenames)
  end in
  let decl := fst (fst decl_retvar_retrenames) in
  let retvar := snd (fst decl_retvar_retrenames) in
  let retrenames := snd decl_retvar_retrenames in
  let localvars : list String.string := List_uniq String.eqb (
      let allvars := (List.app (match retvar with None => nil | Some v => cons v nil end) (cmd.vars body)) in
      (List_minus String.eqb allvars args)) in 
  decl ++ " {" ++ LF ++
    let indent := "  " in
    (match localvars with nil => "" | _ => (variable_declaration indent (List.map rust_var localvars)) end) ++
    rust_cmd indent body ++
    concat "" (List.map (fun '(o, optr) => indent ++ "*" ++ rust_var optr ++ " = " ++ rust_var o ++ ";" ++ LF) retrenames) ++
    indent ++ "return" ++ (match retvar with None => "" | Some rv => " "++ rust_var rv end) ++ ";" ++ LF ++
    "}" ++ LF.

(** Concatenate the unsafe Rust source for a list of bedrock2 functions
    into one module body. The caller is expected to wrap this in any
    needed prelude (e.g. the [_br2_load]/[_br2_store] helpers). *)
Definition rust_module
    (fs : list (String.string * (list String.string * list String.string * cmd)))
    : string :=
  concat LF (List.map rust_func fs).

(** Standard prelude that defines the runtime helpers used by the
    pretty-printed code: 64-bit pointer load/store via raw pointer
    casts. The pretty-printer emits calls of the form
      [_br2_load((p as *const u8).wrapping_add(off) as *const usize)]
    so the helpers must take [*const usize] / [*mut usize] arguments. *)
Definition rust_prelude : string :=
  "//! Auto-generated unsafe Rust from bedrock2." ++ LF ++
  "//! Memory accesses go through [_br2_load]/[_br2_store] helpers." ++ LF ++
  "#![allow(non_snake_case)]" ++ LF ++
  "#![allow(unused_assignments)]" ++ LF ++
  "#![allow(unused_variables)]" ++ LF ++
  "#![allow(unused_mut)]" ++ LF ++
  "#![allow(unused_parens)]" ++ LF ++
  "#![allow(dead_code)]" ++ LF ++ LF ++
  "#[inline(always)]" ++ LF ++
  "pub unsafe fn _br2_load(p: *const usize) -> u64 {" ++ LF ++
  "    *p as u64" ++ LF ++
  "}" ++ LF ++ LF ++
  "#[inline(always)]" ++ LF ++
  "pub unsafe fn _br2_store(p: *mut usize, v: u64) {" ++ LF ++
  "    *p = v as usize;" ++ LF ++
  "}" ++ LF ++ LF.

Definition rust_var_decl '(name, (args, rets, body)) :=
  let decl_retvar_retrenames : string * option String.string * list (String.string * String.string) :=
  match rets with
  | nil => (fmt_c_decl "void" args name nil, None, nil)
  | cons r0 _ => (*return values not supported; only here for Coq type checker*)
  let r0 := List.last rets r0 in
  let rets' := List.removelast rets in
  let retrenames := fst (rename_outs rets' (cmd.vars body)) in
  (fmt_c_decl "uintptr_t" args name (List.map snd retrenames), Some r0, retrenames)
  end in
  let decl := fst (fst decl_retvar_retrenames) in
  let retvar := snd (fst decl_retvar_retrenames) in
  let retrenames := snd decl_retvar_retrenames in
  let localvars : list String.string := List_uniq String.eqb (
      let allvars := (List.app (match retvar with None => nil | Some v => cons v nil end) (cmd.vars body)) in
      (List_minus String.eqb allvars args)) in 
    let indent := "  " in
    (match localvars with nil => "" | _ => (variable_declaration' indent (List.map rust_var localvars)) end).


