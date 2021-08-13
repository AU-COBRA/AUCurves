(*Rust Backend for Bedrock2 project. We mirror the approach og Bedrock2/src/Bedrock22/ToCString.v*)
Require Import bedrock2.Syntax bedrock2.Variables. Import bopname.
Require Import coqutil.Datatypes.ListSet.
Require Import Coq.ZArith.BinIntDef Coq.Numbers.BinNums Coq.Numbers.DecimalString.
Require Import Coq.Strings.String. Local Open Scope string_scope.

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

Definition rust_var := @id string.
Definition rust_fun := @id string.

Definition rust_lit' w := DecimalString.NilZero.string_of_int (BinInt.Z.to_int w) ++ "usize".

Definition rust_lit w :=
  match w with 
    | Z.pos _ => rust_lit' w
    | Z.neg _ => "usize::MAX"
    | _ => rust_lit' w
  end.

Definition rust_bop e1 op e2 :=
  match op with
  | add => e1++".wrapping_add" ++ e2
  | sub => e1++".wrapping_sub" ++ e2
  | mul => e1++".wrapping_mul" ++ e2
  (*For now, only 64-bit implementations are supported.*)
  | mulhuu => "((" ++ e1 ++ " as u128).wrapping_mul(" ++ e2 ++ " as u128) >> 64) as usize"
  (*Not needed for BLS12*)
  (* | divu => e1++"/"++e2 *)
  (* | remu => e1++"%"++e2 *)
  | and => e1++"&"++e2
  | or => e1++"|"++e2
  | xor => e1++"^"++e2
  | sru => e1++">>"++e2
  | slu => e1++"<<"++e2
  (* | srs => "(intptr_t)"++e1++">>"++e2 *)
  (* | lts => "(intptr_t)"++e1++"<"++"(intptr_t)"++e2 *)
  | ltu => "(" ++ e1 ++ "<" ++ e2 ++ ") as usize"
  | eq => "(" ++ e1 ++ "==" ++ e2 ++ ") as usize"
  | _ => "" (*Todo: implement missing operations; for now only operations necessary for Fp2 arithmetic is supported*)
  end%string.

  Definition rust_size (s : access_size) : string :=
  match s with
  | access_size.one => "1"
  | access_size.two => "2"
  | access_size.four => "4"
  | access_size.word => "8" (*For now, only 64-bit is supported*)
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
  | add => "_br2_load((" ++ rust_ptr_varlit e1 ++ " as *const u8).wrapping_add(" ++ rust_ptr_varlit e2 ++ ") as *const usize)"
  | _ => ""
  end.

  Definition rust_store_ptr_op e1 op e2 : string :=
  match op with
  | add => "_br2_store((" ++ rust_ptr_varlit e1 ++ " as *const u8).wrapping_add(" ++ rust_ptr_varlit e2 ++ ") as *mut usize, "
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
| expr.op op e1 e2 => rust_bop ("(" ++ rust_store_expr e1 ++ ")") op ("(" ++ rust_store_expr e2 ++ ")")
end.

Definition rust_ptr_expr (e : expr) : string :=
  match e with
  | expr.op op e1 e2 => rust_ptr_op e1 op e2
  | _ => ""
  end.

  
Fixpoint rust_expr (e : expr) : string :=
match e with
| expr.literal v => rust_lit v
| expr.var x => rust_var x
| expr.load s ea =>  rust_ptr_expr ea
| expr.op op e1 e2 => rust_bop ("(" ++ rust_expr e1 ++ ")") op ("(" ++ rust_expr e2 ++ ")")
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
    indent ++ "let " ++ rust_var x ++ "_arr = [0usize; " ++ rust_lit (bytes_to_words n) ++ "];" ++ LF ++
    indent ++ "let " ++ rust_var x ++ " = " ++ rust_var x ++ "_arr.as_ptr();" ++ LF ++
    rust_cmd indent body 
  | cmd.set x ev =>
    indent ++ rust_var x ++ " = " ++ rust_expr ev ++ ";" ++ LF
  (* | cmd.unset x =>
    indent ++ "// unset " ++ c_var x ++ LF
  | cmd.cond eb t f =>
    indent ++ "if (" ++ c_expr eb ++ ") {" ++ LF ++
      c_cmd ("  "++indent) t ++
    indent ++ "} else {" ++ LF ++
      c_cmd ("  "++indent) f ++
    indent ++ "}" ++ LF *)
  (* | cmd.while eb c =>
    indent ++ "while (" ++ c_expr eb ++ ") {" ++ LF ++
      c_cmd ("  "++indent) c ++
    indent ++ "}" ++ LF *)
  | cmd.seq c1 c2 =>
    rust_cmd indent c1 ++
    rust_cmd indent c2
  | cmd.skip =>
    indent ++ "/*skip*/" ++ LF
  | cmd.call args f es =>
    indent ++ rust_call (List.map rust_var args) (rust_fun f) (List.map rust_expr es)
  (* | cmd.interact binds action es =>
    indent ++ c_act binds action (List.map c_expr es) *)
  | _ => ""
  end.

  Definition fmt_c_decl (rett : string) (args : list String.string) (name : String.string) (retptrs : list String.string) : string :=
    ("pub unsafe fn " ++ rust_fun name ++ "(" ++ concat ", " (
                    List.map (fun a => rust_var a ++ " : *const usize") args ++
                    List.map (fun r => rust_var r ++ " : *const usize") retptrs) ++
                  ") -> ()").

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
  indent ++ "let " ++ (concat (" : usize;" ++ LF ++ indent ++ "let ") local_vars) ++ " : usize;" ++ LF.

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


