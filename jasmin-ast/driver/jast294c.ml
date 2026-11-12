(* jast294c: a jasminc-like driver for the Jasmin compiler library of
   jasmin-lang/jasmin commit 294b46e, whose CIL (extracted Rocq part) was
   re-extracted from the .vo files of the Rocq 9.2 switch.

   It does what compiler/src/main_compiler.ml does, minus the safety checker
   (needs apron) and the linter:
     parse .jazz -> preprocess -> [slice] -> [-auto-spill] -> Conv.cuprog_of_prog
     -> [#exec] -> Compile.compile -> Arch.pp_asm to -o file.
   The architecture module is CoreArchFactory.get_arch_module, i.e. the same
   modules SafetyMain.get_arch_with_analyze builds (core_arch_x86 ~use_lea
   ~use_set0 call_conv / Core_arch_ARM / Core_arch_RISCV, then
   Arch_full.Arch_from_Core_arch), without the analyzer.

   Extra mode:  jast294c -rocq-test [-o out.s] ...
     compiles the Jasmin program Jast_test_prog.test_prog, a Rocq term
     ($JAST_TOOLS/rocqtest/jast_test_prog.v) extracted with the same
     extraction directives as the CIL, instantiated with OCaml-side naming
     functions.  No .jazz text is involved.

   Extra mode:  jast294c -bls12-leaves [-leaves-only f1,f2,..] [-o out.s] ...
     compiles BLS12Leaves.bls12_leaves_prog ... K (the BLS12-381 Fp leaves
     bls12_add/sub/mul/square built as a Rocq term from fiat-crypto's bedrock2
     bodies, $JAST_TOOLS/jast/rocq/JasminBridge/Ast/BLS12Leaves.v),
     extracted with the same directives, instantiated exactly as in -rocq-test.
     No .jazz text, no -auto-spill (refused in this mode).  -leaves-only keeps
     only the listed functions of p_funcs (an OCaml-side filter, for
     diagnostics).  -spill-K N (default 8) gives the spill threshold K : nat of
     the term (Datatypes.S^N O). *)

open Jasmin
open Utils
open Prog
open Glob_options
open CLI_errors

exception UsageError

let rocq_test = ref false
let bls12_leaves = ref false
let leaves_only : string list ref = ref []
let spill_k = ref 8
let leaves_v1 = ref false

(* jasminc options that this driver does not implement (safety checker,
   linter). All other options of Glob_options.options are kept. *)
let unsupported =
  [ "-checksafety"; "-safetyparam"; "-safetyconfig"; "-safetymakeconfigdoc";
    "-nocheckalignment"; "-linting-level" ]

let options =
  List.filter (fun (k, _, _) -> not (List.mem k unsupported)) Glob_options.options
  @ [ "-rocq-test", Arg.Set rocq_test,
      " Compile the Jasmin program built as a Rocq term (Jast_test_prog.test_prog, x86-64) instead of a .jazz file";
      "-bls12-leaves", Arg.Set bls12_leaves,
      " Compile the Rocq term BLS12Leaves.bls12_leaves_prog (BLS12-381 Fp add/sub/mul/square, x86-64) instead of a .jazz file";
      "-leaves-only", Arg.String (fun s -> leaves_only := String.split_on_char ',' s),
      "f1,f2,.. With -bls12-leaves: keep only these functions of p_funcs (diagnostic filter on the OCaml side)";
      "-leaves-v1", Arg.Set leaves_v1, " With -bls12-leaves: compile jast's bls12_leaves_prog (Comp.ccmd_sp) instead of bls12_leaves2_prog";
      "-spill-K", Arg.Set_int spill_k,
      "K With -bls12-leaves: the section variable K (a Rocq nat) of bls12_leaves_prog: a fiat variable is spilled when two consecutive occurrences are more than K statements apart (default 8)" ]

let usage_msg =
  "Usage : jast294c [option] filename\n        jast294c -rocq-test [option]\n        jast294c -bls12-leaves [-spill-K N] [-leaves-only f,..] [option]"

let parse () =
  let infiles = ref [] in
  let set_in s = infiles := s :: !infiles in
  if Sys.win32 then set_cc "windows";
  Arg.parse (Arg.align options) set_in usage_msg;
  let c =
    match !color with
    | Auto -> Unix.isatty (Unix.descr_of_out_channel stderr)
    | Always -> true
    | Never -> false
  in
  if c then enable_colors ();
  match !infiles with
  | [] ->
    if !help_intrinsics || !help_version || !rocq_test || !bls12_leaves then ""
    else raise UsageError
  | [ infile ] ->
    if !rocq_test || !bls12_leaves then raise UsageError;
    check_options ();
    check_infile infile;
    infile
  | infile :: s :: _ -> raise (CLIerror (RedundantInputFile (infile, s)))

let get_asm = function
  | Utils0.Ok asm -> asm
  | Utils0.Error e ->
    raise (HiError (Conv.error_of_cerror (Printer.pp_err ~debug:!debug) e))

let output_asm pp_asm asm =
  if !outfile <> "" then begin
    BatFile.with_file_out !outfile (fun out ->
        let fmt = BatFormat.formatter_of_out_channel out in
        Format.fprintf fmt "%a%!" pp_asm asm);
    if !debug then Format.eprintf "assembly listing written@."
  end else if List.mem Compiler.Assembly !print_list then
    Format.printf "%a%!" pp_asm asm

(* -------------------------------------------------------------------- *)
(* .jazz mode: main_compiler.ml without safety checker and linter.        *)
let compile_jazz infile =
  let module Arch = (val CoreArchFactory.get_arch_module !target_arch !call_conv) in

  if !help_intrinsics then (Help.show_intrinsics Arch.asmOp_sopn (); exit 0);
  if !help_version then (Format.printf "%s@." version_string; exit 0);

  let env, pprog, _ast =
    try Compile.parse_file Arch.arch_info ~idirs:!Glob_options.idirs infile
    with
    | Annot.AnnotationError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
    | Pretyping.TyError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror code
    | Syntax.ParseError (loc, msg) ->
      let msg = match msg with None -> "unexpected token" | Some msg -> msg in
      hierror ~loc:(Lone loc) ~kind:"parse error" "%s" msg
  in

  if !print_dependencies then begin
    Format.printf "%a"
      (pp_list " " (fun fmt p -> Format.fprintf fmt "%s" (BatPathGen.OfString.to_string p)))
      (List.tl (List.rev (Pretyping.Env.dependencies env)));
    exit 0
  end;

  List.iter Label_check.warn_duplicate_label (Label_check.get_labels_errors pprog);

  eprint Compiler.Typing (Printer.pp_pprog ~debug:true Arch.pointer_data Arch.msf_size Arch.asmOp) pprog;

  let prog =
    try Compile.preprocess Arch.pointer_data Arch.msf_size Arch.asmOp pprog
    with Typing.TyError (loc, code) -> hierror ~loc:(Lmore loc) ~kind:"typing error" "%s" code
  in
  let prog = if !slice <> [] then Slicing.slice !slice prog else prog in

  let visit_prog_after_pass ~debug s p =
    eprint s (Printer.pp_prog ~debug Arch.pointer_data Arch.msf_size Arch.asmOp) p
  in
  visit_prog_after_pass ~debug:true Compiler.ParamsExpansion prog;

  let prog =
    match !Glob_options.do_auto_spill with
    | None -> prog
    | Some strategy -> AutoSpill.doit strategy prog
  in

  let cprog = Conv.cuprog_of_prog prog in
  if !debug then Printf.eprintf "translated to coq \n%!";

  (* #exec directives, as in main_compiler *)
  let to_exec = Pretyping.Env.Exec.get env in
  let exec { L.pl_loc = loc; L.pl_desc = (f, m) } =
    let ii = L.i_loc0 loc, [] in
    try
      let pp_range fmt (ptr, sz) = Format.fprintf fmt "%a:%a" Z.pp_print ptr Z.pp_print sz in
      Format.printf "/* Evaluation of %s (@[<h>%a@]):@." f.fn_name (pp_list ",@ " pp_range) m;
      let _m, vs =
        (match Evaluator.initial_memory Arch.reg_size (Z.of_string "1024") m with
         | Utils0.Ok m -> m
         | Utils0.Error err -> raise (Evaluator.Eval_error (ii, err)))
        |> Evaluator.run (module Arch) (Expr.to_uprog Arch.asmOp cprog) ii f []
      in
      Format.printf "@[<v>%a@]@." (pp_list "@ " Evaluator.pp_val) vs;
      Format.printf "*/@."
    with Evaluator.Eval_error (ii, err) ->
      let i_loc, _ = ii in
      hierror ~loc:(Lmore i_loc) ~kind:"evaluation error" "%a" Evaluator.pp_error err
  in
  List.iter exec to_exec;

  match Compile.compile (module Arch) visit_prog_after_pass prog cprog with
  | exception Annot.AnnotationError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
  | r ->
    let asm = get_asm r in
    if !Glob_options.print_export_info_json then
      Format.printf "%a" (fun fmt -> PrintExportInfo.pp_export_info_json fmt env prog) asm;
    output_asm Arch.pp_asm asm

(* -------------------------------------------------------------------- *)
(* -rocq-test / -bls12-leaves modes: compile an extracted Rocq term
   (Jast_test_prog.test_prog or BLS12Leaves.bls12_leaves_prog) *)
let compile_rocq_term () =
  let mode = if !bls12_leaves then "-bls12-leaves" else "-rocq-test" in
  if !target_arch <> X86_64 then
    hierror ~loc:Lnone ~kind:"parsing arguments" "%s is x86-64 only" mode;
  if !bls12_leaves && !Glob_options.do_auto_spill <> None then
    hierror ~loc:Lnone ~kind:"parsing arguments"
      "-bls12-leaves compiles the Rocq term as is: -auto-spill (an OCaml source transformation) is not allowed";
  if !rocq_test && !bls12_leaves then
    hierror ~loc:Lnone ~kind:"parsing arguments" "-rocq-test and -bls12-leaves are exclusive";
  let module C =
    (val CoreArchFactory.core_arch_x86 ~use_lea:!Glob_options.lea
           ~use_set0:!Glob_options.set0 !call_conv) in
  let module Arch = Arch_full.Arch_from_Core_arch (C) in

  (* OCaml-side instances of the section variables of jast_test_prog.v
     (and, identically, of BLS12Leaves.v) *)
  let vars = Hashtbl.create 17 in
  let name (s : string) : CoreIdent.var =
    match Hashtbl.find_opt vars s with
    | Some v -> v
    | None ->
      let v = CoreIdent.V.mk s (Wsize.Reg (Wsize.Normal, Wsize.Direct))
          (CoreIdent.Bty (CoreIdent.U Wsize.U64)) Location._dummy [] in
      Hashtbl.add vars s v; v
  in
  (* the boolean carry variable of BLS12Leaves2 (its own identifier, of type bool) *)
  let cfn : CoreIdent.var =
    CoreIdent.V.mk "cf" (Wsize.Reg (Wsize.Normal, Wsize.Direct)) (CoreIdent.Bty CoreIdent.Bool) Location._dummy [] in
  let funs = Hashtbl.create 17 in
  let fname (s : string) : CoreIdent.funname =
    match Hashtbl.find_opt funs s with
    | Some f -> f
    | None -> let f = CoreIdent.F.mk s in Hashtbl.add funs s f; f
  in
  let finfo (s : string) : FInfo.t =
    (* = FInfo.f_annot_empty, except that -stack-zero / -stack-zero-size are
       honoured exactly as for an un-annotated "export fn" in a .jazz file *)
    let annot = FunctionAnnotations.process_f_annot Location._dummy s FInfo.Export [] in
    (Location._dummy, annot, FInfo.Export,
     { FInfo.ret_annot = []; FInfo.ret_loc = Location._dummy })
  in
  (* one fresh instruction location (unique uid) per instruction index *)
  let iinfos = Hashtbl.create 17 in
  let iinfo (n : BinNums.positive) : IInfo.t =
    match Hashtbl.find_opt iinfos n with
    | Some ii -> ii
    | None -> let ii = (Location.i_loc0 Location._dummy, []) in Hashtbl.add iinfos n ii; ii
  in
  (* atoI: the very record the x86 Arch module uses (X86_arch_full.atoI x86_decl) *)
  let atoI = C.asm_e.Arch_extra._atoI in

  let cprog =
    if !bls12_leaves then begin
      (* bls12_leaves_prog : uprog (extras of the progUnit instance, erased to Obj.t by
         extraction); with progUnit, uprog is convertible to _uprog in Rocq (Expr.to_uprog
         is the identity, extracted to Obj.magic), so this is the reverse identity cast. *)
      if !spill_k < 0 then hierror ~loc:Lnone ~kind:"parsing arguments" "-spill-K: negative";
      let rec nat_of_int acc n = if n = 0 then acc else nat_of_int (Datatypes.S acc) (n - 1) in
      let k = nat_of_int Datatypes.O !spill_k in
      let p : _ Expr._uprog =
        if !leaves_v1 then Obj.magic (BLS12Leaves.bls12_leaves_prog atoI name fname finfo iinfo k)
        else Obj.magic (BLS12Leaves2.bls12_leaves2_prog atoI name cfn fname finfo iinfo k) in
      if !leaves_only = [] then p
      else begin
        let names = List.map (fun (f, _) -> f.CoreIdent.fn_name) p.Expr.p_funcs in
        List.iter (fun s -> if not (List.mem s names) then
                      hierror ~loc:Lnone ~kind:"parsing arguments" "-leaves-only: no function %s" s)
          !leaves_only;
        { p with Expr.p_funcs =
                   List.filter (fun (f, _) -> List.mem f.CoreIdent.fn_name !leaves_only) p.Expr.p_funcs }
      end
    end else hierror ~loc:Lnone ~kind:"parsing arguments" "-rocq-test: not built in this driver" in
  let prog = Conv.prog_of_cuprog cprog in

  let visit_prog_after_pass ~debug s p =
    eprint s (Printer.pp_prog ~debug Arch.pointer_data Arch.msf_size Arch.asmOp) p
  in
  visit_prog_after_pass ~debug:true Compiler.ParamsExpansion prog;

  match Compile.compile (module Arch) visit_prog_after_pass prog cprog with
  | exception Annot.AnnotationError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
  | r -> output_asm Arch.pp_asm (get_asm r)

(* -------------------------------------------------------------------- *)
let main () =
  try
    let infile = parse () in
    if !rocq_test || !bls12_leaves then compile_rocq_term () else compile_jazz infile
  with
  | Utils.HiError e ->
    Format.eprintf "%a@." pp_hierror e;
    exit 1
  | UsageError ->
    Arg.usage (Arg.align options) usage_msg;
    exit 1
  | CLIerror e ->
    Format.eprintf "%a: %s.\n" (pp_print_bold_red Format.pp_print_string) "Error" (pp_cli_error e);
    exit 1

let () = main ()
