From Jasmin Require jasmin_compiler.
(* Do not “Require” other modules from Jasmin here:
   expand the jasmin_compiler module instead. *)

(* ---- Begin of inlined Rocq 9.2 / Stdlib extraction preludes -------------
   Replaces
     From Coq Require ExtrOcamlBasic.
     From Coq Require ExtrOcamlNativeString.
     From Coq Require ExtrOCamlInt63.
   of 294b46e's proofs/lang/extraction.v.  Those files Require
   Corelib.extraction.Extraction, which loads the original (buggy)
   rocq-runtime.plugins.extraction; here the patched copy is loaded instead
   and their directives are copied verbatim, in the order in which Rocq would
   load them (Corelib ExtrOcamlBasic, Stdlib ExtrOcamlChar,
   ExtrOcamlNativeString, ExtrOCamlInt63), with names fully qualified
   because the original files use Require Import. *)

Declare ML Module "rocq-extraction-patched.plugin".

From Stdlib Require Ascii String.
From Stdlib.Strings Require Byte.
From Stdlib Require Uint63 Sint63.

(* -- Corelib/extraction/ExtrOcamlBasic.v (Rocq 9.2) -- *)
Extract Inductive bool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
Extract Inductive prod => "( * )" [ "" ].
Extract Inductive sumbool => bool [ true false ].
Extract Inductive sumor => option [ Some None ].
Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".
Extract Inlined Constant eq_rew_r_dep => "(fun _ _ t -> t)".

(* -- Stdlib/extraction/ExtrOcamlChar.v (Stdlib 9.x) -- *)
Extract Inductive Stdlib.Strings.Ascii.ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Extract Constant Stdlib.Strings.Ascii.zero => "'\000'".
Extract Constant Stdlib.Strings.Ascii.one => "'\001'".
Extract Constant Stdlib.Strings.Ascii.shift =>
 "fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".
Extract Inlined Constant Stdlib.Strings.Ascii.ascii_dec => "(=)".
Extract Inlined Constant Stdlib.Strings.Ascii.eqb => "(=)".
Extract Constant Stdlib.Strings.Ascii.compare =>
  "fun c1 c2 ->
    let cmp = Char.compare c1 c2 in
    if cmp < 0 then Lt else if cmp = 0 then Eq else Gt".

(* -- Stdlib/extraction/ExtrOcamlChar.v and ExtrOcamlNativeString.v (the byte
   block is identical in both files; it is given once) -- *)
Extract Inductive Corelib.Init.Byte.byte => char
["'\x00'" "'\x01'" "'\x02'" "'\x03'" "'\x04'" "'\x05'" "'\x06'" "'\x07'" "'\x08'" "'\t'" "'\n'" "'\x0b'" "'\x0c'" "'\r'" "'\x0e'" "'\x0f'" "'\x10'" "'\x11'" "'\x12'" "'\x13'" "'\x14'" "'\x15'" "'\x16'" "'\x17'" "'\x18'" "'\x19'" "'\x1a'" "'\x1b'" "'\x1c'" "'\x1d'" "'\x1e'" "'\x1f'" "' '" "'!'" "'""'" "'#'" "'$'" "'%'" "'&'" "'\''" "'('" "')'" "'*'" "'+'" "','" "'-'" "'.'" "'/'" "'0'" "'1'" "'2'" "'3'" "'4'" "'5'" "'6'" "'7'" "'8'" "'9'" "':'" "';'" "'<'" "'='" "'>'" "'?'" "'@'" "'A'" "'B'" "'C'" "'D'" "'E'" "'F'" "'G'" "'H'" "'I'" "'J'" "'K'" "'L'" "'M'" "'N'" "'O'" "'P'" "'Q'" "'R'" "'S'" "'T'" "'U'" "'V'" "'W'" "'X'" "'Y'" "'Z'" "'['" "'\\'" "']'" "'^'" "'_'" "'`'" "'a'" "'b'" "'c'" "'d'" "'e'" "'f'" "'g'" "'h'" "'i'" "'j'" "'k'" "'l'" "'m'" "'n'" "'o'" "'p'" "'q'" "'r'" "'s'" "'t'" "'u'" "'v'" "'w'" "'x'" "'y'" "'z'" "'{'" "'|'" "'}'" "'~'" "'\x7f'" "'\x80'" "'\x81'" "'\x82'" "'\x83'" "'\x84'" "'\x85'" "'\x86'" "'\x87'" "'\x88'" "'\x89'" "'\x8a'" "'\x8b'" "'\x8c'" "'\x8d'" "'\x8e'" "'\x8f'" "'\x90'" "'\x91'" "'\x92'" "'\x93'" "'\x94'" "'\x95'" "'\x96'" "'\x97'" "'\x98'" "'\x99'" "'\x9a'" "'\x9b'" "'\x9c'" "'\x9d'" "'\x9e'" "'\x9f'" "'\xa0'" "'\xa1'" "'\xa2'" "'\xa3'" "'\xa4'" "'\xa5'" "'\xa6'" "'\xa7'" "'\xa8'" "'\xa9'" "'\xaa'" "'\xab'" "'\xac'" "'\xad'" "'\xae'" "'\xaf'" "'\xb0'" "'\xb1'" "'\xb2'" "'\xb3'" "'\xb4'" "'\xb5'" "'\xb6'" "'\xb7'" "'\xb8'" "'\xb9'" "'\xba'" "'\xbb'" "'\xbc'" "'\xbd'" "'\xbe'" "'\xbf'" "'\xc0'" "'\xc1'" "'\xc2'" "'\xc3'" "'\xc4'" "'\xc5'" "'\xc6'" "'\xc7'" "'\xc8'" "'\xc9'" "'\xca'" "'\xcb'" "'\xcc'" "'\xcd'" "'\xce'" "'\xcf'" "'\xd0'" "'\xd1'" "'\xd2'" "'\xd3'" "'\xd4'" "'\xd5'" "'\xd6'" "'\xd7'" "'\xd8'" "'\xd9'" "'\xda'" "'\xdb'" "'\xdc'" "'\xdd'" "'\xde'" "'\xdf'" "'\xe0'" "'\xe1'" "'\xe2'" "'\xe3'" "'\xe4'" "'\xe5'" "'\xe6'" "'\xe7'" "'\xe8'" "'\xe9'" "'\xea'" "'\xeb'" "'\xec'" "'\xed'" "'\xee'" "'\xef'" "'\xf0'" "'\xf1'" "'\xf2'" "'\xf3'" "'\xf4'" "'\xf5'" "'\xf6'" "'\xf7'" "'\xf8'" "'\xf9'" "'\xfa'" "'\xfb'" "'\xfc'" "'\xfd'" "'\xfe'" "'\xff'"].
Extract Inlined Constant Stdlib.Strings.Byte.eqb => "(=)".
Extract Inlined Constant Stdlib.Strings.Byte.byte_eq_dec => "(=)".
Extract Inlined Constant Stdlib.Strings.Ascii.ascii_of_byte => "(fun x -> x)".
Extract Inlined Constant Stdlib.Strings.Ascii.byte_of_ascii => "(fun x -> x)".

(* -- Stdlib/extraction/ExtrOcamlNativeString.v (Stdlib 9.x) -- *)
Extract Inductive Stdlib.Strings.String.string => "string"
[
(* EmptyString *)
"(* If this appears, you're using String internals. Please don't *)
  """"
"
(* String *)
"(* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)
"
]
"(* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))
".

Extract Inlined Constant Stdlib.Strings.String.string_dec => "(=)".
Extract Inlined Constant Stdlib.Strings.String.eqb => "(=)".
Extract Inlined Constant Stdlib.Strings.String.append => "(^)".
Extract Inlined Constant Stdlib.Strings.String.concat => "String.concat".
Extract Inlined Constant Stdlib.Strings.String.prefix =>
  "(fun s1 s2 ->
     let l1 = String.length s1 and l2 = String.length s2 in
     l1 <= l2 && String.sub s2 0 l1 = s1)".
Extract Inlined Constant Stdlib.Strings.String.string_of_list_ascii =>
  "(fun l ->
      let a = Array.of_list l in
      String.init (Array.length a) (fun i -> a.(i)))".
Extract Inlined Constant Stdlib.Strings.String.list_ascii_of_string =>
  "(fun s -> List.init (String.length s) (fun i -> s.[i]))".
Extract Inlined Constant Stdlib.Strings.String.string_of_list_byte =>
  "(fun l ->
      let a = Array.of_list l in
      String.init (Array.length a) (fun i -> a.(i)))".
Extract Inlined Constant Stdlib.Strings.String.list_byte_of_string =>
  "(fun s -> List.init (String.length s) (fun i -> s.[i]))".


(* -- Stdlib/extraction/ExtrOCamlInt63.v (Stdlib 9.x) -- *)

(** Basic data types used by some primitive operators. *)

Extract Inductive bool => bool [ true false ].
Extract Inductive prod => "( * )" [ "" ].
Extract Inductive DoubleType.carry => "Uint63.carry" [ "Uint63.C0" "Uint63.C1" ].

(** Primitive types and operators. *)
Extract Constant Uint63.int => "Uint63.t".
Extraction Inline Uint63.int.
(* Otherwise, the name conflicts with the primitive OCaml type [int] *)

Extract Constant Uint63.lsl => "Uint63.l_sl".
Extract Constant Uint63.lsr => "Uint63.l_sr".
Extract Constant Sint63.asr => "Uint63.a_sr".
Extract Constant Uint63.land => "Uint63.l_and".
Extract Constant Uint63.lor => "Uint63.l_or".
Extract Constant Uint63.lxor => "Uint63.l_xor".

Extract Constant Uint63.add => "Uint63.add".
Extract Constant Uint63.sub => "Uint63.sub".
Extract Constant Uint63.mul => "Uint63.mul".
Extract Constant Uint63.mulc => "Uint63.mulc".
Extract Constant Uint63.div => "Uint63.div".
Extract Constant Uint63.mod => "Uint63.rem".
Extract Constant Sint63.div => "Uint63.divs".
Extract Constant Sint63.rem => "Uint63.rems".


Extract Constant Uint63.eqb => "Uint63.equal".
Extract Constant Uint63.ltb => "Uint63.lt".
Extract Constant Uint63.leb => "Uint63.le".
Extract Constant Sint63.ltb => "Uint63.lts".
Extract Constant Sint63.leb => "Uint63.les".

Extract Constant Uint63.addc => "Uint63.addc".
Extract Constant Uint63.addcarryc => "Uint63.addcarryc".
Extract Constant Uint63.subc => "Uint63.subc".
Extract Constant Uint63.subcarryc => "Uint63.subcarryc".

Extract Constant Uint63.diveucl => "Uint63.diveucl".
Extract Constant Uint63.diveucl_21 => "Uint63.div21".
Extract Constant Uint63.addmuldiv => "Uint63.addmuldiv".

Extract Constant Uint63.compare => "(fun x y -> let c = Uint63.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Constant Sint63.compare => "(fun x y -> let c = Uint63.compares x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".

Extract Constant Uint63.head0 => "Uint63.head0".
Extract Constant Uint63.tail0 => "Uint63.tail0".

(* ---- End of inlined Stdlib extraction preludes ---- *)

(* This is a hack to force the extraction to keep the singleton here,
   This need should be removed if we add more constructor to syscall_t *)
Extract Inductive syscall.syscall_t => "(Wsize.wsize * BinNums.coq_Z) Syscall_t.syscall_t" ["Syscall_t.RandomBytes"].
Set Extraction File Comment "This prelude is added at extraction time. See lang/extraction.v. *) [@@@ocaml.warning ""-9-20-27-32-33-34-37-39-50-67""] (* End of prelude. ".

Extraction Inline ssrbool.is_left.
Extraction Inline ssrbool.predT ssrbool.pred_of_argType.
Extraction Inline ssrbool.idP.

Extraction Inline utils.assert.
Extraction Inline utils.Result.bind.
Extraction Inline Datatypes.implb.

Extract Constant strings.ascii_eqb => "Char.equal".
Extract Constant strings.ascii_cmp =>
  "(fun x y -> let c = Char.compare x y in if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt else Datatypes.Gt)".

Extract Constant expr.VarInfo.t => "Location.t".
Extract Constant expr.VarInfo.witness => "Location._dummy".
Extract Constant expr.var_info => "Location.t".
Extract Constant expr.InstrInfo.t => "IInfo.t".
Extract Constant expr.InstrInfo.witness => "IInfo.dummy".
Extract Constant expr.InstrInfo.with_location => "IInfo.with_location".
Extract Constant expr.InstrInfo.is_inline => "IInfo.is_inline".
Extract Constant expr.InstrInfo.var_info_of_ii => "IInfo.var_info_of_ii".
Extract Constant expr.instr_info => "IInfo.t".
Extract Constant expr.fun_info => "FInfo.t".
Extract Constant expr.entry_info_of_fun_info => "FInfo.entry_info".
Extract Constant expr.ret_info_of_fun_info => "FInfo.ret_info".
Extract Constant waes.MixColumns => "(fun _ -> failwith ""MixColumns is not implemented"")".
Extract Constant waes.InvMixColumns => "(fun _ -> failwith ""InvMixColumns not implemented"")".

(* Extraction for Var.FunName *)
Extract Constant var.FunName.t   => "CoreIdent.funname".
Extract Constant var.funname     => "CoreIdent.funname".
Extract Constant var.FunName.tag => "CoreIdent.funname_tag".

(* Module Cident *)

Extract Constant ident.Cident.t       => "CoreIdent.Cident.t".
Extract Constant ident.WrapIdent.t    => "CoreIdent.Cident.t".

Extract Constant ident.Cident.tag     => "CoreIdent.Cident.tag".
Extract Constant ident.Cident.id_name => "CoreIdent.Cident.id_name".
Extract Constant ident.Cident.id_kind => "CoreIdent.Cident.id_kind".

Set Extraction Output Directory "lang/ocaml".

Extraction Blacklist String List Nat Uint63 Utils Var Array.

Separate Extraction
  utils
  warray_
  sem_type
  sopn
  expr
  stack_zero_strategy
  lower_spill.spill_uprog
  psem_defs
  sem_params
  sem_params_of_arch_extra
  arch_decl
  arch_extra
  x86_decl
  x86_instr_decl
  x86_extra
  x86_params
  arm_decl
  arm_instr_decl
  arm_extra
  arm_params
  riscv_decl
  riscv_instr_decl
  riscv_extra
  riscv_params
  compiler
  wint_int.
