(** * ToSafeRustString: Safe Rust wrapper generator for bedrock2 functions.
 *
 * Reads function descriptions (name, parameters with types and access modes)
 * and emits safe Rust code with newtype wrappers and proper references.
 *
 * Key insight: bedrock2's separation logic specs tell us:
 *   - FElem in postcondition unchanged → &T (shared reference)
 *   - FElem in postcondition changed → &mut T (mutable reference)
 *   - Same pointer used for input and output → in-place op (single &mut T)
 *   - Separating conjunction (⋆) → distinct references (Rust borrow checker)
 *
 * The spec witnesses below are written manually but designed to be derivable
 * from `fnspec!` instances by inspection. A future version can mechanically
 * extract them from the bedrock2 spec_of typeclass instances.
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string_scope.

(* ================================================================ *)
(* Output formatting helpers                                          *)
(* ================================================================ *)

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".
Definition QUOTE : string := String (Coq.Strings.Ascii.Ascii false true false false false true false false) "".

Fixpoint join (sep : string) (l : list string) : string :=
  match l with
  | [] => ""
  | [x] => x
  | x :: rest => x ++ sep ++ join sep rest
  end.

Definition nat_to_string (n : nat) : string :=
  DecimalString.NilZero.string_of_int (Nat.to_int n).

(* ================================================================ *)
(* Field type descriptions                                           *)
(* ================================================================ *)

(** A field type kind. Determines the Rust newtype layout and
    extern-call boundary representation. *)
Inductive field_kind :=
  | KLimbs       (* [u64; ft_limbs] — original behavior; field elements *)
  | KBytes       (* [u8; ft_limbs] — fixed-size byte buffers (seed, sig, pk) *)
  | KBytesSlice  (* &[u8] — variable-length byte spans (msg); expands to (ptr, len) on extern *)
  | KUsize.      (* usize — raw integer; ft_limbs ignored *)

(** A field type: name (e.g., "Fp"), number of limbs/bytes, kind. *)
Record field_type := {
  ft_name : string;
  ft_limbs : nat;
  ft_kind : field_kind;
}.

(* ================================================================ *)
(* Parameter modes                                                    *)
(* ================================================================ *)

(** A parameter is read-only, mutated, or both (in-place).
    [ParamInOut] is for in-place operations like [add(out, x, out)]
    where the spec allows the output buffer to alias an input. *)
Inductive param_mode :=
  | ParamIn       (* &T  — read-only *)
  | ParamOut      (* &mut T — write-only (initial value irrelevant) *)
  | ParamInOut.   (* &mut T — read and write *)

Record param_spec := {
  param_name : string;
  param_type : field_type;
  param_mode_val : param_mode;
}.

Record wrapper_spec := {
  wrapper_rust_name : string;  (* safe Rust function name *)
  wrapper_c_name : string;     (* raw C/Jasmin function name *)
  wrapper_params : list param_spec;
}.

(* ================================================================ *)
(* Helper constructors (concise syntax for wrapper specs)            *)
(* ================================================================ *)

Definition mk_in (name : string) (ty : field_type) : param_spec :=
  {| param_name := name; param_type := ty; param_mode_val := ParamIn |}.

Definition mk_out (name : string) (ty : field_type) : param_spec :=
  {| param_name := name; param_type := ty; param_mode_val := ParamOut |}.

Definition mk_inout (name : string) (ty : field_type) : param_spec :=
  {| param_name := name; param_type := ty; param_mode_val := ParamInOut |}.

(* ================================================================ *)
(* Newtype declaration generation                                    *)
(* ================================================================ *)

(** Whether a field type needs a generated newtype declaration.
    KLimbs and KBytes do (fixed-size containers); KBytesSlice and
    KUsize don't (use Rust built-ins directly). *)
Definition needs_newtype (ft : field_type) : bool :=
  match ft_kind ft with
  | KLimbs | KBytes => true
  | KBytesSlice | KUsize => false
  end.

(** Emit `#[repr(transparent)] pub struct Fp(pub [u64; N]);` for a [KLimbs]
    field type, or `pub struct Sig(pub [u8; N]);` for a [KBytes] one.
    The transparent repr ensures the layout matches the raw array,
    so passing &Sig to extern "C" functions is correct. *)
Definition gen_newtype (ft : field_type) : string :=
  match ft_kind ft with
  | KLimbs =>
      "#[repr(transparent)]" ++ LF ++
      "#[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
      "pub struct " ++ ft_name ft ++ "(pub [u64; " ++ nat_to_string (ft_limbs ft) ++ "]);" ++ LF ++ LF ++
      "impl " ++ ft_name ft ++ " {" ++ LF ++
      "    /// Create from raw little-endian limbs (Montgomery form)." ++ LF ++
      "    #[inline] pub const fn from_limbs(limbs: [u64; " ++ nat_to_string (ft_limbs ft) ++ "]) -> Self { " ++ ft_name ft ++ "(limbs) }" ++ LF ++
      "    /// Zero element." ++ LF ++
      "    #[inline] pub const fn zero() -> Self { " ++ ft_name ft ++ "([0u64; " ++ nat_to_string (ft_limbs ft) ++ "]) }" ++ LF ++
      "    /// Borrow as raw limb array." ++ LF ++
      "    #[inline] pub fn as_limbs(&self) -> &[u64; " ++ nat_to_string (ft_limbs ft) ++ "] { &self.0 }" ++ LF ++
      "    /// Mutably borrow as raw limb array." ++ LF ++
      "    #[inline] pub fn as_limbs_mut(&mut self) -> &mut [u64; " ++ nat_to_string (ft_limbs ft) ++ "] { &mut self.0 }" ++ LF ++
      "}" ++ LF
  | KBytes =>
      "#[repr(transparent)]" ++ LF ++
      "#[derive(Clone, Copy, Debug, PartialEq, Eq)]" ++ LF ++
      "pub struct " ++ ft_name ft ++ "(pub [u8; " ++ nat_to_string (ft_limbs ft) ++ "]);" ++ LF ++ LF ++
      "impl " ++ ft_name ft ++ " {" ++ LF ++
      "    /// Create from raw bytes." ++ LF ++
      "    #[inline] pub const fn from_bytes(bytes: [u8; " ++ nat_to_string (ft_limbs ft) ++ "]) -> Self { " ++ ft_name ft ++ "(bytes) }" ++ LF ++
      "    /// Zero buffer." ++ LF ++
      "    #[inline] pub const fn zero() -> Self { " ++ ft_name ft ++ "([0u8; " ++ nat_to_string (ft_limbs ft) ++ "]) }" ++ LF ++
      "    /// Borrow as raw byte array." ++ LF ++
      "    #[inline] pub fn as_bytes(&self) -> &[u8; " ++ nat_to_string (ft_limbs ft) ++ "] { &self.0 }" ++ LF ++
      "    /// Mutably borrow as raw byte array." ++ LF ++
      "    #[inline] pub fn as_bytes_mut(&mut self) -> &mut [u8; " ++ nat_to_string (ft_limbs ft) ++ "] { &mut self.0 }" ++ LF ++
      "}" ++ LF
  | KBytesSlice | KUsize => ""  (* no newtype emitted — uses Rust built-in types *)
  end.

Definition gen_all_newtypes (types : list field_type) : string :=
  join LF (List.map gen_newtype (List.filter needs_newtype types)).

(* ================================================================ *)
(* Wrapper code generation                                           *)
(* ================================================================ *)

(** Map a parameter spec to a Rust safe-wrapper parameter type. *)
Definition rust_ref (ps : param_spec) : string :=
  let ft := param_type ps in
  match ft_kind ft with
  | KLimbs | KBytes =>
      match param_mode_val ps with
      | ParamOut | ParamInOut => "&mut " ++ ft_name ft
      | ParamIn               => "&" ++ ft_name ft
      end
  | KBytesSlice =>
      match param_mode_val ps with
      | ParamOut | ParamInOut => "&mut [u8]"
      | ParamIn               => "&[u8]"
      end
  | KUsize => "usize"
  end.

(** Convert a parameter to its argument list for the unsafe extern call.
    Returns a list of strings — most kinds emit one arg; KBytesSlice
    emits TWO (pointer + length). *)
Definition rust_cast_args (ps : param_spec) : list string :=
  let ft := param_type ps in
  match ft_kind ft with
  | KLimbs =>
      [match param_mode_val ps with
       | ParamOut | ParamInOut => param_name ps ++ ".as_limbs_mut().as_mut_ptr() as usize"
       | ParamIn               => param_name ps ++ ".as_limbs().as_ptr() as usize"
       end]
  | KBytes =>
      [match param_mode_val ps with
       | ParamOut | ParamInOut => param_name ps ++ ".as_bytes_mut().as_mut_ptr() as usize"
       | ParamIn               => param_name ps ++ ".as_bytes().as_ptr() as usize"
       end]
  | KBytesSlice =>
      let ptr := match param_mode_val ps with
                 | ParamOut | ParamInOut => param_name ps ++ ".as_mut_ptr() as usize"
                 | ParamIn               => param_name ps ++ ".as_ptr() as usize"
                 end in
      let len := param_name ps ++ ".len()" in
      [ptr; len]
  | KUsize => [param_name ps]
  end.

(** Number of C/extern args this parameter expands to. *)
Definition extern_arity (ps : param_spec) : nat :=
  match ft_kind (param_type ps) with
  | KBytesSlice => 2
  | _ => 1
  end.

(** Generate the extern "C" parameter declarations for a single param. *)
Definition gen_extern_param (ps : param_spec) : list string :=
  match ft_kind (param_type ps) with
  | KBytesSlice =>
      [param_name ps ++ "_ptr: usize"; param_name ps ++ "_len: usize"]
  | _ => [param_name ps ++ ": usize"]
  end.

(** Generate the extern "C" declaration for a function. *)
Definition gen_extern_decl (ws : wrapper_spec) : string :=
  let params := wrapper_params ws in
  let c_params := List.flat_map gen_extern_param params in
  "    fn " ++ wrapper_c_name ws ++ "(" ++ join ", " c_params ++ ");".

(** Generate the safe Rust wrapper function. *)
Definition gen_safe_wrapper (ws : wrapper_spec) : string :=
  let params := wrapper_params ws in
  let param_decls := List.map (fun ps => param_name ps ++ ": " ++ rust_ref ps) params in
  let call_args := List.flat_map rust_cast_args params in
  "/// Safe wrapper for `" ++ wrapper_c_name ws ++ "`." ++ LF ++
  "///" ++ LF ++
  "/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker." ++ LF ++
  "/// Safety follows from the bedrock2 separation logic proof of `" ++ wrapper_c_name ws ++ "`." ++ LF ++
  "#[inline]" ++ LF ++
  "pub fn " ++ wrapper_rust_name ws ++ "(" ++
    join ", " param_decls ++ ") {" ++ LF ++
  "    unsafe { " ++ wrapper_c_name ws ++ "(" ++
    join ", " call_args ++ ") }" ++ LF ++
  "}" ++ LF.

(** Generate a complete safe Rust module. *)
Definition gen_module (module_name : string) (types : list field_type) (wrappers : list wrapper_spec) : string :=
  "//! Safe Rust wrappers for verified " ++ module_name ++ " arithmetic." ++ LF ++
  "//!" ++ LF ++
  "//! Generated from bedrock2 separation logic specifications." ++ LF ++
  "//! - Read-only buffers map to `&T` (shared references)." ++ LF ++
  "//! - Mutated buffers map to `&mut T` (mutable references)." ++ LF ++
  "//! - Separating conjunction (⋆) maps to Rust's aliasing XOR mutability." ++ LF ++
  "//!" ++ LF ++
  "//! All `unsafe` is confined to the wrapper bodies; the API is safe." ++ LF ++
  "#![allow(non_camel_case_types)]" ++ LF ++ LF ++
  gen_all_newtypes types ++ LF ++
  "extern " ++ QUOTE ++ "C" ++ QUOTE ++ " {" ++ LF ++
    join LF (List.map gen_extern_decl wrappers) ++ LF ++
  "}" ++ LF ++ LF ++
  join LF (List.map gen_safe_wrapper wrappers).

(* ================================================================ *)
(* Curve instantiations                                              *)
(* ================================================================ *)

(** BLS12 / BN254 share types for the 2-3-2 tower. *)
Definition Fp_381  := {| ft_name := "Fp"; ft_limbs := 6; ft_kind := KLimbs |}.
Definition Fp2_381 := {| ft_name := "Fp2"; ft_limbs := 12; ft_kind := KLimbs |}.
Definition Fp6_381 := {| ft_name := "Fp6"; ft_limbs := 36; ft_kind := KLimbs |}.
Definition Fp12_381 := {| ft_name := "Fp12"; ft_limbs := 72; ft_kind := KLimbs |}.

Definition bls12_381_types : list field_type :=
  [Fp_381; Fp2_381; Fp6_381; Fp12_381].

Definition bls12_381_wrappers : list wrapper_spec := [
  {| wrapper_rust_name := "fp_add";
     wrapper_c_name := "bls12_add";
     wrapper_params := [mk_out "out" Fp_381; mk_in "x" Fp_381; mk_in "y" Fp_381] |};

  {| wrapper_rust_name := "fp_sub";
     wrapper_c_name := "bls12_sub";
     wrapper_params := [mk_out "out" Fp_381; mk_in "x" Fp_381; mk_in "y" Fp_381] |};

  {| wrapper_rust_name := "fp_mul";
     wrapper_c_name := "bls12_mul";
     wrapper_params := [mk_out "out" Fp_381; mk_in "x" Fp_381; mk_in "y" Fp_381] |};

  {| wrapper_rust_name := "fp_square";
     wrapper_c_name := "bls12_square";
     wrapper_params := [mk_out "out" Fp_381; mk_in "x" Fp_381] |};

  {| wrapper_rust_name := "fp2_add";
     wrapper_c_name := "bls12_Fp2_add";
     wrapper_params := [mk_out "out" Fp2_381; mk_in "x" Fp2_381; mk_in "y" Fp2_381] |};

  {| wrapper_rust_name := "fp2_mul";
     wrapper_c_name := "bls12_Fp2_mul";
     wrapper_params := [mk_out "out" Fp2_381; mk_in "x" Fp2_381; mk_in "y" Fp2_381] |};

  {| wrapper_rust_name := "fp12_mul";
     wrapper_c_name := "bls12_Fp12_mul";
     wrapper_params := [mk_out "out" Fp12_381; mk_in "x" Fp12_381; mk_in "y" Fp12_381] |};

  {| wrapper_rust_name := "fp12_square";
     wrapper_c_name := "bls12_Fp12_square";
     wrapper_params := [mk_out "out" Fp12_381; mk_in "x" Fp12_381] |};

  {| wrapper_rust_name := "miller_loop";
     wrapper_c_name := "bls12_miller_loop";
     wrapper_params := [mk_out "out" Fp12_381;
                        mk_in "p_x" Fp_381; mk_in "p_y" Fp_381;
                        mk_in "q_x" Fp2_381; mk_in "q_y" Fp2_381] |};

  {| wrapper_rust_name := "pairing";
     wrapper_c_name := "bls12_pairing";
     wrapper_params := [mk_out "out" Fp12_381;
                        mk_in "p_x" Fp_381; mk_in "p_y" Fp_381;
                        mk_in "q_x" Fp2_381; mk_in "q_y" Fp2_381] |}
].

(** BN254: same tower, smaller limbs (4 instead of 6). *)
Definition Fp_bn254 := {| ft_name := "Fp"; ft_limbs := 4; ft_kind := KLimbs |}.
Definition Fp2_bn254 := {| ft_name := "Fp2"; ft_limbs := 8; ft_kind := KLimbs |}.
Definition Fp6_bn254 := {| ft_name := "Fp6"; ft_limbs := 24; ft_kind := KLimbs |}.
Definition Fp12_bn254 := {| ft_name := "Fp12"; ft_limbs := 48; ft_kind := KLimbs |}.

Definition bn254_types : list field_type :=
  [Fp_bn254; Fp2_bn254; Fp6_bn254; Fp12_bn254].

Definition bn254_wrappers : list wrapper_spec := [
  {| wrapper_rust_name := "fp_add";
     wrapper_c_name := "bn254_add";
     wrapper_params := [mk_out "out" Fp_bn254; mk_in "x" Fp_bn254; mk_in "y" Fp_bn254] |};

  {| wrapper_rust_name := "fp_mul";
     wrapper_c_name := "bn254_mul";
     wrapper_params := [mk_out "out" Fp_bn254; mk_in "x" Fp_bn254; mk_in "y" Fp_bn254] |};

  {| wrapper_rust_name := "fp_square";
     wrapper_c_name := "bn254_square";
     wrapper_params := [mk_out "out" Fp_bn254; mk_in "x" Fp_bn254] |};

  {| wrapper_rust_name := "pairing";
     wrapper_c_name := "bn254_pairing";
     wrapper_params := [mk_out "out" Fp12_bn254;
                        mk_in "p_x" Fp_bn254; mk_in "p_y" Fp_bn254;
                        mk_in "q_x" Fp2_bn254; mk_in "q_y" Fp2_bn254] |}
].

(* ================================================================ *)
(* Extraction targets                                                *)
(* ================================================================ *)

Definition bls12_381_safe_rust : string :=
  gen_module "BLS12_381" bls12_381_types bls12_381_wrappers.

Definition bn254_safe_rust : string :=
  gen_module "BN254" bn254_types bn254_wrappers.
