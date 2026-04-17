(** * Generic cubic extension bedrock2 function bodies.

    Defines bedrock2 functions for add, sub, mul, sqr, opp, copy, zero, one,
    inv on BaseField × BaseField × BaseField, parameterized over:
      - Base field FieldParameters + FieldRepresentation
      - A [mul_by_nr] bedrock2 function (multiply by cubic nonresidue)

    Each function calls base field operations component-wise (for add/sub/opp)
    or uses the Karatsuba / Chung-Hasan / cubic-inv formulas (for mul/sqr/inv).

    WP proofs are deferred — this file contains function definitions
    and spec instance declarations only. *)

Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.

Local Open Scope Z_scope.

Section GenericCubicExt.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {BaseField : Type}.
  Context {base_fp : FieldParameters BaseField}.
  Context {base_repr : @FieldRepresentation BaseField base_fp width BW word mem}.
  Context {base_repr_ok : @FieldRepresentation_ok BaseField base_fp width BW word mem base_repr}.

  Variable mul_by_nr_model : BaseField -> BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Notation CE := (BaseField * BaseField * BaseField)%type.

  (* Import generic specs *)
  Local Instance CE_fp : FieldParameters CE :=
    CE_field_parameters mul_by_nr_model prefix eq_dec_base.
  Local Instance CE_repr : @FieldRepresentation CE CE_fp width BW word mem :=
    CE_field_representation mul_by_nr_model prefix eq_dec_base.

  (* ================================================================ *)
  (* Field names                                                       *)
  (* ================================================================ *)

  Context {CE_names : FieldNames (F := CE)}.
  Context {base_names : FieldNames (F := BaseField)}.

  (* ================================================================ *)
  (* Memory layout                                                     *)
  (* ================================================================ *)

  Local Notation base_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (@felem_size_in_words _ base_fp _ _ _ _ base_repr)).

  (** Pointer arithmetic for the 3 base-field components. *)
  Definition ce_expr_c0 (x : Syntax.expr) : Syntax.expr := x.
  Definition ce_expr_c1 (x : Syntax.expr) : Syntax.expr :=
    expr.op bopname.add x (expr.literal base_felem_offset).
  Definition ce_expr_c2 (x : Syntax.expr) : Syntax.expr :=
    expr.op bopname.add x (expr.literal (2 * base_felem_offset)).

  (* ================================================================ *)
  (* mul_by_nonresidue: provided as a variable function                *)
  (* ================================================================ *)

  Variable mul_by_nr_name : string.
  Variable Mul_by_nr_func : string * (list String.string * list String.string * Syntax.cmd.cmd).
  Hypothesis Mul_by_nr_name_eq : fst Mul_by_nr_func = mul_by_nr_name.

  (* ================================================================ *)
  (* Function definitions                                              *)
  (* ================================================================ *)

  Import Syntax BinInt String List.ListNotations.

  (** Copy: copy 3 components. *)
  Definition CE_felem_copy : string * Syntax.func :=
    (felem_copy (F := CE),
     (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (felem_copy (F := BaseField)) [ce_expr_c0 (expr.var "out"); ce_expr_c0 (expr.var "x")]);
      coq:(cmd.call [] (felem_copy (F := BaseField)) [ce_expr_c1 (expr.var "out"); ce_expr_c1 (expr.var "x")]);
      coq:(cmd.call [] (felem_copy (F := BaseField)) [ce_expr_c2 (expr.var "out"); ce_expr_c2 (expr.var "x")])
    ))).

  (** Zero: set all 3 components to zero. *)
  Definition CE_zero_func : string * Syntax.func :=
    (zero (F := CE),
     (["out"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (zero (F := BaseField)) [ce_expr_c0 (expr.var "out")]);
      coq:(cmd.call [] (zero (F := BaseField)) [ce_expr_c1 (expr.var "out")]);
      coq:(cmd.call [] (zero (F := BaseField)) [ce_expr_c2 (expr.var "out")])
    ))).

  (** One: c0 = 1, c1 = c2 = 0. *)
  Definition CE_one_func : string * Syntax.func :=
    (one (F := CE),
     (["out"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (one (F := BaseField)) [ce_expr_c0 (expr.var "out")]);
      coq:(cmd.call [] (zero (F := BaseField)) [ce_expr_c1 (expr.var "out")]);
      coq:(cmd.call [] (zero (F := BaseField)) [ce_expr_c2 (expr.var "out")])
    ))).

  (** Opp: negate each component. *)
  Definition CE_opp : string * Syntax.func :=
    (opp (F := CE),
     (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (opp (F := BaseField)) [ce_expr_c0 (expr.var "out"); ce_expr_c0 (expr.var "x")]);
      coq:(cmd.call [] (opp (F := BaseField)) [ce_expr_c1 (expr.var "out"); ce_expr_c1 (expr.var "x")]);
      coq:(cmd.call [] (opp (F := BaseField)) [ce_expr_c2 (expr.var "out"); ce_expr_c2 (expr.var "x")])
    ))).

  (** Add: copy inputs, add components. *)
  Definition CE_add : string * Syntax.func :=
    (add (F := CE),
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := CE)) as allocx;
      stackalloc (felem_size_in_bytes (F := CE)) as allocy;
      coq:(cmd.call [] (felem_copy (F := CE)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (felem_copy (F := CE)) [expr.var "allocy"; expr.var "iny"]);
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c0 (expr.var "out"); ce_expr_c0 (expr.var "allocx"); ce_expr_c0 (expr.var "allocy")]);
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c1 (expr.var "out"); ce_expr_c1 (expr.var "allocx"); ce_expr_c1 (expr.var "allocy")]);
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c2 (expr.var "out"); ce_expr_c2 (expr.var "allocx"); ce_expr_c2 (expr.var "allocy")])
    ))).

  (** Sub: copy inputs, subtract components. *)
  Definition CE_sub : string * Syntax.func :=
    (sub (F := CE),
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := CE)) as allocx;
      stackalloc (felem_size_in_bytes (F := CE)) as allocy;
      coq:(cmd.call [] (felem_copy (F := CE)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (felem_copy (F := CE)) [expr.var "allocy"; expr.var "iny"]);
      coq:(cmd.call [] (sub (F := BaseField)) [ce_expr_c0 (expr.var "out"); ce_expr_c0 (expr.var "allocx"); ce_expr_c0 (expr.var "allocy")]);
      coq:(cmd.call [] (sub (F := BaseField)) [ce_expr_c1 (expr.var "out"); ce_expr_c1 (expr.var "allocx"); ce_expr_c1 (expr.var "allocy")]);
      coq:(cmd.call [] (sub (F := BaseField)) [ce_expr_c2 (expr.var "out"); ce_expr_c2 (expr.var "allocx"); ce_expr_c2 (expr.var "allocy")])
    ))).

  (** Multiplication: Karatsuba for cubic extension.
      a0b0 = a.c0 * b.c0
      a1b1 = a.c1 * b.c1
      a2b2 = a.c2 * b.c2
      t0 = (a.c1 + a.c2)(b.c1 + b.c2) - a1b1 - a2b2
      c0 = a0b0 + nr(t0)
      t1 = (a.c0 + a.c1)(b.c0 + b.c1) - a0b0 - a1b1
      c1 = t1 + nr(a2b2)
      t2 = (a.c0 + a.c2)(b.c0 + b.c2) - a0b0 - a2b2
      c2 = t2 + a1b1

      Uses 6 base_mul, 1 mul_by_nr (applied twice), several add/sub.
      Temps: t0..t5 (6 base-sized allocations). *)
  Definition CE_mul : string * Syntax.func :=
    (mul (F := CE),
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := BaseField)) as a0b0;
      stackalloc (felem_size_in_bytes (F := BaseField)) as a1b1;
      stackalloc (felem_size_in_bytes (F := BaseField)) as a2b2;
      stackalloc (felem_size_in_bytes (F := BaseField)) as t0;
      stackalloc (felem_size_in_bytes (F := BaseField)) as t1;
      stackalloc (felem_size_in_bytes (F := BaseField)) as t2;
      (* a0b0 = a.c0 * b.c0 *)
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "a0b0"; ce_expr_c0 (expr.var "inx"); ce_expr_c0 (expr.var "iny")]);
      (* a1b1 = a.c1 * b.c1 *)
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "a1b1"; ce_expr_c1 (expr.var "inx"); ce_expr_c1 (expr.var "iny")]);
      (* a2b2 = a.c2 * b.c2 *)
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "a2b2"; ce_expr_c2 (expr.var "inx"); ce_expr_c2 (expr.var "iny")]);

      (* --- c0 = a0b0 + nr((a1+a2)(b1+b2) - a1b1 - a2b2) --- *)
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "t0"; ce_expr_c1 (expr.var "inx"); ce_expr_c2 (expr.var "inx")]);
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "t1"; ce_expr_c1 (expr.var "iny"); ce_expr_c2 (expr.var "iny")]);
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "t1"]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "a1b1"]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "a2b2"]);
      coq:(cmd.call [] mul_by_nr_name [expr.var "t0"; expr.var "t0"]);
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c0 (expr.var "out"); expr.var "a0b0"; expr.var "t0"]);

      (* --- c1 = (a0+a1)(b0+b1) - a0b0 - a1b1 + nr(a2b2) --- *)
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "t0"; ce_expr_c0 (expr.var "inx"); ce_expr_c1 (expr.var "inx")]);
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "t1"; ce_expr_c0 (expr.var "iny"); ce_expr_c1 (expr.var "iny")]);
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "t1"]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "a0b0"]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "a1b1"]);
      coq:(cmd.call [] mul_by_nr_name [expr.var "t1"; expr.var "a2b2"]);
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c1 (expr.var "out"); expr.var "t0"; expr.var "t1"]);

      (* --- c2 = (a0+a2)(b0+b2) - a0b0 - a2b2 + a1b1 --- *)
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "t0"; ce_expr_c0 (expr.var "inx"); ce_expr_c2 (expr.var "inx")]);
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "t1"; ce_expr_c0 (expr.var "iny"); ce_expr_c2 (expr.var "iny")]);
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "t1"]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "a0b0"]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "a2b2"]);
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c2 (expr.var "out"); expr.var "t0"; expr.var "a1b1"])
    ))).

  (** Squaring: Chung-Hasan SQR3.
      s0 = a0², s1 = 2·a0·a1, s2 = (a0-a1+a2)²,
      s3 = 2·a1·a2, s4 = a2²
      c0 = s0 + nr·s3, c1 = s1 + nr·s4,
      c2 = s1 + s2 + s3 - s0 - s4

      Uses 4 base_sqr/mul, 2 mul_by_nr, several add/sub.
      Temps: 5 base-sized allocations. *)
  Definition CE_square : string * Syntax.func :=
    (square (F := CE),
     (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := BaseField)) as s0;
      stackalloc (felem_size_in_bytes (F := BaseField)) as s1;
      stackalloc (felem_size_in_bytes (F := BaseField)) as s2;
      stackalloc (felem_size_in_bytes (F := BaseField)) as s3;
      stackalloc (felem_size_in_bytes (F := BaseField)) as s4;
      (* s0 = a0² *)
      coq:(cmd.call [] (square (F := BaseField)) [expr.var "s0"; ce_expr_c0 (expr.var "x")]);
      (* ab = a0 * a1 ; s1 = 2 * ab *)
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "s1"; ce_expr_c0 (expr.var "x"); ce_expr_c1 (expr.var "x")]);
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "s1"; expr.var "s1"; expr.var "s1"]);
      (* s2 = (a0 - a1 + a2)² *)
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "s2"; ce_expr_c0 (expr.var "x"); ce_expr_c1 (expr.var "x")]);
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "s2"; expr.var "s2"; ce_expr_c2 (expr.var "x")]);
      coq:(cmd.call [] (square (F := BaseField)) [expr.var "s2"; expr.var "s2"]);
      (* bc = a1 * a2 ; s3 = 2 * bc *)
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "s3"; ce_expr_c1 (expr.var "x"); ce_expr_c2 (expr.var "x")]);
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "s3"; expr.var "s3"; expr.var "s3"]);
      (* s4 = a2² *)
      coq:(cmd.call [] (square (F := BaseField)) [expr.var "s4"; ce_expr_c2 (expr.var "x")]);

      (* out.c0 = s0 + nr·s3 *)
      coq:(cmd.call [] mul_by_nr_name [ce_expr_c0 (expr.var "out"); expr.var "s3"]);
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c0 (expr.var "out"); expr.var "s0"; ce_expr_c0 (expr.var "out")]);
      (* out.c1 = s1 + nr·s4 *)
      coq:(cmd.call [] mul_by_nr_name [ce_expr_c1 (expr.var "out"); expr.var "s4"]);
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c1 (expr.var "out"); expr.var "s1"; ce_expr_c1 (expr.var "out")]);
      (* out.c2 = s1 + s2 + s3 - s0 - s4 *)
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c2 (expr.var "out"); expr.var "s1"; expr.var "s2"]);
      coq:(cmd.call [] (add (F := BaseField)) [ce_expr_c2 (expr.var "out"); ce_expr_c2 (expr.var "out"); expr.var "s3"]);
      coq:(cmd.call [] (sub (F := BaseField)) [ce_expr_c2 (expr.var "out"); ce_expr_c2 (expr.var "out"); expr.var "s0"]);
      coq:(cmd.call [] (sub (F := BaseField)) [ce_expr_c2 (expr.var "out"); ce_expr_c2 (expr.var "out"); expr.var "s4"])
    ))).

  (** Inverse: cubic extension formula.
      A = a0² - nr·(a1·a2)
      B = nr·(a2²) - a0·a1
      C = a1² - a0·a2
      FF = a0·A + nr·(a2·B + a1·C)
      result = (A·FF⁻¹, B·FF⁻¹, C·FF⁻¹)

      Uses ~12 base_mul, 3 mul_by_nr, 1 base_inv, several add/sub.
      Temps: 6 base-sized allocations + 1 for FF_inv. *)
  Definition CE_inv : string * Syntax.func :=
    (inv (F := CE),
     (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := BaseField)) as vA;
      stackalloc (felem_size_in_bytes (F := BaseField)) as vB;
      stackalloc (felem_size_in_bytes (F := BaseField)) as vC;
      stackalloc (felem_size_in_bytes (F := BaseField)) as t0;
      stackalloc (felem_size_in_bytes (F := BaseField)) as t1;
      stackalloc (felem_size_in_bytes (F := BaseField)) as vFF;
      stackalloc (felem_size_in_bytes (F := BaseField)) as vFFi;

      (* A = a0² - nr·(a1·a2) *)
      coq:(cmd.call [] (square (F := BaseField)) [expr.var "t0"; ce_expr_c0 (expr.var "x")]);
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "t1"; ce_expr_c1 (expr.var "x"); ce_expr_c2 (expr.var "x")]);
      coq:(cmd.call [] mul_by_nr_name [expr.var "t1"; expr.var "t1"]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "vA"; expr.var "t0"; expr.var "t1"]);

      (* B = nr·(a2²) - a0·a1 *)
      coq:(cmd.call [] (square (F := BaseField)) [expr.var "t0"; ce_expr_c2 (expr.var "x")]);
      coq:(cmd.call [] mul_by_nr_name [expr.var "t0"; expr.var "t0"]);
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "t1"; ce_expr_c0 (expr.var "x"); ce_expr_c1 (expr.var "x")]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "vB"; expr.var "t0"; expr.var "t1"]);

      (* C = a1² - a0·a2 *)
      coq:(cmd.call [] (square (F := BaseField)) [expr.var "t0"; ce_expr_c1 (expr.var "x")]);
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "t1"; ce_expr_c0 (expr.var "x"); ce_expr_c2 (expr.var "x")]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "vC"; expr.var "t0"; expr.var "t1"]);

      (* FF = a0·A + nr·(a2·B + a1·C) *)
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "vFF"; ce_expr_c0 (expr.var "x"); expr.var "vA"]);
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "t0"; ce_expr_c2 (expr.var "x"); expr.var "vB"]);
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "t1"; ce_expr_c1 (expr.var "x"); expr.var "vC"]);
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "t0"; expr.var "t0"; expr.var "t1"]);
      coq:(cmd.call [] mul_by_nr_name [expr.var "t0"; expr.var "t0"]);
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "vFF"; expr.var "vFF"; expr.var "t0"]);

      (* FF_inv = inv(FF) *)
      coq:(cmd.call [] (inv (F := BaseField)) [expr.var "vFFi"; expr.var "vFF"]);

      (* out = (A·FF⁻¹, B·FF⁻¹, C·FF⁻¹) *)
      coq:(cmd.call [] (mul (F := BaseField)) [ce_expr_c0 (expr.var "out"); expr.var "vA"; expr.var "vFFi"]);
      coq:(cmd.call [] (mul (F := BaseField)) [ce_expr_c1 (expr.var "out"); expr.var "vB"; expr.var "vFFi"]);
      coq:(cmd.call [] (mul (F := BaseField)) [ce_expr_c2 (expr.var "out"); expr.var "vC"; expr.var "vFFi"])
    ))).

  (* ================================================================ *)
  (* Spec instance declarations                                        *)
  (* ================================================================ *)

  Instance spec_of_CE_copy : spec_of (felem_copy (F := CE)) :=
    spec_of_felem_copy (F := CE).
  Instance spec_of_CE_add : spec_of (add (F := CE)) :=
    binop_spec bin_add (F := CE).
  Instance spec_of_CE_sub : spec_of (sub (F := CE)) :=
    binop_spec bin_sub (F := CE).
  Instance spec_of_CE_mul : spec_of (mul (F := CE)) :=
    binop_spec bin_mul (F := CE).
  Instance spec_of_CE_opp : spec_of (opp (F := CE)) :=
    unop_spec un_opp (F := CE).
  Instance spec_of_CE_square : spec_of (square (F := CE)) :=
    unop_spec un_square (F := CE).
  Instance spec_of_CE_inv : spec_of (inv (F := CE)) :=
    unop_spec un_inv (F := CE).
  Instance spec_of_CE_zero : spec_of (zero (F := CE)) :=
    nullop_spec null_zero (F := CE).
  Instance spec_of_CE_one : spec_of (one (F := CE)) :=
    nullop_spec null_one (F := CE).

  (** All extension functions, suitable for registration. *)
  Definition CE_funcs : list (string * Syntax.func) :=
    [ Mul_by_nr_func;
      CE_felem_copy; CE_zero_func; CE_one_func;
      CE_opp; CE_add; CE_sub; CE_mul; CE_square; CE_inv ].

End GenericCubicExt.
