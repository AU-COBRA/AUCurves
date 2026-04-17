(** * Generic quadratic extension bedrock2 function bodies.

    Defines bedrock2 functions for add, sub, mul, opp, copy, zero, one,
    square, select_znz on BaseField × BaseField, parameterized over:
      - Base field FieldParameters + FieldRepresentation
      - A [mul_by_nr] bedrock2 function (multiplication by nonresidue)

    Each function builds its body from calls to the base field operations
    (via AbstractField function names).

    WP proofs are deferred to separate files — this file only contains
    function definitions and spec instance declarations. *)

Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.

Local Open Scope Z_scope.

Section GenericQuadExt.

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

  Variable nonresidue : BaseField.
  Variable prefix : string.
  Hypothesis eq_dec_base : forall x y : BaseField, {x = y} + {x <> y}.

  Local Notation QE := (BaseField * BaseField)%type.

  (* Import generic specs *)
  Local Instance QE_fp : FieldParameters QE :=
    QE_field_parameters nonresidue prefix eq_dec_base.
  Local Instance QE_repr : @FieldRepresentation QE QE_fp width BW word mem :=
    QE_field_representation nonresidue prefix eq_dec_base.

  (* ================================================================ *)
  (* Field names                                                       *)
  (* ================================================================ *)

  Context {QE_names : FieldNames (F := QE)}.
  Context {base_names : FieldNames (F := BaseField)}.

  (* ================================================================ *)
  (* Memory layout                                                     *)
  (* ================================================================ *)

  (** Byte offset for the second base-field component. *)
  Local Notation base_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (@felem_size_in_words _ base_fp _ _ _ _ base_repr)).

  (** Expression for the second component of a QE pointer. *)
  Definition qe_expr_2nd (x : Syntax.expr) : Syntax.expr :=
    expr.op bopname.add x (expr.literal base_felem_offset).

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

  (** Copy: copy both components. *)
  Definition QE_felem_copy : string * Syntax.func :=
    (felem_copy (F := QE),
     (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (felem_copy (F := BaseField)) [expr.var "out"; expr.var "x"]);
      coq:(cmd.call [] (felem_copy (F := BaseField)) [qe_expr_2nd (expr.var "out"); qe_expr_2nd (expr.var "x")])
    ))).

  (** Zero: set both components to zero. *)
  Definition QE_zero_func : string * Syntax.func :=
    (zero (F := QE),
     (["out"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (zero (F := BaseField)) [expr.var "out"]);
      coq:(cmd.call [] (zero (F := BaseField)) [qe_expr_2nd (expr.var "out")])
    ))).

  (** One: set first component to one, second to zero. *)
  Definition QE_one_func : string * Syntax.func :=
    (one (F := QE),
     (["out"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (one (F := BaseField)) [expr.var "out"]);
      coq:(cmd.call [] (zero (F := BaseField)) [qe_expr_2nd (expr.var "out")])
    ))).

  (** Opp: negate both components. *)
  Definition QE_opp : string * Syntax.func :=
    (opp (F := QE),
     (["out"; "x"], []:list String.string, bedrock_func_body:(
      coq:(cmd.call [] (opp (F := BaseField)) [expr.var "out"; expr.var "x"]);
      coq:(cmd.call [] (opp (F := BaseField)) [qe_expr_2nd (expr.var "out"); qe_expr_2nd (expr.var "x")])
    ))).

  (** Add: copy inputs (alias safety), then add components. *)
  Definition QE_add : string * Syntax.func :=
    (add (F := QE),
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := QE)) as allocx;
      stackalloc (felem_size_in_bytes (F := QE)) as allocy;
      coq:(cmd.call [] (felem_copy (F := QE)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (felem_copy (F := QE)) [expr.var "allocy"; expr.var "iny"]);
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "out"; expr.var "allocx"; expr.var "allocy"]);
      coq:(cmd.call [] (add (F := BaseField)) [qe_expr_2nd (expr.var "out"); qe_expr_2nd (expr.var "allocx"); qe_expr_2nd (expr.var "allocy")])
    ))).

  (** Sub: copy inputs, then subtract components. *)
  Definition QE_sub : string * Syntax.func :=
    (sub (F := QE),
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := QE)) as allocx;
      stackalloc (felem_size_in_bytes (F := QE)) as allocy;
      coq:(cmd.call [] (felem_copy (F := QE)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (felem_copy (F := QE)) [expr.var "allocy"; expr.var "iny"]);
      coq:(cmd.call [] (sub (F := BaseField)) [expr.var "out"; expr.var "allocx"; expr.var "allocy"]);
      coq:(cmd.call [] (sub (F := BaseField)) [qe_expr_2nd (expr.var "out"); qe_expr_2nd (expr.var "allocx"); qe_expr_2nd (expr.var "allocy")])
    ))).

  (** Select_znz: conditional select on both components. *)
  Definition QE_select_znz : string * Syntax.func :=
    (select_znz (F := QE),
     (["out"; "c"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := QE)) as allocx;
      stackalloc (felem_size_in_bytes (F := QE)) as allocy;
      coq:(cmd.call [] (felem_copy (F := QE)) [expr.var "allocx"; expr.var "inx"]);
      coq:(cmd.call [] (felem_copy (F := QE)) [expr.var "allocy"; expr.var "iny"]);
      coq:(cmd.call [] (select_znz (F := BaseField)) [expr.var "out"; expr.var "c"; expr.var "allocx"; expr.var "allocy"]);
      coq:(cmd.call [] (select_znz (F := BaseField)) [qe_expr_2nd (expr.var "out"); expr.var "c"; qe_expr_2nd (expr.var "allocx"); qe_expr_2nd (expr.var "allocy")])
    ))).

  (** Multiplication: Karatsuba with mul_by_nonresidue.
      (a + bu)(c + du) = (ac + nr·bd) + ((a+b)(c+d) - ac - bd)u

      Temps: v0 (ac), v1 (bd), v2 (a+b / nr·bd)
      v0 = base_mul(a, c)
      v1 = base_mul(b, d)
      v2 = base_add(a, b)
      out.im = base_add(c, d)
      out.im = base_mul(out.im, v2)       -- (a+b)(c+d)
      out.im = base_sub(out.im, v0)       -- ... - ac
      out.im = base_sub(out.im, v1)       -- ad + bc ✓
      v2     = mul_by_nr(v1)              -- nr·bd
      out.re = base_add(v0, v2)           -- ac + nr·bd ✓ *)
  Definition QE_mul : string * Syntax.func :=
    (mul (F := QE),
     (["out"; "inx"; "iny"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := BaseField)) as v0;
      stackalloc (felem_size_in_bytes (F := BaseField)) as v1;
      stackalloc (felem_size_in_bytes (F := BaseField)) as v2;
      (* v0 = a * c *)
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "v0"; expr.var "inx"; expr.var "iny"]);
      (* v1 = b * d *)
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "v1"; qe_expr_2nd (expr.var "inx"); qe_expr_2nd (expr.var "iny")]);
      (* v2 = a + b *)
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "v2"; expr.var "inx"; qe_expr_2nd (expr.var "inx")]);
      (* out.im = c + d *)
      coq:(cmd.call [] (add (F := BaseField)) [qe_expr_2nd (expr.var "out"); expr.var "iny"; qe_expr_2nd (expr.var "iny")]);
      (* out.im = (a+b)(c+d) *)
      coq:(cmd.call [] (mul (F := BaseField)) [qe_expr_2nd (expr.var "out"); qe_expr_2nd (expr.var "out"); expr.var "v2"]);
      (* out.im -= v0 *)
      coq:(cmd.call [] (sub (F := BaseField)) [qe_expr_2nd (expr.var "out"); qe_expr_2nd (expr.var "out"); expr.var "v0"]);
      (* out.im -= v1 *)
      coq:(cmd.call [] (sub (F := BaseField)) [qe_expr_2nd (expr.var "out"); qe_expr_2nd (expr.var "out"); expr.var "v1"]);
      (* v2 = nr * v1 *)
      coq:(cmd.call [] mul_by_nr_name [expr.var "v2"; expr.var "v1"]);
      (* out.re = v0 + nr*v1 *)
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "out"; expr.var "v0"; expr.var "v2"])
    ))).

  (** Squaring: schoolbook (a + bu)² = (a² + nr·b²) + 2ab·u.
      v0 = base_sqr(a)               -- a²
      v1 = base_sqr(b)               -- b²
      v2 = base_mul(a, b)            -- ab
      out.im = base_add(v2, v2)      -- 2ab ✓
      v1 = mul_by_nr(v1)             -- nr·b²
      out.re = base_add(v0, v1)      -- a² + nr·b² ✓ *)
  Definition QE_square : string * Syntax.func :=
    (square (F := QE),
     (["out"; "x"], []:list String.string, bedrock_func_body:(
      stackalloc (felem_size_in_bytes (F := BaseField)) as v0;
      stackalloc (felem_size_in_bytes (F := BaseField)) as v1;
      stackalloc (felem_size_in_bytes (F := BaseField)) as v2;
      (* v0 = a² *)
      coq:(cmd.call [] (square (F := BaseField)) [expr.var "v0"; expr.var "x"]);
      (* v1 = b² *)
      coq:(cmd.call [] (square (F := BaseField)) [expr.var "v1"; qe_expr_2nd (expr.var "x")]);
      (* v2 = a * b *)
      coq:(cmd.call [] (mul (F := BaseField)) [expr.var "v2"; expr.var "x"; qe_expr_2nd (expr.var "x")]);
      (* out.im = 2ab *)
      coq:(cmd.call [] (add (F := BaseField)) [qe_expr_2nd (expr.var "out"); expr.var "v2"; expr.var "v2"]);
      (* v1 = nr * b² *)
      coq:(cmd.call [] mul_by_nr_name [expr.var "v1"; expr.var "v1"]);
      (* out.re = a² + nr*b² *)
      coq:(cmd.call [] (add (F := BaseField)) [expr.var "out"; expr.var "v0"; expr.var "v1"])
    ))).

  (* ================================================================ *)
  (* Spec instance declarations (no proofs — stubs for downstream)     *)
  (* ================================================================ *)

  Instance spec_of_QE_copy : spec_of (felem_copy (F := QE)) :=
    spec_of_felem_copy (F := QE).
  Instance spec_of_QE_add : spec_of (add (F := QE)) :=
    binop_spec bin_add (F := QE).
  Instance spec_of_QE_sub : spec_of (sub (F := QE)) :=
    binop_spec bin_sub (F := QE).
  Instance spec_of_QE_mul : spec_of (mul (F := QE)) :=
    binop_spec bin_mul (F := QE).
  Instance spec_of_QE_opp : spec_of (opp (F := QE)) :=
    unop_spec un_opp (F := QE).
  Instance spec_of_QE_square : spec_of (square (F := QE)) :=
    unop_spec un_square (F := QE).
  Instance spec_of_QE_zero : spec_of (zero (F := QE)) :=
    nullop_spec null_zero (F := QE).
  Instance spec_of_QE_one : spec_of (one (F := QE)) :=
    nullop_spec null_one (F := QE).

  (** All extension functions, suitable for registration. *)
  Definition QE_funcs : list (string * Syntax.func) :=
    [ QE_felem_copy; QE_zero_func; QE_one_func;
      QE_opp; QE_add; QE_sub; QE_mul; QE_square;
      QE_select_znz ].

End GenericQuadExt.
