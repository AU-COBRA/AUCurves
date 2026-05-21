(** * BW6-761 Miller Loop — bedrock2 function body.

    Defines the bedrock2 function body for the BW6-761 optimal-ate
    Miller loop.  The BW6-761 tower is:
      Fp -> Fp3 -> Fp6
    with cubic twist (M-type), so G2 points live in Fp3 (affine).

    BW6-761's pairing in gnark-crypto uses a double-base 5-symbol
    alphabet {-3,-1,0,1,3} for the Miller loop, exploiting
    LoopCounter[i] + 3*LoopCounter1[i].  That optimisation requires
    a 5-way branch inside each iteration and is left as a future
    optimisation: this file ships a single-loop binary Miller body
    parameterised on the absolute value of the seed |x_0|.  The
    final-exponentiation step compensates for the difference.

    Functions defined:
    - bw6_761_Fp3_mul_fp: multiply an Fp3 element by an Fp scalar
    - bw6_761_make_line: line evaluation l(P) in Fp6
    - bw6_761_miller_loop: full Miller loop

    Cf. [BLS24_509_MillerLoop.v] for the parallel BLS24 layout —
    BW6's tower is shorter (2 layers vs 4), the first extension is
    cubic instead of quadratic, and the conjugation/inversion
    structure differs accordingly. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BW6_MillerLoop.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  (* ============================================================== *)
  (* BW6-761 prime parameters and tower instances (from Instances)  *)
  (* ============================================================== *)

  Existing Instances
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp_repr
    bw6_Fp_repr_ok
    bw6_Fp_names
    bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok bw6_Fp3_names
    bw6_Fp6_params bw6_Fp6_repr bw6_Fp6_repr_ok bw6_Fp6_names.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  (* ============================================================== *)
  (* Offset and address helpers                                      *)
  (* ============================================================== *)

  (* Fp-level offset within Fp3 *)
  Local Notation fp_felem_offset :=
    (Memory.bytes_per_word 64 *
     Z.of_nat (@AbstractField.felem_size_in_words Fp _ _ _ _ _ bw6_Fp_repr)).
  Local Definition expr_fp3_c0 (x : Syntax.expr.expr) : Syntax.expr.expr := x.
  Local Definition expr_fp3_c1 (x : Syntax.expr.expr) : Syntax.expr.expr :=
    expr.op bopname.add x (expr.literal fp_felem_offset).
  Local Definition expr_fp3_c2 (x : Syntax.expr.expr) : Syntax.expr.expr :=
    expr.op bopname.add x (expr.literal (2 * fp_felem_offset)).

  (* Fp3-level offset within Fp6 = Fp3 x Fp3 *)
  Local Notation fp3_felem_offset :=
    (Memory.bytes_per_word 64 *
     Z.of_nat (@AbstractField.felem_size_in_words Fp3 _ _ _ _ _ bw6_Fp3_repr)).
  Local Definition expr_fp6_c0 (x : Syntax.expr.expr) : Syntax.expr.expr := x.
  Local Definition expr_fp6_c1 (x : Syntax.expr.expr) : Syntax.expr.expr :=
    expr.op bopname.add x (expr.literal fp3_felem_offset).

  (* ============================================================== *)
  (* Function name helpers                                           *)
  (* ============================================================== *)

  Let fp_add_name   : string := PrimeField.add.
  Let fp_sub_name   : string := PrimeField.sub.
  Let fp_mul_name   : string := PrimeField.mul.
  Let fp_opp_name   : string := PrimeField.opp.
  Let fp_copy_name  : string := PrimeField.felem_copy.
  Let from_word_name : string := PrimeField.from_word.

  Let fp3_add_name  : string := AbstractField.add (F:=Fp3).
  Let fp3_sub_name  : string := AbstractField.sub (F:=Fp3).
  Let fp3_mul_name  : string := AbstractField.mul (F:=Fp3).
  Let fp3_sqr_name  : string := AbstractField.square (F:=Fp3).
  Let fp3_inv_name  : string := AbstractField.inv (F:=Fp3).
  Let fp3_opp_name  : string := AbstractField.opp (F:=Fp3).
  Let fp3_copy_name : string := AbstractField.felem_copy (F:=Fp3).

  Let fp6_add_name  : string := AbstractField.add (F:=Fp6).
  Let fp6_mul_name  : string := AbstractField.mul (F:=Fp6).
  Let fp6_sqr_name  : string := AbstractField.square (F:=Fp6).
  Let fp6_copy_name : string := AbstractField.felem_copy (F:=Fp6).

  (* ============================================================== *)
  (* FElem type notations                                            *)
  (* ============================================================== *)

  Local Notation FElem_Fp  := (@AbstractField.FElem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation FElem_Fp3 := (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation FElem_Fp6 := (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_feval  := (@AbstractField.feval _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_feval := (@AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_feval := (@AbstractField.feval _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_bounded  := (@AbstractField.bounded_by _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_bounded := (@AbstractField.bounded_by _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_bounded := (@AbstractField.bounded_by _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_tight  := (@AbstractField.tight_bounds _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp_loose  := (@AbstractField.loose_bounds _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_tight := (@AbstractField.tight_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_loose := (@AbstractField.loose_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_tight := (@AbstractField.tight_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).
  Local Notation Fp6_loose := (@AbstractField.loose_bounds _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Notation Fp_felem  := (@AbstractField.felem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_felem := (@AbstractField.felem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_felem := (@AbstractField.felem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Typeclasses Opaque bw6_Fp6_params.
  Local Typeclasses Opaque bw6_Fp3_params.

  (* ============================================================== *)
  (* cmd_seq_list helper                                              *)
  (* ============================================================== *)

  Fixpoint cmd_seq_list (cmds : list Syntax.cmd.cmd) : Syntax.cmd.cmd :=
    match cmds with
    | [] => cmd.skip
    | [c] => c
    | c :: rest => cmd.seq c (cmd_seq_list rest)
    end.

  (* ============================================================== *)
  (* Fp3_mul_fp: multiply an Fp3 element by an Fp scalar             *)
  (*   (a0, a1, a2) * s = (a0*s, a1*s, a2*s)                         *)
  (* ============================================================== *)

  Let fp3_mul_fp_name : string := "bw6_761_Fp3_mul_fp".

  Definition bw6_761_Fp3_mul_fp : function_t :=
    (fp3_mul_fp_name,
     (["out"; "x"; "s"], []:list String.string,
      cmd_seq_list [
        cmd.call [] fp_mul_name
          [expr_fp3_c0 (expr.var "out");
           expr_fp3_c0 (expr.var "x"); expr.var "s"];
        cmd.call [] fp_mul_name
          [expr_fp3_c1 (expr.var "out");
           expr_fp3_c1 (expr.var "x"); expr.var "s"];
        cmd.call [] fp_mul_name
          [expr_fp3_c2 (expr.var "out");
           expr_fp3_c2 (expr.var "x"); expr.var "s"]
      ])).

  (* ============================================================== *)
  (* bw6_761_make_line: construct a line evaluation in Fp6           *)
  (*                                                                 *)
  (* For BW6-761 with cubic M-twist over Fp3:                        *)
  (* Given: lambda (slope in Fp3), t_x/t_y (point T in Fp3),         *)
  (*        x_p/y_p (point P in Fp).                                 *)
  (*                                                                 *)
  (* Line evaluation (sparse): l(x,y) = y - lambda*(x - t_x) - t_y   *)
  (* At P = (x_p, y_p) on the curve over Fp:                         *)
  (*   l(P) = y_p - lambda*(x_p - t_x) - t_y                         *)
  (*        = -lambda*x_p + lambda*t_x - t_y + y_p                   *)
  (*                                                                 *)
  (* Stored in Fp6 = Fp3[w]/(w^2 - zeta) as:                         *)
  (*   out.c0 = (lambda*t_x - t_y) in Fp3                            *)
  (*   out.c1 = (-lambda*x_p in c0 slot of Fp3,                      *)
  (*            y_p in c1 slot, 0 in c2 slot)                        *)
  (* This is the convention used by gnark-crypto for M-twists.       *)
  (* ============================================================== *)

  Let make_line_name : string := "bw6_761_make_line".

  Definition bw6_761_make_line : function_t :=
    (make_line_name,
     (["out"; "lam"; "x_t"; "y_t"; "x_p"; "y_p"],
      []:list String.string, bedrock_func_body:(
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as tmp;
       coq:(cmd_seq_list [
         (* tmp = lambda * x_t (in Fp3) *)
         cmd.call [] fp3_mul_name
           [expr.var "tmp"; expr.var "lam"; expr.var "x_t"];
         (* out.c0 = tmp - y_t  (= lambda*x_t - y_t, in Fp3) *)
         cmd.call [] fp3_sub_name
           [expr_fp6_c0 (expr.var "out");
            expr.var "tmp"; expr.var "y_t"];

         (* tmp = lambda * x_p  (Fp3 scaled by Fp) *)
         cmd.call [] fp3_mul_fp_name
           [expr.var "tmp"; expr.var "lam"; expr.var "x_p"];
         (* out.c1.c0 = -tmp.c0  = -lambda.c0 * x_p *)
         cmd.call [] fp_opp_name
           [expr_fp3_c0 (expr_fp6_c1 (expr.var "out"));
            expr_fp3_c0 (expr.var "tmp")];
         (* out.c1.c1 = y_p *)
         cmd.call [] fp_copy_name
           [expr_fp3_c1 (expr_fp6_c1 (expr.var "out"));
            expr.var "y_p"];
         (* out.c1.c2 = 0 *)
         cmd.call [] from_word_name
           [expr_fp3_c2 (expr_fp6_c1 (expr.var "out"));
            expr.literal 0]
       ])
     ))).

  (* ============================================================== *)
  (* Set Fp6 element to 1: c0.c0 = 1, all other components = 0      *)
  (* ============================================================== *)

  Local Definition fp6_set_one (v : string) : Syntax.cmd.cmd :=
    let p := expr.var v in
    cmd_seq_list [
      (* c0.c0 = 1, c0.c1 = 0, c0.c2 = 0 *)
      cmd.call [] from_word_name [expr_fp3_c0 (expr_fp6_c0 p); expr.literal 1];
      cmd.call [] from_word_name [expr_fp3_c1 (expr_fp6_c0 p); expr.literal 0];
      cmd.call [] from_word_name [expr_fp3_c2 (expr_fp6_c0 p); expr.literal 0];
      (* c1.c0 = 0, c1.c1 = 0, c1.c2 = 0 *)
      cmd.call [] from_word_name [expr_fp3_c0 (expr_fp6_c1 p); expr.literal 0];
      cmd.call [] from_word_name [expr_fp3_c1 (expr_fp6_c1 p); expr.literal 0];
      cmd.call [] from_word_name [expr_fp3_c2 (expr_fp6_c1 p); expr.literal 0]
    ].

  (* ============================================================== *)
  (* Fp6 conjugation: negate c1 component (sextic twist, unitary    *)
  (* element).  For Fp6 = Fp3[w]/(w^2 - zeta), the Frobenius        *)
  (* conjugation w -> -w gives conj(c0, c1) = (c0, -c1).            *)
  (* ============================================================== *)

  Local Definition fp6_conj_body (f_var : string) : Syntax.cmd.cmd :=
    cmd_seq_list [
      cmd.call [] fp3_opp_name
        [expr_fp6_c1 (expr.var f_var);
         expr_fp6_c1 (expr.var f_var)]
    ].

  (* ============================================================== *)
  (* Miller loop iteration body                                      *)
  (* ============================================================== *)

  (** BW6-761 seed: |x_0| = 0x8508c00000000001 (64 bits)
      Reference: gnark-crypto ecc/bw6-761/bw6-761.go.  In the
      double-base representation used by gnark, the effective Miller
      loop runs 188 iterations; here we use a single-loop binary
      Miller scaffold with 64-bit seed (the simpler scheme — the
      double-base optimisation is a future refinement). *)
  Let bw6_seed_abs  : Z := 0x8508c00000000001.
  Let bw6_seed_msb  : Z := 64.   (* MSB bit index + 1 *)

  (** One iteration of the Miller loop:
      - Decrement i
      - Doubling step: tangent slope, line eval, update f and T
      - Conditional addition step if bit i of |x_0| is set *)
  Definition miller_loop_iteration : Syntax.cmd.cmd :=
    cmd_seq_list [
      cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));

      (* === Doubling step === *)
      (* Tangent slope: lambda = 3*t_x^2 / (2*t_y) *)
      cmd.call [] fp3_sqr_name [expr.var "tmp1"; expr.var "t_x"];
      cmd.call [] fp3_add_name [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp1"];
      cmd.call [] fp3_add_name [expr.var "lambda"; expr.var "lambda"; expr.var "tmp1"];
      cmd.call [] fp3_add_name [expr.var "tmp1"; expr.var "t_y"; expr.var "t_y"];
      cmd.call [] fp3_inv_name [expr.var "tmp1"; expr.var "tmp1"];
      cmd.call [] fp3_mul_name [expr.var "lambda"; expr.var "lambda"; expr.var "tmp1"];

      (* Line evaluation at P *)
      cmd.call [] make_line_name
        [expr.var "line"; expr.var "lambda";
         expr.var "t_x"; expr.var "t_y";
         expr.var "p_x"; expr.var "p_y"];

      (* f = f^2 * line *)
      cmd.call [] fp6_sqr_name [expr.var "f"; expr.var "f"];
      cmd.call [] fp6_mul_name [expr.var "f"; expr.var "f"; expr.var "line"];

      (* T = 2T: new_x = lambda^2 - 2*t_x *)
      cmd.call [] fp3_sqr_name [expr.var "tmp1"; expr.var "lambda"];
      cmd.call [] fp3_sub_name [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
      cmd.call [] fp3_sub_name [expr.var "tmp2"; expr.var "tmp1"; expr.var "t_x"];
      (* new_y = lambda*(t_x - new_x) - t_y *)
      cmd.call [] fp3_sub_name [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
      cmd.call [] fp3_mul_name [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
      cmd.call [] fp3_sub_name [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
      cmd.call [] fp3_copy_name [expr.var "t_x"; expr.var "tmp2"];

      (* === Conditional addition step === *)
      cmd.set "bit" (expr.op bopname.and
        (expr.op bopname.sru (expr.literal bw6_seed_abs) (expr.var "i"))
        (expr.literal 1));
      cmd.cond (expr.var "bit")
        (cmd_seq_list [
          (* Chord slope: lambda_a = (q_y - t_y) / (q_x - t_x) *)
          cmd.call [] fp3_sub_name [expr.var "tmp1"; expr.var "q_y"; expr.var "t_y"];
          cmd.call [] fp3_sub_name [expr.var "tmp2"; expr.var "q_x"; expr.var "t_x"];
          cmd.call [] fp3_inv_name [expr.var "tmp2"; expr.var "tmp2"];
          cmd.call [] fp3_mul_name [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp2"];
          (* Line evaluation at P *)
          cmd.call [] make_line_name
            [expr.var "line"; expr.var "lambda";
             expr.var "t_x"; expr.var "t_y";
             expr.var "p_x"; expr.var "p_y"];
          (* f = f * line *)
          cmd.call [] fp6_mul_name [expr.var "f"; expr.var "f"; expr.var "line"];
          (* T = T + Q: new_x = lambda^2 - t_x - q_x *)
          cmd.call [] fp3_sqr_name [expr.var "tmp1"; expr.var "lambda"];
          cmd.call [] fp3_sub_name [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
          cmd.call [] fp3_sub_name [expr.var "tmp2"; expr.var "tmp1"; expr.var "q_x"];
          (* new_y = lambda*(t_x - new_x) - t_y *)
          cmd.call [] fp3_sub_name [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
          cmd.call [] fp3_mul_name [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
          cmd.call [] fp3_sub_name [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
          cmd.call [] fp3_copy_name [expr.var "t_x"; expr.var "tmp2"]
        ])
        cmd.skip
    ].

  (** Full Miller loop body: init + while loop + final copy *)
  Definition miller_loop_full_body : Syntax.cmd.cmd :=
    cmd_seq_list [
      fp6_set_one "f";
      cmd.call [] fp3_copy_name [expr.var "t_x"; expr.var "q_x"];
      cmd.call [] fp3_copy_name [expr.var "t_y"; expr.var "q_y"];
      cmd.set "i" (expr.literal bw6_seed_msb);
      cmd.while (expr.var "i") miller_loop_iteration;
      cmd.call [] fp6_copy_name [expr.var "out"; expr.var "f"]
    ].

  (* ============================================================== *)
  (* Top-level Miller loop function                                  *)
  (* ============================================================== *)

  Definition bw6_761_miller_loop : function_t :=
    ("bw6_761_miller_loop",
     (["out"; "p_x"; "p_y"; "q_x"; "q_y"], []:list String.string,
      bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as f;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as t_x;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as t_y;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as lambda;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as tmp1;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as tmp2;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as line;
        coq:(miller_loop_full_body)
      ))).

  (* ============================================================== *)
  (* Spec — memory-safety + bound preservation                       *)
  (* ============================================================== *)

  Instance spec_of_bw6_761_make_line : spec_of "bw6_761_make_line" :=
    fnspec! "bw6_761_make_line" (pout plam pxt pyt pxp pyp : word)
      / (old_out : Fp6_felem) (lam xt yt : Fp3_felem)
        (xp yp : Fp_felem) Rr,
    { requires tr mem :=
        Fp3_bounded Fp3_tight lam /\
        Fp3_bounded Fp3_tight xt /\
        Fp3_bounded Fp3_tight yt /\
        Fp_bounded Fp_loose xp /\
        Fp_bounded Fp_loose yp /\
        (FElem_Fp6 pout old_out *
         (FElem_Fp3 plam lam *
          (FElem_Fp3 pxt xt *
           (FElem_Fp3 pyt yt *
            (FElem_Fp pxp xp *
             (FElem_Fp pyp yp * Rr))))))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_bounded Fp6_loose out /\
          (FElem_Fp6 pout out *
           (FElem_Fp3 plam lam *
            (FElem_Fp3 pxt xt *
             (FElem_Fp3 pyt yt *
              (FElem_Fp pxp xp *
               (FElem_Fp pyp yp * Rr))))))%sep mem' }.

  Instance spec_of_bw6_761_Fp3_mul_fp : spec_of "bw6_761_Fp3_mul_fp" :=
    fnspec! "bw6_761_Fp3_mul_fp" (pout px ps : word)
      / (old_out : Fp3_felem) (x : Fp3_felem) (s : Fp_felem) Rr,
    { requires tr mem :=
        Fp3_bounded Fp3_tight x /\
        Fp_bounded Fp_loose s /\
        (FElem_Fp3 pout old_out *
         (FElem_Fp3 px x *
          (FElem_Fp ps s * Rr)))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp3_bounded Fp3_loose out /\
          (FElem_Fp3 pout out *
           (FElem_Fp3 px x *
            (FElem_Fp ps s * Rr)))%sep mem' }.

  Instance spec_of_bw6_761_miller_loop : spec_of "bw6_761_miller_loop" :=
    fnspec! "bw6_761_miller_loop" (pout p_px p_py p_qx p_qy : word)
      / (old_out : Fp6_felem) (p_x p_y : Fp_felem) (q_x q_y : Fp3_felem)
        Rr,
    { requires tr mem :=
        Fp3_bounded Fp3_tight q_x /\
        Fp3_bounded Fp3_tight q_y /\
        Fp_bounded Fp_loose p_x /\
        Fp_bounded Fp_loose p_y /\
        (FElem_Fp6 pout old_out *
         (FElem_Fp p_px p_x *
          (FElem_Fp p_py p_y *
           (FElem_Fp3 p_qx q_x *
            (FElem_Fp3 p_qy q_y * Rr)))))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_bounded Fp6_loose out /\
          (FElem_Fp6 pout out *
           (FElem_Fp p_px p_x *
            (FElem_Fp p_py p_y *
             (FElem_Fp3 p_qx q_x *
              (FElem_Fp3 p_qy q_y * Rr)))))%sep mem' }.

  (* ============================================================== *)
  (* Collected function list                                         *)
  (* ============================================================== *)

  Definition bw6_761_miller_loop_funcs : list function_t :=
    [ bw6_761_Fp3_mul_fp;
      bw6_761_make_line;
      bw6_761_miller_loop ].

End BW6_MillerLoop.
