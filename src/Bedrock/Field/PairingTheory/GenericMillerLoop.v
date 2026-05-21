(** * GenericMillerLoop — parametric Miller-loop bedrock2 scaffold.

    Per path (C) of docs/bw6-761-pairing-plan.md.  Extracts the
    common skeleton of the per-curve Miller loops into a single
    parameterised body, so new curves (starting with BW6-761) and
    future-refactored existing curves (BLS12, BLS24, BN254/256/446)
    share one source.

    Shape commonality across the 7 existing per-curve files:
      - All loop bits-of-|seed|, MSB downward, decrementing i.
      - Each iteration: doubling step (T := 2T + line; f := f^2 * line)
        and a conditional addition step (if bit set: T := T + Q +
        line; f := f * line).
      - Doubling step shape: lambda = 3 * t_x^2 / (2 * t_y);
        new_x = lambda^2 - 2*t_x; new_y = lambda*(t_x - new_x) - t_y.
      - Addition step shape: lambda = (q_y - t_y) / (q_x - t_x);
        new_x = lambda^2 - t_x - q_x; new_y = lambda*(t_x-new_x) - t_y.
      - Both followed by [make_line] then a multiplication into f.

    Differences across curves (parameterised here):
      - Field-tower depth (BLS12 has Fp2 twist + Fp12 top; BLS24 has
        Fp4 twist + Fp24 top; BW6 has Fp3 twist + Fp6 top).
      - Seed value and bit count.
      - Sign of the seed (some curves need a final conjugation).
      - For BW6: 5-symbol {-3,-1,0,1,3} alphabet rather than binary
        — NOT covered by this generic; a separate
        [GenericMillerLoopMultibase] handles it.

    STATUS (this turn): scaffold only — defines the parametric
    iteration body + the full-loop wrapper + the function record.
    The correctness theorem is left to per-curve [*_MillerLoop_proof.v]
    files.  Real correctness proof is multi-day work; the scaffold
    gives BW6 + other curves an API to target. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Import BinInt String.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Helper: chain a list of commands via cmd.seq. *)
Fixpoint cmd_seq_list (cmds : list Syntax.cmd.cmd) : Syntax.cmd.cmd :=
  match cmds with
  | [] => cmd.skip
  | [c] => c
  | c :: rest => cmd.seq c (cmd_seq_list rest)
  end.

Section GenericMillerLoop.

  Existing Instances
    Bitwidth64.BW64.

  (** *** Twist field op names ***
      Names of bedrock2 functions for the field where G2 points live
      (Fp2 for BLS12/BN, Fp4 for BLS24, Fp3 for BW6). *)
  Variable twist_mul_name : string.
  Variable twist_sqr_name : string.
  Variable twist_add_name : string.
  Variable twist_sub_name : string.
  Variable twist_inv_name : string.
  Variable twist_copy_name : string.

  (** *** Top field op names ***
      Names of bedrock2 functions for the pairing target field
      (Fp12 for BLS12/BN, Fp24 for BLS24, Fp6 for BW6). *)
  Variable top_mul_name : string.
  Variable top_sqr_name : string.

  (** *** Curve-specific helper ***
      Name of the [make_line] function that computes the line
      evaluation l(P) from (lambda, t_x, t_y, p_x, p_y). *)
  Variable make_line_name : string.

  (** *** Seed (loop counter) ***
      |z| as a Z literal.  The loop iterates from bit [seed_msb]
      down to 0. *)
  Variable seed_abs : Z.
  Variable seed_msb : Z.

  (** *** Common bit-test command ***
      Sets variable [bit] to the i-th bit of [seed_abs]. *)
  Definition test_seed_bit : Syntax.cmd.cmd :=
    cmd.set "bit"
      (expr.op bopname.and
        (expr.op bopname.sru (expr.literal seed_abs) (expr.var "i"))
        (expr.literal 1)).

  (** *** Doubling step ***
      Computes the tangent slope, the line evaluation l(P), updates
      f := f^2 * l, and updates T := 2T. *)
  Definition doubling_step : Syntax.cmd.cmd :=
    cmd_seq_list [
      (* lambda = 3 * t_x^2 / (2 * t_y) *)
      cmd.call [] twist_sqr_name [expr.var "tmp1"; expr.var "t_x"];
      cmd.call [] twist_add_name [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp1"];
      cmd.call [] twist_add_name [expr.var "lambda"; expr.var "lambda"; expr.var "tmp1"];
      cmd.call [] twist_add_name [expr.var "tmp1"; expr.var "t_y"; expr.var "t_y"];
      cmd.call [] twist_inv_name [expr.var "tmp1"; expr.var "tmp1"];
      cmd.call [] twist_mul_name [expr.var "lambda"; expr.var "lambda"; expr.var "tmp1"];
      (* Line evaluation at P *)
      cmd.call [] make_line_name
        [expr.var "line"; expr.var "lambda";
         expr.var "t_x"; expr.var "t_y";
         expr.var "p_x"; expr.var "p_y"];
      (* f = f^2 * line *)
      cmd.call [] top_sqr_name [expr.var "f"; expr.var "f"];
      cmd.call [] top_mul_name [expr.var "f"; expr.var "f"; expr.var "line"];
      (* T = 2T: new_x = lambda^2 - 2*t_x *)
      cmd.call [] twist_sqr_name [expr.var "tmp1"; expr.var "lambda"];
      cmd.call [] twist_sub_name [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
      cmd.call [] twist_sub_name [expr.var "tmp2"; expr.var "tmp1"; expr.var "t_x"];
      (* new_y = lambda*(t_x - new_x) - t_y *)
      cmd.call [] twist_sub_name [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
      cmd.call [] twist_mul_name [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
      cmd.call [] twist_sub_name [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
      cmd.call [] twist_copy_name [expr.var "t_x"; expr.var "tmp2"]
    ].

  (** *** Addition step ***
      Adds Q to T (and multiplies f by the chord line). *)
  Definition addition_step : Syntax.cmd.cmd :=
    cmd_seq_list [
      (* lambda_a = (q_y - t_y) / (q_x - t_x) *)
      cmd.call [] twist_sub_name [expr.var "tmp1"; expr.var "q_y"; expr.var "t_y"];
      cmd.call [] twist_sub_name [expr.var "tmp2"; expr.var "q_x"; expr.var "t_x"];
      cmd.call [] twist_inv_name [expr.var "tmp2"; expr.var "tmp2"];
      cmd.call [] twist_mul_name [expr.var "lambda"; expr.var "tmp1"; expr.var "tmp2"];
      (* Line eval *)
      cmd.call [] make_line_name
        [expr.var "line"; expr.var "lambda";
         expr.var "t_x"; expr.var "t_y";
         expr.var "p_x"; expr.var "p_y"];
      (* f = f * line *)
      cmd.call [] top_mul_name [expr.var "f"; expr.var "f"; expr.var "line"];
      (* T = T + Q: new_x = lambda^2 - t_x - q_x *)
      cmd.call [] twist_sqr_name [expr.var "tmp1"; expr.var "lambda"];
      cmd.call [] twist_sub_name [expr.var "tmp1"; expr.var "tmp1"; expr.var "t_x"];
      cmd.call [] twist_sub_name [expr.var "tmp2"; expr.var "tmp1"; expr.var "q_x"];
      (* new_y = lambda*(t_x - new_x) - t_y *)
      cmd.call [] twist_sub_name [expr.var "tmp1"; expr.var "t_x"; expr.var "tmp2"];
      cmd.call [] twist_mul_name [expr.var "tmp1"; expr.var "lambda"; expr.var "tmp1"];
      cmd.call [] twist_sub_name [expr.var "t_y"; expr.var "tmp1"; expr.var "t_y"];
      cmd.call [] twist_copy_name [expr.var "t_x"; expr.var "tmp2"]
    ].

  (** *** One iteration ***
      Decrement i, doubling step, conditional addition. *)
  Definition generic_miller_iteration : Syntax.cmd.cmd :=
    cmd_seq_list [
      cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
      doubling_step;
      test_seed_bit;
      cmd.cond (expr.var "bit") addition_step cmd.skip
    ].

  (** *** Full loop body ***
      Initial: i := seed_msb.  Then while i > 0, iterate.
      The caller is responsible for initializing f := 1 and T := Q
      before calling — the loop wrapper here just handles the iter. *)
  Definition generic_miller_loop_body : Syntax.cmd.cmd :=
    cmd_seq_list [
      cmd.set "i" (expr.literal seed_msb);
      cmd.while (expr.var "i") generic_miller_iteration
    ].

  (** *** Function record ***
      Caller supplies a function name (e.g., "bw6_761_miller_loop").
      Arguments [pout; p_px; p_py; p_qx; p_qy] are pointers into
      memory.  The caller's wrapper is responsible for stackallocating
      [t_x; t_y; lambda; line; tmp1; tmp2] and initializing
      [f := 1; T := Q]. *)
  Definition generic_miller_loop_func (name : string) : function_t :=
    (name,
     (["pout"; "p_px"; "p_py"; "p_qx"; "p_qy"],
      [] : list String.string,
      generic_miller_loop_body)).

End GenericMillerLoop.

(** *** Correctness theorem template ***

    The correctness statement (per-curve) takes the form:

      [Theorem C_miller_loop_ok :
        program_logic_goal_for_function!
          (generic_miller_loop_func
             C.twist_mul_name C.twist_sqr_name ... C.seed_abs C.seed_msb
             "C_miller_loop").]

    Real proof: ~600-800 LoC walking the loop invariant via
    Loops.while_localsmap + per-call bridging lemmas (see
    BLS24_509_MillerLoop_proof.v and PairingTheory/MillerLoopWP.v
    for templates).  Each curve states + proves it in its own
    [*_MillerLoop_proof.v] file, parametric in the generic body
    defined here.

    Note: this scaffold does NOT cover BW6's 5-symbol
    {-3,-1,0,1,3} double-base alphabet; that requires a parallel
    [GenericMillerLoopMultibase] file with a richer iteration body. *)
