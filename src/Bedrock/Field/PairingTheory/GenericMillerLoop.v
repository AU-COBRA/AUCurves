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

    Note: the binary scaffold above does NOT cover BW6's 5-symbol
    {-3,-1,0,1,3} double-base alphabet; the
    [GenericMillerLoopMultibase] section below extends it to that
    case. *)

(** * GenericMillerLoopMultibase — N-symbol parametric Miller-loop scaffold.

    Extends [GenericMillerLoop] above with a non-binary step
    alphabet.  Motivating instance: BW6-761's optimised Miller
    loop, which evaluates the seed as a base-3 / signed-binary
    composite digit at each step (symbols [-3,-1,0,1,3]) rather
    than {0,1}.

    The dispatch shape: at each iteration index [i], the user
    supplies an [Syntax.expr] [decode_symbol i] that loads (e.g.)
    two precomputed bit-arrays [L1[i]] and [L0[i]] and returns a
    [Z] symbol matching one of the supported alphabet entries.
    The iteration then selects one of five sub-bodies via nested
    [cmd.cond] comparing the decoded value against literal
    constants in the order
        [0 -> -1 -> +1 -> -3 -> +3]
    (most-common-first cheap path; final else is unreachable but
    set to [cmd.skip]).

    This file declares only the dispatch skeleton — the per-symbol
    sub-bodies (the actual doubling and signed-multi-addition
    formulas) are passed as [Variable]s by the caller, just like
    the binary case parameterised on the field-op names.

    STATUS (this turn): scaffold only.  Correctness is left to
    each per-curve [*_MillerLoop_proof.v] (BW6-761 first), which
    will discharge the loop invariant against a 5-symbol Gallina
    model living in [PairingTheory/AffineMultibase.v]. *)

Section GenericMillerLoopMultibase.

  Existing Instances
    Bitwidth64.BW64.

  (** *** Twist field op names (same as binary scaffold). *)
  Variable twist_mul_name : string.
  Variable twist_sqr_name : string.
  Variable twist_add_name : string.
  Variable twist_sub_name : string.
  Variable twist_inv_name : string.
  Variable twist_copy_name : string.

  (** *** Top field op names (same as binary scaffold). *)
  Variable top_mul_name : string.
  Variable top_sqr_name : string.

  (** *** Curve-specific helper: [make_line]. *)
  Variable make_line_name : string.

  (** *** Per-iteration symbol decoder ***

      Given an expression denoting the current loop index [i],
      produces a bedrock2 expression whose evaluated value is the
      decoded symbol from the loop alphabet.  For BW6 with
      precomputed twin-bit arrays this is typically something like
      [L1[i] * 3 + L0[i] - bias].  The caller chooses the encoding;
      this scaffold is generic in it. *)
  Variable decode_symbol : Syntax.expr -> Syntax.expr.

  (** *** Per-symbol sub-bodies ***

      Sub-bodies are passed in as arbitrary [cmd.cmd]s so each
      curve can wire them to its own twist/top-field calls.  The
      typical content:

      - [body_zero]: doubling-only step (T := 2T; f := f^2 * l).
      - [body_pos1]: doubling + addition of Q with sign +1.
      - [body_neg1]: doubling + addition of (-Q).
      - [body_pos3]: doubling + addition of (3Q) with sign +1.
      - [body_neg3]: doubling + addition of (-3Q).

      For BW6 specifically, the precomputed [3*Q] point is stored
      alongside [Q] so the [+/-3] branches reuse the
      single-addition formula against [3*Q] rather than chaining
      three additions. *)
  Variable body_zero : Syntax.cmd.cmd.
  Variable body_pos1 : Syntax.cmd.cmd.
  Variable body_neg1 : Syntax.cmd.cmd.
  Variable body_pos3 : Syntax.cmd.cmd.
  Variable body_neg3 : Syntax.cmd.cmd.

  (** *** Loop length ***
      Number of iterations from MSB downward to bit 0 (inclusive
      of the MSB itself; the caller is responsible for the initial
      T := Q (or T := MSB-symbol-Q) seeding). *)
  Variable n_iters_msb : Z.

  (** *** 5-way dispatch ***
      Compares [decode_symbol (expr.var "i")] against each
      supported alphabet entry in turn; the matching sub-body
      runs.  Implemented as nested [cmd.cond] (Coq's bedrock2 has
      no [cmd.match]).  Order is most-common-first
      (0 dominates the BW6 NAF).

      The fall-through [else] branch is [cmd.skip], which is sound
      as long as [decode_symbol] really does take values in
      [{-3,-1,0,1,3}] — the per-curve correctness proof carries
      that as an invariant. *)
  Definition multibase_dispatch : Syntax.cmd.cmd :=
    cmd.seq
      (cmd.set "sym" (decode_symbol (expr.var "i")))
      (cmd.cond
         (expr.op bopname.eq (expr.var "sym") (expr.literal 0))
         body_zero
         (cmd.cond
            (expr.op bopname.eq (expr.var "sym") (expr.literal (-1)))
            body_neg1
            (cmd.cond
               (expr.op bopname.eq (expr.var "sym") (expr.literal 1))
               body_pos1
               (cmd.cond
                  (expr.op bopname.eq (expr.var "sym") (expr.literal (-3)))
                  body_neg3
                  (cmd.cond
                     (expr.op bopname.eq (expr.var "sym") (expr.literal 3))
                     body_pos3
                     cmd.skip))))).

  (** *** One multibase iteration ***
      Decrement [i] (so the loop runs from [n_iters_msb] down to
      [0] inclusive), then dispatch to the per-symbol sub-body. *)
  Definition multibase_miller_iteration : Syntax.cmd.cmd :=
    cmd_seq_list [
      cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1));
      multibase_dispatch
    ].

  (** *** Full multibase loop body. *)
  Definition multibase_miller_loop_body : Syntax.cmd.cmd :=
    cmd_seq_list [
      cmd.set "i" (expr.literal n_iters_msb);
      cmd.while (expr.var "i") multibase_miller_iteration
    ].

  (** *** Function record ***
      Same calling convention as the binary scaffold —
      [pout; p_px; p_py; p_qx; p_qy] in, no return.  The per-curve
      wrapper is responsible for stackallocating temporaries (incl.
      a [sym] slot) and for seeding [f := 1; T := Q] (or the
      multibase-aware MSB-symbol-Q initial value) before the loop. *)
  Definition multibase_miller_loop_func (name : string) : function_t :=
    (name,
     (["pout"; "p_px"; "p_py"; "p_qx"; "p_qy"],
      [] : list String.string,
      multibase_miller_loop_body)).

End GenericMillerLoopMultibase.

(** *** Multibase correctness theorem template ***

    The per-curve statement parallels the binary case:

      [Theorem bw6_761_miller_loop_ok :
        program_logic_goal_for_function!
          (multibase_miller_loop_func
             BW6.twist_mul_name ... BW6.make_line_name
             BW6.decode_symbol
             BW6.body_zero BW6.body_pos1 BW6.body_neg1
             BW6.body_pos3 BW6.body_neg3
             BW6.n_iters_msb
             "bw6_761_miller_loop").]

    The proof discharges the loop invariant against a 5-symbol
    Gallina model in [PairingTheory/AffineMultibase.v], adding one
    extra obligation per dispatch arm (5 vs the binary scaffold's
    2).  Each arm reduces to either the doubling-only lemma
    [doubling_step_correct] (symbol 0) or the addition lemma
    [addition_step_correct] (symbols +/-1, +/-3, using precomputed
    [Q] resp. [3Q]). *)
