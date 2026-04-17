(** * Generic BN final exponentiation hard part (Fuentes-Castañeda).

    Parameterized by function name strings. All 3 BN curves share this
    exact algorithm — only the names differ. Reduces ~90 lines of
    duplication per curve (~270 lines total). *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import bedrock2.Syntax.

Local Open Scope string_scope.

Section BN_FinalExpHardDSD_Generic.

  (* Function name parameters *)
  Variable fp12_mul_name : string.
  Variable fp12_sqr_name : string.
  Variable fp12_conjugate_name : string.
  Variable fp12_frobenius_name : string.
  Variable fp12_copy_name : string.
  Variable pow_u_name : string.
  Variable load_gamma1_name : string.
  Variable load_gamma2_name : string.
  Variable load_w_frob_c1_name : string.

  Local Fixpoint cmd_seq_list (cmds : list cmd.cmd) : cmd.cmd :=
    match cmds with
    | nil => cmd.skip
    | c :: nil => c
    | c :: rest => cmd.seq c (cmd_seq_list rest)
    end.

  (** The Fuentes-Castañeda Algorithm 1 for BN curves.
      Computes f^((p^4-p^2+1)/r) using the decomposition:
        lambda_3*p^3 + lambda_2*p^2 + lambda_1*p + lambda_0
      where lambda_3=1, lambda_2=6u^2+1, lambda_1=1-12u-18u^2-36u^3,
      lambda_0=-2-18u-30u^2-36u^3.

      Operations: 3 pow_u + 4 sqr + 10 mul + 7 frobenius + 4 conjugate.
      Registers: f (input), out, t0, t1, t2, t3 (temporaries),
                 gamma1, gamma2, w_frob_c1 (Frobenius constants). *)

  Definition bn_final_exp_hard_dsd_body : cmd.cmd :=
    cmd_seq_list [
      (* Load Frobenius constants *)
      cmd.call nil load_gamma1_name [expr.var "gamma1"];
      cmd.call nil load_gamma2_name [expr.var "gamma2"];
      cmd.call nil load_w_frob_c1_name [expr.var "w_frob_c1"];

      (* === Phase 1: Powers of u === *)
      cmd.call nil pow_u_name [expr.var "t0"; expr.var "f"];
      cmd.call nil pow_u_name [expr.var "t1"; expr.var "t0"];
      cmd.call nil pow_u_name [expr.var "t2"; expr.var "t1"];

      (* === Phase 2: y6 = conj(f^(u^3) * f^(u^3*p)) === *)
      cmd.call nil fp12_frobenius_name
        [expr.var "t3"; expr.var "t2";
         expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
      cmd.call nil fp12_mul_name
        [expr.var "t2"; expr.var "t2"; expr.var "t3"];
      cmd.call nil fp12_conjugate_name
        [expr.var "t2"; expr.var "t2"];

      (* === Phase 3: T01 = y6^2 * y4 * y5 === *)
      cmd.call nil fp12_sqr_name
        [expr.var "out"; expr.var "t2"];
      cmd.call nil fp12_frobenius_name
        [expr.var "t3"; expr.var "t1";
         expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
      cmd.call nil fp12_mul_name
        [expr.var "t1"; expr.var "t0"; expr.var "t3"];
      cmd.call nil fp12_conjugate_name
        [expr.var "t1"; expr.var "t1"];
      cmd.call nil fp12_mul_name
        [expr.var "out"; expr.var "out"; expr.var "t1"];
      cmd.call nil fp12_conjugate_name
        [expr.var "t1"; expr.var "t3"];
      cmd.call nil fp12_mul_name
        [expr.var "out"; expr.var "out"; expr.var "t1"];

      (* === Phase 4: T11 = T01 * y3 * y5 === *)
      cmd.call nil fp12_frobenius_name
        [expr.var "t2"; expr.var "t0";
         expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
      cmd.call nil fp12_conjugate_name
        [expr.var "t2"; expr.var "t2"];
      cmd.call nil fp12_mul_name
        [expr.var "t0"; expr.var "out"; expr.var "t2"];
      cmd.call nil fp12_mul_name
        [expr.var "t0"; expr.var "t0"; expr.var "t1"];

      (* === Phase 5: T02 = T01 * y2 === *)
      cmd.call nil fp12_frobenius_name
        [expr.var "t1"; expr.var "t3";
         expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
      cmd.call nil fp12_mul_name
        [expr.var "out"; expr.var "out"; expr.var "t1"];

      (* === Phase 6: T13 = (T11^2 * T02)^2 === *)
      cmd.call nil fp12_sqr_name
        [expr.var "t1"; expr.var "t0"];
      cmd.call nil fp12_mul_name
        [expr.var "t1"; expr.var "t1"; expr.var "out"];
      cmd.call nil fp12_sqr_name
        [expr.var "t1"; expr.var "t1"];

      (* === Phase 7: y0 = f^p * f^(p^2) * f^(p^3) === *)
      cmd.call nil fp12_frobenius_name
        [expr.var "t0"; expr.var "f";
         expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
      cmd.call nil fp12_frobenius_name
        [expr.var "t2"; expr.var "t0";
         expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
      cmd.call nil fp12_frobenius_name
        [expr.var "t3"; expr.var "t2";
         expr.var "gamma1"; expr.var "gamma2"; expr.var "w_frob_c1"];
      cmd.call nil fp12_mul_name
        [expr.var "t0"; expr.var "t0"; expr.var "t2"];
      cmd.call nil fp12_mul_name
        [expr.var "t0"; expr.var "t0"; expr.var "t3"];

      (* === Phase 8: Final assembly === *)
      cmd.call nil fp12_mul_name
        [expr.var "t2"; expr.var "t1"; expr.var "t0"];
      cmd.call nil fp12_conjugate_name
        [expr.var "t0"; expr.var "f"];
      cmd.call nil fp12_mul_name
        [expr.var "t0"; expr.var "t1"; expr.var "t0"];
      cmd.call nil fp12_sqr_name
        [expr.var "t0"; expr.var "t0"];
      cmd.call nil fp12_mul_name
        [expr.var "out"; expr.var "t0"; expr.var "t2"]
    ].

End BN_FinalExpHardDSD_Generic.
