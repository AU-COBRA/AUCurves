(** * BW6-761 Optimal-Ate Miller Loop — bedrock2 function body.

    Canonical optimal-ate Miller loop matching gnark-crypto's
    reference algorithm (`ecc/bw6-761/pairing.go::MillerLoop`).

    Per gnark, the BW6-761 Miller exponent is:

      x₀ + 1 + λ·(x₀³ − x₀² − x₀)

    encoded via a 5-symbol alphabet {−3, −1, 0, 1, 3} obtained from
    two NAF-decomposed scalars:
      - LoopCounter  = NAF(x₀ + 1),                  189 bits (i = 0..188)
      - LoopCounter1 = NAF(x₀³ − x₀² − x₀),          189 bits

    At each iteration i ∈ {188, 187, ..., 0}:
      j := LoopCounter1[i]·3 + LoopCounter[i]   ∈ {−3, −1, 0, 1, 3}

    The Miller loop runs in projective coordinates over Fp3 (g2Proj
    = (x: Fp3, y: Fp3, z: Fp3)) starting from `q1` (an endomorphism
    image of the input Q), and adds q0/q0Neg/q1/q1Neg as j prescribes.

    For BW6-761 where G2 lives over Fp (gnark's storage), this file's
    callers (`bw6-761-safe-rust/src/kat.rs`) embed Fp coords in the c0
    slot of a degenerate Fp3 (c1 = c2 = 0).  The Fp3 arithmetic then
    collapses to pure Fp arithmetic on the c0 slot, matching gnark
    bit-for-bit on those test vectors.

    Line encoding (sparse Fp6 = (r0, r1, 0, 0, r4, 0) in basis
    {1, u, u², w, uw, u²w}):
        B0 = (r0,  r1·p.X,  0)         (Fp3)
        B1 = ( 0,  r2·p.Y,  0)         (Fp3)

    This file ships the BODY only.  Phase-2 correctness proof (against
    `affine_miller_optimal_ate` Gallina) is admitted; the bedrock2
    body must build and extract.

    Cf. [BW6_761_MillerLoop.v] for the prior simplified single-loop
    binary Miller body (now superseded for the gnark KAT path). *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
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
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_MillerLoop.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_ProjOps.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BW6_MillerLoopOptimal.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

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
  (* Offsets reused from BW6_761_MillerLoop                          *)
  (* ============================================================== *)

  Local Notation fp_felem_offset :=
    (Memory.bytes_per_word 64 *
     Z.of_nat (@AbstractField.felem_size_in_words Fp _ _ _ _ _ bw6_Fp_repr)).
  Local Definition expr_fp3_c0 (x : Syntax.expr.expr) : Syntax.expr.expr := x.
  Local Definition expr_fp3_c1 (x : Syntax.expr.expr) : Syntax.expr.expr :=
    Syntax.expr.op Syntax.bopname.add x (Syntax.expr.literal fp_felem_offset).
  Local Definition expr_fp3_c2 (x : Syntax.expr.expr) : Syntax.expr.expr :=
    Syntax.expr.op Syntax.bopname.add x (Syntax.expr.literal (2 * fp_felem_offset)).

  Local Notation fp3_felem_offset :=
    (Memory.bytes_per_word 64 *
     Z.of_nat (@AbstractField.felem_size_in_words Fp3 _ _ _ _ _ bw6_Fp3_repr)).
  Local Definition expr_fp6_c0 (x : Syntax.expr.expr) : Syntax.expr.expr := x.
  Local Definition expr_fp6_c1 (x : Syntax.expr.expr) : Syntax.expr.expr :=
    Syntax.expr.op Syntax.bopname.add x (Syntax.expr.literal fp3_felem_offset).

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
  Let fp3_opp_name  : string := AbstractField.opp (F:=Fp3).
  Let fp3_copy_name : string := AbstractField.felem_copy (F:=Fp3).

  Let fp6_mul_name  : string := AbstractField.mul (F:=Fp6).
  Let fp6_sqr_name  : string := AbstractField.square (F:=Fp6).
  Let fp6_copy_name : string := AbstractField.felem_copy (F:=Fp6).

  Local Notation FElem_Fp  := (@AbstractField.FElem _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation FElem_Fp3 := (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation FElem_Fp6 := (@AbstractField.FElem _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

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

  Local Notation Fp_feval  := (@AbstractField.feval _ _ _ _ _ _ bw6_Fp_repr).
  Local Notation Fp3_feval := (@AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp6_feval := (@AbstractField.feval _ bw6_Fp6_params _ _ _ _ bw6_Fp6_repr).

  Local Typeclasses Opaque bw6_Fp6_params.
  Local Typeclasses Opaque bw6_Fp3_params.

  (* Reuse from BW6_761_MillerLoop: *)
  Definition cmd_seq_list := BW6_761_MillerLoop.cmd_seq_list.

  Local Notation make_line_name := "bw6_761_make_line".
  Local Notation fp3_mul_fp_name := "bw6_761_Fp3_mul_fp".

  (* ============================================================== *)
  (* g2_double_step:                                                 *)
  (*   gnark's `(p *g2Proj) doubleStep(evaluations *lineEvaluation)` *)
  (*   eprint.iacr.org/2013/722.pdf §4.3                             *)
  (*                                                                 *)
  (* Inputs (mutable): x, y, z (Fp3 each, g2Proj coords)             *)
  (*                   r0, r1, r2 (Fp3 each, line evaluation)        *)
  (* Result: updates x, y, z = 2·(x,y,z) in proj coords;             *)
  (*         stores line coeffs r0, r1, r2.                           *)
  (*                                                                 *)
  (* Algorithm (let `half = 2^-1 mod p`; computed via add+inv):       *)
  (*   A = x*y;   A = halve(A)                                       *)
  (*   B = y²                                                         *)
  (*   C = z²                                                         *)
  (*   D = 3·C                                                        *)
  (*   E = 4·D = 12·C                                                 *)
  (*   F = 3·E = 36·C                                                 *)
  (*   G = (B + F) ; G = halve(G)                                     *)
  (*   H = (y+z)² − B − C                                             *)
  (*   I = E − B                                                      *)
  (*   J = x²                                                          *)
  (*   EE = E²                                                        *)
  (*   K = 3·EE                                                        *)
  (*   x' = (B − F)·A                                                 *)
  (*   y' = G² − K                                                    *)
  (*   z' = B·H                                                        *)
  (*   r0 = I                                                          *)
  (*   r1 = 3·J                                                        *)
  (*   r2 = −H                                                         *)
  (*                                                                 *)
  (* `halve` here = multiply by 2^{-1} ∈ Fp. Since we don't have a    *)
  (* dedicated "halve" leaf, we compute halves by maintaining inv2.   *)
  (* To avoid a runtime inv2 computation per iteration, the wrapper   *)
  (* passes `half_fp` as a precomputed input ((p+1)/2 in Mont form).  *)
  (* Cleaner: halve(x) = `mul(x, half_fp)`.                            *)
  (* ============================================================== *)

  Local Notation g2_double_step_name := "bw6_761_g2_double_step".

  (** Argument list:
        x, y, z           — proj coords (Fp3 in/out)
        r0, r1, r2        — line eval coeffs (Fp3 out)
        half_fp           — precomputed (p+1)/2 in Mont (Fp)
   *)
  Definition bw6_761_g2_double_step : function_t :=
    (g2_double_step_name,
     (["x"; "y"; "z"; "r0"; "r1"; "r2"; "half_fp"],
      []:list String.string,
      bedrock_func_body:(
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as A;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as B;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as C;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as D;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as E;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as F;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as G;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as H;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as J;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as EE;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as K;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as tmp;
       coq:(cmd_seq_list [
         (* A = x*y *)
         cmd.call [] fp3_mul_name [expr.var "A"; expr.var "x"; expr.var "y"];
         (* A = halve(A) = A * half_fp *)
         cmd.call [] fp3_mul_fp_name [expr.var "A"; expr.var "A"; expr.var "half_fp"];
         (* B = y² *)
         cmd.call [] fp3_sqr_name [expr.var "B"; expr.var "y"];
         (* C = z² *)
         cmd.call [] fp3_sqr_name [expr.var "C"; expr.var "z"];
         (* D = 3·C *)
         cmd.call [] fp3_add_name [expr.var "D"; expr.var "C"; expr.var "C"];
         cmd.call [] fp3_add_name [expr.var "D"; expr.var "D"; expr.var "C"];
         (* E = 4·D = 12·C *)
         cmd.call [] fp3_add_name [expr.var "E"; expr.var "D"; expr.var "D"];
         cmd.call [] fp3_add_name [expr.var "E"; expr.var "E"; expr.var "E"];
         (* F = 3·E = 36·C *)
         cmd.call [] fp3_add_name [expr.var "F"; expr.var "E"; expr.var "E"];
         cmd.call [] fp3_add_name [expr.var "F"; expr.var "F"; expr.var "E"];
         (* G = halve(B + F) *)
         cmd.call [] fp3_add_name [expr.var "G"; expr.var "B"; expr.var "F"];
         cmd.call [] fp3_mul_fp_name [expr.var "G"; expr.var "G"; expr.var "half_fp"];
         (* H = (y+z)² − B − C *)
         cmd.call [] fp3_add_name [expr.var "H"; expr.var "y"; expr.var "z"];
         cmd.call [] fp3_sqr_name [expr.var "H"; expr.var "H"];
         cmd.call [] fp3_sub_name [expr.var "H"; expr.var "H"; expr.var "B"];
         cmd.call [] fp3_sub_name [expr.var "H"; expr.var "H"; expr.var "C"];
         (* I = E − B (kept in tmp) *)
         cmd.call [] fp3_sub_name [expr.var "tmp"; expr.var "E"; expr.var "B"];
         cmd.call [] fp3_copy_name [expr.var "r0"; expr.var "tmp"];   (* r0 = I *)
         (* J = x² *)
         cmd.call [] fp3_sqr_name [expr.var "J"; expr.var "x"];
         (* EE = E² *)
         cmd.call [] fp3_sqr_name [expr.var "EE"; expr.var "E"];
         (* K = 3·EE *)
         cmd.call [] fp3_add_name [expr.var "K"; expr.var "EE"; expr.var "EE"];
         cmd.call [] fp3_add_name [expr.var "K"; expr.var "K"; expr.var "EE"];
         (* x' = (B − F) · A   (reuse tmp) *)
         cmd.call [] fp3_sub_name [expr.var "tmp"; expr.var "B"; expr.var "F"];
         cmd.call [] fp3_mul_name [expr.var "x"; expr.var "tmp"; expr.var "A"];
         (* y' = G² − K *)
         cmd.call [] fp3_sqr_name [expr.var "tmp"; expr.var "G"];
         cmd.call [] fp3_sub_name [expr.var "y"; expr.var "tmp"; expr.var "K"];
         (* z' = B · H *)
         cmd.call [] fp3_mul_name [expr.var "z"; expr.var "B"; expr.var "H"];
         (* r1 = 3·J *)
         cmd.call [] fp3_add_name [expr.var "r1"; expr.var "J"; expr.var "J"];
         cmd.call [] fp3_add_name [expr.var "r1"; expr.var "r1"; expr.var "J"];
         (* r2 = −H *)
         cmd.call [] fp3_opp_name [expr.var "r2"; expr.var "H"]
       ])
     ))).

  (* ============================================================== *)
  (* g2_add_step:                                                    *)
  (*   gnark's `(p *g2Proj) addMixedStep(evaluations, a *G2Affine)`  *)
  (*                                                                 *)
  (* Inputs (mutable): x, y, z (Fp3 each, g2Proj coords)             *)
  (*                   r0, r1, r2 (Fp3 each, line evaluation)        *)
  (* Inputs (read-only): ax, ay (Fp3 each, affine point to add)      *)
  (*                                                                 *)
  (* Algorithm:                                                       *)
  (*   Y2Z1 = ay * z                                                  *)
  (*   O = y − Y2Z1                                                   *)
  (*   X2Z1 = ax * z                                                  *)
  (*   L = x − X2Z1                                                   *)
  (*   C = O²                                                         *)
  (*   D = L²                                                         *)
  (*   E = L · D                                                      *)
  (*   F = z · C                                                      *)
  (*   G = x · D                                                      *)
  (*   H = E + F − 2·G                                                *)
  (*   t1 = y · E                                                     *)
  (*   x' = L · H                                                     *)
  (*   y' = (G − H)·O − t1                                            *)
  (*   z' = E · z                                                     *)
  (*   r0 = ax·O − ay·L                                               *)
  (*   r1 = −O                                                        *)
  (*   r2 = L                                                         *)
  (* ============================================================== *)

  Local Notation g2_add_step_name := "bw6_761_g2_add_step".

  Definition bw6_761_g2_add_step : function_t :=
    (g2_add_step_name,
     (["x"; "y"; "z"; "r0"; "r1"; "r2"; "ax"; "ay"],
      []:list String.string,
      bedrock_func_body:(
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as Y2Z1;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as O;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as X2Z1;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as L;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as C;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as D;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as E;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as F;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as G;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as H;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as t1;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as tmp;
       coq:(cmd_seq_list [
         (* Y2Z1 = ay * z *)
         cmd.call [] fp3_mul_name [expr.var "Y2Z1"; expr.var "ay"; expr.var "z"];
         (* O = y − Y2Z1 *)
         cmd.call [] fp3_sub_name [expr.var "O"; expr.var "y"; expr.var "Y2Z1"];
         (* X2Z1 = ax * z *)
         cmd.call [] fp3_mul_name [expr.var "X2Z1"; expr.var "ax"; expr.var "z"];
         (* L = x − X2Z1 *)
         cmd.call [] fp3_sub_name [expr.var "L"; expr.var "x"; expr.var "X2Z1"];
         (* C = O² *)
         cmd.call [] fp3_sqr_name [expr.var "C"; expr.var "O"];
         (* D = L² *)
         cmd.call [] fp3_sqr_name [expr.var "D"; expr.var "L"];
         (* E = L · D *)
         cmd.call [] fp3_mul_name [expr.var "E"; expr.var "L"; expr.var "D"];
         (* F = z · C *)
         cmd.call [] fp3_mul_name [expr.var "F"; expr.var "z"; expr.var "C"];
         (* G = x · D *)
         cmd.call [] fp3_mul_name [expr.var "G"; expr.var "x"; expr.var "D"];
         (* H = E + F − 2·G *)
         cmd.call [] fp3_add_name [expr.var "H"; expr.var "E"; expr.var "F"];
         cmd.call [] fp3_add_name [expr.var "tmp"; expr.var "G"; expr.var "G"];
         cmd.call [] fp3_sub_name [expr.var "H"; expr.var "H"; expr.var "tmp"];
         (* t1 = y · E *)
         cmd.call [] fp3_mul_name [expr.var "t1"; expr.var "y"; expr.var "E"];
         (* x' = L · H — must be computed AFTER y' uses x as input.
            We compute y' first, then x', then z'. *)
         (* tmp_y_temp = (G − H)·O − t1 *)
         cmd.call [] fp3_sub_name [expr.var "tmp"; expr.var "G"; expr.var "H"];
         cmd.call [] fp3_mul_name [expr.var "tmp"; expr.var "tmp"; expr.var "O"];
         cmd.call [] fp3_sub_name [expr.var "y"; expr.var "tmp"; expr.var "t1"];
         (* x' = L · H *)
         cmd.call [] fp3_mul_name [expr.var "x"; expr.var "L"; expr.var "H"];
         (* z' = E · z *)
         cmd.call [] fp3_mul_name [expr.var "z"; expr.var "E"; expr.var "z"];
         (* r0 = ax · O − ay · L *)
         cmd.call [] fp3_mul_name [expr.var "tmp"; expr.var "ax"; expr.var "O"];
         cmd.call [] fp3_mul_name [expr.var "r0"; expr.var "ay"; expr.var "L"];
         cmd.call [] fp3_sub_name [expr.var "r0"; expr.var "tmp"; expr.var "r0"];
         (* r1 = −O *)
         cmd.call [] fp3_opp_name [expr.var "r1"; expr.var "O"];
         (* r2 = L *)
         cmd.call [] fp3_copy_name [expr.var "r2"; expr.var "L"]
       ])
     ))).

  (* ============================================================== *)
  (* g2_line_compute:                                                *)
  (*   gnark's `(p *g2Proj) lineCompute(evaluations, a)` — same as   *)
  (*   addMixedStep but skips the point-update (used at i=0).        *)
  (* ============================================================== *)

  Local Notation g2_line_compute_name := "bw6_761_g2_line_compute".

  Definition bw6_761_g2_line_compute : function_t :=
    (g2_line_compute_name,
     (["x"; "y"; "z"; "r0"; "r1"; "r2"; "ax"; "ay"],
      []:list String.string,
      bedrock_func_body:(
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as Y2Z1;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as O;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as X2Z1;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as L;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as tmp;
       coq:(cmd_seq_list [
         cmd.call [] fp3_mul_name [expr.var "Y2Z1"; expr.var "ay"; expr.var "z"];
         cmd.call [] fp3_sub_name [expr.var "O"; expr.var "y"; expr.var "Y2Z1"];
         cmd.call [] fp3_mul_name [expr.var "X2Z1"; expr.var "ax"; expr.var "z"];
         cmd.call [] fp3_sub_name [expr.var "L"; expr.var "x"; expr.var "X2Z1"];
         (* r0 = ax · O − ay · L *)
         cmd.call [] fp3_mul_name [expr.var "tmp"; expr.var "ax"; expr.var "O"];
         cmd.call [] fp3_mul_name [expr.var "r0"; expr.var "ay"; expr.var "L"];
         cmd.call [] fp3_sub_name [expr.var "r0"; expr.var "tmp"; expr.var "r0"];
         cmd.call [] fp3_opp_name [expr.var "r1"; expr.var "O"];
         cmd.call [] fp3_copy_name [expr.var "r2"; expr.var "L"]
       ])
     ))).

  (* ============================================================== *)
  (* sparse_line_eval:                                               *)
  (*   Build the sparse Fp6 line (c0, c1, 0, 0, c4, 0) from           *)
  (*   (r0, r1, r2, p_x, p_y).                                       *)
  (*                                                                 *)
  (* Per gnark:                                                       *)
  (*   c0 = r0                                                        *)
  (*   c1 = r1 · p.X                                                  *)
  (*   c4 = r2 · p.Y                                                  *)
  (*                                                                 *)
  (* Layout in Fp6 = Fp3[w]/(w² − zeta) over Fp3 = Fp[u]/(u³ − nr):   *)
  (*   B0 = (c0,  c1,  0)         (Fp3 in u-basis)                    *)
  (*   B1 = ( 0,  c4,  0)                                             *)
  (*                                                                 *)
  (* Since r1, r2 are Fp3 (with c0 slot equal to gnark's Fp value),   *)
  (* and p.X, p.Y are Fp scalars, the products r1·p.X and r2·p.Y are  *)
  (* Fp3-scaled-by-Fp (the existing fp3_mul_fp helper).               *)
  (* ============================================================== *)

  Local Notation sparse_line_name := "bw6_761_sparse_line_eval".

  Definition bw6_761_sparse_line_eval : function_t :=
    (sparse_line_name,
     (["out"; "r0"; "r1"; "r2"; "p_x"; "p_y"],
      []:list String.string,
      bedrock_func_body:(
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as r1px;
       stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as r2py;
       coq:(cmd_seq_list [
         (* r1px = r1 * p_x  (Fp3-scaled-by-Fp) *)
         cmd.call [] fp3_mul_fp_name [expr.var "r1px"; expr.var "r1"; expr.var "p_x"];
         (* r2py = r2 * p_y *)
         cmd.call [] fp3_mul_fp_name [expr.var "r2py"; expr.var "r2"; expr.var "p_y"];
         (* out.B0.c0 = r0.c0,  out.B0.c1 = r1px.c0,  out.B0.c2 = 0 *)
         cmd.call [] fp_copy_name
           [expr_fp3_c0 (expr_fp6_c0 (expr.var "out"));
            expr_fp3_c0 (expr.var "r0")];
         cmd.call [] fp_copy_name
           [expr_fp3_c1 (expr_fp6_c0 (expr.var "out"));
            expr_fp3_c0 (expr.var "r1px")];
         cmd.call [] from_word_name
           [expr_fp3_c2 (expr_fp6_c0 (expr.var "out")); expr.literal 0];
         (* out.B1.c0 = 0,  out.B1.c1 = r2py.c0,  out.B1.c2 = 0 *)
         cmd.call [] from_word_name
           [expr_fp3_c0 (expr_fp6_c1 (expr.var "out")); expr.literal 0];
         cmd.call [] fp_copy_name
           [expr_fp3_c1 (expr_fp6_c1 (expr.var "out"));
            expr_fp3_c0 (expr.var "r2py")];
         cmd.call [] from_word_name
           [expr_fp3_c2 (expr_fp6_c1 (expr.var "out")); expr.literal 0]
       ])
     ))).

  (* ============================================================== *)
  (* Negation helpers (q0Neg, q1Neg) used inside the loop.           *)
  (* These are functions of (q0/q1) — we either precompute them on   *)
  (* the caller side, or compute inline in the body.  We compute     *)
  (* inline here using Fp3_opp on the Y coordinate.                  *)
  (* ============================================================== *)

  (* The miller loop function expects 6 Fp3 G2 inputs: q0.x, q0.y,
     q1.x, q1.y  (q0Neg.x = q0.x, q0Neg.y = -q0.y; same for q1Neg).
     Rather than pass 4 more args, compute negations as needed inside
     the loop body.  But that means per-iteration Fp3_opp calls.

     Simpler: precompute -q0.y and -q1.y once at function entry into
     scratch buffers.  The actual "neg point" coords are then
     (qX.x, -qX.y).

     For our test (G2 in Fp embedded in Fp3 c0 slot), q1 = q0 (since
     thirdRootOneG1 is applied as Fp scalar on Fp3 element with only
     c0 nonzero — produces a non-trivial scaling, so q1 != q0 in
     general).  We accept q1 as an explicit input. *)

  (* ============================================================== *)
  (* Miller loop dispatch by j ∈ {−3, −1, 0, 1, 3}.                  *)
  (*                                                                 *)
  (* For j ≠ 0 (i.e., we do an addMixedStep on the projective point   *)
  (* with affine partner a_x/a_y), the line and the doubleStep-line  *)
  (* are combined with Mul014By014; we instead compute               *)
  (*   line_double = sparse_line(r0_dbl, r1_dbl, r2_dbl, p_x, p_y)   *)
  (*   line_add    = sparse_line(r0_add, r1_add, r2_add, p_x, p_y)   *)
  (*   f = f * line_double * line_add  (two full Fp6 muls)            *)
  (* (algebraically equivalent to Mul014By014 + MulBy01245).          *)
  (* ============================================================== *)

  (** Emit one Miller-loop iteration for a given `j` value. *)
  Definition miller_iter_body (j : Z) : Syntax.cmd.cmd :=
    let dbl_step :=
      cmd.call [] g2_double_step_name
        [expr.var "qx"; expr.var "qy"; expr.var "qz";
         expr.var "r0d"; expr.var "r1d"; expr.var "r2d";
         expr.var "half_fp"]
    in
    let dbl_line :=
      cmd.call [] sparse_line_name
        [expr.var "line_d"; expr.var "r0d"; expr.var "r1d"; expr.var "r2d";
         expr.var "p_x"; expr.var "p_y"]
    in
    let fsq :=
      cmd.call [] fp6_sqr_name [expr.var "f"; expr.var "f"]
    in
    let fmul_line_d :=
      cmd.call [] fp6_mul_name [expr.var "f"; expr.var "f"; expr.var "line_d"]
    in
    if Z.eqb j 0 then
      cmd_seq_list [ fsq; dbl_step; dbl_line; fmul_line_d ]
    else
      let '(ax_name, ay_name) :=
        match j with
        | 1   => ("q0x", "q0y")
        | -1  => ("q0x", "q0ny")
        | 3   => ("q1x", "q1y")
        | -3  => ("q1x", "q1ny")
        | _   => ("q0x", "q0y")
        end
      in
      let add_step :=
        cmd.call [] g2_add_step_name
          [expr.var "qx"; expr.var "qy"; expr.var "qz";
           expr.var "r0a"; expr.var "r1a"; expr.var "r2a";
           expr.var ax_name; expr.var ay_name]
      in
      let add_line :=
        cmd.call [] sparse_line_name
          [expr.var "line_a"; expr.var "r0a"; expr.var "r1a"; expr.var "r2a";
           expr.var "p_x"; expr.var "p_y"]
      in
      let fmul_line_a :=
        cmd.call [] fp6_mul_name [expr.var "f"; expr.var "f"; expr.var "line_a"]
      in
      cmd_seq_list [ fsq; dbl_step; dbl_line; fmul_line_d;
                     add_step; add_line; fmul_line_a ].

  (** Special: i = 0 — uses lineCompute (no point update) with q1Neg. *)
  Definition miller_iter_final : Syntax.cmd.cmd :=
    cmd_seq_list [
      cmd.call [] fp6_sqr_name [expr.var "f"; expr.var "f"];
      cmd.call [] g2_double_step_name
        [expr.var "qx"; expr.var "qy"; expr.var "qz";
         expr.var "r0d"; expr.var "r1d"; expr.var "r2d";
         expr.var "half_fp"];
      cmd.call [] sparse_line_name
        [expr.var "line_d"; expr.var "r0d"; expr.var "r1d"; expr.var "r2d";
         expr.var "p_x"; expr.var "p_y"];
      cmd.call [] fp6_mul_name [expr.var "f"; expr.var "f"; expr.var "line_d"];
      cmd.call [] g2_line_compute_name
        [expr.var "qx"; expr.var "qy"; expr.var "qz";
         expr.var "r0a"; expr.var "r1a"; expr.var "r2a";
         expr.var "q1x"; expr.var "q1ny"];
      cmd.call [] sparse_line_name
        [expr.var "line_a"; expr.var "r0a"; expr.var "r1a"; expr.var "r2a";
         expr.var "p_x"; expr.var "p_y"];
      cmd.call [] fp6_mul_name [expr.var "f"; expr.var "f"; expr.var "line_a"]
    ].

  (** Special: i = 188 — first iteration, no square (result = 1).
      The line is ASSIGNED to result (not multiplied). *)
  Definition miller_iter_init : Syntax.cmd.cmd :=
    cmd_seq_list [
      cmd.call [] g2_double_step_name
        [expr.var "qx"; expr.var "qy"; expr.var "qz";
         expr.var "r0d"; expr.var "r1d"; expr.var "r2d";
         expr.var "half_fp"];
      (* f = sparse_line(r0d, r1d, r2d, p_x, p_y).
         (Since result was 1 before, assigning the sparse Fp6 line
         directly is equivalent to multiplying by the line.) *)
      cmd.call [] sparse_line_name
        [expr.var "f"; expr.var "r0d"; expr.var "r1d"; expr.var "r2d";
         expr.var "p_x"; expr.var "p_y"]
    ].

  (** Loop counter sequences: LoopCounter[0..188] and LoopCounter1[0..188].

      These reproduce gnark-crypto/ecc/bw6-761/bw6-761.go literals.
      LoopCounter is the NAF of (x_0 + 1).
      LoopCounter1 is the NAF of (x_0^3 - x_0^2 - x_0).

      We pre-tabulate j[i] = LoopCounter1[i]*3 + LoopCounter[i] ∈
      {-3, -1, 0, 1, 3} for i = 0..188. *)
  Definition bw6_j_seq : list Z := [
    -3;  1;  0;  0;  0;  0;  0;  0;  0;  0;
     0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
     0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
     0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
     0;  0;  0;  0;  0;  0; -1;  0;  1;  0;
     0;  1;  0;  0;  0;  0;  1;  0;  1;  0;
     0;  0;  0;  1;  0;  0;  0;  0;  0;  0;
     0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
     0;  0;  0;  0;  0;  0;  0;  0;  0;  0;
     0;  0;  0;  3;  0;  0;  3;  0;  0; -3;
     0;  3;  0; -3;  0;  0;  0;  0; -3;  0;
     3;  0;  0;  0;  3;  0;  0;  0;  3;  0;
     0;  3;  0;  3;  0;  0;  0;  3;  0;  0;
     0;  0;  0;  0;  0;  0;  0;  0; -3;  0;
    -3;  0;  0;  0;  0; -3;  0;  0;  3;  0;
     0;  0; -3;  0;  0; -3;  0;  3;  0; -3;
     0;  0;  0;  3;  0;  0;  3;  0; -3;  0;
     3;  0;  3;  0;  0;  0;  3;  0; -3;  0;
    -3;  0;  0;  0;  0;  0;  3;  0;  0
  ].

  (** Iteration count check: should be 189 entries (i = 0..188). *)

  (** Build the unrolled main-loop body: i = 187 down to 1, the
      dispatch on j[i] producing the appropriate iteration body.
      The i = 188 init and i = 0 final are handled separately.

      [bw6_j_seq] is indexed `[j[0], j[1], ..., j[188]]`.
      We need iterations in descending order: i=187, 186, ..., 1.
      Use `List.rev` then `tl` (drop j[188]) then `removelast` (drop j[0]). *)

  (** Helper: take a list of j-values and produce the concatenated
      cmd_seq_list of per-iteration bodies. *)
  Fixpoint emit_iters (js : list Z) : Syntax.cmd.cmd :=
    match js with
    | [] => cmd.skip
    | j :: rest => cmd.seq (miller_iter_body j) (emit_iters rest)
    end.

  (** Take indices 187 down to 1 from bw6_j_seq.
      bw6_j_seq is [j[0], j[1], ..., j[188]].
      We want j[187], j[186], ..., j[1] for the main loop iterations. *)
  Definition bw6_main_loop_js : list Z :=
    (* Drop the last (j[188]) and the first (j[0]), then reverse. *)
    List.rev (List.tl (List.removelast bw6_j_seq)).

  (** Main miller-loop body, fully unrolled. *)
  Definition miller_loop_optimal_body : Syntax.cmd.cmd :=
    cmd_seq_list [
      (* Initialise projective q = q1 = (q1x, q1y, 1) *)
      cmd.call [] fp3_copy_name [expr.var "qx"; expr.var "q1x"];
      cmd.call [] fp3_copy_name [expr.var "qy"; expr.var "q1y"];
      (* qz = (1, 0, 0) in Fp3 = Fp3-of-1 *)
      cmd.call [] from_word_name
        [expr_fp3_c0 (expr.var "qz"); expr.literal 1];
      cmd.call [] from_word_name
        [expr_fp3_c1 (expr.var "qz"); expr.literal 0];
      cmd.call [] from_word_name
        [expr_fp3_c2 (expr.var "qz"); expr.literal 0];
      (* i = 188: init step (no square) *)
      miller_iter_init;
      (* i = 187 .. 1: main loop, fully unrolled *)
      emit_iters bw6_main_loop_js;
      (* i = 0: final step (j = -3, no point update) *)
      miller_iter_final;
      (* Copy f into the output buffer *)
      cmd.call [] fp6_copy_name [expr.var "out"; expr.var "f"]
    ].

  (* ============================================================== *)
  (* Top-level optimal-ate Miller loop function.                     *)
  (*                                                                 *)
  (* Signature:                                                       *)
  (*   bw6_761_miller_loop_optimal(out, p_x, p_y,                     *)
  (*                                q0x, q0y, q1x, q1y,               *)
  (*                                q0ny, q1ny,                       *)
  (*                                half_fp)                          *)
  (*                                                                 *)
  (* Inputs:                                                          *)
  (*   p_x, p_y     : G1 affine coords in Fp                          *)
  (*   q0x, q0y     : original G2 affine in Fp3                       *)
  (*   q1x, q1y     : endomorphism G2 image (= φ(q0)) in Fp3          *)
  (*   q0ny, q1ny   : −q0.y, −q1.y in Fp3 (caller-precomputed)         *)
  (*   half_fp      : (p+1)/2 mod p in Mont form (Fp)                  *)
  (*                                                                 *)
  (* Output: out = e_loop(P, Q) ∈ Fp6 (before final exponentiation).  *)
  (* ============================================================== *)

  Local Notation bw6_761_miller_loop_optimal_name :=
    "bw6_761_miller_loop_optimal".

  Definition bw6_761_miller_loop_optimal : function_t :=
    (bw6_761_miller_loop_optimal_name,
     (["out"; "p_x"; "p_y";
       "q0x"; "q0y"; "q1x"; "q1y";
       "q0ny"; "q1ny";
       "half_fp"],
      []:list String.string,
      bedrock_func_body:(
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as f;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as qx;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as qy;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as qz;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as r0d;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as r1d;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as r2d;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as r0a;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as r1a;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp3)) as r2a;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as line_d;
        stackalloc (AbstractField.felem_size_in_bytes (F:=Fp6)) as line_a;
        coq:(miller_loop_optimal_body)
      ))).

  (* ============================================================== *)
  (* Specs (memory-safety + bounds; full correctness Admitted for    *)
  (* Phase 1).                                                       *)
  (* ============================================================== *)

  Instance spec_of_bw6_761_g2_double_step : spec_of "bw6_761_g2_double_step" :=
    fnspec! "bw6_761_g2_double_step"
      (px py pz pr0 pr1 pr2 phalf : word)
      / (x y z r0 r1 r2 : Fp3_felem) (half : Fp_felem) Rr,
    { requires tr mem :=
        Fp3_bounded Fp3_loose x /\
        Fp3_bounded Fp3_loose y /\
        Fp3_bounded Fp3_loose z /\
        Fp_bounded Fp_tight half /\
        (FElem_Fp3 px x *
         (FElem_Fp3 py y *
          (FElem_Fp3 pz z *
           (FElem_Fp3 pr0 r0 *
            (FElem_Fp3 pr1 r1 *
             (FElem_Fp3 pr2 r2 *
              (FElem_Fp phalf half * Rr)))))))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists x' y' z' r0' r1' r2',
          Fp3_bounded Fp3_loose x' /\
          Fp3_bounded Fp3_loose y' /\
          Fp3_bounded Fp3_loose z' /\
          Fp3_bounded Fp3_loose r0' /\
          Fp3_bounded Fp3_loose r1' /\
          Fp3_bounded Fp3_loose r2' /\
          (FElem_Fp3 px x' *
           (FElem_Fp3 py y' *
            (FElem_Fp3 pz z' *
             (FElem_Fp3 pr0 r0' *
              (FElem_Fp3 pr1 r1' *
               (FElem_Fp3 pr2 r2' *
                (FElem_Fp phalf half * Rr)))))))%sep mem' /\
          (let '((nx, ny, nz), (c0, c1, c2)) :=
             bw6_proj_double_step
               (Fp3_feval x) (Fp3_feval y) (Fp3_feval z) (Fp_feval half) in
           Fp3_feval x' = nx /\ Fp3_feval y' = ny /\ Fp3_feval z' = nz /\
           Fp3_feval r0' = c0 /\ Fp3_feval r1' = c1 /\ Fp3_feval r2' = c2) }.

  Instance spec_of_bw6_761_g2_add_step : spec_of "bw6_761_g2_add_step" :=
    fnspec! "bw6_761_g2_add_step"
      (px py pz pr0 pr1 pr2 pax pay : word)
      / (x y z r0 r1 r2 ax ay : Fp3_felem) Rr,
    { requires tr mem :=
        Fp3_bounded Fp3_loose x /\
        Fp3_bounded Fp3_loose y /\
        Fp3_bounded Fp3_loose z /\
        Fp3_bounded Fp3_tight ax /\
        Fp3_bounded Fp3_tight ay /\
        (FElem_Fp3 px x *
         (FElem_Fp3 py y *
          (FElem_Fp3 pz z *
           (FElem_Fp3 pr0 r0 *
            (FElem_Fp3 pr1 r1 *
             (FElem_Fp3 pr2 r2 *
              (FElem_Fp3 pax ax *
               (FElem_Fp3 pay ay * Rr))))))))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists x' y' z' r0' r1' r2',
          Fp3_bounded Fp3_loose x' /\
          Fp3_bounded Fp3_loose y' /\
          Fp3_bounded Fp3_loose z' /\
          Fp3_bounded Fp3_loose r0' /\
          Fp3_bounded Fp3_loose r1' /\
          Fp3_bounded Fp3_loose r2' /\
          (FElem_Fp3 px x' *
           (FElem_Fp3 py y' *
            (FElem_Fp3 pz z' *
             (FElem_Fp3 pr0 r0' *
              (FElem_Fp3 pr1 r1' *
               (FElem_Fp3 pr2 r2' *
                (FElem_Fp3 pax ax *
                 (FElem_Fp3 pay ay * Rr))))))))%sep mem' /\
          (let '((nx, ny, nz), (c0, c1, c2)) :=
             bw6_proj_add_step
               (Fp3_feval x) (Fp3_feval y) (Fp3_feval z)
               (Fp3_feval ax) (Fp3_feval ay) in
           Fp3_feval x' = nx /\ Fp3_feval y' = ny /\ Fp3_feval z' = nz /\
           Fp3_feval r0' = c0 /\ Fp3_feval r1' = c1 /\ Fp3_feval r2' = c2) }.

  Instance spec_of_bw6_761_g2_line_compute : spec_of "bw6_761_g2_line_compute" :=
    fnspec! "bw6_761_g2_line_compute"
      (px py pz pr0 pr1 pr2 pax pay : word)
      / (x y z r0 r1 r2 ax ay : Fp3_felem) Rr,
    { requires tr mem :=
        Fp3_bounded Fp3_loose x /\
        Fp3_bounded Fp3_loose y /\
        Fp3_bounded Fp3_loose z /\
        Fp3_bounded Fp3_tight ax /\
        Fp3_bounded Fp3_tight ay /\
        (FElem_Fp3 px x *
         (FElem_Fp3 py y *
          (FElem_Fp3 pz z *
           (FElem_Fp3 pr0 r0 *
            (FElem_Fp3 pr1 r1 *
             (FElem_Fp3 pr2 r2 *
              (FElem_Fp3 pax ax *
               (FElem_Fp3 pay ay * Rr))))))))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists r0' r1' r2',
          Fp3_bounded Fp3_loose r0' /\
          Fp3_bounded Fp3_loose r1' /\
          Fp3_bounded Fp3_loose r2' /\
          (FElem_Fp3 px x *
           (FElem_Fp3 py y *
            (FElem_Fp3 pz z *
             (FElem_Fp3 pr0 r0' *
              (FElem_Fp3 pr1 r1' *
               (FElem_Fp3 pr2 r2' *
                (FElem_Fp3 pax ax *
                 (FElem_Fp3 pay ay * Rr))))))))%sep mem' /\
          (let '(c0, c1, c2) :=
             bw6_proj_line_compute
               (Fp3_feval x) (Fp3_feval y) (Fp3_feval z)
               (Fp3_feval ax) (Fp3_feval ay) in
           Fp3_feval r0' = c0 /\ Fp3_feval r1' = c1 /\ Fp3_feval r2' = c2) }.

  Instance spec_of_bw6_761_sparse_line_eval : spec_of "bw6_761_sparse_line_eval" :=
    fnspec! "bw6_761_sparse_line_eval"
      (pout pr0 pr1 pr2 ppx ppy : word)
      / (old_out : Fp6_felem) (r0 r1 r2 : Fp3_felem) (px py : Fp_felem) Rr,
    { requires tr mem :=
        Fp3_bounded Fp3_loose r0 /\
        Fp3_bounded Fp3_loose r1 /\
        Fp3_bounded Fp3_loose r2 /\
        Fp_bounded Fp_loose px /\
        Fp_bounded Fp_loose py /\
        (FElem_Fp6 pout old_out *
         (FElem_Fp3 pr0 r0 *
          (FElem_Fp3 pr1 r1 *
           (FElem_Fp3 pr2 r2 *
            (FElem_Fp ppx px *
             (FElem_Fp ppy py * Rr))))))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_bounded Fp6_loose out /\
          (FElem_Fp6 pout out *
           (FElem_Fp3 pr0 r0 *
            (FElem_Fp3 pr1 r1 *
             (FElem_Fp3 pr2 r2 *
              (FElem_Fp ppx px *
               (FElem_Fp ppy py * Rr))))))%sep mem' /\
          Fp6_feval out =
            bw6_proj_sparse_line
              (Fp3_feval r0) (Fp3_feval r1) (Fp3_feval r2)
              (Fp_feval px) (Fp_feval py) }.

  Instance spec_of_bw6_761_miller_loop_optimal :
      spec_of "bw6_761_miller_loop_optimal" :=
    fnspec! "bw6_761_miller_loop_optimal"
      (pout p_px p_py p_q0x p_q0y p_q1x p_q1y
       p_q0ny p_q1ny p_half : word)
      / (old_out : Fp6_felem)
        (p_x p_y : Fp_felem)
        (q0x q0y q1x q1y q0ny q1ny : Fp3_felem)
        (half : Fp_felem) Rr,
    { requires tr mem :=
        Fp_bounded Fp_loose p_x /\
        Fp_bounded Fp_loose p_y /\
        Fp3_bounded Fp3_tight q0x /\
        Fp3_bounded Fp3_tight q0y /\
        Fp3_bounded Fp3_tight q1x /\
        Fp3_bounded Fp3_tight q1y /\
        Fp3_bounded Fp3_tight q0ny /\
        Fp3_bounded Fp3_tight q1ny /\
        Fp_bounded Fp_tight half /\
        (FElem_Fp6 pout old_out *
         (FElem_Fp p_px p_x *
          (FElem_Fp p_py p_y *
           (FElem_Fp3 p_q0x q0x *
            (FElem_Fp3 p_q0y q0y *
             (FElem_Fp3 p_q1x q1x *
              (FElem_Fp3 p_q1y q1y *
               (FElem_Fp3 p_q0ny q0ny *
                (FElem_Fp3 p_q1ny q1ny *
                 (FElem_Fp p_half half * Rr))))))))))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          Fp6_bounded Fp6_loose out /\
          (FElem_Fp6 pout out *
           (FElem_Fp p_px p_x *
            (FElem_Fp p_py p_y *
             (FElem_Fp3 p_q0x q0x *
              (FElem_Fp3 p_q0y q0y *
               (FElem_Fp3 p_q1x q1x *
                (FElem_Fp3 p_q1y q1y *
                 (FElem_Fp3 p_q0ny q0ny *
                  (FElem_Fp3 p_q1ny q1ny *
                   (FElem_Fp p_half half * Rr))))))))))%sep mem' }.

  (* ============================================================== *)
  (* Function list for extraction                                    *)
  (* ============================================================== *)

  Definition bw6_761_miller_loop_optimal_funcs : list function_t :=
    [ bw6_761_g2_double_step;
      bw6_761_g2_add_step;
      bw6_761_g2_line_compute;
      bw6_761_sparse_line_eval;
      bw6_761_miller_loop_optimal ].

End BW6_MillerLoopOptimal.
