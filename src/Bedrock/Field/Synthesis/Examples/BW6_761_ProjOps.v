(** * BW6-761 instantiation of the projective optimal-ate model.

    Instantiates the generic [ProjectiveMultibase] model at the BW6-761
    tower (Fp -> Fp3 -> Fp6), providing the [FieldOps] instance and the
    three tower constructors/accessors the sparse line needs.  This is
    the shared foundation imported by both the strengthened callee specs
    (in [BW6_761_MillerLoopOptimal]) and the loop invariant (in
    [BW6_761_MillerLoopOptimal_proof_Common]).

    Tower layout (from [GenericCubicSpecs] / [GenericQuadratic]):
      Fp3 = ((F p * F p) * F p)   (cubic, slots c0,c1,c2)
      Fp6 = (Fp3 * Fp3)           (quadratic, blocks B0,B1) *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.ProjectiveMultibase.

Import BinInt String.
Local Open Scope Z_scope.

Section BW6_761_ProjOps.

  Existing Instances
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp3_params bw6_Fp6_params.

  Local Notation Fp  := (F PrimeField.M_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  (** Scalar-multiply an Fp3 by an Fp element (componentwise). *)
  Definition bw6_fp3_mul_fp (x : Fp3) (s : Fp) : Fp3 :=
    let '(a, b, c) := x in (F.mul a s, F.mul b s, F.mul c s).

  (** Unused [make_line] field of [FieldOps] — the projective model
      never calls it (the line is built by [proj_sparse_line] from the
      step coefficients), but the record requires a value. *)
  Definition bw6_make_line_stub (lam Tx Ty : Fp3) (Px Py : Fp) : Fp6 :=
    @AbstractField.Fone _ bw6_Fp6_params.

  (** [FieldOps] instance for the BW6 tower.  Fp2 := Fp3, Fp12 := Fp6. *)
  Definition bw6_proj_ops : FieldOps Fp Fp3 Fp6 :=
    {| fp_zero    := @F.zero PrimeField.M_pos;
       fp_one     := @F.one PrimeField.M_pos;
       fp2_zero   := @AbstractField.Fzero _ bw6_Fp3_params;
       fp2_one    := @AbstractField.Fone _ bw6_Fp3_params;
       fp2_add    := @AbstractField.Fadd _ bw6_Fp3_params;
       fp2_sub    := @AbstractField.Fsub _ bw6_Fp3_params;
       fp2_neg    := @AbstractField.Fopp _ bw6_Fp3_params;
       fp2_mul    := @AbstractField.Fmul _ bw6_Fp3_params;
       fp2_sqr    := fun x => @AbstractField.Fmul _ bw6_Fp3_params x x;
       fp2_inv    := @AbstractField.Finv _ bw6_Fp3_params;
       fp2_mul_fp := bw6_fp3_mul_fp;
       fp12_one   := @AbstractField.Fone _ bw6_Fp6_params;
       fp12_mul   := @AbstractField.Fmul _ bw6_Fp6_params;
       fp12_sqr   := fun x => @AbstractField.Fmul _ bw6_Fp6_params x x;
       make_line  := bw6_make_line_stub |}.

  (** Tower constructors/accessors. *)
  Definition bw6_fp3_mk (a b c : Fp) : Fp3 := (a, b, c).
  Definition bw6_fp3_c0 (x : Fp3) : Fp := fst (fst x).
  Definition bw6_fp6_mk (b0 b1 : Fp3) : Fp6 := (b0, b1).

  (** BW6-specialised per-step models (the value targets for the
      strengthened callee specs). *)
  Definition bw6_proj_double_step := proj_double_step bw6_proj_ops.
  Definition bw6_proj_add_step    := proj_add_step bw6_proj_ops.
  Definition bw6_proj_line_compute := proj_line_compute bw6_proj_ops.
  Definition bw6_proj_sparse_line :=
    proj_sparse_line bw6_proj_ops bw6_fp3_mk bw6_fp3_c0 bw6_fp6_mk.

  (** BW6-specialised loop + top-level model (the value target for the
      strengthened miller-loop postcondition). *)
  Definition bw6_proj_multibase_iter :=
    proj_multibase_iter bw6_proj_ops bw6_fp3_mk bw6_fp3_c0 bw6_fp6_mk.
  Definition bw6_proj_miller_5symbol_aux :=
    proj_miller_5symbol_aux bw6_proj_ops bw6_fp3_mk bw6_fp3_c0 bw6_fp6_mk.
  Definition bw6_proj_optimal_ate :=
    proj_miller_optimal_ate bw6_proj_ops bw6_fp3_mk bw6_fp3_c0 bw6_fp6_mk.

  Definition bw6_proj_init_step :=
    proj_init_step bw6_proj_ops bw6_fp3_mk bw6_fp3_c0 bw6_fp6_mk.
  Definition bw6_proj_main_loop :=
    proj_main_loop bw6_proj_ops bw6_fp3_mk bw6_fp3_c0 bw6_fp6_mk.
  Definition bw6_proj_final_adjustment :=
    proj_final_adjustment bw6_proj_ops bw6_fp3_mk bw6_fp3_c0 bw6_fp6_mk.

  (** Projective Z-coordinate "1" used to lift the affine seed point. *)
  Definition bw6_fp3_one : Fp3 := @AbstractField.Fone _ bw6_Fp3_params.

  (** Whole-body model, structured exactly as [miller_loop_optimal_body]:
        seed T := (q1x, q1y, 1), f := 1;
        i=188 init (no square, f := doubling line);
        i=187..1 main loop over [main_js];
        i=0 final adjustment (line through doubled T at (q1x, q1ny)).
      [main_js] is the bedrock [bw6_main_loop_js] (= rev (tl (removelast
      bw6_j_seq))), supplied by the caller (which has the digit list). *)
  Definition bw6_proj_whole_body
      (main_js : list Z) (Px Py : Fp)
      (q0x q0y q1x q1y q0ny q1ny : Fp3) (half : Fp) : Fp6 :=
    let '(f1, (x1, y1, z1)) :=
      bw6_proj_init_step Px Py half q1x q1y bw6_fp3_one in
    let '(f2, (x2, y2, z2)) :=
      bw6_proj_main_loop main_js
        q0x q0y q0ny q1x q1y q1ny Px Py half f1 x1 y1 z1 in
    bw6_proj_final_adjustment f2 x2 y2 z2 q1x q1ny Px Py half.

End BW6_761_ProjOps.
