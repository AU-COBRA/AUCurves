(** * BW6-761 G2 bedrock2 add (Fp3, projective, a = 0) — WP layer.

    Applies the [MontgomeryCurveSpecsFp3] framework to BW6-761's G2:
    [y^2 = x^3 + b']  over  [Fp3 = Fp[zeta]/(zeta^3 + 4)].

    Companion to [BW6_761Curve_G1_bedrock.v] (G1 over Fp, 12 x 64-bit
    WBW limbs).  This file is the G2 analogue: same projective
    Renes–Costello–Batina add formula specialised to [a = 0], but
    every base field operation acts on Fp3-felems (36 x 64-bit
    limbs = 3 cubic coefficients × 12 limbs each).

    Architecture:

      - The [Syntax.func] body is produced by
        [Fp3_proj_add_func] in [MontgomeryCurveSpecsFp3.v], applied
        with BW6's Fp3 op names (["bw6_761_Fp3_add"], etc., obtained
        via the [AbstractField.add]/[sub]/[mul] strings from
        [bw6_Fp3_params]).

      - The [spec_of] is stated in terms of [AbstractField.FElem]
        for [bw6_Fp3_repr], so the [feval] in the post is the
        Fp3-valued [feval] (a triple of [F bw6_M_pos]).

      - The Gallina post composes [BW6_G2_add_Gallina_spec_a_0] from
        [BW6_761Curve_G2.v] with the framework's
        [Fp3_proj_add_a0]; the two formulas agree by [reflexivity].

    Phase 2 deliverable (GitHub #65): the FRAMEWORK + BODY + SPEC
    + match lemma are Qed.  The full WP correctness proof is
    Admitted with documented recipe (see [BW6_761_G2_add_func_ok]'s
    proof skeleton at the end of this file).  Closing it follows the
    same per-call [next_call] template used by
    [BW6_761_MillerLoop_proof.v] — see that file for the running
    pattern (~30 calls vs Miller's ~60). *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Memory.
Require Import bedrock2.Semantics.
Require Import bedrock2.BasicC64Semantics.

Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.

Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.ModularArithmetic.
Require Crypto.Bedrock.Field.Translation.Parameters.Defaults64.

Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.

Require Import Bedrock.Curve.BW6_761Curve_G2.
Require Import Bedrock.Curve.MontgomeryCurveSpecsFp3.

Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section BW6_761_G2_bedrock.

  (** ** Bring BW6's Fp3 typeclass instances into scope. *)

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp_repr
    bw6_Fp_repr_ok
    bw6_Fp_names
    bw6_Fp3_params
    bw6_Fp3_repr
    bw6_Fp3_repr_ok
    bw6_Fp3_names.

  Local Notation Fp  := (F PrimeField.M_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.

  Local Notation FElem_Fp3 :=
    (@AbstractField.FElem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_bounded :=
    (@AbstractField.bounded_by _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_tight :=
    (@AbstractField.tight_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_loose :=
    (@AbstractField.loose_bounds _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_felem :=
    (@AbstractField.felem _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).
  Local Notation Fp3_feval :=
    (@AbstractField.feval _ bw6_Fp3_params _ _ _ _ bw6_Fp3_repr).

  Local Typeclasses Opaque bw6_Fp3_params.

  (** ** Callee spec instances (Fp3 ops) *)

  Instance spec_of_bw6_761_G2_Fp3_mul : spec_of (AbstractField.mul (F := Fp3)) :=
    AbstractField.binop_spec (F := Fp3) (field_representation := bw6_Fp3_repr)
                             AbstractField.bin_mul.
  Instance spec_of_bw6_761_G2_Fp3_add : spec_of (AbstractField.add (F := Fp3)) :=
    AbstractField.binop_spec (F := Fp3) (field_representation := bw6_Fp3_repr)
                             AbstractField.bin_add.
  Instance spec_of_bw6_761_G2_Fp3_sub : spec_of (AbstractField.sub (F := Fp3)) :=
    AbstractField.binop_spec (F := Fp3) (field_representation := bw6_Fp3_repr)
                             AbstractField.bin_sub.

  (** ** Apply the framework to BW6 *)

  (** The three_b Fp3 element that the body uses.  Computed once,
      passed in by reference by the caller.  Stored as [Fp3] for the
      Gallina spec; the bedrock2 caller stashes its felem at
      [pthreeb]. *)
  Definition bw6_761_G2_three_b_fp3 : Fp3 :=
    @bw6_G2_three_b _ prime_field_parameters bw6_Fp_mul_by_nr_model.

  (** Caller-side function names: BW6 Fp3 ops are auto-derived from
      the [fp3_prefix] string in [BW6_761_Instances.v]. *)
  Local Notation bw6_Fp3_add_name := (@AbstractField.add _ bw6_Fp3_params).
  Local Notation bw6_Fp3_sub_name := (@AbstractField.sub _ bw6_Fp3_params).
  Local Notation bw6_Fp3_mul_name := (@AbstractField.mul _ bw6_Fp3_params).

  (** The actual bedrock2 function body.

      [Fp3_proj_add_body] does NOT depend on [mul_by_nr] or
      [three_b] (those are only used by the Gallina spec, not the
      cmd structure), so they don't appear as section-generalised
      arguments to the body.  Only [base_fp]/[base_repr] (used by
      [felem_size_in_bytes] for stackalloc) + the 3 op-name strings. *)
  Definition BW6_761_G2_add_body : Syntax.cmd.cmd :=
    Fp3_proj_add_body
      (F := Fp) (base_fp := prime_field_parameters) (base_repr := bw6_Fp_repr)
      bw6_Fp3_add_name bw6_Fp3_sub_name bw6_Fp3_mul_name.

  Definition BW6_761_G2_add : Syntax.func :=
    Fp3_proj_add_func
      (F := Fp) (base_fp := prime_field_parameters) (base_repr := bw6_Fp_repr)
      bw6_Fp3_add_name bw6_Fp3_sub_name bw6_Fp3_mul_name.

  Definition BW6_761_G2_add_name : String.string := "bw6_761_G2_add".

  Definition BW6_761_G2_add_func : String.string * Syntax.func :=
    (BW6_761_G2_add_name, BW6_761_G2_add).

  (** ** Match: framework spec ≡ G2-specific Gallina spec

      Both [Fp3_proj_add_a0] (from the framework) and
      [BW6_G2_add_Gallina_spec_a_0] (from [BW6_761Curve_G2.v]) are
      structurally the same projective add formula over Fp3, just
      with their parameters specialised differently.  This lemma
      ties them at the BW6 instance, so downstream consumers only
      need to remember one of the two names. *)
  Lemma BW6_G2_add_specs_match_Fp3_proj_add
    (X1 Y1 Z1 X2 Y2 Z2 : Fp3) :
    @Fp3_proj_add_a0 Fp prime_field_parameters bw6_Fp_mul_by_nr_model
                     bw6_761_G2_three_b_fp3 X1 Y1 Z1 X2 Y2 Z2
    = @BW6_G2_add_Gallina_spec_a_0 Fp prime_field_parameters
                                   bw6_Fp_mul_by_nr_model X1 Y1 Z1 X2 Y2 Z2.
  Proof.
    reflexivity.
  Qed.

  (** ** Function spec (WP-style)

      Matches [spec_of_BW6_761_add] in [BW6_761Curve_G1_bedrock.v]
      structurally, but the carrier is [FElem_Fp3] (3 × 12 = 36
      limbs per coord) and the Gallina post is [Fp3_proj_add_a0]
      via [Fp3_feval] (instead of [eval_from_mont] over WBW limbs).

      The spec takes 10 pointer arguments in the order:
        [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2; pthreeb]
      with [pthreeb] pointing to a caller-allocated buffer holding
      the Fp3-felem encoding of [bw6_761_G2_three_b_fp3]. *)
  Instance spec_of_BW6_761_G2_add : spec_of BW6_761_G2_add_name :=
    fun functions =>
      forall (x1 y1 z1 x2 y2 z2 oldx oldy oldz threeb : Fp3_felem)
             (px1 py1 pz1 px2 py2 pz2 poutx pouty poutz pthreeb : word.rep)
             (tr : Semantics.trace) (m0 : Interface.map.rep)
             (Rout : Interface.map.rep -> Prop),
        Fp3_bounded Fp3_tight x1 /\
        Fp3_bounded Fp3_tight y1 /\
        Fp3_bounded Fp3_tight z1 /\
        Fp3_bounded Fp3_tight x2 /\
        Fp3_bounded Fp3_tight y2 /\
        Fp3_bounded Fp3_tight z2 /\
        Fp3_bounded Fp3_tight threeb /\
        Fp3_feval threeb = bw6_761_G2_three_b_fp3 ->
        ((FElem_Fp3 px1 x1) *
         (FElem_Fp3 py1 y1) *
         (FElem_Fp3 pz1 z1) *
         (FElem_Fp3 px2 x2) *
         (FElem_Fp3 py2 y2) *
         (FElem_Fp3 pz2 z2) *
         (FElem_Fp3 pthreeb threeb) *
         (FElem_Fp3 poutx oldx) *
         (FElem_Fp3 pouty oldy) *
         (FElem_Fp3 poutz oldz) * Rout)%sep m0 ->
        WeakestPrecondition.call functions BW6_761_G2_add_name tr m0
          [poutx; pouty; poutz; px1; py1; pz1; px2; py2; pz2; pthreeb]
          (fun (tr' : Semantics.trace) (m' : Interface.map.rep)
               (rets : list word.rep) =>
             tr = tr' /\
             rets = nil /\
             exists (outx outy outz : Fp3_felem) Rout',
               ((FElem_Fp3 px1 x1) *
                (FElem_Fp3 py1 y1) *
                (FElem_Fp3 pz1 z1) *
                (FElem_Fp3 px2 x2) *
                (FElem_Fp3 py2 y2) *
                (FElem_Fp3 pz2 z2) *
                (FElem_Fp3 pthreeb threeb) *
                (FElem_Fp3 poutx outx) *
                (FElem_Fp3 pouty outy) *
                (FElem_Fp3 poutz outz) * Rout')%sep m' /\
               (Fp3_feval outx, Fp3_feval outy, Fp3_feval outz) =
                 @Fp3_proj_add_a0 _ prime_field_parameters bw6_Fp_mul_by_nr_model
                   bw6_761_G2_three_b_fp3
                   (Fp3_feval x1) (Fp3_feval y1) (Fp3_feval z1)
                   (Fp3_feval x2) (Fp3_feval y2) (Fp3_feval z2) /\
               Fp3_bounded Fp3_tight outx /\
               Fp3_bounded Fp3_tight outy /\
               Fp3_bounded Fp3_tight outz).

  (** ** Correctness (Admitted, with recipe)

      The proof is mechanical — it follows the same per-call pattern
      as [BW6_761_MillerLoop_proof.v] but at the much smaller scale
      of the projective add formula (33 callee invocations vs
      Miller's ~60).  The skeleton:

        1. [eapply WeakestPreconditionProperties.start_func] with
           the [BW6_761_G2_add_func] env entry.
        2. [cbv [WeakestPrecondition.func]] then unfold
           [BW6_761_G2_add] and [Fp3_proj_add_body] to expose the
           cmd skeleton.
        3. Handle the 6 [stackalloc] sites by [eapply
           WeakestPreconditionProperties.exec_seq] +
           [Memory.anybytes_to_FElem] (or its Fp3-felem equivalent).
        4. For each of the 33 [cmd.call] sites:
              - Invoke the appropriate Fp3 callee spec
                ([spec_of_bw6_761_G2_Fp3_mul] /
                 [spec_of_bw6_761_G2_Fp3_add] /
                 [spec_of_bw6_761_G2_Fp3_sub])
              - Discharge the bounds + sep preconditions
              - Extract the [feval out = ...] postcondition
        5. After the last call, the local context contains 33
           Fp3-level [feval]-equations of the form
              [Fp3_feval ti = fpe_op (Fp3_feval xj) (Fp3_feval xk)]
           These telescope to exactly [Fp3_proj_add_a0].
        6. Postcondition: split the sep, witness [outx; outy; outz]
           as the final temporary values, [reflexivity] on the
           Gallina equation modulo a [rewrite] over the 33 [feval]
           equations.

      Total estimated effort: ~600 LoC, ~8 hours.  The same per-call
      pattern can be packaged as an [Ltac next_Fp3_call] tactic that
      handles steps (4a-4c) in one shot, in which case the total
      drops to ~300 LoC.  Compare BLS12_G2_add_func_ok in
      [BLS12Curve_G2.v] which uses exactly this approach for a
      mostly-identical 33-call body (over Fp2 instead of Fp3).

      Blocker: the inline [next_call] tactic in [BLS12Curve_G2.v]
      hard-codes 6-limb Fp2 [Bignum] specs; porting it to abstract
      [AbstractField.binop_spec] over Fp3-felems is straightforward
      but unwritten.  The BW6 Miller loop file at
      [BW6_761_MillerLoop_proof.v] demonstrates the correct
      [AbstractField]-style call-handling and provides reusable
      patterns; the [bw6_761_Fp3_mul_fp_ok] proof in
      [BW6_761_PairingHelpers.v] is the closest reusable template. *)

  Theorem BW6_761_G2_add_func_ok :
    forall functions,
      Interface.map.get functions BW6_761_G2_add_name = Some BW6_761_G2_add ->
      spec_of_bw6_761_G2_Fp3_mul functions ->
      spec_of_bw6_761_G2_Fp3_add functions ->
      spec_of_bw6_761_G2_Fp3_sub functions ->
      spec_of_BW6_761_G2_add functions.
  Proof.
  Admitted.

End BW6_761_G2_bedrock.

(** ** Notes for downstream consumers

    To call [BW6_761_G2_add] from a higher-level routine:

      1. Allocate 10 Fp3-felem buffers (each 36 limbs = 288 bytes
         on x86-64): 3 outputs + 6 input coords + 1 three_b stash.
      2. Initialise the three_b stash with the precomputed encoding
         of [bw6_761_G2_three_b_fp3] (computable via [vm_compute] in
         a pre-pass, akin to G1's [three_b_mont] constant table).
      3. Call [BW6_761_G2_add] with the 10 pointers in the order
         [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2; pthreeb].
      4. The output Fp3-felems are bounded-by-tight and decode (via
         [Fp3_feval]) to the projective add of the input points.

    The next deferred items in Phase 2 are:

      - [bw6_761_G2_double] (projective doubling specialised at
        [a = 0]; formula in [BW6_761Curve_G2.v]'s
        [BW6_G2_dbl_Gallina_spec_a_0]).
      - [bw6_761_G2_neg] (single Fp3 opp on the y-coordinate).
      - Affine wrappers + scalar mul (separate file once the WP
        correctness above is closed).

    These follow the same framework pattern with smaller bodies
    (doubling: ~12 calls; neg: 1 call). *)
