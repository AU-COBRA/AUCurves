(** * Gap G7 at P-256: the table hypothesis becomes a theorem.

    [P256_wNAF_Instance.p256_wnaf_single_full] takes

      p256_table_ok Px Py Pz table_entries

    as a caller obligation: the caller must hand in a buffer already
    holding four on-curve points [pt_eq] to [1P;3P;5P;7P].  Two files
    together discharge it.

    - [WnafTableBuild.rcb_table4_ok] (Qed) is the ALGEBRAIC half: the
      Gallina list [rcb_build_table4 a three_b P] has length four and
      its entries are on the curve and [pt_eq] to the odd multiples.
      §1 below instantiates it at the P-256 constants, giving
      [p256_table4_ok].

    - [WnafTableFunc.precompute_table4_body_ok] (Qed) is the MEMORY
      half: a nineteen-call straight-line bedrock2 command leaves the
      caller's buffer, described by
      [BLS12_wNAF_ProcessDigits.Table4], holding exactly that list.
      §2 instantiates it at the P-256 function table, giving
      [p256_precompute_table4_ok]: after the body runs, the buffer
      holds SOME [entries] that satisfy [p256_table_ok].

    §3 composes the two commands.  [p256_wnaf_single_full_precomputed]
    runs [precompute_table4_body] and then the wNAF driver on the same
    memory and has NO [p256_table_ok] hypothesis: the table it uses is
    the one the first command wrote.  The two hypotheses that remain —
    the scalar bound and [p256_oncurve (Px,Py,Pz)] — are genuine
    caller obligations about the input point and scalar, not about
    memory.

    Honesty ledger: no [Admitted] and no [Axiom] in this file. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P256.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Require Import Bedrock.Group.ScalarMult.WnafTableBuild.
Require Import Bedrock.Group.ScalarMult.WnafTableFunc.
Require Import Bedrock.Group.ScalarMult.P256_wNAF_Instance.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section P256_TableFunc.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p256_field_parameters
    p256_field_parameters_ok
    p256_frep
    p256_frep_ok.

  Local Notation F := (F M_pos).

  (* ================================================================ *)
  (** ** 1. The Gallina table at the P-256 constants                   *)
  (* ================================================================ *)

  (** [WnafTableFunc.table4_of] at the two stored curve constants.  By
      [table4_of_is_rcb] this is [WnafTableBuild.rcb_build_table4] at
      [p256_a_val] / [p256_three_b_val], by conversion. *)
  Definition p256_table4 (P : F * F * F) : list (F * F * F) :=
    table4_of p256_three_b_felem p256_a_felem P.

  (** The chain's table obligation, for that list.  Every side
      condition [rcb_table4_ok] takes is already a theorem of
      P256_wNAF_Instance §1b. *)
  Theorem p256_table4_ok :
    forall Px Py Pz,
      p256_oncurve (Px, Py, Pz) ->
      p256_table_ok Px Py Pz (p256_table4 (Px, Py, Pz)).
  Proof.
    intros Px Py Pz Hoc.
    unfold p256_table4, p256_table_ok.
    rewrite (table4_of_is_rcb p256_three_b_felem p256_a_felem (Px, Py, Pz)).
    exact (rcb_table4_ok p256_M_gt_27 p256_a_val p256_b_val p256_three_b_val
             p256_Hthree_b p256_Hdisc p256_Hexcept (Px, Py, Pz) Hoc).
  Qed.

  (* ================================================================ *)
  (** ** 2. The memory half at P-256                                   *)
  (* ================================================================ *)

  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  (** After [precompute_table4_body] the caller's buffer holds a table
      the chain accepts.  The base point is unchanged; the scratch
      point is clobbered (it ends at 2P, which the statement does not
      expose). *)
  Theorem p256_precompute_table4_ok :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
    forall Px Py Pz,
      p256_oncurve (Px, Py, Pz) ->
    forall pT pQx pQy pQz pPx pPy pPz
      (Qx0 Qy0 Qz0 x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 : F)
      (R : BasicC64Semantics.mem -> Prop) tr m l,
      map.get l "table_P" = Some pT ->
      map.get l "tmpx" = Some pQx ->
      map.get l "tmpy" = Some pQy ->
      map.get l "tmpz" = Some pQz ->
      map.get l "px" = Some pPx ->
      map.get l "py" = Some pPy ->
      map.get l "pz" = Some pPz ->
      (Table4 pT [(x0,y0,z0); (x1,y1,z1); (x2,y2,z2); (x3,y3,z3)]
       ⋆ Point3 (Some tight_bounds) pQx pQy pQz Qx0 Qy0 Qz0
       ⋆ Point3 (Some tight_bounds) pPx pPy pPz Px Py Pz ⋆ R) m ->
      WeakestPrecondition.cmd functions precompute_table4_body tr m l
        (fun tr' m' l' =>
           tr' = tr /\ l' = l /\
           exists entries Qx Qy Qz,
             p256_table_ok Px Py Pz entries /\
             (Table4 pT entries
              ⋆ Point3 (Some tight_bounds) pQx pQy pQz Qx Qy Qz
              ⋆ Point3 (Some tight_bounds) pPx pPy pPz Px Py Pz ⋆ R) m').
  Proof.
    intros functions Htab Hleaf Px Py Pz Hoc pT pQx pQy pQz pPx pPy pPz
           Qx0 Qy0 Qz0 x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 R tr m l
           HlT HlQx HlQy HlQz HlPx HlPy HlPz Hm.
    eapply weaken_cmd.
    1: { refine (precompute_table4_body_ok
                   p256_three_b_felem p256_a_felem functions
                   (p256_felem_copy_spec functions Htab)
                   (p256_HCurveAddInplace functions Htab Hleaf)
                   pT pQx pQy pQz pPx pPy pPz Px Py Pz Qx0 Qy0 Qz0
                   x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 R tr m l
                   HlT HlQx HlQy HlQz HlPx HlPy HlPz Hm). }
    cbv beta. intros tr' m' l' Hp.
    destruct Hp as (Ht & Hl & Qx & Qy & Qz & Hsep).
    split; [ exact Ht | ]. split; [ exact Hl | ].
    exists (p256_table4 (Px, Py, Pz)), Qx, Qy, Qz.
    split; [ exact (p256_table4_ok Px Py Pz Hoc) | exact Hsep ].
  Qed.

  (* ================================================================ *)
  (** ** 3. The composition: G7's table hypothesis is discharged       *)
  (* ================================================================ *)

  (** [p256_wnaf_single_full] with [p256_table_ok] REMOVED from the
      hypotheses.  The command is [precompute_table4_body] followed by
      the wNAF driver body, run on one memory; the table the driver
      reads is the one the first command wrote, and the caller supplies
      only an uninitialised (but well-typed) four-point buffer.

      The driver's aux point doubles as the builder's scratch point:
      the locals hypotheses require "auxx"/"tmpx" (and the other two
      coordinates) to name the same addresses.  The base point lives at
      "px"/"py"/"pz" and survives unchanged.

      What still has to hold of the caller: the scalar bound and
      [p256_oncurve (Px,Py,Pz)].  Both are conditions on the INPUTS,
      not on memory contents. *)
  Theorem p256_wnaf_single_full_precomputed :
    forall functions,
      p256_wnaf_table_ok functions ->
      p256_wnaf_leaf_specs functions ->
    forall k, 0 <= k < 2 ^ 256 ->
    forall Px Py Pz,
      p256_oncurve (Px, Py, Pz) ->
    forall pOx pOy pOz pAx pAy pAz pT pDK pPx pPy pPz
      (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F)
      (x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 : F)
      (Rinner : BasicC64Semantics.mem -> Prop) tr m l,
      map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
      map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
      map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
      map.get l "tmpx" = Some pAx -> map.get l "tmpy" = Some pAy ->
      map.get l "tmpz" = Some pAz ->
      map.get l "px" = Some pPx -> map.get l "py" = Some pPy ->
      map.get l "pz" = Some pPz ->
      map.get l "table_P" = Some pT ->
      map.get l "digits_k" = Some pDK ->
      (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
       ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0
       ⋆ DigitArray pDK (p256_digits k)
       ⋆ Table4 pT [(x0,y0,z0); (x1,y1,z1); (x2,y2,z2); (x3,y3,z3)]
       ⋆ Point3 (Some tight_bounds) pPx pPy pPz Px Py Pz
       ⋆ Rinner) m ->
      WeakestPrecondition.cmd functions
        (cmd.seq precompute_table4_body (snd (snd p256_wnaf_single_func)))
        tr m l
        (fun t m' l' =>
           exists Rx Ry Rz Ax' Ay' Az' entries,
             p256_table_ok Px Py Pz entries
             /\ p256_oncurve (Rx, Ry, Rz)
             /\ p256_pt_eq (Rx, Ry, Rz) (p256_scmul (Z.to_nat k) (Px, Py, Pz))
             /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
                 ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az'
                 ⋆ DigitArray pDK (p256_digits k) ⋆ Table4 pT entries
                 ⋆ Point3 (Some tight_bounds) pPx pPy pPz Px Py Pz
                 ⋆ Rinner) m').
  Proof.
    intros functions Htab Hleaf k Hk Px Py Pz Hoc
           pOx pOy pOz pAx pAy pAz pT pDK pPx pPy pPz
           Ox0 Oy0 Oz0 Ax0 Ay0 Az0 x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3
           Rinner tr m l
           HgOx HgOy HgOz HgAx HgAy HgAz HgTx HgTy HgTz
           HgPx HgPy HgPz HgT HgDK Hm.
    apply wp_seq.
    (* the builder, with the driver's out point and digit array framed *)
    eapply weaken_cmd.
    1: { eapply (p256_precompute_table4_ok functions Htab Hleaf Px Py Pz Hoc
                   pT pAx pAy pAz pPx pPy pPz Ax0 Ay0 Az0
                   x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3
                   (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
                    ⋆ DigitArray pDK (p256_digits k) ⋆ Rinner)%sep tr m l);
         [ exact HgT | exact HgTx | exact HgTy | exact HgTz
         | exact HgPx | exact HgPy | exact HgPz | ecancel_assumption ]. }
    cbv beta. intros tr1 m1 l1 Hp.
    destruct Hp as (Ht1 & Hl1 & entries & Qx & Qy & Qz & Hent & Hsep).
    subst tr1. subst l1.
    (* the driver, with the base point framed and [Hent] supplying G7 *)
    eapply weaken_cmd.
    1: { refine (p256_wnaf_single_full functions Htab Hleaf k Hk Px Py Pz
                   entries Hoc Hent
                   pOx pOy pOz pAx pAy pAz pT pDK Ox0 Oy0 Oz0 Qx Qy Qz
                   (Point3 (Some tight_bounds) pPx pPy pPz Px Py Pz ⋆ Rinner)%sep
                   tr m1 l _ _ _ _ _ _ _ _ _);
         [ exact HgOx | exact HgOy | exact HgOz | exact HgAx | exact HgAy
         | exact HgAz | exact HgT | exact HgDK | ecancel_assumption ]. }
    cbv beta. intros t2 m2 l2 Hq.
    destruct Hq as (Rx & Ry & Rz & Ax' & Ay' & Az' & Honc & Heqv & Hs2).
    exists Rx, Ry, Rz, Ax', Ay', Az', entries.
    split; [ exact Hent | ]. split; [ exact Honc | ]. split; [ exact Heqv | ].
    ecancel_assumption.
  Qed.

End P256_TableFunc.

(** * What this closes

    G7 had two halves.

    - ALGEBRAIC (closed earlier, [WnafTableBuild.rcb_table4_ok]):
      the Gallina list is a correct table.  §1 instantiates it:
      [p256_table4_ok].
    - MEMORY (closed here, on [WnafTableFunc.precompute_table4_body_ok]):
      a bedrock2 command writes that list into the caller's buffer.
      §2 instantiates it: [p256_precompute_table4_ok].

    §3's [p256_wnaf_single_full_precomputed] is
    [P256_wNAF_Instance.p256_wnaf_single_full] with the
    [p256_table_ok] hypothesis discharged rather than assumed.

    NOT claimed here: that any caller (Rust or otherwise) actually
    invokes [precompute_table4_body]; that the digit array holds
    [p256_digits k] by construction rather than by hypothesis; and
    nothing about the extracted code. *)
