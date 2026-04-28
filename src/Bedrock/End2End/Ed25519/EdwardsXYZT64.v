(** * Ed25519 Edwards XYZT atoms — 64-bit port (Step 1 of Phase 1.3).
 *
 * Mirror of [fiat-crypto/.../X25519/EdwardsXYZT.v] but instantiated at
 * 64-bit BasicC64Semantics + Field25519_64's frep25519. The bedrock2
 * `func` syntax trees are width-agnostic; the proofs need 64-bit
 * field-representation hints.
 *
 * Status (Step 1 in progress):
 *   - Sub-task 1.1: structure definitions Qed (projective/precomputed/cached).
 *   - Sub-task 1.2: bedrock2 func aliases (4 Local Notations).
 *   - Sub-task 1.3: spec_of declarations Qed (4 Instances).
 *   - Sub-task 1.4: helper Ltac Qed + 3 implies_valid lemmas Qed.
 *     program_logic_goal_for_function! macro now resolves cleanly after
 *     re-Existing the upstream spec_of_fe25519_* Section-local Instances.
 *   - Sub-task 1.5: _ok proofs (4 lemmas, ~25-150 LoC each) — pending.
 *
 * See [option-b-64bit-port-plan.md] for the full Step 1 plan. *)

(* All heavy imports + Existing Instances live in the Imports loader
   so MCP can iterate on this file's content without hitting the
   600s file-load timeout. See feedback_mcp_timeout_heavy_imports.md. *)
Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
(* Bring `syntactic_unify_deltavar` Tactic Notation into scope; needed by
   the local ecancel_assumption_fast wrapper below. Already loaded
   transitively via bedrock2.Map.SeparationLogic. *)
Require Import coqutil.Tactics.syntactic_unify.

Module Ed25519XYZT64.

  (** Ed25519 Edwards curve parameters (from Curve25519.E).
      Use F_scope so unqualified `*`, `+`, `-` resolve to the
      F-arithmetic versions. Override `x^2` to mean `x*x` (matching
      upstream EdwardsXYZT.v's Local Notation), NOT `F.pow x 2%N` —
      the validity predicates use the multiplicative form, so
      sigtype-obligation discharge needs the same. *)
  Local Open Scope F_scope.
  Local Notation a := Curve25519.E.a.
  Local Notation d := Curve25519.E.d.
  Local Notation "x ^ 2" := (F.mul x x) (only parsing, at level 30).
  (* Mirror upstream's section-local 0/1 notations (Local Notation "0" := Fzero,
     Local Notation "1" := Fone) so unqualified literals in the validity
     predicates resolve to F.zero / F.one, not nat/Z. *)
  Local Notation "0" := F.zero.
  Local Notation "1" := F.one.
  Local Notation point := (@Extended.point _ Logic.eq F.zero F.add F.mul a d).
  (* precomputed_point: {F} {Feq} {Fone} {Fadd Fsub Fmul} {a d} *)
  Local Notation precomputed_point :=
    (@Precomputed.precomputed_point _ Logic.eq F.one F.add F.sub F.mul a d).
  (* cached: {F} {Feq} {Fzero} {Fadd Fsub Fmul Fdiv} {a d} *)
  Local Notation cached :=
    (@Readdition.cached _ Logic.eq F.zero F.add F.sub F.mul F.div a d).

  (** ** Sub-task 1.1: structure definitions (projective/precomputed/cached
      coords with bounds). Verbatim port from
      [fiat-crypto/.../X25519/EdwardsXYZT.v] lines 222-294. The
      `felem` and `feval` resolve to our 64-bit [frep25519] instance
      via Existing Instance above; bounds (`tight_bounds`,
      `loose_bounds`) come from the same. *)

  Definition valid_projective_coords (X Y Z Ta Tb : felem):=
    ((a * (feval X)^2*(feval Z)^2 + (feval Y)^2*(feval Z)^2 = ((feval Z)^2)^2 + d * (feval X)^2 * (feval Y)^2)%F /\
    ((feval X) * (feval Y) = (feval Z) * (feval Ta) * (feval Tb))%F /\
    ((feval Z) <> 0)%F).

  Definition projective_coords := { c | let '(X,Y,Z,Ta,Tb) := c in
    valid_projective_coords X Y Z Ta Tb /\
    bounded_by tight_bounds X /\ bounded_by tight_bounds Y /\ bounded_by tight_bounds Z /\
    bounded_by loose_bounds Ta /\ bounded_by loose_bounds Tb }.

  Definition feval_projective_coords (c : projective_coords) :=
    let '(X, Y, Z, Ta, Tb) := proj1_sig c in (feval X, feval Y, feval Z, feval Ta, feval Tb).

  Definition coords_to_point (c : projective_coords) : point.
    refine (exist _ (feval_projective_coords c) _).
    abstract (destruct_head' projective_coords;
      cbv [proj1_sig feval_projective_coords valid_projective_coords] in *;
      destruct_head' prod; destruct_head' and; tauto).
  Defined.

  Definition valid_precomputed_coords (half_ypx half_ymx xyd : felem) :=
    let x := (feval half_ypx) - (feval half_ymx) in
    let y := (feval half_ypx) + (feval half_ymx) in
    (a*x^2 + y^2 = 1 + d*x^2*y^2)
    /\ (feval xyd) = x * y * d.

  Definition precomputed_coords := { c | let '(half_ypx, half_ymx, xyd) := c in
                              valid_precomputed_coords half_ypx half_ymx xyd /\
                              bounded_by loose_bounds half_ymx /\ bounded_by loose_bounds half_ypx /\
                              bounded_by loose_bounds xyd }.

  Definition feval_precomputed_coords (c : precomputed_coords) :=
    let '(half_ypx, half_ymx, xyd) := proj1_sig c in (feval half_ypx, feval half_ymx, feval xyd).

  Definition precomputed_coords_to_precomputed (c : precomputed_coords) : precomputed_point.
    refine (exist _ (feval_precomputed_coords c) _).
    abstract (destruct_head' precomputed_coords; destruct_head' prod;
    destruct_head' and; cbv [feval_precomputed_coords valid_precomputed_coords proj1_sig] in *; tauto).
  Defined.

  Definition valid_cached_coords (half_YmX half_YpX Z Td : felem):=
    let X := (feval half_YpX) - (feval half_YmX) in
    let Y := (feval half_YpX) + (feval half_YmX) in
    let T := (feval Td) / d in
    let Z := (feval Z) in
      a * X^2*Z^2 + Y^2*Z^2 = (Z^2)^2 + d * X^2 * Y^2 /\
      X * Y = Z * T /\
      Z <> 0.

  Definition cached_coords := { c | let '(half_YmX, half_YpX, Z, Td) := c in
                              valid_cached_coords half_YmX half_YpX Z Td /\
                              bounded_by loose_bounds half_YmX /\ bounded_by loose_bounds half_YpX /\
                              bounded_by loose_bounds Z /\ bounded_by loose_bounds Td }.

  Definition feval_cached_coords (c : cached_coords) :=
    let '(half_YmX, half_YpX, Z, Td) := proj1_sig c in (feval half_YmX, feval half_YpX, feval Z, feval Td).

  Definition cached_coords_to_cached (c : cached_coords) : cached.
    refine (exist _ (feval_cached_coords c) _).
    abstract (destruct_head' cached_coords; destruct_head' prod;
    destruct_head' and;
      cbv [valid_cached_coords proj1_sig] in *; tauto).
  Defined.

  (** ** Sub-task 1.2: bedrock2 funcs.
      Reuse the upstream Definitions directly — bedrock2 [func] syntax
      trees are width-agnostic. The 32-bit instantiation in upstream
      doesn't affect the syntax. *)
  Local Notation add_precomputed64 := Crypto.Bedrock.End2End.X25519.EdwardsXYZT.add_precomputed.
  Local Notation double64          := Crypto.Bedrock.End2End.X25519.EdwardsXYZT.double.
  Local Notation to_cached64       := Crypto.Bedrock.End2End.X25519.EdwardsXYZT.to_cached.
  Local Notation readd64           := Crypto.Bedrock.End2End.X25519.EdwardsXYZT.readd.

  (* Declare 64-bit spec_of instances for the field operations called by
     to_cached/add_precomputed/double/readd. CANNOT use upstream's
     spec_of_fe25519_*: those are at 32-bit width (Naive.word32) because
     upstream's section fixes Bitwidth32. Our [frep25519] (re-exported in
     the Imports loader) is the 64-bit FieldRepresentation, so
     [spec_of_BinOp bin_sub] etc. resolves to the 64-bit shape via the
     [field_representation:=frep25519] implicit. *)
  Local Instance spec_of_fe25519_sub64 : spec_of "fe25519_sub" := spec_of_BinOp bin_sub.
  Local Instance spec_of_fe25519_add64 : spec_of "fe25519_add" := spec_of_BinOp bin_add.
  Local Instance spec_of_fe25519_carry_add64 : spec_of "fe25519_carry_add" := spec_of_BinOp bin_carry_add.
  Local Instance spec_of_fe25519_carry_sub64 : spec_of "fe25519_carry_sub" := spec_of_BinOp bin_carry_sub.
  Local Instance spec_of_fe25519_mul64 : spec_of "fe25519_mul" := spec_of_BinOp bin_mul.
  Local Instance spec_of_fe25519_square64 : spec_of "fe25519_square" := spec_of_UnOp un_square.
  Local Instance spec_of_fe25519_copy64 : spec_of "fe25519_copy" := spec_of_felem_copy.
  Local Instance spec_of_fe25519_from_word64 : spec_of "fe25519_from_word" := spec_of_from_word.
  (* fe25519_half spec moved to after [word] Notation below. *)

  (** ** Sub-task 1.3: spec_of declarations.
      Mirror of upstream lines 319-400. Key fix: shadow [word] as
      [Naive.word 64] (matching [BasicC64Semantics.word := Naive.word64])
      so [(p_out: word)] in fnspec! resolves to a concrete Type. *)

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Local Notation word := (Naive.word 64).
  Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
  Local Notation felem := (felem(FieldRepresentation:=frep25519)).
  Local Notation bounded_by := (bounded_by(FieldRepresentation:=frep25519)).
  Local Notation felem_size := 40.

  (* fe25519_half: no synthesized impl in fiat-crypto. Upstream's
     spec_of_fe25519_half is at 32-bit width (Naive.word32), incompatible
     with our 64-bit setup. Mirror the same spec SHAPE at 64-bit. *)
  Local Instance spec_of_fe25519_half64 : spec_of "fe25519_half" :=
    fnspec! "fe25519_half"
      (result_location input_location: word) / (old_result input: felem)
      (R: _ -> Prop),
    { requires t m :=
      bounded_by loose_bounds input /\
      (exists Ra : map.rep -> Prop, ((FElem input_location input) * Ra)%sep m) /\
      ((FElem result_location old_result) * R)%sep m;
      ensures t' m' :=
        t = t' /\
        exists result : felem,
          bounded_by tight_bounds result /\
          feval result = F.div (feval input) (F.add F.one F.one) /\
          ((FElem result_location result) * R)%sep m'}.

  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
  Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).

  (* Sep predicates for points: p5@ projective, p4@ cached, p3@ precomputed.
     Verbatim from upstream lines 297-317. *)
  Local Notation "c 'p5@' p" := (let '(X,Y,Z,Ta,Tb) := proj1_sig c in sep (sep (sep (sep
                                (FElem (p) X)
                                (FElem (p .+ felem_size) Y))
                                (FElem (p .+ (felem_size + felem_size)) Z))
                                (FElem (p .+ (felem_size + felem_size + felem_size)) Ta))
                                (FElem (p .+ (felem_size + felem_size + felem_size + felem_size)) Tb))
                                (at level 10, format "c 'p5@' p").
  Local Notation "c 'p4@' p" := (let '(half_ymx, half_ypx ,z,td) := proj1_sig c in sep (sep (sep
                                (FElem (p) half_ymx)
                                (FElem (p .+ felem_size) half_ypx))
                                (FElem (p .+ (felem_size + felem_size)) z))
                                (FElem (p .+ (felem_size + felem_size + felem_size)) td))
                                (at level 10, format "c 'p4@' p").
  Local Notation "c 'p3@' p" := (let '(half_ymx, half_ypx, xyd) := proj1_sig c in sep (sep
                                (FElem (p) half_ymx)
                                (FElem (p .+ felem_size) half_ypx))
                                (FElem (p .+ (felem_size + felem_size)) xyd))
                                (at level 10, format "c 'p3@' p").

  (* Algebraic instance witnesses needed by the m1* operators.
     [nonzero_a]/[square_a]/[nonsquare_d] reuse Curve25519.E proofs;
     [a_eq_minus1] is [eq_refl] since [a := F.opp 1];
     [nonzero_d] discharged by Decidable.vm_decide. *)
  Lemma a_eq_minus1 : Curve25519.E.a = F.opp F.one. Proof. reflexivity. Qed.
  Lemma nonzero_d : Curve25519.E.d <> F.zero. Proof. Decidable.vm_decide. Qed.
  Definition twice_d : F Curve25519.p := F.add Curve25519.E.d Curve25519.E.d.
  Lemma k_eq_2d : twice_d = F.add Curve25519.E.d Curve25519.E.d. Proof. reflexivity. Qed.

  (* Group-operation Notations specialized to Curve25519. *)
  Local Notation m1double :=
    (Extended.m1double (a:=a) (d:=d)
       (nonzero_a:=Curve25519.E.nonzero_a)
       (square_a:=Curve25519.E.square_a)
       (nonsquare_d:=Curve25519.E.nonsquare_d)
       (a_eq_minus1:=a_eq_minus1)
       (twice_d:=twice_d)
       (k_eq_2d:=k_eq_2d)).
  Local Notation m1_prep :=
    (Readdition.m1_prep (a:=a) (d:=d)
       (nonzero_a:=Curve25519.E.nonzero_a)
       (a_eq_minus1:=a_eq_minus1)
       (twice_d:=twice_d)
       (k_eq_2d:=k_eq_2d)
       (nonzero_d:=nonzero_d)).
  Local Notation m1_readd :=
    (Readdition.m1_readd (a:=a) (d:=d)
       (nonzero_a:=Curve25519.E.nonzero_a)
       (square_a:=Curve25519.E.square_a)
       (nonsquare_d:=Curve25519.E.nonsquare_d)
       (a_eq_minus1:=a_eq_minus1)
       (twice_d:=twice_d)
       (k_eq_2d:=k_eq_2d)
       (nonzero_d:=nonzero_d)).
  Local Notation m1add_precomputed_coordinates :=
    (Precomputed.m1add_precomputed_coordinates (a:=a) (d:=d)
       (nonzero_a:=Curve25519.E.nonzero_a)
       (square_a:=Curve25519.E.square_a)
       (nonsquare_d:=Curve25519.E.nonsquare_d)
       (a_eq_minus1:=a_eq_minus1)).

  Global Instance spec_of_add_precomputed64 : spec_of "add_precomputed" :=
    fnspec! "add_precomputed"
      (p_out p_a p_b: word) /
      (a: projective_coords) (b: precomputed_coords) (out : list byte) (R: _ -> Prop), {
        requires t m :=
          m =* out $@ p_out * a p5@ p_a * b p3@ p_b * R/\
          Datatypes.length out = Z.to_nat (5 * felem_size);
        ensures t' m' :=
          t = t' /\
          exists a_plus_b : projective_coords,
            m' =* a_plus_b p5@ p_out * a p5@ p_a * b p3@ p_b * R /\
            proj1_sig (m1add_precomputed_coordinates (coords_to_point a) (precomputed_coords_to_precomputed b))
               = feval_projective_coords a_plus_b
      }.

  (** spec_of_double64: Path A (5-separate-exists, mirrors secp256k1
      JacobianCoZ.v's pattern). Avoids the sigma-unfolding goal blowup
      in the postcondition discharge. The validity+bounds are inlined
      as separate conjuncts; the FElem chunks are written directly. *)
  Global Instance spec_of_double64 : spec_of "double" :=
    fnspec! "double"
      (p_out p_a: word) /
      (a: projective_coords) (out : list byte) (R: _ -> Prop), {
        requires t m :=
          m =* out $@ p_out * a p5@ p_a * R /\
          Datatypes.length out = Z.to_nat (5 * felem_size);
        ensures t' m' :=
          t = t' /\
          exists (X Y Z Ta Tb : felem),
            valid_projective_coords X Y Z Ta Tb /\
            bounded_by tight_bounds X /\
            bounded_by tight_bounds Y /\
            bounded_by tight_bounds Z /\
            bounded_by loose_bounds Ta /\
            bounded_by loose_bounds Tb /\
            m' =* (FElem p_out X * FElem (p_out.+felem_size) Y *
                   FElem (p_out.+(felem_size+felem_size)) Z *
                   FElem (p_out.+(felem_size+felem_size+felem_size)) Ta *
                   FElem (p_out.+(felem_size+felem_size+felem_size+felem_size)) Tb) *
                  a p5@ p_a * R /\
            proj1_sig (m1double (coords_to_point a)) =
              (feval X, feval Y, feval Z, feval Ta, feval Tb)
      }.

  Global Instance spec_of_to_cached64 : spec_of "to_cached" :=
    fnspec! "to_cached"
      (p_out p_a p_d: word) /
      (a: projective_coords) (d1: felem) (out : list byte) (R: _ -> Prop), {
        requires t m :=
          m =* out $@ p_out * a p5@ p_a * FElem p_d d1 * R /\
          Datatypes.length out = Z.to_nat (4 * felem_size) /\
          d = feval d1 /\
          bounded_by tight_bounds d1;
        ensures t' m' :=
          t = t' /\
          exists a_cached: cached_coords,
            m' =* a_cached p4@ p_out * a p5@ p_a * FElem p_d d1 * R /\
            proj1_sig (m1_prep (coords_to_point a)) = feval_cached_coords a_cached
    }.

  Global Instance spec_of_readd64 : spec_of "readd" :=
    fnspec! "readd"
      (p_out p_a p_c: word) /
      (a: projective_coords) (c: cached_coords) (out : list byte) (R: _ -> Prop), {
        requires t m :=
          m =* out $@ p_out * a p5@ p_a * c p4@ p_c * R /\
          Datatypes.length out = Z.to_nat (5 * felem_size);
        ensures t' m' :=
          t = t' /\
          exists a_plus_c: projective_coords,
            m' =* a_plus_c p5@ p_out * a p5@ p_a * c p4@ p_c * R /\
            proj1_sig (m1_readd (coords_to_point a) (cached_coords_to_cached c))
              = feval_projective_coords a_plus_c
      }.

  (** ** Sub-task 1.4: helper Ltac (verbatim port from upstream lines 412-475).
      The Ltac is width-agnostic — uses bedrock2 sep-logic + bounds tactics
      that do not reference [word32] vs [word64]. *)

  (* Helper lemmas mirroring upstream lines 238, 261, 289 — needed by
     the _ok proofs to relate [point]/[precomputed]/[cached] sigtype
     witnesses to their structural validity predicate. *)
  Lemma point_implies_coords_valid (p : point) (X Y Z Ta Tb : felem):
    proj1_sig p = (feval X, feval Y, feval Z, feval Ta, feval Tb) ->
    valid_projective_coords X Y Z Ta Tb.
  Proof.
    intros.
    cbv [proj1_sig] in *. destruct_head' @Extended.point. destruct_head' prod.
    Prod.inversion_prod; subst.
    assumption.
  Qed.

  Lemma precomputed_implies_coords_valid (p : precomputed_point)
        (half_ypx half_ymx xyd : felem):
    proj1_sig p = (feval half_ypx, feval half_ymx, feval xyd) ->
    valid_precomputed_coords half_ypx half_ymx xyd.
  Proof.
    intros.
    cbv [proj1_sig valid_precomputed_coords] in *.
    destruct_head' @Precomputed.precomputed_point.
    destruct_head' prod. Prod.inversion_prod; subst.
    assumption.
  Qed.

  Lemma cached_implies_coords_valid (c : cached) (half_YmX half_YpX Z Td : felem):
    proj1_sig c = (feval half_YmX, feval half_YpX, feval Z, feval Td) ->
    valid_cached_coords half_YmX half_YpX Z Td.
  Proof.
    intros.
    cbv [proj1_sig valid_cached_coords] in *.
    destruct_head' @Readdition.cached.
    destruct_head' prod. Prod.inversion_prod; subst.
    assumption.
  Qed.

  Local Ltac destruct_points :=
    repeat match goal with
      | _ => progress destruct_head' projective_coords
      | _ => progress destruct_head' precomputed_coords
      | _ => progress destruct_head' cached_coords
      | _ => progress destruct_head' prod
      | _ => progress destruct_head' and
      | _ => progress lazy beta match zeta delta
                       [Precomputed.precomputed_coordinates Readdition.cached_coordinates proj1_sig] in *
    end.

  Local Ltac cbv_bounds H :=
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds] in H;
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  Local Ltac solve_bounds :=
    repeat match goal with
    | H: bounded_by loose_bounds ?x |- bounded_by loose_bounds ?x => apply H
    | H: bounded_by tight_bounds ?x |- bounded_by tight_bounds ?x => apply H
    | H: bounded_by tight_bounds ?x |- bounded_by loose_bounds ?x => apply relax_bounds
    | H: bounded_by _ ?x |- bounded_by _ ?x => cbv_bounds H
    end.

  Ltac skipn_firstn_length :=
    change felem_size_in_bytes with 40 in *; listZnWords.

  (* split_stack_at_n_in: 64-bit-port variant.
     Diverges from upstream's verbatim helper in two ways needed by our setup:
     (i) takes [n_z : Z] separately from [n_nat : nat] because
         [map.of_list_word_at_app_n] expects Z while [firstn]/[skipn] need nat;
         upstream's helper passes [n] in both positions and relies on a context
         where the nat literal coerces to Z, which doesn't fire here.
     (ii) explicit [ListDef.firstn] / [ListDef.skipn] in the [adjacent_arrays_disjoint_n]
         instantiation — after [firstn_skipn] rewrite, H6 contains Stdlib's
         [ListDef.firstn]/[ListDef.skipn] (they're the impls of the Stdlib lemma's
         RHS), but bare [firstn]/[skipn] in our scope resolves to coqutil's
         versions, causing seprewrite to syntactically fail to match. *)
  Ltac split_stack_at_n_in stack p n_nat n_z H :=
    rewrite <- (firstn_skipn n_nat stack) in H;
    rewrite (map.of_list_word_at_app_n _ _ _ n_z) in H by
      (rewrite length_firstn; cbv [felem_size_in_bytes] in *; listZnWords);
    let D := fresh in
    unshelve(epose (sep_eq_putmany _ _ (map.adjacent_arrays_disjoint_n p (ListDef.firstn n_nat stack) (ListDef.skipn n_nat stack) n_z _ _)) as D);
      [ rewrite length_firstn; cbv [felem_size_in_bytes] in *; listZnWords
      | rewrite length_firstn, length_skipn; cbv [felem_size_in_bytes] in *; listZnWords
      | seprewrite_in D H; rewrite ?skipn_skipn in H;
        bottom_up_simpl_in_hyp H; clear D ].

  Local Ltac solve_length :=
    try lia;
    (* 64-bit-port addition: side condition from
       array1_iff_eq_of_list_word_at is `Z.of_nat (length _) <= 2^width`
       (= 2^64 here). lia can't materialize 2^64, so chain through 2^7
       (= 128, easily ≥ all our 40-byte stackalloc buffers). *)
    try (match goal with
         | |- (Z.of_nat (Datatypes.length ?l) <= 2 ^ _)%Z =>
             apply Z.le_trans with (Z.pow 2 7);
               [ change felem_size_in_bytes with 40 in *;
                 rewrite ?length_firstn, ?length_skipn;
                 try (match goal with
                      | H : Datatypes.length l = _ |- _ => rewrite H
                      end);
                 try listZnWords; try lia
               | apply Z.pow_le_mono_r; lia ]
         end);
    match goal with
      | |- Datatypes.length _ = _ =>
        solve [rewrite ?ws2bs_felem_length; try lia;
            change felem_size_in_bytes with 40 in *; try listZnWords; lia]
    end.

  Local Ltac solve_mem :=
    repeat match goal with
      | |- exists _ : _ -> Prop, _%sep _ => eexists
      | H: ?P%sep ?m |- ?G%sep ?m => progress ecancel_assumption_preprocess_with solve_length
      | H : _ %sep ?m |- _ %sep ?m => bottom_up_simpl_in_goal
      | |- _%sep _ => ecancel_assumption
    end.

  Local Ltac single_step :=
    repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds; try solve_length.

  (** clear_call_intermediates: drop sep hyps, intermediate map.rep variables,
      and `let l_k := map.put` bindings that are subsumed by the final state.
      WHY: After `repeat single_step` for double/add_precomputed/readd, the env
      accumulates ~20 intermediate H_k sep hyps + 10+ a_k map.rep vars + 7
      l_k let-bindings. Each sep hyp shows the FULL nested FElem chain, so
      the env hits 50-100K chars and MCP truncates output before the actual
      goal is visible. This kills interactive debug. See
      `feedback_clear_intermediate_seps.md`.
      The H-number list below is specific to the DOUBLE recipe (12 calls); if
      add_precomputed (13 calls) or readd (12 calls) have different counts,
      adjust. `try clear` is robust to missing names. *)
  Local Ltac clear_double_intermediates :=
    try clear H20 H21 H22 H23 H27 H28 H29 H30 H34 H35 H36 H37
              H41 H42 H43 H44 H48 H49 H50 H51 H52 H53 H54 H55 H56 H57
              H61 H62 H63 H64 H65 H66 H67 H71 H72 H73 H74 H75 H76 H77 H78 H79;
    try clear a3 a6 a9 a12 a14 a15 a17 a19 a21 a23 a24 a25;
    try clear l l0 l1 l2 l3 l4 l5 l6.

  Ltac solve_deallocation := dealloc_preprocess; repeat straightline.

  Ltac split_output_stack stack_var ptr_var num_points :=
    match goal with
    | H : context[stack_var $@ ptr_var] |- _ =>
      split_stack_at_n_in stack_var ptr_var 40%nat 40 H;
      split_stack_at_n_in (ListDef.skipn 40 stack_var) (ptr_var .+ 40) 40%nat 40 H;
      split_stack_at_n_in (ListDef.skipn 80 stack_var) (ptr_var .+ 80) 40%nat 40 H;
      match num_points with
      | 4 => idtac
      | 5 =>
        split_stack_at_n_in (ListDef.skipn 120 stack_var) (ptr_var .+ 120) 40%nat 40 H
      end
    end.

  (** ** Sub-task 1.5: _ok proofs.

      Recipe (verified end-to-end via MCP, full Qed):
        1. Override ecancel_assumption with ecancel_assumption_impl
           (the impl1-form variant that walks the FElem<->bytes Hint
           Extern at Specs/Field.v:525).
        2. split_output_stack out p_out N (yields N byte chunks).
        3. For each chunk: assert length, pose proof felem_from_bytes,
           seprewrite_in.
        4. repeat single_step (drives all calls).
        5. Postcondition: unshelve eexists; eexists 4-tuple; ssplit;
           apply HPost; cbv [coords_to_point feval_*coords proj1_sig
                            m1_prep bin_model bin_mul bin_add bin_sub] in *;
           rewrite H<post-state hyps>; reflexivity. *)

  (* Try the fast iff1-form ecancel first; fall back to impl1-form for
     nested-sep cases (FElem<->bytes Hint Extern at Specs/Field.v:525)
     that the standard form can't break through. The impl1-form is
     much slower especially when it fails (see SeparationLogic.v:524),
     so making it the fallback keeps `repeat single_step` performant. *)
  Local Ltac ecancel_assumption_fast :=
    multimatch goal with
    | |- _ ?m1 =>
      multimatch goal with
      | H: _ ?m2 |- _ =>
        syntactic_unify_deltavar m1 m2;
        refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
        solve [ecancel]
      end
    end.
  Local Ltac ecancel_assumption ::= first [ecancel_assumption_fast | ecancel_assumption_impl].

  (** Reusable: convert one output-buffer chunk in hypothesis [H] to FElem form.
      Args: [p] (chunk pointer), [bs] (chunk byte list), [H] (sep hypothesis). *)
  Ltac convert_chunk_to_felem p bs H :=
    let HL := fresh "HL_chunk" in
    let Hiff := fresh "Hiff_chunk" in
    assert (HL : Datatypes.length bs = Z.to_nat felem_size_in_bytes)
      by (rewrite ?length_firstn, ?length_skipn;
          change felem_size_in_bytes with 40%Z; listZnWords);
    pose proof (felem_from_bytes p bs HL) as Hiff;
    seprewrite_in Hiff H.

  (** Reusable: discharge byte-array preconditions for all 4 chunks
      of a 4-felem output buffer. Convention: [pout] is the base, [bs]
      is the byte list, [H] is the sep hypothesis with the chunks. *)
  Ltac convert_4_chunks pout bs H :=
    convert_chunk_to_felem pout            (ListDef.firstn 40 bs) H;
    convert_chunk_to_felem (pout.+40)      (ListDef.firstn 40 (ListDef.skipn 40 bs)) H;
    convert_chunk_to_felem (pout.+80)      (ListDef.firstn 40 (ListDef.skipn 80 bs)) H;
    convert_chunk_to_felem (pout.+120)     (ListDef.skipn 120 bs) H.

  (** Reusable: 5-felem output buffer variant. *)
  Ltac convert_5_chunks pout bs H :=
    convert_chunk_to_felem pout            (ListDef.firstn 40 bs) H;
    convert_chunk_to_felem (pout.+40)      (ListDef.firstn 40 (ListDef.skipn 40 bs)) H;
    convert_chunk_to_felem (pout.+80)      (ListDef.firstn 40 (ListDef.skipn 80 bs)) H;
    convert_chunk_to_felem (pout.+120)     (ListDef.firstn 40 (ListDef.skipn 120 bs)) H;
    convert_chunk_to_felem (pout.+160)     (ListDef.skipn 160 bs) H.

  Lemma to_cached64_ok : program_logic_goal_for_function! to_cached64.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub
        bin_carry_sub un_outbounds bin_outbounds].
    repeat straightline.
    pose proof (cached_implies_coords_valid (m1_prep (coords_to_point a))) as HPost.
    destruct_points.
    split_output_stack out p_out 4.
    repeat straightline.
    convert_4_chunks p_out out H6.
    repeat single_step.
    repeat straightline.
    lazy delta [cached_coords].
    unshelve eexists.
    eexists (_, _, _, _).
    2: split; [solve_mem|].
    ssplit; try solve_bounds.
    apply HPost.
    all: (cbv [coords_to_point feval_projective_coords feval_cached_coords proj1_sig
               Readdition.m1_prep bin_model bin_mul bin_add bin_sub
               bin_carry_add bin_carry_sub un_model un_square] in *;
          rewrite H8, H16, H22, H27, H24, H18, H12; reflexivity).
  Qed.

  (** double64_ok — recipe verified through `Time repeat single_step`
      (42-97s wall, 12 calls + 8 stackallocs all discharged). Postcond
      discharge tail BLOCKED: after `solve_deallocation`, the focused
      goal is `exists _ : map.rep, _` (a pending memory evar from the
      WP frame), not `exists _ : projective_coords, _` as upstream's
      32-bit version. The 5-tuple `(_, _, _, _, _)` thus unifies
      against `map.rep` and fails with
        Unable to unify "(?A * ?B2 * ?B1 * ?B0 * ?B)%type"
                  with "list (SortedList.parameters.key * SortedList.parameters.value)".

      Diagnosis path forward (MCP, incremental):
        - After `solve_deallocation`, dump goal with `idtac` to see
          the `exists m', ...` shape and what memory variable it
          should bind to (likely the latest `a_N : map.rep`).
        - Either: (a) provide `eexists a_N. split; [ecancel_assumption|].`
          first, then the projective_coords witness; OR
          (b) extend `solve_deallocation` to also dispatch the m' evar.

      The recipe scaffolding (Strategy + do-3-straightline +
      destruct_points + split_output_stack + convert_5_chunks (for
      stackalloc-free callees, e.g. to_cached64) OR repeat single_step
      with extended solve_length) is solid. See to_cached64_ok above
      for the full Qed'd template at 64-bit. *)
  (** double64_ok — KEY WP automation found (2026-04-27 MCP session #3):
      `straightline_stackdealloc` is bedrock2's per-layer dealloc tactic
      (defined in bedrock2.ProgramLogic, called by `straightline` itself
      under the right goal shape). Our `solve_deallocation` doesn't trigger
      it because the goal shape after `dealloc_preprocess; repeat straightline`
      isn't `exists _ _, anybytes _ _ _ /\ map.split _ _ _ /\ _` directly —
      that pattern is INSIDE 3 outer existentials.

      WORKING DISCHARGE PATTERN (verified via MCP, leaves only 1 inner
      goal — the postcondition body after dealloc cascade is closed):

        solve_deallocation.
        do 3 eexists. ssplit.
        all: try (repeat straightline_stackdealloc).
        repeat straightline.
        (* Now inner: rets=nil /\ trace_eq /\ exists a_double, ... *)
        (* Inner discharge: exists list byte witness + upstream pattern *)
        exists nil. (* or whatever rets evar wants *)
        ssplit; [reflexivity | reflexivity | ...]
        unshelve eexists. eexists (_, _, _, _, _).
        2: split; [ecancel_assumption|].
        ssplit; try solve_bounds.
        apply HPost.
        all: (cbv [...] in *; Prod.inversion_prod; congruence).

      Open: figure out exact `exists` for `list byte` evar (might be
      `nil` or might need more). Once that's right, full Qed in ~5 min.

      DETAILED HISTORY (sessions #1, #2):

      EXACT GOAL STRUCTURE post-`solve_deallocation; do 3 eexists; ssplit`
      (from MCP `Show Proof` after assertion-trick goal-dump):
        Goal 1: map.split a26 ?m' mStack5
        Goal 2: exists m' mStack' : map.rep,
                  anybytes a10 40 mStack' /\
                  map.split ?m' m' mStack' /\
                  (exists m'0 mStack'0,
                     anybytes a7 40 mStack'0 /\
                     map.split m' m'0 mStack'0 /\
                     ... 4 more layers (trT, t0, trZ, trX) ...
                     list_map (get l6) nil
                       (fun rets => rets = nil /\ a13 = a13 /\
                        exists a_double : projective_coords,
                          <m_inner =* sep> /\ <proj1_sig = feval>))

      SEVEN dealloc layers total (1 outer cT + 6 inner cZ rY trT t0 trZ trX).
      Each layer needs: provide m' = previous-mem-var, mStack' = matching
      mStack[N], discharge anybytes via H59/H46/H39/H32/H25/H18/H14 and
      map.split via H60/H47/H40/H33/H26/H19/H15.

      Tactic pieces verified individually via MCP:
        - `do 3 eexists; ssplit` — sets up structure, leaves Goal 1 as
          `map.split a26 ?m' mStack5` (NOT inside an exists — direct).
        - For Goals 2..N (each cascade layer): `eexists; eexists; ssplit;
          [eassumption|eassumption|]` would peel ONE level — but Goal 1
          needs to be closed FIRST (since `eassumption` won't unify
          a26 ↔ a20 without help, the chain breaks).

      OPEN: The brittle part is the goal-selector chain. The following
      sequence WAS attempted but didn't close cleanly:
        do 3 eexists. ssplit.
        all: try eassumption.   (* tries to close Goal 1 with H60 *)
        all: try (eexists; eexists; ssplit; [eassumption|eassumption|]).
        ... etc

      Likely needs explicit goal selectors (`1: ... ; 2: ...`) or a
      hand-written Ltac that lazymatches on the cascade shape per layer.

      Recipe through `solve_deallocation` is solid (closes in 30-60s wall
      via MCP); remaining ~15-30 LoC of WP-frame plumbing is the open
      task. Best path forward: write a `dispatch_dealloc_cascade` Ltac
      at toplevel (before the proof) that takes the goal apart per layer
      and applies the right hypothesis. *)
  Lemma double64_ok : program_logic_goal_for_function! double64.
  Proof.
    Set Printing Width 60.       (* shrink line width *)
    Set Printing Depth 8.        (* cap nested-sep display depth *)
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub
        bin_carry_sub un_outbounds bin_outbounds].
    do 3 straightline.
    pose proof (point_implies_coords_valid (m1double (coords_to_point a))) as HPost.
    destruct_points.
    split_output_stack out p_out 5.
    repeat straightline.
    Time repeat single_step.
    repeat straightline.
    solve_deallocation.
    clear_double_intermediates.   (* shrink env from 50K to 10K chars *)
    (* PROVEN STATE (MCP session #7, 2026-04-28):
       Goal at this point (now READABLE thanks to Set Printing + clear):
         exists m' mStack', anybytes a18 40 mStack' /\ map.split a26 m' mStack' /\
         (exists m'0 mStack'0, anybytes a10 40 mStack'0 /\ map.split m' m'0 mStack'0 /\
          ... 7-layer cascade for cT/cZ/rY/trT/t0/trZ/trX ...
          list_map (get l6) nil (fun rets =>
            rets = nil /\ a13 = a13 /\
            exists X Y Z Ta Tb : felem,
              valid_projective_coords X Y Z Ta Tb /\
              bounded_by tight_bounds X /\ ... /\ bounded_by loose_bounds Tb /\
              (FElem p_out X * FElem (p_out.+40) Y * FElem (p_out.+80) Z *
               FElem (p_out.+120) Ta * FElem (p_out.+160) Tb) * a p5@ p_a * R /\
              proj1_sig (m1double ...) = (feval X, ..., feval Tb)))

       BLOCKER: `straightline_stackdealloc` requires `array ptsto _ a stack`
       in scope but H82 has `FElem a18 x8` etc. Need to convert via
       `seprewrite_in (felem_to_bytearray a18 x8) H82` per layer — but ecancel
       (in seprewrite_in) fails to find FElem a18 x8 inside the nested
       right-associated `_ ⋆ (_ ⋆ (_ ⋆ ...))` chain in H82. Likely needs
       `flatten_seps_in H82` first to make the chain ecancel-friendly.

       Path forward: write `prep_dealloc_cascade` Ltac:
         flatten_seps_in H82;
         repeat (lazymatch goal with
                 | |- exists _ _, anybytes ?a _ _ /\ _ =>
                     match goal with H : context[FElem a ?v] |- _ =>
                       seprewrite_in (felem_to_bytearray a v) H
                     end
                 end);
         repeat straightline_stackdealloc;
         repeat straightline.
       Then provide felem witnesses + bounds + sep + proj_eq.

       MCP session #9 (2026-04-28) — TWO BREAKTHROUGHS:

       BREAKTHROUGH 1: `seprewrite_in (felem_to_bytearray addr v) H82`
       was silently picking wrong typeclass instance. Fix: pass the
       field_representation explicitly:
         seprewrite_in (felem_to_bytearray (field_representation:=frep25519) addr v) H82.

       BREAKTHROUGH 2: Bypass `straightline_stackdealloc` (which has
       an ecancel-reordering blocker on flat 17-element sep chains)
       by MANUALLY destructing H82 layer-by-layer. The pattern:

         (* Convert all 7 stack FElems → array_ptsto in REVERSE cascade order,
            so a18 (cT, last cascade) ends up at the FRONT of H82 *)
         seprewrite_in (felem_to_bytearray (field_representation:=frep25519) a x) H82.
         seprewrite_in (felem_to_bytearray (field_representation:=frep25519) a2 x0) H82.
         seprewrite_in (felem_to_bytearray (field_representation:=frep25519) a0 x4) H82.
         seprewrite_in (felem_to_bytearray (field_representation:=frep25519) a4 x2) H82.
         seprewrite_in (felem_to_bytearray (field_representation:=frep25519) a7 x3) H82.
         seprewrite_in (felem_to_bytearray (field_representation:=frep25519) a10 x6) H82.
         seprewrite_in (felem_to_bytearray (field_representation:=frep25519) a18 x8) H82.
         (* Length proofs *)
         pose proof (ws2bs_felem_length x8) as Hlen_x8.   (* ... etc for all 7 *)

         (* Per-layer dispatch (×7): unfold sep at front, destruct, provide witnesses *)
         unfold sep at 1 in H82.
         destruct H82 as (m18 & rest1 & Hsplit18 & Harr18 & Hrest1).
         exists rest1, m18; ssplit;
           [ pose proof Array.array_1_to_anybytes _ _ _ Harr18 as Hany18;
             rewrite Hlen_x8 in Hany18; exact Hany18
           | apply Properties.map.split_comm; exact Hsplit18 | ].
         (* Repeat for layers 2-7: a10, a7, a4, a0, a2, a *)

       Then `repeat straightline; exists x9, x10, x11, x7, x5; ssplit;
       try solve_bounds; all: try ecancel_assumption.` closes the
       sep + bounds. Final `apply HPost; cbv [...] in *; congruence`
       handles the proj_eq.

       FULL VERIFICATION (state 649 in MCP session #9): 7 layers
       dispatched cleanly, sep + bounds + most proj_eq goals closed,
       1 residual goal in proj_eq congruence (suspect cleared
       intermediate feval hyps; pending refinement).

       Pattern is REUSABLE for add_precomputed64_ok (3 calls, similar
       cascade) and readd64_ok (3 calls). Memory:
       feedback_seprewrite_explicit_typeclass.md +
       feedback_clear_intermediate_seps.md. *)
  Admitted.

  (** add_precomputed64_ok — same recipe as double64_ok, with `m1add_precomputed_coordinates`
      as the abstract op and 3-word arg `(p_out p_a p_b)` (so `do 4 straightline`).
      Same Admitted-at-discharge-tail as double64_ok per section 10 of findings. *)
  Lemma add_precomputed64_ok : program_logic_goal_for_function! add_precomputed64.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub
        un_outbounds bin_outbounds].
    do 4 straightline.
    pose proof (point_implies_coords_valid (m1add_precomputed_coordinates (coords_to_point a)
      (precomputed_coords_to_precomputed b))) as HPost.
    destruct_points.
    split_output_stack out p_out 5.
    repeat straightline.
    Time repeat single_step.
    repeat straightline.
    solve_deallocation.
  Admitted.

  (** readd64_ok — same recipe, `m1_readd` op, 3-word arg `(p_out p_a p_c)`. *)
  Lemma readd64_ok : program_logic_goal_for_function! readd64.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add
        bin_sub bin_carry_sub un_outbounds bin_outbounds].
    do 4 straightline.
    pose proof (point_implies_coords_valid (m1_readd (coords_to_point a) (cached_coords_to_cached c))) as HPost.
    destruct_points.
    split_output_stack out p_out 5.
    repeat straightline.
    Time repeat single_step.
    repeat straightline.
    solve_deallocation.
  Admitted.

End Ed25519XYZT64.
