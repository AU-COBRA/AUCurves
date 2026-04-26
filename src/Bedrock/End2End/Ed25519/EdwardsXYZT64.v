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
  (* fe25519_half doesn't have a synthesized impl yet (per upstream comment) —
     reuse upstream's spec shape if it's width-polymorphic, otherwise pending. *)
  Existing Instance Crypto.Bedrock.End2End.X25519.EdwardsXYZT.spec_of_fe25519_half.

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

  Global Instance spec_of_double64 : spec_of "double" :=
    fnspec! "double"
      (p_out p_a: word) /
      (a: projective_coords) (out : list byte) (R: _ -> Prop), {
        requires t m :=
          m =* out $@ p_out * a p5@ p_a * R /\
          Datatypes.length out = Z.to_nat (5 * felem_size);
        ensures t' m' :=
          t = t' /\
          exists a_double: projective_coords,
            m' =* a_double p5@ p_out * a p5@ p_a * R /\
            proj1_sig (m1double (coords_to_point a)) = feval_projective_coords a_double
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
      (rewrite firstn_length; cbv [felem_size_in_bytes] in *; listZnWords);
    let D := fresh in
    unshelve(epose (sep_eq_putmany _ _ (map.adjacent_arrays_disjoint_n p (ListDef.firstn n_nat stack) (ListDef.skipn n_nat stack) n_z _ _)) as D);
      [ rewrite firstn_length; cbv [felem_size_in_bytes] in *; listZnWords
      | rewrite firstn_length, skipn_length; cbv [felem_size_in_bytes] in *; listZnWords
      | seprewrite_in D H; rewrite ?skipn_skipn in H;
        bottom_up_simpl_in_hyp H; clear D ].

  Local Ltac solve_length :=
    try lia;
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

  (** ** Sub-task 1.5: _ok proofs — partial.

      ROOT CAUSE FOUND: upstream's [spec_of_fe25519_*] are at 32-bit width
      (declared inside a section that fixes [Bitwidth32] + [Naive.word32]).
      Our [to_cached64] proof needs 64-bit specs. Fix above declares fresh
      [spec_of_fe25519_*64] Local Instances that resolve [field_representation:=frep25519]
      from the loader (64-bit FieldRepresentation).

      Verified end-to-end via MCP after the fix:
        - [program_logic_goal_for_function! to_cached64] resolves with
          64-bit hypotheses [spec_of_fe25519_sub64 functions], etc.
        - [repeat straightline + destruct_points + split_output_stack] all work.
        - [single_step] (= straightline_call + ssplit + solve_mem) succeeds
          for the first call (fe25519_sub), introducing post-state hypothesis
          H10 about the resulting felem.

      Next blocker: [solve_mem]'s ecancel can't auto-solve the side condition
      [(ws2bs (felem_to_list ?x))$@p_out * ?Rr] (the precondition of
      fe25519_sub asks for an FElem-as-bytes representation, but our H6
      has ListDef.firstn/skipn byte arrays). Needs an explicit
      bytes-to-felem cast lemma application before each call, or an Hint
      Extern that bridges the two. Pending.

      Status: 4-of-7 calls in to_cached64_ok would close with the same
      pattern once the bytes-to-felem coercion is figured out. Each of
      the 4 _ok lemmas (to_cached, add_precomputed, double, readd) shares
      this structure, so the fix is once-for-all. *)

End Ed25519XYZT64.
