(** * OracleLeafTemplate — parametric oracle-leaf-producer templates.
 *
 *  Extracts the recurring producer pattern from
 *  [Fe25519BoundLeafProducers.v].  Each producer in that file (one per
 *  [REdCall] leaf in [fe25519_invert_body]) constructs an
 *  [Hexec_b (REdCall fname dest [args]) rs1 rs2] inhabitant by:
 *
 *    1. Choosing [rs2 := set_encoded rs1 dest.(loc_var) target] —
 *       i.e. a single [rs_set_tower_ed] overwriting [dest] with the
 *       abstract 5-limb encoding of the target field-element.
 *    2. Applying [rexec_call] with [callee_post_bound] as the oracle
 *       witness, then collapsing the oracle's universally-quantified
 *       [x'] back to the caller's known [x] via
 *       [Fp25519_holds_bound_det].
 *
 *  The only per-leaf variation is:
 *    - Source-argument arity (1 for [sqr]/[copy], 2 for [mul]).
 *    - The algebraic post-spec (target field-element as a function
 *      of the source inputs).
 *
 *  We therefore expose TWO templates — [oracle_unop_producer] and
 *  [oracle_binop_producer] — parameterised by the function name and
 *  the algebraic spec.  Going through a single list-typed signature
 *  would force the consumer to do its own arity case-split (because
 *  [callee_post_bound] itself dispatches on [args] shape), defeating
 *  the boilerplate elimination.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBody.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBoundInstantiation.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Concrete radix-2^51 encoder + two named lemmas                *)
(* ================================================================ *)

(** [encode_target x] : concrete 5-limb radix-2^51 representation of
    [x : F p].  Splits [F.to_Z x] into five 51-bit (or 51-bit-or-fewer)
    chunks by repeated [mod 2^51] / [div 2^51].  This trivially fits
    within fiat-crypto's loose-bounds shape (per-limb < 2^54) and the
    positional evaluation reconstructs [F.to_Z x] exactly. *)
Definition encode_target (x : F p) : list Z :=
  let z := F.to_Z x in
  [z mod 2^51;
   (z / 2^51) mod 2^51;
   (z / 2^102) mod 2^51;
   (z / 2^153) mod 2^51;
   z / 2^204].

Lemma encode_target_length :
  forall (x : F p), length (encode_target x) = 5%nat.
Proof. intros x. unfold encode_target. reflexivity. Qed.

(** Helper: [Positional.eval (weight 51 1) 5 (encode_target x)] reduces
    to a [Z] arithmetic identity, which holds because [F.to_Z x < 2^255]. *)
Lemma encode_target_eval :
  forall (x : F p),
    Positional.eval (ModOps.weight 51 1) 5%nat (encode_target x) = F.to_Z x.
Proof.
  intros x.
  pose proof (F.to_Z_range x) as Hrange.
  specialize (Hrange ltac:(lia)).
  cbv [encode_target].
  rewrite !Positional.eval_cons by reflexivity.
  rewrite Positional.eval_nil.
  cbv [ModOps.weight].
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  set (z := F.to_Z x) in *.
  assert (Hp : (Z.pos p = 2^255 - 19)) by reflexivity.
  rewrite Hp in Hrange.
  (* Decompose z via repeated div_mod. *)
  pose proof (Z.div_mod z (2^51) ltac:(lia)) as H1.
  pose proof (Z.div_mod (z/2^51) (2^51) ltac:(lia)) as H2.
  pose proof (Z.div_mod (z/2^51/2^51) (2^51) ltac:(lia)) as H3.
  pose proof (Z.div_mod (z/2^51/2^51/2^51) (2^51) ltac:(lia)) as H4.
  (* Combine div-div = div-product. *)
  assert (Heq1 : z/2^102 = z/2^51/2^51).
  { rewrite !Z.div_div by lia. f_equal; lia. }
  assert (Heq2 : z/2^153 = z/2^51/2^51/2^51).
  { rewrite !Z.div_div by lia. f_equal; lia. }
  assert (Heq3 : z/2^204 = z/2^51/2^51/2^51/2^51).
  { rewrite !Z.div_div by lia. f_equal; lia. }
  rewrite Heq1, Heq2, Heq3.
  change (2 ^ (- (- (51 * 0) / 1))) with 1.
  change (2 ^ (- (- (51 * 1) / 1))) with (2^51).
  change (2 ^ (- (- (51 * 2) / 1))) with (2^51 * 2^51).
  change (2 ^ (- (- (51 * 3) / 1))) with (2^51 * 2^51 * 2^51).
  change (2 ^ (- (- (51 * 4) / 1))) with (2^51 * 2^51 * 2^51 * 2^51).
  nia.
Qed.

Lemma encode_target_decodes :
  forall (x : F p), feval_bound (encode_target x) = x.
Proof.
  intros x. unfold feval_bound.
  rewrite encode_target_eval.
  apply F.of_Z_to_Z.
Qed.

Lemma encode_target_bounded :
  forall (x : F p), limbs_bounded (encode_target x).
Proof.
  intros x.
  pose proof (F.to_Z_range x) as Hrange.
  cbv [limbs_bounded encode_target].
  set (z := F.to_Z x) in *.
  repeat apply Forall_cons; try apply Forall_nil; cbv [limb_loose_bound].
  - split.
    + apply Z.mod_pos_bound; lia.
    + assert (z mod 2^51 < 2^51) by (apply Z.mod_pos_bound; lia).
      assert (2^51 < 2^54) by lia. lia.
  - split.
    + apply Z.mod_pos_bound; lia.
    + assert ((z/2^51) mod 2^51 < 2^51) by (apply Z.mod_pos_bound; lia).
      assert (2^51 < 2^54) by lia. lia.
  - split.
    + apply Z.mod_pos_bound; lia.
    + assert ((z/2^102) mod 2^51 < 2^51) by (apply Z.mod_pos_bound; lia).
      assert (2^51 < 2^54) by lia. lia.
  - split.
    + apply Z.mod_pos_bound; lia.
    + assert ((z/2^153) mod 2^51 < 2^51) by (apply Z.mod_pos_bound; lia).
      assert (2^51 < 2^54) by lia. lia.
  - split.
    + apply Z.div_pos; lia.
    + (* z < 2^255 - 19 < 2^255; z/2^204 < 2^255/2^204 = 2^51 < 2^54 *)
      assert (Hzlt : z < 2^255) by lia.
      apply Z.div_lt_upper_bound; [lia|].
      assert (2^54 * 2^204 = 2^258) by reflexivity.
      lia.
Qed.

(* ================================================================ *)
(* §2. State helpers (set_encoded)                                   *)
(* ================================================================ *)

(** [set_encoded rs dest target] : the state obtained from [rs] by
    overwriting [dest]'s tower slot with [encode_target target]. *)
Definition set_encoded (rs : rust_state_ed) (dest : String.string)
    (target : F p) : rust_state_ed :=
  rs_set_tower_ed rs dest
    (exist_tval_ed TFp25519 (VFp25519 (encode_target target))).

Lemma rs_get_set_encoded_eq :
  forall rs dest target,
    rs_get_tower_ed (set_encoded rs dest target) dest =
    Some (exist_tval_ed TFp25519 (VFp25519 (encode_target target))).
Proof.
  intros rs dest target. unfold set_encoded.
  unfold rs_get_tower_ed, rs_set_tower_ed; cbn.
  induction (rs_tower_ed rs) as [|[k v] rest IH]; cbn.
  - rewrite String.eqb_refl. reflexivity.
  - destruct (String.eqb k dest) eqn:Hk; cbn.
    + apply String.eqb_eq in Hk; subst.
      rewrite String.eqb_refl. reflexivity.
    + apply String.eqb_neq in Hk.
      destruct (String.eqb dest k) eqn:Hxk.
      * apply String.eqb_eq in Hxk; congruence.
      * exact IH.
Qed.

Lemma rs_get_set_encoded_other :
  forall rs dest y target,
    y <> dest ->
    rs_get_tower_ed (set_encoded rs dest target) y =
    rs_get_tower_ed rs y.
Proof.
  intros rs dest y target Hne. unfold set_encoded.
  apply rs_get_set_tower_other_bound.
  intros Heq; apply Hne; symmetry; exact Heq.
Qed.

Lemma Fp25519_holds_bound_set_encoded :
  forall rs dest target,
    Fp25519_holds_bound (set_encoded rs dest target) dest target.
Proof.
  intros rs dest target.
  exists (encode_target target).
  split; [|split; [|split]].
  - apply rs_get_set_encoded_eq.
  - apply encode_target_length.
  - apply encode_target_bounded.
  - apply encode_target_decodes.
Qed.

Lemma Fp25519_holds_bound_set_encoded_other :
  forall rs dest target y v,
    y <> dest ->
    Fp25519_holds_bound rs y v ->
    Fp25519_holds_bound (set_encoded rs dest target) y v.
Proof.
  intros rs dest target y v Hne Hold.
  unfold set_encoded.
  apply let_zero_preserves_holds_bound; assumption.
Qed.

(** [Fp25519_holds_bound] determines its field-element argument
    uniquely (given the same slot and state). *)
Lemma Fp25519_holds_bound_det :
  forall rs v x1 x2,
    Fp25519_holds_bound rs v x1 ->
    Fp25519_holds_bound rs v x2 ->
    x1 = x2.
Proof.
  intros rs v x1 x2 [l1 [Hg1 [_ [_ Hf1]]]] [l2 [Hg2 [_ [_ Hf2]]]].
  rewrite Hg1 in Hg2. injection Hg2 as Hleq. subst l2.
  rewrite <- Hf1, <- Hf2. reflexivity.
Qed.

(* ================================================================ *)
(* §3. Parametric templates                                          *)
(* ================================================================ *)

Local Notation Hexec_b :=
  (rust_exec_ed callee_post_bound callee_post_n_bound function_table_bound).

(** ** [oracle_unop_producer]: template for 1-source leaves.
 *
 *  Discharges the [REdCall fname dest [src]] case of
 *  [callee_post_bound] for any [fname] whose oracle branch in
 *  [callee_post_bound] has the unary shape:
 *
 *    loc_type dst = TFp25519 ->
 *    loc_type src = TFp25519 ->
 *    loc_var dst <> loc_var src ->
 *    forall (x : F p),
 *      Fp25519_holds_bound rs1 (loc_var src) x ->
 *      Fp25519_holds_bound rs2 (loc_var dst) (algebraic_spec x) /\
 *      (frame ...)
 *
 *  The hypothesis [Hbranch] is exactly that oracle-branch shape,
 *  abstracted over the post.  In practice the caller obtains it by
 *  [cbn [callee_post_bound]] reducing the dispatch on [fname].
 *)
Section OracleLeafTemplate.

  (** Common framing condition: every other slot is preserved. *)
  Definition frame_pred (dest : String.string) (rs1 rs2 : rust_state_ed) : Prop :=
    forall (y : String.string) (v : F p),
      y <> dest ->
      Fp25519_holds_bound rs1 y v ->
      Fp25519_holds_bound rs2 y v.

  (** ** Unary leaves (sqr / copy / any 1-source primitive).
   *
   *  Hypothesis [Hbranch] : the [cbn]-reduced [callee_post_bound]
   *  branch for the unary shape, parameterised by the algebraic post
   *  [AlgebraicSpec : F p -> F p].
   *)
  Lemma oracle_unop_producer
        (fname : String.string)
        (AlgebraicSpec : F p -> F p)
        (Hbranch :
           forall (args : list located_ed) (dst : located_ed)
                  (rs1 rs2 : rust_state_ed) (src : located_ed),
             args = [src] ->
             (loc_type dst = TFp25519 ->
              loc_type src = TFp25519 ->
              loc_var dst <> loc_var src ->
              forall (x : F p),
                Fp25519_holds_bound rs1 (loc_var src) x ->
                Fp25519_holds_bound rs2 (loc_var dst) (AlgebraicSpec x) /\
                frame_pred (loc_var dst) rs1 rs2) ->
             callee_post_bound fname args dst rs1 rs2)
    : forall (rs1 : rust_state_ed) (dest src : located_ed) (x : F p),
        dest.(loc_type) = TFp25519 ->
        src.(loc_type) = TFp25519 ->
        dest.(loc_var) <> src.(loc_var) ->
        Fp25519_holds_bound rs1 src.(loc_var) x ->
        exists rs2 : rust_state_ed,
          Hexec_b (REdCall fname dest [src]) rs1 rs2 /\
          Fp25519_holds_bound rs2 dest.(loc_var) (AlgebraicSpec x) /\
          frame_pred dest.(loc_var) rs1 rs2.
  Proof.
    intros rs1 dest src x Hdt Hst Hne Hsrc.
    exists (set_encoded rs1 dest.(loc_var) (AlgebraicSpec x)).
    repeat split.
    - eapply rexec_call.
      eapply Hbranch with (src := src); [reflexivity|].
      intros Hdt' Hst' Hne' x' Hsrc'.
      pose proof (Fp25519_holds_bound_det _ _ _ _ Hsrc Hsrc') as Hxeq.
      subst x'.
      split.
      + apply Fp25519_holds_bound_set_encoded.
      + intros y v Hy Hyv.
        apply Fp25519_holds_bound_set_encoded_other; assumption.
    - apply Fp25519_holds_bound_set_encoded.
    - intros y v Hy Hyv.
      apply Fp25519_holds_bound_set_encoded_other; assumption.
  Qed.

  (** ** Binary leaves (mul / any 2-source primitive). *)
  Lemma oracle_binop_producer
        (fname : String.string)
        (AlgebraicSpec : F p -> F p -> F p)
        (Hbranch :
           forall (args : list located_ed) (dst : located_ed)
                  (rs1 rs2 : rust_state_ed) (a b : located_ed),
             args = [a; b] ->
             (loc_type dst = TFp25519 ->
              loc_type a = TFp25519 ->
              loc_type b = TFp25519 ->
              loc_var dst <> loc_var a ->
              loc_var dst <> loc_var b ->
              forall (xa xb : F p),
                Fp25519_holds_bound rs1 (loc_var a) xa ->
                Fp25519_holds_bound rs1 (loc_var b) xb ->
                Fp25519_holds_bound rs2 (loc_var dst) (AlgebraicSpec xa xb) /\
                frame_pred (loc_var dst) rs1 rs2) ->
             callee_post_bound fname args dst rs1 rs2)
    : forall (rs1 : rust_state_ed) (dest a b : located_ed) (xa xb : F p),
        dest.(loc_type) = TFp25519 ->
        a.(loc_type) = TFp25519 ->
        b.(loc_type) = TFp25519 ->
        dest.(loc_var) <> a.(loc_var) ->
        dest.(loc_var) <> b.(loc_var) ->
        Fp25519_holds_bound rs1 a.(loc_var) xa ->
        Fp25519_holds_bound rs1 b.(loc_var) xb ->
        exists rs2 : rust_state_ed,
          Hexec_b (REdCall fname dest [a; b]) rs1 rs2 /\
          Fp25519_holds_bound rs2 dest.(loc_var) (AlgebraicSpec xa xb) /\
          frame_pred dest.(loc_var) rs1 rs2.
  Proof.
    intros rs1 dest a b xa xb Hdt Hat Hbt Hne_a Hne_b Hxa Hxb.
    exists (set_encoded rs1 dest.(loc_var) (AlgebraicSpec xa xb)).
    repeat split.
    - eapply rexec_call.
      eapply Hbranch with (a := a) (b := b); [reflexivity|].
      intros Hdt' Hat' Hbt' Hne_a' Hne_b' xa' xb' Hxa' Hxb'.
      pose proof (Fp25519_holds_bound_det _ _ _ _ Hxa Hxa') as Hxa_eq.
      pose proof (Fp25519_holds_bound_det _ _ _ _ Hxb Hxb') as Hxb_eq.
      subst xa' xb'.
      split.
      + apply Fp25519_holds_bound_set_encoded.
      + intros y v Hy Hyv.
        apply Fp25519_holds_bound_set_encoded_other; assumption.
    - apply Fp25519_holds_bound_set_encoded.
    - intros y v Hy Hyv.
      apply Fp25519_holds_bound_set_encoded_other; assumption.
  Qed.

End OracleLeafTemplate.
