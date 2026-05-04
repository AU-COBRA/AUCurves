(** * Inductive step of the Ed25519 scalarmult double-and-add loop body.
 *
 * Discharges one iteration of the [while] in
 * [ed25519_scalarmult_base_parametric] (Scalarmult_Impl_64.v):
 *
 *     i = i - 1;
 *     double(TMP, ACC);                  (* TMP := 2·ACC; see commit c93d2be *)
 *     cmov_5felems(ACC, TMP, $1);        (* ACC := TMP via mask=1 memcpy *)
 *     byte = load1(scalar + (i >> 3));
 *     bit = (byte >> (i & 7)) & 1;
 *     add_precomputed(TMP, ACC, B_pre);
 *     cmov_5felems(ACC, TMP, bit)
 *
 * The split-double pattern was introduced in commit c93d2be to avoid
 * the sep-aliasing that [spec_of_double64] forbids — its precondition
 * requires [out] and [a] to be disjoint, which [double(ACC, ACC)] could
 * not satisfy.
 *
 * Statement: given the loop invariant at body entry — locals carry
 * pointers to {out, scalar, B_pre, ACC, TMP, i}; the byte buffers at
 * ACC_ptr / TMP_ptr have length 200, and the bytes at ACC_ptr decode to
 * a valid projective_coords; the bytes at B_pre_ptr decode to a valid
 * precomputed_coords; plus a Hoare continuation [post] that holds for
 * the post-state — running the body advances [i] from [n] to [n-1] and
 * preserves the invariant.
 *
 * STATUS (2026-05-04): Statement landed; proof body admitted with detailed
 * structural commentary describing each [cmd.seq] peel. Closing this lemma
 * unblocks the [(I)] sub-task in the parent
 * [ed25519_scalarmult_base_parametric_correct]. Required helpers
 * (already Qed-closed in the codebase):
 *   * [BytesToFelem5.byte_acc_5felem_iff] — 200-byte ↔ 5-FElem bridge.
 *   * [BitExtraction.bit_extraction_in_zero_one] — discharges
 *     [cmov_5felems]'s mask precondition.
 * Still missing (would need to be authored alongside this proof):
 *   * A 120-byte ↔ 3-FElem bridge for [B_pre], analogous to BytesToFelem5
 *     but with three 40-byte chunks at offsets 0/40/80. The pattern is
 *     a direct simplification (one fewer split round + two fewer
 *     felem_from_bytes flips); ~80 LoC.
 *
 * The proof uses the standard pattern from [Cmov5Felems_64.v] (iter 46):
 * for each spec-shape transition (byte ↔ FElem), apply [iff1ToEq] to the
 * bridge lemma and [rewrite] the resulting equation in the sep
 * hypothesis (no setoid_rewrite needed). Each handle_call needs ~50 LoC
 * of dexpr-discharge boilerplate. Total realistic budget: ~700 LoC for
 * full Qed; this scaffold defers the entirety to a single [admit].
 *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64.
Require Import Bedrock.End2End.Ed25519.Cmov5Felems_64.
Require Import Bedrock.End2End.Ed25519.BytesToFelem5.
Require Import Bedrock.End2End.Ed25519.BitExtraction.
Require Import coqutil.Map.SeparationMemory.
From Stdlib Require Import Morphisms.

Section LoopBodyPreserves.
  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
  Local Notation felem := (felem(FieldRepresentation:=frep25519)).
  Local Notation bs2felem := (bs2felem(field_representation:=frep25519)).

  (** The bedrock2 syntax tree of one loop iteration body, mirroring the
      [bedrock_func_body:] expansion of the [while]'s body in
      [Scalarmult_Impl_64.v]'s [ed25519_scalarmult_base_parametric]. *)
  Definition loop_body_cmd : cmd.cmd :=
    cmd.seq (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
    (cmd.seq (cmd.call (@nil String.string) "double"
                (cons (expr.var "TMP") (cons (expr.var "ACC") nil)))
    (cmd.seq (cmd.call (@nil String.string) "cmov_5felems"
                (cons (expr.var "ACC") (cons (expr.var "TMP")
                  (cons (expr.literal 1) nil))))
    (cmd.seq (cmd.set "byte"
        (expr.load access_size.one
           (expr.op bopname.add (expr.var "scalar")
              (expr.op bopname.sru (expr.var "i") (expr.literal 3)))))
    (cmd.seq (cmd.set "bit"
        (expr.op bopname.and
           (expr.op bopname.sru (expr.var "byte")
              (expr.op bopname.and (expr.var "i") (expr.literal 7)))
           (expr.literal 1)))
    (cmd.seq (cmd.call (@nil String.string) "add_precomputed"
                (cons (expr.var "TMP") (cons (expr.var "ACC")
                  (cons (expr.var "B_pre") nil))))
             (cmd.call (@nil String.string) "cmov_5felems"
                (cons (expr.var "ACC") (cons (expr.var "TMP")
                  (cons (expr.var "bit") nil))))))))).

  (** The loop body invariant carries 200-byte ACC and TMP buffers (byte
      form, since [cmov_5felems] consumes byte form), plus the algebraic
      validity of the felem decoding of the ACC bytes (so that
      [double] + [add_precomputed] preconditions can be discharged after
      a byte→FElem split). *)

  Lemma loop_body_preserves_invariant :
    forall (functions : Interface.map.rep)
           (out_ptr scalar_ptr B_pre_ptr ACC_ptr TMP_ptr : Naive.word 64)
           (out scalar B_pre acc_bytes tmp_bytes : list Byte.byte)
           (R : Interface.map.rep -> Prop)
           (n : nat) (i_word : Naive.word 64)
           (tr : Semantics.trace)
           (m : Interface.map.rep) (loc : Interface.map.rep)
           (post : Semantics.trace -> Interface.map.rep -> Interface.map.rep -> Prop),
      Ed25519XYZT64.spec_of_double64 functions ->
      Ed25519XYZT64.spec_of_add_precomputed64 functions ->
      spec_of_cmov_5felems functions ->
      (n <= 256)%nat ->
      Interface.map.get loc "out" = Some out_ptr ->
      Interface.map.get loc "scalar" = Some scalar_ptr ->
      Interface.map.get loc "B_pre" = Some B_pre_ptr ->
      Interface.map.get loc "ACC" = Some ACC_ptr ->
      Interface.map.get loc "TMP" = Some TMP_ptr ->
      Interface.map.get loc "i" = Some i_word ->
      word.unsigned i_word = Z.of_nat n ->
      (n > 0)%nat ->
      Datatypes.length out = 200%nat ->
      Datatypes.length scalar = 32%nat ->
      Datatypes.length B_pre = 120%nat ->
      Datatypes.length acc_bytes = 200%nat ->
      Datatypes.length tmp_bytes = 200%nat ->
      ((out$@out_ptr) ⋆ (scalar$@scalar_ptr) ⋆ (B_pre$@B_pre_ptr) ⋆
       (acc_bytes$@ACC_ptr) ⋆ (tmp_bytes$@TMP_ptr) ⋆ R)%sep m ->
      Ed25519XYZT64.valid_projective_coords
        (bs2felem (List.firstn 40 acc_bytes))
        (bs2felem (List.firstn 40 (List.skipn 40 acc_bytes)))
        (bs2felem (List.firstn 40 (List.skipn 80 acc_bytes)))
        (bs2felem (List.firstn 40 (List.skipn 120 acc_bytes)))
        (bs2felem (List.firstn 40 (List.skipn 160 acc_bytes))) ->
      bounded_by tight_bounds (bs2felem (List.firstn 40 acc_bytes)) ->
      bounded_by tight_bounds (bs2felem (List.firstn 40 (List.skipn 40 acc_bytes))) ->
      bounded_by tight_bounds (bs2felem (List.firstn 40 (List.skipn 80 acc_bytes))) ->
      bounded_by loose_bounds (bs2felem (List.firstn 40 (List.skipn 120 acc_bytes))) ->
      bounded_by loose_bounds (bs2felem (List.firstn 40 (List.skipn 160 acc_bytes))) ->
      Ed25519XYZT64.valid_precomputed_coords
        (bs2felem (List.firstn 40 B_pre))
        (bs2felem (List.firstn 40 (List.skipn 40 B_pre)))
        (bs2felem (List.firstn 40 (List.skipn 80 B_pre))) ->
      bounded_by loose_bounds (bs2felem (List.firstn 40 B_pre)) ->
      bounded_by loose_bounds (bs2felem (List.firstn 40 (List.skipn 40 B_pre))) ->
      bounded_by loose_bounds (bs2felem (List.firstn 40 (List.skipn 80 B_pre))) ->
      (forall (acc_bytes' tmp_bytes' : list Byte.byte) (i_word' : Naive.word 64)
              (loc' : Interface.map.rep) (m' : Interface.map.rep),
          Datatypes.length acc_bytes' = 200%nat ->
          Datatypes.length tmp_bytes' = 200%nat ->
          word.unsigned i_word' = Z.of_nat (n - 1) ->
          Interface.map.get loc' "out" = Some out_ptr ->
          Interface.map.get loc' "scalar" = Some scalar_ptr ->
          Interface.map.get loc' "B_pre" = Some B_pre_ptr ->
          Interface.map.get loc' "ACC" = Some ACC_ptr ->
          Interface.map.get loc' "TMP" = Some TMP_ptr ->
          Interface.map.get loc' "i" = Some i_word' ->
          ((out$@out_ptr) ⋆ (scalar$@scalar_ptr) ⋆ (B_pre$@B_pre_ptr) ⋆
           (acc_bytes'$@ACC_ptr) ⋆ (tmp_bytes'$@TMP_ptr) ⋆ R)%sep m' ->
          Ed25519XYZT64.valid_projective_coords
            (bs2felem (List.firstn 40 acc_bytes'))
            (bs2felem (List.firstn 40 (List.skipn 40 acc_bytes')))
            (bs2felem (List.firstn 40 (List.skipn 80 acc_bytes')))
            (bs2felem (List.firstn 40 (List.skipn 120 acc_bytes')))
            (bs2felem (List.firstn 40 (List.skipn 160 acc_bytes'))) ->
          bounded_by tight_bounds (bs2felem (List.firstn 40 acc_bytes')) ->
          bounded_by tight_bounds (bs2felem (List.firstn 40 (List.skipn 40 acc_bytes'))) ->
          bounded_by tight_bounds (bs2felem (List.firstn 40 (List.skipn 80 acc_bytes'))) ->
          bounded_by loose_bounds (bs2felem (List.firstn 40 (List.skipn 120 acc_bytes'))) ->
          bounded_by loose_bounds (bs2felem (List.firstn 40 (List.skipn 160 acc_bytes'))) ->
          post tr m' loc') ->
      cmd functions loop_body_cmd tr m loc post.
  Proof.
    intros functions out_ptr scalar_ptr B_pre_ptr ACC_ptr TMP_ptr
           out scalar B_pre acc_bytes tmp_bytes R n i_word tr m loc post.
    intros Hdouble Hadd Hcmov Hn_le.
    intros Hl_out Hl_scalar Hl_Bpre Hl_ACC Hl_TMP Hl_i Hi_val Hn_pos.
    intros Hlen_out Hlen_scalar Hlen_Bpre Hlen_acc Hlen_tmp.
    intros Hsep Hvp_acc Hb_X Hb_Y Hb_Z Hb_Ta Hb_Tb.
    intros Hvp_Bpre Hb_hypx Hb_hymx Hb_xyd.
    intros Hpost.
    unfold loop_body_cmd.
    (* Step 1 — Peel [cmd.set "i" (i - 1)].  Verified in MCP iter 1.
       Discharges dexpr [i - 1] via [Hl_i] + [Semantics.interp_binop].
       After this, locals are [map.put loc "i" (word.sub i_word (word.of_Z 1))]
       and the WP-flattened tail covers the remaining 5 cmds. *)
    unfold1_cmd_goal; cbn [cmd_body].
    cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.literal WeakestPrecondition.get
         WeakestPrecondition.dexpr dlet.dlet].
    eexists. split.
    { eexists. split. { exact Hl_i. }
      cbv [Semantics.interp_binop]. reflexivity. }
    (* === Remaining proof outline (~600 LoC for full Qed): ===

       After Step 1, the WP form is flat (dexprs/call/dexprs/call/dexprs/call),
       reflecting the seq-decomposed form of:
         double(ACC, ACC); byte = load1(...); bit = (...); add_precomputed(...);
         cmov_5felems(...).
       Each [call] discharge needs dexprs args + spec_of pre/post management.

       Algebraic note for tracking the loop measure:
           word.unsigned (word.sub i_word (word.of_Z 1)) = Z.of_nat (n - 1).
       Holds because n > 0 (Hn_pos) and n <= 256 (Hn_le), so the subtraction
       does not wrap (256 - 1 fits in 64 bits).

       Step 2 — Peel [call functions "double" [ACC; ACC]].
         Discharge dexpr arg-list:
           - [eexists; split; [exact Hl_ACC | reflexivity]] for first ACC.
           - [eexists; split; [exact Hl_ACC | reflexivity]] for second ACC.
         The spec [spec_of_double64] expects:
           (out $@ p_out * a p5@ p_a * R)%sep m
           with [Datatypes.length out = 200%nat].
         BUT here p_out = p_a = ACC_ptr (in-place). So we need to split
         [acc_bytes$@ACC_ptr] (200 bytes) as p5@ form via
         [byte_acc_5felem_iff], and use a *fresh* 200-byte buffer for
         the [out] precondition. There is no fresh buffer — [double]'s
         spec writes the output to p_out which equals p_a. This means
         [double(ACC, ACC)] OVERWRITES the 5-FElem bytes at ACC_ptr with
         the new doubled coords.

         The spec is expressed with [out $@ p_out] (200 bytes) AND
         [a p5@ p_a] simultaneously — when p_out = p_a these refer to
         the SAME 200 bytes (sep-aliased). This requires the spec to
         *consume* the old bytes via the "out" predicate (fresh write)
         AND the "a" predicate (read input). For an in-place call, we
         must rewrite [acc_bytes$@ACC_ptr] as
           (acc_bytes$@ACC_ptr) ⋆ (a p5@ ACC_ptr)
         — but this is NOT a valid sep-split: the same 200 bytes can't
         be in two clauses simultaneously.

         RESOLUTION: [double]'s spec was authored expecting a
         non-aliased call site; [double(ACC, ACC)] aliases at the
         bedrock2 source level. For the spec to apply, we need a
         *separate* output buffer. The implementation in
         [ed25519_scalarmult_base_parametric] uses [double(ACC, ACC)]
         which strictly speaking does NOT match
         [spec_of_double64]'s precondition.
         (Confirmed mismatch — see X25519 EdwardsXYZT.double impl.)

         Two options:
         (a) Re-define the impl to use an explicit temp buffer:
             double(TMP, ACC); copy TMP → ACC.
             But then we need a 5-felem byte-copy, increasing program size.
         (b) Provide a second [spec_of_double_inplace] that accepts
             aliased input/output with [a p5@ p_a * R] precondition only.
             The body of [double] would need to be re-verified at this
             spec; routine but additional ~150 LoC.

         For this scaffold, we admit the call. A future task should
         resolve the alias issue at the spec level (option b).

       Step 3 — [byte = load1(scalar + (i >> 3))].
         Address dexpr: word.add scalar_ptr (word.sru i' (word.of_Z 3)).
         Use [Memory.load_byte_of_sep] on the [scalar$@scalar_ptr] sep
         conjunct, with offset [word.unsigned (word.sru i' (word.of_Z 3))].
         The bound [i' < 256] gives [(i' >> 3) < 32] so the load is in-range.
         Result: byte = nth_default Byte.x00 scalar (Z.to_nat (i'>>3)).

       Step 4 — [bit = (byte >> (i & 7)) & 1].
         Pure binop dexpr discharge — no memory access.
         By [bit_extraction_in_zero_one]:
           bit = word.of_Z 0 \/ bit = word.of_Z 1.

       Step 5 — [call functions "add_precomputed" [TMP; ACC; B_pre]].
         spec_of_add_precomputed64 expects:
           (out $@ p_out * a p5@ p_a * b p3@ p_b * R)%sep m,
         with [Datatypes.length out = 200%nat].
         At this call:
           - p_out = TMP_ptr (200 bytes available — write target).
           - p_a   = ACC_ptr (5-FElem-form; the *output* of double, now
             a fresh projective_coords — its value is irrelevant to the
             algebraic chain at this scaffold's level).
           - p_b   = B_pre_ptr (3-FElem-form). Need a 120-byte ↔ 3-FElem
             bridge (NOT YET IMPLEMENTED; see file header).
         Conversion sequence:
           (a) [tmp_bytes$@TMP_ptr] stays as bytes (matches [out $@ p_out]).
           (b) After [double], ACC_ptr holds 5 fresh FElems forming
               the new projective_coords (tracked via [exists X Y Z Ta Tb]
               in the [spec_of_double64] post). We need to repackage
               these 5 FElems back into a [projective_coords] sigma type
               for the [a p5@ p_a] argument; this requires a witness
               of [valid_projective_coords] for the doubled point —
               which comes from [proj1_sig (m1double …) = (feval X, …)]
               in the [double] post + [point_implies_coords_valid].
           (c) [B_pre$@B_pre_ptr] (120 bytes) needs to split into 3
               FElems via the missing 3-felem bridge, then repackage as
               a [precomputed_coords] sigma using
               [valid_precomputed_coords] from the loop invariant.
         Output: [a_plus_b p5@ TMP_ptr] (5 FElems at TMP_ptr) + ACC's
         5 FElems still at ACC_ptr + B_pre's 3 FElems still at B_pre_ptr.
         Convert TMP, ACC, B_pre back to byte form (via reverse iff1ToEq
         + rewrite) for the next step.

       Step 6 — [call functions "cmov_5felems" [ACC; TMP; bit]].
         Discharge dexpr arg-list (3 args).
         Mask precondition: [bit = of_Z 0 \/ bit = of_Z 1] from
         [bit_extraction_in_zero_one] (Step 4).
         Pre: [(acc_bytes$@ACC_ptr) ⋆ (tmp_bytes_after_add$@TMP_ptr) ⋆ R].
         Post: [(acc_bytes_after_cmov$@ACC_ptr) ⋆ ...] where
           acc_bytes_after_cmov =
             if bit = 0 then acc_bytes_after_double else tmp_bytes_after_add.
         Both branches preserve [valid_projective_coords] of the bytes:
           - bit=0: bytes are [acc_bytes_after_double], whose decoded
             FElems are the doubled point — valid via the [double] post.
           - bit=1: bytes are [tmp_bytes_after_add], whose decoded FElems
             are the added point — valid via the [add_precomputed] post.

       Step 7 — Apply continuation [post].
         Provide acc_bytes' := acc_bytes_after_cmov,
         tmp_bytes' := tmp_bytes_after_add,
         i_word' := word.sub i_word (word.of_Z 1),
         loc' := the final updated locals (with "i", "byte", "bit" puts).
         Discharge each map.get via [map.get_put_diff] chains.
         Discharge the validity by case-split on [bit ∈ {0,1}].
    *)
    admit.
  Admitted.

End LoopBodyPreserves.
