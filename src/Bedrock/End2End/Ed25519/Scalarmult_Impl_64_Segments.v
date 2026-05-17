(** * R10 decomposition — segment lemmas
 *
 * Splits R10's body (in [Scalarmult_Impl_64.v]) into four Qed-sealed
 * sub-lemmas, one per call-site.  Integrating them into R10's body
 * extracts < 2% of the proof term, so they did not reduce R10's
 * kernel-check time; they are preserved here as standalone targets
 * and for reuse in Sign/Verify proofs with similar call-chain
 * structure.
 *
 * Pattern: each S<i> takes a parametric [post : trace -> mem -> list
 * word -> Prop] plus a continuation hypothesis [Hcont] proving
 * [post tr m nil] from the segment's output state.  Body:
 * [vm_call_compat. { precond_helper. } destruct H. rewrite Hr.
 * eapply Hcont; [...]].
 *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Import Bedrock.End2End.Ed25519.B_precomputed_64.
Require Import Bedrock.End2End.Ed25519.BytesToFelem3.
Require Import Bedrock.End2End.Ed25519.Felems3ToBytes.
Require Import Bedrock.End2End.Ed25519.DeallocCascade.
Require Import Bedrock.End2End.Ed25519.DeallocCascadeHelper.
Require Import Bedrock.End2End.Ed25519.FromBytesCallHelpers.
Require Import Bedrock.Util.SepCallReflect.

Section R10Segments.
  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
  Local Notation felem := (felem(FieldRepresentation:=frep25519)).
  Local Notation word := (Naive.word 64).
  Local Notation mem := BasicC64Semantics.mem.

  (* Re-declare the Section-local spec instance from Scalarmult_Impl_64.v.
     [Field.spec_of_from_bytes] is the underlying spec body. *)
  Local Instance spec_of_fe25519_from_bytes :
    spec_of "fe25519_from_bytes" := Field.spec_of_from_bytes.

  (* Re-declare the parametric spec.  Same body as [Scalarmult_Impl_64.v]'s
     [spec_of_ed25519_scalarmult_base_parametric] (line 114).  The original
     is Section-local in [Scalarmult_Impl_64.v] and not exported, so we
     duplicate it here.  Keeping bodies syntactically identical is important
     so the typeclass resolution in [vm_call_compat] picks up the right
     spec.  *)
  Local Instance spec_of_ed25519_scalarmult_base_parametric :
    spec_of "ed25519_scalarmult_base_parametric" :=
    fnspec! "ed25519_scalarmult_base_parametric"
      (out_ptr scalar_ptr B_pre_ptr : Naive.word 64) /
      (out scalar B_pre : list Byte.byte) (R : map.rep -> Prop),
    { requires tr mem :=
        Datatypes.length out = 200%nat /\
        Datatypes.length scalar = 32%nat /\
        Datatypes.length B_pre = 120%nat /\
        ((out$@out_ptr) ⋆ (scalar$@scalar_ptr) ⋆ (B_pre$@B_pre_ptr) ⋆ R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        exists out' : list Byte.byte,
          Datatypes.length out' = 200%nat /\
          ((out'$@out_ptr) ⋆ (scalar$@scalar_ptr) ⋆ (B_pre$@B_pre_ptr) ⋆ R)%sep mem' }.

  (** ** Segment S1 — 1st from_bytes(B_pre, B_pre_bytes)
   *
   * Pre-state: post-setup, all 6 chunks ([chunk32_0/1/2] + [chunk40_0/1/2])
   *            split out, [Hsep'] right-assoc with all 6 chunks in flight.
   * Post-state: [X_b0 : felem] extracted, [Hsep_b0_post] holds.
   *
   * Continuation hypothesis: given S1's post (X_b0, Hsep_b0_post, etc.),
   * the deeply-nested 3-call-deep continuation closes.
   *
   * Conclusion: the entry call goal at R10 line 619.
   *
   * Source for body: [Scalarmult_Impl_64.v] lines 619-672.
   *
   * The continuation has shape "S2-entry call goal", which is itself
   * the deeply-nested form
   *   exists args, dexprs m1 l'1 [B_pre+40; B_pre_bytes+32] args /\
   *   call functions "fe25519_from_bytes" tr1 m1 args (fun ... => <S3-...>)
   *
   * Threading a continuation of this exact shape through S1's Lemma
   * signature is mechanical but verbose (~50 LoC of forall-bound
   * existentials).  Using a Prop variable [post : ... -> Prop] keeps
   * the Lemma generic and the verbosity off the type.
   *)
  Lemma R10_S1_first_from_bytes
    (functions : env)
    (Hfb : spec_of_fe25519_from_bytes functions)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (out_init scalar : list Byte.byte)
    (R : mem -> Prop)
    (tr : trace)
    (Hlen_out : Datatypes.length out_init = 200%nat)
    (Hlen_scalar : Datatypes.length scalar = 32%nat)
    (chunk32_0 chunk32_1 chunk32_2 : list Byte.byte)
    (chunk40_0 chunk40_1 chunk40_2 : list Byte.byte)
    (Hc0_len : Datatypes.length chunk32_0 = 32%nat)
    (Hb0_len : Datatypes.length chunk40_0 = 40%nat)
    (Hbib_c0 : Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_0)
    (m' : mem)
    (Hsep' :
      (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
       ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
       ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
       ⋆ sepclause_of_map (chunk40_0$@B_pre_addr)
       ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
       ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
       ⋆ sepclause_of_map (out_init$@out_ptr)
       ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep m')
    (* Continuation: the post-S1 state must close the outer goal *)
    (post : trace -> mem -> list word -> Prop)
    (Hcont :
      forall (a0 : mem) (X_b0 : felem) (tr_after_b0 : trace),
        feval (felem_to_list X_b0) = feval_bytes chunk32_0 ->
        bounded_by tight_bounds (felem_to_list X_b0) ->
        tr_after_b0 = tr ->
        (FElem B_pre_addr X_b0
         ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
         ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
         ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
         ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
         ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
         ⋆ sepclause_of_map (out_init$@out_ptr)
         ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep a0 ->
        post tr_after_b0 a0 nil) :
    (* Conclusion: S1-entry call goal *)
    WeakestPrecondition.call functions "fe25519_from_bytes" tr m'
      (B_pre_addr :: B_pre_bytes_addr :: nil) post.
  Proof.
    vm_call_compat.
    { eapply from_bytes_precond_b0;
        [ ecancel_assumption | exact Hc0_len | exact Hb0_len | exact Hbib_c0 ]. }
    destruct H as (Hr_b0 & Htr_b0 & X_b0 & Hfeval_b0 & Hbnd_b0 & Hsep_b0_post).
    rewrite Hr_b0.
    eapply Hcont;
      [ exact Hfeval_b0
      | exact Hbnd_b0
      | symmetry; exact Htr_b0
      | ecancel_assumption ].
  Time Qed.

  (** ** Segment S2 — 2nd from_bytes(B_pre+40, B_pre_bytes+32)
   *
   * Pre-state: post-S1, X_b0 in scope, [Hsep_b0_post] live.
   * Post-state: X_b1 extracted, [Hsep_b1_post] holds.
   *
   * Source for body: [Scalarmult_Impl_64.v] lines 692-706.
   *)
  Lemma R10_S2_second_from_bytes
    (functions : env)
    (Hfb : spec_of_fe25519_from_bytes functions)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (out_init scalar : list Byte.byte)
    (R : mem -> Prop)
    (tr : trace)
    (chunk32_0 chunk32_1 chunk32_2 : list Byte.byte)
    (chunk40_1 chunk40_2 : list Byte.byte)
    (X_b0 : felem)
    (Hc1_len : Datatypes.length chunk32_1 = 32%nat)
    (Hb1_len : Datatypes.length chunk40_1 = 40%nat)
    (Hbib_c1 : Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_1)
    (a0 : mem)
    (Hsep_b0_post :
      (FElem B_pre_addr X_b0
       ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
       ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
       ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
       ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
       ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
       ⋆ sepclause_of_map (out_init$@out_ptr)
       ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep a0)
    (post : trace -> mem -> list word -> Prop)
    (Hcont :
      forall (a1 : mem) (X_b1 : felem) (tr_after_b1 : trace),
        feval (felem_to_list X_b1) = feval_bytes chunk32_1 ->
        bounded_by tight_bounds (felem_to_list X_b1) ->
        tr_after_b1 = tr ->
        (FElem (word.add B_pre_addr (word.of_Z 40)) X_b1
         ⋆ FElem B_pre_addr X_b0
         ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
         ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
         ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
         ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
         ⋆ sepclause_of_map (out_init$@out_ptr)
         ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep a1 ->
        post tr_after_b1 a1 nil) :
    WeakestPrecondition.call functions "fe25519_from_bytes" tr a0
      (word.add B_pre_addr (word.of_Z 40)
       :: word.add B_pre_bytes_addr (word.of_Z 32) :: nil) post.
  Proof.
    vm_call_compat.
    { eapply from_bytes_precond_b1;
        [ ecancel_assumption | exact Hc1_len | exact Hb1_len | exact Hbib_c1 ]. }
    destruct H as (Hr_b1 & Htr_b1 & X_b1 & Hfeval_b1 & Hbnd_b1 & Hsep_b1_post).
    rewrite Hr_b1.
    eapply Hcont;
      [ exact Hfeval_b1
      | exact Hbnd_b1
      | symmetry; exact Htr_b1
      | ecancel_assumption ].
  Time Qed.

  (** ** Segment S3 — 3rd from_bytes(B_pre+80, B_pre_bytes+64)
   *
   * Pre-state: post-S2, X_b0 + X_b1 in scope.
   * Post-state: X_b2 extracted, [Hsep_b2_post] holds.
   *
   * Source for body: [Scalarmult_Impl_64.v] lines 710-723.
   *)
  Lemma R10_S3_third_from_bytes
    (functions : env)
    (Hfb : spec_of_fe25519_from_bytes functions)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (out_init scalar : list Byte.byte)
    (R : mem -> Prop)
    (tr : trace)
    (chunk32_0 chunk32_1 chunk32_2 : list Byte.byte)
    (chunk40_2 : list Byte.byte)
    (X_b0 X_b1 : felem)
    (Hc2_len : Datatypes.length chunk32_2 = 32%nat)
    (Hb2_len : Datatypes.length chunk40_2 = 40%nat)
    (Hbib_c2 : Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_2)
    (a1 : mem)
    (Hsep_b1_post :
      (FElem (word.add B_pre_addr (word.of_Z 40)) X_b1
       ⋆ FElem B_pre_addr X_b0
       ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
       ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
       ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
       ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
       ⋆ sepclause_of_map (out_init$@out_ptr)
       ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep a1)
    (post : trace -> mem -> list word -> Prop)
    (Hcont :
      forall (a2 : mem) (X_b2 : felem) (tr_after_b2 : trace),
        feval (felem_to_list X_b2) = feval_bytes chunk32_2 ->
        bounded_by tight_bounds (felem_to_list X_b2) ->
        tr_after_b2 = tr ->
        (FElem (word.add B_pre_addr (word.of_Z 80)) X_b2
         ⋆ FElem (word.add B_pre_addr (word.of_Z 40)) X_b1
         ⋆ FElem B_pre_addr X_b0
         ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
         ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
         ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
         ⋆ sepclause_of_map (out_init$@out_ptr)
         ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep a2 ->
        post tr_after_b2 a2 nil) :
    WeakestPrecondition.call functions "fe25519_from_bytes" tr a1
      (word.add B_pre_addr (word.of_Z 80)
       :: word.add B_pre_bytes_addr (word.of_Z 64) :: nil) post.
  Proof.
    vm_call_compat.
    { eapply from_bytes_precond_b2;
        [ ecancel_assumption | exact Hc2_len | exact Hb2_len | exact Hbib_c2 ]. }
    destruct H as (Hr_b2 & Htr_b2 & X_b2 & Hfeval_b2 & Hbnd_b2 & Hsep_b2_post).
    rewrite Hr_b2.
    eapply Hcont;
      [ exact Hfeval_b2
      | exact Hbnd_b2
      | symmetry; exact Htr_b2
      | ecancel_assumption ].
  Time Qed.

  (** ** Segment S4 — parametric call + dealloc cascade
   *
   * Pre-state: all 3 X_b<i> in scope, ready for parametric call.
   * Post-state: out_par extracted, dealloc closes via [dealloc_cascade_full].
   *
   * Source for body: [Scalarmult_Impl_64.v] lines 727-759.
   *
   * **Hypothesis**: this segment is the bottleneck (deepest sep, dealloc
   * cascade with [ecancel_assumption_impl] bridge through 9-atom state).
   *)
  Lemma R10_S4_parametric_and_dealloc
    (functions : env)
    (Hpar : spec_of_ed25519_scalarmult_base_parametric functions)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (out_init scalar : list Byte.byte)
    (R : mem -> Prop)
    (tr : trace)
    (chunk32_0 chunk32_1 chunk32_2 : list Byte.byte)
    (X_b0 X_b1 X_b2 : felem)
    (Hlen_out : Datatypes.length out_init = 200%nat)
    (Hlen_scalar : Datatypes.length scalar = 32%nat)
    (Hc0_len : Datatypes.length chunk32_0 = 32%nat)
    (Hc1_len : Datatypes.length chunk32_1 = 32%nat)
    (Hc2_len : Datatypes.length chunk32_2 = 32%nat)
    (a2 : mem)
    (Hsep_b2_post :
      (FElem (word.add B_pre_addr (word.of_Z 80)) X_b2
       ⋆ FElem (word.add B_pre_addr (word.of_Z 40)) X_b1
       ⋆ FElem B_pre_addr X_b0
       ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
       ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
       ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
       ⋆ sepclause_of_map (out_init$@out_ptr)
       ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep a2)
    (post : trace -> mem -> list word -> Prop)
    (Hcont :
      forall (m_final : mem) (out_par : list Byte.byte) (tr_after : trace),
        Datatypes.length out_par = 200%nat ->
        tr_after = tr ->
        (sepclause_of_map (out_par$@out_ptr)
         ⋆ sepclause_of_map (scalar$@scalar_ptr)
         ⋆ sepclause_of_map
             ((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b0)
               ++ ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b1)
               ++ ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b2))%list
              $@B_pre_addr)
         ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
         ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
         ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
         ⋆ R)%sep m_final ->
        post tr_after m_final nil) :
    WeakestPrecondition.call functions "ed25519_scalarmult_base_parametric" tr a2
      (out_ptr :: scalar_ptr :: B_pre_addr :: nil) post.
  Proof.
    vm_call_compat.
    1: { eapply parametric_call_precond;
           [ exact Hlen_out | exact Hlen_scalar | ecancel_assumption ]. }
    destruct H as (Hr_par & Htr_par & out_par & Hlen_par & Hsep_par).
    rewrite Hr_par.
    eapply Hcont;
      [ exact Hlen_par
      | exact Htr_par
      | ecancel_assumption ].
  Time Qed.

  (** ** R10_close_4_calls — chains S1 → S2 → S3 → S4
   *
   * Conclusion: [call functions "fe25519_from_bytes" tr m' [B_pre_addr;
   * B_pre_bytes_addr] post_4call] where [post_4call] is the deeply-nested
   * 3-call-deep continuation parameterized by an outer [Hcont_final].
   *)
  Lemma R10_close_4_calls
    (functions : env)
    (Hfb : spec_of_fe25519_from_bytes functions)
    (Hpar : spec_of_ed25519_scalarmult_base_parametric functions)
    (out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr : word)
    (out_init scalar : list Byte.byte)
    (R : mem -> Prop)
    (tr : trace)
    (Hlen_out : Datatypes.length out_init = 200%nat)
    (Hlen_scalar : Datatypes.length scalar = 32%nat)
    (chunk32_0 chunk32_1 chunk32_2 : list Byte.byte)
    (chunk40_0 chunk40_1 chunk40_2 : list Byte.byte)
    (Hc0_len : Datatypes.length chunk32_0 = 32%nat)
    (Hc1_len : Datatypes.length chunk32_1 = 32%nat)
    (Hc2_len : Datatypes.length chunk32_2 = 32%nat)
    (Hb0_len : Datatypes.length chunk40_0 = 40%nat)
    (Hb1_len : Datatypes.length chunk40_1 = 40%nat)
    (Hb2_len : Datatypes.length chunk40_2 = 40%nat)
    (Hbib_c0 : Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_0)
    (Hbib_c1 : Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_1)
    (Hbib_c2 : Field.bytes_in_bounds (FieldRepresentation:=frep25519) chunk32_2)
    (m' : mem)
    (Hsep' :
      (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
       ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
       ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
       ⋆ sepclause_of_map (chunk40_0$@B_pre_addr)
       ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
       ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
       ⋆ sepclause_of_map (out_init$@out_ptr)
       ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep m')
    (post : trace -> mem -> list word -> Prop)
    (Hcont_final :
      forall (m_final : mem) (out_par : list Byte.byte)
             (X_b0 X_b1 X_b2 : felem),
        Datatypes.length out_par = 200%nat ->
        (sepclause_of_map (out_par$@out_ptr)
         ⋆ sepclause_of_map (scalar$@scalar_ptr)
         ⋆ sepclause_of_map
             ((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b0)
               ++ ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b1)
               ++ ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b2))%list
              $@B_pre_addr)
         ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
         ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
         ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
         ⋆ R)%sep m_final ->
        post tr m_final nil) :
    WeakestPrecondition.call functions "fe25519_from_bytes" tr m'
      (B_pre_addr :: B_pre_bytes_addr :: nil) post.
  Proof.
    (* Chaining S1..S4 inside an abstract [post] cannot peel the
       deeply-nested [exists l, putmany ... /\ exists args, dexprs ...
       /\ call ...] shape that R10's concrete post unfolds to.  The
       chained form is preserved here as a placeholder; the live
       version of this composition lives inline in R10's proof body
       in [Scalarmult_Impl_64.v], where [post] is the concrete
       deeply-nested form. *)
  Admitted.

End R10Segments.
