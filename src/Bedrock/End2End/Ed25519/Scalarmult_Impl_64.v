(** * Ed25519 scalarmult against fixed basepoint — bedrock2 body (64-bit).
 *
 * Discharge target for [Scalarmult.v]'s [Parameter ed25519_scalarmult_base]
 * + [Axiom ed25519_scalarmult_base_correct].
 *
 * Algorithm: standard left-to-right double-and-add, MSB-first, 256
 * iterations.  Constant-time discipline: the conditional add is
 * implemented as an unconditional add into [TMP] followed by a
 * constant-time [cmov_5felems(ACC, TMP, bit)].  No branch on bit.
 *
 * **Parametric form**: takes the precomputed basepoint [B_pre] as an
 * explicit pointer argument (3 felems × 40 bytes = 120 bytes).  The
 * 2-arg API [ed25519_scalarmult_base(out, scalar)] required by the
 * existing weak [Axiom] in [Scalarmult.v] is provided by a thin wrapper
 * that allocates [B_pre] on the stack and initializes its bytes from a
 * vm_compute'd constant (R10.C).
 *
 * STATUS:
 *   - Parametric Definition + parametric spec_of stated.
 *   - Wrapper for 2-arg API: pending R10.C (B_precomputed bytes).
 *   - WP correctness proof: pending R10.A (cmov_5felems_correct) and R10.E. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Import Bedrock.End2End.Ed25519.Cmov5Felems_64.
Require Import Bedrock.End2End.Ed25519.B_precomputed_64.

Section ScalarmultImpl64.
  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  (** [ed25519_scalarmult_base_parametric(out, scalar, B_pre)]
      Computes [scalar · B] in extended twisted Edwards coordinates
      (X, Y, Z, Ta, Tb), with [Ta · Tb = T] tracked separately.

      Buffer sizes:
        out    — 200 bytes (5 felems)
        scalar — 32 bytes (LE-encoded 256-bit scalar)
        B_pre  — 120 bytes (3 felems: half_ypx, half_ymx, xyd)

      ACC starts at the identity ((0, 1, 1, 0, 0)). For i from 255 down
      to 0: double ACC, then unconditionally compute TMP = ACC + B (via
      add_precomputed), then constant-time cmov ACC ← TMP if bit i of
      scalar is 1.

      Final memcpy ACC → out is via an unconditional cmov_5felems with
      mask=1, reusing the same primitive (no separate memmove needed). *)
  Definition ed25519_scalarmult_base_parametric :=
    func! (out, scalar, B_pre) {
      stackalloc 200 as ACC;
      stackalloc 200 as TMP;
      fe25519_from_word(ACC,        $0);
      fe25519_from_word(ACC + $40,  $1);
      fe25519_from_word(ACC + $80,  $1);
      fe25519_from_word(ACC + $120, $0);
      fe25519_from_word(ACC + $160, $0);
      i = $256;
      while ($0 < i) {
        i = i - $1;
        double(ACC, ACC);
        byte = load1(scalar + (i >> $3));
        bit = (byte >> (i & $7)) & $1;
        add_precomputed(TMP, ACC, B_pre);
        cmov_5felems(ACC, TMP, bit)
      };
      cmov_5felems(out, ACC, $1)
    }.

  (** Hoare-spec for the parametric form. Weak postcondition: only
      length(out) = 200. Strengthening to "out encodes scalar · B" is
      a separate task (R10.F) requiring connection to the abstract
      [Ed25519XYZT.scalarmult] from EdwardsXYZT25519.v:96. *)
  Instance spec_of_ed25519_scalarmult_base_parametric :
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

  Lemma ed25519_scalarmult_base_parametric_correct :
    forall functions,
      Interface.map.get functions "ed25519_scalarmult_base_parametric"
        = Some ed25519_scalarmult_base_parametric ->
      (* Callee specs needed: spec_of_fe25519_from_word, spec_of_double,
         spec_of_add_precomputed, spec_of_cmov_5felems. The wrapper
         layer wires these from EdwardsXYZT64 + Cmov5Felems_64. *)
      spec_of_cmov_5felems functions ->
      spec_of_ed25519_scalarmult_base_parametric functions.
  Proof.
    (* Plan:
       1. straightline through the two stackallocs and 5 from_word calls
          to set ACC = identity.
       2. Apply Loops.while_localsmap with measure = nat counting
          remaining iterations (from 256 down to 0). Loop invariant:
            - locals contain {out, scalar, B_pre, ACC, TMP, i}
            - i is a word with unsigned value n ∈ [0, 256]
            - sep predicate: 200 bytes at out_ptr (some content) +
              200 bytes at ACC (current accumulator) +
              200 bytes at TMP (don't-care) +
              32 bytes at scalar (unchanged) +
              120 bytes at B_pre (unchanged) +
              R
            - measure decreases each iteration (handle_call double,
              add_precomputed, cmov each preserve sep + don't change i).
       3. Each iteration: handle_call double_correct,
          handle_call add_precomputed64_correct,
          handle_call cmov_5felems_correct, decrement i, prove invariant.
       4. Loop exit (i = 0): handle_call cmov_5felems_correct with
          mask=1 to copy ACC bytes to out_ptr. Postcondition follows.

       Estimated 300-500 LoC of bedrock2 WP plumbing. *)
  Admitted.

  (** Helper: emit a sequence of word-sized stores to materialize a
      list of u64 literals into consecutive memory at [base + offset .. ].
      Used to load the [B_precomputed_u64s] constant into a stack buffer. *)
  Fixpoint init_u64_seq (base : string) (offset : Z) (vs : list Z) : cmd.cmd :=
    match vs with
    | nil => cmd.skip
    | v :: rest =>
      cmd.seq
        (cmd.store access_size.word
           (expr.op bopname.add (expr.var base) (expr.literal offset))
           (expr.literal v))
        (init_u64_seq base (offset + 8) rest)
    end.

  (** Forward WP lemma for [init_u64_seq]: running it from [base+offset] on
      a buffer of length [8|vs|] leaves the buffer holding
      [flat_map (LittleEndianList.le_split 8) vs]. Proof by induction on [vs] (~50 LoC):
      each iteration peels one [cmd.store] via [Memory.store_Z],
      then applies the IH at offset+8 on the (skipn 8) suffix. *)
  Lemma init_u64_seq_correct
        (functions : map.rep)
        (base : string) (offset : Z) (vs : list Z)
        (base_addr : Naive.word 64) (init_bytes : list Byte.byte) :
    Datatypes.length init_bytes = (8 * Datatypes.length vs)%nat ->
    Forall (fun v => 0 <= v < 2^64) vs ->
    0 <= offset ->
    offset + Z.of_nat (Datatypes.length init_bytes) <= 2^64 ->
    forall tr m loc R post,
      Interface.map.get loc base = Some base_addr ->
      ((init_bytes$@(word.add base_addr (word.of_Z offset))) ⋆ R)%sep m ->
      (forall m',
        ((List.flat_map (LittleEndianList.le_split 8) vs)$@(word.add base_addr (word.of_Z offset)) ⋆ R)%sep m' ->
        post tr m' loc) ->
      cmd functions (init_u64_seq base offset vs) tr m loc post.
  Proof.
    revert offset init_bytes.
    induction vs as [|v rest IH]; intros offset init_bytes
           Hlen Hbnd Hofs Hofs_bnd tr m loc R post Hloc Hsep Hpost.
    - (* Base case vs = nil: cmd.skip *)
      simpl in Hlen. destruct init_bytes; [|simpl in Hlen; discriminate].
      simpl. apply Hpost. simpl. exact Hsep.
    - (* Inductive case vs = v :: rest. CMD peeled to store-WP form via
         unfold1_cmd_goal (per reference_cbv_cmd_body_overunfold.md).
         Remaining steps (~40 LoC, admitted for now):
         1. Provide store address [base_addr + word.of_Z offset] via dexpr+map.get.
         2. Provide stored value [word.of_Z v] via dexpr literal.
         3. Discharge store via SeparationMemory.uncurried_store_Z_of_sep
            on (firstn 8 init_bytes), giving m' with le_split bytes at base+offset.
         4. Apply IH on rest at offset+8, init_bytes := skipn 8 init_bytes.
         5. Combine: le_split 8 v$@base+offset ⋆ flat_map ... rest$@base+offset+8
            ↔ flat_map (le_split 8) (v::rest)$@base+offset
            via sep_eq_of_list_word_at_app reverse + iff1ToEq trick. *)
      simpl init_u64_seq.
      inversion Hbnd as [|? ? Hv_bnd Hrest_bnd]; subst.
      simpl in Hlen.
      unfold1_cmd_goal. cbn [cmd_body].
      (* Address dexpr [base + offset] + value dexpr [v] discharged via
         standard map.get + literal patterns.  Verified in MCP at
         state_id=26 of session bxpoyyf7a (2026-05-04). *)
      cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body
           WeakestPrecondition.expr WeakestPrecondition.expr_body
           WeakestPrecondition.literal WeakestPrecondition.get
           WeakestPrecondition.store WeakestPrecondition.dexpr
           dlet.dlet].
      eexists. split.
      { eexists. split. { exact Hloc. }
        cbv [Semantics.interp_binop]. reflexivity. }
      eexists. split. { reflexivity. }
      (* Discharge [Memory.store_Z m (base+offset) 8 v = Some m1] via
         [SeparationMemory.uncurried_store_Z_of_sep] applied at
         [firstn 8 init_bytes] (the 8 bytes about to be overwritten).
         Then apply [IH] on [rest] at offset [offset + 8] with
         [init_bytes := skipn 8 init_bytes], using the post-store sep
         predicate (the [le_split 8 v] block goes into the IH's R0).
         Finally re-assemble flat_map (le_split 8) (v::rest) =
         le_split 8 v ++ flat_map (le_split 8) rest via
         [sep_eq_of_list_word_at_app] + [iff1ToEq]. *)
      assert (Hsplit_init : init_bytes = (List.firstn 8 init_bytes ++ List.skipn 8 init_bytes)%list)
        by (rewrite List.firstn_skipn; reflexivity).
      assert (Hlen_first : Datatypes.length (List.firstn 8 init_bytes) = 8%nat).
      { rewrite List.length_firstn, Hlen. cbv [Bitwidth64.BW64]. Lia.lia. }
      assert (Hlen_skip : Datatypes.length (List.skipn 8 init_bytes) = (8 * Datatypes.length rest)%nat).
      { rewrite List.length_skipn, Hlen. Lia.lia. }
      epose proof (SeparationMemory.sep_eq_of_list_word_at_app
                     (word.add base_addr (word.of_Z offset))
                     (List.firstn 8 init_bytes) (List.skipn 8 init_bytes) 8) as Hm1.
      specialize (Hm1 ltac:(rewrite Hlen_first; reflexivity)).
      specialize (Hm1 ltac:(rewrite Hlen_first, Hlen_skip; cbv [Bitwidth64.BW64]; Lia.lia)).
      apply iff1ToEq in Hm1.
      rewrite Hsplit_init in Hsep at 1.
      rewrite Hm1 in Hsep.
      edestruct (SeparationMemory.uncurried_store_Z_of_sep
                  (word.add base_addr (word.of_Z offset)) 8%nat
                  (List.firstn 8 init_bytes) v
                  (sepclause_of_map ((List.skipn 8 init_bytes)$@(word.add (word.add base_addr (word.of_Z offset)) (word.of_Z 8))) ⋆ R)%sep
                  m)
        as [m1 [Hstore_eq Hsep1]].
      { ssplit.
        - ecancel_assumption.
        - exact Hlen_first.
        - cbv [Bitwidth64.BW64]. Lia.lia. }
      exists m1. split.
      { unfold Memory.store. cbn [bytes_per bytes_per_word].
        rewrite word.unsigned_of_Z. cbv [word.wrap].
        rewrite Z.mod_small by Lia.lia.
        exact Hstore_eq. }
      apply IH with
        (R := (sepclause_of_map ((LittleEndianList.le_split 8 v)$@(word.add base_addr (word.of_Z offset))) ⋆ R)%sep)
        (init_bytes := List.skipn 8 init_bytes).
      + exact Hlen_skip.
      + exact Hrest_bnd.
      + Lia.lia.
      + rewrite Hlen_skip. Lia.lia.
      + exact Hloc.
      + assert (Haddr_eq : word.add base_addr (word.of_Z (offset + 8)) =
                           word.add (word.add base_addr (word.of_Z offset)) (word.of_Z 8))
          by ZnWords.
        rewrite Haddr_eq.
        ecancel_assumption.
      + intros m' Hsep_post.
        apply Hpost.
        cbn [flat_map].
        epose proof (SeparationMemory.sep_eq_of_list_word_at_app
                       (word.add base_addr (word.of_Z offset))
                       (LittleEndianList.le_split 8 v)
                       (List.flat_map (LittleEndianList.le_split 8) rest)
                       8) as Hm2.
        specialize (Hm2 ltac:(rewrite LittleEndianList.length_le_split; reflexivity)).
        specialize (Hm2 ltac:(
          rewrite LittleEndianList.length_le_split;
          rewrite (List.flat_map_const_length _ 8) by (intros; apply LittleEndianList.length_le_split);
          cbv [Bitwidth64.BW64]; Lia.lia)).
        apply iff1ToEq in Hm2.
        rewrite Hm2.
        assert (Haddr_eq2 : word.add base_addr (word.of_Z (offset + 8)) =
                           word.add (word.add base_addr (word.of_Z offset)) (word.of_Z 8))
          by ZnWords.
        rewrite Haddr_eq2 in Hsep_post.
        ecancel_assumption.
  Qed.

  (** Public 2-arg API: [ed25519_scalarmult_base(out, scalar)].
      Allocates B_pre limb buffer on stack, materializes B_precomputed
      bytes via 12 word stores (computed at compile time from
      [B_precomputed_u64s]), converts each 32-byte chunk to limb form
      via [fe25519_from_bytes], then delegates to the parametric form. *)
  Definition ed25519_scalarmult_base :=
    func! (out, scalar) {
      stackalloc 96 as B_pre_bytes;
      stackalloc 120 as B_pre;
      coq:(init_u64_seq "B_pre_bytes" 0 B_precomputed_u64s);
      fe25519_from_bytes(B_pre,        B_pre_bytes);
      fe25519_from_bytes(B_pre + $40,  B_pre_bytes + $32);
      fe25519_from_bytes(B_pre + $80,  B_pre_bytes + $64);
      ed25519_scalarmult_base_parametric(out, scalar, B_pre)
    }.

  (** Hoare-spec for the public 2-arg API. Shape mirrors the existing
      [Axiom ed25519_scalarmult_base_correct] in [Scalarmult.v]; once
      the [Lemma] below is closed (Qed), [Scalarmult.v] can be edited
      to replace the [Parameter ed25519_scalarmult_base] +
      [Axiom ed25519_scalarmult_base_correct] by a re-export of this
      [Definition] + [Lemma]. *)
  Instance spec_of_ed25519_scalarmult_base :
    spec_of "ed25519_scalarmult_base" :=
    fnspec! "ed25519_scalarmult_base"
      (out_ptr scalar_ptr : Naive.word 64) /
      (out_init scalar : list Byte.byte) (R : map.rep -> Prop),
    { requires tr mem :=
        Datatypes.length out_init = 200%nat /\
        Datatypes.length scalar = 32%nat /\
        ((out_init$@out_ptr) ⋆ (scalar$@scalar_ptr) ⋆ R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        exists out_bytes : list Byte.byte,
          Datatypes.length out_bytes = 200%nat /\
          ((out_bytes$@out_ptr) ⋆ (scalar$@scalar_ptr) ⋆ R)%sep mem' }.

  Lemma ed25519_scalarmult_base_correct :
    forall functions,
      Interface.map.get functions "ed25519_scalarmult_base"
        = Some ed25519_scalarmult_base ->
      spec_of_ed25519_scalarmult_base_parametric functions ->
      (* Plus callees: spec_of_fe25519_from_bytes wired from
         EdwardsXYZT64_Imports → Field25519_64. *)
      spec_of_ed25519_scalarmult_base functions.
  Proof.
    intros functions Hf Hpar.
    cbv [program_logic_goal_for]; intros.
    cbv [spec_of_ed25519_scalarmult_base].
    intros out_ptr scalar_ptr out_init scalar R tr mem
           (Hlen_out & Hlen_scalar & Hsep).
    (* Phase 0: expand [call] to [exec] form via Hf. *)
    unfold call.
    do 3 eexists. split; [exact Hf|].
    eexists. split; [reflexivity|].
    (* Convert exec → cmd so we can use straightline. *)
    apply sound_cmd; try typeclasses eauto.
    (* Phase 1: peel both stackallocs (96 + 120 bytes). *)
    straightline.
    split; [reflexivity|].
    intros B_pre_bytes_addr mStack1 mCombined1 Hany1 Hsplit1.
    unfold dlet.dlet.
    straightline.
    split; [reflexivity|].
    intros B_pre_addr mStack2 mCombined2 Hany2 Hsplit2.
    unfold dlet.dlet.
    (* Phase 2: peel cmd.seq for init_u64_seq, apply init_u64_seq_correct.
       The first stackalloc gives us 96 bytes at B_pre_bytes_addr;
       after init_u64_seq, those bytes are flat_map (LittleEndianList.le_split 8) B_precomputed_u64s
       which equals B_precomputed_bytes by B_precomputed_u64s_to_bytes. *)
    (* Step the cmd.seq peeling and apply init_u64_seq_correct: *)
    eapply WeakestPreconditionProperties.Proper_cmd; cycle 1.
    { eapply init_u64_seq_correct.
      - rewrite B_precomputed_u64s_length.
        (* length of any 96-byte init_bytes from anybytes — proven via anybytes_unique_domain *)
        admit.
      - exact B_precomputed_u64s_bound.
      - Lia.lia.
      - admit. (* offset + length <= 2^64; trivially since 0 + 96 < 2^64 *)
      - rewrite ?map.get_put_diff by congruence.
        rewrite map.get_put_same. reflexivity.
      - admit. (* init_bytes$@B_pre_bytes_addr ⋆ R sep predicate; needs
                 anybytes → exists init_bytes, init_bytes$@... extraction *)
      - intros m' Hsep'.
        (* Phase 3: 3× handle_call fe25519_from_bytes_correct.
           After init_u64_seq, B_pre_bytes holds B_precomputed_bytes
           (after rewriting via B_precomputed_u64s_to_bytes).
           Each fe25519_from_bytes call:
           - reads 32 bytes from B_pre_bytes_addr + 32*i
           - writes 40 bytes (5 limbs) to B_pre_addr + 40*i
           Phase 4: handle_call ed25519_scalarmult_base_parametric_correct (via Hpar)
           gives out_bytes with length 200.
           Phase 5: dealloc B_pre / B_pre_bytes from m' to recover m'_inner.
           Phase 6: provide nil for rets, tr=tr, out_bytes existential. *)
        admit. }
    intros tr' m' l' Hpost.
    (* Proper_cmd's monotonicity goal: post derived from inner post. *)
    admit.
  Admitted.

End ScalarmultImpl64.
