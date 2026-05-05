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
Require Import Bedrock.End2End.Ed25519.BytesToFelem3.
Require Import Bedrock.End2End.Ed25519.DeallocCascade.

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
      to 0: double ACC into TMP (via [double(TMP, ACC)]), unconditionally
      cmov ACC ← TMP (memcpy via [cmov_5felems(ACC, TMP, $1)]),
      unconditionally compute TMP = ACC + B (via add_precomputed),
      then constant-time cmov ACC ← TMP if bit i of scalar is 1.

      The [double(TMP, ACC); cmov_5felems(ACC, TMP, $1)] pattern (rather
      than the natural [double(ACC, ACC)]) avoids the sep-aliasing that
      [spec_of_double64] forbids — its precondition requires [out] and
      [a] to be sep-disjoint.  TMP is reused as scratch for the doubling
      output before being overwritten by the subsequent add_precomputed.

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
        double(TMP, ACC);
        cmov_5felems(ACC, TMP, $1);
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
    (* === Phase 0 (verified in MCP, 2026-05-04, state_id=185): ===
       cbv [program_logic_goal_for]. intros funs Hf Hcmov.
       cbv [spec_of_ed25519_scalarmult_base_parametric].
       intros out_ptr scalar_ptr B_pre_ptr out scalar B_pre R tr mem
              (Hlen_out & Hlen_scalar & Hlen_Bpre & Hsep).
       unfold call.
       do 3 eexists. split; [exact Hf|].
       eexists. split; [reflexivity|].
       apply sound_cmd; try typeclasses eauto.
       (* Two stackallocs: *)
       straightline. split; [reflexivity|].
       intros ACC_addr mStack1 mCombined1 Hany_ACC Hsplit_ACC.
       unfold dlet.dlet.
       straightline. split; [reflexivity|].
       intros TMP_addr mStack2 mCombined2 Hany_TMP Hsplit_TMP.
       unfold dlet.dlet.

       === Realistic scope assessment (after deep MCP exploration): ===
       The originally estimated 300-500 LoC undercounts the work by ~4×.
       This proof realistically requires ~1500-2000 LoC of WP plumbing,
       comparable to Bedrock.Field.Synthesis.Examples.BLS12_GLV_ScalarMultBedrock
       (1542 LoC, 2 Qed = ~700 LoC/lemma). Key reasons:

       * SPEC SHAPE MISMATCH. cmov_5felems is BYTE-level (200-byte buffer
         in/out). double + add_precomputed64 are FELEM-level (5 separate
         FElem chunks via the p5@ notation), and require valid_projective_coords
         + 5 bounds proofs in their preconditions. The loop accumulator ACC
         must alternate between byte-form (for cmov_5felems input) and
         FElem-decomposed form (for double's input/output) at every iteration.

         Bridging is via felem_from_bytes / felem_to_bytes (Lift1Prop.iff1
         rewrites in EdwardsXYZT64_Imports → Field25519_64), but each transition
         requires:
         - Extracting 5 chunks of 40 bytes via List.firstn/skipn at offsets
           0, 40, 80, 120, 160.
         - Showing each 40-byte chunk decodes to a felem with feval = the
           algebraic value (and bounds).
         - For the *initial* identity (0,1,1,0,0), proving valid_projective_coords
           with feval Z = F.one ≠ 0 (vm_decide).
         - After each double / add_precomputed, taking the 5 fresh FElem
           chunks and re-merging them into 200 bytes (each via length_le_split
           on whatever bs2felem witnesses are extracted).

       * HANDLE_CALL boilerplate. For each of (5 from_word) + (256 × 3 calls in
         body) + (1 cmov_5felems at exit), we need:
         - dexpr discharge for arg-list (eexists; split; map.get_put_diff chain).
         - unify the hypothesized sep predicate against the spec's pre.
         - peel the post: instantiate existentials, sep manipulation.
         - map.get_put_diff chain (~10 puts deep at the loop body interior).

       * IDENTITY VALIDITY witnesses. The 5 from_word calls produce 5 FElems
         X, Y, Z, Ta, Tb with feval X = 0, feval Y = 1, feval Z = 1, feval Ta = 0,
         feval Tb = 0. We must construct an `acc0 : projective_coords` whose
         proj1_sig is (X, Y, Z, Ta, Tb) — discharging valid_projective_coords:
           a*0^2*1^2 + 1^2*1^2 = 1^2^2 + d*0^2*1^2  (clearly true)
           0 * 1 = 1 * 0 * 0                          (clearly true)
           1 ≠ 0                                       (Curve25519 inhabited)
         These need to be exhibited in a sigma type — ~50 LoC of glue.

       === Required additional callee specs (NOT YET WIRED): ===
       The current Lemma signature only exposes spec_of_cmov_5felems. To run
       handle_call on the four other callees, the signature must be extended:
         spec_of_fe25519_from_word functions ->
         spec_of_double64 functions ->
         spec_of_add_precomputed64 functions ->
       These can be added either as additional hypotheses or via Existing Instance.

       === Sub-obligations for a future session (in order, with LoC budget): ===

       (A) Phase 0: setup + 2 stackallocs.    [verified 2026-05-04, ~30 LoC]
       (B) anybytes → 200-byte split.          [~30 LoC; uses anybytes_to_array_1]
       (C) 5 × from_word handle_call:          [~500 LoC]
           - split 200 bytes into 5 × 40 byte chunks at ACC_addr + 0/40/80/120/160
           - per call: dexpr address (ACC + literal offset), dexpr value (literal),
             handle_call with the 40-byte chunk + R-frame containing the other 160 bytes
           - extract FElem from output postcondition
       (D) Identity projective_coords witness. [~80 LoC]
           - assemble (X0, Y1, Z1, Ta0, Tb0) into projective_coords identity
           - valid_projective_coords proof on (0,1,1,0,0)
       (E) Convert ACC's 5 FElems back to a 200-byte view for the loop invariant.
           [~60 LoC; setoid_rewrite felem_to_bytes 5×]
       (F) Set i = 256.                         [~5 LoC]
       (G) Loop invariant definition.           [~80 LoC]
           Carries: locals {out,scalar,B_pre,ACC,TMP,i}, i = word.of_Z (Z.of_nat n),
           n ∈ [0,256], EITHER (acc_bytes : list byte, length 200, plus dummy TMP_bytes
           length 200, plus sep) OR (acc_pcoords : projective_coords + p5@ at ACC_addr,
           plus 200 anybytes at TMP_addr, plus the byte sep). The byte form is needed
           at cmov_5felems boundaries; FElem form at double/add_precomputed.
           Likely best to carry BYTE form in invariant; convert in/out at each call.
       (H) Apply Loops.while_localsmap; entry case (n=256). [~50 LoC]
       (I) Loop body, n = S n':                 [~600 LoC]
           - i = i - 1
           - byte→FElem split for ACC (5×)
           - handle_call double  (input: a p5@ ACC_addr + 200 bytes at TMP_addr;
             output: 5 FElems at ACC_addr forming new acc_pcoords)
           - FElem→byte merge for ACC (5×) to recover ACC bytes for cmov input
           - byte→FElem split for ACC (again, for add_precomputed input)
           - dexpr discharge for byte = load1(scalar + (i >> 3))
           - dexpr discharge for bit = (byte >> (i & 7)) & 1
           - byte→FElem split for B_pre (3×) for add_precomputed input
           - handle_call add_precomputed (input: a p5@ ACC_addr + 200 bytes at TMP_addr
             + b p3@ B_pre_ptr; output: a_plus_b p5@ TMP_addr)
           - FElem→byte merge for ACC, TMP, B_pre (back to byte form)
           - handle_call cmov_5felems(ACC, TMP, bit) with mask = bit ∈ {0,1}
             (Note: bit-validity {0,1} requires Z.land bound proof + word.eqb cast)
           - prove invariant for n' (sep + locals + measure decrease)
       (J) Loop exit, n = 0:                    [~30 LoC]
           handle_call cmov_5felems(out, ACC, 1) — pure byte copy.
       (K) Stackalloc dealloc cascade.           [~80 LoC]
           Need to recover m' such that (out'$@out_ptr ⋆ scalar$@scalar_ptr ⋆
             B_pre$@B_pre_ptr ⋆ R)%sep m' from the post-loop sep including
           ACC bytes (200) + TMP bytes (200) at the stackalloc'd addrs.
           Provide anybytes ACC_addr 200 mStack' + map.split via the impl1
           direction of byte → anybytes (array_1_to_anybytes).
       (L) Postcondition: provide rets=nil, tr=tr, out' = out_bytes_after_final_cmov.

       Without phases (C) through (J), this proof cannot reach Qed.
       Phases (A) and (B) alone are reproducible in MCP; phases (G)-(I) are
       the hard meat (~600-800 LoC) that requires either (a) a 3-7 day session
       or (b) factoring out heavy lemmas (e.g., a generic `byte_chunk_to_felem`
       wrapper) into separate Qed'd Lemmas before re-attempting. *)
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

  (** Callee spec wiring: [fe25519_from_bytes] from Field25519_64. *)
  Local Instance spec_of_fe25519_from_bytes :
    spec_of "fe25519_from_bytes" := Field.spec_of_from_bytes.

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
      spec_of_fe25519_from_bytes functions ->
      spec_of_ed25519_scalarmult_base functions.
  Proof.
    intros functions Hf Hpar Hfb.
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
    (* Phase 1.5: extract bytes from anybytes hypotheses, convert to $@ form. *)
    destruct (Array.anybytes_to_array_1 _ _ _ Hany1) as [init_bytes [Harr1 Hlen1]].
    destruct (Array.anybytes_to_array_1 _ _ _ Hany2) as [B_pre_init [Harr2 Hlen2]].
    change (Z.to_nat 96) with 96%nat in Hlen1.
    change (Z.to_nat 120) with 120%nat in Hlen2.
    pose proof (array1_iff_eq_of_list_word_at B_pre_bytes_addr init_bytes
                  ltac:(rewrite Hlen1; cbn; Lia.lia)) as Hiff1.
    apply iff1ToEq in Hiff1. rewrite Hiff1 in Harr1.
    pose proof (array1_iff_eq_of_list_word_at B_pre_addr B_pre_init
                  ltac:(rewrite Hlen2; cbn; Lia.lia)) as Hiff2.
    apply iff1ToEq in Hiff2. rewrite Hiff2 in Harr2.
    (* Build the combined sep predicate (init ⋆ B_pre ⋆ out ⋆ scalar ⋆ R) on mCombined2. *)
    assert (HsepC1 :
      (sepclause_of_map (init_bytes$@B_pre_bytes_addr) ⋆
       sepclause_of_map (out_init$@out_ptr) ⋆
       sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep mCombined1).
    { assert (Hiff : Lift1Prop.iff1
        (sepclause_of_map (init_bytes$@B_pre_bytes_addr) ⋆
         sepclause_of_map (out_init$@out_ptr) ⋆
         sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep
        (sep (sepclause_of_map (init_bytes$@B_pre_bytes_addr))
             (sepclause_of_map (out_init$@out_ptr) ⋆
              sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep)) by cancel.
      apply Hiff.
      exists mStack1, mem. ssplit.
      - apply Properties.map.split_comm. exact Hsplit1.
      - exact Harr1.
      - exact Hsep. }
    assert (HsepC2 :
      (sepclause_of_map (init_bytes$@B_pre_bytes_addr) ⋆
       sepclause_of_map (B_pre_init$@B_pre_addr) ⋆
       sepclause_of_map (out_init$@out_ptr) ⋆
       sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep mCombined2).
    { assert (Hiff : Lift1Prop.iff1
        (sepclause_of_map (init_bytes$@B_pre_bytes_addr) ⋆
         sepclause_of_map (B_pre_init$@B_pre_addr) ⋆
         sepclause_of_map (out_init$@out_ptr) ⋆
         sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep
        (sep (sepclause_of_map (B_pre_init$@B_pre_addr))
             (sepclause_of_map (init_bytes$@B_pre_bytes_addr) ⋆
              sepclause_of_map (out_init$@out_ptr) ⋆
              sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep)) by cancel.
      apply Hiff.
      exists mStack2, mCombined1. ssplit.
      - apply Properties.map.split_comm. exact Hsplit2.
      - exact Harr2.
      - exact HsepC1. }
    (* Right-associated form needed by init_u64_seq_correct's hypothesis: *)
    assert (HsepC2_ra :
      sep (sepclause_of_map (init_bytes$@B_pre_bytes_addr))
          (sep (sepclause_of_map (B_pre_init$@B_pre_addr))
               (sep (sepclause_of_map (out_init$@out_ptr))
                    (sep (sepclause_of_map (scalar$@scalar_ptr)) R))) mCombined2).
    { assert (Hiff: Lift1Prop.iff1
        (sepclause_of_map (init_bytes$@B_pre_bytes_addr) ⋆
         sepclause_of_map (B_pre_init$@B_pre_addr) ⋆
         sepclause_of_map (out_init$@out_ptr) ⋆
         sepclause_of_map (scalar$@scalar_ptr) ⋆ R)%sep
        (sep (sepclause_of_map (init_bytes$@B_pre_bytes_addr))
             (sep (sepclause_of_map (B_pre_init$@B_pre_addr))
                  (sep (sepclause_of_map (out_init$@out_ptr))
                       (sep (sepclause_of_map (scalar$@scalar_ptr)) R))))) by cancel.
      apply Hiff. exact HsepC2. }
    (* Phase 2: peel cmd.seq for init_u64_seq, apply init_u64_seq_correct.
       The first stackalloc gives us 96 bytes at B_pre_bytes_addr;
       after init_u64_seq, those bytes are flat_map (LittleEndianList.le_split 8) B_precomputed_u64s
       which equals B_precomputed_bytes by B_precomputed_u64s_to_bytes. *)
    (* Step the cmd.seq peeling and apply init_u64_seq_correct: *)
    eapply WeakestPreconditionProperties.Proper_cmd; cycle 1.
    { eapply init_u64_seq_correct.
      - rewrite B_precomputed_u64s_length. exact Hlen1.
      - exact B_precomputed_u64s_bound.
      - Lia.lia.
      - rewrite Hlen1. cbv [Bitwidth64.BW64]. Lia.lia.
      - rewrite ?map.get_put_diff by congruence.
        rewrite map.get_put_same. reflexivity.
      - assert (Heq : word.add B_pre_bytes_addr (word.of_Z 0) = B_pre_bytes_addr) by ZnWords.
        rewrite Heq. exact HsepC2_ra.
      - intros m' Hsep'.
        (* Phase 3: rewrite flat_map → B_precomputed_bytes; normalize offset 0;
           abstract the 96-byte buffer; split into 3 × 32-byte chunks; split
           B_pre_init (120 bytes) into 3 × 40-byte FElems. *)
        rewrite B_precomputed_u64s_to_bytes in Hsep'.
        replace (word.add B_pre_bytes_addr (word.of_Z 0)) with B_pre_bytes_addr in Hsep' by ZnWords.
        remember B_precomputed_bytes as bs eqn:Hbs.
        assert (Hbs_len : Datatypes.length bs = 96%nat)
          by (rewrite Hbs; apply B_precomputed_bytes_length).
        (* Keep Hbs : bs = B_precomputed_bytes for later vm_compute on
           bytes_in_bounds (chunk32_i = firstn 32 (skipn _ B_precomputed_bytes)). *)
        set (chunk32_0 := List.firstn 32 bs).
        set (chunk32_1 := List.firstn 32 (List.skipn 32 bs)).
        set (chunk32_2 := List.skipn 64 bs).
        assert (Hc0_len : Datatypes.length chunk32_0 = 32%nat) by
          (subst chunk32_0; rewrite List.length_firstn, Hbs_len; lia).
        assert (Hc1_len : Datatypes.length chunk32_1 = 32%nat) by
          (subst chunk32_1; rewrite List.length_firstn, List.length_skipn, Hbs_len; lia).
        assert (Hc2_len : Datatypes.length chunk32_2 = 32%nat) by
          (subst chunk32_2; rewrite List.length_skipn, Hbs_len; lia).
        assert (Hbs_split : bs = (chunk32_0 ++ chunk32_1 ++ chunk32_2)%list).
        { subst chunk32_0 chunk32_1 chunk32_2.
          rewrite <- (List.firstn_skipn 32 bs) at 1; f_equal.
          rewrite <- (List.firstn_skipn 32 (ListDef.skipn 32 bs)) at 1.
          f_equal. rewrite skipn_skipn. f_equal. }
        rewrite Hbs_split in Hsep' at 1.
        epose proof (SeparationMemory.sep_eq_of_list_word_at_app B_pre_bytes_addr
                       chunk32_0 (chunk32_1 ++ chunk32_2)%list 32
                       ltac:(rewrite Hc0_len; reflexivity)
                       ltac:(rewrite Hc0_len, !List.length_app, Hc1_len, Hc2_len; cbv [Bitwidth64.BW64]; lia)) as Hs0.
        apply iff1ToEq in Hs0; rewrite Hs0 in Hsep'; clear Hs0.
        epose proof (SeparationMemory.sep_eq_of_list_word_at_app
                       (word.add B_pre_bytes_addr (word.of_Z 32))
                       chunk32_1 chunk32_2 32
                       ltac:(rewrite Hc1_len; reflexivity)
                       ltac:(rewrite Hc1_len, Hc2_len; cbv [Bitwidth64.BW64]; lia)) as Hs1.
        apply iff1ToEq in Hs1; rewrite Hs1 in Hsep'; clear Hs1.
        replace (word.add (word.add B_pre_bytes_addr (word.of_Z 32)) (word.of_Z 32)) with
          (word.add B_pre_bytes_addr (word.of_Z 64)) in Hsep' by ring.
        (* Phase 4: split B_pre_init (120 raw bytes) into 3 × 40-byte raw chunks.

           NB: The previous attempt used [BytesToFelem3.byte_3felem_iff] to
           convert bytes → FElem here.  That was WRONG — spec_of_from_bytes
           wants the output buffer in raw [out$@pout] form, and only gives
           back [FElem pout X] AFTER the call.  Pre-converting to FElem
           breaks the precondition shape.

           Approach: keep raw bytes, split via sep_eq_of_list_word_at_app. *)
        set (chunk40_0 := List.firstn 40 B_pre_init).
        set (chunk40_1 := List.firstn 40 (List.skipn 40 B_pre_init)).
        set (chunk40_2 := List.skipn 80 B_pre_init).
        assert (Hb0_len : Datatypes.length chunk40_0 = 40%nat) by
          (subst chunk40_0; rewrite List.length_firstn, Hlen2; lia).
        assert (Hb1_len : Datatypes.length chunk40_1 = 40%nat) by
          (subst chunk40_1; rewrite List.length_firstn, List.length_skipn, Hlen2; lia).
        assert (Hb2_len : Datatypes.length chunk40_2 = 40%nat) by
          (subst chunk40_2; rewrite List.length_skipn, Hlen2; lia).
        assert (Hb_split : B_pre_init = (chunk40_0 ++ chunk40_1 ++ chunk40_2)%list).
        { subst chunk40_0 chunk40_1 chunk40_2.
          rewrite <- (List.firstn_skipn 40 B_pre_init) at 1; f_equal.
          rewrite <- (List.firstn_skipn 40 (ListDef.skipn 40 B_pre_init)) at 1.
          f_equal. rewrite skipn_skipn. f_equal. }
        rewrite Hb_split in Hsep' at 1.
        epose proof (SeparationMemory.sep_eq_of_list_word_at_app B_pre_addr
                       chunk40_0 (chunk40_1 ++ chunk40_2)%list 40
          ltac:(rewrite Hb0_len; reflexivity)
          ltac:(rewrite Hb0_len, !List.length_app, Hb1_len, Hb2_len;
                cbv [Bitwidth64.BW64]; lia)) as Hb0.
        apply iff1ToEq in Hb0; rewrite Hb0 in Hsep'; clear Hb0.
        epose proof (SeparationMemory.sep_eq_of_list_word_at_app
                       (word.add B_pre_addr (word.of_Z 40))
                       chunk40_1 chunk40_2 40
          ltac:(rewrite Hb1_len; reflexivity)
          ltac:(rewrite Hb1_len, Hb2_len; cbv [Bitwidth64.BW64]; lia)) as Hb1.
        apply iff1ToEq in Hb1; rewrite Hb1 in Hsep'; clear Hb1.
        replace (word.add (word.add B_pre_addr (word.of_Z 40)) (word.of_Z 40)) with
          (word.add B_pre_addr (word.of_Z 80)) in Hsep' by ring.
        (* Phase 5: peel cmd.seq via cbn [cmd_body] to expose 3 from_bytes calls
           + 1 parametric call as nested [exists args, dexprs ⋆ call] structure. *)
        cbn [cmd_body].
        (* Phase 6 (incomplete): 1st from_bytes(B_pre, B_pre_bytes) call.

           Working session 2026-05-04 (5h budget) — partial progress:

           PHASE 4 FIX (committed): Replaced prior agent's incorrect use of
           [BytesToFelem3.byte_3felem_iff] (which converts raw 120 bytes to
           3 FElems) with [SeparationMemory.sep_eq_of_list_word_at_app]
           splits.  Result: Hsep' now has 3 × 40 raw bytes at B_pre_addr +
           (0/40/80) — matches the [out$@pout] shape spec_of_from_bytes
           expects for the OUTPUT.

           PHASE 6 PROGRESS in MCP: Verified the proof CAN advance from
           here.  dexprs discharge + [straightline_call] both work cleanly.
           After straightline_call, [ssplit] produces 4 precondition goals:
             (1) exists Ra, (array ptsto _ B_pre_bytes_addr ?bs ⋆ Ra) m'
             (2) (?out$@B_pre_addr ⋆ ?Rr) m'
             (3) length ?out = Z.to_nat felem_size_in_bytes
             (4) bytes_in_bounds ?bs

           Goal (1) closes via:
             eexists. instantiate (2 := chunk32_0). setoid_rewrite
             (array1_iff_eq_of_list_word_at B_pre_bytes_addr chunk32_0).
             ecancel_assumption.

           Goal (2) needs ?out := chunk40_0; [instantiate (1 := chunk40_0)]
           keeps picking ?Rr instead of ?out — needs explicit unification
           via [refine] or rewrite-then-ecancel.  ~30-60 min to find.

           Goal (3) closes via [change (Z.to_nat felem_size_in_bytes) with
           40%nat; exact Hb0_len].

           Goal (4) [bytes_in_bounds chunk32_0]: chunk32_0 is
           [firstn 32 B_precomputed_bytes] (rewritable via Hbs).  Pattern:
           [unfold bytes_in_bounds, frep25519, ...; cbv; ssplit] per
           ristretto_scalarmult_ok lines 201-214.

           Remaining work:
             - Goal 2-4 above (~1-2 hours).
             - Post-call continuation: extract FElem at B_pre_addr from
               post hypothesis [H : a1 = nil /\ tr = a /\ exists X, ...].
               Then [exists nil. ssplit. { reflexivity. } { ...next call...}].
             - Repeat for 2nd and 3rd from_bytes (B_pre+40, B_pre+80).
             - Re-merge 3 FElems → 120 raw bytes via felem_to_bytearray +
               sep_eq_of_list_word_at_app reverse.
             - Parametric call via Hpar.
             - Dealloc cascade: byte_buffer_to_anybytes_120 + _96.
             - Final post: rets=nil, tr=tr, out_bytes=out', length=200.
           Estimated 3-5 additional hours. *)
        admit. }
    intros tr' m' l' Hpost. exact Hpost.
  Admitted.

End ScalarmultImpl64.
