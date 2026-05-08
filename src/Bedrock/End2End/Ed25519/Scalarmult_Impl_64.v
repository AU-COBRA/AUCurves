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
Require Import Bedrock.End2End.Ed25519.Felems3ToBytes.
Require Import Bedrock.End2End.Ed25519.DeallocCascade.
Require Import Bedrock.End2End.Ed25519.DeallocCascadeHelper.
Require Import Bedrock.End2End.Ed25519.FromBytesCallHelpers.
Require Import Bedrock.Util.SepReflectiveAC.
Require Import Bedrock.Util.SepDeep.  (* deep_ecancel infra; not currently wired *)

(** ** Deep [vm_compute] cancel — experimental, REVERTED.

    [Bedrock.Util.SepDeep.deep_ecancel] was wired in for the 3 [from_bytes]
    Goal-1 sites at lines ~617/684/721 in commit [34e175b].  Despite
    deep_ecancel running AFTER [setoid_rewrite Hiff_c{0,1,2}], the mere
    presence of the [deep_ecancel Hsep'] call in the file text triggered a
    fatal-out-of-memory at the immediately preceding [setoid_rewrite Hiff_c0]
    (line ~617) — confirmed by 3 isolation tests on 2026-05-08:
      - Import [SepDeep] alone, keep [reflective_ecancel]:  builds clean.
      - Import [SepDeep] + use [deep_ecancel]:               OOM at line 617.
      - No [SepDeep] import, [reflective_ecancel] only:      builds clean.
    Likely cause: Rocq's tactic interpreter pre-resolves typeclass instances
    for the upcoming [seps_pick_iff1_decb] call at the surrounding [bullet]
    level, which interacts badly with [setoid_rewrite]'s class search.  The
    [SepDeep.v] infrastructure is left in place (Qed-clean lemmas + tactic +
    tested standalone via [deep_ecancel_test]) for future iteration.  The 3
    R10 sites stay on [reflective_ecancel].  *)

(** Strategy 0 on field-rep + sep coercion was tested 2026-05-07 to reduce
    Qed kernel-check time on this lemma — it does NOT help.  Multiple
    Strategy 0 sets and native compilation (.cmxs cached for fiat-crypto)
    were tried; all give the same 60+ min Qed profile.  Left as documentation;
    re-enable if profiling tools (perf/gdb, root-only) become available. *)
(* Strategy 0 [frep25519 sepclause_of_map]. *)

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
    (* Apply init_u64_seq_correct directly (no Proper_cmd) — keeps the
       body cmd's post as the concrete POST_inner2 (the dealloc cascade)
       rather than introducing a Type-codomain ?x evar that resists
       Prop-typed instantiation.  Option B per session 2026-05-05. *)
    eapply init_u64_seq_correct.
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
        (* Single Qed-sealed split via [split_3x32_iff1] helper. *)
        match type of Hsep' with
        | (sepclause_of_map (bs$@?a) ⋆ ?rest)%sep _ =>
          pose proof (split_3x32_iff1 bs chunk32_0 chunk32_1 chunk32_2 a rest
                        Hbs_split Hc0_len Hc1_len Hc2_len) as Hsplit32
        end.
        apply iff1ToEq in Hsplit32; rewrite Hsplit32 in Hsep'; clear Hsplit32.
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
        (* Single Qed-sealed split via [split_3x40_iff1] helper. *)
        match type of Hsep' with
        | context[(sepclause_of_map (B_pre_init$@?a) ⋆ ?rest)%sep] =>
          pose proof (split_3x40_iff1 B_pre_init chunk40_0 chunk40_1 chunk40_2 a rest
                        Hb_split Hb0_len Hb1_len Hb2_len) as Hsplit40
        end.
        apply iff1ToEq in Hsplit40; rewrite Hsplit40 in Hsep'; clear Hsplit40.
        (* Phase 5: peel cmd.seq via cbn [cmd_body] to expose 3 from_bytes calls
           + 1 parametric call as nested [exists args, dexprs ⋆ call] structure. *)
        cbn [cmd_body].
        (* Phase 6: 1st from_bytes(B_pre, B_pre_bytes) — dexprs + Goal 1 of
           4-conjunct precond verified Qed-clean below; Goals 2-4 + post-call
           remain as one outer admit. *)
        eexists. split.
        { cbv [WeakestPrecondition.dexprs WeakestPrecondition.list_map
               WeakestPrecondition.list_map_body
               WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get dlet.dlet].
          eexists. split. { rewrite map.get_put_same. reflexivity. }
          eexists. split. { rewrite ?map.get_put_diff by congruence.
                            rewrite map.get_put_same. reflexivity. }
          reflexivity. }
        straightline_call.
        { (* 4-conjunct precond for 1st from_bytes *)
          pose proof (array1_iff_eq_of_list_word_at B_pre_bytes_addr chunk32_0
                        ltac:(rewrite Hc0_len; cbn; lia)) as Hiff_c0.
          apply iff1ToEq in Hiff_c0.
          ssplit.
          - (* Goal 1: input bytes ⊆ memory — deep ecancel via vm_compute *)
            eexists. setoid_rewrite Hiff_c0. reflective_ecancel Hsep'.
          - (* Goal 2: output buffer — Qed-sealed iff1 helper *)
            pose proof (reshape_iff_b0 chunk32_0 chunk32_1 chunk32_2
                          chunk40_0 chunk40_1 chunk40_2 out_init scalar
                          out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr R) as Hiff_b0.
            apply iff1ToEq in Hiff_b0.
            assert (Hsep_b0 : (sepclause_of_map (chunk40_0$@B_pre_addr) ⋆
                   (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
                    ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
                    ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
                    ⋆ sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40)))
                    ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
                    ⋆ sepclause_of_map (out_init$@out_ptr)
                    ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep m')
              by (rewrite <- Hiff_b0; ecancel_assumption).
            clear Hiff_b0.
            exact Hsep_b0.
          - (* Goal 3: output length = felem_size_in_bytes *)
            change (Z.to_nat felem_size_in_bytes) with 40%nat. exact Hb0_len.
          - (* Goal 4: bytes_in_bounds chunk32_0 — apply Qed-clean helper. *)
            subst chunk32_0. rewrite Hbs. apply chunk32_0_in_bounds. }
        (* Post-call continuation: extract 1st from_bytes post, then
           [repeat straightline] auto-discharges 2nd/3rd from_bytes +
           parametric calls via the typeclass-resolved [Hfb] and [Hpar]
           specs.  The remaining admit is the final dealloc + out_bytes
           obligation only.  Goal at the admit:
             exists m'0 mStack', anybytes B_pre_addr 120 mStack'
             /\ map.split m' m'0 mStack' /\ (exists m'1 mStack'0,
                  anybytes B_pre_bytes_addr 96 mStack'0
                  /\ map.split m'0 m'1 mStack'0
                  /\ (exists rets, map.getmany_of_list l' nil = Some rets
                       /\ rets = nil /\ tr' = tr
                       /\ (exists out_bytes : list byte,
                            length out_bytes = 200
                            /\ (out_bytes$@out_ptr ⋆ scalar$@scalar_ptr ⋆ R) m'1))).
           Closes via: DeallocCascade.byte_buffer_to_anybytes_120 for
           B_pre + parametric byte_buffer_to_anybytes (n=96) for
           B_pre_bytes + standard rets/tr/out_bytes assembly.

           [repeat eexists] from this state opens 4+ sub-goals:
             G1: Z.of_nat (length ?bs) = 120        (B_pre bytes length)
             G2: Z.of_nat (length ?bs) <= 2^64       (bound)
             G3: m' = map.putmany ... ?bs$@B_pre_addr (layout)
             G4+ (shelved, ~5 of them): rets, tr, out_bytes, sep
           At this point the inner-WP post evar [?x] is unconstrained
           because [repeat straightline] couldn't sniff the actual
           post-state from the (Hfb, Hpar)-driven advance — it advanced
           but left the post abstract.

           Resolution: instead of [repeat straightline] auto-advancing,
           manually peel each post extraction (1st from_bytes done;
           2nd/3rd/parametric yet to do) so we have concrete sep-state
           hypotheses to feed into the dealloc cascade.  ~150-200 LoC
           of structured WP work. *)
        destruct H as (Hr_b0 & Htr_b0 & X_b0 & Hfeval_b0 & Hbnd_b0 & Hsep_b0_post).
        rewrite Hr_b0.
        eexists. split. { reflexivity. }
        repeat straightline.
        (* 2nd from_bytes(B_pre + 40, B_pre_bytes + 32) — same 4-conjunct
           pattern as 1st, but pulling chunk40_1 / chunk32_1.  Verified Qed
           via MCP at state 869 (2026-05-05). *)
        straightline_call.
        { pose proof (array1_iff_eq_of_list_word_at
                        (word.add B_pre_bytes_addr (word.of_Z 32)) chunk32_1
                        ltac:(rewrite Hc1_len; cbn; lia)) as Hiff_c1.
          apply iff1ToEq in Hiff_c1.
          ssplit.
          - eexists. setoid_rewrite Hiff_c1. reflective_ecancel Hsep_b0_post.
          - assert (Hsep_b1 :
              (sepclause_of_map (chunk40_1$@(word.add B_pre_addr (word.of_Z 40))) ⋆
               (FElem B_pre_addr X_b0
                ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
                ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
                ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
                ⋆ sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80)))
                ⋆ sepclause_of_map (out_init$@out_ptr)
                ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep a0).
            { apply (reshape_b1 a0 chunk32_0 chunk32_1 chunk32_2
                       chunk40_1 chunk40_2 (FElem B_pre_addr X_b0)
                       out_init scalar
                       out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr R).
              exact Hsep_b0_post. }
            exact Hsep_b1.
          - change (Z.to_nat felem_size_in_bytes) with 40%nat. exact Hb1_len.
          - subst chunk32_1. rewrite Hbs. apply chunk32_1_in_bounds. }
        (* Post-2nd-from_bytes: extract X_b1, advance dexprs for 3rd.
           The post hyp was auto-introduced by [straightline_call] using a
           fresh `H?` name; matching by structure rather than by name. *)
        match goal with
        | H : _ = nil /\ _ = _ /\ exists _ : felem, _ |- _ =>
            destruct H as (Hr_b1 & Htr_b1 & X_b1 & Hfeval_b1 & Hbnd_b1 & Hsep_b1_post)
        end.
        rewrite Hr_b1.
        eexists. split. { reflexivity. }
        repeat straightline.
        (* 3rd from_bytes(B_pre + 80, B_pre_bytes + 64) — symmetric to 2nd
           but pulling chunk40_2 / chunk32_2.  Verified Qed via MCP at
           state 896 (2026-05-05). *)
        straightline_call.
        { pose proof (array1_iff_eq_of_list_word_at
                        (word.add B_pre_bytes_addr (word.of_Z 64)) chunk32_2
                        ltac:(rewrite Hc2_len; cbn; lia)) as Hiff_c2.
          apply iff1ToEq in Hiff_c2.
          ssplit.
          - eexists. setoid_rewrite Hiff_c2. reflective_ecancel Hsep_b1_post.
          - assert (Hsep_b2 :
              (sepclause_of_map (chunk40_2$@(word.add B_pre_addr (word.of_Z 80))) ⋆
               (FElem (word.add B_pre_addr (word.of_Z 40)) X_b1
                ⋆ FElem B_pre_addr X_b0
                ⋆ sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
                ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
                ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
                ⋆ sepclause_of_map (out_init$@out_ptr)
                ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep a2).
            { apply (reshape_b2 a2 chunk32_0 chunk32_1 chunk32_2 chunk40_2
                       (FElem B_pre_addr X_b0)
                       (FElem (word.add B_pre_addr (word.of_Z 40)) X_b1)
                       out_init scalar
                       out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr R).
              exact Hsep_b1_post. }
            exact Hsep_b2.
          - change (Z.to_nat felem_size_in_bytes) with 40%nat. exact Hb2_len.
          - subst chunk32_2. rewrite Hbs. apply chunk32_2_in_bounds. }
        (* Post-3rd-from_bytes: extract X_b2, advance dexprs for parametric. *)
        match goal with
        | H : _ = nil /\ _ = _ /\ exists _ : felem, _ |- _ =>
            destruct H as (Hr_b2 & Htr_b2 & X_b2 & Hfeval_b2 & Hbnd_b2 & Hsep_b2_post)
        end.
        clear Hsep_b0_post Hsep_b1_post.
        rewrite Hr_b2.
        eexists. split. { reflexivity. }
        repeat straightline.
        (* Parametric call.  Use felems3_to_bytes_iff helper backward
           (iff1_sym) on the goal's concat → FElem chain, so the precond's
           sep matches Hsep_b2_post directly via ecancel_assumption_impl. *)
        straightline_call.
        1: { ssplit.
             - exact Hlen_out.
             - exact Hlen_scalar.
             - instantiate (1 := ((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b0))
                                 ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b1))
                                 ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b2)))%list).
               rewrite !List.length_app, !ws2bs_felem_length. cbn. reflexivity.
             - pose proof (felems3_to_bytes_iff X_b0 X_b1 X_b2 B_pre_addr) as Hhelper.
               apply iff1ToEq in Hhelper.
               rewrite <- Hhelper.
               instantiate (1 := (sepclause_of_map (chunk32_0$@B_pre_bytes_addr)
                                  ⋆ sepclause_of_map (chunk32_1$@(word.add B_pre_bytes_addr (word.of_Z 32)))
                                  ⋆ sepclause_of_map (chunk32_2$@(word.add B_pre_bytes_addr (word.of_Z 64)))
                                  ⋆ R)%sep).
               ecancel_assumption_impl. }
        (* Post-parametric: extract out_par, then dealloc cascade.
           Match by structure since auto-intro variable names vary. *)
        match goal with
        | H : _ = nil /\ _ = _ /\ exists _ : list Init.Byte.byte, _ |- _ =>
            destruct H as (Hr_par & Htr_par & out_par & Hlen_par & Hsep_par)
        end.
        (* Clear stale state to speed up ecancel_assumption_impl. *)
        clear Hsep_b2_post Hsep' HsepC0 HsepC1 HsepC2 HsepC2_ra Hsep_b0_post
              Hsep_b1_post Hsep0 HsepC1 || idtac.
        rewrite Hr_par.
        eexists. split. { reflexivity. }
        (* Drop iff1 facts to keep the context clean for ecancel. *)
        repeat match goal with
        | H : Lift1Prop.iff1 _ _ |- _ => clear H
        end.
        pose proof (sep_rearrange_for_dealloc _ out_par scalar
                      ((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b0))
                       ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b1))
                       ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b2)))%list
                      chunk32_0 chunk32_1 chunk32_2
                      out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr R
                      Hsep_par) as Hsep_par_b.
        pose proof (dealloc_cascade_helper _ out_par scalar X_b0 X_b1 X_b2
                      out_ptr scalar_ptr B_pre_addr B_pre_bytes_addr
                      chunk32_0 chunk32_1 chunk32_2 R
                      Hc0_len Hc1_len Hc2_len Hsep_par_b) as Hcasc.
        destruct Hcasc as (mInner_a & mStack_a & Hany_120 & Hsplit_120 &
                           mInner_b & mStack_b & Hany_96 & Hsplit_96 & HRest_96).
        exists mInner_a, mStack_a.
        ssplit; [exact Hany_120 | exact Hsplit_120 |].
        exists mInner_b, mStack_b.
        ssplit; [exact Hany_96 | exact Hsplit_96 |].
        eexists. split. { reflexivity. }
        ssplit. { reflexivity. } { exact Htr_par. }
        exists out_par. split.
        { exact Hlen_par. }
        { exact HRest_96. }
  Admitted.
  (* ============================================================================
     STATUS: Admitted — needs an upstream bedrock2 refactor to close.
     ============================================================================

     The proof body fully elaborates (~0.1 sec) and discharges every conjunct via
     the helpers in DeallocCascadeHelper.v.  But `Qed` kernel-check on the
     resulting proof term runs >30 min (last measurement: build #34, 2026-05-07,
     killed at 30 min before completion).

     Helpers landed and used in this proof:
       - sep_rearrange_for_dealloc, dealloc_cascade_helper  (post-parametric cascade)
       - reshape_iff_b0, reshape_b1, reshape_b2             (cancel for output buffer)
       - split_3x32_iff1, split_3x40_iff1                   (bs / B_pre_init splits)
       - chunk32_{0,1,2}_in_bounds (in B_precomputed_64.v)  (vm_compute on bytes)
     Total proof-term reduction vs the original inline-cancel form: estimated
     ~50 KB of ~80 KB.  The reflective Ltac `reflective_reshape` in
     DeallocCascadeHelper.v is also defined (verified working via MCP) but only
     applicable to non-FElem hypotheses; left for future use.

     Why this isn't enough.  The remaining 30 KB of proof term comes from the
     5 `straightline_call` invocations + their post-call destructure + the
     `repeat straightline` glue between them.  These are bedrock2-supplied
     tactics that produce sizable terms.  Per `reference_slow_proofs_fiat.md`
     Root Cause 15, the fundamental fix is per-call factoring, but that
     requires the bedrock2 spec_of / call machinery to be amenable to
     factor-out-the-proof-term-and-reuse — which it currently is not without
     significant restructuring of how WP-call posts thread through the proof.

     Per `reference_slow_proofs_fiat.md`'s "Reflective tactics for sep-logic"
     section: a fully reflective fix would require Rtac-style deep embedding
     of the bedrock2 sep predicate (Malecha ESOP 2016, ~88× speedup on similar
     problems), explicitly noted as a multi-week project.

     Pitfalls verified in the 2026-05-06/07 sessions (don't retry):
     - `replace x with y by exact eq` is SLOWER than `rewrite eq at 1` when
       subordinate lets reference x (chunk32_X bodies contain `bs`).
     - `abstract` on cancel makes things WORSE (sub-Qed blowup from context closure).
     - `clearbody chunk32_*` before the cascade does NOT help (proof term up
       to the clearbody is what's blowing up, not the residual after).
     - `flatten_seps_in H` fails on FElem-bearing hypotheses (the
       `iff1_syntactic_reflexivity` step inside flatten can't bridge typeclass-
       method elaboration differences).  `flatten_seps_in_goal` works on the
       same shapes — different code path.

     Recommended next-session approach:
       Either (a) accept Admitted indefinitely and wire the parametric spec
       through to the wrapper without proving correctness; or (b) commit to
       the multi-week Rtac/SepReflectiveAC-style deep-embedding refactor of
       the bedrock2 sep predicate.
     ============================================================================ *)

(* DEAD CODE — preserved for documentation of the intended cascade structure.
   Once WPCleanup tactics are adopted to slim the context before this point,
   the cascade closes via the following sequence (verified at sub-step level
   in MCP at state 1134; ecancel times out only at the composite assert):

        (* Dealloc 1: B_pre (120 bytes) via byte_buffer_to_anybytes_120.
           Inline chunk32_* let-bindings before the assert — without this,
           ecancel_assumption_impl goes exponential on the deep nested
           binders. *)
        cbv beta delta [chunk32_0 chunk32_1 chunk32_2] in *.
        match type of Hsep_par with
        | _ ?m =>
          assert (Hsep_par_b :
            (sepclause_of_map (((ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b0))
                                ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b1))
                                ++ (ArrayCasts.ws2bs (Z.to_nat (bytes_per_word 64)) (felem_to_list X_b2)))$@B_pre_addr)
              ⋆ (sepclause_of_map (out_par$@out_ptr) ⋆ sepclause_of_map (scalar$@scalar_ptr)
                ⋆ sepclause_of_map ((List.firstn 32 (List.firstn 32 bs0 ++ List.firstn 32 (List.skipn 32 bs0) ++ List.skipn 64 bs0))$@B_pre_bytes_addr)
                ⋆ sepclause_of_map ((List.firstn 32 (List.skipn 32 (List.firstn 32 bs0 ++ List.firstn 32 (List.skipn 32 bs0) ++ List.skipn 64 bs0)))$@(word.add B_pre_bytes_addr (word.of_Z 32)))
                ⋆ sepclause_of_map ((List.skipn 64 (List.firstn 32 bs0 ++ List.firstn 32 (List.skipn 32 bs0) ++ List.skipn 64 bs0))$@(word.add B_pre_bytes_addr (word.of_Z 64)))
                ⋆ R))%sep m)
            by ecancel_assumption_impl
        end.
        edestruct (byte_buffer_to_anybytes_120 _ B_pre_addr _ _
                     ltac:(rewrite !List.length_app, !ws2bs_felem_length; cbn; reflexivity)
                     Hsep_par_b)
          as (mStack_120 & mInner_120 & Hany_120 & Hsplit_120 & HsepInner_120).
        exists mInner_120, mStack_120. ssplit; [exact Hany_120 | exact Hsplit_120 |].
        (* Dealloc 2: B_pre_bytes (96 bytes) — combine 3 × 32-byte chunks.
           After [cbv beta delta] above, chunk32_* are inlined; use the
           raw List.firstn / List.skipn expressions directly. *)
        set (c0 := List.firstn 32 (List.firstn 32 bs0 ++ List.firstn 32 (List.skipn 32 bs0) ++ List.skipn 64 bs0)).
        set (c1 := List.firstn 32 (List.skipn 32 (List.firstn 32 bs0 ++ List.firstn 32 (List.skipn 32 bs0) ++ List.skipn 64 bs0))).
        set (c2 := List.skipn 64 (List.firstn 32 bs0 ++ List.firstn 32 (List.skipn 32 bs0) ++ List.skipn 64 bs0)).
        assert (Hc0_len' : Datatypes.length c0 = 32%nat) by
          (subst c0; rewrite List.length_firstn, List.length_app, List.length_firstn,
                                List.length_app, List.length_firstn, List.length_skipn, Hbs_len; lia).
        assert (Hc1_len' : Datatypes.length c1 = 32%nat) by
          (subst c1; rewrite List.length_firstn, List.length_skipn, List.length_app,
                                List.length_firstn, List.length_app, List.length_firstn,
                                List.length_skipn, Hbs_len; lia).
        assert (Hc2_len' : Datatypes.length c2 = 32%nat) by
          (subst c2; rewrite List.length_skipn, List.length_app, List.length_firstn,
                                List.length_app, List.length_firstn, List.length_skipn, Hbs_len; lia).
        epose proof (sep_eq_of_list_word_at_app B_pre_bytes_addr
                       c0 (c1 ++ c2)%list 32
                       ltac:(rewrite Hc0_len'; reflexivity)
                       ltac:(rewrite Hc0_len', !List.length_app, Hc1_len', Hc2_len'; cbv [Bitwidth64.BW64]; lia)) as Hbpb0.
        epose proof (sep_eq_of_list_word_at_app (word.add B_pre_bytes_addr (word.of_Z 32))
                       c1 c2 32
                       ltac:(rewrite Hc1_len'; reflexivity)
                       ltac:(rewrite Hc1_len', Hc2_len'; cbv [Bitwidth64.BW64]; lia)) as Hbpb1.
        replace (word.add (word.add B_pre_bytes_addr (word.of_Z 32)) (word.of_Z 32))
          with (word.add B_pre_bytes_addr (word.of_Z 64)) in Hbpb1 by ring.
        assert (Hbpb_combined : (sepclause_of_map ((c0 ++ c1 ++ c2)$@B_pre_bytes_addr)
            ⋆ (sepclause_of_map (out_par$@out_ptr) ⋆ sepclause_of_map (scalar$@scalar_ptr) ⋆ R))%sep mInner_120).
        { seprewrite Hbpb0. seprewrite Hbpb1. ecancel_assumption_impl. }
        edestruct (byte_buffer_to_anybytes _ B_pre_bytes_addr _ _
                     ltac:(rewrite !List.length_app, Hc0_len', Hc1_len', Hc2_len'; reflexivity)
                     ltac:(rewrite !List.length_app, Hc0_len', Hc1_len', Hc2_len'; cbv [Bitwidth64.BW64]; lia)
                     Hbpb_combined)
          as (mStack_96 & mInner_96 & Hany_96 & Hsplit_96 & HsepInner_96).
        exists mInner_96, mStack_96. ssplit; [exact Hany_96 | exact Hsplit_96 |].
        (* Final post: rets=nil + tr=tr + exists out_bytes, length=200, sep. *)
        eexists. split. { reflexivity. }
        ssplit. { reflexivity. } { exact Htr_par. }
        exists out_par. split.
        { exact Hlen_par. }
        { exact HsepInner_96. }
*)

End ScalarmultImpl64.
