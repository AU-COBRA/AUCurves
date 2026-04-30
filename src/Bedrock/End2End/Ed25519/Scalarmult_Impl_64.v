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
    (* Expand the [call] goal: provide argnames/retnames/body witnesses via
       Hf, then provide the locals map and unfold to [exec] over body. *)
    unfold call.
    do 3 eexists. split; [exact Hf|].
    eexists. split; [reflexivity|].
    (* Now in [exec functions body tr mem locals post] form.
       Plan:
       1. straightline through both stackallocs (96 + 120 bytes).
       2. Process the [coq:(init_u64_seq ...)] sequence: 12 word stores.
          NEEDS [init_u64_seq_correct] forward lemma proved by induction
          on the u64 list. After invocation, the 96-byte buffer at
          B_pre_bytes contains [flat_map (le_split 8) B_precomputed_u64s
          = B_precomputed_bytes] (via [B_precomputed_u64s_to_bytes]).
       3. handle_call fe25519_from_bytes_correct × 3 to convert each
          32-byte chunk to 40-byte limb form.
       4. handle_call ed25519_scalarmult_base_parametric_correct (Hpar).
       5. Stackalloc dealloc cascade for B_pre / B_pre_bytes.
       6. Postcondition: existence of out_bytes from parametric postcondition. *)
  Admitted.

End ScalarmultImpl64.
