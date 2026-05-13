(** * TrustAxioms — registry of every cross-tool trust assumption in
      the AUCurves verified Signal pipeline.

      This file lists, in one place, every axiom that connects our
      Rocq verification chain to facts proved in another formalism
      (EasyCrypt, Lean, EC-extracted Jasmin) OR to external runtime
      components (rustc, the host CPU).

      Goal: a downstream auditor can run [Print Assumptions] on the
      top-level Signal-protocol correctness theorem and cross-check
      every axiom against this registry, where each entry has:

      - A NAME (greppable across files).
      - A STATEMENT (what's asserted).
      - PROVENANCE (which other tool has the proof, with file:line).
      - AUDIT CHECKLIST (concrete steps to re-validate).

      An axiom is "closed" when ALL audit checklist items pass.
      No axiom in this registry is closed today; all are flagged as
      currently-trusted.

      Maintained per-session.  Last update: 2026-05-13.
 *)

From Bedrock Require Import RustCmdToRustSimulates LibjadeAxioms.

(* ================================================================ *)
(* §1.  Rocq IR → emitted Rust source                                *)
(* ================================================================ *)

(** [RustcExec_correct] — the SOLE axiom of [RustCmdToRustSimulates.v].

    Statement: for any rust_cmd_ed program [body], the opaque
    [RustcExec] relation on the emitted Rust source matches
    [rust_exec_ed] (our Rocq IR semantics).

    Provenance: NONE in Rocq.  Provable in:
    - Lean side: [JasminToRustEmitSimulates.RustcExec_correct] — has
      the SAME axiom (same shape), discharged identically (a 1-line
      Qed depending on the axiom).  Cross-formalism agreement only.
    - To make this a real theorem, we'd need:
      (a) A Rocq model of Rust source semantics (MiniRust / Aeneas /
          RustBelt port), OR
      (b) Translate the IR to bedrock2/Jasmin and use the Rocq
          Jasmin compiler chain (which IS Rocq-Qed).  This works for
          the algorithmic content; the residual gap is "rustc's output
          on our string matches Jasmin's output on the same algorithm,"
          which collapses if we go all-Jasmin.

    Audit checklist:
    [ ] [Print Assumptions print_module_preserves_semantics] shows
        exactly RustcExec_correct?
    [ ] Lean side states the same shape?
    [ ] rs_func_emit is structural string-concat (see reflexivity
        lemmas in RustCmdToRustSimulates.v §4)?
 *)
Check @RustcExec_correct.

(* ================================================================ *)
(* §2.  libjade Jasmin primitives                                    *)
(* ================================================================ *)

(** All [jade_*_correct] axioms from [LibjadeAxioms.v]:
    - [jade_hash_sha256_correct] — SHA-256
    - [jade_hash_sha512_correct] — SHA-512
    - [jade_curve25519_x25519_correct] — X25519 variable-base
    - [jade_curve25519_x25519_base_correct] — X25519 base-point
    - [jade_mlkem768_keypair_derand_correct] — ML-KEM-768 keygen
    - [jade_mlkem768_enc_derand_correct] — ML-KEM-768 encaps
    - [jade_mlkem768_dec_correct] — ML-KEM-768 decaps

    Provenance: EasyCrypt proofs in libjade/proof/...  (cited per axiom).
    formosa-mlkem for ML-KEM proofs.

    Audit checklist (per axiom): see [LibjadeAxioms.v]. *)
Check @jade_hash_sha256_correct.
Check @jade_hash_sha512_correct.
Check @jade_curve25519_x25519_correct.
Check @jade_curve25519_x25519_base_correct.
Check @jade_mlkem768_keypair_derand_correct.
Check @jade_mlkem768_enc_derand_correct.
Check @jade_mlkem768_dec_correct.

(* ================================================================ *)
(* §3.  Section hypotheses (per-theorem, NOT global axioms)          *)
(* ================================================================ *)

(** The following are NOT axioms but [Section Hypothesis]s used by the
    four functional-correctness theorems.  After Section closure, they
    become explicit theorem parameters — visible in the theorem's
    type signature, NOT in [Print Assumptions] output.

    Listed here for audit completeness.

    [Fe25519InvertCorrect.v] (Closed under global context):
    - sqr_correct, mul_correct, copy_correct, scalar_set_preserves_holds,
      let_zero_preserves_holds (5 leaf-algebra + frame hypotheses)

    [Scalar25519FromWideCorrect.v] (Closed):
    - from_bytes_mod_order_correct, mul_correct, add_correct,
      negate_correct, setbytes_extra_correct, setbytes_sixteen_correct,
      let_zero_preserves_holds_FpL, let_zero_preserves_holds_B32, c256_eq
      (9 hypotheses)

    [MontToEdwardsCorrect.v] (Closed):
    - one_correct, add_correct, sub_correct, mul_correct, invert_correct
      (reuses fe25519_invert_correct), encode_y_length, to_bytes_correct,
      set_sign_bit_correct, let_zero_preserves_holds_Fp,
      let_zero_preserves_holds_B32 (10 hypotheses)

    [BuildCombTableCorrect.v] (Closed):
    - comb_cell_set_correct, point_mul16_correct, copy_correct,
      let_zero_preserves_cell, let_zero_preserves_fp,
      scalar_set_preserves_cell, scalar_set_preserves_fp,
      epoint_smul_one, epoint_smul_compose, Cell_holds_eq, Fp_holds_eq
      (11 hypotheses)

    Per the [Print Assumptions] discipline, these are NOT trusted —
    they're parameters of the theorem.  Concrete instantiations
    (e.g., [Sign_Verify_RustCmd.v]) discharge them. *)

(* ================================================================ *)
(* §4.  External runtime trust (not stated as Rocq axioms)           *)
(* ================================================================ *)

(** These trust assumptions are NOT statable in Rocq because they
    refer to physical execution (CPU, OS, hardware random source).
    Listed here for completeness:

    - **rustc compilation**: rustc translates our emitted .rs source
      to x86-64 (or other) assembly correctly.  Trust transferred to
      rustc's developers + LLVM project.
    - **Host CPU**: AES-NI instructions, AVX, SIMD all execute per
      Intel/AMD specs.  Trust transferred to silicon vendors.
    - **OS RNG** (`/dev/urandom`, `getrandom(2)`): provides
      cryptographically-secure randomness.  Trust transferred to OS
      vendor (kernel CSPRNG implementation).

    No work to do on these in Rocq.  Mitigations: KAT-based regression
    testing (already in place); CPU CT-test harnesses (TODO). *)

(* ================================================================ *)
(* §5.  RustCrypto dependencies (to be removed / replaced)           *)
(* ================================================================ *)

(** Current production-path RustCrypto deps in curve25519-jasmin-rs:

    1. **aes-gcm = "0.10"** — AES-256-GCM AEAD (DEFAULT backend).
       USED BY: [src/symmetric.rs::aes256_gcm_*], consumed by Sender
       Keys + Double Ratchet AEAD step.
       REPLACEMENT PATHS (in increasing order of formal grounding):
         (a) **libcrux HACL** [Cargo feature `aes_gcm_libcrux`,
             LANDED 2026-05-13]: route through F*-verified HACL*
             via [libcrux::aead].  Links the Rust runtime to the
             CatCrypt UC theorem
               CatCrypt.Crypto.AEAD.AESGCMBridge.aesgcm_realizes_faead
             (F_AEAD UC realization on top of GCMReduction game-hop),
             with composition into key exchange via aesgcm_ke_to_sc.
             Trust transferred: from "RustCrypto crate authors" to
             "F* / HACL* proof + Cryspen's Rust bindings".  KAT'd
             byte-for-byte against the RustCrypto path across 15
             message sizes in [symmetric::tests::aes_gcm_cross_backend_kat].
             Both backends are kept feature-flagged so users can
             fall back; the libcrux path is the verified-by-default
             target for the Signal stack.
         (b) **libjade Jasmin AES-GCM** (queued): build GHASH on top
             of libjade AES-CTR (libjade has CTR proofs at
             libjade/proof/crypto_aead/aes256ctr).  EasyCrypt-grade
             end-to-end (compiler chain is EC-verified).  EFFORT: 1-2
             sessions for GHASH + composition.  Brings the AES-GCM
             primitive into the SAME EasyCrypt trust regime as
             SHA-256/SHA-512/X25519/ML-KEM-768.
       INTERIM (default): trust aes-gcm crate (published, audited,
       AES-NI-using).
       UC-CHAIN STATUS for path (a): the Lean theorem
       [aesgcm_realizes_faead] in
       [SSProve-lean/CatCrypt/Crypto/AEAD/AESGCMBridge.lean] is the
       security statement; the libcrux backend is the runtime that
       implements the realizing-protocol.

    2. **prost = "0.12"** — protobuf serialization.
       USED BY: not yet wired (queued for protobuf marshaling).
       REPLACEMENT PATH: hand-authored per-message-type marshalers
       in CatCrypt.  Per [[project_signal_dalek_free]] estimate: 1-2
       months.
       INTERIM: remove dep if unused, otherwise trust.

    3. **rand_core / getrandom** — RNG trait + OS entropy.
       USED BY: nothing in production paths (only randomized XEdDSA
       sign + test fixtures).  Production deterministic XEdDSA now
       has [xeddsa_sign_deterministic] (this session).
       REPLACEMENT PATH: keep (the trait interface is minimal).

    4. **Dev-deps only** (NOT in production trust set):
       - signal-spqr-hax, x3dh-hax, pqxdh-hax, sender-keys-hax (test
         skeletons; the protocol logic is what runs at deploy, our
         primitives via the trait impls)
       - hmac, sha2, ed25519-dalek (compat impls inside hax crates;
         #[cfg(test)] gated in the hax crates themselves)
       - rand, hex, criterion — testing only

    Discipline: when a new dep is added to production paths, list it
    here with a replacement plan and an INTERIM trust note. *)
