# Rewriting `ed25519_sign`'s bedrock2 body to be the rust_cmd_ed translation

Instead of bridging the existing pointer-arithmetic body in
`Sign.v` to `rust_cmd_ed`, rewrite the body to **be** the
translation.  Same correctness guarantees, simpler verification
chain.

## What changes

### Today's `Sign.v` body

```coq
Definition ed25519_sign : Syntax.func :=
  func! (sig_out, seed, msg, msg_len) {
    stackalloc 64 as h_full;
    sha512_64(h_full, seed, $32);
    stackalloc 32 as a;
    memmove(a, h_full, $32);            (* pointer arithmetic *)
    clamp_64(a);
    stackalloc 32 as prefix;
    memmove(prefix, h_full + $32, $32); (* pointer arithmetic *)
    ...
    memmove(sig_out + $32, R_bytes, $32) (* pointer arithmetic *)
  }.
```

Pointer arithmetic (`h_full + $32`, `sig_out + $32`) is the
non-rust_cmd_ed-y part.  Calls `memmove` (the libc-style
3-arg one) with computed offsets.

### Rewritten body

```coq
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd. (* ed25519_sign_rs *)
Require Import Bedrock.RustCmdToC.                          (* to_bedrock_cmd *)

Definition ed25519_sign_body : Syntax.cmd :=
  to_bedrock_cmd ed25519_sign_rs.

Definition ed25519_sign : Syntax.func :=
  ([("sig_out", []); ("seed", []); ("msg", []); ("msg_len", [])],
   [], (* return list *)
   ed25519_sign_body).
```

The body is now `to_bedrock_cmd ed25519_sign_rs`.  No pointer
arithmetic anywhere — every region copy is a named call:
`memmove_a_from_h(a, h_full)`, `memmove_chal_R(chal_buf, R_bytes)`,
etc.

## Same guarantees — yes

The `rfc8032_ed25519_sign seed msg` post-condition is preserved
under the rewrite.  Verification chain:

```
ed25519_sign_strong_correct (Qed)
  └── output = ed25519_sign_gallina_lifted seed msg ...
      └── (ed25519_sign_gallina_lifted_clean, Qed)
          = ed25519_sign_gallina seed msg
              └── (Definition ed25519_sign_gallina ≜ rfc8032_ed25519_sign)
                  └── matches Sign.v's expected post

bedrock_cmd_ed_to_syntax (rust_to_bedrock_cmd_ed ed25519_sign_rs)
  = to_bedrock_cmd ed25519_sign_rs    (by to_bedrock_cmd_factors, Qed)

so:  WP.cmd functions ed25519_sign_body
       = WP.cmd functions (to_bedrock_cmd ed25519_sign_rs)
       = WP.cmd functions (bedrock_cmd_ed_to_syntax (rust_to_bedrock_cmd_ed ed25519_sign_rs))

Apply bridge_complete (once axioms closed):
       ⇐ bedrock_exec_ed strong_callee_post (rust_to_bedrock_cmd_ed ed25519_sign_rs) rs1 rs2

Apply safe_cmd_correct_ed (Qed):
       ⇒ rust_exec_ed strong_callee_post ed25519_sign_rs rs1 rs2

Apply ed25519_sign_strong_correct (Qed):
       ⇒ slot_holds rs2 v_sig_out (ed25519_sign_gallina_lifted ...)

Compose with state_refine_ed:
       ⇒ (rfc8032_ed25519_sign seed msg)$@sig_out_ptr ⋆ ... in m'.
```

The post-condition we end up with is the same `rfc8032_ed25519_sign
seed msg` post — the Axiom's post — provided we set
`Definition rfc8032_ed25519_sign := ed25519_sign_gallina`.

## Trade-offs

### Pro
- **Removes the structural mismatch** that today blocks the
  bedrock2 axiom from being a Theorem.
- **Verification chain is end-to-end Qed** (modulo the 8 bridge
  axioms in `SafeRustEd25519WPBridge.v` and the discharge work
  for those, which is bounded mechanical bedrock2 WP).
- **Extraction stays the same** — already uses
  `to_bedrock_cmd` / `c_emit` / `rs_func_emit` paths.

### Con
- **More named callees**: the current pointer-arithmetic body
  uses one `memmove(...)` function (libc).  The rewritten body
  uses 10 named `memmove_<NAME>` helpers.  These are already
  implemented in `curve25519-jasmin-rs/src/ed25519_rustcmd/memmove_helpers.rs`
  as safe-Rust slice copies — no lift required for the Rust
  extraction path.  For the C extraction path (`c_emit` /
  `to_bedrock_c`), each helper needs a `void
  memmove_<NAME>(uint8_t* dst, const uint8_t* src) { memcpy(dst+off, src,
  N); }` stub in C.
- **Function table grows**: `functions` map needs entries for the
  10 memmove helpers in addition to `sha512_64` etc.  Trivial
  bedrock2-side fnspec definition each.
- **Slight verbosity** in the bedrock2 source at the call-graph
  level — but the rust_cmd_ed source remains as compact as before.

## Concrete steps

1. **Add bedrock2 fnspecs for the memmove helpers.**  Each is a
   3-line `Definition spec_of_memmove_X (functions : env) :
   Prop := ...` pattern matching the bridges in
   `RemainingBridges.v`.
2. **Define `ed25519_sign_body`** as `to_bedrock_cmd
   ed25519_sign_rs` (one line).  Replace the current `func! { ...
   }` body in `ed25519_sign`.
3. **State the new theorem** (replacing the Axiom):
   ```coq
   Theorem ed25519_sign_correct :
     forall functions ...,
       spec_of_sha512_64 functions ->
       spec_of_scalar_reduce functions ->
       spec_of_scalar_muladd functions ->
       spec_of_ed25519_compress functions ->
       spec_of_ed25519_scalarmult_base_bridge functions ->
       spec_of_clamp_64 functions ->
       spec_of_memmove_a_from_h functions ->
       (* ... 9 more memmove fnspecs ... *)
       Datatypes.length sig_out_init = 64%nat ->
       Datatypes.length seed = 32%nat ->
       Datatypes.length msg <= 4096%nat ->
       ((sig_out_init$@sig_out_ptr) ⋆
        (seed$@seed_ptr) ⋆ (msg$@msg_ptr) ⋆ R)%sep m ->
       Interface.map.get functions "ed25519_sign"%string = Some ed25519_sign ->
       WeakestPrecondition.call functions "ed25519_sign"%string t m
         (sig_out_ptr :: seed_ptr :: msg_ptr ::
          word.of_Z (Z.of_nat (Datatypes.length msg)) :: nil)
         (fun t' m' rets =>
            t' = t /\ rets = nil /\
            ((rfc8032_ed25519_sign seed msg)$@sig_out_ptr ⋆
             (seed$@seed_ptr) ⋆ (msg$@msg_ptr) ⋆ R)%sep m').
   Proof.
     intros.
     (* Apply bridge_complete after instantiating callee_post
        with strong_callee_post.  Each spec_of_* hypothesis
        discharges one of the 19 calls' callee_post obligation
        via the corresponding leaf bridge. *)
   Qed.
   ```
4. **Discharge the bridge axioms** in
   `SafeRustEd25519WPBridge.v` (~600 LoC, mechanical).

After step 4, the entire chain is Qed.  Today it's Qed except for
the 8 bridge axioms.  Going from Axiom → Theorem in `Sign.v`
modulo those 8 is a strictly smaller change than today's
"axiomatic monolith".

## Whether to do it

Depends on what consumers expect.  If consumers (libsignal, signal-wasm)
go through the **rust_cmd_ed → Rust** path (which they should, per
the eval doc), they don't touch `Sign.v`'s bedrock2 body at all —
the alias `ed25519_sign_strong_correct_alias` is sufficient.

If consumers want the **bedrock2 → C → ABI** path (e.g., a
non-Rust consumer linking against `ed25519_sign.c` extracted via
bedrock2 ToCString), the rewrite is necessary to drop the Axiom.

For AUCurves' own deliverable (verified Rust for libsignal),
**the rewrite is optional but cleaner**.  For a publishable
"AUCurves bedrock2 Ed25519 has zero axioms", the rewrite + bridge
axiom discharge is the path.

Last updated: 2026-05-09.
