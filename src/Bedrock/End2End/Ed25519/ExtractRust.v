(** * Ed25519 verified-Rust extraction.
 *
 * Tier-1 #7 of the Ed25519-in-AUCurves track. Two-stage pipeline:
 *
 *   Stage 1 (bedrock2 → C source):
 *     ToCString.c_module ed25519_funcs : string
 *     This produces the C body for the bedrock2 [ed25519_sign] /
 *     [ed25519_verify] functions. Already supported by AUCurves'
 *     existing [bedrock2.ToCString] integration; same pattern as
 *     [End2End/X25519_64/ExtractJasmin.v]'s c_module emission.
 *
 *   Stage 2 (safe Rust wrapper):
 *     ToSafeRustString.gen_module emits a safe Rust facade with
 *     [#[repr(transparent)]] newtypes around the C externs.
 *     The bls12_381 / bn254 extractions in [ToSafeRustString.v]
 *     are the working templates.
 *
 * STATUS (2026-04-26): blocked on Phase 1.3 / 1.4 — Sign.v and
 * Verify.v don't define their bedrock2 [Func] bodies yet. ToCString
 * needs concrete [func]s, and [Ed25519Sign.ed25519_sign] /
 * [Ed25519Verify.ed25519_verify] are still [Parameter]s.
 *
 * Additionally, [ToSafeRustString.v]'s [field_type] / [wrapper_spec]
 * ADTs assume [u64; N]-style arrays. Ed25519 sign/verify pass
 * variable-length byte arrays (msg) and fixed-size byte buffers
 * (sig 64, pk 32, seed 32). The infrastructure needs a small
 * extension (~50 LoC) before Ed25519 wrappers fit cleanly:
 *   - Add a [BytesArray N] variant to [field_type].
 *   - Add a [BytesPtrLen] variant for variable-length byte spans.
 *   - Update [gen_newtype], [rust_ref], [rust_cast], [gen_extern_decl],
 *     [gen_safe_wrapper] to dispatch on the new variants.
 *
 * Once those land:
 *
 *   Definition Ed25519Seed   := {| ft_name := "Seed";   ft_kind := Bytes 32 |}.
 *   Definition Ed25519PubKey := {| ft_name := "PubKey"; ft_kind := Bytes 32 |}.
 *   Definition Ed25519Sig    := {| ft_name := "Sig";    ft_kind := Bytes 64 |}.
 *   Definition Ed25519Msg    := {| ft_name := "Msg";    ft_kind := BytesPtrLen |}.
 *
 *   Definition ed25519_types : list field_type :=
 *     [Ed25519Seed; Ed25519PubKey; Ed25519Sig; Ed25519Msg].
 *
 *   Definition ed25519_wrappers : list wrapper_spec := [
 *     {| wrapper_rust_name := "sign";
 *        wrapper_c_name := "ed25519_sign";
 *        wrapper_params := [mk_out "sig_out" Ed25519Sig;
 *                           mk_in "seed" Ed25519Seed;
 *                           mk_in "msg" Ed25519Msg] |};
 *     {| wrapper_rust_name := "verify";
 *        wrapper_c_name := "ed25519_verify";
 *        wrapper_params := [mk_out "result" (Bytes 1);
 *                           mk_in "pk" Ed25519PubKey;
 *                           mk_in "sig" Ed25519Sig;
 *                           mk_in "msg" Ed25519Msg] |}
 *   ].
 *
 *   Definition ed25519_safe_rust : string :=
 *     gen_module "Ed25519" ed25519_types ed25519_wrappers.
 *
 *   Definition ed25519_c_source : string :=
 *     ToCString.c_module ed25519_funcs.   (* requires Sign.v / Verify.v bodies *)
 *
 *   (* Concatenated module that the consumer imports as one .rs *)
 *   Definition ed25519_rust_module : string :=
 *     ed25519_safe_rust.
 *
 *   (* Correctness theorem composes:
 *      - ed25519_sign_correct (Phase 1.3) — bedrock2 → spec
 *      - ToCString.c_module_correct — bedrock2 → C
 *      - ToSafeRustString safe-wrapper soundness — extern → safe Rust *)
 *   Theorem ed25519_sign_rust_correct :
 *     forall seed msg result_sig,
 *       length seed = 32 -> length msg < ... ->
 *       (* the safe Rust ed25519::sign(sig_out, seed, msg) leaves
 *          sig_out = rfc8032_ed25519_sign seed msg *) ...
 *   Proof.
 *     intros.
 *     apply gen_safe_wrapper_sound.    (* wrapper layer *)
 *     apply c_module_correct.          (* ToCString layer *)
 *     apply Ed25519Sign.ed25519_sign_correct.   (* bedrock2 layer *)
 *   Qed.
 *
 * STATUS UPDATE NEEDED when consuming this file:
 *   - $WORKSPACE/../SSProve-lean/scripts/extract_ed25519_rust.sh
 *     stage 2 currently consumes a placeholder; flip when this file
 *     produces a real string.
 *)

(* Placeholder — full ToSafeRustString integration deferred. *)
Definition ed25519_extract_status : nat := 0.
