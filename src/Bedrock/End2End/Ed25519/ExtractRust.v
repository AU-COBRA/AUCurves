(** * Ed25519 verified-Rust extraction.
 *
 * Tier-1 #7 of the Ed25519-in-AUCurves track. Two-stage pipeline:
 *
 *   Stage 1 (bedrock2 → C source):
 *     ToCString.c_module ed25519_funcs : string
 *     This produces the C body for the bedrock2 [ed25519_sign] /
 *     [ed25519_verify] functions. Pending Phase 1.3 / 1.4 (Sign.v
 *     and Verify.v don't define their bodies yet — currently
 *     [Parameter]s).
 *
 *   Stage 2 (safe Rust wrapper):
 *     ToSafeRustString.gen_module emits a safe Rust facade with
 *     [#[repr(transparent)]] newtypes around the C externs. STAGE 2
 *     IS NOW UNBLOCKED — [ToSafeRustString.v]'s [field_type] gained
 *     the [ft_kind] discriminator (KLimbs/KBytes/KBytesSlice/KUsize)
 *     in commit history below, so byte-buffer + variable-length-msg
 *     wrappers fit cleanly. The wrapper module text is producible
 *     now, in advance of the bedrock2 body — it just declares the
 *     extern "C" signature shape that Stage 1's output will fill.
 *)

From Stdlib Require Import String List ZArith.
Require Import Bedrock.ToSafeRustString.
Import ListNotations.

Local Open Scope string_scope.

(** ** Ed25519 byte-buffer field types. *)
Definition Ed25519Seed   := {| ft_name := "Seed";   ft_limbs := 32; ft_kind := KBytes |}.
Definition Ed25519PubKey := {| ft_name := "PubKey"; ft_limbs := 32; ft_kind := KBytes |}.
Definition Ed25519Sig    := {| ft_name := "Sig";    ft_limbs := 64; ft_kind := KBytes |}.
Definition Ed25519Result := {| ft_name := "Result"; ft_limbs := 1;  ft_kind := KBytes |}.
Definition Ed25519Msg    := {| ft_name := "Msg";    ft_limbs := 0;  ft_kind := KBytesSlice |}.

Definition ed25519_types : list field_type :=
  [Ed25519Seed; Ed25519PubKey; Ed25519Sig; Ed25519Result; Ed25519Msg].

(** ** Ed25519 wrapper specs.
    Mirror the bedrock2 signatures from [Sign.v] / [Verify.v]. *)
Definition ed25519_wrappers : list wrapper_spec := [
  {| wrapper_rust_name := "sign";
     wrapper_c_name := "ed25519_sign";
     wrapper_params := [mk_out "sig_out" Ed25519Sig;
                        mk_in "seed" Ed25519Seed;
                        mk_in "msg" Ed25519Msg] |};

  {| wrapper_rust_name := "verify";
     wrapper_c_name := "ed25519_verify";
     wrapper_params := [mk_out "result" Ed25519Result;
                        mk_in "pk" Ed25519PubKey;
                        mk_in "sig" Ed25519Sig;
                        mk_in "msg" Ed25519Msg] |}
].

(** ** Stage 2 output: safe Rust wrapper module text.
    Producible NOW (independent of bedrock2 body). The extern "C"
    signature this declares matches what Stage 1's ToCString output
    must emit when Sign.v / Verify.v are filled in. *)
Definition ed25519_safe_rust : string :=
  gen_module "Ed25519" ed25519_types ed25519_wrappers.

(** ** Status notes for downstream consumers.
    $WORKSPACE/../SSProve-lean/scripts/extract_ed25519_rust.sh
    stage 2 can now consume [ed25519_safe_rust] (a real string).
    Stage 1 (the C body for ed25519_sign / ed25519_verify) is still
    pending Sign.v + Verify.v bedrock2 bodies. The wrapper module
    expects extern "C" signatures:

      fn ed25519_sign(sig_out: usize, seed: usize, msg_ptr: usize, msg_len: usize);
      fn ed25519_verify(result: usize, pk: usize, sig: usize, msg_ptr: usize, msg_len: usize);

    matching the bedrock2 [func]s' parameter lists. *)
Definition ed25519_extract_status : nat := 1.  (* was 0; now Stage 2 ready *)
