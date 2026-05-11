(** * XEdDSA Sign_Strong_Correctness — strong correctness for xeddsa_sign_rs.
 *
 * Functional postcondition: under [strong_callee_post_xeddsa] (each
 * leaf returns its Gallina spec AND frames all other slots), the
 * v_xed_sig_out slot after execution equals the lifted
 * [xeddsa_sign_gallina_lifted] applied to (k, msg, Z, ...).
 *
 * Mirrors [Bedrock.End2End.Ed25519.Sign_Strong_Correctness] step-for-step.
 *
 * Architecture:
 *   §1 leaf Gallina specs reused (sha512_full_spec, scalar_reduce_spec,
 *      ed25519_scalarmult_base_spec, ed25519_compress_spec, scalar_muladd_spec)
 *      and two new ones: [calculate_key_pair_a_spec], [calculate_key_pair_A_spec],
 *      [xed_hash_1_spec].
 *   §2 [xeddsa_sign_gallina]                : clean reference.
 *   §3 [xeddsa_sign_gallina_lifted]         : lifted reference (matches
 *                                              protocol's intermediate slots).
 *   §4 [strong_callee_post_xeddsa]          : per-call obligation.
 *   §5 frame lemma                          : Qed.
 *   §6 [xeddsa_sign_strong_correct]         : main theorem (Qed).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Require Import Bedrock.End2End.Ed25519.SHA512Bridge.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.XEdDSA.Sign_RustCmd.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Per-callee Gallina specs                                       *)
(* ================================================================ *)

(** Reused as Parameters from [Sign_Strong_Correctness.v] / [RemainingBridges.v]:
    - [sha512_full_spec]                : list byte -> list byte
    - [scalar_reduce_spec]              : list byte -> list byte
    - [ed25519_scalarmult_base_spec]    : list byte -> list byte
    - [ed25519_compress_spec]           : list byte -> list byte
    - [scalar_muladd_spec]              : 3 args -> list byte
*)

(** New XEdDSA-specific leaf specs. *)

(** [calculate_key_pair_a_spec]: derived Edwards scalar from X25519 priv.
    Body: compute Edwards public A = clamp(k) · B, derive sign bit; if
    sign is 1, return -clamp(k) mod L, else return clamp(k).  Treated
    as opaque here. *)
Parameter calculate_key_pair_a_spec : list Byte.byte -> list Byte.byte.
Parameter calculate_key_pair_a_spec_len :
  forall k, length k = 32%nat ->
    length (calculate_key_pair_a_spec k) = 32%nat.

(** [calculate_key_pair_A_spec]: compressed Edwards public key whose
    sign bit has been forced to 0 (matched against the a-fixup). *)
Parameter calculate_key_pair_A_spec : list Byte.byte -> list Byte.byte.
Parameter calculate_key_pair_A_spec_len :
  forall k, length k = 32%nat ->
    length (calculate_key_pair_A_spec k) = 32%nat.

(** [xed_hash_1_spec]: SHA-512 with internal domain-separation prefix
    [0xFE || 0xFF^31].  The leaf prepends these 32 bytes before hashing
    its argument, so callers pass only the protocol payload.

    Defined (not axiomatised) as a thin wrapper over [sha512_full_spec]
    so it does not appear in [Print Assumptions] for downstream theorems. *)
Definition xed_hash_1_spec (input : list Byte.byte) : list Byte.byte :=
  sha512_full_spec
    (Byte.xfe :: List.repeat Byte.xff 31 ++ input)%list.

Lemma xed_hash_1_spec_len :
  forall input, length (xed_hash_1_spec input) = 64%nat.
Proof. intros input; apply sha512_full_spec_len. Qed.

(* ================================================================ *)
(* §2. Memmove spec helpers — XEdDSA buffer layouts                   *)
(* ================================================================ *)

(** All memmove leaves write a fragment of a larger destination buffer.
    Specs describe the exact output as a concat of (kept-prefix, copied-payload,
    kept-suffix). *)

Definition memmove_xed_nonce_a_spec   (src_bs dst_bs : list Byte.byte)
  : list Byte.byte :=
  (src_bs ++ skipn (length src_bs) dst_bs)%list.

Definition memmove_xed_nonce_msg_spec (src_bs dst_bs : list Byte.byte)
  : list Byte.byte :=
  (firstn 32 dst_bs ++ src_bs ++ skipn (32 + length src_bs) dst_bs)%list.

Definition memmove_xed_nonce_Z_spec   (src_bs dst_bs : list Byte.byte)
  : list Byte.byte :=
  (firstn (32 + xed_msg_width) dst_bs ++ src_bs
   ++ skipn (32 + xed_msg_width + length src_bs) dst_bs)%list.

Definition memmove_xed_chal_R_spec (src_bs dst_bs : list Byte.byte)
  : list Byte.byte :=
  (src_bs ++ skipn (length src_bs) dst_bs)%list.

Definition memmove_xed_chal_A_spec (src_bs dst_bs : list Byte.byte)
  : list Byte.byte :=
  (firstn 32 dst_bs ++ src_bs ++ skipn (32 + length src_bs) dst_bs)%list.

Definition memmove_xed_chal_M_spec (src_bs dst_bs : list Byte.byte)
  : list Byte.byte :=
  (firstn 64 dst_bs ++ src_bs)%list.

Definition memmove_xed_sig_R_spec (src_bs dst_bs : list Byte.byte)
  : list Byte.byte :=
  (firstn 32 dst_bs ++ src_bs)%list.

(* ================================================================ *)
(* §3. Gallina reference                                              *)
(* ================================================================ *)

(** Clean reference for XEdDSA, depending only on (k, msg, Z).  Assumes
    all hash inputs / outputs are tight. *)
Definition xeddsa_sign_gallina
    (k msg Z_rand : list Byte.byte) : list Byte.byte :=
  let a        := calculate_key_pair_a_spec k in
  let A_bytes  := calculate_key_pair_A_spec k in
  let nonce    := (a ++ msg ++ Z_rand)%list in
  let r_full   := xed_hash_1_spec nonce in
  let r        := scalar_reduce_spec r_full in
  let R_xyzt   := ed25519_scalarmult_base_spec r in
  let R_bytes  := ed25519_compress_spec R_xyzt in
  let chal     := (R_bytes ++ A_bytes ++ msg)%list in
  let k_full   := sha512_full_spec chal in
  let k_red    := scalar_reduce_spec k_full in
  let s        := scalar_muladd_spec r k_red a in
  (s ++ R_bytes)%list.

(** Lifted reference: matches the bedrock2 protocol's intermediate
    state precisely.  The [nonce_init], [chal_init], [sig_init] are
    the byte contents of the corresponding slots BEFORE any partial
    memmove writes (i.e. zeros after REdLetZero in the canonical case).
    The hash lengths are existentially quantified in the theorem. *)
Definition xeddsa_sign_gallina_lifted
    (k msg Z_rand : list Byte.byte)
    (nonce_hash_len chal_hash_len : nat)
    (nonce_init chal_init sig_init : list Byte.byte)
  : list Byte.byte :=
  let a        := calculate_key_pair_a_spec k in
  let A_bytes  := calculate_key_pair_A_spec k in
  let nonce_C3 := memmove_xed_nonce_a_spec a nonce_init in
  let nonce_C4 := memmove_xed_nonce_msg_spec msg nonce_C3 in
  let nonce_C5 := memmove_xed_nonce_Z_spec Z_rand nonce_C4 in
  let r_full   := xed_hash_1_spec (firstn nonce_hash_len nonce_C5) in
  let r        := scalar_reduce_spec r_full in
  let R_xyzt   := ed25519_scalarmult_base_spec r in
  let R_bytes  := ed25519_compress_spec R_xyzt in
  let chal_C11 := memmove_xed_chal_R_spec R_bytes chal_init in
  let chal_C12 := memmove_xed_chal_A_spec A_bytes chal_C11 in
  let chal_C13 := memmove_xed_chal_M_spec msg chal_C12 in
  let k_full   := sha512_full_spec (firstn chal_hash_len chal_C13) in
  let k_red    := scalar_reduce_spec k_full in
  let sig_C16  := (scalar_muladd_spec r k_red a ++ skipn 32 sig_init)%list in
  (firstn 32 sig_C16 ++ R_bytes)%list.

(* ================================================================ *)
(* §4. Strong callee_post predicate                                   *)
(* ================================================================ *)

(** Per-call obligation: dest gets the leaf's spec, and the other
    tower slots + the dynamic message length scalar are framed. *)
Definition strong_callee_post_xeddsa
           (fname : String.string)
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  (rs_get_scalar_ed rs1 v_xed_msg_len = rs_get_scalar_ed rs2 v_xed_msg_len) /\
  match fname, args with
  | "calculate_key_pair_a", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (calculate_key_pair_a_spec src_bs)
  | "calculate_key_pair_A", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (calculate_key_pair_A_spec src_bs)
  | "xed_hash_1", [src; len_arg] =>
      exists src_bs len,
        slot_holds rs1 src.(loc_var) src_bs /\
        rs_get_scalar_ed rs1 len_arg.(loc_var) = Some len /\
        slot_holds rs2 dst.(loc_var)
          (xed_hash_1_spec (firstn (Z.to_nat len) src_bs))
  | "sha512_64", [src; len_arg] =>
      exists src_bs len,
        slot_holds rs1 src.(loc_var) src_bs /\
        rs_get_scalar_ed rs1 len_arg.(loc_var) = Some len /\
        slot_holds rs2 dst.(loc_var)
          (sha512_full_spec (firstn (Z.to_nat len) src_bs))
  | "scalar_reduce", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (scalar_reduce_spec src_bs)
  | "scalar_muladd", [r; k; a] =>
      exists r_bs k_bs a_bs dst_bs,
        slot_holds rs1 r.(loc_var) r_bs /\
        slot_holds rs1 k.(loc_var) k_bs /\
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var)
          (scalar_muladd_spec r_bs k_bs a_bs ++ skipn 32 dst_bs)
  | "ed25519_compress", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_compress_spec src_bs)
  | "ed25519_scalarmult_base", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_scalarmult_base_spec src_bs)
  | "memmove_xed_nonce_a", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_xed_nonce_a_spec src_bs dst_bs)
  | "memmove_xed_nonce_msg", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_xed_nonce_msg_spec src_bs dst_bs)
  | "memmove_xed_nonce_Z", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_xed_nonce_Z_spec src_bs dst_bs)
  | "memmove_xed_chal_R", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_xed_chal_R_spec src_bs dst_bs)
  | "memmove_xed_chal_A", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_xed_chal_A_spec src_bs dst_bs)
  | "memmove_xed_chal_M", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_xed_chal_M_spec src_bs dst_bs)
  | "memmove_xed_sig_R", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_xed_sig_R_spec src_bs dst_bs)
  | _, _ => True
  end.

(* ================================================================ *)
(* §5. Frame lemma — Qed                                              *)
(* ================================================================ *)

Lemma strong_callee_post_xeddsa_frame_other_slots :
  forall fname args dst rs1 rs2 x,
    strong_callee_post_xeddsa fname args dst rs1 rs2 ->
    x <> dst.(loc_var) ->
    rs_get_tower_ed rs1 x = rs_get_tower_ed rs2 x.
Proof.
  intros fname args dst rs1 rs2 x [Hframe _] Hne.
  apply (Hframe x Hne).
Qed.

(* ================================================================ *)
(* §6. Strong correctness theorem                                     *)
(* ================================================================ *)

(** [neq_var_xed] proves [v_xed_X <> v_xed_Y]. *)
Ltac neq_var_xed :=
  cbn [LE_TBytes LE_TU64 loc_var];
  cbv [v_xed_sig_out v_xed_k v_xed_msg v_xed_msg_len v_xed_Z
       v_xed_a v_xed_A v_xed_nonce v_xed_r_full v_xed_r
       v_xed_R_xyzt v_xed_R_bytes v_xed_chal v_xed_k_full
       v_xed_k_red];
  discriminate.

Ltac peel_call_seq_xed H Hframe Hres :=
  let Hcall := fresh "Hcall" in
  let Hrest := fresh "Hrest" in
  let Hsc := fresh "Hsc_xmsg" in
  inversion H; subst; clear H;
  match goal with
  | Hc : rust_exec_ed _ _ _ (REdCall _ _ _) _ _,
    Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hc into Hcall; rename Hr into Hrest
  end;
  inversion Hcall; subst; clear Hcall;
  match goal with
  | Hc : strong_callee_post_xeddsa _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe [Hsc Hres]]
  end;
  match goal with
  | Hh : rs_get_scalar_ed _ v_xed_msg_len = Some _ |- _ =>
      rewrite Hsc in Hh; clear Hsc
  end;
  rename Hrest into H.

Ltac peel_last_call_xed H Hframe Hres :=
  let Hsc := fresh "Hsc_xmsg" in
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_xeddsa _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe [Hsc Hres]]; clear Hsc
  end.

Theorem xeddsa_sign_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (k msg Z_rand sig_init : list Byte.byte)
         (msg_len : Z),
    length k = 32%nat ->
    length msg = xed_msg_width ->
    length Z_rand = 64%nat ->
    (0 <= msg_len <= Z.of_nat xed_msg_width)%Z ->
    slot_holds rs1 v_xed_k k ->
    slot_holds rs1 v_xed_msg msg ->
    slot_holds rs1 v_xed_Z Z_rand ->
    slot_holds rs1 v_xed_sig_out sig_init ->
    rs_get_scalar_ed rs1 v_xed_msg_len = Some msg_len ->
    rust_exec_ed strong_callee_post_xeddsa callee_post_n function_table
                 xeddsa_sign_rs rs1 rs2 ->
    exists nonce_hash_len chal_hash_len nonce_init chal_init,
      slot_holds rs2 v_xed_sig_out
        (xeddsa_sign_gallina_lifted k msg Z_rand
           nonce_hash_len chal_hash_len
           nonce_init chal_init sig_init).
Proof.
  intros callee_post_n function_table rs1 rs2 k msg Z_rand sig_init msg_len
         Hk_len Hmsg_len HZ_len Hmsg_len_bound
         Hk Hmsg HZ Hsig_init Hmsg_len_get Hexec.
  unfold xeddsa_sign_rs in Hexec.

  (* Stage A: peel 10 REdLetZero allocations. *)
  repeat (match goal with
          | H : rust_exec_ed _ _ _ (REdLetZero _ _ _) _ _ |- _ =>
              inversion H; subst; clear H
          end).

  (* Propagate input slots through the 10 fresh allocations. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hk_alloc : slot_holds rs_alloc v_xed_k k) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hk);
      assert (Hmsg_alloc : slot_holds rs_alloc v_xed_msg msg) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hmsg);
      assert (HZ_alloc : slot_holds rs_alloc v_xed_Z Z_rand) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact HZ);
      assert (Hsig_alloc : slot_holds rs_alloc v_xed_sig_out sig_init) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hsig_init);
      assert (Hmsg_len_alloc : rs_get_scalar_ed rs_alloc v_xed_msg_len = Some msg_len) by
        (repeat rewrite scalar_get_set_tower; exact Hmsg_len_get);
      rename H into Hexec
  end.
  clear Hk Hmsg HZ Hsig_init Hmsg_len_get.

  (* === Stage B: 16 call inversions === *)

  (* C1: calculate_key_pair_a (xed_a ← xed_k) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hk_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  clear Hframe Hsrc.

  (* C2: calculate_key_pair_A (xed_A ← xed_k) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hk_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  clear Hframe Hsrc.

  (* C3: memmove_xed_nonce_a (nonce ← a) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs3 [Hsrc [Hdst Htgt3]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_xed].
  clear Hframe Hsrc Hdst.

  (* C4: memmove_xed_nonce_msg (nonce ← msg) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt4]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt3) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_xed].
  clear Hframe Hsrc Hdst Htgt3.

  (* C5: memmove_xed_nonce_Z (nonce ← Z) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt5]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc HZ_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt4) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_xed].
  clear Hframe Hsrc Hdst Htgt4.

  (* Peel REdLetU64 "xed_nonce_hash_len" *)
  inversion Hexec; subst; clear Hexec.
  match goal with
  | Hev : eval_sexpr_ed _ _ = Some _ |- _ =>
      rename Hev into Heval_nl
  end.
  match goal with
  | Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hr into Hexec
  end.
  cbn [eval_sexpr_ed] in Heval_nl.
  rewrite Hmsg_len_alloc in Heval_nl.
  inversion Heval_nl as [Hv_nl].
  assert (Hxmsg_set : v_xed_msg_len <> "xed_nonce_hash_len")
    by (cbv [v_xed_msg_len]; intro Hcontra; discriminate Hcontra).
  match goal with
  | _ : context [rs_set_scalar_ed ?rs0 "xed_nonce_hash_len" ?v0] |- _ =>
      pose proof (slot_holds_scalar_set_other rs0 "xed_nonce_hash_len" v0 _ _
                    Hxmsg_set Hmsg_len_alloc) as Hmsg_len_alloc';
      clear Hmsg_len_alloc Hxmsg_set;
      rename Hmsg_len_alloc' into Hmsg_len_alloc
  end.

  (* C6: xed_hash_1 (r_full ← nonce, nonce_hash_len) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [len6 [Hsrc [Hlen6 Htgt6]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt5) as Heq; subst src_bs.
  cbn [LE_TU64 loc_var] in Hlen6.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_xed].
  clear Hframe Hsrc Htgt5.

  (* C7: scalar_reduce (r ← r_full) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt7]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt6) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_xed].
  clear Hframe Hsrc Htgt6.

  (* C8: ed25519_scalarmult_base (R_xyzt ← r) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt8]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt7) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt7; [|neq_var_xed].
  clear Hframe Hsrc.

  (* C9: ed25519_compress (R_bytes ← R_xyzt) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt9]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt8) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt7; [|neq_var_xed].
  clear Hframe Hsrc Htgt8.

  (* C10: memmove_xed_chal_R (chal ← R_bytes) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs10 [Hsrc [Hdst Htgt10]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt9) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt7; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt9; [|neq_var_xed].
  clear Hframe Hsrc Hdst.

  (* C11: memmove_xed_chal_A (chal ← A) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt11]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt2) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt10) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt7; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt9; [|neq_var_xed].
  clear Hframe Hsrc Hdst Htgt10.

  (* C12: memmove_xed_chal_M (chal ← msg) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt12]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt11) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt7; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt9; [|neq_var_xed].
  clear Hframe Hsrc Hdst Htgt2 Htgt11.

  (* Peel REdLetU64 "xed_chal_hash_len" *)
  inversion Hexec; subst; clear Hexec.
  match goal with
  | Hev : eval_sexpr_ed _ _ = Some _ |- _ =>
      rename Hev into Heval_cl
  end.
  match goal with
  | Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hr into Hexec
  end.
  cbn [eval_sexpr_ed] in Heval_cl.
  rewrite Hmsg_len_alloc in Heval_cl.
  inversion Heval_cl as [Hv_cl].
  assert (Hxmsg_set_cl : v_xed_msg_len <> "xed_chal_hash_len")
    by (cbv [v_xed_msg_len]; intro Hcontra; discriminate Hcontra).
  match goal with
  | _ : context [rs_set_scalar_ed ?rs0 "xed_chal_hash_len" ?v0] |- _ =>
      pose proof (slot_holds_scalar_set_other rs0 "xed_chal_hash_len" v0 _ _
                    Hxmsg_set_cl Hmsg_len_alloc) as Hmsg_len_alloc';
      clear Hmsg_len_alloc Hxmsg_set_cl;
      rename Hmsg_len_alloc' into Hmsg_len_alloc
  end.

  (* C13: sha512_64 (k_full ← chal, chal_hash_len) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [len13 [Hsrc [Hlen13 Htgt13]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt12) as Heq; subst src_bs.
  cbn [LE_TU64 loc_var] in Hlen13.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt7; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt9; [|neq_var_xed].
  clear Hframe Hsrc Htgt12.

  (* C14: scalar_reduce (k_red ← k_full) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt14]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt13) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hk_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in HZ_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt7; [|neq_var_xed].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt9; [|neq_var_xed].
  clear Hframe Hsrc Htgt13.

  (* C15: scalar_muladd (sig_out ← r, k_red, a) *)
  peel_call_seq_xed Hexec Hframe Hres.
  destruct Hres as [r_bs [k_bs [a_bs [dst_bs [Hsr [Hsk [Hsa [Hsd Htgt15]]]]]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsr Htgt7) as Heq; subst r_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsk Htgt14) as Heq; subst k_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsa Htgt1) as Heq; subst a_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsd Hsig_alloc) as Heq; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt9; [|neq_var_xed].
  clear Hframe Hsr Hsk Hsa Hsd Hk_alloc Hmsg_alloc HZ_alloc Hsig_alloc
        Htgt1 Htgt7 Htgt14.

  (* C16: memmove_xed_sig_R (sig_out ← R_bytes) — last call *)
  peel_last_call_xed Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt16]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt9) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt15) as Heq2; subst dst_bs.
  clear Hframe Hsrc Hdst.

  (* Stage C: assembly. *)
  cbn [LE_TBytes loc_var] in Htgt16.
  exists (Z.to_nat len6), (Z.to_nat len13), dst_bs3, dst_bs10.
  unfold xeddsa_sign_gallina_lifted, memmove_xed_sig_R_spec.
  exact Htgt16.
Qed.
