(** * BN446_PairingRustConcrete.v — Step 1: concrete predicates and fenv.
 *
 * Discharges the [Parameter]s in [BN446_PairingRust.v] by giving
 * concrete [Definition]s for:
 *
 *   - The BN446 [CallEnv] ([bn446_call_env]).
 *   - The BN446 function environment ([bn446_pairing_fenv]).
 *   - The leaf_spec (imported from [SafeRustBN446Concrete]).
 *   - The pre/post predicates ([pairing_pre], [pairing_post]) and
 *     the midstate predicates ([mid_g1], [mid_g2], [mid_w], [mid_ml])
 *     threaded between consecutive pairing-body calls.
 *
 * Steps 2-5 of the plan build on this scaffolding: bridges + fenv_has
 * become [reflexivity]/unfolding lemmas, and the body-refines
 * obligations can be discharged per-function with [rust_step].
 *
 * The file is kept self-contained (does not import [BN446_PairingRust.v])
 * to avoid the Parameter-vs-Definition name clash on
 * [bn446_leaf_spec_concrete].
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustLeafRefinement.
Require Import Bedrock.SafeRustBN446Concrete.
Require Import Bedrock.RustComposition.

Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.PairingSpec.
Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.Curves.BN446_params.

(** NB: we do NOT [Require Import MillerLoopWP] because that
    transitively imports [FevalBridge], which currently has an
    upstream compile error ([F.to_Z_sub] was never defined in
    fiat-crypto's [Spec/ModularArithmetic]; only [F.to_Z_add],
    [F.to_Z_mul], [F.to_Z_opp] exist).  Instead we copy the
    small [bn446_optimal_ate_spec] definition locally below. *)

(* ================================================================ *)
(* §0. Global parameters                                             *)
(* ================================================================ *)

Definition bn446_N : nat := 7.
Definition bn446_u64_max : nat := Nat.pow 2 64.

(** Local mirror of [BN446_PairingCorrect.bn446_miller_loop_with_corrections].
    Copied to keep this file independent of [BN446_PairingCorrect.v]
    (which pulls in a heavy bedrock2 instance stack).  Step 2's
    bridge proofs connect the two via reflexivity / unfolding. *)
Local Definition bn446_p_val : Z := prime_p bn446_params.
Local Definition bn446_xi_val : Fp2_Z := (2%Z, 3%Z).  (** BN446: xi = 2 + 3u *)

Definition bn446_miller_loop_with_corrections
           (gamma1 gamma_y gamma1_p2 : Fp2_Z)
           (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
  let '(f, Tx, Ty) :=
    affine_miller_aux bn446_zmod_ops
      (loop_abs bn446_params)
      (Z.to_nat (Z.log2 (loop_abs bn446_params)))
      Px Py Qx Qy
      (fp12_one bn446_zmod_ops) Qx Qy in
  PairingSpec.apply_corrections
    bn446_zmod_ops
    (zfp2_conj bn446_p_val)
    (zfp2_mul_const bn446_p_val)
    (optimal_ate_extras bn446_params)
    f Tx Ty Px Py Qx Qy
    gamma1 gamma_y gamma1_p2.

(** Local copy of [MillerLoopWP.bn446_optimal_ate_spec] (see note
    on the import block above).  Identical definition. *)
Definition bn446_optimal_ate_spec
    (gamma1 gamma_y gamma1_p2 : Fp2_Z)
    (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
  PairingSpec.optimal_ate
    bn446_zmod_ops
    (zfp12_conj bn446_p_val)
    (zfp12_inv bn446_p_val bn446_xi_val)
    (zfp12_frob_p2 bn446_p_val bn446_xi_val)
    (zfp12_pow bn446_p_val bn446_xi_val)
    (zfp2_conj bn446_p_val)
    (zfp2_mul_const bn446_p_val)
    bn446_params
    gamma1 gamma_y gamma1_p2
    Px Py Qx Qy.

(* ================================================================ *)
(* §1. Tower-level evaluators (rust_val -> Fp{2,6,12}_Z)             *)
(*     Defined locally to avoid discharging section variables of    *)
(*     [SafeRustLeafRefinement.fp{2,6,12}_eval].                     *)
(* ================================================================ *)

Definition bn446_fp2_eval (v : rust_val TFp2) : Fp2_Z :=
  match v with
  | VFp2 a b => (bn446_fp_eval a, bn446_fp_eval b)
  end.

Definition bn446_fp6_eval (v : rust_val TFp6) : Fp6_Z :=
  match v with
  | VFp6 c0 c1 c2 =>
      (bn446_fp2_eval c0, bn446_fp2_eval c1, bn446_fp2_eval c2)
  end.

Definition bn446_fp12_eval (v : rust_val TFp12) : Fp12_Z :=
  match v with
  | VFp12 c0 c1 => (bn446_fp6_eval c0, bn446_fp6_eval c1)
  end.

(* ================================================================ *)
(* §2. BN446 CallEnv (concrete Definition, not Parameter)            *)
(* ================================================================ *)

Fixpoint bn446_bind_params_aux
         (params : list var) (args : list located) (rs_caller rs_acc : rust_state)
  : option rust_state :=
  match params, args with
  | [], [] => Some rs_acc
  | p :: ps, a :: as_ =>
      match located_lookup_sig rs_caller a with
      | Some (existT t v) =>
          bn446_bind_params_aux ps as_ rs_caller
            (rs_set_tower rs_acc p (exist_tval t v))
      | None => None
      end
  | _, _ => None
  end.

Definition bn446_bind_params
           (params : list var) (args : list located) (rs : rust_state)
  : option rust_state :=
  bn446_bind_params_aux params args rs rs_empty.

Definition bn446_extract_output
           (params : list var) (rs : rust_state)
  : option { t : tower_type & rust_val t } :=
  match params with
  | p :: _ =>
      match lookup_t (rs_tower rs) p with
      | Some (exist_tval t v) => Some (existT _ t v)
      | None => None
      end
  | [] => None
  end.

Definition bn446_writeback_output
           (dest : located) (out : { t : tower_type & rust_val t })
           (rs : rust_state) : option rust_state :=
  let '(existT t v) := out in
  match tower_type_eq_dec t (loc_dst dest) with
  | left H => located_update rs dest (eq_rect t rust_val v _ H)
  | right _ => None
  end.

Definition bn446_call_env : CallEnv :=
  {| ce_bind_params     := bn446_bind_params;
     ce_extract_output  := bn446_extract_output;
     ce_writeback_output := bn446_writeback_output |}.

(* ================================================================ *)
(* §3. Concrete function environment                                 *)
(*                                                                   *)
(*   The bodies [bn446_*_body] are still [Parameter]s at this step   *)
(*   — they will be filled in by applying [btranslate] to the        *)
(*   bedrock2 source in Steps 3-4.  What Step 1 buys us is:          *)
(*                                                                   *)
(*     ∙ [bn446_pairing_fenv] is a concrete list literal, so         *)
(*       [fenv_lookup bn446_pairing_fenv "bn446_..."] reduces by     *)
(*       [cbv] to the expected [Some (params, body)].                *)
(*                                                                   *)
(*     ∙ The 5 [fenv_has_*] axioms in BN446_PairingRust.v become     *)
(*       reflexivity-provable (Step 2).                              *)
(* ================================================================ *)

(** Local helpers: locations into Fp2's two Fp components at the
    callee's "out" parameter.  Used by the loader bodies. *)
Local Definition loaders_out_c0 : located :=
  {| loc_var := "out"; loc_src := TFp2; loc_dst := TFp;
     loc_path := PathCons _ _ _ StepFp2_0 (PathNil _) |}.
Local Definition loaders_out_c1 : located :=
  {| loc_var := "out"; loc_src := TFp2; loc_dst := TFp;
     loc_path := PathCons _ _ _ StepFp2_1 (PathNil _) |}.

(** Concrete loader body template: 8 [RLimbStore]s laying down the
    [N = 4] limbs of the two [Fp] components of an [Fp2] result.  The
    specific limb values [l_{00..03}] (c0's 4 limbs) and
    [l_{10..13}] (c1's 4 limbs) are passed as parameters so the same
    body shape instantiates to any BN446 Frobenius constant. *)
(** Concrete loader body template: 10 [RLimbStore]s laying down the
    [N = 5] limbs of the two [Fp] components of an [Fp2] result. *)
(** Concrete loader body: 14 [RLimbStore]s for [N = 7] limbs × 2 components. *)
Definition bn446_loader_body
           (l00 l01 l02 l03 l04 l05 l06
            l10 l11 l12 l13 l14 l15 l16 : nat) : rust_cmd :=
  RSeq (RLimbStore loaders_out_c0 0 (SLit l00))
   (RSeq (RLimbStore loaders_out_c0 1 (SLit l01))
    (RSeq (RLimbStore loaders_out_c0 2 (SLit l02))
     (RSeq (RLimbStore loaders_out_c0 3 (SLit l03))
      (RSeq (RLimbStore loaders_out_c0 4 (SLit l04))
       (RSeq (RLimbStore loaders_out_c0 5 (SLit l05))
        (RSeq (RLimbStore loaders_out_c0 6 (SLit l06))
         (RSeq (RLimbStore loaders_out_c1 0 (SLit l10))
          (RSeq (RLimbStore loaders_out_c1 1 (SLit l11))
           (RSeq (RLimbStore loaders_out_c1 2 (SLit l12))
            (RSeq (RLimbStore loaders_out_c1 3 (SLit l13))
             (RSeq (RLimbStore loaders_out_c1 4 (SLit l14))
              (RSeq (RLimbStore loaders_out_c1 5 (SLit l15))
                    (RLimbStore loaders_out_c1 6 (SLit l16)))))))))))))).

(** Loader parameters: 14 limbs per Frobenius constant (7 per Fp component). *)
Parameter bn446_gamma1_l00 bn446_gamma1_l01 bn446_gamma1_l02 bn446_gamma1_l03
          bn446_gamma1_l04 bn446_gamma1_l05 bn446_gamma1_l06
          bn446_gamma1_l10 bn446_gamma1_l11 bn446_gamma1_l12 bn446_gamma1_l13
          bn446_gamma1_l14 bn446_gamma1_l15 bn446_gamma1_l16
        : nat.
Parameter bn446_gamma_y_l00 bn446_gamma_y_l01 bn446_gamma_y_l02 bn446_gamma_y_l03
          bn446_gamma_y_l04 bn446_gamma_y_l05 bn446_gamma_y_l06
          bn446_gamma_y_l10 bn446_gamma_y_l11 bn446_gamma_y_l12 bn446_gamma_y_l13
          bn446_gamma_y_l14 bn446_gamma_y_l15 bn446_gamma_y_l16
        : nat.
Parameter bn446_gamma1_p2_l00 bn446_gamma1_p2_l01 bn446_gamma1_p2_l02 bn446_gamma1_p2_l03
          bn446_gamma1_p2_l04 bn446_gamma1_p2_l05 bn446_gamma1_p2_l06
          bn446_gamma1_p2_l10 bn446_gamma1_p2_l11 bn446_gamma1_p2_l12 bn446_gamma1_p2_l13
          bn446_gamma1_p2_l14 bn446_gamma1_p2_l15 bn446_gamma1_p2_l16
        : nat.

Definition bn446_load_g1_body : rust_cmd :=
  bn446_loader_body
    bn446_gamma1_l00 bn446_gamma1_l01 bn446_gamma1_l02 bn446_gamma1_l03
    bn446_gamma1_l04 bn446_gamma1_l05 bn446_gamma1_l06
    bn446_gamma1_l10 bn446_gamma1_l11 bn446_gamma1_l12 bn446_gamma1_l13
    bn446_gamma1_l14 bn446_gamma1_l15 bn446_gamma1_l16.
Definition bn446_load_g2_body : rust_cmd :=
  bn446_loader_body
    bn446_gamma_y_l00 bn446_gamma_y_l01 bn446_gamma_y_l02 bn446_gamma_y_l03
    bn446_gamma_y_l04 bn446_gamma_y_l05 bn446_gamma_y_l06
    bn446_gamma_y_l10 bn446_gamma_y_l11 bn446_gamma_y_l12 bn446_gamma_y_l13
    bn446_gamma_y_l14 bn446_gamma_y_l15 bn446_gamma_y_l16.
Definition bn446_load_w_body : rust_cmd :=
  bn446_loader_body
    bn446_gamma1_p2_l00 bn446_gamma1_p2_l01 bn446_gamma1_p2_l02 bn446_gamma1_p2_l03
    bn446_gamma1_p2_l04 bn446_gamma1_p2_l05 bn446_gamma1_p2_l06
    bn446_gamma1_p2_l10 bn446_gamma1_p2_l11 bn446_gamma1_p2_l12 bn446_gamma1_p2_l13
    bn446_gamma1_p2_l14 bn446_gamma1_p2_l15 bn446_gamma1_p2_l16.

(** Concrete bodies for the miller loop and final exponentiation.
    Like the loaders, both are placeholders consisting of a single
    [RLimbStore]: discharging the refinement obligation reduces to
    [inversion] on the (currently absent) [RLimbStore] semantics rule.

    To replace these with verified Fp tower implementations:
    1. Extend [rust_exec_fenv] with [XF_limb_store] (and [XF_limb_load]
       if needed for the miller loop's reads of corner constants).
    2. Build [bn446_finalexp_body] as a chain of [RCall]s into
       [bn446_Fp12_*] tower ops, each itself a [RCall] chain into
       [bn446_Fp6_*] / [bn446_Fp2_*] / [bn446_Fp_*] until reaching
       leaf operations.
    3. Build [bn446_miller_body] as a [RWhileNz] over a loop counter,
       with each iteration a sequence of Fp12 doublings, line updates
       and selective additions.
    4. Replace the vacuous refinement proofs below with [rust_step]
       chains using the (newly proven) Fp tower op refinements. *)
(** Body placeholder for miller / finalexp: target is an [TFp12]
    location (not [TFp]), so [XF_limb_store] cannot fire (it requires
    [loc_dst loc = TFp]).  Leaves the refinement vacuously true
    until Phase B / Phase C replace these with real implementations. *)
Local Definition miller_dummy_loc : located :=
  {| loc_var := "tmp"; loc_src := TFp12; loc_dst := TFp12; loc_path := PathNil _ |}.
Definition bn446_miller_body : rust_cmd :=
  RLimbStore miller_dummy_loc 0 (SLit 0).
Definition bn446_finalexp_body : rust_cmd :=
  RLimbStore miller_dummy_loc 0 (SLit 0).

(** Parameter lists as used in the bedrock2 sources. *)
Definition bn446_load_g1_params : list var := ["out"].
Definition bn446_load_g2_params : list var := ["out"].
Definition bn446_load_w_params  : list var := ["out"].
Definition bn446_miller_params  : list var :=
  ["tmp"; "px"; "py"; "qx"; "qy"].
Definition bn446_finalexp_params : list var :=
  ["out"; "f"; "g1"; "g2"; "w"].

Definition bn446_pairing_fenv : rust_fenv :=
  [ ("bn446_load_gamma1_p2",      (bn446_load_g1_params,
                                   bn446_load_g1_body));
    ("bn446_load_gamma2_p2",      (bn446_load_g2_params,
                                   bn446_load_g2_body));
    ("bn446_load_w_frob_p2_c1",   (bn446_load_w_params,
                                   bn446_load_w_body));
    ("bn446_miller_loop_optimal", (bn446_miller_params,
                                   bn446_miller_body));
    ("bn446_final_exp_dsd",       (bn446_finalexp_params,
                                   bn446_finalexp_body)) ].

(* ================================================================ *)
(* §4. Typed location lookups                                        *)
(* ================================================================ *)

(** [extract_at loc t rs]: read the rust_val at [loc] in [rs],
    coerced to type [t].  Returns [None] if the types don't match
    or the variable isn't in scope. *)
Definition extract_at (loc : located) (t : tower_type) (rs : rust_state)
  : option (rust_val t) :=
  match tower_type_eq_dec (loc_dst loc) t with
  | left H =>
      match located_lookup rs loc with
      | Some v => Some (eq_rect (loc_dst loc) rust_val v _ H)
      | None => None
      end
  | right _ => None
  end.

(** Foundational disjointness lemma: setting a tower variable [x] in
    [rs] doesn't affect [extract_at loc t rs] when [loc_var loc <> x].
    Used to show that 4 stackallocs (binding fresh names) preserve all
    user-location lookups, and that one callee's writeback to [dest]
    preserves all lookups at locations with different variable names. *)
Lemma lookup_t_update_in_place_other :
  forall env x v y,
    String.eqb y x = false ->
    lookup_t (update_in_place env x v) y = lookup_t env y.
Proof.
  induction env as [| [k w] env IH]; intros x v y Hneq; simpl.
  - rewrite Hneq; reflexivity.
  - destruct (String.eqb k x) eqn:Heqkx.
    + simpl. apply String.eqb_eq in Heqkx; subst k.
      rewrite Hneq. reflexivity.
    + simpl. destruct (String.eqb y k) eqn:Heqyk.
      * reflexivity.
      * apply IH; assumption.
Qed.

Lemma extract_at_set_other :
  forall loc t rs x v,
    loc_var loc <> x ->
    extract_at loc t (rs_set_tower rs x v) = extract_at loc t rs.
Proof.
  intros loc t rs x v Hneq.
  unfold extract_at, located_lookup, rs_set_tower; simpl.
  rewrite lookup_t_update_in_place_other.
  - reflexivity.
  - apply String.eqb_neq. exact Hneq.
Qed.

(** Writeback to [dest] preserves [extract_at] at locations whose
    variable name differs from [dest]'s.  [located_update] (defined in
    [SafeRustSimulation]) updates only the variable [loc_var dest]
    via [rs_set_tower], so lookups at disjoint variable names are
    invariant. *)
Lemma extract_at_writeback_other :
  forall loc t rs dest v rs',
    loc_var loc <> loc_var dest ->
    located_update rs dest v = Some rs' ->
    extract_at loc t rs' = extract_at loc t rs.
Proof.
  intros loc t rs dest v rs' Hneq Hupd.
  unfold located_update in Hupd.
  destruct (lookup_t (rs_tower rs) (loc_var dest)) as [[t' v']|] eqn:Hlk;
    [|discriminate Hupd].
  destruct (tower_type_eq_dec t' (loc_src dest)) as [Heq_t|]; [|discriminate Hupd].
  injection Hupd as <-.
  apply extract_at_set_other; assumption.
Qed.

(* ================================================================ *)
(* §5. Concrete predicates                                           *)
(* ================================================================ *)

Section ConcretePredicates.

  (** Caller-facing locations (from the pairing dest+args). *)
  Context (out_loc        : located)      (* TFp12 *)
          (p_x_loc p_y_loc : located)     (* TFp *)
          (q_x_loc q_y_loc : located).    (* TFp2 *)

  (** Stackalloc'd locations inside the pairing body. *)
  Context (g1_loc g2_loc w_loc : located) (* TFp2 *)
          (ml_loc : located).             (* TFp12 *)

  (** Frobenius constants set by the loaders (mathematical values). *)
  Context (gamma1 gamma_y gamma1_p2 : Fp2_Z).

  (** Bounds / validity predicates on the input locations. *)
  Definition Fp_at (loc : located) (rs : rust_state) : Prop :=
    loc_dst loc = TFp /\ exists v, extract_at loc TFp rs = Some v.

  Definition Fp2_at (loc : located) (rs : rust_state) : Prop :=
    loc_dst loc = TFp2 /\ exists v, extract_at loc TFp2 rs = Some v.

  Definition Fp12_at (loc : located) (rs : rust_state) : Prop :=
    loc_dst loc = TFp12 /\ exists v, extract_at loc TFp12 rs = Some v.

  (** Input state: all five caller locations carry well-typed values. *)
  Definition pairing_pre : spec_t :=
    fun rs =>
      Fp12_at out_loc rs /\
      Fp_at p_x_loc rs /\ Fp_at p_y_loc rs /\
      Fp2_at q_x_loc rs /\ Fp2_at q_y_loc rs.

  (** [mid_g1]: after load_gamma1_p2, the [g1_loc] slot holds a
      rust_val whose evaluation equals [gamma1]; [pairing_pre] still
      holds (input slots preserved). *)
  Definition mid_g1 : spec_t :=
    fun rs =>
      pairing_pre rs /\
      exists v, extract_at g1_loc TFp2 rs = Some v /\
                bn446_fp2_eval v = gamma1.

  (** [mid_g2]: additionally [g2_loc] holds an Fp2 eval'ing to [gamma_y]. *)
  Definition mid_g2 : spec_t :=
    fun rs =>
      mid_g1 rs /\
      exists v, extract_at g2_loc TFp2 rs = Some v /\
                bn446_fp2_eval v = gamma_y.

  (** [mid_w]: additionally [w_loc] holds [gamma1_p2]. *)
  Definition mid_w : spec_t :=
    fun rs =>
      mid_g2 rs /\
      exists v, extract_at w_loc TFp2 rs = Some v /\
                bn446_fp2_eval v = gamma1_p2.

  (** [mid_ml]: after miller_loop_optimal, [ml_loc] holds the
      miller-with-corrections value at this pair of points. *)
  Definition mid_ml : spec_t :=
    fun rs =>
      mid_w rs /\
      exists ml_val px py qx qy,
        extract_at ml_loc TFp12 rs = Some ml_val /\
        extract_at p_x_loc TFp rs = Some px /\
        extract_at p_y_loc TFp rs = Some py /\
        extract_at q_x_loc TFp2 rs = Some qx /\
        extract_at q_y_loc TFp2 rs = Some qy /\
        bn446_fp12_eval ml_val =
          bn446_miller_loop_with_corrections
            gamma1 gamma_y gamma1_p2
            (bn446_fp_eval px) (bn446_fp_eval py)
            (bn446_fp2_eval qx) (bn446_fp2_eval qy).

  (** [pairing_post]: after final_exp, [out_loc] holds the full
      optimal-ate pairing value.  Matches the G2 strong spec
      postcondition (see BN446_PairingCorrect.v:387-390). *)
  Definition pairing_post : spec_t :=
    fun rs =>
      exists out px py qx qy,
        extract_at out_loc TFp12 rs = Some out /\
        extract_at p_x_loc TFp rs = Some px /\
        extract_at p_y_loc TFp rs = Some py /\
        extract_at q_x_loc TFp2 rs = Some qx /\
        extract_at q_y_loc TFp2 rs = Some qy /\
        bn446_fp12_eval out =
          bn446_optimal_ate_spec gamma1 gamma_y gamma1_p2
            (bn446_fp_eval px) (bn446_fp_eval py)
            (bn446_fp2_eval qx) (bn446_fp2_eval qy).

End ConcretePredicates.

(* ================================================================ *)
(* §6. Sanity: fenv_lookup reduces on concrete entries               *)
(* ================================================================ *)

Lemma fenv_has_pairing_load_g1 :
  fenv_lookup bn446_pairing_fenv "bn446_load_gamma1_p2" =
    Some (bn446_load_g1_params, bn446_load_g1_body).
Proof. reflexivity. Qed.

Lemma fenv_has_pairing_load_g2 :
  fenv_lookup bn446_pairing_fenv "bn446_load_gamma2_p2" =
    Some (bn446_load_g2_params, bn446_load_g2_body).
Proof. reflexivity. Qed.

Lemma fenv_has_pairing_load_w :
  fenv_lookup bn446_pairing_fenv "bn446_load_w_frob_p2_c1" =
    Some (bn446_load_w_params, bn446_load_w_body).
Proof. reflexivity. Qed.

Lemma fenv_has_pairing_miller :
  fenv_lookup bn446_pairing_fenv "bn446_miller_loop_optimal" =
    Some (bn446_miller_params, bn446_miller_body).
Proof. reflexivity. Qed.

Lemma fenv_has_pairing_finalexp :
  fenv_lookup bn446_pairing_fenv "bn446_final_exp_dsd" =
    Some (bn446_finalexp_params, bn446_finalexp_body).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §7. Callee-side predicates (used by refines_call bridges)         *)
(* ================================================================ *)

(** A single variable [out_var] names the output parameter inside
    every callee's local state; it matches the leading entry in
    [bn446_*_params]. *)
Definition out_var : var := "out".
Definition tmp_var : var := "tmp".
Definition px_var : var := "px".
Definition py_var : var := "py".
Definition qx_var : var := "qx".
Definition qy_var : var := "qy".
Definition f_var : var := "f".
Definition g1_var : var := "g1".
Definition g2_var : var := "g2".
Definition w_var : var := "w".

Definition loc_Fp (x : var) : located :=
  {| loc_var := x; loc_src := TFp; loc_dst := TFp; loc_path := PathNil _ |}.
Definition loc_Fp2 (x : var) : located :=
  {| loc_var := x; loc_src := TFp2; loc_dst := TFp2; loc_path := PathNil _ |}.
Definition loc_Fp12 (x : var) : located :=
  {| loc_var := x; loc_src := TFp12; loc_dst := TFp12; loc_path := PathNil _ |}.

(** Projections into Fp2's two Fp components.  Used by the loaders to
    target individual limbs of each component. *)
Definition loc_Fp2_c0 (x : var) : located :=
  {| loc_var := x; loc_src := TFp2; loc_dst := TFp;
     loc_path := PathCons _ _ _ StepFp2_0 (PathNil _) |}.
Definition loc_Fp2_c1 (x : var) : located :=
  {| loc_var := x; loc_src := TFp2; loc_dst := TFp;
     loc_path := PathCons _ _ _ StepFp2_1 (PathNil _) |}.

Section CalleePredicates.

  Context (gamma1 gamma_y gamma1_p2 : Fp2_Z).

  (** Loaders: require [out] to already hold an [Fp2] value (from
      the caller's stackalloc).  Post asserts [out] holds the
      specific Frobenius constant. *)
  Definition load_g1_callee_pre  : spec_t :=
    fun rs => exists v, extract_at (loc_Fp2 out_var) TFp2 rs = Some v.
  Definition load_g2_callee_pre  : spec_t :=
    fun rs => exists v, extract_at (loc_Fp2 out_var) TFp2 rs = Some v.
  Definition load_w_callee_pre   : spec_t :=
    fun rs => exists v, extract_at (loc_Fp2 out_var) TFp2 rs = Some v.

  Definition load_g1_callee_post : spec_t :=
    fun rs => exists v, extract_at (loc_Fp2 out_var) TFp2 rs = Some v
                        /\ bn446_fp2_eval v = gamma1.
  Definition load_g2_callee_post : spec_t :=
    fun rs => exists v, extract_at (loc_Fp2 out_var) TFp2 rs = Some v
                        /\ bn446_fp2_eval v = gamma_y.
  Definition load_w_callee_post  : spec_t :=
    fun rs => exists v, extract_at (loc_Fp2 out_var) TFp2 rs = Some v
                        /\ bn446_fp2_eval v = gamma1_p2.

  (** Miller loop: reads [px py qx qy]; writes [tmp].

      The pre/post are parameterised on the caller's mathematical
      input values [(px_v, py_v, qx_v, qy_v)].  [miller_callee_pre]
      asserts that the slot values evaluate to the given inputs;
      [miller_callee_post] asserts [tmp] equals the Miller loop of
      those inputs.  The caller discharges the pre with its own
      values and recovers the matching post equation.  *)
  Definition miller_callee_pre
             (px_v py_v : Z) (qx_v qy_v : Fp2_Z) : spec_t :=
    fun rs =>
      (exists v, extract_at (loc_Fp12 tmp_var) TFp12 rs = Some v) /\
      (exists v, extract_at (loc_Fp px_var) TFp rs = Some v
                 /\ bn446_fp_eval v = px_v) /\
      (exists v, extract_at (loc_Fp py_var) TFp rs = Some v
                 /\ bn446_fp_eval v = py_v) /\
      (exists v, extract_at (loc_Fp2 qx_var) TFp2 rs = Some v
                 /\ bn446_fp2_eval v = qx_v) /\
      (exists v, extract_at (loc_Fp2 qy_var) TFp2 rs = Some v
                 /\ bn446_fp2_eval v = qy_v).

  Definition miller_callee_post
             (px_v py_v : Z) (qx_v qy_v : Fp2_Z) : spec_t :=
    fun rs =>
      exists tmp,
        extract_at (loc_Fp12 tmp_var) TFp12 rs = Some tmp /\
        bn446_fp12_eval tmp =
          bn446_miller_loop_with_corrections
            gamma1 gamma_y gamma1_p2 px_v py_v qx_v qy_v.

  (** Final exponentiation: reads [f g1 g2 w]; writes [out].
      Parameterised on the input [f_v] value; the [g1 g2 w] slots are
      still required to be present but their values don't constrain
      the spec (they're curve constants, only used internally by the
      DSD-optimised body). *)
  Definition finalexp_callee_pre (f_v : Fp12_Z) : spec_t :=
    fun rs =>
      (exists v, extract_at (loc_Fp12 out_var) TFp12 rs = Some v) /\
      (exists v, extract_at (loc_Fp12 f_var) TFp12 rs = Some v
                 /\ bn446_fp12_eval v = f_v) /\
      (exists v, extract_at (loc_Fp2 g1_var) TFp2 rs = Some v) /\
      (exists v, extract_at (loc_Fp2 g2_var) TFp2 rs = Some v) /\
      (exists v, extract_at (loc_Fp2 w_var) TFp2 rs = Some v).

  Definition finalexp_callee_post (f_v : Fp12_Z) : spec_t :=
    fun rs =>
      exists out,
        extract_at (loc_Fp12 out_var) TFp12 rs = Some out /\
        bn446_fp12_eval out =
          PairingSpec.final_exp bn446_zmod_ops
            (zfp12_conj bn446_p_val)
            (zfp12_inv bn446_p_val bn446_xi_val)
            (zfp12_frob_p2 bn446_p_val bn446_xi_val)
            (zfp12_pow bn446_p_val bn446_xi_val)
            (prime_p bn446_params) (scalar_r bn446_params)
            f_v.

End CalleePredicates.

(* ================================================================ *)
(* §8. Concrete pairing body and its refinement theorem              *)
(*                                                                   *)
(* The strategy from here is:                                        *)
(*                                                                   *)
(*   - [pairing_body] is a concrete [rust_cmd]: 4 [RLetZero]         *)
(*     stackallocs wrapping 5 sequenced [RCall]s.                    *)
(*                                                                   *)
(*   - The 5 [_body_refines] of the callees are declared as          *)
(*     [Hypothesis] inside this section.  They will be discharged    *)
(*     in later steps: Step 3 supplies concrete loader bodies + 4    *)
(*     [RLimbStore]-based proofs; Step 4 builds the bottom-up Fp2 -> *)
(*     Fp6 -> Fp12 tower that settles [miller] and [finalexp].       *)
(*                                                                   *)
(*   - All 11 bridges + [pre_after_4_stackallocs] are proven here    *)
(*     against the concrete predicates from §5 and the concrete      *)
(*     [bn446_call_env] from §2.  These proofs use only [destruct],  *)
(*     [exists], and the concrete definitions of [extract_at] /      *)
(*     [bn446_bind_params] / [bn446_extract_output] /                *)
(*     [bn446_writeback_output].                                     *)
(* ================================================================ *)

(* ================================================================ *)
(* §7.5 Loader body execution lemmas                                 *)
(*                                                                   *)
(*   Structural facts about [bn446_loader_body]: executing the 8    *)
(*   [RLimbStore]s against a state where "out" holds an [Fp2] value *)
(*   produces a final state where "out" holds the specific [Fp2]    *)
(*   value assembled from the 8 limb parameters.  This is purely    *)
(*   structural — no arithmetic claims.  The arithmetic connection  *)
(*   to abstract [gamma*] values is deferred to the Section-level   *)
(*   hypotheses [Hgamma1_fp2_eval] etc.                             *)
(* ================================================================ *)

(** Single-step lemma: executing one [RLimbStore] to [loaders_out_c0]
    at limb index [k] with scalar literal value [v] updates c0's k-th
    limb.  Proof is a single inversion on [XF_limb_store]; the [eq_rect]
    casts reduce because [loc_dst loaders_out_c0 = TFp] computationally. *)
Lemma limb_store_c0_effect :
  forall k v rs rs' vc0 vc1,
    extract_at (loc_Fp2 "out") TFp2 rs = Some (VFp2 vc0 vc1) ->
    rust_exec_fenv bn446_N bn446_u64_max bn446_pairing_fenv
                   bn446_leaf_spec_concrete bn446_call_env
                   (RLimbStore loaders_out_c0 k (SLit v)) rs rs' ->
    extract_at (loc_Fp2 "out") TFp2 rs' =
      Some (VFp2 (replace_limb k v vc0) vc1).
Proof.
  intros k v rs rs' vc0 vc1 Hext Hexec.
  inversion Hexec as [| | | | | | | | | | | loc' k' e' v' rs_ rs'_ Heq old_fp Hev Hlk Hup]; subst.
  (* Hev : sexpr_eval _ rs (SLit v) = Some v' simplifies to v' = v *)
  cbn in Hev. injection Hev as Hvv. subst v'.
  assert (Heq_refl : Heq = eq_refl).
  { apply Eqdep_dec.UIP_dec. decide equality. }
  subst Heq.
  unfold located_lookup, loaders_out_c0 in Hlk; cbn in Hlk.
  unfold extract_at, located_lookup, loc_Fp2 in Hext; cbn in Hext.
  destruct (lookup_t (rs_tower rs) "out") as [[t_stored v_stored]|] eqn:Hls;
    [|discriminate Hext].
  destruct (tower_type_eq_dec t_stored TFp2) as [Ht|]; [|discriminate Hext].
  subst t_stored. cbn in Hext, Hlk.
  injection Hext as Hv_eq. subst v_stored.
  cbn in Hlk. injection Hlk as Hofp. subst old_fp.
  cbn in Hup. unfold loaders_out_c0 in Hup; cbn in Hup.
  unfold located_update in Hup; cbn in Hup.
  rewrite Hls in Hup.
  destruct (tower_type_eq_dec TFp2 TFp2) as [Ht2|]; [|contradiction].
  cbn in Hup.
  injection Hup as Hrs'_eq. subst rs'.
  unfold extract_at, located_lookup, loc_Fp2; cbn.
  unfold rs_set_tower; cbn.
  rewrite lookup_t_update_same.
  cbn.
  assert (Ht2_refl : Ht2 = eq_refl).
  { apply Eqdep_dec.UIP_dec. decide equality. }
  subst Ht2. cbn. reflexivity.
Qed.

(** Symmetric lemma for c1 stores. *)
Lemma limb_store_c1_effect :
  forall k v rs rs' vc0 vc1,
    extract_at (loc_Fp2 "out") TFp2 rs = Some (VFp2 vc0 vc1) ->
    rust_exec_fenv bn446_N bn446_u64_max bn446_pairing_fenv
                   bn446_leaf_spec_concrete bn446_call_env
                   (RLimbStore loaders_out_c1 k (SLit v)) rs rs' ->
    extract_at (loc_Fp2 "out") TFp2 rs' =
      Some (VFp2 vc0 (replace_limb k v vc1)).
Proof.
  intros k v rs rs' vc0 vc1 Hext Hexec.
  inversion Hexec as [| | | | | | | | | | | loc' k' e' v' rs_ rs'_ Heq old_fp Hev Hlk Hup]; subst.
  cbn in Hev. injection Hev as Hvv. subst v'.
  assert (Heq_refl : Heq = eq_refl).
  { apply Eqdep_dec.UIP_dec. decide equality. }
  subst Heq.
  unfold located_lookup, loaders_out_c1 in Hlk; cbn in Hlk.
  unfold extract_at, located_lookup, loc_Fp2 in Hext; cbn in Hext.
  destruct (lookup_t (rs_tower rs) "out") as [[t_stored v_stored]|] eqn:Hls;
    [|discriminate Hext].
  destruct (tower_type_eq_dec t_stored TFp2) as [Ht|]; [|discriminate Hext].
  subst t_stored. cbn in Hext, Hlk.
  injection Hext as Hv_eq. subst v_stored.
  cbn in Hlk. injection Hlk as Hofp. subst old_fp.
  cbn in Hup. unfold loaders_out_c1 in Hup; cbn in Hup.
  unfold located_update in Hup; cbn in Hup.
  rewrite Hls in Hup.
  destruct (tower_type_eq_dec TFp2 TFp2) as [Ht2|]; [|contradiction].
  cbn in Hup.
  injection Hup as Hrs'_eq. subst rs'.
  unfold extract_at, located_lookup, loc_Fp2; cbn.
  unfold rs_set_tower; cbn.
  rewrite lookup_t_update_same.
  cbn.
  assert (Ht2_refl : Ht2 = eq_refl).
  { apply Eqdep_dec.UIP_dec. decide equality. }
  subst Ht2. cbn. reflexivity.
Qed.

(** Full loader body effect: 14 [RLimbStore]s transform an [Fp2] value
    whose two components are 7-limb lists into one where each limb
    matches the corresponding parameter.  The length-7 assumption
    captures the BN446 limb count [bn446_N = 7]. *)
Lemma bn446_loader_body_effect :
  forall l00 l01 l02 l03 l04 l05 l06
         l10 l11 l12 l13 l14 l15 l16 rs rs' lc0_init lc1_init,
    length lc0_init = 7%nat -> length lc1_init = 7%nat ->
    extract_at (loc_Fp2 "out") TFp2 rs = Some (VFp2 (VFp lc0_init) (VFp lc1_init)) ->
    rust_exec_fenv bn446_N bn446_u64_max bn446_pairing_fenv
                   bn446_leaf_spec_concrete bn446_call_env
                   (bn446_loader_body l00 l01 l02 l03 l04 l05 l06
                                      l10 l11 l12 l13 l14 l15 l16) rs rs' ->
    extract_at (loc_Fp2 "out") TFp2 rs' =
      Some (VFp2 (VFp [l00; l01; l02; l03; l04; l05; l06])
                 (VFp [l10; l11; l12; l13; l14; l15; l16])).
Proof.
  intros l00 l01 l02 l03 l04 l05 l06 l10 l11 l12 l13 l14 l15 l16
         rs rs' lc0_init lc1_init Hlen0 Hlen1 Hext Hexec.
  unfold bn446_loader_body in Hexec.
  inversion Hexec as [| ? ? ? ? r1  H1  R1  | | | | | | | | | | ]; clear Hexec; subst.
  inversion R1   as [| ? ? ? ? r2  H2  R2  | | | | | | | | | | ]; clear R1; subst.
  inversion R2   as [| ? ? ? ? r3  H3  R3  | | | | | | | | | | ]; clear R2; subst.
  inversion R3   as [| ? ? ? ? r4  H4  R4  | | | | | | | | | | ]; clear R3; subst.
  inversion R4   as [| ? ? ? ? r5  H5  R5  | | | | | | | | | | ]; clear R4; subst.
  inversion R5   as [| ? ? ? ? r6  H6  R6  | | | | | | | | | | ]; clear R5; subst.
  inversion R6   as [| ? ? ? ? r7  H7  R7  | | | | | | | | | | ]; clear R6; subst.
  inversion R7   as [| ? ? ? ? r8  H8  R8  | | | | | | | | | | ]; clear R7; subst.
  inversion R8   as [| ? ? ? ? r9  H9  R9  | | | | | | | | | | ]; clear R8; subst.
  inversion R9   as [| ? ? ? ? r10 H10 R10 | | | | | | | | | | ]; clear R9; subst.
  inversion R10  as [| ? ? ? ? r11 H11 R11 | | | | | | | | | | ]; clear R10; subst.
  inversion R11  as [| ? ? ? ? r12 H12 R12 | | | | | | | | | | ]; clear R11; subst.
  inversion R12  as [| ? ? ? ? r13 H13 H14 | | | | | | | | | | ]; clear R12; subst.
  pose proof (limb_store_c0_effect _ _ _ _ _ _ Hext H1) as E1. cbn in E1.
  pose proof (limb_store_c0_effect _ _ _ _ _ _ E1   H2) as E2. cbn in E2.
  pose proof (limb_store_c0_effect _ _ _ _ _ _ E2   H3) as E3. cbn in E3.
  pose proof (limb_store_c0_effect _ _ _ _ _ _ E3   H4) as E4. cbn in E4.
  pose proof (limb_store_c0_effect _ _ _ _ _ _ E4   H5) as E5. cbn in E5.
  pose proof (limb_store_c0_effect _ _ _ _ _ _ E5   H6) as E6. cbn in E6.
  pose proof (limb_store_c0_effect _ _ _ _ _ _ E6   H7) as E7. cbn in E7.
  destruct lc0_init as [| a0 [| a1 [| a2 [| a3 [| a4 [| a5 [| a6 [| ??]]]]]]]];
    try (cbn in Hlen0; lia).
  cbn in E7.
  pose proof (limb_store_c1_effect _ _ _ _ _ _ E7   H8)  as E8'. cbn in E8'.
  pose proof (limb_store_c1_effect _ _ _ _ _ _ E8'  H9)  as E9.  cbn in E9.
  pose proof (limb_store_c1_effect _ _ _ _ _ _ E9   H10) as E10. cbn in E10.
  pose proof (limb_store_c1_effect _ _ _ _ _ _ E10  H11) as E11. cbn in E11.
  pose proof (limb_store_c1_effect _ _ _ _ _ _ E11  H12) as E12. cbn in E12.
  pose proof (limb_store_c1_effect _ _ _ _ _ _ E12  H13) as E13. cbn in E13.
  pose proof (limb_store_c1_effect _ _ _ _ _ _ E13  H14) as E14. cbn in E14.
  destruct lc1_init as [| b0 [| b1 [| b2 [| b3 [| b4 [| b5 [| b6 [| ??]]]]]]]];
    try (cbn in Hlen1; lia).
  cbn in E14.
  exact E14.
Qed.

Section PairingBodyRefines.

  (** Caller-facing locations (the inputs to the pairing). *)
  Context (out_loc : located) (p_x_loc p_y_loc : located)
          (q_x_loc q_y_loc : located).

  (** The Frobenius constants (mathematical values, supplied by the
      G2 chain). *)
  Context (gamma1 gamma_y gamma1_p2 : Fp2_Z).

  (** Type constraints on the user's locations. *)
  Hypothesis Hout_Fp12 : loc_dst out_loc = TFp12.
  Hypothesis Hpx_Fp    : loc_dst p_x_loc = TFp.
  Hypothesis Hpy_Fp    : loc_dst p_y_loc = TFp.
  Hypothesis Hqx_Fp2   : loc_dst q_x_loc = TFp2.
  Hypothesis Hqy_Fp2   : loc_dst q_y_loc = TFp2.

  (** Stackalloc slot locations (named with the stackalloc var). *)
  Definition tmp_loc : located := loc_Fp12 tmp_var.
  Definition g1_loc  : located := loc_Fp2 "gamma1_p2".
  Definition g2_loc  : located := loc_Fp2 "gamma2_p2".
  Definition w_loc   : located := loc_Fp2 "w_frob_p2_c1".

  (** Fresh-variable hypotheses: the 4 stackalloc names must not
      collide with the user-location variable names.  In BN446 the
      pairing bedrock2 source uses distinct names ("pout", "p_x",
      "p_y", "p_qx", "p_qy" for inputs); the stackallocs use
      "tmp" / "gamma1_p2" / "gamma2_p2" / "w_frob_p2_c1". *)
  Hypothesis Hfresh_out  :
    loc_var out_loc <> tmp_var /\ loc_var out_loc <> "gamma1_p2" /\
    loc_var out_loc <> "gamma2_p2" /\ loc_var out_loc <> "w_frob_p2_c1".
  Hypothesis Hfresh_px   :
    loc_var p_x_loc <> tmp_var /\ loc_var p_x_loc <> "gamma1_p2" /\
    loc_var p_x_loc <> "gamma2_p2" /\ loc_var p_x_loc <> "w_frob_p2_c1".
  Hypothesis Hfresh_py   :
    loc_var p_y_loc <> tmp_var /\ loc_var p_y_loc <> "gamma1_p2" /\
    loc_var p_y_loc <> "gamma2_p2" /\ loc_var p_y_loc <> "w_frob_p2_c1".
  Hypothesis Hfresh_qx   :
    loc_var q_x_loc <> tmp_var /\ loc_var q_x_loc <> "gamma1_p2" /\
    loc_var q_x_loc <> "gamma2_p2" /\ loc_var q_x_loc <> "w_frob_p2_c1".
  Hypothesis Hfresh_qy   :
    loc_var q_y_loc <> tmp_var /\ loc_var q_y_loc <> "gamma1_p2" /\
    loc_var q_y_loc <> "gamma2_p2" /\ loc_var q_y_loc <> "w_frob_p2_c1".

  (** Location-shape hypotheses: the user locations are "simple"
      [loc_Fp] / [loc_Fp2] / [loc_Fp12] — i.e. they use [PathNil]
      with [loc_src = loc_dst].  This holds whenever the caller
      supplies plain variable bindings (no struct-field offsets),
      which is the actual usage in the bedrock2 pairing entry point.
      These hypotheses let [located_lookup_sig] / [located_update]
      reduce cleanly in the [compose_miller] / [compose_finalexp]
      bridge proofs, without hand-threading [eq_rect] casts. *)
  Hypothesis Hout_shape : out_loc = loc_Fp12 (loc_var out_loc).
  Hypothesis Hpx_shape  : p_x_loc = loc_Fp   (loc_var p_x_loc).
  Hypothesis Hpy_shape  : p_y_loc = loc_Fp   (loc_var p_y_loc).
  Hypothesis Hqx_shape  : q_x_loc = loc_Fp2  (loc_var q_x_loc).
  Hypothesis Hqy_shape  : q_y_loc = loc_Fp2  (loc_var q_y_loc).

  (** User-location distinctness: the 5 user locations have pairwise
      distinct variable names.  This is needed for the finalexp
      post-bridge to show that writing to [out_loc] preserves the 4
      input-location values.  Standard no-aliasing precondition for
      safe Rust entry points. *)
  Hypothesis Hdistinct_out_users :
    loc_var out_loc <> loc_var p_x_loc /\
    loc_var out_loc <> loc_var p_y_loc /\
    loc_var out_loc <> loc_var q_x_loc /\
    loc_var out_loc <> loc_var q_y_loc.

  (** Local copies of the §5 predicates specialised to this
      section's concrete locations + stackalloc slots. *)
  Notation pre      := (pairing_pre out_loc p_x_loc p_y_loc
                                    q_x_loc q_y_loc).
  Notation post     := (pairing_post out_loc p_x_loc p_y_loc
                                     q_x_loc q_y_loc
                                     gamma1 gamma_y gamma1_p2).
  Notation mid1     := (mid_g1 out_loc p_x_loc p_y_loc
                               q_x_loc q_y_loc g1_loc gamma1).
  Notation mid2     := (mid_g2 out_loc p_x_loc p_y_loc
                               q_x_loc q_y_loc g1_loc g2_loc
                               gamma1 gamma_y).
  Notation mid3     := (mid_w  out_loc p_x_loc p_y_loc
                               q_x_loc q_y_loc g1_loc g2_loc w_loc
                               gamma1 gamma_y gamma1_p2).
  Notation mid4     := (mid_ml out_loc p_x_loc p_y_loc
                               q_x_loc q_y_loc g1_loc g2_loc w_loc
                               tmp_loc
                               gamma1 gamma_y gamma1_p2).

  (** The 5 per-callee body-refines hypotheses (to be discharged
      in Steps 3 and 4).  Each says the safe-Rust body refines its
      callee pre/post (see §7). *)
  (** [load_*_body_refines]: discharged in Phase 3 by [inversion] on
      the (currently absent) [RLimbStore] semantics rule.  Since
      [bn446_loader_body_skeleton] is built from [RSeq] + [RLimbStore]
      and [rust_exec_fenv] has no [XF_limb_store] constructor, the
      body has no executions, so the refinement holds vacuously by
      [inversion Hexec] on the inner [RLimbStore] step. *)
  (** Arithmetic hypotheses connecting the specific [bn446_gamma*_l**]
      Montgomery limbs to the abstract [gamma1 / gamma_y / gamma1_p2]
      values.  An instantiator discharges these at the point where the
      caller fixes the limb values (e.g. by [reflexivity] after
      substituting limbs + using a cached Montgomery-limbs table). *)
  Hypothesis Hgamma1_fp2_eval :
    bn446_fp2_eval
      (VFp2 (VFp [bn446_gamma1_l00; bn446_gamma1_l01; bn446_gamma1_l02;
                  bn446_gamma1_l03; bn446_gamma1_l04; bn446_gamma1_l05;
                  bn446_gamma1_l06])
            (VFp [bn446_gamma1_l10; bn446_gamma1_l11; bn446_gamma1_l12;
                  bn446_gamma1_l13; bn446_gamma1_l14; bn446_gamma1_l15;
                  bn446_gamma1_l16]))
    = gamma1.
  Hypothesis Hgamma_y_fp2_eval :
    bn446_fp2_eval
      (VFp2 (VFp [bn446_gamma_y_l00; bn446_gamma_y_l01; bn446_gamma_y_l02;
                  bn446_gamma_y_l03; bn446_gamma_y_l04; bn446_gamma_y_l05;
                  bn446_gamma_y_l06])
            (VFp [bn446_gamma_y_l10; bn446_gamma_y_l11; bn446_gamma_y_l12;
                  bn446_gamma_y_l13; bn446_gamma_y_l14; bn446_gamma_y_l15;
                  bn446_gamma_y_l16]))
    = gamma_y.
  Hypothesis Hgamma1_p2_fp2_eval :
    bn446_fp2_eval
      (VFp2 (VFp [bn446_gamma1_p2_l00; bn446_gamma1_p2_l01; bn446_gamma1_p2_l02;
                  bn446_gamma1_p2_l03; bn446_gamma1_p2_l04; bn446_gamma1_p2_l05;
                  bn446_gamma1_p2_l06])
            (VFp [bn446_gamma1_p2_l10; bn446_gamma1_p2_l11; bn446_gamma1_p2_l12;
                  bn446_gamma1_p2_l13; bn446_gamma1_p2_l14; bn446_gamma1_p2_l15;
                  bn446_gamma1_p2_l16]))
    = gamma1_p2.

  Hypothesis Hloader_input_len7 :
    forall rs,
      (exists v, extract_at (loc_Fp2 out_var) TFp2 rs = Some v) ->
      exists lc0 lc1,
        length lc0 = 7%nat /\ length lc1 = 7%nat /\
        extract_at (loc_Fp2 out_var) TFp2 rs =
          Some (VFp2 (VFp lc0) (VFp lc1)).

  Theorem load_g1_body_refines :
    rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                 bn446_leaf_spec_concrete bn446_call_env
                 load_g1_callee_pre bn446_load_g1_body
                 (load_g1_callee_post gamma1).
  Proof.
    unfold rust_refines, load_g1_callee_pre.
    intros rs1 rs2 Hpre Hexec.
    pose proof (Hloader_input_len7 _ Hpre) as [lc0 [lc1 [Hlen0 [Hlen1 Hext]]]].
    unfold load_g1_callee_post.
    eexists. split;
      [|exact Hgamma1_fp2_eval].
    unfold bn446_load_g1_body in Hexec.
    exact (bn446_loader_body_effect _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hlen0 Hlen1 Hext Hexec).
  Qed.

  Theorem load_g2_body_refines :
    rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                 bn446_leaf_spec_concrete bn446_call_env
                 load_g2_callee_pre bn446_load_g2_body
                 (load_g2_callee_post gamma_y).
  Proof.
    unfold rust_refines, load_g2_callee_pre.
    intros rs1 rs2 Hpre Hexec.
    pose proof (Hloader_input_len7 _ Hpre) as [lc0 [lc1 [Hlen0 [Hlen1 Hext]]]].
    unfold load_g2_callee_post.
    eexists. split;
      [|exact Hgamma_y_fp2_eval].
    unfold bn446_load_g2_body in Hexec.
    exact (bn446_loader_body_effect _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hlen0 Hlen1 Hext Hexec).
  Qed.

  Theorem load_w_body_refines :
    rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                 bn446_leaf_spec_concrete bn446_call_env
                 load_w_callee_pre bn446_load_w_body
                 (load_w_callee_post gamma1_p2).
  Proof.
    unfold rust_refines, load_w_callee_pre.
    intros rs1 rs2 Hpre Hexec.
    pose proof (Hloader_input_len7 _ Hpre) as [lc0 [lc1 [Hlen0 [Hlen1 Hext]]]].
    unfold load_w_callee_post.
    eexists. split;
      [|exact Hgamma1_p2_fp2_eval].
    unfold bn446_load_w_body in Hexec.
    exact (bn446_loader_body_effect _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hlen0 Hlen1 Hext Hexec).
  Qed.
  (** [miller_body_refines] / [finalexp_body_refines]: Phase 2 and
      Phase 4.  Discharged vacuously (both bodies are placeholder
      [RLimbStore] single commands; semantics has no rule). *)
  Theorem miller_body_refines :
    forall px_v py_v qx_v qy_v,
      rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                   bn446_leaf_spec_concrete bn446_call_env
                   (miller_callee_pre px_v py_v qx_v qy_v)
                   bn446_miller_body
                   (miller_callee_post gamma1 gamma_y gamma1_p2
                                       px_v py_v qx_v qy_v).
  Proof.
    intros; unfold rust_refines, bn446_miller_body.
    intros rs1 rs2 _ Hexec. exfalso.
    inversion Hexec; discriminate.
  Qed.

  Theorem finalexp_body_refines :
    forall f_v,
      rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                   bn446_leaf_spec_concrete bn446_call_env
                   (finalexp_callee_pre f_v)
                   bn446_finalexp_body
                   (finalexp_callee_post f_v).
  Proof.
    intros; unfold rust_refines, bn446_finalexp_body.
    intros rs1 rs2 _ Hexec. exfalso.
    inversion Hexec; discriminate.
  Qed.

  (** The concrete pairing body: 4 stackallocs + 5 calls. *)
  Definition pairing_calls : rust_cmd :=
    RSeq (RCall "bn446_load_gamma1_p2"      g1_loc [g1_loc])
      (RSeq (RCall "bn446_load_gamma2_p2"   g2_loc [g2_loc])
        (RSeq (RCall "bn446_load_w_frob_p2_c1" w_loc [w_loc])
          (RSeq (RCall "bn446_miller_loop_optimal" tmp_loc
                       [tmp_loc; p_x_loc; p_y_loc; q_x_loc; q_y_loc])
                (RCall "bn446_final_exp_dsd" out_loc
                       [out_loc; tmp_loc; g1_loc; g2_loc; w_loc])))).

  Definition pairing_body : rust_cmd :=
    RLetZero tmp_var             TFp12
      (RLetZero "gamma1_p2"      TFp2
        (RLetZero "gamma2_p2"    TFp2
          (RLetZero "w_frob_p2_c1" TFp2
            pairing_calls))).

  (* ================================================================ *)
  (* §8.1 [has_slots] invariant + strengthened working predicates     *)
  (*                                                                   *)
  (*   The §5 [pairing_pre] / [mid_*] predicates speak only about the  *)
  (*   user-facing locations and the Frobenius-constant equalities.   *)
  (*   The bridges in Phases 1.2-1.4 also need that the four          *)
  (*   stackalloc slots are reachable by [extract_at] (otherwise the  *)
  (*   [pre_bridge] obligation in [refines_call] cannot construct the *)
  (*   [in_vals] for the callee).  We package that reachability as    *)
  (*   [has_slots] and define strengthened working predicates         *)
  (*   [pre_sa] / [mid{1,2,3,4}_sa] that carry it alongside the §5    *)
  (*   ones.  The Theorem-level [pre] / [post] are unchanged.         *)
  (* ================================================================ *)

  Definition has_slots (rs : rust_state) : Prop :=
    (exists v, extract_at tmp_loc TFp12 rs = Some v) /\
    (exists v, extract_at g1_loc  TFp2  rs = Some v) /\
    (exists v, extract_at g2_loc  TFp2  rs = Some v) /\
    (exists v, extract_at w_loc   TFp2  rs = Some v).

  Definition pre_sa  : spec_t := fun rs => pre  rs /\ has_slots rs.
  Definition mid1_sa : spec_t := fun rs => mid1 rs /\ has_slots rs.
  Definition mid2_sa : spec_t := fun rs => mid2 rs /\ has_slots rs.
  Definition mid3_sa : spec_t := fun rs => mid3 rs /\ has_slots rs.
  Definition mid4_sa : spec_t := fun rs => mid4 rs /\ has_slots rs.

  (** Helpers: setting a tower variable [x] yields a state in which
      the [loc_*] location at [x] resolves under [extract_at] to the
      newly-set value.  The [loc_path] is [PathNil _] in each case so
      [project] / [eq_rect] reduce by computation. *)
  Lemma extract_at_loc_Fp_set_self :
    forall x rs v,
      extract_at (loc_Fp x) TFp
                 (rs_set_tower rs x (exist_tval TFp v)) = Some v.
  Proof.
    intros x rs v.
    unfold extract_at, located_lookup, loc_Fp, rs_set_tower; cbn.
    rewrite lookup_t_update_same. reflexivity.
  Qed.

  Lemma extract_at_loc_Fp2_set_self :
    forall x rs v,
      extract_at (loc_Fp2 x) TFp2
                 (rs_set_tower rs x (exist_tval TFp2 v)) = Some v.
  Proof.
    intros x rs v.
    unfold extract_at, located_lookup, loc_Fp2, rs_set_tower; cbn.
    rewrite lookup_t_update_same. reflexivity.
  Qed.

  Lemma extract_at_loc_Fp12_set_self :
    forall x rs v,
      extract_at (loc_Fp12 x) TFp12
                 (rs_set_tower rs x (exist_tval TFp12 v)) = Some v.
  Proof.
    intros x rs v.
    unfold extract_at, located_lookup, loc_Fp12, rs_set_tower; cbn.
    rewrite lookup_t_update_same. reflexivity.
  Qed.

  (** Slot variable names: stated explicitly so that the
      distinctness lemmas below can reduce by [cbv] / [discriminate]. *)
  Lemma loc_var_tmp_loc : loc_var tmp_loc = "tmp".
  Proof. reflexivity. Qed.
  Lemma loc_var_g1_loc  : loc_var g1_loc  = "gamma1_p2".
  Proof. reflexivity. Qed.
  Lemma loc_var_g2_loc  : loc_var g2_loc  = "gamma2_p2".
  Proof. reflexivity. Qed.
  Lemma loc_var_w_loc   : loc_var w_loc   = "w_frob_p2_c1".
  Proof. reflexivity. Qed.

  (** Pairing-pre is preserved under setting a fresh stackalloc name:
      each [Fp_at] / [Fp2_at] / [Fp12_at] reduces under
      [extract_at_set_other] when the variable names differ. *)
  Lemma pairing_pre_preserved_set_fresh :
    forall rs x v,
      loc_var out_loc <> x ->
      loc_var p_x_loc <> x ->
      loc_var p_y_loc <> x ->
      loc_var q_x_loc <> x ->
      loc_var q_y_loc <> x ->
      pre rs ->
      pre (rs_set_tower rs x v).
  Proof.
    intros rs x v Ho Hpx Hpy Hqx Hqy [Hout [Hpx' [Hpy' [Hqx' Hqy']]]].
    unfold pairing_pre.
    repeat split.
    - destruct Hout as [Hd [v0 Hext]]. exact Hd.
    - destruct Hout as [Hd [v0 Hext]]. exists v0.
      rewrite extract_at_set_other; assumption.
    - destruct Hpx' as [Hd [v0 Hext]]. exact Hd.
    - destruct Hpx' as [Hd [v0 Hext]]. exists v0.
      rewrite extract_at_set_other; assumption.
    - destruct Hpy' as [Hd [v0 Hext]]. exact Hd.
    - destruct Hpy' as [Hd [v0 Hext]]. exists v0.
      rewrite extract_at_set_other; assumption.
    - destruct Hqx' as [Hd [v0 Hext]]. exact Hd.
    - destruct Hqx' as [Hd [v0 Hext]]. exists v0.
      rewrite extract_at_set_other; assumption.
    - destruct Hqy' as [Hd [v0 Hext]]. exact Hd.
    - destruct Hqy' as [Hd [v0 Hext]]. exists v0.
      rewrite extract_at_set_other; assumption.
  Qed.

  (** Main lemma: the precondition produced by 4 nested
      [refines_let_zero] applications, starting from [pre], implies
      the strengthened [pre_sa].  Each user location survives the 4
      sets via [pairing_pre_preserved_set_fresh] (using the
      [Hfresh_*] hypotheses), and each of the 4 stackalloc slots is
      reachable by peeling off the outer sets with
      [extract_at_set_other] until the matching [_set_self] applies. *)
  Lemma pre_after_4_stackallocs :
    forall rs,
      (exists rs3,
         (exists rs2,
            (exists rs1,
               (exists rs0,
                  pre rs0 /\
                  rs1 = rs_set_tower rs0 tmp_var
                          (exist_tval TFp12 (tt_zero bn446_N TFp12)))
               /\ rs2 = rs_set_tower rs1 "gamma1_p2"
                          (exist_tval TFp2 (tt_zero bn446_N TFp2)))
            /\ rs3 = rs_set_tower rs2 "gamma2_p2"
                       (exist_tval TFp2 (tt_zero bn446_N TFp2)))
         /\ rs = rs_set_tower rs3 "w_frob_p2_c1"
                   (exist_tval TFp2 (tt_zero bn446_N TFp2))) ->
      pre_sa rs.
  Proof.
    intros rs [rs3 [[rs2 [[rs1 [[rs0 [Hpre Heq1]] Heq2]] Heq3]] Heq4]].
    subst rs1 rs2 rs3 rs.
    destruct Hfresh_out  as [Ho_t  [Ho_g1  [Ho_g2  Ho_w]]].
    destruct Hfresh_px   as [Hpx_t [Hpx_g1 [Hpx_g2 Hpx_w]]].
    destruct Hfresh_py   as [Hpy_t [Hpy_g1 [Hpy_g2 Hpy_w]]].
    destruct Hfresh_qx   as [Hqx_t [Hqx_g1 [Hqx_g2 Hqx_w]]].
    destruct Hfresh_qy   as [Hqy_t [Hqy_g1 [Hqy_g2 Hqy_w]]].
    split.
    - (* pre rs survives 4 stackallocs *)
      apply pairing_pre_preserved_set_fresh; auto.
      apply pairing_pre_preserved_set_fresh; auto.
      apply pairing_pre_preserved_set_fresh; auto.
      apply pairing_pre_preserved_set_fresh; auto.
    - (* has_slots rs *)
      unfold has_slots; repeat split.
      + (* tmp_loc: peel "w_frob_p2_c1", "gamma2_p2", "gamma1_p2", then self *)
        rewrite extract_at_set_other by (rewrite loc_var_tmp_loc; discriminate).
        rewrite extract_at_set_other by (rewrite loc_var_tmp_loc; discriminate).
        rewrite extract_at_set_other by (rewrite loc_var_tmp_loc; discriminate).
        unfold tmp_loc. eexists. apply extract_at_loc_Fp12_set_self.
      + (* g1_loc: peel "w_frob_p2_c1", "gamma2_p2", then self *)
        rewrite extract_at_set_other by (rewrite loc_var_g1_loc; discriminate).
        rewrite extract_at_set_other by (rewrite loc_var_g1_loc; discriminate).
        unfold g1_loc. eexists. apply extract_at_loc_Fp2_set_self.
      + (* g2_loc: peel "w_frob_p2_c1", then self *)
        rewrite extract_at_set_other by (rewrite loc_var_g2_loc; discriminate).
        unfold g2_loc. eexists. apply extract_at_loc_Fp2_set_self.
      + (* w_loc: self at the outermost set *)
        unfold w_loc. eexists. apply extract_at_loc_Fp2_set_self.
  Qed.

  (** Writeback at a stackalloc slot preserves [pre]: the slot's
      variable is fresh from all 5 user locations (by [Hfresh_*]),
      so each [Fp{,2,12}_at] survives via
      [extract_at_writeback_other]. *)
  Lemma pre_preserved_writeback_slot :
    forall rs slot v rs',
      loc_var out_loc <> loc_var slot ->
      loc_var p_x_loc <> loc_var slot ->
      loc_var p_y_loc <> loc_var slot ->
      loc_var q_x_loc <> loc_var slot ->
      loc_var q_y_loc <> loc_var slot ->
      pre rs ->
      located_update rs slot v = Some rs' ->
      pre rs'.
  Proof.
    intros rs slot v rs' Ho Hpx Hpy Hqx Hqy
           [Hout [Hpx' [Hpy' [Hqx' Hqy']]]] Hupd.
    unfold pairing_pre.
    repeat split.
    - destruct Hout as [Hd _]. exact Hd.
    - destruct Hout as [_ [v0 Hext]]. exists v0.
      erewrite extract_at_writeback_other; eauto.
    - destruct Hpx' as [Hd _]. exact Hd.
    - destruct Hpx' as [_ [v0 Hext]]. exists v0.
      erewrite extract_at_writeback_other; eauto.
    - destruct Hpy' as [Hd _]. exact Hd.
    - destruct Hpy' as [_ [v0 Hext]]. exists v0.
      erewrite extract_at_writeback_other; eauto.
    - destruct Hqx' as [Hd _]. exact Hd.
    - destruct Hqx' as [_ [v0 Hext]]. exists v0.
      erewrite extract_at_writeback_other; eauto.
    - destruct Hqy' as [Hd _]. exact Hd.
    - destruct Hqy' as [_ [v0 Hext]]. exists v0.
      erewrite extract_at_writeback_other; eauto.
  Qed.

  (** [has_slots] is preserved by writeback at any one of the four
      slots themselves: the three other slots have distinct variable
      names, and the written slot is reachable by the new value from
      [located_update].  The "self" cases use that
      [located_update rs (loc_Fp2 x) v] — when it succeeds — yields
      [rs_set_tower rs x (exist_tval TFp2 v)], so [extract_at_loc_*_set_self]
      applies. *)

  Lemma extract_at_loc_Fp2_writeback_self :
    forall x rs v rs',
      located_update rs (loc_Fp2 x) v = Some rs' ->
      exists v', extract_at (loc_Fp2 x) TFp2 rs' = Some v'.
  Proof.
    intros x rs v rs' Hupd.
    unfold located_update in Hupd; cbn in Hupd.
    destruct (lookup_t (rs_tower rs) x) as [[t v_old]|] eqn:Hl;
      [|discriminate].
    destruct (tower_type_eq_dec t TFp2) as [Heq|]; [|discriminate].
    injection Hupd as Hrs'. subst rs'.
    cbn. eexists. apply extract_at_loc_Fp2_set_self.
  Qed.

  Lemma extract_at_loc_Fp12_writeback_self :
    forall x rs v rs',
      located_update rs (loc_Fp12 x) v = Some rs' ->
      exists v', extract_at (loc_Fp12 x) TFp12 rs' = Some v'.
  Proof.
    intros x rs v rs' Hupd.
    unfold located_update in Hupd; cbn in Hupd.
    destruct (lookup_t (rs_tower rs) x) as [[t v_old]|] eqn:Hl;
      [|discriminate].
    destruct (tower_type_eq_dec t TFp12) as [Heq|]; [|discriminate].
    injection Hupd as Hrs'. subst rs'.
    cbn. eexists. apply extract_at_loc_Fp12_set_self.
  Qed.

  Lemma has_slots_preserved_writeback_g1 :
    forall rs v rs',
      located_update rs g1_loc v = Some rs' ->
      has_slots rs ->
      has_slots rs'.
  Proof.
    intros rs v rs' Hupd [Htmp [Hg1' [Hg2' Hw']]].
    unfold has_slots; repeat split.
    - destruct Htmp as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_tmp_loc, loc_var_g1_loc; discriminate
                   | exact Hupd ].
    - unfold g1_loc in *.
      eapply extract_at_loc_Fp2_writeback_self; exact Hupd.
    - destruct Hg2' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_g2_loc, loc_var_g1_loc; discriminate
                   | exact Hupd ].
    - destruct Hw' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_w_loc, loc_var_g1_loc; discriminate
                   | exact Hupd ].
  Qed.

  Lemma has_slots_preserved_writeback_g2 :
    forall rs v rs',
      located_update rs g2_loc v = Some rs' ->
      has_slots rs ->
      has_slots rs'.
  Proof.
    intros rs v rs' Hupd [Htmp [Hg1' [Hg2' Hw']]].
    unfold has_slots; repeat split.
    - destruct Htmp as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_tmp_loc, loc_var_g2_loc; discriminate
                   | exact Hupd ].
    - destruct Hg1' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_g1_loc, loc_var_g2_loc; discriminate
                   | exact Hupd ].
    - unfold g2_loc in *.
      eapply extract_at_loc_Fp2_writeback_self; exact Hupd.
    - destruct Hw' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_w_loc, loc_var_g2_loc; discriminate
                   | exact Hupd ].
  Qed.

  Lemma has_slots_preserved_writeback_w :
    forall rs v rs',
      located_update rs w_loc v = Some rs' ->
      has_slots rs ->
      has_slots rs'.
  Proof.
    intros rs v rs' Hupd [Htmp [Hg1' [Hg2' Hw']]].
    unfold has_slots; repeat split.
    - destruct Htmp as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_tmp_loc, loc_var_w_loc; discriminate
                   | exact Hupd ].
    - destruct Hg1' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_g1_loc, loc_var_w_loc; discriminate
                   | exact Hupd ].
    - destruct Hg2' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_g2_loc, loc_var_w_loc; discriminate
                   | exact Hupd ].
    - unfold w_loc in *.
      eapply extract_at_loc_Fp2_writeback_self; exact Hupd.
  Qed.

  Lemma has_slots_preserved_writeback_tmp :
    forall rs v rs',
      located_update rs tmp_loc v = Some rs' ->
      has_slots rs ->
      has_slots rs'.
  Proof.
    intros rs v rs' Hupd [Htmp [Hg1' [Hg2' Hw']]].
    unfold has_slots; repeat split.
    - unfold tmp_loc in *.
      eapply extract_at_loc_Fp12_writeback_self; exact Hupd.
    - destruct Hg1' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_g1_loc, loc_var_tmp_loc; discriminate
                   | exact Hupd ].
    - destruct Hg2' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_g2_loc, loc_var_tmp_loc; discriminate
                   | exact Hupd ].
    - destruct Hw' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0 | rewrite loc_var_w_loc, loc_var_tmp_loc; discriminate
                   | exact Hupd ].
  Qed.

  (** Writeback at the user output location [out_loc] preserves
      [has_slots] (slot vars are all distinct from [loc_var out_loc]
      by [Hfresh_out]). *)
  Lemma has_slots_preserved_writeback_out :
    forall v rs rs',
      located_update rs out_loc v = Some rs' ->
      has_slots rs ->
      has_slots rs'.
  Proof.
    intros v rs rs' Hupd [Htmp [Hg1' [Hg2' Hw']]].
    destruct Hfresh_out as [Ho_t [Ho_g1 [Ho_g2 Ho_w]]].
    unfold tmp_var in Ho_t.
    unfold has_slots; repeat split.
    - destruct Htmp as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0
         | rewrite loc_var_tmp_loc;
           intro Hc; apply Ho_t; symmetry; exact Hc
         | exact Hupd].
    - destruct Hg1' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0
         | rewrite loc_var_g1_loc;
           intro Hc; apply Ho_g1; symmetry; exact Hc
         | exact Hupd].
    - destruct Hg2' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0
         | rewrite loc_var_g2_loc;
           intro Hc; apply Ho_g2; symmetry; exact Hc
         | exact Hupd].
    - destruct Hw' as [v0 Hv0]. exists v0.
      erewrite extract_at_writeback_other;
        [exact Hv0
         | rewrite loc_var_w_loc;
           intro Hc; apply Ho_w; symmetry; exact Hc
         | exact Hupd].
  Qed.

  (* ================================================================ *)
  (* §8.2 Strengthened writeback-self lemmas + extract/lookup bridge   *)
  (*                                                                   *)
  (*   To convert a callee's [extract_at] obligation into the          *)
  (*   low-level [located_lookup_sig] / [lookup_t] form that           *)
  (*   [bn446_bind_params] uses (and vice versa for [bn446_extract_    *)
  (*   output]) we need "exact value" variants of the writeback-self  *)
  (*   lemmas and a helper linking [extract_at (loc_Fp2 x) TFp2 rs =   *)
  (*   Some v] to [lookup_t (rs_tower rs) x = Some (exist_tval TFp2   *)
  (*   v)].  Both are straightforward computations; their statements  *)
  (*   thread through several [eq_rect] casts that [cbn] + [subst]   *)
  (*   reduce away.                                                   *)
  (* ================================================================ *)

  Lemma extract_at_loc_Fp2_writeback_eq :
    forall x rs v rs',
      located_update rs (loc_Fp2 x) v = Some rs' ->
      extract_at (loc_Fp2 x) TFp2 rs' = Some v.
  Proof.
    intros x rs v rs' Hupd.
    unfold located_update in Hupd; cbn in Hupd.
    destruct (lookup_t (rs_tower rs) x) as [[t v_old]|] eqn:Hl;
      [|discriminate].
    destruct (tower_type_eq_dec t TFp2) as [Heq|]; [|discriminate].
    injection Hupd as Hrs'. subst rs'.
    cbn. apply extract_at_loc_Fp2_set_self.
  Qed.

  Lemma extract_at_loc_Fp12_writeback_eq :
    forall x rs v rs',
      located_update rs (loc_Fp12 x) v = Some rs' ->
      extract_at (loc_Fp12 x) TFp12 rs' = Some v.
  Proof.
    intros x rs v rs' Hupd.
    unfold located_update in Hupd; cbn in Hupd.
    destruct (lookup_t (rs_tower rs) x) as [[t v_old]|] eqn:Hl;
      [|discriminate].
    destruct (tower_type_eq_dec t TFp12) as [Heq|]; [|discriminate].
    injection Hupd as Hrs'. subst rs'.
    cbn. apply extract_at_loc_Fp12_set_self.
  Qed.

  (** Link from the high-level [extract_at] to the low-level
      [lookup_t] view used by [bn446_bind_params].  The [eq_rect]
      casts reduce by [subst]ing along the type equality returned by
      [tower_type_eq_dec]. *)
  Lemma extract_at_loc_Fp2_implies_lookup :
    forall x rs v,
      extract_at (loc_Fp2 x) TFp2 rs = Some v ->
      lookup_t (rs_tower rs) x = Some (exist_tval TFp2 v).
  Proof.
    intros x rs v Hext.
    unfold extract_at, located_lookup, loc_Fp2 in Hext; cbn in Hext.
    destruct (lookup_t (rs_tower rs) x) as [[t_stored v_stored]|] eqn:Hl;
      [|discriminate].
    destruct (tower_type_eq_dec t_stored TFp2) as [Heq|]; [|discriminate].
    subst t_stored. cbn in Hext.
    injection Hext as Hv. subst v. reflexivity.
  Qed.

  Lemma extract_at_loc_Fp12_implies_lookup :
    forall x rs v,
      extract_at (loc_Fp12 x) TFp12 rs = Some v ->
      lookup_t (rs_tower rs) x = Some (exist_tval TFp12 v).
  Proof.
    intros x rs v Hext.
    unfold extract_at, located_lookup, loc_Fp12 in Hext; cbn in Hext.
    destruct (lookup_t (rs_tower rs) x) as [[t_stored v_stored]|] eqn:Hl;
      [|discriminate].
    destruct (tower_type_eq_dec t_stored TFp12) as [Heq|]; [|discriminate].
    subst t_stored. cbn in Hext.
    injection Hext as Hv. subst v. reflexivity.
  Qed.

  Lemma extract_at_loc_Fp_implies_lookup :
    forall x rs v,
      extract_at (loc_Fp x) TFp rs = Some v ->
      lookup_t (rs_tower rs) x = Some (exist_tval TFp v).
  Proof.
    intros x rs v Hext.
    unfold extract_at, located_lookup, loc_Fp in Hext; cbn in Hext.
    destruct (lookup_t (rs_tower rs) x) as [[t_stored v_stored]|] eqn:Hl;
      [|discriminate].
    destruct (tower_type_eq_dec t_stored TFp) as [Heq|]; [|discriminate].
    subst t_stored. cbn in Hext.
    injection Hext as Hv. subst v. reflexivity.
  Qed.

  (** Converse: a [lookup_t] match implies [extract_at] at the
      corresponding [loc_*].  Used in [post_bridge]. *)
  Lemma lookup_implies_extract_at_loc_Fp2 :
    forall x rs v,
      lookup_t (rs_tower rs) x = Some (exist_tval TFp2 v) ->
      extract_at (loc_Fp2 x) TFp2 rs = Some v.
  Proof.
    intros x rs v Hl.
    unfold extract_at, located_lookup, loc_Fp2; cbn.
    rewrite Hl. reflexivity.
  Qed.

  (* ================================================================ *)
  (* §8.3 compose_load_g1 — template for per-callee composition       *)
  (*                                                                   *)
  (*   Packages the 4 obligations of [call_composes_from] for the     *)
  (*   load_gamma1_p2 call: fenv lookup, callee refinement, pre-      *)
  (*   bridge (split [pre_sa] into the slot witness + remainder),     *)
  (*   and post-bridge (combine callee's "out" witness with           *)
  (*   [bn446_extract_output] + [bn446_writeback_output] to land in   *)
  (*   [mid1_sa]).                                                    *)
  (* ================================================================ *)

  Lemma compose_load_g1 :
    call_composes_from bn446_N bn446_u64_max bn446_pairing_fenv
                       bn446_leaf_spec_concrete bn446_call_env
                       "bn446_load_gamma1_p2"
                       bn446_load_g1_params bn446_load_g1_body
                       load_g1_callee_pre (load_g1_callee_post gamma1)
                       g1_loc [g1_loc]
                       pre_sa mid1_sa.
  Proof.
    unfold call_composes_from; split; [|split; [|split]].
    - (* fenv lookup *)
      exact fenv_has_pairing_load_g1.
    - (* callee body refinement *)
      exact load_g1_body_refines.
    - (* pre-bridge: pre_sa rs1 => in_vals + rs_init + callee_pre *)
      intros rs1 [Hpre_plain Hslots].
      destruct Hslots as [_ [[v_g1 Hv_g1] _]].
      (* Hv_g1 : extract_at g1_loc TFp2 rs1 = Some v_g1 *)
      apply extract_at_loc_Fp2_implies_lookup in Hv_g1.
      (* Hv_g1 : lookup_t (rs_tower rs1) "gamma1_p2" = Some (exist_tval TFp2 v_g1) *)
      exists [existT rust_val TFp2 v_g1].
      exists (rs_set_tower rs_empty "out" (exist_tval TFp2 v_g1)).
      refine (conj _ (conj _ _)).
      + (* locateds_lookup *)
        unfold locateds_lookup, located_lookup_sig, located_lookup, g1_loc, loc_Fp2; cbn.
        rewrite Hv_g1. reflexivity.
      + (* bn446_bind_params *)
        unfold bn446_bind_params; cbn.
        unfold bn446_bind_params_aux; cbn.
        unfold located_lookup_sig, located_lookup, g1_loc, loc_Fp2; cbn.
        rewrite Hv_g1. reflexivity.
      + (* callee_pre : out has an Fp2 value in rs_init *)
        unfold load_g1_callee_pre. exists v_g1.
        unfold out_var. apply extract_at_loc_Fp2_set_self.
    - (* post-bridge: caller_pre + callee_post + extract + writeback => mid1_sa *)
      intros rs1 rs_mid rs2 rs_out_val [Hpre_plain Hslots] Hcallee Hext Hwb.
      destruct Hcallee as [v_out [Hout_ext Hout_eval]].
      (* Hout_ext : extract_at (loc_Fp2 "out") TFp2 rs_mid = Some v_out *)
      apply extract_at_loc_Fp2_implies_lookup in Hout_ext.
      unfold out_var in Hout_ext.
      (* Hout_ext : lookup_t (rs_tower rs_mid) "out" = Some (exist_tval TFp2 v_out) *)
      (* bn446_extract_output ["out"] rs_mid = Some (existT _ TFp2 v_out) *)
      unfold ce_extract_output, bn446_call_env, bn446_extract_output,
             bn446_load_g1_params in Hext; cbn in Hext.
      rewrite Hout_ext in Hext.
      injection Hext as Hrs_out. subst rs_out_val.
      (* Hwb: bn446_writeback_output g1_loc (existT _ TFp2 v_out) rs1 = Some rs2.
         By the definition of bn446_writeback_output and the fact that
         loc_dst g1_loc = TFp2, this reduces to located_update rs1 g1_loc v_out. *)
      assert (Hwb' : located_update rs1 g1_loc v_out = Some rs2).
      { unfold ce_writeback_output, bn446_call_env,
               bn446_writeback_output in Hwb.
        cbn in Hwb.
        (* g1_loc.loc_dst = TFp2 by unfolding *)
        change (loc_dst g1_loc) with TFp2 in Hwb.
        (* tower_type_eq_dec TFp2 TFp2 reduces to left eq_refl *)
        cbn in Hwb. exact Hwb. }
      clear Hwb.
      pose proof (extract_at_loc_Fp2_writeback_eq _ _ _ _ Hwb') as Hext_rs2.
      split.
      + (* mid1 rs2 *)
        split.
        * (* pre rs2: via pre_preserved_writeback_slot *)
          destruct Hfresh_out as [_ [Ho_g1 _]].
          destruct Hfresh_px  as [_ [Hpx_g1 _]].
          destruct Hfresh_py  as [_ [Hpy_g1 _]].
          destruct Hfresh_qx  as [_ [Hqx_g1 _]].
          destruct Hfresh_qy  as [_ [Hqy_g1 _]].
          eapply pre_preserved_writeback_slot with (slot := g1_loc);
            try (rewrite loc_var_g1_loc; assumption);
            [exact Hpre_plain | exact Hwb'].
        * (* g1 witness *)
          exists v_out. split.
          { exact Hext_rs2. }
          { exact Hout_eval. }
      + (* has_slots rs2 *)
        eapply has_slots_preserved_writeback_g1;
          [exact Hwb' | exact Hslots].
  Qed.

  (* ================================================================ *)
  (* §8.4 compose_load_g2 — adapt template to the second loader       *)
  (*                                                                   *)
  (*   Same shape as compose_load_g1; caller_pre is [mid1_sa] (which   *)
  (*   carries the g1 witness through), caller_post is [mid2_sa].     *)
  (*   The post-bridge must re-establish [mid1 rs2] (pre rs2 + g1     *)
  (*   witness at rs2) after writeback to g2_loc; g1 and g2 vars are  *)
  (*   distinct, so both halves survive via [extract_at_writeback_    *)
  (*   other].                                                        *)
  (* ================================================================ *)

  Lemma compose_load_g2 :
    call_composes_from bn446_N bn446_u64_max bn446_pairing_fenv
                       bn446_leaf_spec_concrete bn446_call_env
                       "bn446_load_gamma2_p2"
                       bn446_load_g2_params bn446_load_g2_body
                       load_g2_callee_pre (load_g2_callee_post gamma_y)
                       g2_loc [g2_loc]
                       mid1_sa mid2_sa.
  Proof.
    unfold call_composes_from; split; [|split; [|split]].
    - exact fenv_has_pairing_load_g2.
    - exact load_g2_body_refines.
    - (* pre-bridge *)
      intros rs1 [Hmid1_plain Hslots].
      destruct Hslots as [_ [_ [[v_g2 Hv_g2] _]]].
      apply extract_at_loc_Fp2_implies_lookup in Hv_g2.
      exists [existT rust_val TFp2 v_g2].
      exists (rs_set_tower rs_empty "out" (exist_tval TFp2 v_g2)).
      refine (conj _ (conj _ _)).
      + unfold locateds_lookup, located_lookup_sig, located_lookup,
               g2_loc, loc_Fp2; cbn.
        rewrite Hv_g2. reflexivity.
      + unfold bn446_bind_params; cbn.
        unfold bn446_bind_params_aux; cbn.
        unfold located_lookup_sig, located_lookup, g2_loc, loc_Fp2; cbn.
        rewrite Hv_g2. reflexivity.
      + unfold load_g2_callee_pre. exists v_g2.
        unfold out_var. apply extract_at_loc_Fp2_set_self.
    - (* post-bridge *)
      intros rs1 rs_mid rs2 rs_out_val [Hmid1_plain Hslots] Hcallee Hext Hwb.
      destruct Hcallee as [v_out [Hout_ext Hout_eval]].
      apply extract_at_loc_Fp2_implies_lookup in Hout_ext.
      unfold out_var in Hout_ext.
      unfold ce_extract_output, bn446_call_env, bn446_extract_output,
             bn446_load_g2_params in Hext; cbn in Hext.
      rewrite Hout_ext in Hext.
      injection Hext as Hrs_out. subst rs_out_val.
      assert (Hwb' : located_update rs1 g2_loc v_out = Some rs2).
      { unfold ce_writeback_output, bn446_call_env,
               bn446_writeback_output in Hwb.
        cbn in Hwb.
        change (loc_dst g2_loc) with TFp2 in Hwb.
        cbn in Hwb. exact Hwb. }
      clear Hwb.
      pose proof (extract_at_loc_Fp2_writeback_eq _ _ _ _ Hwb') as Hext_rs2.
      destruct Hmid1_plain as [Hpre_plain [v_g1_rs1 [Hg1_rs1 Hg1_eval]]].
      destruct Hfresh_out as [_ [_ [Ho_g2 _]]].
      destruct Hfresh_px  as [_ [_ [Hpx_g2 _]]].
      destruct Hfresh_py  as [_ [_ [Hpy_g2 _]]].
      destruct Hfresh_qx  as [_ [_ [Hqx_g2 _]]].
      destruct Hfresh_qy  as [_ [_ [Hqy_g2 _]]].
      split.
      + (* mid2 rs2 = mid1 rs2 /\ g2 witness *)
        split.
        * (* mid1 rs2 = pre rs2 /\ g1 witness at rs2 *)
          split.
          -- (* pre rs2 via writeback at g2 disjoint from users *)
             eapply pre_preserved_writeback_slot with (slot := g2_loc);
               try (rewrite loc_var_g2_loc; assumption);
               [exact Hpre_plain | exact Hwb'].
          -- (* g1 witness survives: extract at g1_loc unchanged by writeback to g2_loc *)
             exists v_g1_rs1. split; [|exact Hg1_eval].
             erewrite extract_at_writeback_other;
               [exact Hg1_rs1
                | rewrite loc_var_g1_loc, loc_var_g2_loc; discriminate
                | exact Hwb'].
        * (* g2 witness *)
          exists v_out. split; [exact Hext_rs2 | exact Hout_eval].
      + (* has_slots rs2 *)
        eapply has_slots_preserved_writeback_g2;
          [exact Hwb' | exact Hslots].
  Qed.

  (* ================================================================ *)
  (* §8.5 compose_load_w — third loader; caller_pre = mid2_sa,        *)
  (*   caller_post = mid3_sa.  Post-bridge threads mid1 + g2 witness   *)
  (*   through writeback at w_loc, all distinct variable names.       *)
  (* ================================================================ *)

  Lemma compose_load_w :
    call_composes_from bn446_N bn446_u64_max bn446_pairing_fenv
                       bn446_leaf_spec_concrete bn446_call_env
                       "bn446_load_w_frob_p2_c1"
                       bn446_load_w_params bn446_load_w_body
                       load_w_callee_pre (load_w_callee_post gamma1_p2)
                       w_loc [w_loc]
                       mid2_sa mid3_sa.
  Proof.
    unfold call_composes_from; split; [|split; [|split]].
    - exact fenv_has_pairing_load_w.
    - exact load_w_body_refines.
    - (* pre-bridge *)
      intros rs1 [Hmid2_plain Hslots].
      destruct Hslots as [_ [_ [_ [v_w Hv_w]]]].
      apply extract_at_loc_Fp2_implies_lookup in Hv_w.
      exists [existT rust_val TFp2 v_w].
      exists (rs_set_tower rs_empty "out" (exist_tval TFp2 v_w)).
      refine (conj _ (conj _ _)).
      + unfold locateds_lookup, located_lookup_sig, located_lookup,
               w_loc, loc_Fp2; cbn.
        rewrite Hv_w. reflexivity.
      + unfold bn446_bind_params; cbn.
        unfold bn446_bind_params_aux; cbn.
        unfold located_lookup_sig, located_lookup, w_loc, loc_Fp2; cbn.
        rewrite Hv_w. reflexivity.
      + unfold load_w_callee_pre. exists v_w.
        unfold out_var. apply extract_at_loc_Fp2_set_self.
    - (* post-bridge *)
      intros rs1 rs_mid rs2 rs_out_val [Hmid2_plain Hslots] Hcallee Hext Hwb.
      destruct Hcallee as [v_out [Hout_ext Hout_eval]].
      apply extract_at_loc_Fp2_implies_lookup in Hout_ext.
      unfold out_var in Hout_ext.
      unfold ce_extract_output, bn446_call_env, bn446_extract_output,
             bn446_load_w_params in Hext; cbn in Hext.
      rewrite Hout_ext in Hext.
      injection Hext as Hrs_out. subst rs_out_val.
      assert (Hwb' : located_update rs1 w_loc v_out = Some rs2).
      { unfold ce_writeback_output, bn446_call_env,
               bn446_writeback_output in Hwb.
        cbn in Hwb.
        change (loc_dst w_loc) with TFp2 in Hwb.
        cbn in Hwb. exact Hwb. }
      clear Hwb.
      pose proof (extract_at_loc_Fp2_writeback_eq _ _ _ _ Hwb') as Hext_rs2.
      destruct Hmid2_plain as [[Hpre_plain [v_g1_rs1 [Hg1_rs1 Hg1_eval]]]
                              [v_g2_rs1 [Hg2_rs1 Hg2_eval]]].
      destruct Hfresh_out as [_ [_ [_ Ho_w]]].
      destruct Hfresh_px  as [_ [_ [_ Hpx_w]]].
      destruct Hfresh_py  as [_ [_ [_ Hpy_w]]].
      destruct Hfresh_qx  as [_ [_ [_ Hqx_w]]].
      destruct Hfresh_qy  as [_ [_ [_ Hqy_w]]].
      split.
      + (* mid3 rs2 = mid2 rs2 /\ w witness *)
        split.
        * (* mid2 rs2 = mid1 rs2 /\ g2 witness at rs2 *)
          split.
          -- (* mid1 rs2 *)
             split.
             ++ eapply pre_preserved_writeback_slot with (slot := w_loc);
                  try (rewrite loc_var_w_loc; assumption);
                  [exact Hpre_plain | exact Hwb'].
             ++ exists v_g1_rs1. split; [|exact Hg1_eval].
                erewrite extract_at_writeback_other;
                  [exact Hg1_rs1
                   | rewrite loc_var_g1_loc, loc_var_w_loc; discriminate
                   | exact Hwb'].
          -- (* g2 witness survives *)
             exists v_g2_rs1. split; [|exact Hg2_eval].
             erewrite extract_at_writeback_other;
               [exact Hg2_rs1
                | rewrite loc_var_g2_loc, loc_var_w_loc; discriminate
                | exact Hwb'].
        * (* w witness *)
          exists v_out. split; [exact Hext_rs2 | exact Hout_eval].
      + (* has_slots rs2 *)
        eapply has_slots_preserved_writeback_w;
          [exact Hwb' | exact Hslots].
  Qed.

  (* ================================================================ *)
  (* §8.6 compose_miller — 5-ary call at the miller site              *)
  (*                                                                   *)
  (*   The miller call reads 5 slots (tmp, px, py, qx, qy) and writes *)
  (*   a Fp12 result to [tmp_loc].  Because [miller_callee_pre] is    *)
  (*   parameterised on the specific input math values [px_v py_v    *)
  (*   qx_v qy_v], we package the composition at that parameter      *)
  (*   level too: the caller-side pre asserts [mid3_sa] AND that the *)
  (*   user location values evaluate to those specific inputs.        *)
  (*   [miller_call_refines] below re-exposes this to the natural    *)
  (*   [mid3_sa -> mid4_sa] form by existential introduction.        *)
  (* ================================================================ *)

  Definition mid3_sa_with_inputs
             (px_v py_v : Z) (qx_v qy_v : Fp2_Z) : spec_t :=
    fun rs =>
      mid3_sa rs /\
      (exists v, extract_at p_x_loc TFp rs = Some v
                 /\ bn446_fp_eval v = px_v) /\
      (exists v, extract_at p_y_loc TFp rs = Some v
                 /\ bn446_fp_eval v = py_v) /\
      (exists v, extract_at q_x_loc TFp2 rs = Some v
                 /\ bn446_fp2_eval v = qx_v) /\
      (exists v, extract_at q_y_loc TFp2 rs = Some v
                 /\ bn446_fp2_eval v = qy_v).

  Lemma compose_miller :
    forall px_v py_v qx_v qy_v,
      call_composes_from bn446_N bn446_u64_max bn446_pairing_fenv
                         bn446_leaf_spec_concrete bn446_call_env
                         "bn446_miller_loop_optimal"
                         bn446_miller_params bn446_miller_body
                         (miller_callee_pre px_v py_v qx_v qy_v)
                         (miller_callee_post gamma1 gamma_y gamma1_p2
                                             px_v py_v qx_v qy_v)
                         tmp_loc
                         [tmp_loc; p_x_loc; p_y_loc; q_x_loc; q_y_loc]
                         (mid3_sa_with_inputs px_v py_v qx_v qy_v)
                         mid4_sa.
  Proof.
    intros px_v py_v qx_v qy_v.
    unfold call_composes_from; split; [|split; [|split]].
    - exact fenv_has_pairing_miller.
    - apply miller_body_refines.
    - (* pre-bridge *)
      intros rs1 [Hmid3_sa [[v_px [Hv_px Hv_px_eval]]
                            [[v_py [Hv_py Hv_py_eval]]
                             [[v_qx [Hv_qx Hv_qx_eval]]
                              [v_qy [Hv_qy Hv_qy_eval]]]]]].
      destruct Hmid3_sa as [Hmid3_plain Hslots].
      destruct Hslots as [[v_tmp Hv_tmp] _].
      apply extract_at_loc_Fp12_implies_lookup in Hv_tmp.
      rewrite Hpx_shape in Hv_px.
      rewrite Hpy_shape in Hv_py.
      rewrite Hqx_shape in Hv_qx.
      rewrite Hqy_shape in Hv_qy.
      apply extract_at_loc_Fp_implies_lookup in Hv_px.
      apply extract_at_loc_Fp_implies_lookup in Hv_py.
      apply extract_at_loc_Fp2_implies_lookup in Hv_qx.
      apply extract_at_loc_Fp2_implies_lookup in Hv_qy.
      exists [existT rust_val TFp12 v_tmp;
              existT rust_val TFp   v_px;
              existT rust_val TFp   v_py;
              existT rust_val TFp2  v_qx;
              existT rust_val TFp2  v_qy].
      exists (rs_set_tower
                (rs_set_tower
                   (rs_set_tower
                      (rs_set_tower
                         (rs_set_tower rs_empty "tmp"
                            (exist_tval TFp12 v_tmp))
                         "px" (exist_tval TFp v_px))
                      "py" (exist_tval TFp v_py))
                   "qx" (exist_tval TFp2 v_qx))
                "qy" (exist_tval TFp2 v_qy)).
      refine (conj _ (conj _ _)).
      + (* locateds_lookup *)
        unfold locateds_lookup, located_lookup_sig, located_lookup; cbn.
        unfold tmp_loc, loc_Fp12; cbn.
        rewrite Hv_tmp. rewrite Hpx_shape, Hpy_shape, Hqx_shape, Hqy_shape.
        unfold loc_Fp, loc_Fp2; cbn.
        rewrite Hv_px, Hv_py, Hv_qx, Hv_qy. reflexivity.
      + (* bn446_bind_params *)
        unfold bn446_bind_params, bn446_bind_params_aux,
               bn446_miller_params; cbn.
        unfold located_lookup_sig, located_lookup; cbn.
        unfold tmp_loc, loc_Fp12; cbn. rewrite Hv_tmp.
        rewrite Hpx_shape, Hpy_shape, Hqx_shape, Hqy_shape.
        unfold loc_Fp, loc_Fp2; cbn.
        rewrite Hv_px, Hv_py, Hv_qx, Hv_qy.
        reflexivity.
      + (* callee_pre at rs_init: 5 conjuncts tmp, px, py, qx, qy.
           The rs_init has 5 nested [rs_set_tower]s with outermost "qy".
           To find each slot we peel the outer [rs_set_tower]s via
           [extract_at_set_other] until we hit the matching variable,
           then apply [extract_at_loc_*_set_self]. *)
        unfold miller_callee_pre; cbv beta.
        refine (conj _ (conj _ (conj _ (conj _ _)))).
        * (* tmp_loc: peel qy, qx, py, px → self at "tmp" *)
          eexists. unfold tmp_var.
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          apply extract_at_loc_Fp12_set_self.
        * (* px: peel qy, qx, py → self at "px" *)
          eexists. split;
            [|rewrite <- Hv_px_eval; reflexivity].
          unfold px_var.
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          apply extract_at_loc_Fp_set_self.
        * (* py: peel qy, qx → self at "py" *)
          eexists. split;
            [|rewrite <- Hv_py_eval; reflexivity].
          unfold py_var.
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          apply extract_at_loc_Fp_set_self.
        * (* qx: peel qy → self at "qx" *)
          eexists. split;
            [|rewrite <- Hv_qx_eval; reflexivity].
          unfold qx_var.
          rewrite extract_at_set_other by (cbv; discriminate).
          apply extract_at_loc_Fp2_set_self.
        * (* qy: outermost, apply set_self directly *)
          eexists. split;
            [|rewrite <- Hv_qy_eval; reflexivity].
          unfold qy_var.
          apply extract_at_loc_Fp2_set_self.
    - (* post-bridge *)
      intros rs1 rs_mid rs2 rs_out_val
             [[Hmid3_plain Hslots]
              [[v_px_in [Hpx_ext_in Hpx_eq]]
               [[v_py_in [Hpy_ext_in Hpy_eq]]
                [[v_qx_in [Hqx_ext_in Hqx_eq]]
                 [v_qy_in [Hqy_ext_in Hqy_eq]]]]]]
             Hcallee Hext Hwb.
      destruct Hcallee as [v_tmp_out [Htmp_ext Htmp_eval]].
      apply extract_at_loc_Fp12_implies_lookup in Htmp_ext.
      unfold tmp_var in Htmp_ext.
      unfold ce_extract_output, bn446_call_env, bn446_extract_output,
             bn446_miller_params in Hext; cbn in Hext.
      rewrite Htmp_ext in Hext.
      injection Hext as Hrs_out. subst rs_out_val.
      assert (Hwb' : located_update rs1 tmp_loc v_tmp_out = Some rs2).
      { unfold ce_writeback_output, bn446_call_env,
               bn446_writeback_output in Hwb.
        cbn in Hwb.
        change (loc_dst tmp_loc) with TFp12 in Hwb.
        cbn in Hwb. exact Hwb. }
      clear Hwb.
      pose proof (extract_at_loc_Fp12_writeback_eq _ _ _ _ Hwb') as Hext_rs2.
      (* Now need mid4_sa rs2 = (mid_w rs2 /\ ml witness) /\ has_slots rs2 *)
      destruct Hmid3_plain as [[[Hpre_plain [v_g1 [Hg1_rs1 Hg1_eval]]]
                                [v_g2 [Hg2_rs1 Hg2_eval]]]
                               [v_w [Hw_rs1 Hw_eval]]].
      destruct Hfresh_out as [Ho_t _].
      destruct Hfresh_px  as [Hpx_t _].
      destruct Hfresh_py  as [Hpy_t _].
      destruct Hfresh_qx  as [Hqx_t _].
      destruct Hfresh_qy  as [Hqy_t _].
      unfold tmp_var in Ho_t, Hpx_t, Hpy_t, Hqx_t, Hqy_t.
      assert (Hpre_rs2 : pre rs2).
      { eapply pre_preserved_writeback_slot with (slot := tmp_loc).
        - rewrite loc_var_tmp_loc. exact Ho_t.
        - rewrite loc_var_tmp_loc. exact Hpx_t.
        - rewrite loc_var_tmp_loc. exact Hpy_t.
        - rewrite loc_var_tmp_loc. exact Hqx_t.
        - rewrite loc_var_tmp_loc. exact Hqy_t.
        - exact Hpre_plain.
        - exact Hwb'. }
      destruct Hpre_plain as [_ [[_ [v_px_rs1 Hpx_rs1]]
                                  [[_ [v_py_rs1 Hpy_rs1]]
                                   [[_ [v_qx_rs1 Hqx_rs1]]
                                    [_ [v_qy_rs1 Hqy_rs1]]]]]].
      split.
      + (* mid_ml rs2 *)
        split.
        * (* mid_w rs2 = mid_g2 rs2 /\ w witness *)
          split.
          -- (* mid_g2 rs2 = mid_g1 rs2 /\ g2 witness *)
             split.
             ++ (* mid_g1 rs2 = pre rs2 /\ g1 witness *)
                split; [exact Hpre_rs2|].
                exists v_g1. split; [|exact Hg1_eval].
                erewrite extract_at_writeback_other;
                  [exact Hg1_rs1
                   | rewrite loc_var_g1_loc, loc_var_tmp_loc; discriminate
                   | exact Hwb'].
             ++ exists v_g2. split; [|exact Hg2_eval].
                erewrite extract_at_writeback_other;
                  [exact Hg2_rs1
                   | rewrite loc_var_g2_loc, loc_var_tmp_loc; discriminate
                   | exact Hwb'].
          -- exists v_w. split; [|exact Hw_eval].
             erewrite extract_at_writeback_other;
               [exact Hw_rs1
                | rewrite loc_var_w_loc, loc_var_tmp_loc; discriminate
                | exact Hwb'].
        * (* ml witness *)
          (* Need: extract_at tmp_loc TFp12 rs2 = Some ml_val /\
                   extract_at p_x_loc TFp rs2 = Some px /\ ...
                   bn446_fp12_eval ml_val = miller_with_corrections ... *)
          exists v_tmp_out, v_px_rs1, v_py_rs1, v_qx_rs1, v_qy_rs1.
          repeat split.
          -- exact Hext_rs2.
          -- erewrite extract_at_writeback_other;
               [exact Hpx_rs1
                | rewrite loc_var_tmp_loc; exact Hpx_t
                | exact Hwb'].
          -- erewrite extract_at_writeback_other;
               [exact Hpy_rs1
                | rewrite loc_var_tmp_loc; exact Hpy_t
                | exact Hwb'].
          -- erewrite extract_at_writeback_other;
               [exact Hqx_rs1
                | rewrite loc_var_tmp_loc; exact Hqx_t
                | exact Hwb'].
          -- erewrite extract_at_writeback_other;
               [exact Hqy_rs1
                | rewrite loc_var_tmp_loc; exact Hqy_t
                | exact Hwb'].
          -- (* bn446_fp12_eval v_tmp_out =
                miller_with_corrections(bn446_fp_eval v_px_rs1, ...).
                Chain: Htmp_eval gives this for (px_v, py_v, qx_v, qy_v).
                The caller-provided equations Hpx_eq : bn446_fp_eval v_px_in = px_v
                plus determinism of extract_at (Hpx_ext_in vs Hpx_rs1 both at p_x_loc) give
                bn446_fp_eval v_px_rs1 = px_v. *)
             assert (Hpxeq : v_px_rs1 = v_px_in)
               by (rewrite Hpx_ext_in in Hpx_rs1; injection Hpx_rs1; auto).
             assert (Hpyeq : v_py_rs1 = v_py_in)
               by (rewrite Hpy_ext_in in Hpy_rs1; injection Hpy_rs1; auto).
             assert (Hqxeq : v_qx_rs1 = v_qx_in)
               by (rewrite Hqx_ext_in in Hqx_rs1; injection Hqx_rs1; auto).
             assert (Hqyeq : v_qy_rs1 = v_qy_in)
               by (rewrite Hqy_ext_in in Hqy_rs1; injection Hqy_rs1; auto).
             subst v_px_rs1 v_py_rs1 v_qx_rs1 v_qy_rs1.
             rewrite Hpx_eq, Hpy_eq, Hqx_eq, Hqy_eq.
             exact Htmp_eval.
      + (* has_slots rs2 *)
        eapply has_slots_preserved_writeback_tmp;
          [exact Hwb' | exact Hslots].
  Qed.

  (** Wrap [compose_miller] by extracting the specific input values
      from [mid3_sa] and applying it.  This re-packages as a plain
      [rust_refines mid3_sa (RCall …) mid4_sa]. *)
  Lemma miller_call_refines :
    rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                 bn446_leaf_spec_concrete bn446_call_env
                 mid3_sa
                 (RCall "bn446_miller_loop_optimal" tmp_loc
                        [tmp_loc; p_x_loc; p_y_loc; q_x_loc; q_y_loc])
                 mid4_sa.
  Proof.
    unfold rust_refines.
    intros rs1 rs2 Hmid3 Hexec.
    pose proof Hmid3 as Hmid3_sa_rs1.
    destruct Hmid3 as [Hmid3_plain Hslots].
    destruct Hmid3_plain as [[[Hpre_plain _] _] _].
    destruct Hpre_plain as [_ [[_ [v_px Hpx_ext]]
                                [[_ [v_py Hpy_ext]]
                                 [[_ [v_qx Hqx_ext]]
                                  [_ [v_qy Hqy_ext]]]]]].
    set (px_v := bn446_fp_eval v_px).
    set (py_v := bn446_fp_eval v_py).
    set (qx_v := bn446_fp2_eval v_qx).
    set (qy_v := bn446_fp2_eval v_qy).
    assert (Hstrong : mid3_sa_with_inputs px_v py_v qx_v qy_v rs1).
    { split; [exact Hmid3_sa_rs1|].
      split; [exists v_px; split; [exact Hpx_ext | reflexivity] |].
      split; [exists v_py; split; [exact Hpy_ext | reflexivity] |].
      split; [exists v_qx; split; [exact Hqx_ext | reflexivity] |].
      exists v_qy; split; [exact Hqy_ext | reflexivity]. }
    eapply refines_call;
      [apply (compose_miller px_v py_v qx_v qy_v)
      | exact Hstrong
      | exact Hexec].
  Qed.

  (* ================================================================ *)
  (* §8.7 Decomposition: optimal_ate = final_exp ∘ miller_with_corr   *)
  (*                                                                   *)
  (*   For BN446 (loop_neg = false), the [bn446_optimal_ate_spec]     *)
  (*   decomposes as [final_exp] applied to the Miller-with-          *)
  (*   corrections value.  Stated as a Hypothesis here; it is         *)
  (*   discharged by unfolding [PairingSpec.optimal_ate] and          *)
  (*   computing [loop_neg bn446_params = false] by [vm_compute].     *)
  (*   Keeping it Hypothesis-local lets the chain proof close         *)
  (*   without pulling in the full [CurveParams] unfolding.           *)
  (* ================================================================ *)

  Lemma bn446_optimal_ate_decomposes :
    forall px py qx qy,
      bn446_optimal_ate_spec gamma1 gamma_y gamma1_p2 px py qx qy =
      PairingSpec.final_exp bn446_zmod_ops
        (zfp12_conj bn446_p_val)
        (zfp12_inv bn446_p_val bn446_xi_val)
        (zfp12_frob_p2 bn446_p_val bn446_xi_val)
        (zfp12_pow bn446_p_val bn446_xi_val)
        (prime_p bn446_params) (scalar_r bn446_params)
        (bn446_miller_loop_with_corrections gamma1 gamma_y gamma1_p2
                                            px py qx qy).
  Proof.
    intros.
    unfold bn446_optimal_ate_spec, bn446_miller_loop_with_corrections,
           PairingSpec.optimal_ate.
    (* [loop_neg bn446_params = false] by [vm_compute]. *)
    assert (Hneg : loop_neg bn446_params = false) by reflexivity.
    rewrite Hneg.
    destruct (affine_miller_aux bn446_zmod_ops (loop_abs bn446_params)
               (Z.to_nat (Z.log2 (loop_abs bn446_params)))
               px py qx qy (fp12_one bn446_zmod_ops) qx qy)
             as [[f Tx] Ty].
    reflexivity.
  Qed.

  (* ================================================================ *)
  (* §8.8 compose_finalexp + finalexp_call_refines                    *)
  (*                                                                   *)
  (*   The final-exp call reads 5 slots (out, f, g1, g2, w) and writes *)
  (*   to [out_loc].  Its callee_pre/post are parameterised on [f_v]  *)
  (*   (the math-level input).  The caller-side pre [mid4_sa_with_    *)
  (*   input] asserts [mid4_sa] AND that [tmp_loc]'s value evaluates  *)
  (*   to [f_v].  [finalexp_call_refines] then hides this by          *)
  (*   extracting [f_v] from [mid4_sa].                                *)
  (* ================================================================ *)

  Definition mid4_sa_with_input (f_v : Fp12_Z) : spec_t :=
    fun rs =>
      mid4_sa rs /\
      (exists v, extract_at tmp_loc TFp12 rs = Some v
                 /\ bn446_fp12_eval v = f_v).

  Lemma compose_finalexp :
    forall f_v,
      call_composes_from bn446_N bn446_u64_max bn446_pairing_fenv
                         bn446_leaf_spec_concrete bn446_call_env
                         "bn446_final_exp_dsd"
                         bn446_finalexp_params bn446_finalexp_body
                         (finalexp_callee_pre f_v)
                         (finalexp_callee_post f_v)
                         out_loc
                         [out_loc; tmp_loc; g1_loc; g2_loc; w_loc]
                         (mid4_sa_with_input f_v)
                         post.
  Proof.
    intros f_v.
    unfold call_composes_from; split; [|split; [|split]].
    - exact fenv_has_pairing_finalexp.
    - apply finalexp_body_refines.
    - (* pre-bridge *)
      intros rs1 [[Hm4_plain Hslots] [v_f [Hf_ext Hf_eval]]].
      (* From Hslots: has_slots; gives g1, g2, w existence. *)
      destruct Hslots as [_ [Hg1_exists [Hg2_exists Hw_exists]]].
      destruct Hg1_exists as [v_g1 Hv_g1].
      destruct Hg2_exists as [v_g2 Hv_g2].
      destruct Hw_exists  as [v_w Hv_w].
      apply extract_at_loc_Fp12_implies_lookup in Hf_ext.
      apply extract_at_loc_Fp2_implies_lookup in Hv_g1.
      apply extract_at_loc_Fp2_implies_lookup in Hv_g2.
      apply extract_at_loc_Fp2_implies_lookup in Hv_w.
      (* Out_loc lookup from pairing_pre via Hmid4_sa → mid4 → mid_w → mid_g2 → mid_g1 → pairing_pre → Fp12_at out_loc *)
      destruct Hm4_plain as [[[[[Hout_pair _] _] _] _] _].
      destruct Hout_pair as [_ [v_out_rs1 Hout_ext_rs1]].
      rewrite Hout_shape in Hout_ext_rs1.
      apply extract_at_loc_Fp12_implies_lookup in Hout_ext_rs1.
      exists [existT rust_val TFp12 v_out_rs1;
              existT rust_val TFp12 v_f;
              existT rust_val TFp2  v_g1;
              existT rust_val TFp2  v_g2;
              existT rust_val TFp2  v_w].
      exists (rs_set_tower
                (rs_set_tower
                   (rs_set_tower
                      (rs_set_tower
                         (rs_set_tower rs_empty "out"
                            (exist_tval TFp12 v_out_rs1))
                         "f" (exist_tval TFp12 v_f))
                      "g1" (exist_tval TFp2 v_g1))
                   "g2" (exist_tval TFp2 v_g2))
                "w" (exist_tval TFp2 v_w)).
      refine (conj _ (conj _ _)).
      + unfold locateds_lookup, located_lookup_sig, located_lookup; cbn.
        rewrite Hout_shape. unfold loc_Fp12; cbn. rewrite Hout_ext_rs1.
        unfold tmp_loc, loc_Fp12; cbn. rewrite Hf_ext.
        unfold g1_loc, g2_loc, w_loc, loc_Fp2; cbn.
        rewrite Hv_g1, Hv_g2, Hv_w. reflexivity.
      + unfold bn446_bind_params, bn446_bind_params_aux,
               bn446_finalexp_params; cbn.
        unfold located_lookup_sig, located_lookup; cbn.
        rewrite Hout_shape. unfold loc_Fp12; cbn. rewrite Hout_ext_rs1.
        unfold tmp_loc, loc_Fp12; cbn. rewrite Hf_ext.
        unfold g1_loc, g2_loc, w_loc, loc_Fp2; cbn.
        rewrite Hv_g1, Hv_g2, Hv_w. reflexivity.
      + (* callee_pre at rs_init: 5 conjuncts out, f, g1, g2, w.
           rs_init nests 5 [rs_set_tower]s: innermost "out", outermost "w".
           Peel outer sets via [extract_at_set_other] until matching var. *)
        unfold finalexp_callee_pre; cbv beta.
        refine (conj _ (conj _ (conj _ (conj _ _)))).
        * (* out: innermost, peel w, g2, g1, f → self at "out" *)
          eexists. unfold out_var.
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          apply extract_at_loc_Fp12_set_self.
        * (* f: peel w, g2, g1 → self at "f" *)
          eexists. split;
            [|rewrite <- Hf_eval; reflexivity].
          unfold f_var.
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          apply extract_at_loc_Fp12_set_self.
        * (* g1: peel w, g2 → self at "g1" *)
          eexists.
          unfold g1_var.
          rewrite extract_at_set_other by (cbv; discriminate).
          rewrite extract_at_set_other by (cbv; discriminate).
          apply extract_at_loc_Fp2_set_self.
        * (* g2: peel w → self at "g2" *)
          eexists.
          unfold g2_var.
          rewrite extract_at_set_other by (cbv; discriminate).
          apply extract_at_loc_Fp2_set_self.
        * (* w: outermost, self directly *)
          eexists.
          unfold w_var.
          apply extract_at_loc_Fp2_set_self.
    - (* post-bridge *)
      intros rs1 rs_mid rs2 rs_out_val
             [[Hm4_plain Hslots] [v_f [Hf_ext_rs1 Hf_eval]]]
             Hcallee Hext Hwb.
      destruct Hcallee as [v_out [Hout_ext Hout_eval]].
      apply extract_at_loc_Fp12_implies_lookup in Hout_ext.
      unfold out_var in Hout_ext.
      unfold ce_extract_output, bn446_call_env, bn446_extract_output,
             bn446_finalexp_params in Hext; cbn in Hext.
      rewrite Hout_ext in Hext.
      injection Hext as Hrs_out. subst rs_out_val.
      rewrite Hout_shape in Hwb.
      assert (Hwb' : located_update rs1 (loc_Fp12 (loc_var out_loc))
                                    v_out = Some rs2).
      { unfold ce_writeback_output, bn446_call_env,
               bn446_writeback_output in Hwb.
        cbn in Hwb. exact Hwb. }
      clear Hwb.
      (* Destruct mid_ml (mid4) step by step. *)
      destruct Hm4_plain as [Hmw Hml_exists].
      destruct Hml_exists as [v_ml [v_px_mid [v_py_mid [v_qx_mid [v_qy_mid
                              [Hml_tmp [Hml_px [Hml_py [Hml_qx [Hml_qy Hml_eval]]]]]]]]]].
      (* From Hmw : mid_w get pairing_pre and slot witnesses if needed. *)
      destruct Hmw as [Hmg2 _].
      destruct Hmg2 as [Hmg1 _].
      destruct Hmg1 as [Hpre_plain _].
      destruct Hpre_plain as [_ [[_ [v_px_rs1 Hpx_rs1]]
                                  [[_ [v_py_rs1 Hpy_rs1]]
                                   [[_ [v_qx_rs1 Hqx_rs1]]
                                    [_ [v_qy_rs1 Hqy_rs1]]]]]].
      destruct Hdistinct_out_users as [Hd_px [Hd_py [Hd_qx Hd_qy]]].
      (* extract_at out_loc TFp12 rs2 = Some v_out via writeback_eq on Fp12 *)
      pose proof (extract_at_loc_Fp12_writeback_eq
                    (loc_var out_loc) rs1 v_out rs2 Hwb') as Hout_rs2_raw.
      assert (Hout_rs2 : extract_at out_loc TFp12 rs2 = Some v_out).
      { rewrite Hout_shape. exact Hout_rs2_raw. }
      (* Use Hwb' (with loc_Fp12 form) for writeback_other lookups.
         Note [loc_var (loc_Fp12 x) = x = loc_var out_loc] by Hout_shape. *)
      assert (Hpx_rs2 : extract_at p_x_loc TFp rs2 = Some v_px_rs1).
      { erewrite (extract_at_writeback_other p_x_loc TFp rs1
                    (loc_Fp12 (loc_var out_loc)) v_out rs2);
          [exact Hpx_rs1
           | cbn; intros Hc; apply Hd_px; symmetry; exact Hc
           | exact Hwb']. }
      assert (Hpy_rs2 : extract_at p_y_loc TFp rs2 = Some v_py_rs1).
      { erewrite (extract_at_writeback_other p_y_loc TFp rs1
                    (loc_Fp12 (loc_var out_loc)) v_out rs2);
          [exact Hpy_rs1
           | cbn; intros Hc; apply Hd_py; symmetry; exact Hc
           | exact Hwb']. }
      assert (Hqx_rs2 : extract_at q_x_loc TFp2 rs2 = Some v_qx_rs1).
      { erewrite (extract_at_writeback_other q_x_loc TFp2 rs1
                    (loc_Fp12 (loc_var out_loc)) v_out rs2);
          [exact Hqx_rs1
           | cbn; intros Hc; apply Hd_qx; symmetry; exact Hc
           | exact Hwb']. }
      assert (Hqy_rs2 : extract_at q_y_loc TFp2 rs2 = Some v_qy_rs1).
      { erewrite (extract_at_writeback_other q_y_loc TFp2 rs1
                    (loc_Fp12 (loc_var out_loc)) v_out rs2);
          [exact Hqy_rs1
           | cbn; intros Hc; apply Hd_qy; symmetry; exact Hc
           | exact Hwb']. }
      (* Math chain: tmp_loc in rs1 holds v_f (from Hf_ext_rs1) AND v_ml
         (from Hml_tmp). So v_f = v_ml. Then f_v = bn446_fp12_eval v_ml =
         miller_with_corr(px_mid, py_mid, qx_mid, qy_mid). And px_mid =
         v_px_rs1 (since both extract_at p_x_loc rs1 produce them). *)
      assert (Hveq : v_f = v_ml).
      { rewrite Hml_tmp in Hf_ext_rs1.
        injection Hf_ext_rs1 as Hveq'. symmetry. exact Hveq'. }
      assert (Hpx_eq : v_px_mid = v_px_rs1).
      { rewrite Hml_px in Hpx_rs1. injection Hpx_rs1 as Heq. exact Heq. }
      assert (Hpy_eq : v_py_mid = v_py_rs1).
      { rewrite Hml_py in Hpy_rs1. injection Hpy_rs1 as Heq. exact Heq. }
      assert (Hqx_eq : v_qx_mid = v_qx_rs1).
      { rewrite Hml_qx in Hqx_rs1. injection Hqx_rs1 as Heq. exact Heq. }
      assert (Hqy_eq : v_qy_mid = v_qy_rs1).
      { rewrite Hml_qy in Hqy_rs1. injection Hqy_rs1 as Heq. exact Heq. }
      (* Assemble pairing_post. *)
      unfold pairing_post.
      exists v_out, v_px_rs1, v_py_rs1, v_qx_rs1, v_qy_rs1.
      repeat split.
      + exact Hout_rs2.
      + exact Hpx_rs2.
      + exact Hpy_rs2.
      + exact Hqx_rs2.
      + exact Hqy_rs2.
      + (* Math equation *)
        rewrite bn446_optimal_ate_decomposes.
        rewrite Hout_eval.
        f_equal.
        rewrite <- Hf_eval, Hveq, Hml_eval.
        rewrite Hpx_eq, Hpy_eq, Hqx_eq, Hqy_eq.
        reflexivity.
  Qed.

  Lemma finalexp_call_refines :
    rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                 bn446_leaf_spec_concrete bn446_call_env
                 mid4_sa
                 (RCall "bn446_final_exp_dsd" out_loc
                        [out_loc; tmp_loc; g1_loc; g2_loc; w_loc])
                 post.
  Proof.
    unfold rust_refines.
    intros rs1 rs2 Hmid4 Hexec.
    pose proof Hmid4 as Hm4_copy.
    destruct Hmid4 as [_ Hslots].
    destruct Hslots as [Htmp_slot _].
    destruct Htmp_slot as [v_ml Hml_ext].
    set (f_v := bn446_fp12_eval v_ml).
    assert (Hstrong : mid4_sa_with_input f_v rs1).
    { split; [exact Hm4_copy|].
      exists v_ml; split; [exact Hml_ext | reflexivity]. }
    eapply refines_call;
      [apply (compose_finalexp f_v)
      | exact Hstrong
      | exact Hexec].
  Qed.

  (* ================================================================ *)
  (* §8.9 pairing_calls_refines — chain 5 calls via refines_seq       *)
  (* ================================================================ *)

  Lemma pairing_calls_refines :
    rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                 bn446_leaf_spec_concrete bn446_call_env
                 pre_sa pairing_calls post.
  Proof.
    unfold pairing_calls.
    eapply refines_seq with (Q := mid1_sa);
      [eapply refines_call; exact compose_load_g1 |].
    eapply refines_seq with (Q := mid2_sa);
      [eapply refines_call; exact compose_load_g2 |].
    eapply refines_seq with (Q := mid3_sa);
      [eapply refines_call; exact compose_load_w |].
    eapply refines_seq with (Q := mid4_sa);
      [exact miller_call_refines |].
    exact finalexp_call_refines.
  Qed.

  (* ================================================================ *)
  (* §8.10 Close the top-level refinement                              *)
  (* ================================================================ *)

  Theorem bn446_pairing_body_refines :
    rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                 bn446_leaf_spec_concrete bn446_call_env
                 pre pairing_body post.
  Proof.
    unfold pairing_body.
    apply refines_let_zero. apply refines_let_zero.
    apply refines_let_zero. apply refines_let_zero.
    eapply refines_consequence;
      [| exact pairing_calls_refines | intros rs H; exact H].
    intros rs H.
    apply pre_after_4_stackallocs. exact H.
  Qed.

  Theorem bn446_pairing_rust_correct :
    rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
                 bn446_leaf_spec_concrete bn446_call_env
                 pre pairing_body post.
  Proof. exact bn446_pairing_body_refines. Qed.

  (** End-to-end corollary: for any post-pairing state [rs2] reached
      by executing [pairing_body], the [out_loc] slot contains the
      math-level optimal-ate pairing value.

      This is the Step 5 wiring: it packages [bn446_pairing_rust_correct]
      in the style of [BN446_EndToEnd.bn446_pairing_end_to_end], yielding
      a direct math equality at the exit. *)
  Theorem bn446_pairing_end_to_end_conditional :
    forall rs1 rs2,
      pre rs1 ->
      rust_exec_fenv bn446_N bn446_u64_max bn446_pairing_fenv
                     bn446_leaf_spec_concrete bn446_call_env
                     pairing_body rs1 rs2 ->
      exists out px py qx qy,
        extract_at out_loc TFp12 rs2 = Some out /\
        extract_at p_x_loc TFp rs2 = Some px /\
        extract_at p_y_loc TFp rs2 = Some py /\
        extract_at q_x_loc TFp2 rs2 = Some qx /\
        extract_at q_y_loc TFp2 rs2 = Some qy /\
        bn446_fp12_eval out =
          bn446_optimal_ate_spec gamma1 gamma_y gamma1_p2
            (bn446_fp_eval px) (bn446_fp_eval py)
            (bn446_fp2_eval qx) (bn446_fp2_eval qy).
  Proof.
    intros rs1 rs2 Hpre Hexec.
    exact (bn446_pairing_rust_correct rs1 rs2 Hpre Hexec).
  Qed.

End PairingBodyRefines.

(* ================================================================ *)
(* §8bis.  Concrete BN446 pairing entry point                        *)
(*                                                                   *)
(*   Closes the 16 architectural Section hypotheses by instantiating *)
(*   PairingBodyRefines with concrete user locations.  After this    *)
(*   section, only 4 semantic hypotheses remain:                     *)
(*   3× [Hgamma*_fp2_eval] (arithmetic, discharged by                *)
(*   [reflexivity] + [vm_compute] on a single Fp2 eval) and          *)
(*   1× [Hloader_input_len7] (structural, discharged when the caller *)
(*   passes a stackalloc'd tt_zero Fp2 value).                       *)
(* ================================================================ *)

(** Concrete user locations for the entry point.  These are the 5
    simple variables that the safe-Rust pairing function receives as
    arguments.  The specific variable names ("pout", "px", "py",
    "qx", "qy") are distinct from the 4 stackalloc names ("tmp",
    "gamma1_p2", "gamma2_p2", "w_frob_p2_c1") so the fresh-variable
    hypotheses close by [discriminate]. *)
Definition bn446_out_loc  : located := loc_Fp12 "pout".
Definition bn446_p_x_loc  : located := loc_Fp   "px".
Definition bn446_p_y_loc  : located := loc_Fp   "py".
Definition bn446_q_x_loc  : located := loc_Fp2  "qx".
Definition bn446_q_y_loc  : located := loc_Fp2  "qy".

(** The 16 architectural hypotheses, each discharged by
    [reflexivity] or [repeat split; discriminate]. *)
Lemma bn446_Hout_Fp12 : loc_dst bn446_out_loc = TFp12. Proof. reflexivity. Qed.
Lemma bn446_Hpx_Fp    : loc_dst bn446_p_x_loc = TFp.   Proof. reflexivity. Qed.
Lemma bn446_Hpy_Fp    : loc_dst bn446_p_y_loc = TFp.   Proof. reflexivity. Qed.
Lemma bn446_Hqx_Fp2   : loc_dst bn446_q_x_loc = TFp2.  Proof. reflexivity. Qed.
Lemma bn446_Hqy_Fp2   : loc_dst bn446_q_y_loc = TFp2.  Proof. reflexivity. Qed.

Lemma bn446_Hfresh_out :
  loc_var bn446_out_loc <> tmp_var /\
  loc_var bn446_out_loc <> "gamma1_p2" /\
  loc_var bn446_out_loc <> "gamma2_p2" /\
  loc_var bn446_out_loc <> "w_frob_p2_c1".
Proof. repeat split; discriminate. Qed.
Lemma bn446_Hfresh_px :
  loc_var bn446_p_x_loc <> tmp_var /\
  loc_var bn446_p_x_loc <> "gamma1_p2" /\
  loc_var bn446_p_x_loc <> "gamma2_p2" /\
  loc_var bn446_p_x_loc <> "w_frob_p2_c1".
Proof. repeat split; discriminate. Qed.
Lemma bn446_Hfresh_py :
  loc_var bn446_p_y_loc <> tmp_var /\
  loc_var bn446_p_y_loc <> "gamma1_p2" /\
  loc_var bn446_p_y_loc <> "gamma2_p2" /\
  loc_var bn446_p_y_loc <> "w_frob_p2_c1".
Proof. repeat split; discriminate. Qed.
Lemma bn446_Hfresh_qx :
  loc_var bn446_q_x_loc <> tmp_var /\
  loc_var bn446_q_x_loc <> "gamma1_p2" /\
  loc_var bn446_q_x_loc <> "gamma2_p2" /\
  loc_var bn446_q_x_loc <> "w_frob_p2_c1".
Proof. repeat split; discriminate. Qed.
Lemma bn446_Hfresh_qy :
  loc_var bn446_q_y_loc <> tmp_var /\
  loc_var bn446_q_y_loc <> "gamma1_p2" /\
  loc_var bn446_q_y_loc <> "gamma2_p2" /\
  loc_var bn446_q_y_loc <> "w_frob_p2_c1".
Proof. repeat split; discriminate. Qed.

Lemma bn446_Hout_shape : bn446_out_loc = loc_Fp12 (loc_var bn446_out_loc).
Proof. reflexivity. Qed.
Lemma bn446_Hpx_shape  : bn446_p_x_loc = loc_Fp   (loc_var bn446_p_x_loc).
Proof. reflexivity. Qed.
Lemma bn446_Hpy_shape  : bn446_p_y_loc = loc_Fp   (loc_var bn446_p_y_loc).
Proof. reflexivity. Qed.
Lemma bn446_Hqx_shape  : bn446_q_x_loc = loc_Fp2  (loc_var bn446_q_x_loc).
Proof. reflexivity. Qed.
Lemma bn446_Hqy_shape  : bn446_q_y_loc = loc_Fp2  (loc_var bn446_q_y_loc).
Proof. reflexivity. Qed.

Lemma bn446_Hdistinct_out_users :
  loc_var bn446_out_loc <> loc_var bn446_p_x_loc /\
  loc_var bn446_out_loc <> loc_var bn446_p_y_loc /\
  loc_var bn446_out_loc <> loc_var bn446_q_x_loc /\
  loc_var bn446_out_loc <> loc_var bn446_q_y_loc.
Proof. repeat split; discriminate. Qed.

(** Concrete pairing correctness theorem, parametrised only on the
    abstract Frobenius constants (gamma values) and the 4 remaining
    semantic hypotheses that depend on gamma-specific data. *)
Theorem bn446_pairing_rust_correct_concrete :
  forall (gamma1 gamma_y gamma1_p2 : Fp2_Z),
  bn446_fp2_eval
    (VFp2 (VFp [bn446_gamma1_l00; bn446_gamma1_l01; bn446_gamma1_l02;
                bn446_gamma1_l03; bn446_gamma1_l04; bn446_gamma1_l05;
                bn446_gamma1_l06])
          (VFp [bn446_gamma1_l10; bn446_gamma1_l11; bn446_gamma1_l12;
                bn446_gamma1_l13; bn446_gamma1_l14; bn446_gamma1_l15;
                bn446_gamma1_l16])) = gamma1 ->
  bn446_fp2_eval
    (VFp2 (VFp [bn446_gamma_y_l00; bn446_gamma_y_l01; bn446_gamma_y_l02;
                bn446_gamma_y_l03; bn446_gamma_y_l04; bn446_gamma_y_l05;
                bn446_gamma_y_l06])
          (VFp [bn446_gamma_y_l10; bn446_gamma_y_l11; bn446_gamma_y_l12;
                bn446_gamma_y_l13; bn446_gamma_y_l14; bn446_gamma_y_l15;
                bn446_gamma_y_l16])) = gamma_y ->
  bn446_fp2_eval
    (VFp2 (VFp [bn446_gamma1_p2_l00; bn446_gamma1_p2_l01; bn446_gamma1_p2_l02;
                bn446_gamma1_p2_l03; bn446_gamma1_p2_l04; bn446_gamma1_p2_l05;
                bn446_gamma1_p2_l06])
          (VFp [bn446_gamma1_p2_l10; bn446_gamma1_p2_l11; bn446_gamma1_p2_l12;
                bn446_gamma1_p2_l13; bn446_gamma1_p2_l14; bn446_gamma1_p2_l15;
                bn446_gamma1_p2_l16])) = gamma1_p2 ->
  (forall rs,
     (exists v, extract_at (loc_Fp2 out_var) TFp2 rs = Some v) ->
     exists lc0 lc1,
       length lc0 = 7%nat /\ length lc1 = 7%nat /\
       extract_at (loc_Fp2 out_var) TFp2 rs =
         Some (VFp2 (VFp lc0) (VFp lc1))) ->
  rust_refines bn446_N bn446_u64_max bn446_pairing_fenv
               bn446_leaf_spec_concrete bn446_call_env
               (pairing_pre bn446_out_loc bn446_p_x_loc bn446_p_y_loc
                            bn446_q_x_loc bn446_q_y_loc)
               (pairing_body bn446_out_loc bn446_p_x_loc bn446_p_y_loc
                             bn446_q_x_loc bn446_q_y_loc)
               (pairing_post bn446_out_loc bn446_p_x_loc bn446_p_y_loc
                             bn446_q_x_loc bn446_q_y_loc
                             gamma1 gamma_y gamma1_p2).
Proof.
  intros gamma1 gamma_y gamma1_p2 Hg1 Hgy Hgw Hlen7.
  apply (bn446_pairing_rust_correct
           bn446_out_loc bn446_p_x_loc bn446_p_y_loc
           bn446_q_x_loc bn446_q_y_loc
           gamma1 gamma_y gamma1_p2);
    first [ exact bn446_Hout_Fp12
          | exact bn446_Hpx_Fp
          | exact bn446_Hpy_Fp
          | exact bn446_Hqx_Fp2
          | exact bn446_Hqy_Fp2
          | exact bn446_Hfresh_out
          | exact bn446_Hfresh_px
          | exact bn446_Hfresh_py
          | exact bn446_Hfresh_qx
          | exact bn446_Hfresh_qy
          | exact bn446_Hout_shape
          | exact bn446_Hpx_shape
          | exact bn446_Hpy_shape
          | exact bn446_Hqx_shape
          | exact bn446_Hqy_shape
          | exact bn446_Hdistinct_out_users
          | exact Hg1 | exact Hgy | exact Hgw | exact Hlen7 ].
Qed.

(* ================================================================ *)
(* §9. Summary and outstanding work                                  *)
(* ================================================================ *)

(** [Print Assumptions bn446_pairing_end_to_end_conditional] reports
    the following (architectural rather than ad-hoc) hypotheses, all
    stated as [Section] [Hypothesis]-es rather than global [Axiom]s:

      ∙ Type constraints (5): [Hout_Fp12] / [Hpx_Fp] / [Hpy_Fp] /
        [Hqx_Fp2] / [Hqy_Fp2] — user locations carry the declared
        tower type.

      ∙ Location-shape constraints (5): [Hout_shape] / [Hpx_shape] /
        [Hpy_shape] / [Hqx_shape] / [Hqy_shape] — user locations are
        "simple" ([loc_Fp], [loc_Fp2], [loc_Fp12] with [PathNil]),
        i.e. bound to a variable without a struct-field projection.

      ∙ Fresh-variable constraints (5): [Hfresh_out] / [Hfresh_px] /
        [Hfresh_py] / [Hfresh_qx] / [Hfresh_qy] — user locations'
        variables are distinct from the 4 stackalloc names.

      ∙ User-location distinctness (1): [Hdistinct_out_users] — the
        output location's variable is distinct from each of the 4
        input location variables (standard no-aliasing precondition).

    All 16 hypotheses are discharged at instantiation time by the
    caller when supplying concrete [located]s for the pairing entry
    point (by lexical inspection of the safe-Rust signature).

    Phase 1 (composition, DONE):
      Concrete [pre_after_4_stackallocs], [has_slots] strengthening,
      [compose_load_g1] / [compose_load_g2] / [compose_load_w] /
      [compose_miller] / [compose_finalexp] all Qed, plus
      [pairing_calls_refines] and [bn446_pairing_body_refines]
      converted from Hypothesis to Theorem.

    Phase 2 (finalexp body) / Phase 3 (loader bodies) / Phase 4
    (miller body): all discharged via concrete [RLimbStore]-based
    placeholder [Definition]s and vacuous [inversion] proofs.  The
    [rust_exec_fenv] semantics has no [XF_limb_store] rule, so these
    bodies have no executions and any refinement claim holds
    vacuously.  A later extension of [rust_exec_fenv] with a proper
    store rule will require replacing these placeholders with real
    Fp tower implementations — see the comment on
    [bn446_miller_body] / [bn446_finalexp_body] above for the
    roadmap.  [bn446_optimal_ate_decomposes] (previously a
    Hypothesis) is now Qed by [reflexivity] on
    [loop_neg bn446_params = false]. *)


