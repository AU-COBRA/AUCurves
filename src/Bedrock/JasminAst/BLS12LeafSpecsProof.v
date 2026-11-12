(** * fiat-crypto's BLS12-381 Fp contracts imply [BLS12LeafSpecs]'s bridge propositions.

    Loaded in fiat-crypto's environment (it requires bls12_prime.v, hence the synthesis
    pipeline, and so cannot be loaded with Jasmin's semantics).  [bls12_*_eq] check the
    printed bodies of [BLS12LeafBodies] against fiat's functions, the constant lemmas check the
    literals of [BLS12LeafSpecs] (modulus, Montgomery constant, limb count), and
    [bls12_*_contract_proof] derive each bridge proposition from [bls12_*_correct]. *)
From Stdlib Require Import String List ZArith.
Import ListNotations.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import bedrock2.Syntax bedrock2.Semantics bedrock2.BasicC64Semantics.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.JasminAst.BLS12LeafBodies Bedrock.JasminAst.BLS12LeafSpecs.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Lemma bls12_mul_eq : bls12_mul = ("bls12_mul", (params3, [], bls12_mul_body)).
Proof. vm_compute. reflexivity. Qed.
Lemma bls12_add_eq : bls12_add = ("bls12_add", (params3, [], bls12_add_body)).
Proof. vm_compute. reflexivity. Qed.
Lemma bls12_sub_eq : bls12_sub = ("bls12_sub", (params3, [], bls12_sub_body)).
Proof. vm_compute. reflexivity. Qed.
Lemma bls12_square_eq : bls12_square = ("bls12_square", (params2, [], bls12_square_body)).
Proof. vm_compute. reflexivity. Qed.
Lemma m_eq : m = bls12_p. Proof. reflexivity. Qed.
Lemma Mpos_eq : @M_pos bls12_field_parameters = bls12_p_pos. Proof. reflexivity. Qed.
Lemma mprime_eq : Crypto.PushButtonSynthesis.WordByWordMontgomery.m' m 64 = bls12_mprime. Proof. vm_compute. reflexivity. Qed.
Lemma n_eq : Crypto.PushButtonSynthesis.WordByWordMontgomery.n m 64 = 6%nat. Proof. vm_compute. reflexivity. Qed.
Lemma feval_eq (x : list word) : @feval _ _ _ _ _ bls12_frep x = eval_w x.
Proof.
  cbv [feval bls12_frep Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.field_representation Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation Crypto.Bedrock.Field.Interface.Representation.frep Crypto.Bedrock.Field.Interface.Representation.eval_words Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.eval_trans eval_w].
  rewrite mprime_eq, n_eq. reflexivity.
Qed.

Lemma bounded_eq (x : list word) :
  (@bounded_by _ _ _ _ _ bls12_frep (@loose_bounds _ _ _ _ _ bls12_frep) x <-> valid_w x) /\
  (@bounded_by _ _ _ _ _ bls12_frep (@tight_bounds _ _ _ _ _ bls12_frep) x <-> valid_w x).
Proof.
  cbv [bounded_by loose_bounds tight_bounds bls12_frep Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.field_representation Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation Crypto.Bedrock.Field.Interface.Representation.frep Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.list_in_bounds valid_w].
  rewrite n_eq. tauto.
Qed.

Lemma bls12_mul_contract_proof : bls12_mul_contract.
Proof.
  intros pout px py x y out Rr t mem0 (hx & hy & hvx & hvy & hout & hRx & hRy & hR).
  pose (fs := map.put map.empty "bls12_mul" (snd bls12_mul) : env).
  assert (hfs : map.get fs (fst bls12_mul) = Some (snd bls12_mul)) by apply map.get_put_same.
  pose proof (bls12_mul_correct fs hfs) as hspec.
  specialize (hspec pout px py (exist _ x hx) (exist _ y hy) out Rr t mem0).
  destruct (bounded_eq x) as [[_ hbx] _]; destruct (bounded_eq y) as [[_ hby] _].
  specialize (hspec (conj (hbx hvx) (conj (hby hvy) (conj hout (conj hRx (conj hRy hR)))))).
  destruct hspec as (argnames & retnames & body & hget & l & hl & hexec).
  unfold fs in hget; rewrite map.get_put_same, bls12_mul_eq in hget; cbn in hget.
  inversion hget; subst argnames retnames body; clear hget.
  exists fs, l; split; [exact hl|].
  eapply exec.weaken; [exact hexec|].
  intros t' m' l' (rets & hrets & hnil & htr & out0 & hfe & hb & hsep).
  split; [congruence|].
  exists (proj1_sig out0); split; [exact (proj2_sig out0)|].
  split; [rewrite <- !feval_eq; exact hfe|].
  split; [apply (proj1 (proj2 (bounded_eq _))); exact hb|].
  exact hsep.
Qed.

Lemma bls12_add_contract_proof : bls12_add_contract.
Proof.
  intros pout px py x y out Rr t mem0 (hx & hy & hvx & hvy & hout & hRx & hRy & hR).
  pose (fs := map.put map.empty "bls12_add" (snd bls12_add) : env).
  assert (hfs : map.get fs (fst bls12_add) = Some (snd bls12_add)) by apply map.get_put_same.
  pose proof (bls12_add_correct fs hfs) as hspec.
  specialize (hspec pout px py (exist _ x hx) (exist _ y hy) out Rr t mem0).
  destruct (bounded_eq x) as [_ [_ hbx]]; destruct (bounded_eq y) as [_ [_ hby]].
  specialize (hspec (conj (hbx hvx) (conj (hby hvy) (conj hout (conj hRx (conj hRy hR)))))).
  destruct hspec as (argnames & retnames & body & hget & l & hl & hexec).
  unfold fs in hget; rewrite map.get_put_same, bls12_add_eq in hget; cbn in hget.
  inversion hget; subst argnames retnames body; clear hget.
  exists fs, l; split; [exact hl|].
  eapply exec.weaken; [exact hexec|].
  intros t' m' l' (rets & hrets & hnil & htr & out0 & hfe & hb & hsep).
  split; [congruence|].
  exists (proj1_sig out0); split; [exact (proj2_sig out0)|].
  split; [rewrite <- !feval_eq; exact hfe|].
  split; [apply (proj1 (proj1 (bounded_eq _))); exact hb|].
  exact hsep.
Qed.

Lemma bls12_sub_contract_proof : bls12_sub_contract.
Proof.
  intros pout px py x y out Rr t mem0 (hx & hy & hvx & hvy & hout & hRx & hRy & hR).
  pose (fs := map.put map.empty "bls12_sub" (snd bls12_sub) : env).
  assert (hfs : map.get fs (fst bls12_sub) = Some (snd bls12_sub)) by apply map.get_put_same.
  pose proof (bls12_sub_correct fs hfs) as hspec.
  specialize (hspec pout px py (exist _ x hx) (exist _ y hy) out Rr t mem0).
  destruct (bounded_eq x) as [_ [_ hbx]]; destruct (bounded_eq y) as [_ [_ hby]].
  specialize (hspec (conj (hbx hvx) (conj (hby hvy) (conj hout (conj hRx (conj hRy hR)))))).
  destruct hspec as (argnames & retnames & body & hget & l & hl & hexec).
  unfold fs in hget; rewrite map.get_put_same, bls12_sub_eq in hget; cbn in hget.
  inversion hget; subst argnames retnames body; clear hget.
  exists fs, l; split; [exact hl|].
  eapply exec.weaken; [exact hexec|].
  intros t' m' l' (rets & hrets & hnil & htr & out0 & hfe & hb & hsep).
  split; [congruence|].
  exists (proj1_sig out0); split; [exact (proj2_sig out0)|].
  split; [rewrite <- !feval_eq; exact hfe|].
  split; [apply (proj1 (proj1 (bounded_eq _))); exact hb|].
  exact hsep.
Qed.

Lemma bls12_square_contract_proof : bls12_square_contract.
Proof.
  intros pout px x out Rr t mem0 (hx & hvx & hout & hRx & hR).
  pose (fs := map.put map.empty "bls12_square" (snd bls12_square) : env).
  assert (hfs : map.get fs (fst bls12_square) = Some (snd bls12_square)) by apply map.get_put_same.
  pose proof (bls12_square_correct fs hfs) as hspec.
  specialize (hspec pout px (exist _ x hx) out Rr t mem0).
  destruct (bounded_eq x) as [[_ hbx] _].
  specialize (hspec (conj (hbx hvx) (conj hout (conj hRx hR)))).
  destruct hspec as (argnames & retnames & body & hget & l & hl & hexec).
  unfold fs in hget; rewrite map.get_put_same, bls12_square_eq in hget; cbn in hget.
  inversion hget; subst argnames retnames body; clear hget.
  exists fs, l; split; [exact hl|].
  eapply exec.weaken; [exact hexec|].
  intros t' m' l' (rets & hrets & hnil & htr & out0 & hfe & hb & hsep).
  split; [congruence|].
  exists (proj1_sig out0); split; [exact (proj2_sig out0)|].
  split; [rewrite <- !feval_eq; exact hfe|].
  split; [apply (proj1 (proj2 (bounded_eq _))); exact hb|].
  exact hsep.
Qed.
