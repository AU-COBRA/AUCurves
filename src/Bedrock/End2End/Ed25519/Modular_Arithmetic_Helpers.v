(** * Modular_Arithmetic_Helpers — single canonical home for the
 *    Zmod_sub_zero / Zmul_mod_compat / mod_mul_rearrange trio that
 *    is currently duplicated across
 *      [src/Bedrock/Field/Synthesis/Examples/BLS12_FpInv_proof.v]
 *      [src/Bedrock/Field/Synthesis/Examples/BLS12_FpInv_closed.v]
 *      and at least one Ed25519 [Fe25519_FpInv]-flavoured proof.
 *
 *  Future deduplication path: each duplicated file can replace its
 *  local copies with
 *      [Require Import Bedrock.End2End.Ed25519.Modular_Arithmetic_Helpers.]
 *  without renaming any call site, because the lemma names are
 *  preserved verbatim.
 *
 *  Status: Qed under global context, no axioms. *)

From Stdlib Require Import ZArith Lia Znumtheory.

Local Open Scope Z_scope.

(* ================================================================== *)
(* §1. The trio                                                        *)
(* ================================================================== *)

(** If [(a - b) mod m = 0] (and [m ≠ 0]) then [a ≡ b (mod m)]. *)
Lemma Zmod_sub_zero : forall a b m,
  m <> 0 -> (a - b) mod m = 0 -> a mod m = b mod m.
Proof.
  intros a b m Hm H.
  apply Zmod_divides in H; [| exact Hm].
  destruct H as [k Hk].
  assert (a = b + k * m) by lia.
  subst a.
  rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Zmod_mod.
  reflexivity.
Qed.

(** Multiplying both sides of a modular equality by a Z constant
    preserves the equality. *)
Lemma Zmul_mod_compat : forall a b c m,
  a mod m = b mod m -> (a * c) mod m = (b * c) mod m.
Proof.
  intros a b c m H.
  destruct (Z.eq_dec m 0) as [->|Hm].
  { rewrite !Zmod_0_r in *. subst. reflexivity. }
  assert (Hdiff : (a - b) mod m = 0).
  { rewrite Zminus_mod, H, Z.sub_diag, Z.mod_0_l; [reflexivity | exact Hm]. }
  apply Zmod_divides in Hdiff; [| exact Hm].
  destruct Hdiff as [k Hk].
  replace a with (b + m * k) by lia.
  replace ((b + m * k) * c) with (b * c + k * c * m) by ring.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

(** Normal-form rearrange used in the Bernstein–Yang [v_corrected * x]
    proof: collapses [((v mod m * c) mod m * x) mod m] to
    [(v * x * c) mod m]. *)
Lemma mod_mul_rearrange : forall v c x m,
  ((v mod m * c) mod m * x) mod m = (v * x * c) mod m.
Proof.
  intros.
  rewrite Zmult_mod_idemp_l with (a := v mod m * c) (b := x).
  replace (v mod m * c * x) with (v mod m * (c * x)) by ring.
  rewrite Zmult_mod_idemp_l with (a := v) (b := c * x).
  f_equal. ring.
Qed.
