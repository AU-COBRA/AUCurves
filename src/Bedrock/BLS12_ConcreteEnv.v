(** * BLS12-381: one concrete bedrock2 environment for G1, G2, GT and the pairing.

    [bls12_concrete_funcs] is the environment of the functional pairing theorem,
    [bls12_pairing_funcs ++ bls12_extra_funcs] (= [ExtractBLS12TowerJasmin.bls12_tower_funcs]),
    followed by [bls12_group_extra]:
    - [BLS12_G1ArenaRust.bls12_g1_funcs]: ["msm_bls12"], ["g1_scalar_mul"] and their callees
      (the list printed into [bls12-381-safe-rust/src/g1_msm_extracted.rs]);
    - [BLS12_G2ArenaRust.bls12_g2_funcs]: ["g2_scalar_mul"], the in-place and out-of-place
      addition and doubling over Fp2 and ["bls12_Fp2_three_b"] ([src/g2_extracted.rs]), and the
      constant-time ladder ["g2_scalar_mul_ct"] with its swap renamed ["ct_cswap12"]
      ([ExtractBLS12GroupJasmin.bls12_g2_funcs_jasmin], as in the Jasmin group module; the G1
      list has ["g1_scalar_mul_ct"] and its swap ["ct_cswap"]);
    - [ExtractBLS12GroupJasmin.bls12_zero], [bls12_one]: [bls12_from_word(out, 0 / 1)], the
      constant stores of the Jasmin group module;
    - [BLS12_Fp12Pow.bls12_Fp12_pow] (printed by no emitter).
    Apart from [bls12_Fp12_pow] and the nine entry points of the Jasmin group module (which
    only pass coordinate pointers on), these are the functions of
    [ExtractBLS12GroupJasmin.bls12_group_funcs], with the same bodies.

    Names.  [bls12_concrete_funcs_bound]: every function of the list (65 of the pairing
    environment, 22 of the group part) is bound in [bls12_concrete_env] to its own body.  The one name that occurs twice is
    ["bls12_felem_copy"] (in [bls12_pairing_funcs] and in [bls12_g1_funcs]), with the same body
    [bls12_felem_copy.bls12_felem_copy] ([bls12_concrete_names_dup]).

    The field leaves of the group theorems are discharged here for [bls12_concrete_env], by
    the proofs of the pairing environment ([BLS12_PairingLeaves*], [BLS12_FpExtra]):
    - G1 ([BLS12_MSM_Closed]): fiat-crypto [spec_of_BinOp bin_mul / bin_add / bin_sub]
      ([bls12_mul_correct], ...), [spec_of_store_const "bls12_zero" 0 / "bls12_one" 1]
      ([store_const_ok], from fiat-crypto's [spec_of_from_word] of [bls12_from_word]);
    - G2 ([BLS12_G2_ScalarMul]): [spec_of_af_mul / af_add / af_sub] at Fp2
      ([bls12_Fp2_mul_spec], ...; the same contracts as [MS.spec_of_Fp2_*] up to conversion);
    - GT ([BLS12_Fp12Pow]): [BLS12_CycExp.spec_of_Fp12_mul], [BLS12_Fp12Pow.spec_of_Fp12_sqr],
      [BLS12_CycExp.spec_of_Fp_from_word] ([bls12_Fp12_mul_spec], [bls12_Fp12_sqr_spec],
      [bls12_Fp_from_word_leaf_CE]).
    [bls12_concrete_extends]: the environment extends the pairing environment, so the
    pairing theorem holds for it too ([BLS12_ConcreteUnconditional]).  No Admitted, no Axiom. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith Lia.
From Stdlib Require Import Lists.List.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpExtra.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalEnv.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalLeaves.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp2.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesTower.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp12.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp12SqrInv.
Require Bedrock.Specs.AbstractField.
Require Bedrock.Specs.PrimeField.
Require Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp12Pow.
Require Bedrock.Group.CurveAdd.CurveAddAF.
Require Bedrock.BLS12_MSM_Wrappers.
Require Bedrock.BLS12_G1ArenaRust.
Require Bedrock.BLS12_G2ArenaRust.
Require Bedrock.BLS12_G2_ThreeB.
Require Bedrock.BLS12_G2_Closed.
Require Bedrock.BLS12_G2_ScalarMul.
Require Bedrock.ExtractBLS12GroupJasmin.
Require Bedrock.ExtractBLS12TowerJasmin.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module CE := Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Module GP := Bedrock.Field.Synthesis.Examples.BLS12_Fp12Pow.
Module GJ := Bedrock.ExtractBLS12GroupJasmin.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Existing Instances
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

Local Notation function_t := (String.string * Syntax.func)%type.

(** ** The environment *)

(** The G2 list as in the Jasmin group module, [GJ.bls12_g2_funcs_jasmin]: its swap
    ["ct_cswap"] (12 words) renamed ["ct_cswap12"] in its definition and in
    [g2_scalar_mul_ct], so that it is not shadowed by the G1 swap ["ct_cswap"] (6 words) of
    [bls12_g1_funcs] (#25 added both). *)
Definition bls12_group_extra : list function_t :=
  Bedrock.BLS12_G1ArenaRust.bls12_g1_funcs ++ GJ.bls12_g2_funcs_jasmin
  ++ [GJ.bls12_zero; GJ.bls12_one; GP.bls12_Fp12_pow].

Definition bls12_concrete_extra : list function_t := bls12_extra_funcs ++ bls12_group_extra.

Definition bls12_concrete_funcs : list function_t :=
  bls12_pairing_funcs ++ bls12_concrete_extra.

Definition bls12_concrete_env : Semantics.env := map.of_list bls12_concrete_funcs.

(** The pairing environment comes first: it is the tower list the Jasmin emitter prints. *)
Lemma bls12_concrete_funcs_tower :
  bls12_concrete_funcs = Bedrock.ExtractBLS12TowerJasmin.bls12_tower_funcs ++ bls12_group_extra.
Proof.
  cbv [bls12_concrete_funcs bls12_concrete_extra Bedrock.ExtractBLS12TowerJasmin.bls12_tower_funcs].
  apply app_assoc.
Qed.

(** The group part is the Jasmin group module's list without its entry points, with [bls12_zero],
    [bls12_one] where the module has them, and [bls12_Fp12_pow] added; the module renames the G2
    swap ["ct_cswap"] to ["ct_cswap12"] ([GJ.bls12_g2_funcs_jasmin], #25). *)
Lemma bls12_group_funcs_jasmin :
  GJ.bls12_group_funcs
  = GJ.bls12_group_entries ++ Bedrock.BLS12_G1ArenaRust.bls12_g1_funcs
    ++ GJ.bls12_g2_funcs_jasmin ++ [GJ.bls12_zero; GJ.bls12_one]
    ++ Bedrock.ExtractBLS12TowerJasmin.bls12_tower_funcs.
Proof. reflexivity. Qed.

(** ** Lookup *)

Lemma first_binding_app_None' (l1 l2 : list function_t) (k : string) :
  first_binding l1 k = None -> first_binding (l1 ++ l2) k = first_binding l2 k.
Proof.
  unfold first_binding. induction l1 as [| a l1 IH]; simpl.
  - intros _. reflexivity.
  - destruct (String.eqb (fst a) k); [discriminate | exact IH].
Qed.

Lemma bls12_concrete_extends :
  map.extends bls12_concrete_env (map.of_list (bls12_pairing_funcs ++ bls12_extra_funcs)).
Proof.
  intros k v H. cbv [bls12_concrete_env bls12_concrete_funcs bls12_concrete_extra].
  rewrite get_of_list_find in *. rewrite app_assoc. exact (first_binding_app _ _ _ _ H).
Qed.

(** A function of [bls12_pairing_funcs]. *)
Local Ltac env_main :=
  cbv [bls12_concrete_env bls12_concrete_funcs];
  rewrite get_of_list_find; apply first_binding_app; exact eq_refl.
(** A function of [bls12_extra_funcs]. *)
Local Ltac env_extra :=
  cbv [bls12_concrete_env bls12_concrete_funcs bls12_concrete_extra];
  rewrite get_of_list_find, first_binding_app_None' by exact eq_refl;
  apply first_binding_app; exact eq_refl.
(** A function of [bls12_group_extra]. *)
Local Ltac env_group :=
  cbv [bls12_concrete_env bls12_concrete_funcs bls12_concrete_extra];
  rewrite get_of_list_find, first_binding_app_None' by exact eq_refl;
  rewrite first_binding_app_None' by exact eq_refl; exact eq_refl.

Local Notation env := bls12_concrete_env.

Lemma cenv_mul : map.get env "bls12_mul" = Some (snd bls12_mul).
Proof. env_main. Qed.
Lemma cenv_add : map.get env "bls12_add" = Some (snd bls12_add).
Proof. env_main. Qed.
Lemma cenv_sub : map.get env "bls12_sub" = Some (snd bls12_sub).
Proof. env_main. Qed.
Lemma cenv_square : map.get env "bls12_square" = Some (snd bls12_square).
Proof. env_main. Qed.
Lemma cenv_felem_copy : map.get env "bls12_felem_copy" = Some bls12_felem_copy.
Proof. env_main. Qed.

Lemma cenv_from_word : map.get env "bls12_from_word" = Some (snd bls12_from_word).
Proof. env_extra. Qed.
Lemma cenv_to_mont : map.get env "bls12_to_mont" = Some (snd bls12_to_mont).
Proof. env_extra. Qed.
Lemma cenv_opp : map.get env "bls12_opp" = Some (snd bls12_opp).
Proof. env_extra. Qed.
Lemma cenv_Fp2_felem_copy :
  map.get env "bls12_Fp2_felem_copy" = Some (snd bls12_Fp2_felem_copy).
Proof. env_extra. Qed.
Lemma cenv_Fp2_add : map.get env "bls12_Fp2_add" = Some (snd bls12_Fp2_add).
Proof. env_extra. Qed.
Lemma cenv_Fp2_sub : map.get env "bls12_Fp2_sub" = Some (snd bls12_Fp2_sub).
Proof. env_extra. Qed.
Lemma cenv_Fp2_mul : map.get env "bls12_Fp2_mul" = Some (snd bls12_Fp2_mul).
Proof. env_extra. Qed.
Lemma cenv_Fp2_square : map.get env "bls12_Fp2_square" = Some (snd bls12_Fp2_square).
Proof. env_extra. Qed.
Lemma cenv_Fp2_opp : map.get env "bls12_Fp2_opp" = Some (snd bls12_Fp2_opp).
Proof. env_extra. Qed.
Lemma cenv_Fp2_inv : map.get env "bls12_Fp2_inv" = Some (snd bls12_Fp2_inv).
Proof. env_extra. Qed.

(** G1 *)
Lemma cenv_msm_bls12 :
  map.get env "msm_bls12" = Some (snd Bedrock.BLS12_G1ArenaRust.g1_msm).
Proof. env_group. Qed.
Lemma cenv_g1_scalar_mul :
  map.get env "g1_scalar_mul" = Some (snd Bedrock.BLS12_G1ArenaRust.g1_smul).
Proof. env_group. Qed.
Lemma cenv_msm_curve_add :
  map.get env "msm_curve_add" = Some (snd Bedrock.BLS12_G1ArenaRust.msm_curve_add).
Proof. env_group. Qed.
Lemma cenv_msm_curve_double :
  map.get env "msm_curve_double" = Some (snd Bedrock.BLS12_G1ArenaRust.msm_curve_double).
Proof. env_group. Qed.
Lemma cenv_curve_add :
  map.get env "curve_add" = Some (snd Bedrock.BLS12_G1ArenaRust.g1_curve_add).
Proof. env_group. Qed.
Lemma cenv_curve_double_a0 :
  map.get env "curve_double_a0" = Some (snd Bedrock.BLS12_G1ArenaRust.g1_curve_double_a0).
Proof. env_group. Qed.
Lemma cenv_store_zero :
  map.get env "store_zero" = Some (snd Bedrock.BLS12_G1ArenaRust.g1_store_zero).
Proof. env_group. Qed.
Lemma cenv_three_b :
  map.get env "bls12_three_b" = Some (snd Bedrock.BLS12_G1ArenaRust.g1_three_b).
Proof. env_group. Qed.
(** ["bls12_felem_copy"] is bound by the pairing list, to the body of [g1_felem_copy]. *)
Lemma cenv_g1_felem_copy :
  map.get env "bls12_felem_copy" = Some (snd Bedrock.BLS12_G1ArenaRust.g1_felem_copy).
Proof. exact cenv_felem_copy. Qed.
Lemma cenv_zero : map.get env "bls12_zero" = Some (snd GJ.bls12_zero).
Proof. env_group. Qed.
Lemma cenv_one : map.get env "bls12_one" = Some (snd GJ.bls12_one).
Proof. env_group. Qed.

(** G2 *)
Lemma cenv_g2_scalar_mul :
  map.get env "g2_scalar_mul" = Some Bedrock.BLS12_G2_ScalarMul.g2_scalar_mul_func.
Proof. env_group. Qed.
Lemma cenv_g2_curve_add_ip :
  map.get env Bedrock.BLS12_G2_ScalarMul.g2_curve_add_ip_name
  = Some Bedrock.BLS12_G2_ScalarMul.g2_add_ip_body.
Proof. env_group. Qed.
Lemma cenv_g2_curve_double_ip :
  map.get env Bedrock.BLS12_G2_ScalarMul.g2_curve_double_ip_name
  = Some Bedrock.BLS12_G2_ScalarMul.g2_double_ip_body.
Proof. env_group. Qed.
Lemma cenv_g2_three_b :
  map.get env Bedrock.BLS12_G2_Closed.g2_three_b_name
  = Some Bedrock.BLS12_G2_ThreeB.g2_three_b_body.
Proof. env_group. Qed.

(** GT *)
Lemma cenv_Fp12_pow : map.get env "bls12_Fp12_pow" = Some GP.bls12_Fp12_pow_func.
Proof. env_group. Qed.

(** ** Names

    The names of the group part, none of which is bound by the pairing environment except
    ["bls12_felem_copy"], which [bls12_pairing_funcs] binds to the body of [g1_felem_copy]. *)

Lemma bls12_group_extra_names :
  List.map fst bls12_group_extra =
  [ "msm_bls12"; "g1_scalar_mul"; "msm_curve_add"; "msm_curve_double"; "curve_add";
    "curve_double_a0"; "store_zero"; "bls12_three_b"; "bls12_felem_copy";
    "g1_scalar_mul_ct"; "ct_cswap";
    "g2_scalar_mul"; "g2_curve_add_ip"; "g2_curve_double_ip"; "g2_curve_add";
    "g2_curve_double"; "bls12_Fp2_three_b"; "g2_scalar_mul_ct"; "ct_cswap12";
    "bls12_zero"; "bls12_one"; "bls12_Fp12_pow" ].
Proof. reflexivity. Qed.

Lemma bls12_group_extra_names_NoDup : NoDup (List.map fst bls12_group_extra).
Proof.
  rewrite bls12_group_extra_names.
  repeat constructor; cbv [In]; intuition discriminate.
Qed.

Lemma bls12_group_names_fresh :
  Forall (fun k => first_binding (bls12_pairing_funcs ++ bls12_extra_funcs) k = None)
    [ "msm_bls12"; "g1_scalar_mul"; "msm_curve_add"; "msm_curve_double"; "curve_add";
      "curve_double_a0"; "store_zero"; "bls12_three_b"; "g1_scalar_mul_ct"; "ct_cswap";
      "g2_scalar_mul"; "g2_curve_add_ip"; "g2_curve_double_ip"; "g2_curve_add";
      "g2_curve_double"; "bls12_Fp2_three_b"; "g2_scalar_mul_ct"; "ct_cswap12";
      "bls12_zero"; "bls12_one"; "bls12_Fp12_pow" ].
Proof. repeat constructor; exact eq_refl. Qed.

Lemma bls12_concrete_names_dup :
  first_binding (bls12_pairing_funcs ++ bls12_extra_funcs) "bls12_felem_copy"
  = Some (snd Bedrock.BLS12_G1ArenaRust.g1_felem_copy).
Proof. exact eq_refl. Qed.

(** Hence every function of the group part is bound to its own body. *)
Lemma bls12_group_extra_bound :
  Forall (fun f : function_t => map.get env (fst f) = Some (snd f)) bls12_group_extra.
Proof.
  cbv [bls12_group_extra Bedrock.BLS12_G1ArenaRust.bls12_g1_funcs
       GJ.bls12_g2_funcs_jasmin Bedrock.BLS12_G2ArenaRust.bls12_g2_funcs List.map app].
  repeat constructor; cbv [env bls12_concrete_env]; rewrite get_of_list_find; exact eq_refl.
Qed.

(** The 65 functions of the pairing environment are bound to their own bodies too (their names
    are pairwise distinct). *)
Lemma bls12_tower_bound :
  Forall (fun f : function_t => map.get env (fst f) = Some (snd f))
    (bls12_pairing_funcs ++ bls12_extra_funcs).
Proof.
  cbv [bls12_pairing_funcs BLS12_Pairing.bls12_all_pairing_funcs BLS12_Pairing.bls12_Fp6_funcs
       BLS12_Pairing.bls12_Fp12_funcs BLS12_Pairing.bls12_pairing_ops bls12_extra_funcs app].
  repeat constructor; cbv [env bls12_concrete_env]; rewrite get_of_list_find; exact eq_refl.
Qed.

(** No function of the list is shadowed by an earlier one with another body. *)
Lemma bls12_concrete_funcs_bound :
  Forall (fun f : function_t => map.get env (fst f) = Some (snd f)) bls12_concrete_funcs.
Proof.
  cbv [bls12_concrete_funcs bls12_concrete_extra]. rewrite app_assoc.
  apply Forall_app. exact (conj bls12_tower_bound bls12_group_extra_bound).
Qed.

(** ** The G1 leaves *)

Section G1Leaves.
  Existing Instances Bitwidth64.BW64 bls12_field_parameters bls12_frep
    bls12_field_parameters_ok bls12_frep_ok.

  Local Notation F := (F M_pos).

  Lemma cenv_spec_mul : spec_of_BinOp bin_mul env.
  Proof. exact (bls12_mul_correct env cenv_mul). Qed.
  Lemma cenv_spec_add : spec_of_BinOp bin_add env.
  Proof. exact (bls12_add_correct env cenv_add). Qed.
  Lemma cenv_spec_sub : spec_of_BinOp bin_sub env.
  Proof. exact (bls12_sub_correct env cenv_sub). Qed.

  Local Ltac solve_mapget :=
    first [ apply map.get_put_same
          | (rewrite !map.get_put_diff by congruence;
             first [ apply map.get_put_same | eassumption | reflexivity ])
          | eassumption
          | reflexivity ].

  Local Ltac eval_call_args :=
    repeat match goal with
           | x := _ : @Interface.map.rep _ _ _ |- _ => subst x
           end;
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.dexpr
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | (eexists; split; [ solve [ solve_mapget ] | ])
      | (eexists; split; [ exact eq_refl | ]) ]).

  Local Ltac wp_expose_call :=
    repeat (lazymatch goal with
            | |- WeakestPrecondition.cmd _ _ _ _ _ _ =>
                unfold1_cmd_goal;
                cbv beta match delta [WeakestPrecondition.cmd_body]
            end).

  (** A one-call body [name(out) := bls12_from_word(out, c)] stores the constant [c], tight,
      by fiat-crypto's [spec_of_from_word]. *)
  Lemma store_const_ok (name : string) (c : Z) (functions : Semantics.env) :
    map.get functions name
    = Some (["out"], [], cmd.call [] "bls12_from_word" [expr.var "out"; expr.literal c]) ->
    spec_of_from_word functions ->
    0 <= c < 2 ^ 64 ->
    Bedrock.BLS12_MSM_Wrappers.spec_of_store_const name (F.of_Z M_pos c) functions.
  Proof.
    intros Henv Hfw Hc. cbv [Bedrock.BLS12_MSM_Wrappers.spec_of_store_const].
    intros p x R tr m Hm.
    cbv [Compilation2.FElem] in Hm.
    destruct Hm as (m1 & m2 & Hsplit & (v & Hv) & HR).
    eapply SeparationLogic.sep_emp_l in Hv. destruct Hv as (_ & Hv).
    apply (proj1 (felem_to_bytes p v m1)) in Hv.
    eapply WeakestPreconditionProperties.start_func; [ exact Henv | ].
    cbv match beta delta [WeakestPrecondition.func].
    eexists. split. { reflexivity. }
    wp_expose_call.
    eexists. split. { solve [ eval_call_args ]. }
    eapply Semantics.weaken_call.
    1: { eapply Hfw. split.
         - exists m1, m2. split; [ exact Hsplit | ]. split; [ exact Hv | exact HR ].
         - apply ws2bs_felem_length. }
    intros tr1 m1' rets1 (Hr1 & Htr1 & X & HX & HbX & Hm1'). subst rets1 tr1.
    eexists. split. { exact eq_refl. }
    cbv beta match fix delta [list_map list_map_body].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    cbv [Compilation2.FElem].
    eapply SeparationLogic.Proper_sep_impl1; [ | reflexivity | exact Hm1' ].
    intros mX HmX. exists X.
    eapply SeparationLogic.sep_emp_l. split; [ | exact HmX ]. split; [ | exact HbX ].
    rewrite HX. rewrite word.unsigned_of_Z_nowrap by exact Hc. reflexivity.
  Qed.

  Lemma cenv_spec_zero :
    Bedrock.BLS12_MSM_Wrappers.spec_of_store_const "bls12_zero" (F.of_Z M_pos 0) env.
  Proof.
    eapply store_const_ok; [ exact cenv_zero
                           | exact (bls12_from_word_correct env cenv_from_word cenv_to_mont)
                           | lia ].
  Qed.

  Lemma cenv_spec_one :
    Bedrock.BLS12_MSM_Wrappers.spec_of_store_const "bls12_one" (F.of_Z M_pos 1) env.
  Proof.
    eapply store_const_ok; [ exact cenv_one
                           | exact (bls12_from_word_correct env cenv_from_word cenv_to_mont)
                           | lia ].
  Qed.
End G1Leaves.

(** ** The Fp and Fp2 leaves of the pairing environment, for [env] *)

Local Ltac envs :=
  first [ exact cenv_mul | exact cenv_add | exact cenv_sub | exact cenv_square
        | exact cenv_felem_copy | exact cenv_from_word | exact cenv_to_mont | exact cenv_opp
        | exact cenv_Fp2_felem_copy | exact cenv_Fp2_add | exact cenv_Fp2_sub
        | exact cenv_Fp2_mul | exact cenv_Fp2_square | exact cenv_Fp2_opp | exact cenv_Fp2_inv ].

Lemma cenv_Fp2_copy_leaf : MS.spec_of_Fp2_felem_copy env.
Proof. exact (bls12_Fp2_felem_copy_spec env cenv_felem_copy cenv_Fp2_felem_copy). Qed.
Lemma cenv_Fp2_mul_leaf : MS.spec_of_Fp2_mul env.
Proof. eapply bls12_Fp2_mul_spec; envs. Qed.
Lemma cenv_Fp2_add_leaf : MS.spec_of_Fp2_add env.
Proof. eapply bls12_Fp2_add_spec; envs. Qed.
Lemma cenv_Fp2_sub_leaf : MS.spec_of_Fp2_sub env.
Proof. eapply bls12_Fp2_sub_spec; envs. Qed.
Lemma cenv_Fp_copy_leaf : MS.spec_of_Fp_felem_copy env.
Proof. exact (bls12_Fp_felem_copy_leaf env cenv_felem_copy). Qed.
Lemma cenv_Fp_sub_leaf :
  AbstractField.binop_spec (F:=F
                                 (@Bedrock.Specs.PrimeField.M_pos MS.bls12_pf_params))
    (field_representation:=MS.bls12_Fp_rep) AbstractField.bin_sub env.
Proof. exact (bls12_Fp_sub_leaf env cenv_sub). Qed.
Lemma cenv_Fp_add_leaf :
  AbstractField.binop_spec (F:=F
                                 (@Bedrock.Specs.PrimeField.M_pos MS.bls12_pf_params))
    (field_representation:=MS.bls12_Fp_rep) AbstractField.bin_add env.
Proof. exact (bls12_Fp_add_leaf_MS env cenv_add). Qed.

(** ** The G2 leaves: the Fp2 contracts of [BLS12_G2_ScalarMul] *)

Section G2Leaves.
  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls12_Fp2.bls12_prime_parameters bls12_Fp2.bls12_field_representation
    bls12_Fp2.bls12_Fp2_field_parameters bls12_Fp2.bls12_Fp2_field_representation
    bls12_Fp2.bls12_prime_parameters_ok bls12_Fp2.bls12_field_representation_ok.
  Existing Instance PrimeField.prime_field_parameters.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp2 := (Fp * Fp)%type.

  Lemma cenv_spec_Fp2_mul : Bedrock.Group.CurveAdd.CurveAddAF.spec_of_af_mul (F:=Fp2) env.
  Proof. exact cenv_Fp2_mul_leaf. Qed.
  Lemma cenv_spec_Fp2_add : Bedrock.Group.CurveAdd.CurveAddAF.spec_of_af_add (F:=Fp2) env.
  Proof. exact cenv_Fp2_add_leaf. Qed.
  Lemma cenv_spec_Fp2_sub : Bedrock.Group.CurveAdd.CurveAddAF.spec_of_af_sub (F:=Fp2) env.
  Proof. exact cenv_Fp2_sub_leaf. Qed.
End G2Leaves.

(** ** The GT leaves: the contracts of [BLS12_Fp12Pow] *)

Lemma cenv_Fp12_mul_leaf : CE.spec_of_Fp12_mul env.
Proof.
  exact (bls12_Fp12_mul_spec bls12_concrete_extra cenv_Fp2_copy_leaf cenv_Fp2_add_leaf
           cenv_Fp2_sub_leaf cenv_Fp2_mul_leaf cenv_Fp_copy_leaf cenv_Fp_sub_leaf
           cenv_Fp_add_leaf).
Qed.

Lemma cenv_Fp12_sqr_leaf : GP.spec_of_Fp12_sqr env.
Proof.
  pose proof cenv_Fp2_copy_leaf as Hcp2.
  pose proof cenv_Fp2_mul_leaf as Hmul2.
  pose proof cenv_Fp2_add_leaf as Hadd2.
  pose proof cenv_Fp2_sub_leaf as Hsub2.
  assert (Hsqr2 : MS.spec_of_Fp2_sqr env).
  { eapply bls12_Fp2_square_spec.
    all: lazymatch goal with |- map.get _ _ = _ => envs | _ => exact Hmul2 end. }
  pose proof cenv_Fp_copy_leaf as Hcp1.
  pose proof cenv_Fp_sub_leaf as Hsub1.
  pose proof cenv_Fp_add_leaf as Hadd1.
  assert (H : MS.spec_of_Fp12_sqr env).
  { eapply (bls12_Fp12_sqr_leaf_MS bls12_concrete_extra).
  all:
    lazymatch goal with
    | |- MS.spec_of_Fp2_felem_copy _ => exact Hcp2
    | |- MS.spec_of_Fp2_add _ => exact Hadd2
    | |- MS.spec_of_Fp2_sub _ => exact Hsub2
    | |- MS.spec_of_Fp2_mul _ => exact Hmul2
    | |- MS.spec_of_Fp2_sqr _ => exact Hsqr2
    | |- MS.spec_of_Fp_felem_copy _ => exact Hcp1
    | |- AbstractField.binop_spec AbstractField.bin_sub _ => exact Hsub1
    | |- AbstractField.binop_spec AbstractField.bin_add _ => exact Hadd1
    | |- ?g => idtac "UNMATCHED" g; fail
    end. }
  exact H.
Qed.

Lemma cenv_Fp_from_word_leaf : CE.spec_of_Fp_from_word env.
Proof. exact (bls12_Fp_from_word_leaf_CE env cenv_from_word cenv_to_mont). Qed.
