(** * BLS12-381: the functional pairing theorem for the concrete function list of the extraction.

    [bls12_pairing_funcs] is the list of bedrock2 functions that the C printer
    ([BLS12_Extract.all_funcs]) emits: the fiat-crypto base-field functions followed by
    [BLS12_Pairing.bls12_all_pairing_funcs].  The function environment is
    [map.of_list (bls12_pairing_funcs ++ extra)] for an arbitrary list [extra]; since
    [map.of_list] keeps the first binding of a name, [extra] cannot shadow a function of the
    extraction.

    - [get_of_list_find]: [map.get (map.of_list l) k] is the first binding of [k] in [l].
    - [bls12_pairing_env_facts]: the 16 environment facts of
      [BLS12_PairingFunctionalClosed.bls12_pairing_functional_closed] hold for every [extra],
      by computation on the names of [bls12_pairing_funcs].
    - [bls12_pairing_functional_of_arith_leaves]: the functional specification of
      [bls12_pairing] for this environment, assuming only the 19 arithmetic leaf specs
      ([bls12_pairing_arith_leaves]).
    - [bls12_pairing_funcs_missing]: the extraction's list has no binding for the Fp2-level
      callees (mul, add, sub, square, inv, opp, felem_copy) nor for the base-field opp, inv and
      from_word; their code is linked from outside the verified list (hand-written Rust
      wrappers / C).  For [extra = []] the corresponding leaf specs are therefore unsatisfiable
      (a call to an unbound function has weakest precondition [False]); a non-vacuous
      instance of the theorem needs verified bodies for these functions in [extra].
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Require Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExpHardDSD.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctional.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalClosed.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module FE := Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Module CE := Bedrock.Field.Synthesis.Examples.BLS12_CycExp.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Existing Instances
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

Local Notation function_t := (String.string * Syntax.func)%type.

(** The function list of the C printer ([BLS12_Extract.all_funcs], same expression). *)
Definition bls12_pairing_funcs : list function_t :=
  [ bls12_add; bls12_sub; bls12_mul; bls12_square;
    bls12_select_znz;
    ("bls12_felem_copy", bls12_felem_copy) ] ++ BLS12_Pairing.bls12_all_pairing_funcs.

(** ** Lookup in [map.of_list] *)

Definition first_binding (l : list function_t) (k : string) : option Syntax.func :=
  option_map snd (List.find (fun p => String.eqb (fst p) k) l).

Lemma get_of_list_find (l : list function_t) (k : string) :
  map.get (map.of_list l : env) k = first_binding l k.
Proof.
  unfold first_binding.
  induction l as [| [k0 v0] l IH]; cbn [map.of_list List.find fst].
  - rewrite map.get_empty. reflexivity.
  - rewrite map.get_put_dec. destruct (String.eqb k0 k); [reflexivity | exact IH].
Qed.

Lemma first_binding_app (l1 l2 : list function_t) (k : string) v :
  first_binding l1 k = Some v -> first_binding (l1 ++ l2) k = Some v.
Proof.
  unfold first_binding. induction l1 as [| a l1 IH]; simpl.
  - discriminate.
  - destruct (String.eqb (fst a) k); [intros H; exact H | exact IH].
Qed.

(** One conversion per name: [List.find] on [bls12_pairing_funcs] only compares names, and the
    element it returns is syntactically the expected function, so the bodies are never
    normalized ([vm_compute] would evaluate every body of the list). *)
Local Ltac env_fact :=
  intros extra; rewrite get_of_list_find; apply first_binding_app;
  exact eq_refl.

Section EnvFacts.
  Variable extra : list function_t.
  Local Notation functions := (map.of_list (bls12_pairing_funcs ++ extra) : env).

  Lemma env_pairing : map.get functions "bls12_pairing" = Some (snd bls12_pairing).
  Proof. revert extra; env_fact. Qed.
  Lemma env_load_gamma1_p2 :
    map.get functions "bls12_load_gamma1_p2" = Some (snd bls12_load_gamma1_p2).
  Proof. revert extra; env_fact. Qed.
  Lemma env_load_gamma2_p2 :
    map.get functions "bls12_load_gamma2_p2" = Some (snd bls12_load_gamma2_p2).
  Proof. revert extra; env_fact. Qed.
  Lemma env_load_w_frob_p2_c1 :
    map.get functions "bls12_load_w_frob_p2_c1" = Some (snd bls12_load_w_frob_p2_c1).
  Proof. revert extra; env_fact. Qed.
  Lemma env_miller_loop : map.get functions "bls12_miller_loop" = Some (snd bls12_miller_loop).
  Proof. revert extra; env_fact. Qed.
  Lemma env_make_line : map.get functions "bls12_make_line" = Some (snd bls12_make_line).
  Proof. revert extra; env_fact. Qed.
  Lemma env_Fp2_mul_fp : map.get functions "bls12_Fp2_mul_fp" = Some (snd bls12_Fp2_mul_fp).
  Proof. revert extra; env_fact. Qed.
  Lemma env_final_exp : map.get functions "bls12_final_exp" = Some (snd bls12_final_exp).
  Proof. revert extra; env_fact. Qed.
  Lemma env_final_exp_hard_dsd :
    map.get functions "bls12_final_exp_hard_dsd" = Some (snd bls12_final_exp_hard_dsd).
  Proof. revert extra; env_fact. Qed.
  Lemma env_cyc_exp_x_neg :
    map.get functions "bls12_Fp12_cyc_exp_x_neg" = Some (snd bls12_Fp12_cyc_exp_x_neg).
  Proof. revert extra; env_fact. Qed.
  Lemma env_cyc_exp_c_neg :
    map.get functions "bls12_Fp12_cyc_exp_c_neg" = Some (snd bls12_Fp12_cyc_exp_c_neg).
  Proof. revert extra; env_fact. Qed.
  Lemma env_load_gamma1 : map.get functions "bls12_load_gamma1" = Some (snd bls12_load_gamma1).
  Proof. revert extra; env_fact. Qed.
  Lemma env_load_gamma2 : map.get functions "bls12_load_gamma2" = Some (snd bls12_load_gamma2).
  Proof. revert extra; env_fact. Qed.
  Lemma env_load_w_frob_c1 :
    map.get functions "bls12_load_w_frob_c1" = Some (snd bls12_load_w_frob_c1).
  Proof. revert extra; env_fact. Qed.
  Lemma env_cyc_sqr_gs :
    map.get functions "bls12_Fp12_cyclotomic_square" = Some (snd bls12_Fp12_cyclotomic_square).
  Proof. revert extra; env_fact. Qed.
  Lemma env_mul_by_line :
    map.get functions "bls12_Fp12_mul_by_line" = Some (snd bls12_Fp12_mul_by_line).
  Proof. revert extra; env_fact. Qed.
End EnvFacts.

(** ** The arithmetic leaves *)

(** The 19 leaf specs of [bls12_pairing_functional_closed] (Miller loop, then final
    exponentiation). *)
Definition bls12_pairing_arith_leaves (functions : env) : Prop :=
  MS.spec_of_Fp2_mul functions /\ MS.spec_of_Fp2_add functions /\ MS.spec_of_Fp2_sub functions /\
  MS.spec_of_Fp2_sqr functions /\ MS.spec_of_Fp2_inv functions /\ MS.spec_of_Fp2_opp functions /\
  MS.spec_of_Fp2_felem_copy functions /\
  MS.spec_of_Fp12_sqr functions /\ MS.spec_of_Fp12_felem_copy functions /\
  MS.spec_of_Fp_mul functions /\ MS.spec_of_Fp_felem_copy functions /\ MS.spec_of_Fp_from_word functions /\
  FE.spec_of_Fp12_mul functions /\ FE.spec_of_Fp12_inv functions /\ FE.spec_of_Fp12_conjugate functions /\
  spec_of_Fp2_mul_xi_381 functions /\ CE.spec_of_Fp_from_word functions /\
  spec_of_Fp12_frobenius_381 functions /\ spec_of_Fp12_frobenius_p2_381 functions.

Theorem bls12_pairing_env_leaves : forall extra,
  bls12_pairing_arith_leaves (map.of_list (bls12_pairing_funcs ++ extra)) ->
  bls12_pairing_leaves (map.of_list (bls12_pairing_funcs ++ extra)).
Proof.
  intros extra H.
  destruct H as (H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & H35).
  (* The conjunction in the order of [bls12_pairing_leaves], built explicitly: [exact] of an
     environment fact against a leaf spec would unfold the spec. *)
  refine (conj (env_pairing extra) _).
  refine (conj (env_load_gamma1_p2 extra) _).
  refine (conj (env_load_gamma2_p2 extra) _).
  refine (conj (env_load_w_frob_p2_c1 extra) _).
  refine (conj (env_miller_loop extra) _).
  refine (conj (env_make_line extra) _).
  refine (conj (env_Fp2_mul_fp extra) _).
  refine (conj (env_final_exp extra) _).
  refine (conj (env_final_exp_hard_dsd extra) _).
  refine (conj (env_cyc_exp_x_neg extra) _).
  refine (conj (env_cyc_exp_c_neg extra) _).
  refine (conj (env_load_gamma1 extra) _).
  refine (conj (env_load_gamma2 extra) _).
  refine (conj (env_load_w_frob_c1 extra) _).
  refine (conj (env_cyc_sqr_gs extra) _).
  refine (conj (env_mul_by_line extra) _).
  refine (conj H17 _).
  refine (conj H18 _).
  refine (conj H19 _).
  refine (conj H20 _).
  refine (conj H21 _).
  refine (conj H22 _).
  refine (conj H23 _).
  refine (conj H24 _).
  refine (conj H25 _).
  refine (conj H26 _).
  refine (conj H27 _).
  refine (conj H28 _).
  refine (conj H29 _).
  refine (conj H30 _).
  refine (conj H31 _).
  refine (conj H32 _).
  refine (conj H33 _).
  refine (conj H34 _).
  exact H35.
Qed.

Theorem bls12_pairing_functional_of_arith_leaves : forall extra,
  bls12_pairing_arith_leaves (map.of_list (bls12_pairing_funcs ++ extra)) ->
  spec_of_bls12_pairing_functional (map.of_list (bls12_pairing_funcs ++ extra)).
Proof.
  intros extra H.
  exact (bls12_pairing_functional_of_leaves _ (bls12_pairing_env_leaves extra H)).
Qed.

Print Assumptions bls12_pairing_functional_of_arith_leaves.

(** ** Callees outside the extraction's list *)

(** The names are the ones the leaf specs call (projections of the instances of
    BLS12_MillerStepFunctional). *)
Definition bls12_pairing_external_names : list string :=
  [ @AbstractField.mul _ MS.bls12_Fp2_params'; @AbstractField.add _ MS.bls12_Fp2_params';
    @AbstractField.sub _ MS.bls12_Fp2_params'; @AbstractField.square _ MS.bls12_Fp2_params';
    @AbstractField.inv _ MS.bls12_Fp2_params'; @AbstractField.opp _ MS.bls12_Fp2_params';
    @AbstractField.felem_copy _ MS.bls12_Fp2_params';
    @PrimeField.from_word MS.bls12_pf_params;
    @PrimeField.opp MS.bls12_pf_params; @PrimeField.inv MS.bls12_pf_params ].

Lemma bls12_pairing_external_names_eq :
  bls12_pairing_external_names =
  [ "bls12_Fp2_mul"; "bls12_Fp2_add"; "bls12_Fp2_sub"; "bls12_Fp2_square"; "bls12_Fp2_inv";
    "bls12_Fp2_opp"; "bls12_Fp2_felem_copy"; "bls12_from_word"; "bls12_opp"; "bls12_inv" ].
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_pairing_funcs_missing :
  Forall (fun k => map.get (map.of_list bls12_pairing_funcs : env) k = None)
    bls12_pairing_external_names.
Proof.
  rewrite bls12_pairing_external_names_eq.
  repeat constructor; rewrite get_of_list_find; exact eq_refl.
Qed.
