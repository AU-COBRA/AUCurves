Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.

Local Open Scope Z_scope.

Local Existing Instances default_parameters default_parameters_ok.

(* Vesta prime: p = 2^254 + 45560315531419706090280762371685220353 *)
Local Definition m := Eval compute in 28948022309329048855892746252171976963363056481941647379679742748393362948097%Z.
Local Definition prefix := "vesta_"%string.

Instance names : names_of_operations.
Proof. make_names_of_operations prefix. Defined.

Definition ops : wbwmontgomery_reified_ops m.
Proof. make_reified_ops. Time Defined.

Instance vesta_bedrock2_funcs : bedrock2_wbwmontgomery_funcs.
Proof. funcs_from_ops ops. Defined.

Instance vesta_bedrock2_specs : bedrock2_wbwmontgomery_specs.
Proof. specs_from_ops ops m. Defined.

Instance vesta_bedrock2_correctness : bedrock2_wbwmontgomery_correctness.
Proof. prove_correctness ops m. Qed.
