Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bw6_761_prime_certif.

Local Open Scope Z_scope.

Local Existing Instances default_parameters default_parameters_ok.

(* BW6-761 prime (761 bits, 12 x 64-bit limbs) *)
Local Definition m := Eval compute in bw6_761_modulus.
Local Definition prefix := "bw6_761_"%string.

Instance names : names_of_operations.
Proof. make_names_of_operations prefix. Defined.

Definition ops : wbwmontgomery_reified_ops m.
Proof. make_reified_ops. Time Defined.

Instance bw6_bedrock2_funcs : bedrock2_wbwmontgomery_funcs.
Proof. funcs_from_ops ops. Defined.

Instance bw6_bedrock2_specs : bedrock2_wbwmontgomery_specs.
Proof. specs_from_ops ops m. Defined.

Instance bw6_bedrock2_correctness : bedrock2_wbwmontgomery_correctness.
Proof. prove_correctness ops m. Qed.
