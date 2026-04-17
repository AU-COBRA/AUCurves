(* Vesta prime certificate — primality proof via Pocklington.
   Exports vesta_modulus and prime_vesta.
   Certificate from AUCurves/src/Bedrock/Curve/Vesta_prime_certif.v *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List. Import ListNotations.
From Coqprime Require Import PocklingtonRefl BasePrimes.

Local Open Scope positive_scope.

Definition vesta_modulus : Z := 28948022309329048855892746252171976963363056481941647379679742748393362948097%Z.

Definition vesta_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos 28948022309329048855892746252171976963363056481941647379679742748393362948097)%Z.

Lemma vesta_modulus_pos : vesta_modulus = Z.pos vesta_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Lemma prime_vesta : prime vesta_modulus.
Proof.
  rewrite vesta_modulus_pos.
  apply (Pocklington_refl
          (Pock_certif vesta_prime_pos 5
            ((1690502597179744445941507, 1)::(2,32)::nil)
            2903932920479730657625245538929162)
         ((Pock_certif 1690502597179744445941507 2
            ((4129989133, 1)::(2,1)::nil) 12648372724) ::
          (Pock_certif 4129989133 2
            ((359, 1)::(2,2)::nil) 1161) ::
          (Proof_certif 359 prime359) ::
          (Proof_certif 2 prime2) ::
           nil)).
  native_cast_no_check (refl_equal true).
Qed.
