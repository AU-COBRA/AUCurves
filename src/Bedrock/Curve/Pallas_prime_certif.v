(* Pallas prime certificate -- primality proof via Pocklington.
   Exports pallas_modulus and prime_pallas. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
From Coqprime Require Import PocklingtonRefl BasePrimes.

Local Open Scope positive_scope.

Definition pallas_modulus : Z := 28948022309329048855892746252171976963363056481941560715954676764349967630337%Z.

Definition pallas_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos 28948022309329048855892746252171976963363056481941560715954676764349967630337)%Z.

Lemma pallas_modulus_pos : pallas_modulus = Z.pos pallas_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Lemma prime_pallas : prime pallas_modulus.
Proof.
  rewrite pallas_modulus_pos.
  apply (Pocklington_refl
          (Pock_certif pallas_prime_pos 5
            ((539204044132271846773, 1)::(2,32)::nil)
            3528487722874966710488899962520)
         ((Pock_certif 539204044132271846773 5
            ((14923, 1)::(3, 5)::(2,2)::nil) 4900163) ::
          (Proof_certif 14923 prime14923) ::
          (Proof_certif 3 prime3) ::
          (Proof_certif 2 prime2) ::
           nil)).
  native_cast_no_check (refl_equal true).
Qed.
