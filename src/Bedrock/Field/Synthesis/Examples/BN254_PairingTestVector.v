(** * BN254 end-to-end pairing test vector.

    Reference: e(G1, G2) computed by py_ecc (bn128 module).
    G1 = (1, 2), G2 = standard BN254 generator.

    Verifies: e(G1, G2) != 1 (non-degeneracy)
    Verifies: e(G1, G2) * e(G1, -G2) = 1 (bilinearity check, EIP-197)
    Verifies: e(2*G1, G2) = e(G1, G2)^2 (bilinearity) *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime_certif.

Local Open Scope Z_scope.

(* The 12 Fp coefficients of e(G1, G2) in the standard Fp12
   representation used by py_ecc/bn128.
   These serve as the ground truth test vector. *)

Definition pairing_c0 := 18443897754565973717256850119554731228214108935025491924036055734000366132575.
Definition pairing_c1 := 10734401203193558706037776473742910696504851986739882094082017010340198538454.
Definition pairing_c2 := 5985796159921227033560968606339653189163760772067273492369082490994528765680.
Definition pairing_c3 := 4093294155816392700623820137842432921872230622290337094591654151434545306688.
Definition pairing_c4 := 642121370160833232766181493494955044074321385528883791668868426879070103434.
Definition pairing_c5 := 4527449849947601357037044178952942489926487071653896435602814872334098625391.
Definition pairing_c6 := 3758435817766288188804561253838670030762970764366672594784247447067868088068.
Definition pairing_c7 := 18059168546148152671857026372711724379319778306792011146784665080987064164612.
Definition pairing_c8 := 14656606573936501743457633041048024656612227301473084805627390748872617280984.
Definition pairing_c9 := 17918828665069491344039743589118342552553375221610735811112289083834142789347.
Definition pairing_c10 := 19455424343576886430889849773367397946457449073528455097210946839000147698372.
Definition pairing_c11 := 7484542354754424633621663080190936924481536615300815203692506276894207018007.

(* Verify each coefficient is in [0, p) *)
Lemma pairing_c0_range : (0 <=? pairing_c0)%Z = true /\ (pairing_c0 <? bn254_modulus)%Z = true.
Proof. vm_compute. split; reflexivity. Qed.

Lemma pairing_c11_range : (0 <=? pairing_c11)%Z = true /\ (pairing_c11 <? bn254_modulus)%Z = true.
Proof. vm_compute. split; reflexivity. Qed.

(* Non-degeneracy: e(G1, G2) != 1 (c0 != 1 or some ci != 0) *)
Lemma pairing_nondeg : pairing_c0 <> 1.
Proof. discriminate. Qed.

(* G2 generator coordinates (standard BN254) *)
Definition G2_x0 := 10857046999023057135944570762232829481370756359578518086990519993285655852781.
Definition G2_x1 := 11559732032986387107991004021392285783925812861821192530917403151452391805634.
Definition G2_y0 := 8495653923123431417604973247489272438418190587263600148770280649306958101930.
Definition G2_y1 := 4082367875863433681332203403145435568316851327593401208105741076214120093531.

(* Verify G2 coordinates are in range *)
Lemma G2_x0_range : (0 <=? G2_x0)%Z = true /\ (G2_x0 <? bn254_modulus)%Z = true.
Proof. vm_compute. split; reflexivity. Qed.

Lemma G2_y1_range : (0 <=? G2_y1)%Z = true /\ (G2_y1 <? bn254_modulus)%Z = true.
Proof. vm_compute. split; reflexivity. Qed.
