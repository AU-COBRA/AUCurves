(** * BLS24-509 Frobenius constants (precomputed gamma values).

    These are powers of tower nonresidues evaluated modulo p, needed
    by the Frobenius endomorphisms in the final exponentiation.

    All values verified by computation in Python using the BLS24-509
    prime p = (z-1)^2*(z^8-z^4+1)/3 + z, z = -0x800000ffff801. *)

From Coq Require Import ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.BLS24Pairing.Tower.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_prime.

Local Open Scope Z_scope.

Section FrobeniusConstants.
  Let p := bls24_509_prime_pos.
  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp4 := (Fp2 * Fp2)%type.
  Local Notation Fp8 := (Fp4 * Fp4)%type.

  (* Helper: construct field element from hex *)
  Local Notation "[ x ]" := (F.of_Z p x).

  (* ================================================================ *)
  (* Frobenius pi (x -> x^p)                                          *)
  (* ================================================================ *)

  (** gamma_fp4 = (1+u)^{(p-1)/2} in Fp2 *)
  Definition gamma_fp4 : Fp2 :=
    ([0x11e5521bcb21ac3ea8765fdb8a940d9109b4ab1b09723aeae29c73a11e3c586852ec3121d438c2f805c28ebd0522ee2e10f8712f13f86a40f288d055f9920189],
     [0x11e5521bcb21ac3ea8765fdb8a940d9109b4ab1b09723aeae29c73a11e3c586852ec3121d438c2f805c28ebd0522ee2e10f8712f13f86a40f288d055f9920189]).

  (** gamma_fp8 = v^{(p-1)/2} in Fp4 *)
  Definition gamma_fp8 : Fp4 :=
    (([0], [0]),
     ([0], [0x8fe34a02b967dd15e36690cd384c629355eb580ec434c775e5cd1383872ec8a8fc988b48c790bfbb03b282fc4f5ed3685de65048b03dc85adbc58b94b04421c])).

  (** gamma_fp24_1 = w^{(p-1)/3} in Fp8 *)
  Definition gamma_fp24_1 : Fp8 :=
    ((([0], [0]),
      ([0x35ba538b2da929924763dc2e1e85137426f3c2d9950aca22ba572215aa506e8d7fae80e810c85bc994aa862afe639b646cd7a325595f5b97324f5cf05c240c5],
       [0x11f9b1c74c5f3802d877b4f217d89bbf891b8c1bc3c7d1ea07448ee2856b89d28a739db0fb0c1b343680b3fdc1d49a1ca79642d518f79d472e181bbeb2fd91e6])),
     (([0], [0]), ([0], [0]))).

  (** gamma_fp24_2 = w^{2(p-1)/3} in Fp8 *)
  Definition gamma_fp24_2 : Fp8 :=
    ((([0x12bf078cf16682196faf4e4dfbd2d2b10691603aa2fda0b8130f7a0aa198a64cf88798f97b5a5c2c34d786cf45436cba6ec28602044fed90a6ca1f47477b9f56],
       [0x2964f730dd348828d3ea466fdee1a45c4f9680eba1addd41fda86f93e77ea6e69e6ecc600be44c49af3d5912c7767187fa137056a3da56ffa72f24671443355]),
      ([0], [0])),
     (([0], [0]), ([0], [0]))).

  (* ================================================================ *)
  (* Frobenius pi^2 (x -> x^{p^2})                                    *)
  (* ================================================================ *)

  (** gamma_fp4_p2 = (1+u)^{(p^2-1)/2} = p-1 in Fp (note: (0, p-1) = -1) *)
  Definition gamma_fp4_p2 : Fp2 :=
    ([0x155556ffff39ca9bfcedf2b4f9c0ecf6cb8ac8495d187e8c32ea0103e01090bb626e85bf7c18a0f0cfcb5c6071bad3d2ee63bd076e8d9300a13d118db8bfd2aa],
     [0]).

  (** gamma_fp8_p2 = v^{(p^2-1)/2} = u in Fp2 *)
  Definition gamma_fp8_p2 : Fp4 :=
    (([0], [1]), ([0], [0])).

  Definition gamma_fp24_p2_1 : Fp8 :=
    ((([0], [0x800008fffbc8bfb95c10064573d512e7608eb809f8837210349069202fc5b46ce35e046a9e458e94683bc19e53f7c63f39dedd94e1dd77d3809]),
      ([0], [0])),
     (([0], [0]), ([0], [0]))).

  Definition gamma_fp24_p2_2 : Fp8 :=
    ((([0x155556ffff39c29bfc5df2f86dc55735cb26710c0bea08834769617ba8ef8d725bdc82c320d1d2baef84b27c18d18d4f3249d7c7f2299f62b363c36fe1429aa3], [0]),
      ([0], [0])),
     (([0], [0]), ([0], [0]))).

  (* ================================================================ *)
  (* Frobenius pi^4 (x -> x^{p^4})                                    *)
  (* ================================================================ *)

  (** gamma_fp4_p4 = (1+u)^{(p^4-1)/2} = 1 (identity!) *)
  Definition gamma_fp4_p4 : Fp2 := ([1], [0]).

  Definition gamma_fp8_p4 : Fp4 :=
    (([0x155556ffff39ca9bfcedf2b4f9c0ecf6cb8ac8495d187e8c32ea0103e01090bb626e85bf7c18a0f0cfcb5c6071bad3d2ee63bd076e8d9300a13d118db8bfd2aa], [0]),
     ([0], [0])).

  Definition gamma_fp24_p4_1 : Fp8 :=
    ((([0x155556ffff39c29bfc5df2f86dc55735cb26710c0bea08834769617ba8ef8d725bdc82c320d1d2baef84b27c18d18d4f3249d7c7f2299f62b363c36fe1429aa3], [0]),
      ([0], [0])),
     (([0], [0]), ([0], [0]))).

  Definition gamma_fp24_p4_2 : Fp8 :=
    ((([0x155556ffff39c29bfc5df2f86dc55735cb26710c0bea08834769617ba8ef8d725bdc82c320d1d2baef84b27c18d18d4f3249d7c7f2299f62b363c36fe1429aa2], [0]),
      ([0], [0])),
     (([0], [0]), ([0], [0]))).

End FrobeniusConstants.
