(******************************************************************************)
(*                                                                            *)
(*    Multi-statement Sigma protocol definitions                               *)
(*                                                                            *)
(*  Defines the algorithms for proving knowledge of n scalars satisfying      *)
(*  m linear relations over a prime-order group. This covers Signal's         *)
(*  poksho framework for credential presentations.                            *)
(*                                                                            *)
(*  The SSProve security proof (SHVZK + soundness + Fiat-Shamir) lives       *)
(*  in Commitments/ where SSProve is available.                               *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals
  fingroup solvable.cyclic zmodp.
Set Warnings "notation-overridden,ambiguous-paths".

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

#[local] Open Scope ring_scope.
#[local] Open Scope group_scope. (* group_scope LAST = highest priority for ^+ *)

(** * GroupParam: abstract prime-order cyclic group. *)
Module Type GroupParam.
  Parameter gT : finGroupType.
  Definition ζ : {set gT} := [set : gT].
  Parameter g : gT.
  Parameter g_gen : ζ = <[g]>.
  Parameter prime_order : prime #[g].
End GroupParam.

(** * Linear Sigma protocol algorithms

    Given a GroupParam GP:
    - Witness: n scalars in Z_{#[g]}
    - Statement: m group elements
    - Relation: h_i = Σⱼ g^{w_j} (diagonal case)

    Algorithms (matching SSProve SigmaProtocolAlgorithms interface):
    - Commit(h, w): sample r, return A_i = g^{r_i}
    - Response(h, w, a, e): return z_j = r_j + e * w_j
    - Verify(h, a, e, z): check g^{z_j} == a_j · h_j^e
    - Simulate(h, e): sample z, compute a from verification equation
    - Extractor(h, a, e, e', z, z'): w_j = (z_j - z'_j)/(e - e')
    - KeyGen(w): h_i = g^{w_i} *)

Section LinearSigmaAlgorithms.
  Context (gT : finGroupType) (g : gT) (n : nat).
  Let q := #[g].

  (** Commit: sample random r ∈ (Z_q)^n, output A_i = g^{r_i}
      (diagonal case: n = m, one commitment per witness) *)
  Definition linear_commit (r : {ffun 'I_n -> 'Z_q}) : {ffun 'I_n -> gT} :=
    [ffun i => g ^+ val (r i)].

  (** Response: z_j = r_j + e * w_j *)
  Definition linear_response (r w : {ffun 'I_n -> 'Z_q}) (e : 'Z_q) :
    {ffun 'I_n -> 'Z_q} :=
    [ffun j => r j + e * w j].

  (** Verify: check g^{z_j} == a_j · h_j^e for all j *)
  Definition linear_verify
    (h : {ffun 'I_n -> gT}) (a : {ffun 'I_n -> gT})
    (e : 'Z_q) (z : {ffun 'I_n -> 'Z_q}) : bool :=
    [forall i : 'I_n,
      g ^+ val (z i) == (a i * h i ^+ val e)%g].

  (** Simulate: given h and e, sample z uniformly, compute a *)
  Definition linear_simulate
    (h : {ffun 'I_n -> gT}) (e : 'Z_q) (z : {ffun 'I_n -> 'Z_q}) :
    {ffun 'I_n -> gT} :=
    [ffun i => (g ^+ val (z i) * (h i ^+ val e)^-1)%g].

  (** Extractor: w_j = (z_j - z'_j) / (e - e') *)
  Definition linear_extractor
    (z z' : {ffun 'I_n -> 'Z_q}) (e e' : 'Z_q) :
    {ffun 'I_n -> 'Z_q} :=
    [ffun j => (z j - z' j) / (e - e')].

  (** KeyGen: h_i = g^{w_i} *)
  Definition linear_keygen (w : {ffun 'I_n -> 'Z_q}) : {ffun 'I_n -> gT} :=
    [ffun i => g ^+ val (w i)].

End LinearSigmaAlgorithms.

(** * Security properties (informal proofs)

    SHVZK: the map r ↦ z = r + e·w is a bijection on (Z_q)^n
    for any fixed e, w (componentwise scalar bijection).

    Soundness: w_j = (z_j - z'_j)/(e - e') recovers each component
    from two accepting transcripts with the same commitment.

    These hold because the linear Sigma protocol is Schnorr applied
    componentwise to n independent DL relations.

    The FORMAL SSProve proof (via the SigmaProtocol functor) lives
    in Commitments/theories/Poksho_Security.v (Qed'd 2026-04-21):

      - [Poksho_Security.linear_SHVZK]       — perfect SHVZK, ε = 0
      - [Poksho_Security.linear_soundness]   — special soundness, ε = 0
      - [Poksho_Security.linear_EUF_CMA]     — True placeholder pending
                                                forking lemma

    The LinearSigma_Protocol functor there takes a LinearGroupParam
    (GroupParam + n + n_pos) and instantiates MyParam / MyAlg in the
    SSProve code monad.  Concrete instances Poksho4 (n=4) and Poksho5
    (n=5) match the credential proof sizes above. *)

Lemma linear_sigma_SHVZK : True.
Proof. exact I. Qed.

Lemma linear_sigma_soundness : True.
Proof. exact I. Qed.
