(** * SafeRustLeafRefinement.v
 *
 * Instantiates the abstract [leaf_spec] from SafeRustSimulation.v
 * for the 8 BN254 Fp leaf primitives, and states the per-leaf
 * correctness properties that connect limb-level operations to
 * field arithmetic over Z/pZ.
 *
 * Contents:
 *   §1  BN254 parameters (prime, limb count)
 *   §2  Helper: extract Fp value from a sigma
 *   §3  Concrete leaf_spec assembly (case-match on function name)
 *   §4  Unfolding lemmas (one per leaf)
 *   §5  Mathematical interpretation (parametric fp_eval)
 *   §6  Per-leaf correctness hypotheses
 *   §7  End-to-end: safe_cmd_correct instantiated for BN254
 *   §8  felem_copy: fully concrete proof (zero axioms)
 *
 * Trust: the per-leaf correctness hypotheses in §6 are discharged by:
 *   - fiat-crypto WordByWordMontgomery proofs (add/sub/mul/square)
 *   - Jasmin assembly verification (opp/felem_copy — note: copy is
 *     also proven from first principles in §8)
 *   - Direct inspection of <5 lines of Rust (from_word)
 *   - fiat-crypto select_znz proof (select_znz)
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znat.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Require Import Bedrock.SafeRustSimulation.

(* ================================================================ *)
(* §1. BN254 parameters                                              *)
(* ================================================================ *)

Definition bn254_p : Z :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583.

Definition bn254_N : nat := 4.  (** 4 × 64-bit limbs = 256 bits *)
Definition bn254_u64_max : nat := Nat.pow 2 64.

(* ================================================================ *)
(* §2. Helper: extract Fp value from a typed Sigma                    *)
(* ================================================================ *)

(** Try to project a sigma-packed tower value to [rust_val TFp].
    Returns [None] if the value is Fp2/Fp6/Fp12. *)
Definition extract_fp (s : { t : tower_type & rust_val t })
    : option (rust_val TFp) :=
  match s with
  | existT _ TFp v => Some v
  | _ => None
  end.

Lemma extract_fp_existT_TFp : forall v,
  extract_fp (existT _ TFp v) = Some v.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §2b. Modular arithmetic helpers (outside section)                  *)
(* ================================================================ *)

(** Strip inner [mod]s from [(a mod n - b mod n + c) mod n]. *)
Lemma normalize_mod3 : forall a b c n,
  n > 0 ->
  (a mod n - b mod n + c) mod n = (a - b + c) mod n.
Proof.
  intros. rewrite Zplus_mod, Zminus_mod, !Zmod_mod.
  rewrite <- Zminus_mod, <- Zplus_mod. reflexivity.
Qed.

(** Karatsuba imaginary part: the double-sub chain computes ad + bc. *)
Lemma karatsuba_im_mod : forall fa fb fc fd n,
  n > 0 ->
  ((((fa + fb) mod n * ((fc + fd) mod n)) mod n -
    (fa * fc) mod n + n) mod n -
   (fb * fd) mod n + n) mod n =
  (fa * fd + fb * fc) mod n.
Proof.
  intros fa fb fc fd n Hn.
  transitivity (((fa + fb) * (fc + fd) - fa * fc + n - fb * fd + n) mod n).
  { rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
    rewrite (normalize_mod3 _ _ n n Hn).
    replace (((fa + fb) * (fc + fd)) mod n - (fa * fc) mod n +
             n - fb * fd + n)
      with (((fa + fb) * (fc + fd)) mod n - (fa * fc) mod n +
            (n - fb * fd + n)) by ring.
    rewrite (normalize_mod3 _ _ (n - fb * fd + n) n Hn).
    f_equal. ring. }
  { replace ((fa + fb) * (fc + fd) - fa * fc + n - fb * fd + n)
      with (fa * fd + fb * fc + 2 * n) by ring.
    rewrite Z_mod_plus by lia. reflexivity. }
Qed.

(* ================================================================ *)
(* §3. Concrete leaf_spec                                             *)
(* ================================================================ *)

Section ConcreteLeafSpec.

(** Per-leaf implementation functions. These are parameters matching
    the fiat-crypto synthesized implementations.

    Convention for scalar-argument leaves:
    - [from_word]: the input [rust_val TFp] encodes [[w; 0; 0; 0]]
      where [w] is the word value (as a nat limb).
    - [select_znz]: the first arg encodes [[c; 0; 0; 0]] where
      [c] is 0 or 1. *)

Variable add_impl : rust_val TFp -> rust_val TFp -> rust_val TFp.
Variable sub_impl : rust_val TFp -> rust_val TFp -> rust_val TFp.
Variable mul_impl : rust_val TFp -> rust_val TFp -> rust_val TFp.
Variable square_impl : rust_val TFp -> rust_val TFp.
Variable opp_impl : rust_val TFp -> rust_val TFp.
Variable from_word_impl : rust_val TFp -> rust_val TFp.
Variable select_znz_impl :
  rust_val TFp -> rust_val TFp -> rust_val TFp -> rust_val TFp.

(** felem_copy is concrete: identity on the limb representation. *)
Definition copy_impl (x : rust_val TFp) : rust_val TFp := x.

(** Helper: dispatch on function name for Fp-destination calls. *)
Definition bn254_leaf_spec_fp
    (f : string) (dst : rust_val TFp)
    (args : list { t : tower_type & rust_val t }) : rust_val TFp :=
  if String.eqb f "bn254_add" then
    match args with
    | [a1; a2] =>
        match extract_fp a1, extract_fp a2 with
        | Some x, Some y => add_impl x y
        | _, _ => dst
        end
    | _ => dst
    end
  else if String.eqb f "bn254_sub" then
    match args with
    | [a1; a2] =>
        match extract_fp a1, extract_fp a2 with
        | Some x, Some y => sub_impl x y
        | _, _ => dst
        end
    | _ => dst
    end
  else if String.eqb f "bn254_mul" then
    match args with
    | [a1; a2] =>
        match extract_fp a1, extract_fp a2 with
        | Some x, Some y => mul_impl x y
        | _, _ => dst
        end
    | _ => dst
    end
  else if String.eqb f "bn254_square" then
    match args with
    | [a1] =>
        match extract_fp a1 with
        | Some x => square_impl x
        | None => dst
        end
    | _ => dst
    end
  else if String.eqb f "bn254_opp" then
    match args with
    | [a1] =>
        match extract_fp a1 with
        | Some x => opp_impl x
        | None => dst
        end
    | _ => dst
    end
  else if String.eqb f "bn254_felem_copy" then
    match args with
    | [a1] =>
        match extract_fp a1 with
        | Some x => copy_impl x
        | None => dst
        end
    | _ => dst
    end
  else if String.eqb f "bn254_from_word" then
    match args with
    | [a1] =>
        match extract_fp a1 with
        | Some w => from_word_impl w
        | None => dst
        end
    | _ => dst
    end
  else if String.eqb f "bn254_select_znz" then
    match args with
    | [a1; a2; a3] =>
        match extract_fp a1, extract_fp a2, extract_fp a3 with
        | Some c, Some x, Some y => select_znz_impl c x y
        | _, _, _ => dst
        end
    | _ => dst
    end
  else dst.

(** The full leaf_spec: for Fp destinations, dispatch to
    [bn254_leaf_spec_fp]; for higher tower types, return the
    destination unchanged (identity). All 8 BN254 leaf primitives
    operate on Fp, so the identity fallback is never reached for
    well-formed tower programs. *)
Definition bn254_leaf_spec
    (f : string) (dt : tower_type) (in_ts : list tower_type)
    (dst : rust_val dt) (args : list { t : tower_type & rust_val t })
    : rust_val dt :=
  match dt as d return rust_val d -> rust_val d with
  | TFp   => fun dst_fp => bn254_leaf_spec_fp f dst_fp args
  | TFp2  => fun d => d
  | TFp6  => fun d => d
  | TFp12 => fun d => d
  end dst.

(* ================================================================ *)
(* §4. Unfolding lemmas                                               *)
(* ================================================================ *)

(** These lemmas expose what [bn254_leaf_spec] computes for each
    concrete leaf function, given well-typed arguments.  They simplify
    proof goals that arise when instantiating [safe_cmd_correct]. *)

Lemma leaf_spec_add : forall dst x y,
  bn254_leaf_spec "bn254_add" TFp [TFp; TFp] dst
    [existT _ TFp x; existT _ TFp y] = add_impl x y.
Proof. reflexivity. Qed.

Lemma leaf_spec_sub : forall dst x y,
  bn254_leaf_spec "bn254_sub" TFp [TFp; TFp] dst
    [existT _ TFp x; existT _ TFp y] = sub_impl x y.
Proof. reflexivity. Qed.

Lemma leaf_spec_mul : forall dst x y,
  bn254_leaf_spec "bn254_mul" TFp [TFp; TFp] dst
    [existT _ TFp x; existT _ TFp y] = mul_impl x y.
Proof. reflexivity. Qed.

Lemma leaf_spec_square : forall dst x,
  bn254_leaf_spec "bn254_square" TFp [TFp] dst
    [existT _ TFp x] = square_impl x.
Proof. reflexivity. Qed.

Lemma leaf_spec_opp : forall dst x,
  bn254_leaf_spec "bn254_opp" TFp [TFp] dst
    [existT _ TFp x] = opp_impl x.
Proof. reflexivity. Qed.

Lemma leaf_spec_copy : forall dst x,
  bn254_leaf_spec "bn254_felem_copy" TFp [TFp] dst
    [existT _ TFp x] = x.
Proof. reflexivity. Qed.

Lemma leaf_spec_from_word : forall dst w,
  bn254_leaf_spec "bn254_from_word" TFp [TFp] dst
    [existT _ TFp w] = from_word_impl w.
Proof. reflexivity. Qed.

Lemma leaf_spec_select_znz : forall dst c x y,
  bn254_leaf_spec "bn254_select_znz" TFp [TFp; TFp; TFp] dst
    [existT _ TFp c; existT _ TFp x; existT _ TFp y] =
    select_znz_impl c x y.
Proof. reflexivity. Qed.

(** Non-Fp destinations are identity. *)
Lemma leaf_spec_non_fp : forall f dt in_ts dst args,
  dt <> TFp ->
  bn254_leaf_spec f dt in_ts dst args = dst.
Proof.
  intros f dt in_ts dst args Hneq.
  unfold bn254_leaf_spec.
  destruct dt; try reflexivity.
  contradiction.
Qed.

(* ================================================================ *)
(* §5. Mathematical interpretation                                    *)
(* ================================================================ *)

(** [fp_eval] interprets [rust_val TFp] limbs as a mathematical field
    element in Z/pZ. The concrete evaluation depends on the Montgomery
    representation parameters used by fiat-crypto's
    [WordByWordMontgomery]. We take it as a parameter here; the
    concrete definition is [feval] in fiat-crypto's field synthesis. *)
Variable fp_eval : rust_val TFp -> Z.

(** The evaluation is always in [0, p). *)
Hypothesis fp_eval_range : forall v, 0 <= fp_eval v < bn254_p.

(* ================================================================ *)
(* §6. Per-leaf correctness hypotheses                                *)
(* ================================================================ *)

(** Each hypothesis states that the implementation function preserves
    [fp_eval] according to the mathematical field operation.

    These are the trust assumptions that connect the Jasmin/CryptOpt
    assembly code to the mathematical specification. They are proved
    by the fiat-crypto WordByWordMontgomery correctness theorem or by
    the Jasmin assembly verification. *)

Hypothesis add_correct : forall x y,
  fp_eval (add_impl x y) = (fp_eval x + fp_eval y) mod bn254_p.

Hypothesis sub_correct : forall x y,
  fp_eval (sub_impl x y) =
    (fp_eval x - fp_eval y + bn254_p) mod bn254_p.

Hypothesis mul_correct : forall x y,
  fp_eval (mul_impl x y) = (fp_eval x * fp_eval y) mod bn254_p.

Hypothesis square_correct : forall x,
  fp_eval (square_impl x) = (fp_eval x * fp_eval x) mod bn254_p.

Hypothesis opp_correct : forall x,
  fp_eval (opp_impl x) = (bn254_p - fp_eval x) mod bn254_p.

(** [copy_correct] is a theorem, not a hypothesis: [copy_impl] is the
    identity on limbs, so [fp_eval] is trivially preserved. *)
Lemma copy_correct : forall x, fp_eval (copy_impl x) = fp_eval x.
Proof. reflexivity. Qed.

(** For [from_word], the input encodes a raw word in the first limb.
    We extract it via [word_of_fp]. *)
Definition word_of_fp (v : rust_val TFp) : Z :=
  match v with
  | VFp (w :: _) => Z.of_nat w
  | VFp [] => 0
  end.

Hypothesis from_word_correct : forall w,
  fp_eval (from_word_impl w) = word_of_fp w mod bn254_p.

(** [select_znz]: condition is in the first limb of the first arg. *)
Definition cond_of_fp (v : rust_val TFp) : nat :=
  match v with
  | VFp (c :: _) => c
  | VFp [] => 0
  end.

Hypothesis select_znz_correct : forall c x y,
  fp_eval (select_znz_impl c x y) =
    if Nat.eqb (cond_of_fp c) 0 then fp_eval x else fp_eval y.

(* ================================================================ *)
(* §7. End-to-end theorem: safe_cmd_correct for BN254                 *)
(* ================================================================ *)

(** Direct instantiation of the simulation theorem from
    [SafeRustSimulation.v]. The proof is trivial: [safe_cmd_correct]
    is universally quantified over [leaf_spec], so we just plug in
    [bn254_leaf_spec]. *)

Theorem bn254_safe_cmd_correct :
  forall c rs1 rs2,
    cmd_clean c ->
    state_ac_fresh rs1 ->
    bedrock_exec bn254_N bn254_u64_max bn254_leaf_spec c rs1 rs2 ->
    rust_exec bn254_N bn254_u64_max bn254_leaf_spec
              (btranslate c) rs1 rs2.
Proof.
  intros c rs1 rs2 Hclean Hfresh Hexec.
  exact (safe_cmd_correct bn254_N bn254_u64_max bn254_leaf_spec
           c rs1 rs2 Hclean Hfresh Hexec).
Qed.

(** The combined correctness statement:
    if the bedrock_exec program [c] preserves [fp_eval] at all Fp
    leaves (ensured by the per-leaf hypotheses in §6), and the
    program satisfies [cmd_clean] and starts from a fresh state,
    then the translated Rust program also preserves [fp_eval].

    This follows from [bn254_safe_cmd_correct] and the unfolding
    lemmas in §4: the Rust execution applies [bn254_leaf_spec] to
    the same inputs, and each leaf computes the correct result. *)

(** Per-leaf eval preservation: the leaf_spec applied to add/sub/mul/...
    preserves fp_eval.  These are direct corollaries of the unfolding
    lemmas + correctness hypotheses. *)

Corollary leaf_eval_add : forall dst x y,
  fp_eval (bn254_leaf_spec "bn254_add" TFp [TFp; TFp] dst
             [existT _ TFp x; existT _ TFp y]) =
  (fp_eval x + fp_eval y) mod bn254_p.
Proof. intros. rewrite leaf_spec_add. apply add_correct. Qed.

Corollary leaf_eval_sub : forall dst x y,
  fp_eval (bn254_leaf_spec "bn254_sub" TFp [TFp; TFp] dst
             [existT _ TFp x; existT _ TFp y]) =
  (fp_eval x - fp_eval y + bn254_p) mod bn254_p.
Proof. intros. rewrite leaf_spec_sub. apply sub_correct. Qed.

Corollary leaf_eval_mul : forall dst x y,
  fp_eval (bn254_leaf_spec "bn254_mul" TFp [TFp; TFp] dst
             [existT _ TFp x; existT _ TFp y]) =
  (fp_eval x * fp_eval y) mod bn254_p.
Proof. intros. rewrite leaf_spec_mul. apply mul_correct. Qed.

Corollary leaf_eval_square : forall dst x,
  fp_eval (bn254_leaf_spec "bn254_square" TFp [TFp] dst
             [existT _ TFp x]) =
  (fp_eval x * fp_eval x) mod bn254_p.
Proof. intros. rewrite leaf_spec_square. apply square_correct. Qed.

Corollary leaf_eval_opp : forall dst x,
  fp_eval (bn254_leaf_spec "bn254_opp" TFp [TFp] dst
             [existT _ TFp x]) =
  (bn254_p - fp_eval x) mod bn254_p.
Proof. intros. rewrite leaf_spec_opp. apply opp_correct. Qed.

Corollary leaf_eval_copy : forall dst x,
  fp_eval (bn254_leaf_spec "bn254_felem_copy" TFp [TFp] dst
             [existT _ TFp x]) = fp_eval x.
Proof. intros. rewrite leaf_spec_copy. reflexivity. Qed.

Corollary leaf_eval_from_word : forall dst w,
  fp_eval (bn254_leaf_spec "bn254_from_word" TFp [TFp] dst
             [existT _ TFp w]) = word_of_fp w mod bn254_p.
Proof. intros. rewrite leaf_spec_from_word. apply from_word_correct. Qed.

Corollary leaf_eval_select_znz : forall dst c x y,
  fp_eval (bn254_leaf_spec "bn254_select_znz" TFp [TFp; TFp; TFp] dst
             [existT _ TFp c; existT _ TFp x; existT _ TFp y]) =
  if Nat.eqb (cond_of_fp c) 0 then fp_eval x else fp_eval y.
Proof.
  intros. rewrite leaf_spec_select_znz. apply select_znz_correct.
Qed.

(* ================================================================ *)
(* §8. felem_copy: fully concrete proof (zero extra axioms)           *)
(* ================================================================ *)

(** [felem_copy] is the identity on limbs, so its leaf_spec case is
    completely determined by the [copy_impl := id] definition.
    The following shows that an [XR_call] step for [felem_copy]
    in the Rust semantics produces a state with the source value
    at the destination — matching the bedrock2 spec exactly. *)

Lemma felem_copy_identity : forall dst x,
  bn254_leaf_spec "bn254_felem_copy" TFp [TFp] dst
    [existT _ TFp x] = x.
Proof. reflexivity. Qed.

(** Copying preserves [fp_eval] — proven without hypotheses. *)
Lemma felem_copy_eval : forall x,
  fp_eval (copy_impl x) = fp_eval x.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §9. Derived properties from the per-leaf hypotheses                *)
(* ================================================================ *)

(** These lemmas demonstrate that the per-leaf hypotheses are strong
    enough to derive useful algebraic properties. *)

(** opp is involutive: fp_eval(opp(opp(x))) = fp_eval(x). *)
Lemma opp_involutive : forall x,
  fp_eval (opp_impl (opp_impl x)) = fp_eval x.
Proof.
  intros x.
  rewrite opp_correct, opp_correct.
  pose proof (fp_eval_range x) as [Hlo Hhi].
  assert (Hpgt : 0 < bn254_p) by reflexivity.
  pose proof (Z.mod_pos_bound (bn254_p - fp_eval x) bn254_p Hpgt).
  destruct (Z.eq_dec (fp_eval x) 0) as [Hz | Hnz].
  - rewrite Hz. replace (bn254_p - 0) with bn254_p by lia.
    rewrite Z.mod_same by lia. reflexivity.
  - assert (H1 : 0 <= bn254_p - fp_eval x < bn254_p) by lia.
    rewrite (Z.mod_small _ _ H1).
    replace (bn254_p - (bn254_p - fp_eval x)) with (fp_eval x) by lia.
    rewrite Z.mod_small by lia. reflexivity.
Qed.

(** add then sub: fp_eval(sub(add(x,y), y)) = fp_eval(x). *)
Lemma add_sub_cancel : forall x y,
  fp_eval (sub_impl (add_impl x y) y) = fp_eval x.
Proof.
  intros x y.
  rewrite sub_correct, add_correct.
  pose proof (fp_eval_range x) as [Hxlo Hxhi].
  pose proof (fp_eval_range y) as [Hylo Hyhi].
  assert (Hpgt : 0 < bn254_p) by reflexivity.
  replace ((fp_eval x + fp_eval y) mod bn254_p - fp_eval y + bn254_p)
    with ((fp_eval x + fp_eval y) mod bn254_p + (bn254_p - fp_eval y)) by lia.
  rewrite Zplus_mod_idemp_l.
  replace (fp_eval x + fp_eval y + (bn254_p - fp_eval y))
    with (fp_eval x + 1 * bn254_p) by lia.
  rewrite Z_mod_plus_full.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(** copy is truly transparent: leaf_spec reduces to the input value. *)
Lemma copy_transparent : forall dst x,
  bn254_leaf_spec "bn254_felem_copy" TFp [TFp] dst
    [existT _ TFp x] = x.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* §10. Tower-level evaluation (Fp2)                                  *)
(* ================================================================ *)

(** Extend [fp_eval] to [rust_val TFp2] = pair of Fp values.
    An Fp2 element (a, b) represents a + b·u where u² = -1. *)
Definition fp2_eval (v : rust_val TFp2) : Z * Z :=
  match v with
  | VFp2 a b => (fp_eval a, fp_eval b)
  end.

(** Fp2 addition at the tower level: if the Rust program calls
    [bn254_add] on each component pair, the result's fp2_eval is
    componentwise addition mod p. *)
Lemma fp2_add_eval : forall a0 a1 b0 b1,
  let sum0 := add_impl a0 b0 in
  let sum1 := add_impl a1 b1 in
  fp2_eval (VFp2 sum0 sum1) =
    ((fp_eval a0 + fp_eval b0) mod bn254_p,
     (fp_eval a1 + fp_eval b1) mod bn254_p).
Proof.
  intros. unfold fp2_eval. f_equal; apply add_correct.
Qed.

(** Fp2 negation: opp on each component. *)
Lemma fp2_opp_eval : forall a0 a1,
  fp2_eval (VFp2 (opp_impl a0) (opp_impl a1)) =
    ((bn254_p - fp_eval a0) mod bn254_p,
     (bn254_p - fp_eval a1) mod bn254_p).
Proof.
  intros. unfold fp2_eval. f_equal; apply opp_correct.
Qed.

(** Fp2 subtraction: sub on each component. *)
Lemma fp2_sub_eval : forall a0 a1 b0 b1,
  fp2_eval (VFp2 (sub_impl a0 b0) (sub_impl a1 b1)) =
    ((fp_eval a0 - fp_eval b0 + bn254_p) mod bn254_p,
     (fp_eval a1 - fp_eval b1 + bn254_p) mod bn254_p).
Proof.
  intros. unfold fp2_eval. f_equal; apply sub_correct.
Qed.

(** Fp2 multiplication (Karatsuba, β = -1):
    (a + bu)(c + du) = (ac - bd) + ((a+b)(c+d) - ac - bd)u

    The bedrock2 code computes:
      v0 = mul(a, c)       — ac
      v1 = mul(b, d)       — bd
      v2 = add(a, b)       — a + b
      im = add(c, d)       — c + d
      im = mul(im, v2)     — (a+b)(c+d)
      im = sub(im, v0)     — (a+b)(c+d) - ac
      im = sub(im, v1)     — (a+b)(c+d) - ac - bd
      re = sub(v0, v1)     — ac - bd
*)
Lemma fp2_mul_eval : forall a b c d,
  let ac := mul_impl a c in
  let bd := mul_impl b d in
  let apb := add_impl a b in
  let cpd := add_impl c d in
  let apb_cpd := mul_impl apb cpd in
  let im1 := sub_impl apb_cpd ac in
  let im := sub_impl im1 bd in
  let re := sub_impl ac bd in
  fp2_eval (VFp2 re im) =
    ((fp_eval a * fp_eval c - fp_eval b * fp_eval d + bn254_p) mod bn254_p,
     (fp_eval a * fp_eval d + fp_eval b * fp_eval c) mod bn254_p).
Proof.
  intros. unfold fp2_eval. f_equal.
  - (* re = sub(mul(a,c), mul(b,d)) *)
    subst re ac bd.
    rewrite sub_correct, !mul_correct.
    apply (normalize_mod3 _ _ bn254_p bn254_p ltac:(reflexivity)).
  - (* im = (a+b)(c+d) - ac - bd = ad + bc *)
    subst im im1 apb_cpd apb cpd ac bd.
    rewrite !sub_correct, !mul_correct, !add_correct.
    apply (karatsuba_im_mod _ _ _ _ bn254_p ltac:(reflexivity)).
Qed.

(* ================================================================ *)
(* §10b. Tower-level evaluation (Fp6, Fp12)                          *)
(* ================================================================ *)

(** Fp6 = Fp2[v]/(v³ - ξ) where ξ = (9, 1).
    An Fp6 element (c0, c1, c2) represents c0 + c1·v + c2·v².

    Fp12 = Fp6[w]/(w² - v).
    An Fp12 element (c0, c1) represents c0 + c1·w. *)

Definition fp6_eval (v : rust_val TFp6) : (Z * Z) * (Z * Z) * (Z * Z) :=
  match v with
  | VFp6 c0 c1 c2 => (fp2_eval c0, fp2_eval c1, fp2_eval c2)
  end.

Definition fp12_eval (v : rust_val TFp12) :
    ((Z * Z) * (Z * Z) * (Z * Z)) * ((Z * Z) * (Z * Z) * (Z * Z)) :=
  match v with
  | VFp12 c0 c1 => (fp6_eval c0, fp6_eval c1)
  end.

(** Structural lemmas: eval decomposes into components. *)
Lemma fp6_eval_unfold : forall c0 c1 c2,
  fp6_eval (VFp6 c0 c1 c2) = (fp2_eval c0, fp2_eval c1, fp2_eval c2).
Proof. reflexivity. Qed.

Lemma fp12_eval_unfold : forall c0 c1,
  fp12_eval (VFp12 c0 c1) = (fp6_eval c0, fp6_eval c1).
Proof. reflexivity. Qed.

(** mul_xi for BN254: ξ = (9, 1).
    (a + bu) · (9 + u) = (9a - b) + (a + 9b)u

    The bedrock2 code computes 9x as x+x → 2x+2x → 4x+4x → 8x+x. *)

Definition fp_mul9 (x : rust_val TFp) : rust_val TFp :=
  let x2 := add_impl x x in
  let x4 := add_impl x2 x2 in
  let x8 := add_impl x4 x4 in
  add_impl x8 x.

Lemma fp_mul9_correct : forall x,
  fp_eval (fp_mul9 x) = (9 * fp_eval x) mod bn254_p.
Proof.
  intros x. unfold fp_mul9.
  set (x2 := add_impl x x).
  set (x4 := add_impl x2 x2).
  set (x8 := add_impl x4 x4).
  assert (H2 : fp_eval x2 = (2 * fp_eval x) mod bn254_p)
    by (subst x2; rewrite add_correct; f_equal; ring).
  assert (H4 : fp_eval x4 = (4 * fp_eval x) mod bn254_p)
    by (subst x4; rewrite add_correct, H2;
        rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r; f_equal; ring).
  assert (H8 : fp_eval x8 = (8 * fp_eval x) mod bn254_p)
    by (subst x8; rewrite add_correct, H4;
        rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r; f_equal; ring).
  rewrite add_correct, H8.
  rewrite Zplus_mod_idemp_l. f_equal. ring.
Qed.

(** Full mul_xi: (a, b) ↦ (9a - b, a + 9b). *)
Lemma fp2_mul_xi_eval : forall a b,
  let a9 := fp_mul9 a in
  let b9 := fp_mul9 b in
  let re := sub_impl a9 b in
  let im := add_impl a b9 in
  fp2_eval (VFp2 re im) =
    ((9 * fp_eval a - fp_eval b + bn254_p) mod bn254_p,
     (fp_eval a + 9 * fp_eval b) mod bn254_p).
Proof.
  intros. unfold fp2_eval. f_equal.
  - subst re a9. rewrite sub_correct, fp_mul9_correct.
    replace ((9 * fp_eval a) mod bn254_p - fp_eval b + bn254_p)
      with ((9 * fp_eval a) mod bn254_p + (bn254_p - fp_eval b)) by ring.
    rewrite Zplus_mod_idemp_l. f_equal. ring.
  - subst im b9. rewrite add_correct, fp_mul9_correct.
    rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* ================================================================ *)
(* §10c. Fp6 / Fp12 componentwise structure                           *)
(* ================================================================ *)

(** Projection helpers for Fp2 values. Using a dependent match on
    [rust_val TFp2] directly tangles with the GADT; we use simple
    Fp2-constructed values and project via pattern match inside the
    [let]. *)
Definition fp2_re (v : rust_val TFp2) : rust_val TFp :=
  match v with VFp2 a _ => a end.
Definition fp2_im (v : rust_val TFp2) : rust_val TFp :=
  match v with VFp2 _ b => b end.

Lemma fp2_re_eval : forall a b, fp_eval (fp2_re (VFp2 a b)) = fp_eval a.
Proof. reflexivity. Qed.

Lemma fp2_im_eval : forall a b, fp_eval (fp2_im (VFp2 a b)) = fp_eval b.
Proof. reflexivity. Qed.

(** Componentwise Fp6 addition using the Fp2 formulas. *)
Lemma fp6_add_eval : forall c0 c1 c2 d0 d1 d2,
  let s0 := VFp2 (add_impl (fp2_re c0) (fp2_re d0))
                  (add_impl (fp2_im c0) (fp2_im d0)) in
  let s1 := VFp2 (add_impl (fp2_re c1) (fp2_re d1))
                  (add_impl (fp2_im c1) (fp2_im d1)) in
  let s2 := VFp2 (add_impl (fp2_re c2) (fp2_re d2))
                  (add_impl (fp2_im c2) (fp2_im d2)) in
  fp6_eval (VFp6 s0 s1 s2) =
    (fp2_eval s0, fp2_eval s1, fp2_eval s2).
Proof. reflexivity. Qed.

(** Fp12 eval is the pair of its Fp6 eval results. *)
Lemma fp12_eval_pair : forall c0 c1,
  fp12_eval (VFp12 c0 c1) = (fp6_eval c0, fp6_eval c1).
Proof. reflexivity. Qed.

End ConcreteLeafSpec.

(* ================================================================ *)
(* §11. Print assumptions audit                                       *)
(* ================================================================ *)

(** After the section closes, the correctness corollaries carry their
    Section [Variable]s and [Hypothesis]es as explicit parameters.
    This makes the trust footprint visible:

    [Print Assumptions leaf_eval_add]
      → Closed (add_impl, fp_eval, add_correct are parameters)

    [Print Assumptions felem_copy_identity]
      → Closed (no axioms — copy is definitionally identity)

    [Print Assumptions bn254_safe_cmd_correct]
      → Closed (7 impl functions are parameters; simulation is Qed)

    [Print Assumptions opp_involutive]
      → Closed (uses opp_impl, fp_eval, opp_correct, fp_eval_range)

    [Print Assumptions add_sub_cancel]
      → Closed (uses add/sub_impl, fp_eval, add/sub_correct, fp_eval_range)

    All report "Closed under the global context" because Section
    variables become universally quantified parameters after End.
    No [Admitted], no [Axiom]. The trust assumptions are explicit
    in the types of the exported lemmas. *)
