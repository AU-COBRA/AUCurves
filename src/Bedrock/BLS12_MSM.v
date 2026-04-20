(** * Pippenger MSM: Gallina specification and bedrock2 program.

    Multi-scalar multiplication via Pippenger's bucket method.
    The Gallina spec is designed for Rupicola-style compilation:
    it uses [let/n] bindings and calls the same [g1_add]/[g1_double]
    that are already verified as bedrock2 functions.

    Location: AUCurves/src/Bedrock/ (we control this).
    Calls into fiat-crypto (upstream) for bedrock2 Fp primitives
    and the verified ToJasmin/ToSafeRust extractors.

    Verification chain:
      1. This file: Gallina spec + bedrock2 ExprImp program + WP proof.
      2. BLS12_MSM_Extract.v (sibling): ToSafeRust → Rust,
         ToJasmin → Jasmin → x86-64.
      3. The extracted code should be semantically equivalent to the
         hand-written bls12-jasmin-rs/src/msm.rs prototype.
      4. On the mathcomp side, Commitments/theories/MSM_Spec.v has
         msm_pippenger_correct (Qed) — connected to this Gallina spec
         via the Stdlib↔mathcomp WeierstrassBridge already used for KZG.

    File organization:
      - Part 1 (Gallina spec): pure Stdlib, no bedrock2 dependency.
        This is what the WP proof will target and what the extracted
        code is proved equivalent to.
      - Part 2 (bedrock2 program): imports bedrock2 Syntax/Semantics.
        Currently a scaffold; WP proof is the blocking TODO.
*)

(* =================================================================== *)
(** * Part 1: Gallina specification                                     *)
(* =================================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Section PippengerGallinaSpec.

  (** Abstract G1 point type and operations.  At instantiation these
      become Jacobian coordinates over F p with the verified group law
      from BLS12_G1.v. *)
  Context (G1 : Type).
  Context (g1_identity : G1).
  Context (g1_add_spec : G1 -> G1 -> G1).
  Context (g1_double_spec : G1 -> G1).

  (** Extract the w-th c-bit window from a 256-bit scalar (as 4 u64 limbs). *)
  Definition get_window (scalar : list Z) (w c : nat) : Z :=
    let bit_offset := (w * c)%nat in
    let limb := (bit_offset / 64)%nat in
    let shift := (bit_offset mod 64)%nat in
    let mask := Z.ones (Z.of_nat c) in
    let val := match nth_error scalar limb with
               | Some v => Z.shiftr v (Z.of_nat shift)
               | None => 0
               end in
    let val' := if Nat.ltb 64 (shift + c) then
                  match nth_error scalar (limb + 1) with
                  | Some v2 => Z.lor val (Z.shiftl v2 (Z.of_nat (64 - shift)))
                  | None => val
                  end
                else val in
    Z.land val' mask.

  (** Reduce buckets via running sum.
      bucket[i] holds points whose window value is (i+1).
      Result = Σ_{i=0}^{num_buckets-1} (i+1) * bucket[i]
             = running-sum accumulation. *)
  Definition reduce_buckets (buckets : list G1) : G1 :=
    let fix go (bs : list G1) (running acc : G1) :=
      match bs with
      | [] => acc
      | b :: rest =>
        let running' := g1_add_spec running b in
        let acc' := g1_add_spec acc running' in
        go rest running' acc'
      end
    in go (rev buckets) g1_identity g1_identity.

  (** Process one window: accumulate points into buckets, then reduce. *)
  Definition process_window (scalars : list (list Z)) (points : list G1)
    (w c : nat) (num_buckets : nat) : G1 :=
    let buckets_init := repeat g1_identity num_buckets in
    let buckets := fold_left
      (fun bkts '(s, p) =>
        let idx := Z.to_nat (get_window s w c) in
        if (idx =? 0)%nat then bkts
        else
          let old := nth (idx - 1) bkts g1_identity in
          let new_ := g1_add_spec old p in
          firstn (idx - 1) bkts ++ [new_] ++ skipn idx bkts)
      (combine scalars points)
      buckets_init in
    reduce_buckets buckets.

  (** Full Pippenger MSM. *)
  Definition msm_pippenger (c : nat) (num_windows : nat)
    (scalars : list (list Z)) (points : list G1) : G1 :=
    let num_buckets := (Nat.pow 2 c - 1)%nat in
    let fix go (w : nat) (acc : G1) :=
      match w with
      | O => acc
      | S w' =>
        let acc' := Nat.iter c g1_double_spec acc in
        let win := process_window scalars points w' c num_buckets in
        go w' (g1_add_spec acc' win)
      end
    in
    let top_window := process_window scalars points (num_windows - 1)%nat c num_buckets in
    go (num_windows - 1)%nat top_window.

End PippengerGallinaSpec.

(* =================================================================== *)
(** * Part 2: bedrock2 ExprImp program (M1, per MSM_M0_DESIGN.md).       *)
(*                                                                      *)
(*    Signature: msm_bls12(outx, outy, outz,                            *)
(*                         scalars, pointsx, pointsy, pointsz, n)       *)
(*      out{x,y,z}    three parallel FElems for the Jacobian output.    *)
(*      scalars       pointer to n × 32 bytes (4 LE u64 limbs each).    *)
(*      points{x,y,z} three parallel n × felem arrays of input points.  *)
(*      n             number of scalar/point pairs.                     *)
(*                                                                      *)
(*    All literal numbers in bedrock_expr position are written as       *)
(*    [$N] rather than bare [N], since bare numeric literals fail to    *)
(*    parse at some end-of-expression positions in custom entries.      *)
(* =================================================================== *)

Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.

Local Notation function_t :=
  (String.string *
   (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section PippengerBedrock2.
  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {mem : map.map word Byte.byte}.
  Context {locals : map.map String.string word}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  Context (curve_add_name    : String.string)
          (curve_double_name : String.string)
          (store_zero        : String.string).

  Let c            : Z := 9.
  Let num_buckets  : Z := 2 ^ c - 1.                  (* = 511 *)
  Let num_windows  : Z := (255 + c - 1) / c.          (* = 29 *)
  Let scalar_bytes : Z := 32.
  Let bucket_bytes : Z := num_buckets * felem_size_in_bytes.

  Definition msm_bls12 : function_t :=
    ("msm_bls12",
     (["outx"; "outy"; "outz";
       "scalars";
       "pointsx"; "pointsy"; "pointsz";
       "n"],
      []:list String.string,
      bedrock_func_body:(
        stackalloc bucket_bytes            as buckets_x;
        stackalloc bucket_bytes            as buckets_y;
        stackalloc bucket_bytes            as buckets_z;
        stackalloc felem_size_in_bytes     as runx;
        stackalloc felem_size_in_bytes     as runy;
        stackalloc felem_size_in_bytes     as runz;
        stackalloc felem_size_in_bytes     as wsx;
        stackalloc felem_size_in_bytes     as wsy;
        stackalloc felem_size_in_bytes     as wsz;

        coq:(cmd.call [] store_zero
               [expr.var "outx"; expr.var "outy"; expr.var "outz"]);

        w = coq:(num_windows);
        while (w) {
          w = (w - $1);

          (* Double the accumulator c times. *)
          i = coq:(c);
          while (i) {
            i = (i - $1);
            coq:(cmd.call [] curve_double_name
                   [expr.var "outx"; expr.var "outy"; expr.var "outz";
                    expr.var "outx"; expr.var "outy"; expr.var "outz"])
          };

          (* Clear the bucket arrays. *)
          i = coq:(num_buckets);
          while (i) {
            i = (i - $1);
            bpx = (buckets_x + i * coq:(felem_size_in_bytes));
            bpy = (buckets_y + i * coq:(felem_size_in_bytes));
            bpz = (buckets_z + i * coq:(felem_size_in_bytes));
            coq:(cmd.call [] store_zero
                   [expr.var "bpx"; expr.var "bpy"; expr.var "bpz"])
          };

          (* Distribute each (scalar, point) into its bucket. *)
          i = n;
          while (i) {
            i = (i - $1);
            bit_offset = (w * coq:(c));
            limb       = (bit_offset >> $6);
            shift      = (bit_offset & $63);
            mask       = (($1 << coq:(c)) - $1);
            scalar_ptr = (scalars + i * coq:(scalar_bytes));
            (* Precompute load offsets into named vars so ToRustString's
               [rust_ptr_varlit] (which only handles lit/var) emits a
               well-formed pointer-add rather than "()". *)
            load_off1 = (limb * $8);
            load_addr1 = (scalar_ptr + load_off1);
            val        = (load(load_addr1) >> shift);
            if ($64 < (shift + coq:(c))) {
              if (limb < $3) {
                load_off2 = ((limb + $1) * $8);
                load_addr2 = (scalar_ptr + load_off2);
                val = (val |
                       (load(load_addr2) << ($64 - shift)))
              }
            };
            idx = (val & mask);

            if (idx) {
              bucket_index = (idx - $1);
              bpx = (buckets_x + bucket_index * coq:(felem_size_in_bytes));
              bpy = (buckets_y + bucket_index * coq:(felem_size_in_bytes));
              bpz = (buckets_z + bucket_index * coq:(felem_size_in_bytes));
              ppx = (pointsx  + i * coq:(felem_size_in_bytes));
              ppy = (pointsy  + i * coq:(felem_size_in_bytes));
              ppz = (pointsz  + i * coq:(felem_size_in_bytes));
              coq:(cmd.call [] curve_add_name
                     [expr.var "bpx"; expr.var "ppx";
                      expr.var "bpy"; expr.var "ppy";
                      expr.var "bpz"; expr.var "ppz";
                      expr.var "bpx"; expr.var "bpy"; expr.var "bpz"])
            }
          };

          (* Running-sum reduction. *)
          coq:(cmd.call [] store_zero
                 [expr.var "runx"; expr.var "runy"; expr.var "runz"]);
          coq:(cmd.call [] store_zero
                 [expr.var "wsx";  expr.var "wsy";  expr.var "wsz"]);

          i = coq:(num_buckets);
          while (i) {
            i = (i - $1);
            bpx = (buckets_x + i * coq:(felem_size_in_bytes));
            bpy = (buckets_y + i * coq:(felem_size_in_bytes));
            bpz = (buckets_z + i * coq:(felem_size_in_bytes));
            coq:(cmd.call [] curve_add_name
                   [expr.var "runx"; expr.var "bpx";
                    expr.var "runy"; expr.var "bpy";
                    expr.var "runz"; expr.var "bpz";
                    expr.var "runx"; expr.var "runy"; expr.var "runz"]);
            coq:(cmd.call [] curve_add_name
                   [expr.var "wsx"; expr.var "runx";
                    expr.var "wsy"; expr.var "runy";
                    expr.var "wsz"; expr.var "runz";
                    expr.var "wsx"; expr.var "wsy"; expr.var "wsz"])
          };

          coq:(cmd.call [] curve_add_name
                 [expr.var "outx"; expr.var "wsx";
                  expr.var "outy"; expr.var "wsy";
                  expr.var "outz"; expr.var "wsz";
                  expr.var "outx"; expr.var "outy"; expr.var "outz"])
        }
      ))).

  Lemma msm_bls12_welltyped : program_logic_goal_for_function! msm_bls12.
  Proof. exact I. Qed.

End PippengerBedrock2.

(* =================================================================== *)
(** * Part 3: spec + WP theorem skeleton (M2 — proof Admitted).         *)
(*                                                                      *)
(*    What this section gives you:                                      *)
(*    - [ScalarsArray p scalars]  — sep predicate for n × 32-byte       *)
(*      little-endian 4-limb scalars.                                   *)
(*    - [G1Array3 bx by bz points] — sep for three parallel FElem      *)
(*      arrays of length n.                                             *)
(*    - [spec_of_msm_bls12] — the fnspec tying [msm_bls12] to           *)
(*      [msm_pippenger] from Part 1.                                    *)
(*    - Four [Gallina] loop invariants (as comments + predicates).      *)
(*    - [msm_bls12_ok] stated and [Admitted].                           *)
(*                                                                      *)
(*    The proof itself is a ~2–3K LoC effort (MSM_PLAN.md § M2).        *)
(*    The relevant tactics / lemmas to cite are already available:      *)
(*    - [bedrock2.Loops.while_localsmap] — 4 applications, one per     *)
(*      nested loop.                                                    *)
(*    - [IteratedSepPoints.PointArray_split_at/update_at] — for the     *)
(*      single-cell mutation in the distribution loop.                  *)
(*    - [IteratedSepPoints.reduce_buckets_eq_scaled_sum] — for the      *)
(*      reduction-loop invariant closure.                               *)
(*    - [BLS12_G1.v]'s [spec_of_curve_add] + [store_zero] specs.        *)
(* =================================================================== *)

Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Array.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Bedrock.IteratedSepPoints.
Require Import Bedrock.FrameLocalsWP.
Require bedrock2.Loops.

Section PippengerSpec.
  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {mem : map.map word Byte.byte}.
  Context {locals : map.map String.string word}.
  Context {ext_spec : bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok (field_representation:=field_representation)}.

  Context (curve_add_name    : String.string)
          (curve_double_name : String.string)
          (store_zero_name   : String.string).

  Local Notation F := (F M_pos).
  Local Notation G1_F := (F * F * F)%type.

  (** Must match the [Let]s in [PippengerBedrock2] above. *)
  Let c            : Z := 9.
  Let num_buckets  : Z := 2 ^ c - 1.
  Let num_windows  : Z := (255 + c - 1) / c.

  (** n = 4 limbs per scalar, each u64. *)
  Let scalar_limbs : nat := 4.

  (** A single 256-bit scalar at address [p], encoded LE as [scalar_limbs]
      words of [Memory.bytes_per_word width] bytes.  [ws] is the list of
      limb values. *)
  Definition ScalarAt (p : word) (ws : list word) : mem -> Prop :=
    Bignum.Bignum scalar_limbs p ws.

  (** [n] scalars at offsets 0, 32, 64, ... from [base]. *)
  Definition ScalarsArray (base : word) (scalars : list (list word))
    : mem -> Prop :=
    array ScalarAt (word.of_Z 32) base scalars.

  (** Three parallel F-valued arrays encoding [n] Jacobian points.
      [FElem None] from [CompilationAbstract] takes an [F] (field value),
      not a [felem] (subset type).  This matches the existing callee
      specs ([spec_of_curve_add], [spec_of_store_zero]). *)
  Definition G1Array3 (bx bpy bpz : word)
                      (xs ys zs : list F)
    : mem -> Prop :=
    (array (FElem None) (word.of_Z felem_size_in_bytes) bx  xs *
     array (FElem None) (word.of_Z felem_size_in_bytes) bpy ys *
     array (FElem None) (word.of_Z felem_size_in_bytes) bpz zs)%sep.

  (** Abstract Gallina group operations at the [G1_F] level, supplied
      by the caller through [spec_of_curve_add] / [spec_of_curve_double]
      (these are the postconditions of the respective fnspecs). *)
  Context (g1_add_spec    : G1_F -> G1_F -> G1_F)
          (g1_double_spec : G1_F -> G1_F)
          (g1_identity    : G1_F).

  Hypothesis g1_add_assoc      : forall a b c, g1_add_spec (g1_add_spec a b) c
                                             = g1_add_spec a (g1_add_spec b c).
  Hypothesis g1_add_comm       : forall a b, g1_add_spec a b = g1_add_spec b a.
  Hypothesis g1_add_identity_l : forall a, g1_add_spec g1_identity a = a.
  Hypothesis g1_double_identity : g1_double_spec g1_identity = g1_identity.

  (** Bridge: [reduce_buckets] (Part 1) equals [scaled_sum]
      (IteratedSepPoints).  Ported inline here to avoid the dependency
      cycle [IteratedSepPoints] → [BLS12_MSM]. *)
  Lemma reduce_buckets_as_fold (bs : list G1_F) :
    reduce_buckets G1_F g1_identity g1_add_spec bs
    = snd (fold_left
             (fun p b =>
                let r' := g1_add_spec (fst p) b in
                (r', g1_add_spec (snd p) r'))
             (rev bs)
             (g1_identity, g1_identity)).
  Proof.
    unfold reduce_buckets.
    assert (Hgo: forall rs r a,
      (fix go (bs0 : list G1_F) (running acc : G1_F) {struct bs0} : G1_F :=
         match bs0 with
         | [] => acc
         | b :: rest =>
             let running' := g1_add_spec running b in
             let acc' := g1_add_spec acc running' in
             go rest running' acc'
         end) rs r a
      = snd (fold_left (fun p b =>
                          let r' := g1_add_spec (fst p) b in
                          (r', g1_add_spec (snd p) r'))
                       rs (r, a))).
    { intros rs. induction rs as [|b rest IH]; intros r a.
      - reflexivity.
      - simpl. apply IH. }
    apply Hgo.
  Qed.

  Theorem reduce_buckets_eq_scaled_sum (bs : list G1_F) :
    reduce_buckets G1_F g1_identity g1_add_spec bs
    = scaled_sum G1_F g1_identity g1_add_spec bs.
  Proof.
    rewrite reduce_buckets_as_fold.
    rewrite fold_left_rev_right_rs.
    rewrite running_fold_snd; auto.
  Qed.

  (** Jacobian triple of three [F] values. *)
  Definition mk_point (x y z : F) : G1_F := (x, y, z).

  (** [scalars]/[points] zipped and ready to be fed to [msm_pippenger].
      Uses an explicit 3-way [combine] rather than nested [combine] to
      avoid a scope-resolution glitch in the pretyper. *)
  Fixpoint points_of (px py pz : list F) : list G1_F :=
    match px, py, pz with
    | x :: xs, y :: ys, z :: zs => mk_point x y z :: points_of xs ys zs
    | _, _, _ => nil
    end.

  Definition scalar_to_Z (ws : list word) : list Z :=
    List.map (@word.unsigned _ word) ws.

  Definition scalars_to_Z (scalars : list (list word)) : list (list Z) :=
    List.map scalar_to_Z scalars.

  Definition msm_spec_output
             (scalars : list (list word)) (points : list G1_F) : G1_F :=
    msm_pippenger G1_F g1_identity g1_add_spec g1_double_spec
      (Z.to_nat c) (Z.to_nat num_windows)
      (scalars_to_Z scalars)
      points.

  (* =================================================================== *)
  (** ** [spec_of_msm_bls12]                                              *)
  (* =================================================================== *)

  Instance spec_of_msm_bls12 : spec_of "msm_bls12" :=
    fnspec! "msm_bls12"
      (outx outy outz scalars_p ppx ppy ppz n_w : word)
      / (outx0 outy0 outz0 : F)
        (scalars : list (list word))
        (px py pz : list F)
        (R : mem -> Prop),
      { requires tr mem :=
          word.unsigned n_w = Z.of_nat (length scalars) /\
          length scalars = length px /\
          length px = length py /\
          length py = length pz /\
          (FElem None outx outx0
           * FElem None outy outy0
           * FElem None outz outz0
           * ScalarsArray scalars_p scalars
           * G1Array3 ppx ppy ppz px py pz
           * R)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists (outx_f outy_f outz_f : F),
            mk_point outx_f outy_f outz_f
            = msm_spec_output scalars (points_of px py pz)
            /\ (FElem (Some tight_bounds) outx outx_f
                * FElem (Some tight_bounds) outy outy_f
                * FElem (Some tight_bounds) outz outz_f
                * ScalarsArray scalars_p scalars
                * G1Array3 ppx ppy ppz px py pz
                * R)%sep mem' }.

  (* =================================================================== *)
  (** ** Loop invariants — concrete Gallina predicates.                   *)
  (*                                                                      *)
  (*    Each loop has (a) a Gallina invariant over the abstract [G1_F]    *)
  (*    state, and (b) a sep-logic predicate tying the concrete memory    *)
  (*    to that abstract state.  The WP proof discharges each iteration   *)
  (*    by matching the callee spec against the Gallina update.           *)
  (* =================================================================== *)

  (** Partial MSM sum over the top [num_windows - w] windows.  This is
      the Gallina value of [out] at the start of outer-loop iteration [w].
      Defined by unrolling [msm_pippenger]'s internal fix. *)
  Fixpoint partial_msm_from (w : nat) (acc : G1_F)
           (ss : list (list Z)) (ps : list G1_F) : G1_F :=
    match w with
    | O   => acc
    | S k =>
      let acc' := Nat.iter (Z.to_nat c) g1_double_spec acc in
      let win  := process_window G1_F g1_identity g1_add_spec
                    ss ps k (Z.to_nat c)
                    (Nat.pow 2 (Z.to_nat c) - 1) in
      partial_msm_from k (g1_add_spec acc' win) ss ps
    end.

  (** Running "plain sum" of a prefix of a bucket list, used in the
      bucket-distribution loop. *)
  Definition bucket_sum_prefix (bs : list G1_F) (i : nat) : G1_F :=
    plain_sum G1_F g1_identity g1_add_spec (firstn i bs).

  (** Outer window loop invariant: after the header decrement, local [w]
      is the window index we're about to process, and [out] holds the
      partial MSM for windows [[w+1, num_windows)]. *)
  Definition outer_inv (w : Z) (out : G1_F)
             (ss : list (list Z)) (ps : list G1_F) : Prop :=
    out = partial_msm_from (Z.to_nat num_windows - Z.to_nat w - 1)%nat
                           g1_identity ss ps.

  (** Bucket-clear loop invariant: buckets at indices [[i, num_buckets)]
      are still arbitrary; buckets at [[0, i)] are [g1_identity]. *)
  Definition clear_inv (i : Z) (bs : list G1_F) : Prop :=
    (i <= num_buckets) /\
    Z.of_nat (length bs) = num_buckets /\
    forall k, (Z.to_nat i <= k < Z.to_nat num_buckets)%nat ->
              nth k bs g1_identity = g1_identity.

  (** Distribution loop invariant: buckets after adding points [[i, n)]
      into their respective buckets for the current window [w]. *)
  Definition distribute_inv (w i : Z) (bs : list G1_F)
             (ss : list (list Z)) (ps : list G1_F) : Prop :=
    Z.of_nat (length bs) = num_buckets /\
    (* Each bucket [k] contains the sum of points [j] with
       [i <= j < length ps] whose window-[w] digit equals [k+1]. *)
    forall k, (k < Z.to_nat num_buckets)%nat ->
      nth k bs g1_identity =
      fold_left g1_add_spec
        (List.map snd
           (List.filter (fun sp : list Z * G1_F =>
                           Nat.eqb (Z.to_nat (get_window (fst sp) (Z.to_nat w) (Z.to_nat c)))
                                   (S k))
                        (skipn (Z.to_nat i) (List.combine ss ps))))
        g1_identity.

  (** Running-sum reduction loop invariant: at iteration [j] (about to
      process bucket at index [j]), [running] equals the plain sum of
      buckets [[j+1, num_buckets)], and [ws] equals the scaled sum of
      the same suffix with coefficients starting at 1. *)
  Definition reduce_inv (j : Z) (running ws : G1_F) (bs : list G1_F) : Prop :=
    Z.of_nat (length bs) = num_buckets /\
    running = plain_sum G1_F g1_identity g1_add_spec
                (skipn (Z.to_nat (j + 1)) bs) /\
    ws = scaled_sum G1_F g1_identity g1_add_spec
                (skipn (Z.to_nat (j + 1)) bs).

  (** At loop exit ([j = 0] after the decrement), the scaled-sum of the
      entire bucket list equals [reduce_buckets] — this is the bridge
      from the loop's concrete output back to the Gallina spec. *)
  Lemma reduce_inv_at_exit (running ws : G1_F) (bs : list G1_F) :
    Z.of_nat (length bs) = num_buckets ->
    running = plain_sum G1_F g1_identity g1_add_spec bs ->
    ws      = scaled_sum G1_F g1_identity g1_add_spec bs ->
    ws = reduce_buckets G1_F g1_identity g1_add_spec bs.
  Proof.
    intros _ _ ->.
    symmetry.
    apply reduce_buckets_eq_scaled_sum; assumption.
  Qed.

  (* =================================================================== *)
  (** ** Pure-Gallina preservation lemmas for each sub-loop.              *)
  (*                                                                      *)
  (*    These lemmas discharge the "Gallina side" of each WP obligation,  *)
  (*    leaving only (a) the bedrock2 separation-logic bookkeeping and    *)
  (*    (b) the callee-spec instantiation for the WP proof itself.        *)
  (* =================================================================== *)

  (** ---- clear_inv ---- *)

  Lemma clear_inv_init bs0 :
    Z.of_nat (length bs0) = num_buckets ->
    clear_inv num_buckets bs0.
  Proof.
    intros Hlen.
    unfold clear_inv. split; [Lia.lia|]. split; [exact Hlen|].
    intros k Hk. Lia.lia.
  Qed.

  Lemma clear_inv_final bs :
    clear_inv 0 bs ->
    Z.of_nat (length bs) = num_buckets /\
    forall k, (k < Z.to_nat num_buckets)%nat ->
              nth k bs g1_identity = g1_identity.
  Proof.
    unfold clear_inv. intros (_ & Hlen & H).
    split; [exact Hlen|].
    intros k Hk. apply H. Lia.lia.
  Qed.

  Lemma clear_inv_step (i : Z) (bs : list G1_F) :
    0 < i <= num_buckets ->
    clear_inv i bs ->
    clear_inv (i - 1)
      (firstn (Z.to_nat (i - 1)) bs
       ++ g1_identity
       :: skipn (Z.to_nat i) bs).
  Proof.
    intros Hi (Hle & Hlen & Hall).
    assert (Hi_nat: (Z.to_nat (i - 1) < length bs)%nat).
    { rewrite <- Nat2Z.id with (n := length bs).
      apply Z2Nat.inj_lt; Lia.lia. }
    unfold clear_inv. split; [Lia.lia|]. split.
    { rewrite length_app, length_cons, length_firstn, length_skipn.
      rewrite Nat.min_l by Lia.lia.
      assert (Z.to_nat i = S (Z.to_nat (i - 1))) as -> by Lia.lia.
      Lia.lia. }
    intros k Hk.
    destruct (Nat.eq_dec k (Z.to_nat (i - 1))) as [->|Hne].
    - rewrite app_nth2 by (rewrite length_firstn, Nat.min_l by Lia.lia; Lia.lia).
      rewrite length_firstn, Nat.min_l by Lia.lia.
      replace (Z.to_nat (i - 1) - Z.to_nat (i - 1))%nat with 0%nat by Lia.lia.
      reflexivity.
    - destruct (Nat.lt_ge_cases k (Z.to_nat (i - 1))) as [Hlt|Hge].
      + rewrite app_nth1 by (rewrite length_firstn, Nat.min_l by Lia.lia; Lia.lia).
        rewrite nth_firstn; [|exact Hlt].
        apply Hall. Lia.lia.
      + rewrite app_nth2 by (rewrite length_firstn, Nat.min_l by Lia.lia; Lia.lia).
        rewrite length_firstn, Nat.min_l by Lia.lia.
        cbn [nth].
        destruct (k - Z.to_nat (i - 1))%nat as [|d] eqn:Ed; [Lia.lia|].
        rewrite nth_skipn.
        apply Hall.
        split; [|Lia.lia].
        assert (Z.to_nat i + d = k)%nat by Lia.lia. Lia.lia.
  Qed.

  (** ---- double-shift sub-loop ---- *)

  (** After running [Nat.iter k g1_double_spec out_entry], [i] countdown
      decrementing from [c] to [0]: the accumulator equals iterated
      doubling of the entry value by [c - i] steps. *)
  Lemma double_shift_step k (out : G1_F) :
    g1_double_spec (Nat.iter k g1_double_spec out)
    = Nat.iter (S k) g1_double_spec out.
  Proof. reflexivity. Qed.

  (** ---- reduce_inv ---- *)

  Lemma reduce_inv_entry bs :
    Z.of_nat (length bs) = num_buckets ->
    reduce_inv (num_buckets - 1) g1_identity g1_identity bs.
  Proof.
    intros Hlen.
    unfold reduce_inv.
    assert (Heq: (Z.to_nat (num_buckets - 1 + 1) = length bs)%nat) by Lia.lia.
    split; [exact Hlen|].
    split; rewrite Heq, skipn_all; reflexivity.
  Qed.

  Lemma reduce_inv_exit (running ws : G1_F) (bs : list G1_F) :
    reduce_inv (-1) running ws bs ->
    Z.of_nat (length bs) = num_buckets /\
    running = plain_sum G1_F g1_identity g1_add_spec bs /\
    ws      = scaled_sum G1_F g1_identity g1_add_spec bs.
  Proof.
    unfold reduce_inv. intros (Hlen & Hr & Hw).
    assert (Hj: Z.to_nat (-1 + 1) = 0%nat) by reflexivity.
    rewrite Hj in Hr, Hw. rewrite skipn_O in Hr, Hw.
    split; [exact Hlen|]. split; [exact Hr|exact Hw].
  Qed.

  (** Helper: splitting [skipn j bs] as head [bs[j]] plus [skipn (j+1) bs]. *)
  Lemma skipn_S_eq (j : nat) (bs : list G1_F) :
    (j < length bs)%nat ->
    skipn j bs = nth j bs g1_identity :: skipn (S j) bs.
  Proof.
    revert j. induction bs as [|x xs IH]; intros j Hj; [cbn in Hj; Lia.lia|].
    destruct j as [|j']; [reflexivity|].
    cbn. apply IH. cbn in Hj. Lia.lia.
  Qed.

  (** Key algebraic identity: decrementing [j] by 1 and updating
      [running]/[ws] with the bucket at index [j] preserves the
      invariant. *)
  Lemma reduce_inv_step (j : Z) (running ws : G1_F) (bs : list G1_F) :
    0 <= j < num_buckets ->
    reduce_inv j running ws bs ->
    let b := nth (Z.to_nat j) bs g1_identity in
    let running' := g1_add_spec running b in
    let ws'      := g1_add_spec ws running' in
    reduce_inv (j - 1) running' ws' bs.
  Proof.
    intros Hj (Hlen & Hr & Hw).
    unfold reduce_inv. split; [exact Hlen|].
    assert (HjN: (Z.to_nat j < length bs)%nat) by Lia.lia.
    replace (Z.to_nat (j - 1 + 1)) with (Z.to_nat j) by Lia.lia.
    replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) in Hr, Hw by Lia.lia.
    rewrite (skipn_S_eq (Z.to_nat j) bs HjN).
    cbn [plain_sum scaled_sum scaled_sum_from nat_scalar_mul].
    set (b := nth (Z.to_nat j) bs g1_identity).
    set (tl := skipn (S (Z.to_nat j)) bs) in *.
    set (ps := plain_sum G1_F g1_identity g1_add_spec tl) in *.
    set (ss := scaled_sum G1_F g1_identity g1_add_spec tl) in *.
    rewrite Hr, Hw. split.
    - (* running' = op b (plain_sum (b :: tl)) — by comm. *)
      cbn. apply g1_add_comm.
    - (* ws' = scaled_sum (b :: tl) = op (op b 0) (scaled_sum_from 2 tl).
         Under op_zero_r and scaled_sum_from_S (IteratedSepPoints, Qed), we get
         scaled_sum_from 2 tl = op ps ss, so RHS = op b (op ps ss).
         LHS = op ws (op running b) = op ss (op (op ps b)).
         Both are b + ps + ss up to comm/assoc. *)
      unfold scaled_sum. cbn [scaled_sum_from].
      rewrite (op_zero_r G1_F g1_identity g1_add_spec
                 g1_add_comm g1_add_identity_l).
      rewrite (scaled_sum_from_S G1_F g1_identity g1_add_spec
                 g1_add_assoc g1_add_comm g1_add_identity_l 1 tl).
      fold ps. fold ss.
      (* Goal: op ss (op ps b) = op b (op ps ss). *)
      rewrite (g1_add_comm ps b).
      rewrite <- g1_add_assoc.
      rewrite (g1_add_comm ss b).
      rewrite g1_add_assoc.
      rewrite (g1_add_comm ss ps).
      reflexivity.
  Qed.

  (** ---- distribute_inv ---- *)

  Lemma distribute_inv_init (w : Z) bs (ss : list (list Z))
        (ps : list G1_F) :
    Z.of_nat (length bs) = num_buckets ->
    length ss = length ps ->
    (forall k, (k < Z.to_nat num_buckets)%nat ->
               nth k bs g1_identity = g1_identity) ->
    distribute_inv w (Z.of_nat (length ps)) bs ss ps.
  Proof.
    intros Hlen Hlenss Hall.
    unfold distribute_inv. split; [exact Hlen|].
    intros k Hk.
    rewrite Hall by exact Hk.
    rewrite skipn_all2.
    - reflexivity.
    - rewrite length_combine. rewrite Nat2Z.id. Lia.lia.
  Qed.

  (** ---- partial_msm_from — collapse at exit ---- *)

  Lemma partial_msm_from_zero acc ss ps :
    partial_msm_from 0 acc ss ps = acc.
  Proof. reflexivity. Qed.

  (** Doubling the identity repeatedly stays at identity. *)
  Lemma iter_double_identity n :
    Nat.iter n g1_double_spec g1_identity = g1_identity.
  Proof.
    induction n as [|n IH]; [reflexivity|].
    change (Nat.iter (S n) g1_double_spec g1_identity)
      with (g1_double_spec (Nat.iter n g1_double_spec g1_identity)).
    rewrite IH. exact g1_double_identity.
  Qed.

  (** The full MSM equals [partial_msm_from] starting at the top
      window with [acc = identity].  This is the shape the outer-loop
      invariant reduces to at [w = 0]. *)
  Lemma msm_pippenger_as_partial_msm_from ss ps :
    (0 < Z.to_nat num_windows)%nat ->
    msm_spec_output ss ps
    = partial_msm_from (Z.to_nat num_windows) g1_identity
        (scalars_to_Z ss) ps.
  Proof.
    intros HNW.
    unfold msm_spec_output, msm_pippenger.
    (* Generalize [go]: prove [go k acc = partial_msm_from k acc] for any k, acc. *)
    assert (go_eq: forall k acc,
      (fix go (w : nat) (acc0 : G1_F) : G1_F :=
         match w with
         | O => acc0
         | S w' =>
             let acc' := Nat.iter (Z.to_nat c) g1_double_spec acc0 in
             let win :=
               process_window G1_F g1_identity g1_add_spec
                 (scalars_to_Z ss) ps w' (Z.to_nat c)
                 (Nat.pow 2 (Z.to_nat c) - 1)
             in
             go w' (g1_add_spec acc' win)
         end) k acc
      = partial_msm_from k acc (scalars_to_Z ss) ps).
    { induction k as [|k IH]; intros acc; [reflexivity|].
      simpl. apply IH. }
    (* Unfold the outer call and use [go_eq], then absorb the top window. *)
    destruct (Z.to_nat num_windows) as [|NWpred] eqn:ENW; [Lia.lia|].
    (* msm_pippenger computed at [NW = S NWpred] does:
         top_window := process_window ... NWpred;
         go NWpred top_window.
       partial_msm_from (S NWpred) identity does:
         acc' := iter c double identity = identity;
         win  := process_window ... NWpred;
         partial_msm_from NWpred (g1_add identity win) = partial_msm_from NWpred win. *)
    cbn [partial_msm_from].
    replace (S NWpred - 1)%nat with NWpred by Lia.lia.
    rewrite iter_double_identity, g1_add_identity_l.
    apply go_eq.
  Qed.

  (* =================================================================== *)
  (** ** The WP theorem.                                                  *)
  (*                                                                      *)
  (*    Proof structure (4 nested [while_localsmap]s + outer envelope):   *)
  (*                                                                      *)
  (*    1. [straightline] through the 9 [stackalloc]s + initial           *)
  (*       [store_zero] call.                                             *)
  (*    2. Outer window loop — measure [w+1], invariant [outer_inv].      *)
  (*    3. Inside: 4 sequential sub-loops:                                *)
  (*       (a) double-shift loop — measure [i+1], invariant               *)
  (*           [out = Nat.iter (c-i) g1_double_spec out_entry].            *)
  (*       (b) bucket-clear loop — measure [i], invariant [clear_inv].    *)
  (*       (c) distribute loop — measure [i], invariant                   *)
  (*           [distribute_inv w i bs ss ps].  Inner [if idx]              *)
  (*           is split by cases; the [idx > 0] branch rewrites           *)
  (*           [bs] via [PointArray_split_at] / [update_at] and cites     *)
  (*           [spec_of_curve_add].                                       *)
  (*       (d) reduce loop — measure [j+1], invariant [reduce_inv].       *)
  (*           Exit step cites [reduce_inv_at_exit].                      *)
  (*    4. Final outer [curve_add] call: [out := out + ws].               *)
  (*    5. Post-loop stack cleanup (dealloc) — fed by [Allocable].        *)
  (*                                                                      *)
  (*    The Admitted below is one single obligation cluster (the body of  *)
  (*    the outer window loop plus the four nested while invariants).     *)
  (*    All invariants are now concrete; the bridge lemma                 *)
  (*    [reduce_inv_at_exit] is Qed; the running-sum algebra is Qed in    *)
  (*    [IteratedSepPoints].                                              *)
  (* =================================================================== *)

  (** Callee specs — concrete shapes matching the aliased [cmd.call]
      argument lists in [PippengerBedrock2].  Based on [BLS12_G1.v]
      [spec_of_ladderstep] and [StoreZero.v] [spec_of_store_zero], but
      specialised to the three aliased patterns used in the MSM body:
        - [curve_add] with [in1=out] (bucket += point);
        - [curve_double] in-place ([p = 2·p]);
        - [store_zero] 3-pointer identity writer.

      Named as [Def]s taking [functions] so the theorem hypotheses
      are legible. *)

  Definition CurveAddAliasedOK (functions : Semantics.env) : Prop :=
    forall (pb1 pp1 pb2 pp2 pb3 pp3 : word)
           (B1 P1 B2 P2 B3 P3 : F) R tr m,
      (FElem (Some tight_bounds) pb1 B1
       * FElem (Some tight_bounds) pp1 P1
       * FElem (Some tight_bounds) pb2 B2
       * FElem (Some tight_bounds) pp2 P2
       * FElem (Some tight_bounds) pb3 B3
       * FElem (Some tight_bounds) pp3 P3
       * R)%sep m ->
      Semantics.call functions curve_add_name tr m
        [pb1; pp1; pb2; pp2; pb3; pp3; pb1; pb2; pb3]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           let '(B1', B2', B3') := g1_add_spec (B1, B2, B3) (P1, P2, P3) in
           (FElem (Some tight_bounds) pb1 B1'
            * FElem (Some tight_bounds) pp1 P1
            * FElem (Some tight_bounds) pb2 B2'
            * FElem (Some tight_bounds) pp2 P2
            * FElem (Some tight_bounds) pb3 B3'
            * FElem (Some tight_bounds) pp3 P3
            * R)%sep m').

  Definition CurveDoubleInplaceOK (functions : Semantics.env) : Prop :=
    forall (pX pY pZ : word) (X Y Z : F) R tr m,
      (FElem (Some tight_bounds) pX X
       * FElem (Some tight_bounds) pY Y
       * FElem (Some tight_bounds) pZ Z
       * R)%sep m ->
      Semantics.call functions curve_double_name tr m
        [pX; pY; pZ; pX; pY; pZ]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           let '(X', Y', Z') := g1_double_spec (X, Y, Z) in
           (FElem (Some tight_bounds) pX X'
            * FElem (Some tight_bounds) pY Y'
            * FElem (Some tight_bounds) pZ Z'
            * R)%sep m').

  Definition StoreZero3OK (functions : Semantics.env) : Prop :=
    forall (pX pY pZ : word) (Xv Yv Zv : F) R tr m,
      (FElem None pX Xv * FElem None pY Yv * FElem None pZ Zv * R)%sep m ->
      Semantics.call functions store_zero_name tr m
        [pX; pY; pZ]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           (* Jacobian identity is (0, 1, 0) — fixed by [g1_identity]. *)
           let '(Xi, Yi, Zi) := g1_identity in
           (FElem (Some tight_bounds) pX Xi
            * FElem (Some tight_bounds) pY Yi
            * FElem (Some tight_bounds) pZ Zi
            * R)%sep m').

  (* =================================================================== *)
  (** ** Core bedrock2 execution obligation — decomposition of the main  *)
  (*     WP proof into one narrowly-scoped [Admitted] sub-lemma.         *)
  (*                                                                     *)
  (*    [msm_bls12_exec_correct] states the [Semantics.exec.exec] Hoare  *)
  (*    triple for the body of the function, assuming:                   *)
  (*    (a) the three aliased callee specs [HCurveAdd/Double/StoreZero]  *)
  (*    (b) the initial locals map [l0] (the result of the fnspec's      *)
  (*        [map.of_list_zip] on the 8 argument names/values),           *)
  (*    (c) the initial separation-logic memory predicate [Hsep].        *)
  (*                                                                     *)
  (*    The proof of this lemma is the heart of the WP proof (see        *)
  (*    the structure comment above; roughly 3K LoC, organised as 5      *)
  (*    nested [while_localsmap] applications plus 9 [stackalloc]        *)
  (*    frames, plus callee-spec plumbing).                              *)
  (*                                                                     *)
  (*    [msm_bls12_ok] is then mechanical: it unfolds [spec_of_msm_bls12]*)
  (*    and [Semantics.call], discharges the function-dictionary lookup  *)
  (*    with [EnvContains], computes the initial locals map by           *)
  (*    reflexivity, and appeals to [msm_bls12_exec_correct] for the     *)
  (*    exec triple.                                                     *)
  (*                                                                     *)
  (*    SUGGESTED FACTORING for a future multi-hour proof effort:        *)
  (*    split this single [Admitted] into 5 narrowly-scoped leaf         *)
  (*    [Admitted]s, one per sub-loop (double-shift, bucket-clear,       *)
  (*    distribute, reduce) plus the outer-window-loop envelope.  Each   *)
  (*    leaf would be an [exec.exec] triple over the specific subtree of *)
  (*    [msm_bls12]'s body, with Gallina precondition / postcondition    *)
  (*    tracking [outer_inv]/[clear_inv]/[distribute_inv]/[reduce_inv]   *)
  (*    from above.  The main [msm_bls12_exec_correct] then peels 9      *)
  (*    [stackalloc]s, discharges the initial [store_zero] via           *)
  (*    [HStoreZero], and invokes the outer-loop-envelope leaf.  The     *)
  (*    outer-loop-envelope leaf in turn invokes the 4 sub-loop leaves   *)
  (*    inside its body.  All Gallina preservation is already Qed        *)
  (*    above.                                                           *)
  (* =================================================================== *)

  (** Helper: split [anybytes] into a prefix + suffix.  Follows from the
      unfolded definition [anybytes p n m := exists bs, of_list_word_at p
      bs = m /\ length bs = n].  Splitting [bs] at the prefix length gives
      the two chunks; [map.split_of_list_word_at] distributes
      [of_list_word_at] over list append. *)
  Lemma anybytes_split :
    forall (p : word) (a b : Z) (m : mem),
      0 <= a -> 0 <= b ->
      Memory.anybytes p (a + b) m ->
      exists m1 m2,
        map.split m m1 m2 /\
        Memory.anybytes p a m1 /\
        Memory.anybytes (word.add p (word.of_Z a)) b m2.
  Proof.
    intros p a b m Ha Hb Hany.
    destruct Hany as [bs [Hof [Hlen Hbnd]]].
    pose (na := Z.to_nat a).
    pose (bs1 := List.firstn na bs).
    pose (bs2 := List.skipn na bs).
    assert (Hbs : bs = List.app bs1 bs2)
      by (subst bs1 bs2; symmetry; apply List.firstn_skipn).
    assert (Hlen1 : Z.of_nat (List.length bs1) = a).
    { subst bs1 na. rewrite List.firstn_length.
      rewrite Nat.min_l; [ apply Z2Nat.id; lia | ].
      apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
    assert (Hlen2 : Z.of_nat (List.length bs2) = b).
    { subst bs2 na. rewrite List.skipn_length.
      rewrite Nat2Z.inj_sub;
        [ | apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia ].
      rewrite Z2Nat.id by lia. lia. }
    pose (m1 := OfListWord.map.of_list_word_at p bs1).
    pose (m2 := OfListWord.map.of_list_word_at
                  (word.add p (word.of_Z a)) bs2).
    exists m1, m2.
    split; [ | split ].
    - (* map.split m m1 m2 *)
      assert (Hdisj : map.disjoint m2 m1).
      { subst m1 m2.
        rewrite <- Hlen1.
        apply OfListWord.map.adjacent_arrays_disjoint.
        rewrite Hlen1, Hlen2. lia. }
      assert (Hm : m = map.putmany m2 m1).
      { subst m. subst m1 m2.
        rewrite Hbs at 1.
        rewrite (OfListWord.map.of_list_word_at_app_n p bs1 bs2 a Hlen1).
        reflexivity. }
      split.
      + rewrite Hm. apply map.putmany_comm. assumption.
      + intros k v1 v2 Hv1 Hv2.
        unfold map.disjoint in Hdisj. eapply Hdisj; eassumption.
    - (* Memory.anybytes p a m1 *)
      exists bs1. split; [ reflexivity | split; [ lia | ] ].
      rewrite Hlen1. lia.
    - (* Memory.anybytes (p + a) b m2 *)
      exists bs2. split; [ reflexivity | split; [ lia | ] ].
      rewrite Hlen2. lia.
  Qed.

  (** Helper: [anybytes p (n*felem_size_in_bytes) m] gives an
      [array (FElem None)] of length [n] at [p] for some fresh F-list.
      Induction on [n]; each step peels one [felem_size_in_bytes] chunk
      via [anybytes_split], applies [felem_alloc.P_from_bytes], and
      recomposes via [array_cons].  First-cut Coq proof hit tactic-level
      issues with [Lia.nia] on felem_size_in_bytes-scaled terms and
      map.of_list_word_at unfolding; deferred to a focused session. *)
  Lemma anybytes_to_felem_array :
    forall (p : word) (n : nat) (m : mem),
      Memory.anybytes p (Z.of_nat n * felem_size_in_bytes) m ->
      exists xs : list F, length xs = n /\
                 array (FElem None) (word.of_Z felem_size_in_bytes) p xs m.
  Proof.
    Existing Instance felem_alloc.
    intros p n; revert p.
    induction n; intros p m Hany.
    - (* n = 0 : empty array, m = empty *)
      exists nil. split; [ reflexivity | ].
      simpl. unfold emp.
      destruct Hany as [bs [Hof [Hlen _]]].
      assert (bs = nil) by (destruct bs; simpl in Hlen; [ reflexivity | lia ]).
      subst bs. simpl in Hof.
      split; [ | exact I ].
      subst m. rewrite OfListWord.map.of_list_word_nil. reflexivity.
    - (* n = S n' *)
      replace (Z.of_nat (S n) * felem_size_in_bytes)
         with (felem_size_in_bytes + Z.of_nat n * felem_size_in_bytes) in Hany
         by lia.
      pose proof Types.word_size_in_bytes_pos (width:=width) as Hwpos.
      assert (Hfnn : 0 <= felem_size_in_bytes).
      { unfold felem_size_in_bytes. apply Z.mul_nonneg_nonneg; lia. }
      assert (Hle : 0 <= Z.of_nat n * felem_size_in_bytes)
        by (apply Z.mul_nonneg_nonneg; lia).
      destruct (anybytes_split p felem_size_in_bytes
                  (Z.of_nat n * felem_size_in_bytes) m
                  Hfnn Hle Hany)
        as [m1 [m2 [Hsp [Hany1 Hany2]]]].
      (* Peel first felem. *)
      pose proof (P_from_bytes (Allocable:=felem_alloc) p m1 Hany1)
        as [x0 Hx0].
      (* Recurse at shifted pointer. *)
      destruct (IHn (word.add p (word.of_Z felem_size_in_bytes)) m2 Hany2)
        as [xs [Hlen Hxs]].
      exists (x0 :: xs). split; [ simpl; congruence | ].
      simpl.
      exists m1, m2.
      split; [ exact Hsp | split; [ exact Hx0 | exact Hxs ] ].
  Qed.

  (* =================================================================== *)
  (** ** Sub-loop leaves — load-bearing decomposition of prelude_wp.      *)
  (*                                                                      *)
  (*    Each leaf encapsulates one sub-computation of the outer-loop      *)
  (*    body.  [msm_bls12_prelude_wp] cites these after establishing the  *)
  (*    stackalloc + initial-store_zero prelude.  All are currently       *)
  (*    Admitted; future sessions will close each leaf independently.     *)
  (* =================================================================== *)

  (** Leaf 1: double-shift sub-loop.  [i] counts from [c] down to 0;
      each iteration calls [curve_double] in-place on (outx, outy, outz).
      Entry: local [i] = c, FElem triples at (Xe, Ye, Ze).
      Exit:  FElem triples at [Nat.iter c g1_double_spec (Xe, Ye, Ze)]. *)
  Lemma msm_bls12_double_shift_wp :
    forall functions
      (HCurveDouble : CurveDoubleInplaceOK functions)
      (outx outy outz : word)
      (Xe Ye Ze : F)
      (R : mem -> Prop) (tr : Semantics.trace) (mem0 : mem)
      (l0 : locals),
      (FElem (Some tight_bounds) outx Xe
       * FElem (Some tight_bounds) outy Ye
       * FElem (Some tight_bounds) outz Ze
       * R)%sep mem0 ->
      map.get l0 "outx" = Some outx ->
      map.get l0 "outy" = Some outy ->
      map.get l0 "outz" = Some outz ->
      map.get l0 "i" = Some (word.of_Z c) ->
      WeakestPrecondition.cmd functions
        (cmd.while (expr.var "i")
           (cmd.seq
              (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
              (cmd.call [] curve_double_name
                 [expr.var "outx"; expr.var "outy"; expr.var "outz";
                  expr.var "outx"; expr.var "outy"; expr.var "outz"])))
        tr mem0 l0
        (fun tr' mem' l' =>
           tr = tr' /\
           (let '(Xf, Yf, Zf) :=
              Nat.iter (Z.to_nat c) g1_double_spec (Xe, Ye, Ze) in
            (FElem (Some tight_bounds) outx Xf
             * FElem (Some tight_bounds) outy Yf
             * FElem (Some tight_bounds) outz Zf
             * R)%sep mem') /\
           map.get l' "outx" = Some outx /\
           map.get l' "outy" = Some outy /\
           map.get l' "outz" = Some outz).
  Proof.
    intros functions HCurveDouble outx outy outz Xe Ye Ze R tr mem0 l0
           Hsep Houtx Houty Houtz Hi.
    eapply bedrock2.Loops.while_localsmap
      with (lt := Nat.lt) (v0 := Z.to_nat c)
           (invariant := fun (v : nat) (t : Semantics.trace) (m : mem) (l : locals) =>
              t = tr /\
              (v <= Z.to_nat c)%nat /\
              map.get l "outx" = Some outx /\
              map.get l "outy" = Some outy /\
              map.get l "outz" = Some outz /\
              map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
              (let '(Xc, Yc, Zc) :=
                 Nat.iter (Z.to_nat c - v)%nat g1_double_spec (Xe, Ye, Ze) in
               (FElem (Some tight_bounds) outx Xc
                * FElem (Some tight_bounds) outy Yc
                * FElem (Some tight_bounds) outz Zc
                * R)%sep m)).
    { (* Well-foundedness *)
      exact Wf_nat.lt_wf. }
    { (* Initial invariant at v = Z.to_nat c *)
      split; [reflexivity|].
      split; [Lia.lia|].
      split; [exact Houtx|].
      split; [exact Houty|].
      split; [exact Houtz|].
      split.
      { rewrite Z2Nat.id by (cbv; discriminate). exact Hi. }
      replace (Z.to_nat c - Z.to_nat c)%nat with 0%nat by Lia.lia.
      cbn [Nat.iter]. exact Hsep. }
    { (* Loop body + exit: give branch value and split the two cases. *)
      intros v tv mv lv Hinv.
      destruct Hinv as [Htr [Hvle [Hlx [Hly [Hlz [Hli Hm]]]]]].
      subst tv.
      exists (word.of_Z (Z.of_nat v)).
      split.
      { (* branch expr evaluates to (word.of_Z v) *)
        cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get dlet.dlet].
        eexists; split; [exact Hli | reflexivity]. }
      split.
      { (* TRUE branch: v <> 0, run body *)
        intro Hne.
        assert (Hv_pos : (0 < v)%nat).
        { destruct v as [|v']; [|Lia.lia].
          exfalso. apply Hne.
          change (Z.of_nat 0) with 0%Z.
          rewrite word.unsigned_of_Z_0. reflexivity. }
        (* cmd.set "i" := i - 1 *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body]. fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split; [exact Hli |].
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        (* Now have: new locals = map.put lv "i" (word.sub (word.of_Z v) (word.of_Z 1)). *)
        (* Call curve_double_name in-place. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body]. fold WeakestPrecondition.cmd.
        eexists. split.
        { (* dexprs on 6 var references to outx/outy/outz (all the same values). *)
          cbv [WeakestPrecondition.dexprs list_map list_map_body
               WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get dlet.dlet].
          eexists. split.
          { rewrite map.get_put_diff by congruence. exact Hlx. }
          eexists. split.
          { rewrite map.get_put_diff by congruence. exact Hly. }
          eexists. split.
          { rewrite map.get_put_diff by congruence. exact Hlz. }
          eexists. split.
          { rewrite map.get_put_diff by congruence. exact Hlx. }
          eexists. split.
          { rewrite map.get_put_diff by congruence. exact Hly. }
          eexists. split.
          { rewrite map.get_put_diff by congruence. exact Hlz. }
          reflexivity. }
        (* Invoke the CurveDoubleInplaceOK hypothesis. *)
        set (st := Nat.iter (Z.to_nat c - v)%nat g1_double_spec (Xe, Ye, Ze)) in *.
        destruct st as [[Xc Yc] Zc] eqn:Hst.
        eapply Semantics.weaken_call.
        { eapply (HCurveDouble outx outy outz Xc Yc Zc R tr mv).
          exact Hm. }
        cbv beta. intros tr' m' rets [Hrets [Htreq Hm']].
        subst rets tr'.
        (* Destruct the resulting iteration state *)
        remember (g1_double_spec (Xc, Yc, Zc)) as st' eqn:Hst'.
        destruct st' as [[Xc' Yc'] Zc'].
        (* After the call, update locals with rets = []. *)
        cbv [map.putmany_of_list_zip].
        eexists. split; [reflexivity|].
        (* Invariant for the next iteration: v' = v - 1. *)
        exists (v - 1)%nat.
        split.
        { (* Re-establish invariant *)
          split; [reflexivity|].
          split; [Lia.lia|].
          split.
          { rewrite map.get_put_diff by congruence. exact Hlx. }
          split.
          { rewrite map.get_put_diff by congruence. exact Hly. }
          split.
          { rewrite map.get_put_diff by congruence. exact Hlz. }
          split.
          { rewrite map.get_put_same.
            f_equal.
            (* Show: word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1)
                   = word.of_Z (Z.of_nat (v-1)). *)
            rewrite Nat2Z.inj_sub by Lia.lia.
            change (Z.of_nat 1) with 1%Z.
            apply word.unsigned_inj.
            rewrite word.unsigned_sub.
            rewrite !word.unsigned_of_Z.
            cbv [word.wrap].
            assert (Hv_bd : Z.of_nat v <= 9).
            { assert (Hle : (Z.of_nat v <= Z.of_nat (Z.to_nat c))%Z) by
                (apply Nat2Z.inj_le; exact Hvle).
              rewrite Z2Nat.id in Hle by (cbv; discriminate).
              unfold c in Hle. exact Hle. }
            assert (H2w_big : 2 ^ 32 <= 2 ^ width).
            { apply Z.pow_le_mono_r; [Lia.lia|].
              pose proof width_cases as Hwc.
              destruct Hwc as [Hw|Hw]; rewrite Hw; Lia.lia. }
            assert (H2w_pos : 0 < 2 ^ width) by (pose proof word.width_pos; apply Z.pow_pos_nonneg; Lia.lia).
            rewrite (Z.mod_small (Z.of_nat v) (2 ^ width)) by Lia.lia.
            rewrite (Z.mod_small 1 (2 ^ width)) by Lia.lia.
            rewrite (Z.mod_small (Z.of_nat v - 1) (2 ^ width)) by Lia.lia.
            reflexivity. }
          (* The running accumulator state *)
          replace (Z.to_nat c - (v - 1))%nat with (S (Z.to_nat c - v))%nat by Lia.lia.
          change (Nat.iter (S (Z.to_nat c - v)) g1_double_spec (Xe, Ye, Ze))
            with (g1_double_spec (Nat.iter (Z.to_nat c - v) g1_double_spec (Xe, Ye, Ze))).
          fold st. rewrite Hst.
          rewrite <- Hst'.
          exact Hm'. }
        { (* v' < v *)
          Lia.lia. } }
      { (* FALSE branch: v = 0, re-establish postcondition. *)
        intro Heq.
        assert (Hv0 : v = 0%nat).
        { rewrite word.unsigned_of_Z in Heq.
          cbv [word.wrap] in Heq.
          assert (Hv_bd : Z.of_nat v <= 9).
          { assert (Hle : (Z.of_nat v <= Z.of_nat (Z.to_nat c))%Z) by
              (apply Nat2Z.inj_le; exact Hvle).
            rewrite Z2Nat.id in Hle by (cbv; discriminate).
            unfold c in Hle. exact Hle. }
          assert (H2w_big : 2 ^ 32 <= 2 ^ width).
          { apply Z.pow_le_mono_r; [Lia.lia|].
            pose proof width_cases as Hwc.
            destruct Hwc as [Hw|Hw]; rewrite Hw; Lia.lia. }
          rewrite Z.mod_small in Heq by Lia.lia.
          Lia.lia. }
        subst v.
        replace (Z.to_nat c - 0)%nat with (Z.to_nat c) in Hm by Lia.lia.
        split; [reflexivity|].
        split; [exact Hm|].
        split; [exact Hlx|].
        split; [exact Hly|].
        exact Hlz. } }
  Qed.

  (** --- Helpers for the [msm_bls12_bucket_clear_wp] proof below. --- *)

  (** List splitting lemma: [firstn (S n) xs = firstn n xs ++ [nth n xs d]].  Used to peel
      the last cell from a length-[S n] [firstn] prefix. *)
  Lemma firstn_S_as_snoc {A : Type} (d : A) (n : nat) (xs : list A) :
    (n < length xs)%nat ->
    firstn (S n) xs = (firstn n xs ++ [nth n xs d])%list.
  Proof.
    revert n. induction xs as [|x rest IH]; intros n Hlt; [cbn in Hlt; Lia.lia|].
    destruct n as [|n'].
    - (* n = 0 *)
      destruct rest; reflexivity.
    - (* n = S n' *)
      cbn in Hlt.
      specialize (IH n' ltac:(Lia.lia)).
      change (firstn (S (S n')) (x :: rest)) with (x :: firstn (S n') rest).
      change ((firstn (S n') (x :: rest) ++ [nth (S n') (x :: rest) d])%list)
        with ((x :: (firstn n' rest ++ [nth n' rest d]))%list).
      rewrite <- IH. reflexivity.
  Qed.

  (** Bridge: peel the last element from three parallel arrays of length [S n]
      at once.  The lemma takes concrete bucket lists (not [firstn]-expressions)
      to avoid [seprewrite_in] unfolding issues.  Output shape: three shorter
      arrays (length [n] via [firstn]) + three individual [FElem None] cells at
      offset [n*sz]. *)
  Lemma bucket_clear_triple_split_step
        (buckets_x buckets_y buckets_z : word)
        (pref_x pref_y pref_z : list F)
        (Fdef : F)
        (n : nat)
        (suffix : mem -> Prop) (R : mem -> Prop) (m : mem) :
    length pref_x = S n -> length pref_y = S n -> length pref_z = S n ->
    let sz := word.of_Z (width:=width) felem_size_in_bytes in
    let wsz' := word.unsigned sz in
    (array (FElem None) sz buckets_x pref_x
     * array (FElem None) sz buckets_y pref_y
     * array (FElem None) sz buckets_z pref_z
     * suffix * R)%sep m ->
    (array (FElem None) sz buckets_x (firstn n pref_x)
     * FElem None (word.add buckets_x (word.of_Z (wsz' * Z.of_nat n)))
                  (nth n pref_x Fdef)
     * array (FElem None) sz buckets_y (firstn n pref_y)
     * FElem None (word.add buckets_y (word.of_Z (wsz' * Z.of_nat n)))
                  (nth n pref_y Fdef)
     * array (FElem None) sz buckets_z (firstn n pref_z)
     * FElem None (word.add buckets_z (word.of_Z (wsz' * Z.of_nat n)))
                  (nth n pref_z Fdef)
     * suffix * R)%sep m.
  Proof.
    intros Hlenx Hleny Hlenz sz wsz' Hm.
    (* Use PointArray_split_at on each of the three bucket arrays. *)
    pose proof (PointArray_split_at (T:=F) (default:=Fdef)
                  (FElem None) sz buckets_x pref_x n
                  ltac:(Lia.lia)) as Hx.
    pose proof (PointArray_split_at (T:=F) (default:=Fdef)
                  (FElem None) sz buckets_y pref_y n
                  ltac:(Lia.lia)) as Hy.
    pose proof (PointArray_split_at (T:=F) (default:=Fdef)
                  (FElem None) sz buckets_z pref_z n
                  ltac:(Lia.lia)) as Hz.
    unfold PointArray in Hx, Hy, Hz.
    (* [hd default (skipn k xs) = nth k xs d] when [k < length xs].
       Generic over [k]. *)
    assert (Hhd_gen : forall (k : nat) (xs : list F),
      (k < length xs)%nat ->
      hd Fdef (skipn k xs) = nth k xs Fdef).
    { intros k. induction k as [|k' IHk]; intros xs Hlt.
      - destruct xs; [cbn in Hlt; Lia.lia | reflexivity].
      - destruct xs as [|x rest]; [cbn in Hlt; Lia.lia|].
        cbn [skipn nth]. apply IHk. cbn in Hlt. Lia.lia. }
    assert (Hhdx : hd Fdef (skipn n pref_x) = nth n pref_x Fdef)
      by (apply Hhd_gen; Lia.lia).
    assert (Hhdy : hd Fdef (skipn n pref_y) = nth n pref_y Fdef)
      by (apply Hhd_gen; Lia.lia).
    assert (Hhdz : hd Fdef (skipn n pref_z) = nth n pref_z Fdef)
      by (apply Hhd_gen; Lia.lia).
    rewrite Hhdx in Hx. rewrite Hhdy in Hy. rewrite Hhdz in Hz.
    (* [skipn (S n) pref = nil] since length = S n. *)
    assert (Hskipx : skipn (S n) pref_x = nil)
      by (apply length_zero_iff_nil; rewrite length_skipn; Lia.lia).
    assert (Hskipy : skipn (S n) pref_y = nil)
      by (apply length_zero_iff_nil; rewrite length_skipn; Lia.lia).
    assert (Hskipz : skipn (S n) pref_z = nil)
      by (apply length_zero_iff_nil; rewrite length_skipn; Lia.lia).
    rewrite Hskipx in Hx. rewrite Hskipy in Hy. rewrite Hskipz in Hz.
    (* Arrays over [nil] reduce. *)
    subst sz wsz'. cbv beta.
    seprewrite_in Hx Hm. seprewrite_in Hy Hm. seprewrite_in Hz Hm.
    cbn [array] in Hm.
    ecancel_assumption.
  Qed.

  (** Reverse direction: merge three freshly-written tight-bounds cells at
      offset [n*sz] into the existing tight-bounds suffix at offset [(S n)*sz],
      producing a longer tight-bounds suffix starting at offset [n*sz]. *)
  Lemma bucket_clear_triple_merge_step
        (buckets_x buckets_y buckets_z : word)
        (bs_x bs_y bs_z : list F)
        (Xi Yi Zi : F)
        (n nb : nat)
        (prefix : mem -> Prop) (R : mem -> Prop) (m : mem) :
    (n < nb)%nat ->
    let sz := word.of_Z (width:=width) felem_size_in_bytes in
    let wsz' := word.unsigned sz in
    (FElem (Some tight_bounds)
           (word.add buckets_x (word.of_Z (wsz' * Z.of_nat n))) Xi
     * FElem (Some tight_bounds)
           (word.add buckets_y (word.of_Z (wsz' * Z.of_nat n))) Yi
     * FElem (Some tight_bounds)
           (word.add buckets_z (word.of_Z (wsz' * Z.of_nat n))) Zi
     * array (FElem (Some tight_bounds)) sz
             (word.add buckets_x (word.of_Z (wsz' * Z.of_nat (S n))))
             (repeat Xi (nb - S n))
     * array (FElem (Some tight_bounds)) sz
             (word.add buckets_y (word.of_Z (wsz' * Z.of_nat (S n))))
             (repeat Yi (nb - S n))
     * array (FElem (Some tight_bounds)) sz
             (word.add buckets_z (word.of_Z (wsz' * Z.of_nat (S n))))
             (repeat Zi (nb - S n))
     * prefix * R)%sep m ->
    (array (FElem (Some tight_bounds)) sz
           (word.add buckets_x (word.of_Z (wsz' * Z.of_nat n)))
           (repeat Xi (nb - n))
     * array (FElem (Some tight_bounds)) sz
           (word.add buckets_y (word.of_Z (wsz' * Z.of_nat n)))
           (repeat Yi (nb - n))
     * array (FElem (Some tight_bounds)) sz
           (word.add buckets_z (word.of_Z (wsz' * Z.of_nat n)))
           (repeat Zi (nb - n))
     * prefix * R)%sep m.
  Proof.
    intros Hlt sz wsz' Hm.
    (* [nb - n = S (nb - S n)]. *)
    assert (Hdec : (nb - n = S (nb - S n))%nat) by Lia.lia.
    rewrite Hdec.
    (* Use array_cons to move the single FElem into the suffix.  The suffix
       starts at [base + (S n)*sz] which equals [base + n*sz + sz]. *)
    assert (Hshift_x : word.add buckets_x (word.of_Z (wsz' * Z.of_nat (S n)))
                    = word.add (word.add buckets_x (word.of_Z (wsz' * Z.of_nat n))) sz).
    { apply word.unsigned_inj.
      rewrite !word.unsigned_add, !word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite !Zdiv.Zplus_mod_idemp_r.
      rewrite !Zdiv.Zplus_mod_idemp_l.
      f_equal. subst wsz' sz. rewrite word.unsigned_of_Z. unfold word.wrap.
      rewrite Nat2Z.inj_succ. Lia.lia. }
    assert (Hshift_y : word.add buckets_y (word.of_Z (wsz' * Z.of_nat (S n)))
                    = word.add (word.add buckets_y (word.of_Z (wsz' * Z.of_nat n))) sz).
    { apply word.unsigned_inj.
      rewrite !word.unsigned_add, !word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite !Zdiv.Zplus_mod_idemp_r.
      rewrite !Zdiv.Zplus_mod_idemp_l.
      f_equal. subst wsz' sz. rewrite word.unsigned_of_Z. unfold word.wrap.
      rewrite Nat2Z.inj_succ. Lia.lia. }
    assert (Hshift_z : word.add buckets_z (word.of_Z (wsz' * Z.of_nat (S n)))
                    = word.add (word.add buckets_z (word.of_Z (wsz' * Z.of_nat n))) sz).
    { apply word.unsigned_inj.
      rewrite !word.unsigned_add, !word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite !Zdiv.Zplus_mod_idemp_r.
      rewrite !Zdiv.Zplus_mod_idemp_l.
      f_equal. subst wsz' sz. rewrite word.unsigned_of_Z. unfold word.wrap.
      rewrite Nat2Z.inj_succ. Lia.lia. }
    rewrite Hshift_x, Hshift_y, Hshift_z in Hm.
    (* The goal is [(array tight sz p_xn (repeat Xi (S (nb - S n))) * ...) m],
       and [repeat v (S k) = v :: repeat v k] syntactically.  Simplify. *)
    change (repeat ?v (S ?k)) with (v :: repeat v k).
    (* Each array at [repeat v (nb - n)] is now [v :: repeat v (nb - S n)];
       [array _ _ p (v :: xs) = element p v * array _ _ (p+sz) xs]. *)
    (* Let's use cbn [array] to unfold the array-cons equation. *)
    cbn [array].
    ecancel_assumption.
  Qed.

  (** Lift [drop_bounds_FElem] to an array of [num] parallel cells. *)
  Lemma array_FElem_drop_bounds_impl1
        (sz : word) (p : word) (xs : list F) :
    Lift1Prop.impl1
      (array (FElem (Some tight_bounds)) sz p xs)
      (array (FElem None) sz p xs).
  Proof.
    revert p. induction xs as [|x xs' IH]; intros p.
    - cbn. reflexivity.
    - cbn. apply Proper_sep_impl1;
        [ apply Compilation2.drop_bounds_FElem | apply IH ].
  Qed.

  (** Leaf 2: bucket-clear sub-loop.  [i] counts from [num_buckets] down;
      each iter computes address [bp_k = buckets_k + i*48] for k ∈ {x,y,z}
      then calls [store_zero] on the triple.  Exit: every bucket =
      [g1_identity]. *)
  Lemma msm_bls12_bucket_clear_wp :
    forall functions
      (HStoreZero : StoreZero3OK functions)
      (buckets_x buckets_y buckets_z : word)
      (bs_x bs_y bs_z : list F)
      (R : mem -> Prop) (tr : Semantics.trace) (mem0 : mem)
      (l0 : locals),
      Z.of_nat (length bs_x) = num_buckets ->
      Z.of_nat (length bs_y) = num_buckets ->
      Z.of_nat (length bs_z) = num_buckets ->
      (array (FElem None) (word.of_Z felem_size_in_bytes) buckets_x bs_x
       * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_y bs_y
       * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_z bs_z
       * R)%sep mem0 ->
      map.get l0 "buckets_x" = Some buckets_x ->
      map.get l0 "buckets_y" = Some buckets_y ->
      map.get l0 "buckets_z" = Some buckets_z ->
      map.get l0 "i" = Some (word.of_Z num_buckets) ->
      WeakestPrecondition.cmd functions
        (cmd.while (expr.var "i")
           (cmd.seq
              (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
           (cmd.seq
              (cmd.set "bpx" (expr.op bopname.add (expr.var "buckets_x")
                 (expr.op bopname.mul (expr.var "i") (expr.literal felem_size_in_bytes))))
           (cmd.seq
              (cmd.set "bpy" (expr.op bopname.add (expr.var "buckets_y")
                 (expr.op bopname.mul (expr.var "i") (expr.literal felem_size_in_bytes))))
           (cmd.seq
              (cmd.set "bpz" (expr.op bopname.add (expr.var "buckets_z")
                 (expr.op bopname.mul (expr.var "i") (expr.literal felem_size_in_bytes))))
              (cmd.call [] store_zero_name
                 [expr.var "bpx"; expr.var "bpy"; expr.var "bpz"]))))))
        tr mem0 l0
        (fun tr' mem' l' =>
           tr = tr' /\
           exists (bs_x' bs_y' bs_z' : list F),
             Z.of_nat (length bs_x') = num_buckets /\
             Z.of_nat (length bs_y') = num_buckets /\
             Z.of_nat (length bs_z') = num_buckets /\
             (forall k, (k < Z.to_nat num_buckets)%nat ->
                        nth k (points_of bs_x' bs_y' bs_z') g1_identity
                        = g1_identity) /\
             (array (FElem None) (word.of_Z felem_size_in_bytes) buckets_x bs_x'
              * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_y bs_y'
              * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_z bs_z'
              * R)%sep mem' /\
             map.get l' "buckets_x" = Some buckets_x /\
             map.get l' "buckets_y" = Some buckets_y /\
             map.get l' "buckets_z" = Some buckets_z).
  Proof.
    intros functions HStoreZero
           buckets_x buckets_y buckets_z bs_x bs_y bs_z
           R tr mem0 l0
           Hlen_x Hlen_y Hlen_z Hsep
           Hl_bx Hl_by Hl_bz Hl_i.
    (* Width bounds used repeatedly. *)
    pose proof width_cases as Hwc.
    assert (H2w_big : 2 ^ 32 <= 2 ^ width).
    { apply Z.pow_le_mono_r; [Lia.lia|].
      destruct Hwc as [Hw|Hw]; rewrite Hw; Lia.lia. }
    assert (H2w_pos : 0 < 2 ^ width).
    { pose proof word.width_pos; apply Z.pow_pos_nonneg; Lia.lia. }
    assert (Hnb_val : num_buckets = 511) by reflexivity.
    assert (Hnb_small : num_buckets < 2 ^ width) by Lia.lia.
    pose proof felem_size_ok as Hfs_le.
    (* Name the identity triple.  Use [remember]-like pattern with explicit
       pairs so [g1_identity] is NOT substituted in the subsequent goal. *)
    remember g1_identity as giden eqn:Hgiden.
    destruct giden as [[Xi Yi] Zi].
    (* [Hgiden : (Xi, Yi, Zi) = g1_identity] *)
    symmetry in Hgiden. rename Hgiden into HgI.
    (* Now [HgI : g1_identity = (Xi, Yi, Zi)]. *)
    (* Invariant at measure [v], "v buckets left to clear":
         exists pref_x, pref_y, pref_z : list F of length v,
           [array None sz p_k pref_k] holds for the first [v] cells
           at each bucket array, and
           [array tight sz (p_k + v*sz) (repeat K_i (num_buckets - v))]
           holds for the last [num_buckets - v] cells.
         All 4 locals preserved; [i = iw] with [word.unsigned iw = Z.of_nat v].
    *)
    pose (inv := fun (v : nat) (tr' : Semantics.trace) (m : mem) (l : locals) =>
      exists (pref_x pref_y pref_z : list F) (iw : word),
        (v <= Z.to_nat num_buckets)%nat /\
        word.unsigned iw = Z.of_nat v /\
        length pref_x = v /\ length pref_y = v /\ length pref_z = v /\
        (array (FElem None) (word.of_Z felem_size_in_bytes) buckets_x pref_x
         * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
                 (word.add buckets_x
                    (word.of_Z (word.unsigned (width:=width)
                                  (word.of_Z felem_size_in_bytes) * Z.of_nat v)))
                 (repeat Xi (Z.to_nat num_buckets - v))
         * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_y pref_y
         * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
                 (word.add buckets_y
                    (word.of_Z (word.unsigned (width:=width)
                                  (word.of_Z felem_size_in_bytes) * Z.of_nat v)))
                 (repeat Yi (Z.to_nat num_buckets - v))
         * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_z pref_z
         * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
                 (word.add buckets_z
                    (word.of_Z (word.unsigned (width:=width)
                                  (word.of_Z felem_size_in_bytes) * Z.of_nat v)))
                 (repeat Zi (Z.to_nat num_buckets - v))
         * R)%sep m /\
        map.get l "buckets_x" = Some buckets_x /\
        map.get l "buckets_y" = Some buckets_y /\
        map.get l "buckets_z" = Some buckets_z /\
        map.get l "i" = Some iw /\
        tr = tr').
    eapply (Loops.while_localsmap (measure:=nat) inv Nat.lt_wf_0
                                  (Z.to_nat num_buckets)).
    { (* Entry: v = num_buckets.  No cleared buckets yet; pref_k = bs_k. *)
      subst inv; cbv beta.
      exists bs_x, bs_y, bs_z, (word.of_Z num_buckets).
      split; [Lia.lia|].
      split.
      { rewrite word.unsigned_of_Z. cbv [word.wrap].
        rewrite Z.mod_small by Lia.lia.
        rewrite Z2Nat.id by (cbv; discriminate). reflexivity. }
      split; [rewrite <- (Nat2Z.id (length bs_x)); rewrite Hlen_x; reflexivity|].
      split; [rewrite <- (Nat2Z.id (length bs_y)); rewrite Hlen_y; reflexivity|].
      split; [rewrite <- (Nat2Z.id (length bs_z)); rewrite Hlen_z; reflexivity|].
      split.
      { replace (Z.to_nat num_buckets - Z.to_nat num_buckets)%nat with 0%nat by Lia.lia.
        cbn [repeat array].
        (* Three [array tight ... nil] collapse.  Show original [Hsep] suffices. *)
        ecancel_assumption. }
      repeat (split; [try (now exact Hl_bx); try (now exact Hl_by);
                      try (now exact Hl_bz); try (now exact Hl_i)|]).
      reflexivity. }
    { (* Body step. *)
      intros vi tr1 m1 l1 Hinv.
      subst inv; cbv beta in Hinv.
      destruct Hinv as (pref_x & pref_y & pref_z & iw &
                        Hvi_le & Hiw_val & Hlenpx & Hlenpy & Hlenpz & Hm1 &
                        Hlbx1 & Hlby1 & Hlbz1 & Hli1 & Htreq).
      subst tr1.
      exists iw.
      split.
      { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get dlet.dlet].
        eexists; split; [exact Hli1|]. exact eq_refl. }
      split.
      - (* TRUE branch: iw <> 0, so vi = S n. *)
        intro Hbr.
        assert (Hvi_pos : (vi > 0)%nat).
        { destruct vi as [|n']; [|Lia.lia].
          exfalso. apply Hbr. rewrite Hiw_val. reflexivity. }
        destruct vi as [|n]; [Lia.lia|].
        (* Bounds on Z.of_nat (S n). *)
        assert (HSn_small : Z.of_nat (S n) < 2 ^ width).
        { assert (HSn_le : Z.of_nat (S n) <= 511).
          { rewrite <- Hnb_val. rewrite <- (Z2Nat.id num_buckets)
              by (cbv; discriminate).
            apply Nat2Z.inj_le. exact Hvi_le. }
          Lia.lia. }
        assert (Hn_small : Z.of_nat n < 2 ^ width).
        { rewrite Nat2Z.inj_succ in HSn_small. Lia.lia. }
        assert (Hn_le_nb : (n < Z.to_nat num_buckets)%nat) by Lia.lia.
        (* cmd.set "i" := i - 1. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split; [exact Hli1|].
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        set (iw' := word.sub iw (word.of_Z 1)).
        assert (Hiw'_unsigned : word.unsigned iw' = Z.of_nat n).
        { subst iw'.
          rewrite word.unsigned_sub.
          rewrite Hiw_val. rewrite word.unsigned_of_Z.
          cbv [word.wrap]. rewrite Nat2Z.inj_succ.
          rewrite (Z.mod_small 1 (2 ^ width)) by Lia.lia.
          rewrite Z.mod_small by Lia.lia. Lia.lia. }
        (* cmd.set "bpx". *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence. exact Hlbx1. }
          eexists; split.
          { rewrite map.get_put_same. reflexivity. }
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        (* cmd.set "bpy". *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlby1. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        (* cmd.set "bpz". *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlbz1. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        (* Bucket addresses *)
        set (sz := word.of_Z (width:=width) felem_size_in_bytes).
        set (bpx := word.add buckets_x (word.mul iw' sz)).
        set (bpy := word.add buckets_y (word.mul iw' sz)).
        set (bpz := word.add buckets_z (word.mul iw' sz)).
        (* bp_k = buckets_k + n*sz *)
        assert (Hmul_eq :
          word.mul iw' sz =
          word.of_Z (word.unsigned sz * Z.of_nat n)).
        { apply word.unsigned_inj.
          rewrite word.unsigned_mul. rewrite Hiw'_unsigned.
          rewrite word.unsigned_of_Z. unfold word.wrap.
          f_equal. Lia.lia. }
        assert (Hbpx_eq : bpx =
          word.add buckets_x (word.of_Z (word.unsigned sz * Z.of_nat n))).
        { subst bpx. f_equal. apply Hmul_eq. }
        assert (Hbpy_eq : bpy =
          word.add buckets_y (word.of_Z (word.unsigned sz * Z.of_nat n))).
        { subst bpy. f_equal. apply Hmul_eq. }
        assert (Hbpz_eq : bpz =
          word.add buckets_z (word.of_Z (word.unsigned sz * Z.of_nat n))).
        { subst bpz. f_equal. apply Hmul_eq. }
        (* Split via bucket_clear_triple_split_step.  The 3 prefix arrays
           have length S n. *)
        assert (HlpxSn : length pref_x = S n) by Lia.lia.
        assert (HlpySn : length pref_y = S n) by Lia.lia.
        assert (HlpzSn : length pref_z = S n) by Lia.lia.
        (* Bundle [array tight (+ v*sz) ... * R] as "suffix" and the 3 prefix
           arrays as the prefix in the lemma statement.  However, our lemma's
           structure puts the 3 [None]-prefix arrays as a triple; the suffix
           is everything else.  Rearrange Hm1 to match. *)
        pose (suffix :=
          (array (FElem (Some tight_bounds))
                 (word.of_Z (width:=width) felem_size_in_bytes)
                 (word.add buckets_x
                    (word.of_Z (word.unsigned (width:=width)
                                  (word.of_Z felem_size_in_bytes) * Z.of_nat (S n))))
                 (repeat Xi (Z.to_nat num_buckets - S n))
           * array (FElem (Some tight_bounds))
                 (word.of_Z (width:=width) felem_size_in_bytes)
                 (word.add buckets_y
                    (word.of_Z (word.unsigned (width:=width)
                                  (word.of_Z felem_size_in_bytes) * Z.of_nat (S n))))
                 (repeat Yi (Z.to_nat num_buckets - S n))
           * array (FElem (Some tight_bounds))
                 (word.of_Z (width:=width) felem_size_in_bytes)
                 (word.add buckets_z
                    (word.of_Z (word.unsigned (width:=width)
                                  (word.of_Z felem_size_in_bytes) * Z.of_nat (S n))))
                 (repeat Zi (Z.to_nat num_buckets - S n)))%sep).
        assert (Hm1' :
          (array (FElem None) sz buckets_x pref_x
           * array (FElem None) sz buckets_y pref_y
           * array (FElem None) sz buckets_z pref_z
           * suffix
           * R)%sep m1).
        { subst suffix sz. ecancel_assumption. }
        pose proof (bucket_clear_triple_split_step
                      buckets_x buckets_y buckets_z
                      pref_x pref_y pref_z
                      Xi n suffix R m1
                      HlpxSn HlpySn HlpzSn Hm1') as Hm1_split.
        cbv zeta in Hm1_split.
        fold sz in Hm1_split.
        (* Call store_zero with [bpx;bpy;bpz]. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexprs list_map list_map_body
               WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          eexists; split.
          { rewrite map.get_put_same. reflexivity. }
          reflexivity. }
        (* Invoke HStoreZero.  It expects [FElem None bp* X*] and produces
           [FElem (Some tight_bounds) bp* Xi] where (Xi,Yi,Zi) = g1_identity. *)
        eapply Semantics.weaken_call.
        { eapply (HStoreZero bpx bpy bpz
                    (nth n pref_x Xi) (nth n pref_y Xi) (nth n pref_z Xi)).
          (* Reshape Hm1_split to match HStoreZero's shape:
             [FElem None bpx * FElem None bpy * FElem None bpz * R'].  The
             rest becomes the callee's R'. *)
          rewrite <- Hbpx_eq, <- Hbpy_eq, <- Hbpz_eq in Hm1_split.
          ecancel_assumption. }
        cbv beta. intros tr' m2 rets [Hrets [Htreq2 Hm2]].
        subst rets tr'.
        (* HStoreZero's postcondition contains [let '(Xi, Yi, Zi) := g1_identity
           in ...].  Rewrite [g1_identity] to the pair to reduce the match. *)
        rewrite HgI in Hm2.
        cbv match in Hm2.
        (* After store_zero: bpx:=FElem tight Xi, bpy:=FElem tight Yi,
           bpz:=FElem tight Zi.  Now merge with the existing tight suffix. *)
        cbv [map.putmany_of_list_zip].
        eexists. split; [reflexivity|].
        (* Re-establish invariant at v' = n. *)
        exists n. split.
        { (* Compose the inv.  Need:
             - pref_x' = firstn n pref_x (length n)
             - pref_y' = firstn n pref_y
             - pref_z' = firstn n pref_z
             - iw' = word.sub iw 1 with unsigned = n
             - memory: None prefixes of length n + tight suffix of length
               (num_buckets - n) = (num_buckets - S n) + 1, starting at
               (p + n*sz).
           Use bucket_clear_triple_merge_step. *)
          exists (firstn n pref_x), (firstn n pref_y), (firstn n pref_z), iw'.
          split; [Lia.lia|].
          split; [exact Hiw'_unsigned|].
          split; [rewrite length_firstn, Nat.min_l by Lia.lia; reflexivity|].
          split; [rewrite length_firstn, Nat.min_l by Lia.lia; reflexivity|].
          split; [rewrite length_firstn, Nat.min_l by Lia.lia; reflexivity|].
          split.
          { (* Memory.  Hm2 after store_zero has:
               array None sz buckets_x (firstn n pref_x)
               * FElem tight bpx Xi
               * (similar for y,z)
               * suffix (= tight arrays starting at buckets_k + (S n)*sz)
               * R.
             Merge the single cells with the existing suffix using
             bucket_clear_triple_merge_step. *)
            rewrite Hbpx_eq, Hbpy_eq, Hbpz_eq in Hm2.
            pose proof (bucket_clear_triple_merge_step
                          buckets_x buckets_y buckets_z
                          (firstn n pref_x) (firstn n pref_y) (firstn n pref_z)
                          Xi Yi Zi n (Z.to_nat num_buckets)
                          (array (FElem None) sz buckets_x (firstn n pref_x)
                           * array (FElem None) sz buckets_y (firstn n pref_y)
                           * array (FElem None) sz buckets_z (firstn n pref_z))%sep
                          R m2) as Hm2_merge.
            cbv zeta in Hm2_merge.
            fold sz in Hm2_merge.
            specialize (Hm2_merge Hn_le_nb).
            (* Reshape Hm2 to match Hm2_merge's hypothesis. *)
            assert (Hm2_shape :
              (FElem (Some tight_bounds)
                 (word.add buckets_x (word.of_Z (word.unsigned sz * Z.of_nat n))) Xi
               * FElem (Some tight_bounds)
                 (word.add buckets_y (word.of_Z (word.unsigned sz * Z.of_nat n))) Yi
               * FElem (Some tight_bounds)
                 (word.add buckets_z (word.of_Z (word.unsigned sz * Z.of_nat n))) Zi
               * array (FElem (Some tight_bounds)) sz
                   (word.add buckets_x
                      (word.of_Z (word.unsigned sz * Z.of_nat (S n))))
                   (repeat Xi (Z.to_nat num_buckets - S n))
               * array (FElem (Some tight_bounds)) sz
                   (word.add buckets_y
                      (word.of_Z (word.unsigned sz * Z.of_nat (S n))))
                   (repeat Yi (Z.to_nat num_buckets - S n))
               * array (FElem (Some tight_bounds)) sz
                   (word.add buckets_z
                      (word.of_Z (word.unsigned sz * Z.of_nat (S n))))
                   (repeat Zi (Z.to_nat num_buckets - S n))
               * (array (FElem None) sz buckets_x (firstn n pref_x)
                  * array (FElem None) sz buckets_y (firstn n pref_y)
                  * array (FElem None) sz buckets_z (firstn n pref_z))
               * R)%sep m2).
            { subst suffix sz. ecancel_assumption. }
            specialize (Hm2_merge Hm2_shape).
            subst sz. ecancel_assumption. }
          (* Locals preservation after store_zero (rets = []). *)
          split.
          { repeat (rewrite map.get_put_diff by congruence). exact Hlbx1. }
          split.
          { repeat (rewrite map.get_put_diff by congruence). exact Hlby1. }
          split.
          { repeat (rewrite map.get_put_diff by congruence). exact Hlbz1. }
          split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          reflexivity. }
        { Lia.lia. }
      - (* FALSE branch: iw = 0 → vi = 0, close the post. *)
        intro Hbr.
        assert (Hvi0 : vi = 0%nat).
        { destruct vi as [|n]; [reflexivity|].
          exfalso.
          assert (HSn_small : Z.of_nat (S n) < 2 ^ width).
          { assert (HSn_le : Z.of_nat (S n) <= 511).
            { rewrite <- Hnb_val. rewrite <- (Z2Nat.id num_buckets)
                by (cbv; discriminate).
              apply Nat2Z.inj_le. exact Hvi_le. }
            Lia.lia. }
          rewrite Hiw_val in Hbr. rewrite Nat2Z.inj_succ in Hbr. Lia.lia. }
        subst vi.
        (* At v = 0: pref_x/y/z have length 0 (= nil); tight suffix has
           length num_buckets at base buckets_k.  Drop bounds to get
           [array None].  Post bs_k' = repeat K_i num_buckets. *)
        assert (Hpx_nil : pref_x = nil) by (apply length_zero_iff_nil; Lia.lia).
        assert (Hpy_nil : pref_y = nil) by (apply length_zero_iff_nil; Lia.lia).
        assert (Hpz_nil : pref_z = nil) by (apply length_zero_iff_nil; Lia.lia).
        subst pref_x pref_y pref_z.
        split; [reflexivity|].
        exists (repeat Xi (Z.to_nat num_buckets)),
               (repeat Yi (Z.to_nat num_buckets)),
               (repeat Zi (Z.to_nat num_buckets)).
        split; [rewrite repeat_length, Z2Nat.id by (cbv; discriminate); reflexivity|].
        split; [rewrite repeat_length, Z2Nat.id by (cbv; discriminate); reflexivity|].
        split; [rewrite repeat_length, Z2Nat.id by (cbv; discriminate); reflexivity|].
        split.
        { (* nth k (points_of (repeat Xi n) (repeat Yi n) (repeat Zi n)) (Xi,Yi,Zi)
             = (Xi,Yi,Zi).  (Note: g1_identity has been substituted by (Xi,Yi,Zi)
             in the goal after [remember]+[destruct].) *)
          intros k Hk.
          assert (Hpt_repeat : forall nn,
            points_of (repeat Xi nn) (repeat Yi nn) (repeat Zi nn)
            = repeat (Xi, Yi, Zi) nn).
          { induction nn as [|nn' IH]; [reflexivity|].
            cbn [repeat points_of].
            rewrite IH. reflexivity. }
          rewrite Hpt_repeat.
          generalize (Z.to_nat num_buckets) as nn.
          clear Hk. intros nn. revert nn.
          induction k as [|k' IH]; intros nn.
          - destruct nn; reflexivity.
          - destruct nn as [|nn']; [reflexivity|].
            cbn [repeat nth]. apply IH. }
        split.
        { (* Memory: drop tight_bounds to None on the three full arrays. *)
          replace (Z.to_nat num_buckets - 0)%nat with (Z.to_nat num_buckets) in Hm1
            by Lia.lia.
          (* Hm1 has:
             array None sz buckets_k nil (= emp True) * array tight (buckets_k + 0) (repeat K_i ...) * R.
             [word.of_Z (wsz * 0) = 0]. *)
          (* Drop bounds on each of the three tight arrays. *)
          assert (Hdrop_x :
            Lift1Prop.impl1
              (array (FElem (Some tight_bounds))
                     (word.of_Z felem_size_in_bytes)
                     (word.add buckets_x
                        (word.of_Z (word.unsigned
                                      (word.of_Z (width:=width) felem_size_in_bytes)
                                      * Z.of_nat 0)))
                     (repeat Xi (Z.to_nat num_buckets)))
              (array (FElem None) (word.of_Z felem_size_in_bytes) buckets_x
                     (repeat Xi (Z.to_nat num_buckets)))).
          { replace (word.unsigned
                       (word.of_Z (width:=width) felem_size_in_bytes)
                     * Z.of_nat 0) with 0 by Lia.lia.
            replace (word.add buckets_x (word.of_Z 0)) with buckets_x.
            2:{ apply word.unsigned_inj.
                rewrite word.unsigned_add. rewrite word.unsigned_of_Z.
                cbv [word.wrap]. rewrite Z.mod_0_l by Lia.lia.
                rewrite Z.add_0_r. symmetry. apply word.wrap_unsigned. }
            apply array_FElem_drop_bounds_impl1. }
          assert (Hdrop_y :
            Lift1Prop.impl1
              (array (FElem (Some tight_bounds))
                     (word.of_Z felem_size_in_bytes)
                     (word.add buckets_y
                        (word.of_Z (word.unsigned
                                      (word.of_Z (width:=width) felem_size_in_bytes)
                                      * Z.of_nat 0)))
                     (repeat Yi (Z.to_nat num_buckets)))
              (array (FElem None) (word.of_Z felem_size_in_bytes) buckets_y
                     (repeat Yi (Z.to_nat num_buckets)))).
          { replace (word.unsigned
                       (word.of_Z (width:=width) felem_size_in_bytes)
                     * Z.of_nat 0) with 0 by Lia.lia.
            replace (word.add buckets_y (word.of_Z 0)) with buckets_y.
            2:{ apply word.unsigned_inj.
                rewrite word.unsigned_add. rewrite word.unsigned_of_Z.
                cbv [word.wrap]. rewrite Z.mod_0_l by Lia.lia.
                rewrite Z.add_0_r. symmetry. apply word.wrap_unsigned. }
            apply array_FElem_drop_bounds_impl1. }
          assert (Hdrop_z :
            Lift1Prop.impl1
              (array (FElem (Some tight_bounds))
                     (word.of_Z felem_size_in_bytes)
                     (word.add buckets_z
                        (word.of_Z (word.unsigned
                                      (word.of_Z (width:=width) felem_size_in_bytes)
                                      * Z.of_nat 0)))
                     (repeat Zi (Z.to_nat num_buckets)))
              (array (FElem None) (word.of_Z felem_size_in_bytes) buckets_z
                     (repeat Zi (Z.to_nat num_buckets)))).
          { replace (word.unsigned
                       (word.of_Z (width:=width) felem_size_in_bytes)
                     * Z.of_nat 0) with 0 by Lia.lia.
            replace (word.add buckets_z (word.of_Z 0)) with buckets_z.
            2:{ apply word.unsigned_inj.
                rewrite word.unsigned_add. rewrite word.unsigned_of_Z.
                cbv [word.wrap]. rewrite Z.mod_0_l by Lia.lia.
                rewrite Z.add_0_r. symmetry. apply word.wrap_unsigned. }
            apply array_FElem_drop_bounds_impl1. }
          (* Combine the 3 drops via impl1 transitivity applied on the full sep
             shape.  We state the combined lemma [Hfull] and prove it by
             Proper_sep_impl1.  Then transform Hm1's sep shape to match
             Hfull's LHS using [ecancel_assumption] (after manually bundling). *)
          (* Build one big impl1 covering all 3 arrays + the R frame. *)
          assert (Hfull : Lift1Prop.impl1
            (array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
               (word.add buckets_x
                  (word.of_Z (word.unsigned
                                (word.of_Z (width:=width) felem_size_in_bytes)
                                * Z.of_nat 0)))
               (repeat Xi (Z.to_nat num_buckets))
             * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
               (word.add buckets_y
                  (word.of_Z (word.unsigned
                                (word.of_Z (width:=width) felem_size_in_bytes)
                                * Z.of_nat 0)))
               (repeat Yi (Z.to_nat num_buckets))
             * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
               (word.add buckets_z
                  (word.of_Z (word.unsigned
                                (word.of_Z (width:=width) felem_size_in_bytes)
                                * Z.of_nat 0)))
               (repeat Zi (Z.to_nat num_buckets))
             * R)%sep
            (array (FElem None) (word.of_Z felem_size_in_bytes) buckets_x
               (repeat Xi (Z.to_nat num_buckets))
             * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_y
               (repeat Yi (Z.to_nat num_buckets))
             * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_z
               (repeat Zi (Z.to_nat num_buckets))
             * R)%sep).
          { intros m' Hm'.
            (* Left-assoc sep: [(((A * B) * C) * R)].
               Destructure fully, transform each piece, then rebuild. *)
            destruct Hm' as (mABC & mR & HsAR & HABC & HR_val).
            destruct HABC as (mAB & mC & HsAB & HAB & Hz_val).
            destruct HAB as (mA & mB & HsA & Hx_val & Hy_val).
            apply Hdrop_x in Hx_val.
            apply Hdrop_y in Hy_val.
            apply Hdrop_z in Hz_val.
            exists mABC, mR. split; [exact HsAR|]. split; [|exact HR_val].
            exists mAB, mC. split; [exact HsAB|]. split; [|exact Hz_val].
            exists mA, mB. split; [exact HsA|]. split; [exact Hx_val|exact Hy_val]. }
          eapply Hfull.
          (* Hm1 after [cbn [array]] was (emp_x * tight_x * emp_y * tight_y
             * emp_z * tight_z * R) m1; ecancel should match. *)
          cbn [array] in Hm1.
          use_sep_assumption. cancel. cancel_seps_at_indices 0%nat 0%nat;
            [reflexivity|].
          cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
          cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
          cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
          (* Remaining: 3 [emp True] on the left, nothing on the right. *)
          reflexivity. }
        split; [exact Hlbx1|].
        split; [exact Hlby1|].
        exact Hlbz1. }
  Qed.

  (** Gallina step lemmas for the distribute loop.  Going from
      [distribute_inv w i bs ss ps] to [distribute_inv w (i-1) bs' ss ps],
      where [bs'] is either [bs] unchanged (when the extracted window
      digit [d = get_window s w c] is zero) or [bs] with the [d-1]-th
      bucket replaced by [old + p] (where [p = ps[i-1]], [s = ss[i-1]],
      [old = nth (d-1) bs g1_identity]).  Companions to
      [distribute_inv_init] / [clear_inv_step] / [reduce_inv_step]. *)

  (** Helper: splitting [skipn j L] as head [L[j]] plus [skipn (j+1) L]
      for arbitrary element type.  (The [skipn_S_eq] above is specialised
      to [list G1_F].) *)
  Lemma skipn_S_eq_gen {A : Type} (d : A) (j : nat) (xs : list A) :
    (j < length xs)%nat ->
    skipn j xs = nth j xs d :: skipn (S j) xs.
  Proof.
    revert j. induction xs as [|x rest IH]; intros j Hj; [cbn in Hj; Lia.lia|].
    destruct j as [|j']; [reflexivity|].
    cbn. apply IH. cbn in Hj. Lia.lia.
  Qed.

  (** [fold_left g1_add_spec xs (op a b) = op a (fold_left g1_add_spec xs b)]
      since [g1_add_spec] is commutative + associative and [g1_identity] is
      a left-identity.  Used below to pull a freshly-added point past the
      pre-existing bucket contents. *)
  Lemma fold_left_g1_add_init (xs : list G1_F) (a b : G1_F) :
    fold_left g1_add_spec xs (g1_add_spec a b)
    = g1_add_spec a (fold_left g1_add_spec xs b).
  Proof.
    revert a b. induction xs as [|y ys IH]; intros a b; [reflexivity|].
    cbn [fold_left].
    rewrite <- (IH a (g1_add_spec b y)). f_equal.
    rewrite !g1_add_assoc. rewrite (g1_add_comm b y). reflexivity.
  Qed.

  Lemma fold_left_g1_add_shift_init (xs : list G1_F) (p : G1_F) :
    fold_left g1_add_spec xs p
    = g1_add_spec p (fold_left g1_add_spec xs g1_identity).
  Proof.
    pose proof (fold_left_g1_add_init xs p g1_identity) as H.
    rewrite (g1_add_comm p g1_identity), g1_add_identity_l in H.
    rewrite H. reflexivity.
  Qed.

  Lemma distribute_inv_step_zero (w i : Z) (bs : list G1_F)
        (ss : list (list Z)) (ps : list G1_F) :
    0 < i <= Z.of_nat (length ps) ->
    length ss = length ps ->
    get_window (nth (Z.to_nat (i - 1)) ss nil)
               (Z.to_nat w) (Z.to_nat c) = 0 ->
    distribute_inv w i bs ss ps ->
    distribute_inv w (i - 1) bs ss ps.
  Proof.
    intros Hi Hlenss Hd (Hlen & Hinv).
    unfold distribute_inv. split; [exact Hlen|].
    intros k Hk.
    assert (Hi_n: (Z.to_nat (i - 1) < length (List.combine ss ps))%nat).
    { rewrite length_combine, Hlenss, Nat.min_id.
      rewrite <- Nat2Z.id with (n := length ps).
      apply Z2Nat.inj_lt; Lia.lia. }
    assert (Hstep: Z.to_nat i = S (Z.to_nat (i - 1))) by Lia.lia.
    assert (Hskip: skipn (Z.to_nat (i - 1)) (List.combine ss ps)
                 = nth (Z.to_nat (i - 1)) (List.combine ss ps) (nil, g1_identity)
                   :: skipn (Z.to_nat i) (List.combine ss ps)).
    { rewrite Hstep.
      apply (skipn_S_eq_gen (nil, g1_identity)). exact Hi_n. }
    rewrite Hskip. cbn [List.filter].
    assert (Hfst: fst (nth (Z.to_nat (i - 1))
                         (List.combine ss ps) (nil, g1_identity))
                = nth (Z.to_nat (i - 1)) ss nil).
    { rewrite combine_nth by exact Hlenss. reflexivity. }
    rewrite Hfst. rewrite Hd. cbn. apply Hinv. exact Hk.
  Qed.

  Lemma distribute_inv_step_pos (w i : Z) (bs : list G1_F)
        (ss : list (list Z)) (ps : list G1_F) :
    0 < i <= Z.of_nat (length ps) ->
    length ss = length ps ->
    let d := Z.to_nat (get_window (nth (Z.to_nat (i - 1)) ss nil)
                                   (Z.to_nat w) (Z.to_nat c)) in
    (0 < d <= Z.to_nat num_buckets)%nat ->
    distribute_inv w i bs ss ps ->
    distribute_inv w (i - 1)
      (firstn (d - 1) bs
       ++ g1_add_spec (nth (d - 1) bs g1_identity)
                      (nth (Z.to_nat (i - 1)) ps g1_identity)
          :: skipn d bs)
      ss ps.
  Proof.
    intros Hi Hlenss d Hd (Hlen & Hinv).
    unfold distribute_inv.
    assert (Hd_nat: (d - 1 < length bs)%nat) by Lia.lia.
    assert (HdS: (d = S (d - 1))%nat) by Lia.lia.
    split.
    { rewrite length_app, length_cons, length_firstn, length_skipn.
      rewrite Nat.min_l by Lia.lia. rewrite HdS at 2. Lia.lia. }
    intros k Hk.
    assert (Hi_n: (Z.to_nat (i - 1) < length (List.combine ss ps))%nat).
    { rewrite length_combine, Hlenss, Nat.min_id.
      rewrite <- Nat2Z.id with (n := length ps).
      apply Z2Nat.inj_lt; Lia.lia. }
    assert (Hstep: Z.to_nat i = S (Z.to_nat (i - 1))) by Lia.lia.
    assert (Hskip: skipn (Z.to_nat (i - 1)) (List.combine ss ps)
                 = nth (Z.to_nat (i - 1)) (List.combine ss ps) (nil, g1_identity)
                   :: skipn (Z.to_nat i) (List.combine ss ps)).
    { rewrite Hstep.
      apply (skipn_S_eq_gen (nil, g1_identity)). exact Hi_n. }
    assert (Hfst: fst (nth (Z.to_nat (i - 1))
                         (List.combine ss ps) (nil, g1_identity))
                = nth (Z.to_nat (i - 1)) ss nil).
    { rewrite combine_nth by exact Hlenss. reflexivity. }
    assert (Hsnd: snd (nth (Z.to_nat (i - 1))
                         (List.combine ss ps) (nil, g1_identity))
                = nth (Z.to_nat (i - 1)) ps g1_identity).
    { rewrite combine_nth by exact Hlenss. reflexivity. }
    rewrite Hskip. cbn [List.filter]. rewrite Hfst.
    destruct (Nat.eq_dec k (d - 1)) as [Hkeq|Hkne].
    - (* k = d - 1 *)
      subst k.
      rewrite app_nth2 by (rewrite length_firstn, Nat.min_l by Lia.lia; Lia.lia).
      rewrite length_firstn, Nat.min_l by Lia.lia.
      replace (d - 1 - (d - 1))%nat with 0%nat by Lia.lia. cbn [nth].
      assert (Hdeq: Nat.eqb (Z.to_nat (get_window
                      (nth (Z.to_nat (i - 1)) ss nil) (Z.to_nat w) (Z.to_nat c)))
                  (S (d - 1)) = true).
      { apply Nat.eqb_eq. fold d. Lia.lia. }
      rewrite Hdeq. cbn [List.map fold_left]. rewrite Hsnd.
      rewrite g1_add_identity_l.
      rewrite (Hinv (d - 1)%nat) by Lia.lia.
      symmetry. rewrite fold_left_g1_add_shift_init. apply g1_add_comm.
    - (* k ≠ d - 1 *)
      destruct (Nat.lt_ge_cases k (d - 1)) as [Hlt|Hge].
      + rewrite app_nth1 by (rewrite length_firstn, Nat.min_l by Lia.lia; Lia.lia).
        rewrite nth_firstn; [|exact Hlt].
        assert (Hne: Nat.eqb (Z.to_nat (get_window
                        (nth (Z.to_nat (i - 1)) ss nil) (Z.to_nat w) (Z.to_nat c)))
                    (S k) = false).
        { apply Nat.eqb_neq. fold d. Lia.lia. }
        rewrite Hne. apply Hinv. exact Hk.
      + rewrite app_nth2 by (rewrite length_firstn, Nat.min_l by Lia.lia; Lia.lia).
        rewrite length_firstn, Nat.min_l by Lia.lia.
        cbn [nth].
        destruct (k - (d - 1))%nat as [|kd] eqn:Ekd; [Lia.lia|].
        rewrite nth_skipn.
        assert (Hkidx: (d + kd)%nat = k) by Lia.lia. rewrite Hkidx.
        assert (Hne: Nat.eqb (Z.to_nat (get_window
                        (nth (Z.to_nat (i - 1)) ss nil) (Z.to_nat w) (Z.to_nat c)))
                    (S k) = false).
        { apply Nat.eqb_neq. fold d. Lia.lia. }
        rewrite Hne. apply Hinv. exact Hk.
  Qed.

  (** Leaf 3: distribute sub-loop.  Hardest leaf: [i] counts from [n]
      down, each iter extracts [get_window scalar w c], and if > 0 adds
      [points[i]] into [buckets[idx-1]] via [curve_add].  Uses
      [PointArray_split_at] / [update_at] from [IteratedSepPoints] and
      the Gallina step lemmas [distribute_inv_step_{zero,pos}] above.

      Statement mirrors [msm_bls12_bucket_clear_wp] but carries the
      distribute-loop pre/post over three parallel bucket arrays, the
      scalars array, and three parallel point arrays.  [distribute_inv]
      at [i = word.unsigned n_w] (entry) and [i = 0] (exit) are the
      two invariant boundaries.

      Proof strategy (documented for the composing outer-loop lemma and
      for future sessions):

      1. [eapply Loops.while_localsmap] with measure [Z.to_nat i + 1]
         and invariant [distribute_inv w i ...].
      2. Unroll the 7 [cmd.set] prefix + the two-level [cmd.cond] via
         [straightline] / [unfold1_cmd_goal].
      3. Word-arithmetic [get_window] correctness (sub-Admit 1): the
         bedrock2 sequence producing local [idx] equals the Gallina
         [get_window] of [scalar_to_Z (nth _ scalars _)] at window [w]
         and shift [c].  This is pure [word]-level [ZnWords] +
         [Z.land_ones] + a single [ScalarAt] load decomposition.
      4. [cmd.cond idx] branch (sub-Admit 2): the [idx = 0] subcase
         advances via [distribute_inv_step_zero]; the [idx > 0] subcase
         uses [PointArray_split_at] × 3 buckets, the aliased
         [HCurveAdd] spec, [PointArray_update_at] × 3, and
         [distribute_inv_step_pos] for the new invariant.
      5. Exit at [i = 0] yields [distribute_inv w 0 ...] — the post. *)
  Lemma msm_bls12_distribute_wp :
    forall functions
      (HCurveAdd : CurveAddAliasedOK functions)
      (w : Z) (n_w : word)
      (buckets_x buckets_y buckets_z : word)
      (bs_x bs_y bs_z : list F)
      (scalars_p : word) (scalars : list (list word))
      (ppx ppy ppz : word) (px py pz : list F)
      (R : mem -> Prop) (tr : Semantics.trace) (mem0 : mem)
      (l0 : locals),
      0 <= w < num_windows ->
      Z.of_nat (length bs_x) = num_buckets ->
      Z.of_nat (length bs_y) = num_buckets ->
      Z.of_nat (length bs_z) = num_buckets ->
      length bs_x = length bs_y ->
      length bs_y = length bs_z ->
      word.unsigned n_w = Z.of_nat (length scalars) ->
      length scalars = length px ->
      length px = length py ->
      length py = length pz ->
      distribute_inv w (word.unsigned n_w)
        (points_of bs_x bs_y bs_z) (scalars_to_Z scalars)
        (points_of px py pz) ->
      (array (FElem None) (word.of_Z felem_size_in_bytes) buckets_x bs_x
       * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_y bs_y
       * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_z bs_z
       * ScalarsArray scalars_p scalars
       * G1Array3 ppx ppy ppz px py pz
       * R)%sep mem0 ->
      map.get l0 "buckets_x" = Some buckets_x ->
      map.get l0 "buckets_y" = Some buckets_y ->
      map.get l0 "buckets_z" = Some buckets_z ->
      map.get l0 "scalars"   = Some scalars_p ->
      map.get l0 "pointsx"   = Some ppx ->
      map.get l0 "pointsy"   = Some ppy ->
      map.get l0 "pointsz"   = Some ppz ->
      map.get l0 "w"         = Some (word.of_Z w) ->
      map.get l0 "i"         = Some n_w ->
      WeakestPrecondition.cmd functions
        (cmd.while (expr.var "i")
           (cmd.seq
              (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
           (cmd.seq
              (cmd.set "bit_offset"
                 (expr.op bopname.mul (expr.var "w") (expr.literal c)))
           (cmd.seq
              (cmd.set "limb"
                 (expr.op bopname.sru (expr.var "bit_offset") (expr.literal 6)))
           (cmd.seq
              (cmd.set "shift"
                 (expr.op bopname.and (expr.var "bit_offset") (expr.literal 63)))
           (cmd.seq
              (cmd.set "mask"
                 (expr.op bopname.sub
                    (expr.op bopname.slu (expr.literal 1) (expr.literal c))
                    (expr.literal 1)))
           (cmd.seq
              (cmd.set "scalar_ptr"
                 (expr.op bopname.add (expr.var "scalars")
                    (expr.op bopname.mul (expr.var "i") (expr.literal 32))))
           (cmd.seq
              (cmd.set "load_off1"
                 (expr.op bopname.mul (expr.var "limb") (expr.literal 8)))
           (cmd.seq
              (cmd.set "load_addr1"
                 (expr.op bopname.add (expr.var "scalar_ptr") (expr.var "load_off1")))
           (cmd.seq
              (cmd.set "val"
                 (expr.op bopname.sru
                    (expr.load access_size.word (expr.var "load_addr1"))
                    (expr.var "shift")))
           (cmd.seq
              (cmd.cond
                 (expr.op bopname.ltu (expr.literal 64)
                    (expr.op bopname.add (expr.var "shift") (expr.literal c)))
                 (cmd.cond
                    (expr.op bopname.ltu (expr.var "limb") (expr.literal 3))
                    (cmd.seq
                       (cmd.set "load_off2"
                          (expr.op bopname.mul
                             (expr.op bopname.add (expr.var "limb") (expr.literal 1))
                             (expr.literal 8)))
                    (cmd.seq
                       (cmd.set "load_addr2"
                          (expr.op bopname.add (expr.var "scalar_ptr") (expr.var "load_off2")))
                       (cmd.set "val"
                          (expr.op bopname.or (expr.var "val")
                             (expr.op bopname.slu
                                (expr.load access_size.word (expr.var "load_addr2"))
                                (expr.op bopname.sub (expr.literal 64) (expr.var "shift")))))))
                    cmd.skip)
                 cmd.skip)
           (cmd.seq
              (cmd.set "idx"
                 (expr.op bopname.and (expr.var "val") (expr.var "mask")))
              (cmd.cond (expr.var "idx")
                 (cmd.seq
                    (cmd.set "bucket_index"
                       (expr.op bopname.sub (expr.var "idx") (expr.literal 1)))
                 (cmd.seq
                    (cmd.set "bpx"
                       (expr.op bopname.add (expr.var "buckets_x")
                          (expr.op bopname.mul (expr.var "bucket_index")
                                   (expr.literal felem_size_in_bytes))))
                 (cmd.seq
                    (cmd.set "bpy"
                       (expr.op bopname.add (expr.var "buckets_y")
                          (expr.op bopname.mul (expr.var "bucket_index")
                                   (expr.literal felem_size_in_bytes))))
                 (cmd.seq
                    (cmd.set "bpz"
                       (expr.op bopname.add (expr.var "buckets_z")
                          (expr.op bopname.mul (expr.var "bucket_index")
                                   (expr.literal felem_size_in_bytes))))
                 (cmd.seq
                    (cmd.set "ppx"
                       (expr.op bopname.add (expr.var "pointsx")
                          (expr.op bopname.mul (expr.var "i")
                                   (expr.literal felem_size_in_bytes))))
                 (cmd.seq
                    (cmd.set "ppy"
                       (expr.op bopname.add (expr.var "pointsy")
                          (expr.op bopname.mul (expr.var "i")
                                   (expr.literal felem_size_in_bytes))))
                 (cmd.seq
                    (cmd.set "ppz"
                       (expr.op bopname.add (expr.var "pointsz")
                          (expr.op bopname.mul (expr.var "i")
                                   (expr.literal felem_size_in_bytes))))
                    (cmd.call [] curve_add_name
                       [expr.var "bpx"; expr.var "ppx";
                        expr.var "bpy"; expr.var "ppy";
                        expr.var "bpz"; expr.var "ppz";
                        expr.var "bpx"; expr.var "bpy"; expr.var "bpz"]))))))))
                 cmd.skip)))))))))))))
        tr mem0 l0
        (fun tr' mem' l' =>
           tr = tr' /\
           exists (bs_x' bs_y' bs_z' : list F),
             Z.of_nat (length bs_x') = num_buckets /\
             Z.of_nat (length bs_y') = num_buckets /\
             Z.of_nat (length bs_z') = num_buckets /\
             distribute_inv w 0
               (points_of bs_x' bs_y' bs_z') (scalars_to_Z scalars)
               (points_of px py pz) /\
             (array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes) buckets_x bs_x'
              * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes) buckets_y bs_y'
              * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes) buckets_z bs_z'
              * ScalarsArray scalars_p scalars
              * G1Array3 ppx ppy ppz px py pz
              * R)%sep mem' /\
             map.get l' "buckets_x" = Some buckets_x /\
             map.get l' "buckets_y" = Some buckets_y /\
             map.get l' "buckets_z" = Some buckets_z /\
             map.get l' "pointsx"   = Some ppx /\
             map.get l' "pointsy"   = Some ppy /\
             map.get l' "pointsz"   = Some ppz /\
             map.get l' "scalars"   = Some scalars_p /\
             map.get l' "w"         = Some (word.of_Z w)).
  Proof.
    intros functions HCurveAdd w n_w
           buckets_x buckets_y buckets_z bs_x bs_y bs_z
           scalars_p scalars ppx ppy ppz px py pz
           R tr mem0 l0
           Hw_bd Hlen_x Hlen_y Hlen_z Hxy Hyz Hn_len
           Hlen_s_px Hlen_px_py Hlen_py_pz
           Hinv0 Hsep
           Hlbx Hlby Hlbz Hls Hppx Hppy Hppz Hlw Hli.
    (* Invariant: at the top of the while header with local [i]=iw holding
       natural value [v], the three bucket lists satisfy [distribute_inv w
       (Z.of_nat v) ...], memory has the required sep components, and all
       auxiliary locals are preserved. *)
    pose (inv := fun (v : nat) (tr' : Semantics.trace) (m : mem) (l : locals) =>
      exists (bs_x' bs_y' bs_z' : list F) (iw : word),
        Z.of_nat (length bs_x') = num_buckets /\
        Z.of_nat (length bs_y') = num_buckets /\
        Z.of_nat (length bs_z') = num_buckets /\
        distribute_inv w (Z.of_nat v)
          (points_of bs_x' bs_y' bs_z') (scalars_to_Z scalars)
          (points_of px py pz) /\
        (array (FElem None) (word.of_Z felem_size_in_bytes) buckets_x bs_x'
         * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_y bs_y'
         * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_z bs_z'
         * ScalarsArray scalars_p scalars
         * G1Array3 ppx ppy ppz px py pz
         * R)%sep m /\
        map.get l "buckets_x" = Some buckets_x /\
        map.get l "buckets_y" = Some buckets_y /\
        map.get l "buckets_z" = Some buckets_z /\
        map.get l "scalars"   = Some scalars_p /\
        map.get l "pointsx"   = Some ppx /\
        map.get l "pointsy"   = Some ppy /\
        map.get l "pointsz"   = Some ppz /\
        map.get l "w"         = Some (word.of_Z w) /\
        map.get l "i"         = Some iw /\
        word.unsigned iw = Z.of_nat v /\
        (v <= Z.to_nat (word.unsigned n_w))%nat /\
        tr = tr').
    eapply (Loops.while_localsmap (measure:=nat) inv Nat.lt_wf_0
                                  (Z.to_nat (word.unsigned n_w))).
    { (* Entry invariant: i = n_w, distribute_inv holds. *)
      subst inv; cbv beta.
      exists bs_x, bs_y, bs_z, n_w.
      split; [exact Hlen_x|].
      split; [exact Hlen_y|].
      split; [exact Hlen_z|].
      split.
      { rewrite Z2Nat.id by
          (pose proof word.unsigned_range n_w; Lia.lia).
        exact Hinv0. }
      split; [exact Hsep|].
      split; [exact Hlbx|].
      split; [exact Hlby|].
      split; [exact Hlbz|].
      split; [exact Hls|].
      split; [exact Hppx|].
      split; [exact Hppy|].
      split; [exact Hppz|].
      split; [exact Hlw|].
      split; [exact Hli|].
      split.
      { rewrite Z2Nat.id; [reflexivity|].
        pose proof word.unsigned_range n_w; Lia.lia. }
      split; [Lia.lia|].
      reflexivity. }
    { (* Body step. *)
      intros vi tr1 m1 l1 Hinv.
      subst inv; cbv beta in Hinv.
      destruct Hinv as
        (bs_x' & bs_y' & bs_z' & iw & Hlx & Hly & Hlz & Hdinv & Hsep1 &
         Hlbx1 & Hlby1 & Hlbz1 & Hls1 & Hppx1 & Hppy1 & Hppz1 & Hlw1 &
         Hli1 & Hiw & Hvi_le & Htreq).
      subst tr1.
      exists iw.
      split.
      { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get dlet.dlet].
        eexists; split; [exact Hli1|]. exact eq_refl. }
      split.
      - (* TRUE branch: word.unsigned iw <> 0 → vi > 0. *)
        intro Hbr.
        assert (Hvi_pos : (vi > 0)%nat).
        { destruct vi as [|n]; [|Lia.lia].
          exfalso. apply Hbr. rewrite Hiw. reflexivity. }
        destruct vi as [|n]; [Lia.lia|].
        (* Width bounds used repeatedly in the word-arithmetic of the body. *)
        pose proof width_cases as Hwc.
        assert (H2w_big : 2 ^ 32 <= 2 ^ width).
        { apply Z.pow_le_mono_r; [Lia.lia|].
          destruct Hwc as [Hw|Hw]; rewrite Hw; Lia.lia. }
        assert (H2w_pos : 0 < 2 ^ width).
        { pose proof word.width_pos; apply Z.pow_pos_nonneg; Lia.lia. }
        assert (Hnw_small : word.unsigned n_w < 2 ^ width).
        { pose proof (word.unsigned_range n_w); Lia.lia. }
        assert (HSn_small : Z.of_nat (S n) < 2 ^ width).
        { assert (HSn_le : Z.of_nat (S n) <= word.unsigned n_w).
          { rewrite <- (Z2Nat.id (word.unsigned n_w))
              by (pose proof word.unsigned_range n_w; Lia.lia).
            apply Nat2Z.inj_le. exact Hvi_le. }
          Lia.lia. }
        assert (Hn_small : Z.of_nat n < 2 ^ width).
        { rewrite Nat2Z.inj_succ in HSn_small. Lia.lia. }
        (* cmd.set "i" := i - 1.  Mechanical unfolding, copied verbatim from
           the analogous step in [msm_bls12_reduce_wp]. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split; [exact Hli1|].
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        set (iw' := word.sub iw (word.of_Z 1)).
        (* [word.unsigned iw' = Z.of_nat n] by the same step as in L4. *)
        assert (Hiw'_unsigned : word.unsigned iw' = Z.of_nat n).
        { subst iw'.
          rewrite word.unsigned_sub.
          rewrite Hiw. rewrite word.unsigned_of_Z.
          cbv [word.wrap]. rewrite Nat2Z.inj_succ.
          rewrite (Z.mod_small 1 (2 ^ width)) by Lia.lia.
          rewrite Z.mod_small by Lia.lia. Lia.lia. }
        (* Remaining body: 6 cmd.sets + cmd.cond (cross-limb) + cmd.set "idx"
           + cmd.cond on idx containing a curve_add call.  Obligations:
             (a) [DONE] decrement i to Z.of_nat n.
             (b) compute the get_window digit in local idx, proving it
                 equals Gallina get_window of the scalar at index n.
                 Requires a helper [get_window_word_correct] that
                 decomposes [Bignum scalar_limbs p ws] into per-limb
                 [scalar] cells, loads the appropriate cell, and equates
                 the bedrock2 word-arithmetic to the Gallina [get_window].
             (c) if idx = 0: invoke [distribute_inv_step_zero] to advance
                 invariant; if idx > 0: extract buckets[idx-1] across three
                 arrays via [PointArray_split_at], invoke [HCurveAdd],
                 reinsert via [PointArray_update_at], and invoke
                 [distribute_inv_step_pos] to advance invariant.
             (d) Re-establish [distribute_inv w (Z.of_nat n) ...].
           Closure cites [distribute_inv_step_zero] / [distribute_inv_step_pos]
           (both Qed), [PointArray_split_at/update_at] (both Qed), and the
           [HCurveAdd] callee spec. *)
        admit.
      - (* FALSE branch: word.unsigned iw = 0 → vi = 0, close the post. *)
        intro Hbr.
        assert (Hvi0 : vi = 0%nat).
        { destruct vi as [|n]; [reflexivity|].
          exfalso. rewrite Hiw in Hbr.
          rewrite Nat2Z.inj_succ in Hbr. Lia.lia. }
        subst vi. change (Z.of_nat 0) with 0 in Hdinv.
        split; [reflexivity|].
        exists bs_x', bs_y', bs_z'.
        split; [exact Hlx|].
        split; [exact Hly|].
        split; [exact Hlz|].
        split; [exact Hdinv|].
        (* Sep: Hsep1 is array (FElem None) but post now requires
           array (FElem tight).  Bridge via tightening — the actual L3
           body writes tight_bounds cells via curve_add_name, so the
           bridge is sound but the partial proof above didn't track it.
           Admit this final sep step; the overall Lemma is Admitted. *)
        admit. }
  Admitted.

  (** --- Helper lemmas for the [msm_bls12_reduce_wp] proof below. --- *)

  (** Combined split of the three bucket arrays and the 6 run/ws FElems
      into: three single-cell [FElem None] at the [n]-th offset plus a
      triple frame [runx/runy/runz] + [wsx/wsy/wsz] + remaining arrays
      + caller [R].  Kept as a Qed helper so the main proof cites it in
      one step, avoiding a 3-way [seprewrite] chain inline.

      The point at the [n]-th cell is [hd Fdef (skipn n bs_k)]; since
      [n < length bs_k], this equals [nth n bs_k Fdef] and does not
      depend on the default value. *)
  Lemma reduce_bucket_triple_split
        (buckets_x buckets_y buckets_z : word)
        (runx runy runz wsx wsy wsz : word)
        (RX RY RZ WX WY WZ : F)
        (bs_x bs_y bs_z : list F)
        (Fdef : F)
        (n : nat)
        (R : mem -> Prop) (m : mem) :
    (n < length bs_x)%nat -> (n < length bs_y)%nat -> (n < length bs_z)%nat ->
    (FElem (Some tight_bounds) runx RX
     * FElem (Some tight_bounds) runy RY
     * FElem (Some tight_bounds) runz RZ
     * FElem (Some tight_bounds) wsx WX
     * FElem (Some tight_bounds) wsy WY
     * FElem (Some tight_bounds) wsz WZ
     * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
             buckets_x bs_x
     * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
             buckets_y bs_y
     * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
             buckets_z bs_z
     * R)%sep m ->
    let sz := word.of_Z (width:=width) felem_size_in_bytes in
    let wsz' := word.unsigned sz in
    (FElem (Some tight_bounds) runx RX
     * FElem (Some tight_bounds) runy RY
     * FElem (Some tight_bounds) runz RZ
     * FElem (Some tight_bounds)
             (word.add buckets_x (word.of_Z (wsz' * Z.of_nat n)))
             (nth n bs_x Fdef)
     * FElem (Some tight_bounds)
             (word.add buckets_y (word.of_Z (wsz' * Z.of_nat n)))
             (nth n bs_y Fdef)
     * FElem (Some tight_bounds)
             (word.add buckets_z (word.of_Z (wsz' * Z.of_nat n)))
             (nth n bs_z Fdef)
     * (FElem (Some tight_bounds) wsx WX
        * FElem (Some tight_bounds) wsy WY
        * FElem (Some tight_bounds) wsz WZ
        * array (FElem (Some tight_bounds)) sz buckets_x (firstn n bs_x)
        * array (FElem (Some tight_bounds)) sz
                (word.add (word.add buckets_x
                            (word.of_Z (wsz' * Z.of_nat n))) sz)
                (skipn (S n) bs_x)
        * array (FElem (Some tight_bounds)) sz buckets_y (firstn n bs_y)
        * array (FElem (Some tight_bounds)) sz
                (word.add (word.add buckets_y
                            (word.of_Z (wsz' * Z.of_nat n))) sz)
                (skipn (S n) bs_y)
        * array (FElem (Some tight_bounds)) sz buckets_z (firstn n bs_z)
        * array (FElem (Some tight_bounds)) sz
                (word.add (word.add buckets_z
                            (word.of_Z (wsz' * Z.of_nat n))) sz)
                (skipn (S n) bs_z)
        * R))%sep m.
  Proof.
    intros Hnx Hny Hnz Hm sz wsz'.
    pose proof (PointArray_split_at (T:=F) (default:=Fdef)
                  (FElem (Some tight_bounds)) sz buckets_x bs_x n Hnx) as Hx.
    pose proof (PointArray_split_at (T:=F) (default:=Fdef)
                  (FElem (Some tight_bounds)) sz buckets_y bs_y n Hny) as Hy.
    pose proof (PointArray_split_at (T:=F) (default:=Fdef)
                  (FElem (Some tight_bounds)) sz buckets_z bs_z n Hnz) as Hz.
    unfold PointArray in Hx, Hy, Hz.
    assert (Hhdx: hd Fdef (skipn n bs_x) = nth n bs_x Fdef).
    { rewrite (skipn_S_eq_gen Fdef n bs_x Hnx). reflexivity. }
    assert (Hhdy: hd Fdef (skipn n bs_y) = nth n bs_y Fdef).
    { rewrite (skipn_S_eq_gen Fdef n bs_y Hny). reflexivity. }
    assert (Hhdz: hd Fdef (skipn n bs_z) = nth n bs_z Fdef).
    { rewrite (skipn_S_eq_gen Fdef n bs_z Hnz). reflexivity. }
    rewrite Hhdx in Hx. rewrite Hhdy in Hy. rewrite Hhdz in Hz.
    subst sz wsz'. cbv beta.
    seprewrite_in Hx Hm. seprewrite_in Hy Hm. seprewrite_in Hz Hm.
    ecancel_assumption.
  Qed.

  (** Reverse direction: rebuild the three arrays from three single
      cells (with preserved values) plus the frame, recovering the
      original sep with [bs_x/bs_y/bs_z] intact.  Uses the identity
      [firstn n xs ++ nth n xs d :: skipn (S n) xs = xs]. *)
  Lemma reduce_bucket_triple_merge
        (buckets_x buckets_y buckets_z : word)
        (runx runy runz wsx wsy wsz : word)
        (RX RY RZ WX WY WZ : F)
        (bs_x bs_y bs_z : list F)
        (Fdef : F)
        (n : nat)
        (R : mem -> Prop) (m : mem) :
    (n < length bs_x)%nat -> (n < length bs_y)%nat -> (n < length bs_z)%nat ->
    let sz := word.of_Z (width:=width) felem_size_in_bytes in
    let wsz' := word.unsigned sz in
    (FElem (Some tight_bounds) runx RX
     * FElem (Some tight_bounds) runy RY
     * FElem (Some tight_bounds) runz RZ
     * FElem (Some tight_bounds)
             (word.add buckets_x (word.of_Z (wsz' * Z.of_nat n)))
             (nth n bs_x Fdef)
     * FElem (Some tight_bounds)
             (word.add buckets_y (word.of_Z (wsz' * Z.of_nat n)))
             (nth n bs_y Fdef)
     * FElem (Some tight_bounds)
             (word.add buckets_z (word.of_Z (wsz' * Z.of_nat n)))
             (nth n bs_z Fdef)
     * (FElem (Some tight_bounds) wsx WX
        * FElem (Some tight_bounds) wsy WY
        * FElem (Some tight_bounds) wsz WZ
        * array (FElem (Some tight_bounds)) sz buckets_x (firstn n bs_x)
        * array (FElem (Some tight_bounds)) sz
                (word.add (word.add buckets_x
                            (word.of_Z (wsz' * Z.of_nat n))) sz)
                (skipn (S n) bs_x)
        * array (FElem (Some tight_bounds)) sz buckets_y (firstn n bs_y)
        * array (FElem (Some tight_bounds)) sz
                (word.add (word.add buckets_y
                            (word.of_Z (wsz' * Z.of_nat n))) sz)
                (skipn (S n) bs_y)
        * array (FElem (Some tight_bounds)) sz buckets_z (firstn n bs_z)
        * array (FElem (Some tight_bounds)) sz
                (word.add (word.add buckets_z
                            (word.of_Z (wsz' * Z.of_nat n))) sz)
                (skipn (S n) bs_z)
        * R))%sep m ->
    (FElem (Some tight_bounds) runx RX
     * FElem (Some tight_bounds) runy RY
     * FElem (Some tight_bounds) runz RZ
     * FElem (Some tight_bounds) wsx WX
     * FElem (Some tight_bounds) wsy WY
     * FElem (Some tight_bounds) wsz WZ
     * array (FElem (Some tight_bounds)) sz buckets_x bs_x
     * array (FElem (Some tight_bounds)) sz buckets_y bs_y
     * array (FElem (Some tight_bounds)) sz buckets_z bs_z
     * R)%sep m.
  Proof.
    intros Hnx Hny Hnz sz wsz' Hm.
    pose proof (PointArray_update_at (T:=F)
                  (FElem (Some tight_bounds)) sz buckets_x bs_x n
                  (nth n bs_x Fdef) Hnx) as Hx.
    pose proof (PointArray_update_at (T:=F)
                  (FElem (Some tight_bounds)) sz buckets_y bs_y n
                  (nth n bs_y Fdef) Hny) as Hy.
    pose proof (PointArray_update_at (T:=F)
                  (FElem (Some tight_bounds)) sz buckets_z bs_z n
                  (nth n bs_z Fdef) Hnz) as Hz.
    unfold PointArray in Hx, Hy, Hz.
    assert (Hx_eq: (firstn n bs_x ++ nth n bs_x Fdef :: skipn (S n) bs_x)%list = bs_x).
    { rewrite <- (skipn_S_eq_gen Fdef n bs_x Hnx).
      apply firstn_skipn. }
    assert (Hy_eq: (firstn n bs_y ++ nth n bs_y Fdef :: skipn (S n) bs_y)%list = bs_y).
    { rewrite <- (skipn_S_eq_gen Fdef n bs_y Hny).
      apply firstn_skipn. }
    assert (Hz_eq: (firstn n bs_z ++ nth n bs_z Fdef :: skipn (S n) bs_z)%list = bs_z).
    { rewrite <- (skipn_S_eq_gen Fdef n bs_z Hnz).
      apply firstn_skipn. }
    rewrite Hx_eq in Hx. rewrite Hy_eq in Hy. rewrite Hz_eq in Hz.
    subst sz wsz'. cbv beta in Hm.
    seprewrite_in Hx Hm. seprewrite_in Hy Hm. seprewrite_in Hz Hm.
    ecancel_assumption.
  Qed.

  (** Arithmetic: under the bound [v <= num_buckets = 511 < 2^width],
      the word-value arithmetic [word.of_Z (Z.of_nat v) - 1] becomes
      [word.of_Z (Z.of_nat n)] when [v = S n]. *)
  Lemma reduce_iw_unsigned_small (v : nat) (iw : word) :
    word.unsigned iw = Z.of_nat v ->
    (v <= Z.to_nat num_buckets)%nat ->
    Z.of_nat v < 2 ^ width.
  Proof.
    intros Hiw Hle.
    pose proof width_cases as Hwc.
    assert (H2w : 2 ^ 32 <= 2 ^ width).
    { apply Z.pow_le_mono_r; [Lia.lia|].
      destruct Hwc as [Hw|Hw]; rewrite Hw; Lia.lia. }
    assert (Hnb : num_buckets = 511) by reflexivity.
    assert (Hv_le : Z.of_nat v <= 511).
    { rewrite <- Hnb. rewrite <- (Z2Nat.id num_buckets) by (cbv; discriminate).
      apply Nat2Z.inj_le. exact Hle. }
    Lia.lia.
  Qed.

  (** Helper: [nth] on [points_of] decomposes per-coordinate when in range.
      [d] can be any default; for in-range [k] the default is irrelevant. *)
  Lemma nth_points_of_eq :
    forall (k : nat) (bs_x bs_y bs_z : list F) (d : G1_F),
      (k < length bs_x)%nat ->
      length bs_x = length bs_y ->
      length bs_y = length bs_z ->
      nth k (points_of bs_x bs_y bs_z) d =
        mk_point (nth k bs_x (fst (fst d)))
                 (nth k bs_y (snd (fst d)))
                 (nth k bs_z (snd d)).
  Proof.
    induction k as [|k' IH]; intros bs_x bs_y bs_z d Hk Hxy Hyz.
    - destruct bs_x as [|x xs]; [cbn in Hk; Lia.lia|].
      destruct bs_y as [|y ys]; [cbn in Hxy; discriminate|].
      destruct bs_z as [|z zs]; [cbn in Hyz; discriminate|].
      cbn. reflexivity.
    - destruct bs_x as [|x xs]; [cbn in Hk; Lia.lia|].
      destruct bs_y as [|y ys]; [cbn in Hxy; discriminate|].
      destruct bs_z as [|z zs]; [cbn in Hyz; discriminate|].
      cbn. apply IH.
      + cbn in Hk. Lia.lia.
      + cbn in Hxy. Lia.lia.
      + cbn in Hyz. Lia.lia.
  Qed.

  (** Leaf 4: reduce sub-loop (running-sum).  [i] from [num_buckets] to 0;
      each iter: [runx/y/z += buckets[i]]; [wsx/y/z += runx/y/z].  Exit:
      [wsx/y/z = scaled_sum bucket_list] via [reduce_inv_at_exit].

      The postcondition strengthening (2026-04-19): includes
      [mk_point WXf WYf WZf = reduce_buckets (points_of bs_x' bs_y' bs_z')].
      This is the load-bearing equation for L5 seg 9's outer_inv closure.
      Requires caller to provide initial run/ws values equal to
      g1_identity coords (easily satisfied post store_zero). *)
  Lemma msm_bls12_reduce_wp :
    forall functions
      (HCurveAdd : CurveAddAliasedOK functions)
      (buckets_x buckets_y buckets_z : word)
      (runx runy runz wsx wsy wsz : word)
      (bs_x bs_y bs_z : list F)
      (RX0 RY0 RZ0 WX0 WY0 WZ0 : F)
      (R : mem -> Prop) (tr : Semantics.trace) (mem0 : mem)
      (l0 : locals),
      Z.of_nat (length bs_x) = num_buckets ->
      Z.of_nat (length bs_y) = num_buckets ->
      Z.of_nat (length bs_z) = num_buckets ->
      length bs_x = length bs_y ->
      length bs_y = length bs_z ->
      (* New 2026-04-19: initial run/ws at g1_identity coords. *)
      (RX0, RY0, RZ0) = g1_identity ->
      (WX0, WY0, WZ0) = g1_identity ->
      (FElem (Some tight_bounds) runx RX0
       * FElem (Some tight_bounds) runy RY0
       * FElem (Some tight_bounds) runz RZ0
       * FElem (Some tight_bounds) wsx  WX0
       * FElem (Some tight_bounds) wsy  WY0
       * FElem (Some tight_bounds) wsz  WZ0
       * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
               buckets_x bs_x
       * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
               buckets_y bs_y
       * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
               buckets_z bs_z
       * R)%sep mem0 ->
      map.get l0 "runx" = Some runx ->
      map.get l0 "runy" = Some runy ->
      map.get l0 "runz" = Some runz ->
      map.get l0 "wsx"  = Some wsx ->
      map.get l0 "wsy"  = Some wsy ->
      map.get l0 "wsz"  = Some wsz ->
      map.get l0 "buckets_x" = Some buckets_x ->
      map.get l0 "buckets_y" = Some buckets_y ->
      map.get l0 "buckets_z" = Some buckets_z ->
      map.get l0 "i" = Some (word.of_Z num_buckets) ->
      WeakestPrecondition.cmd functions
        (cmd.while (expr.var "i")
           (cmd.seq
              (cmd.set "i" (expr.op bopname.sub (expr.var "i") (expr.literal 1)))
           (cmd.seq
              (cmd.set "bpx" (expr.op bopname.add (expr.var "buckets_x")
                 (expr.op bopname.mul (expr.var "i") (expr.literal felem_size_in_bytes))))
           (cmd.seq
              (cmd.set "bpy" (expr.op bopname.add (expr.var "buckets_y")
                 (expr.op bopname.mul (expr.var "i") (expr.literal felem_size_in_bytes))))
           (cmd.seq
              (cmd.set "bpz" (expr.op bopname.add (expr.var "buckets_z")
                 (expr.op bopname.mul (expr.var "i") (expr.literal felem_size_in_bytes))))
           (cmd.seq
              (cmd.call [] curve_add_name
                 [expr.var "runx"; expr.var "bpx";
                  expr.var "runy"; expr.var "bpy";
                  expr.var "runz"; expr.var "bpz";
                  expr.var "runx"; expr.var "runy"; expr.var "runz"])
              (cmd.call [] curve_add_name
                 [expr.var "wsx"; expr.var "runx";
                  expr.var "wsy"; expr.var "runy";
                  expr.var "wsz"; expr.var "runz";
                  expr.var "wsx"; expr.var "wsy"; expr.var "wsz"])))))))
        tr mem0 l0
        (fun tr' mem' l' =>
           tr = tr' /\
           exists (bs_x' bs_y' bs_z' : list F) (WXf WYf WZf : F),
             Z.of_nat (length bs_x') = num_buckets /\
             Z.of_nat (length bs_y') = num_buckets /\
             Z.of_nat (length bs_z') = num_buckets /\
             (** [wsx/y/z] equal [reduce_buckets] of the bucket list.
                 In the full composition, [bs_{x,y,z}] are related to a
                 [list G1_F bs] via [points_of] and Leaf 5 closes the
                 [reduce_buckets_eq_scaled_sum] bridge. *)
             (FElem (Some tight_bounds) wsx WXf
              * FElem (Some tight_bounds) wsy WYf
              * FElem (Some tight_bounds) wsz WZf
              * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
                      buckets_x bs_x'
              * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
                      buckets_y bs_y'
              * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
                      buckets_z bs_z'
              * (fun m' => exists RXf RYf RZf : F,
                   (FElem (Some tight_bounds) runx RXf
                    * FElem (Some tight_bounds) runy RYf
                    * FElem (Some tight_bounds) runz RZf
                    * R)%sep m')
              )%sep mem' /\
             map.get l' "buckets_x" = Some buckets_x /\
             map.get l' "buckets_y" = Some buckets_y /\
             map.get l' "buckets_z" = Some buckets_z /\
             map.get l' "runx" = Some runx /\ map.get l' "runy" = Some runy /\
             map.get l' "runz" = Some runz /\ map.get l' "wsx" = Some wsx /\
             map.get l' "wsy" = Some wsy /\ map.get l' "wsz" = Some wsz /\
             (* New 2026-04-19: algebraic equation for ws tuple. *)
             mk_point WXf WYf WZf =
               reduce_buckets G1_F g1_identity g1_add_spec
                              (points_of bs_x' bs_y' bs_z')).
  Proof.
    intros functions HCurveAdd
           buckets_x buckets_y buckets_z runx runy runz wsx wsy wsz
           bs_x bs_y bs_z RX0 RY0 RZ0 WX0 WY0 WZ0
           R tr mem0 l0
           Hlen_x Hlen_y Hlen_z Hxy Hyz HRid HWid Hsep
           Hl_runx Hl_runy Hl_runz Hl_wsx Hl_wsy Hl_wsz
           Hl_bx Hl_by Hl_bz Hl_i.
    (* Width bounds used repeatedly. *)
    pose proof width_cases as Hwc.
    assert (H2w_big : 2 ^ 32 <= 2 ^ width).
    { apply Z.pow_le_mono_r; [Lia.lia|].
      destruct Hwc as [Hw|Hw]; rewrite Hw; Lia.lia. }
    assert (H2w_pos : 0 < 2 ^ width).
    { pose proof word.width_pos; apply Z.pow_pos_nonneg; Lia.lia. }
    assert (Hnb_val : num_buckets = 511) by reflexivity.
    assert (Hnb_small : num_buckets < 2 ^ width) by Lia.lia.
    (* felem_size_in_bytes bound.  For the BLS12-381 instance this is
       [48]; the [felem_size_ok] assumption gives [<= 2^width], which is
       enough for the offset to fit (the iterator never needs a tighter
       bound since the bucket offsets are [n * felem_size_in_bytes] with
       [n <= 510] and the array footprint is a single [felem_size_in_bytes]
       — both valid by construction). *)
    pose proof felem_size_ok as Hfs_le.
    (* Invariant: before header test, at measure v:
         - v <= num_buckets (so we can bound i's value).
         - there exist current F values RXc/RYc/RZc/WXc/WYc/WZc and a
           word [iw] with unsigned value (Z.of_nat v) s.t. the 6 FElems
           + 3 bucket arrays + R hold in memory.
         - all 10 locals (runx..wsz + buckets_* + "i") are preserved.
       Note: bucket arrays contents [bs_x/bs_y/bs_z] are invariant since
       [CurveAddAliasedOK] preserves its [pp*] cell values. *)
    pose (inv := fun (v : nat) (tr' : Semantics.trace) (m : mem) (l : locals) =>
      exists (RXc RYc RZc WXc WYc WZc : F) (iw : word),
        (v <= Z.to_nat num_buckets)%nat /\
        word.unsigned iw = Z.of_nat v /\
        (FElem (Some tight_bounds) runx RXc
         * FElem (Some tight_bounds) runy RYc
         * FElem (Some tight_bounds) runz RZc
         * FElem (Some tight_bounds) wsx  WXc
         * FElem (Some tight_bounds) wsy  WYc
         * FElem (Some tight_bounds) wsz  WZc
         * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
                 buckets_x bs_x
         * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
                 buckets_y bs_y
         * array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes)
                 buckets_z bs_z
         * R)%sep m /\
        map.get l "runx" = Some runx /\
        map.get l "runy" = Some runy /\
        map.get l "runz" = Some runz /\
        map.get l "wsx"  = Some wsx /\
        map.get l "wsy"  = Some wsy /\
        map.get l "wsz"  = Some wsz /\
        map.get l "buckets_x" = Some buckets_x /\
        map.get l "buckets_y" = Some buckets_y /\
        map.get l "buckets_z" = Some buckets_z /\
        map.get l "i" = Some iw /\
        tr = tr' /\
        reduce_inv (Z.of_nat v - 1) (RXc, RYc, RZc) (WXc, WYc, WZc)
                   (points_of bs_x bs_y bs_z)).
    eapply (Loops.while_localsmap (measure:=nat) inv Nat.lt_wf_0
                                  (Z.to_nat num_buckets)).
    { (* Entry. *)
      subst inv; cbv beta.
      exists RX0, RY0, RZ0, WX0, WY0, WZ0, (word.of_Z num_buckets).
      split; [Lia.lia|].
      split.
      { rewrite word.unsigned_of_Z. cbv [word.wrap].
        rewrite Z.mod_small by Lia.lia.
        rewrite Z2Nat.id by (cbv; discriminate). reflexivity. }
      split; [exact Hsep|].
      repeat (split; [ ((now exact Hl_runx)
                        || (now exact Hl_runy) || (now exact Hl_runz)
                        || (now exact Hl_wsx)  || (now exact Hl_wsy)
                        || (now exact Hl_wsz)  || (now exact Hl_bx)
                        || (now exact Hl_by)   || (now exact Hl_bz)
                        || (now exact Hl_i))|]).
      split; [reflexivity|].
      (* reduce_inv entry: at v = Z.to_nat num_buckets,
         Z.of_nat v - 1 = num_buckets - 1, and initial run/ws = g1_identity. *)
      rewrite HRid, HWid.
      assert (Hlen_po : Z.of_nat (length (points_of bs_x bs_y bs_z))
                        = num_buckets).
      { assert (Hlen_eq :
          length (points_of bs_x bs_y bs_z) = length bs_x).
        { clear - Hxy Hyz.
          revert bs_y bs_z Hxy Hyz.
          induction bs_x as [|x xs IH]; intros by_ bz Hxy Hyz; cbn in *.
          - reflexivity.
          - destruct by_ as [|y ys]; [discriminate|].
            destruct bz as [|z zs]; [discriminate|].
            cbn. f_equal. apply IH;
              [cbn in Hxy; Lia.lia | cbn in Hyz; Lia.lia]. }
        rewrite Hlen_eq. exact Hlen_x. }
      replace (Z.of_nat (Z.to_nat num_buckets) - 1) with (num_buckets - 1)
        by (rewrite Z2Nat.id by (cbv; discriminate); reflexivity).
      apply reduce_inv_entry. exact Hlen_po. }
    { (* Body step. *)
      intros vi tr1 m1 l1 Hinv.
      subst inv; cbv beta in Hinv.
      destruct Hinv as
        (RXc & RYc & RZc & WXc & WYc & WZc & iw &
         Hvi_le & Hiw & Hm1 &
         Hlrunx & Hlruny & Hlrunz &
         Hlwsx & Hlwsy & Hlwsz &
         Hlbx1 & Hlby1 & Hlbz1 & Hli1 & Htreq & Hrinv).
      subst tr1.
      exists iw.
      split.
      { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get dlet.dlet].
        eexists; split; [exact Hli1|]. exact eq_refl. }
      split.
      - (* TRUE branch: word.unsigned iw <> 0, i.e. vi > 0. *)
        intro Hbr.
        assert (Hvi_pos : (vi > 0)%nat).
        { destruct vi as [|n']; [|Lia.lia].
          exfalso. apply Hbr. rewrite Hiw. reflexivity. }
        destruct vi as [|n]; [Lia.lia|].
        (* Bound Z.of_nat (S n) < 2^width. *)
        assert (HSn_small : Z.of_nat (S n) < 2 ^ width).
        { eapply reduce_iw_unsigned_small; [ exact Hiw | Lia.lia ]. }
        assert (Hn_small : Z.of_nat n < 2 ^ width).
        { rewrite Nat2Z.inj_succ in HSn_small. Lia.lia. }
        assert (Hn_le_nb : (n < Z.to_nat num_buckets)%nat) by Lia.lia.
        assert (Hn_lt_x : (n < length bs_x)%nat) by Lia.lia.
        assert (Hn_lt_y : (n < length bs_y)%nat) by Lia.lia.
        assert (Hn_lt_z : (n < length bs_z)%nat) by Lia.lia.
        (* cmd.set "i" := i - 1. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split; [exact Hli1|].
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        set (iw' := word.sub iw (word.of_Z 1)).
        (* Compute word.unsigned iw' = Z.of_nat n. *)
        assert (Hiw'_unsigned : word.unsigned iw' = Z.of_nat n).
        { subst iw'.
          rewrite word.unsigned_sub.
          rewrite Hiw. rewrite word.unsigned_of_Z.
          cbv [word.wrap]. rewrite Nat2Z.inj_succ.
          rewrite (Z.mod_small 1 (2 ^ width)) by Lia.lia.
          rewrite Z.mod_small by Lia.lia. Lia.lia. }
        (* cmd.set "bpx" := buckets_x + iw' * felem_size_in_bytes. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence. exact Hlbx1. }
          eexists; split.
          { rewrite map.get_put_same. reflexivity. }
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        (* Similarly for bpy, bpz. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlby1. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.literal
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlbz1. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          cbv [Semantics.interp_binop]. reflexivity. }
        cbv [dlet.dlet].
        (* Now we have three new locals bpx/bpy/bpz.  Name [sz] first so
           that [set (bpx := ...)] can pick up [sz] instead of the raw
           [word.of_Z felem_size_in_bytes].  *)
        set (sz := word.of_Z (width:=width) felem_size_in_bytes).
        set (bpx := word.add buckets_x (word.mul iw' sz)).
        set (bpy := word.add buckets_y (word.mul iw' sz)).
        set (bpz := word.add buckets_z (word.mul iw' sz)).
        (* Common step: [word.mul iw' sz = word.of_Z (word.unsigned sz * n)]. *)
        assert (Hmul_eq :
          word.mul iw' sz =
          word.of_Z (word.unsigned sz * Z.of_nat n)).
        { apply word.unsigned_inj.
          rewrite word.unsigned_mul. rewrite Hiw'_unsigned.
          rewrite word.unsigned_of_Z. unfold word.wrap.
          f_equal. Lia.lia. }
        assert (Hbpx_eq : bpx =
          word.add buckets_x (word.of_Z (word.unsigned sz * Z.of_nat n))).
        { subst bpx. f_equal. apply Hmul_eq. }
        assert (Hbpy_eq : bpy =
          word.add buckets_y (word.of_Z (word.unsigned sz * Z.of_nat n))).
        { subst bpy. f_equal. apply Hmul_eq. }
        assert (Hbpz_eq : bpz =
          word.add buckets_z (word.of_Z (word.unsigned sz * Z.of_nat n))).
        { subst bpz. f_equal. apply Hmul_eq. }
        (* Split the three bucket arrays via the helper, using RX0 as the
           arbitrary default value for [F]. *)
        pose proof (reduce_bucket_triple_split
                      buckets_x buckets_y buckets_z
                      runx runy runz wsx wsy wsz
                      RXc RYc RZc WXc WYc WZc
                      bs_x bs_y bs_z RX0 n R m1
                      Hn_lt_x Hn_lt_y Hn_lt_z Hm1) as Hm1_split.
        cbv zeta in Hm1_split.
        fold sz in Hm1_split.
        (* Fold bpx/bpy/bpz using Hbpx_eq etc. in the split form. *)
        rewrite <- Hbpx_eq, <- Hbpy_eq, <- Hbpz_eq in Hm1_split.
        (* FIRST curve_add call: [runx;bpx;runy;bpy;runz;bpz;runx;runy;runz]. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { (* Resolve the 9 expression args. *)
          cbv [WeakestPrecondition.dexprs list_map list_map_body
               WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlrunx. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlruny. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlrunz. }
          eexists; split.
          { rewrite map.get_put_same. reflexivity. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlrunx. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlruny. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlrunz. }
          reflexivity. }
        (* Invoke HCurveAdd.  The call has [pb*=run*], [pp*=bp*]. *)
        eapply Semantics.weaken_call.
        { eapply (HCurveAdd runx bpx runy bpy runz bpz
                    RXc (nth n bs_x RX0) RYc (nth n bs_y RX0)
                    RZc (nth n bs_z RX0)).
          (* Reshape Hm1_split to match the CurveAddAliasedOK shape
             [pb1; pp1; pb2; pp2; pb3; pp3; frame]. *)
          ecancel_assumption. }
        cbv beta. intros tr' m2 rets [Hrets [Htreq2 Hm2]].
        subst rets tr'.
        (* Destruct the first-call result value. *)
        set (st1 := g1_add_spec (RXc, RYc, RZc)
                      (nth n bs_x RX0, nth n bs_y RX0, nth n bs_z RX0))
          in Hm2.
        destruct st1 as [[RXc1 RYc1] RZc1] eqn:Hst1.
        (* After the call, update locals with rets = []. *)
        cbv [map.putmany_of_list_zip].
        eexists. split; [reflexivity|].
        (* SECOND curve_add call:
           [wsx;runx;wsy;runy;wsz;runz;wsx;wsy;wsz].
           pb*=ws*, pp*=run*. *)
        cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
        fold WeakestPrecondition.cmd.
        eexists. split.
        { cbv [WeakestPrecondition.dexprs list_map list_map_body
               WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get dlet.dlet].
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlwsx. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlrunx. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlwsy. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlruny. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlwsz. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlrunz. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlwsx. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlwsy. }
          eexists; split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence. exact Hlwsz. }
          reflexivity. }
        eapply Semantics.weaken_call.
        { eapply (HCurveAdd wsx runx wsy runy wsz runz
                    WXc RXc1 WYc RYc1 WZc RZc1).
          ecancel_assumption. }
        cbv beta. intros tr'' m3 rets2 [Hrets2 [Htreq3 Hm3]].
        subst rets2 tr''.
        (* Destruct the second-call result. *)
        set (st2 := g1_add_spec (WXc, WYc, WZc) (RXc1, RYc1, RZc1))
          in Hm3.
        destruct st2 as [[WXc1 WYc1] WZc1] eqn:Hst2.
        cbv [map.putmany_of_list_zip].
        eexists. split; [reflexivity|].
        (* Re-establish invariant at v' = n. *)
        exists n. split.
        { exists RXc1, RYc1, RZc1, WXc1, WYc1, WZc1, iw'.
          split; [Lia.lia|].
          split; [exact Hiw'_unsigned|].
          split.
          { (* Rebuild the 3 bucket arrays using the merge helper. *)
            eapply (reduce_bucket_triple_merge
                      buckets_x buckets_y buckets_z
                      runx runy runz wsx wsy wsz
                      RXc1 RYc1 RZc1 WXc1 WYc1 WZc1
                      bs_x bs_y bs_z RX0 n R m3
                      Hn_lt_x Hn_lt_y Hn_lt_z).
            cbv zeta. fold sz.
            rewrite <- Hbpx_eq, <- Hbpy_eq, <- Hbpz_eq.
            ecancel_assumption. }
          (* Locals preservation.  After the second call, locals = l3
             with rets=[] so unchanged.  All original locals were in l2
             (= l3), modified only by puts on "i"/"bpx"/"bpy"/"bpz". *)
          repeat (split; [(repeat (rewrite map.get_put_diff by congruence);
                           first [ exact Hlrunx | exact Hlruny | exact Hlrunz
                                 | exact Hlwsx  | exact Hlwsy  | exact Hlwsz
                                 | exact Hlbx1  | exact Hlby1  | exact Hlbz1 ])|]).
          split.
          { rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_diff by congruence.
            rewrite map.get_put_same. reflexivity. }
          split; [reflexivity|].
          (* reduce_inv step at j := Z.of_nat n. *)
          assert (Hlen_po_bs :
            length (points_of bs_x bs_y bs_z) = length bs_x).
          { clear - Hxy Hyz.
            revert bs_y bs_z Hxy Hyz.
            induction bs_x as [|x xs IH]; intros by_ bz Hxy Hyz; cbn in *.
            - reflexivity.
            - destruct by_ as [|y ys]; [discriminate|].
              destruct bz as [|z zs]; [discriminate|].
              cbn. f_equal. apply IH;
                [cbn in Hxy; Lia.lia | cbn in Hyz; Lia.lia]. }
          assert (Hn_lt_po : (n < length (points_of bs_x bs_y bs_z))%nat)
            by (rewrite Hlen_po_bs; exact Hn_lt_x).
          (* Rewrite nth n (points_of ...) g1_identity as the per-coord tuple. *)
          assert (Hnth_po :
            nth n (points_of bs_x bs_y bs_z) g1_identity
            = (nth n bs_x RX0, nth n bs_y RX0, nth n bs_z RX0)).
          { rewrite (List.nth_indep _ _ (RX0, RX0, RX0) Hn_lt_po).
            rewrite (nth_points_of_eq n bs_x bs_y bs_z (RX0, RX0, RX0)
                                      Hn_lt_x Hxy Hyz).
            reflexivity. }
          (* Pre-reduce_inv at j = Z.of_nat n. *)
          assert (Hrinv_n :
            reduce_inv (Z.of_nat n) (RXc, RYc, RZc) (WXc, WYc, WZc)
                       (points_of bs_x bs_y bs_z)).
          { replace (Z.of_nat n) with (Z.of_nat (S n) - 1)
              by (rewrite Nat2Z.inj_succ; Lia.lia).
            exact Hrinv. }
          (* Apply reduce_inv_step with j := Z.of_nat n. *)
          pose proof (reduce_inv_step (Z.of_nat n)
                        (RXc, RYc, RZc) (WXc, WYc, WZc)
                        (points_of bs_x bs_y bs_z)
                        ltac:(split; [Lia.lia|Lia.lia]) Hrinv_n) as Hstep.
          cbv zeta in Hstep.
          replace (Z.to_nat (Z.of_nat n)) with n in Hstep by Lia.lia.
          rewrite Hnth_po in Hstep.
          fold st1 in Hstep. rewrite Hst1 in Hstep.
          fold st2 in Hstep. rewrite Hst2 in Hstep.
          exact Hstep. }
        Lia.lia.
      - (* FALSE branch: word.unsigned iw = 0 → vi = 0, close the post. *)
        intro Hbr.
        assert (Hvi0 : vi = 0%nat).
        { destruct vi as [|n]; [reflexivity|].
          exfalso.
          assert (HSn_small : Z.of_nat (S n) < 2 ^ width).
          { eapply reduce_iw_unsigned_small; [ exact Hiw | Lia.lia ]. }
          rewrite Hiw in Hbr. rewrite Nat2Z.inj_succ in Hbr. Lia.lia. }
        subst vi.
        split; [reflexivity|].
        exists bs_x, bs_y, bs_z, WXc, WYc, WZc.
        split; [exact Hlen_x|].
        split; [exact Hlen_y|].
        split; [exact Hlen_z|].
        split.
        { (* Split the mem manually.  The goal is
             (A * (fun m' => exists x y z, B(x,y,z) m'))%sep mem'
           which unfolds to
             exists ma mb, map.split mem' ma mb /\ A ma /\ (fun m' => ...) mb.
           We reshape Hm1 into two halves matching A and the B(RXc,RYc,RZc)
           position, then destruct and supply x=RXc, y=RYc, z=RZc. *)
          assert (Hm1' :
            (FElem (Some tight_bounds) wsx WXc
             * FElem (Some tight_bounds) wsy WYc
             * FElem (Some tight_bounds) wsz WZc
             * array (FElem (Some tight_bounds))
                     (word.of_Z felem_size_in_bytes) buckets_x bs_x
             * array (FElem (Some tight_bounds))
                     (word.of_Z felem_size_in_bytes) buckets_y bs_y
             * array (FElem (Some tight_bounds))
                     (word.of_Z felem_size_in_bytes) buckets_z bs_z
             * (FElem (Some tight_bounds) runx RXc
                * FElem (Some tight_bounds) runy RYc
                * FElem (Some tight_bounds) runz RZc
                * R))%sep m1).
          { ecancel_assumption. }
          destruct Hm1' as (ma & mb & Hsp & Ha & Hb).
          exists ma, mb. split; [exact Hsp|]. split; [exact Ha|].
          exists RXc, RYc, RZc. exact Hb. }
        split; [exact Hlbx1|].
        split; [exact Hlby1|].
        split; [exact Hlbz1|].
        split; [exact Hlrunx|].
        split; [exact Hlruny|].
        split; [exact Hlrunz|].
        split; [exact Hlwsx|].
        split; [exact Hlwsy|].
        split; [exact Hlwsz|].
        (* [mk_point WXc WYc WZc = reduce_buckets ...] via reduce_inv_exit
           + reduce_inv_at_exit. *)
        assert (Hrinv_neg1 :
          reduce_inv (-1) (RXc, RYc, RZc) (WXc, WYc, WZc)
                     (points_of bs_x bs_y bs_z)).
        { replace (-1) with (Z.of_nat 0 - 1) by reflexivity.
          exact Hrinv. }
        pose proof (reduce_inv_exit _ _ _ Hrinv_neg1) as (Hlen_po & Hrp & Hwp).
        unfold mk_point.
        apply (reduce_inv_at_exit _ _ _ Hlen_po Hrp Hwp). }
  Qed.

  (* =================================================================== *)
  (** ** Leaf 5: outer-loop body.                                         *)
  (*                                                                      *)
  (*    The outer-loop body runs once per window [w] (from [num_windows-1]*)
  (*    down to 0) and has the form:                                      *)
  (*                                                                      *)
  (*      w = w - 1;                         (* header decrement *)       *)
  (*      <double-shift loop>       (Leaf 1: out := 2^c . out)            *)
  (*      <bucket-clear loop>       (Leaf 2: buckets_* := 0 each)         *)
  (*      <distribute loop>         (Leaf 3: accumulate window digits)    *)
  (*      store_zero(runx,runy,runz);                                     *)
  (*      store_zero(wsx,wsy,wsz);                                        *)
  (*      <reduce loop>             (Leaf 4: ws := scaled_sum buckets)    *)
  (*      curve_add(out, ws, out)   (* out := out + ws *)                 *)
  (*                                                                      *)
  (*    Contract (outer envelope):                                        *)
  (*    - Pre-state: [outer_inv (S w) out0 scalars (points_of px py pz)]  *)
  (*      holds, i.e., [out0 = partial_msm_from (num_windows-(S w)-1)     *)
  (*      identity scalars ps].                                           *)
  (*    - Post-state: [outer_inv w out1 ...] holds, where                 *)
  (*      [out1 = (iter c double out0) + process_window ss ps w c bkts].  *)
  (*    - Sep memory: preserves the 9 FElem/array footprints for          *)
  (*      (out, buckets, run, ws) + the read-only scalars/points/R; the   *)
  (*      buckets/run/ws contents may be mutated arbitrarily but the      *)
  (*      array footprints are preserved.                                 *)
  (*    - Locals: all 17 stackalloc/argument pointer bindings are         *)
  (*      preserved; [w] is updated from [Z.of_nat (S w)] (pre) to        *)
  (*      [Z.of_nat w] (post).                                            *)
  (* =================================================================== *)

  (** The outer-loop-body command, extracted as an ExprImp term for               *)
  (** citation in [msm_bls12_outer_body_wp].  Matches lines 186-271 of            *)
  (** [msm_bls12] (the body of the outer [while (w)] loop).                       *)
  Definition outer_body_cmd : Syntax.cmd.cmd :=
    bedrock_func_body:(
      w = (w - $1);

      (* Double the accumulator c times. *)
      i = coq:(c);
      while (i) {
        i = (i - $1);
        coq:(cmd.call [] curve_double_name
               [expr.var "outx"; expr.var "outy"; expr.var "outz";
                expr.var "outx"; expr.var "outy"; expr.var "outz"])
      };

      (* Clear the bucket arrays. *)
      i = coq:(num_buckets);
      while (i) {
        i = (i - $1);
        bpx = (buckets_x + i * coq:(felem_size_in_bytes));
        bpy = (buckets_y + i * coq:(felem_size_in_bytes));
        bpz = (buckets_z + i * coq:(felem_size_in_bytes));
        coq:(cmd.call [] store_zero_name
               [expr.var "bpx"; expr.var "bpy"; expr.var "bpz"])
      };

      (* Distribute each (scalar, point) into its bucket. *)
      i = n;
      while (i) {
        i = (i - $1);
        bit_offset = (w * coq:(c));
        limb       = (bit_offset >> $6);
        shift      = (bit_offset & $63);
        mask       = (($1 << coq:(c)) - $1);
        scalar_ptr = (scalars + i * coq:(32));
        load_off1  = (limb * $8);
        load_addr1 = (scalar_ptr + load_off1);
        val        = (load(load_addr1) >> shift);
        if ($64 < (shift + coq:(c))) {
          if (limb < $3) {
            load_off2 = ((limb + $1) * $8);
            load_addr2 = (scalar_ptr + load_off2);
            val = (val |
                   (load(load_addr2) << ($64 - shift)))
          }
        };
        idx = (val & mask);

        if (idx) {
          bucket_index = (idx - $1);
          bpx = (buckets_x + bucket_index * coq:(felem_size_in_bytes));
          bpy = (buckets_y + bucket_index * coq:(felem_size_in_bytes));
          bpz = (buckets_z + bucket_index * coq:(felem_size_in_bytes));
          ppx = (pointsx  + i * coq:(felem_size_in_bytes));
          ppy = (pointsy  + i * coq:(felem_size_in_bytes));
          ppz = (pointsz  + i * coq:(felem_size_in_bytes));
          coq:(cmd.call [] curve_add_name
                 [expr.var "bpx"; expr.var "ppx";
                  expr.var "bpy"; expr.var "ppy";
                  expr.var "bpz"; expr.var "ppz";
                  expr.var "bpx"; expr.var "bpy"; expr.var "bpz"])
        }
      };

      (* Running-sum reduction. *)
      coq:(cmd.call [] store_zero_name
             [expr.var "runx"; expr.var "runy"; expr.var "runz"]);
      coq:(cmd.call [] store_zero_name
             [expr.var "wsx";  expr.var "wsy";  expr.var "wsz"]);

      i = coq:(num_buckets);
      while (i) {
        i = (i - $1);
        bpx = (buckets_x + i * coq:(felem_size_in_bytes));
        bpy = (buckets_y + i * coq:(felem_size_in_bytes));
        bpz = (buckets_z + i * coq:(felem_size_in_bytes));
        coq:(cmd.call [] curve_add_name
               [expr.var "runx"; expr.var "bpx";
                expr.var "runy"; expr.var "bpy";
                expr.var "runz"; expr.var "bpz";
                expr.var "runx"; expr.var "runy"; expr.var "runz"]);
        coq:(cmd.call [] curve_add_name
               [expr.var "wsx"; expr.var "runx";
                expr.var "wsy"; expr.var "runy";
                expr.var "wsz"; expr.var "runz";
                expr.var "wsx"; expr.var "wsy"; expr.var "wsz"])
      };

      coq:(cmd.call [] curve_add_name
             [expr.var "outx"; expr.var "wsx";
              expr.var "outy"; expr.var "wsy";
              expr.var "outz"; expr.var "wsz";
              expr.var "outx"; expr.var "outy"; expr.var "outz"])
    ).

  (** Helper: tighten an array-of-[FElem None] to an array-of-[FElem (Some
      tight_bounds)] when every cell admits a tight-bounded encoding.

      The bare form ([FElem None ==> FElem (Some tight_bounds)] without
      hypotheses) is NOT sound: [FElem None] only knows some witness
      [felem] evaluates to [v]; a tight-bounded witness may not agree
      with the bytes in memory.  We therefore require per-cell
      [bounded_by tight_bounds] as an extra hypothesis, phrased so it
      applies to the *existing* felem witness the left-hand side
      carries.

      The intended usage site is L5 segment 7 where every cell equals
      [g1_identity] = [(0, 1, 0)]: the three constant Fp coordinates
      admit a canonical tight-bounded encoding (fiat-crypto's
      [from_word] spec witnesses this for any field-of-word value).
      At the concrete BLS12-381 instantiation, the hypothesis
      discharges by rewriting each cell to its [(0, 1, 0)] value and
      applying the [bounded_by tight_bounds] field fact.  Here in the
      generic module we keep the hypothesis abstract. *)
  Lemma array_FElem_tighten_pointwise :
    forall (sz p : word) (xs : list F),
      Forall (fun v => forall f, feval f = v -> bounded_by tight_bounds f) xs ->
      Lift1Prop.impl1
        (array (FElem None) sz p xs)
        (array (FElem (Some tight_bounds)) sz p xs).
  Proof using field_representation_ok locals locals_ok mem_ok word_ok.
    intros sz p xs Hforall.
    revert p. induction Hforall as [|x xs' Hx Hforall' IH]; intros p.
    - cbn. reflexivity.
    - cbn. apply Proper_sep_impl1.
      + (* Per-cell: FElem None p x ==> FElem (Some tight_bounds) p x,
           using the pointwise bounds hypothesis on the existing witness. *)
        unfold Compilation2.FElem, Lift1Prop.ex1. intros m [v' Hm].
        apply sep_emp_l in Hm as [[Hfeval _] Hm].
        exists v'. apply sep_emp_l. split.
        * split; [exact Hfeval|]. cbn [Compilation2.maybe_bounded].
          apply Hx; exact Hfeval.
        * exact Hm.
      + apply IH.
  Qed.

  (** Back-compat alias with the old name: specialized form where every
      cell evaluates to a single fixed F-value [c] (per-coordinate).
      The per-cell hypothesis reduces to the single [bounded_by] proof
      [Hbnd] for that [c].

      Typical usage in L5 segment 7 (one invocation per coordinate):
      the x-array has every cell = [fst (fst g1_identity)] (i.e. the
      fixed x-coordinate of the identity, [0] in the usual encoding),
      the y-array every cell = [snd (fst g1_identity)] (e.g. [F.one]),
      and the z-array every cell = [snd g1_identity] (e.g. [0]).  Each
      of the three constant F-values has a canonical tight-bounded
      encoding at the concrete BLS12-381 instantiation, discharging
      [Hbnd] by [vm_compute]. *)
  Lemma array_FElem_tighten_at_identity :
    forall (sz p : word) (xs : list F) (cv : F),
      (forall f, feval f = cv -> bounded_by tight_bounds f) ->
      Forall (fun v => v = cv) xs ->
      Lift1Prop.impl1
        (array (FElem None) sz p xs)
        (array (FElem (Some tight_bounds)) sz p xs).
  Proof using field_representation_ok locals locals_ok mem_ok word_ok.
    intros sz p xs cv Hbnd Hid.
    apply array_FElem_tighten_pointwise.
    eapply Forall_impl; [|exact Hid].
    intros v ->. exact Hbnd.
  Qed.

  (** Gallina helper: [points_of] length is the minimum of the three
      coordinate-list lengths; with all three equal, the zip-3 has that
      common length. *)
  Lemma length_points_of_eq :
    forall px py pz : list F,
      length px = length py -> length py = length pz ->
      length (points_of px py pz) = length px.
  Proof.
    induction px as [|x px' IH]; intros py pz Hxy Hyz; cbn in *.
    - reflexivity.
    - destruct py as [|y py']; [discriminate|].
      destruct pz as [|z pz']; [discriminate|].
      cbn. f_equal. apply IH; [cbn in Hxy; Lia.lia | cbn in Hyz; Lia.lia].
  Qed.

  Lemma length_scalars_to_Z :
    forall ss, length (scalars_to_Z ss) = length ss.
  Proof. intros. unfold scalars_to_Z. apply List.map_length. Qed.

  (** Entry condition for L3's [distribute_inv]: when [i = length scalars]
      and every bucket cell is [g1_identity], the invariant holds because
      [skipn (length) full_list = nil] makes the fold_left trivial. *)
  Lemma distribute_inv_entry :
    forall (w : Z) (n_w : word) (bs : list G1_F)
           (ss : list (list word)) (ps : list G1_F),
      word.unsigned n_w = Z.of_nat (length ss) ->
      length ss = length ps ->
      Z.of_nat (length bs) = num_buckets ->
      (forall k, (k < Z.to_nat num_buckets)%nat ->
         nth k bs g1_identity = g1_identity) ->
      distribute_inv w (word.unsigned n_w) bs (scalars_to_Z ss) ps.
  Proof.
    intros w n_w bs ss ps Hn_len Hlen Hbs_len Hid.
    unfold distribute_inv.
    split; [exact Hbs_len|].
    intros k Hk.
    rewrite Hid by exact Hk.
    (* Show: g1_identity = fold_left _ (map snd (filter ... (skipn ... (combine ...)))) g1_identity. *)
    rewrite Hn_len, Nat2Z.id.
    rewrite List.skipn_all2.
    2: { rewrite List.combine_length, length_scalars_to_Z, <- Hlen, Nat.min_id. Lia.lia. }
    cbn. reflexivity.
  Qed.

  (** Leaf 5: outer-loop body.  Composes leaves 1-4 + final [curve_add].
      Maintains [outer_inv]; the Gallina window counter advances from
      [S w] (pre) to [w] (post) by the header decrement at the top of
      the body.  The postcondition re-establishes [outer_inv] at the
      decremented abstract window index and updates [outx/outy/outz]
      in memory to reflect the Gallina step

          out1 = (iter c double out0) + process_window(ss, ps, w, ...).

      The proof composes the 5 sub-leaves:
      - Leaf 1 ([msm_bls12_double_shift_wp]): out := iter c double out.
      - Leaf 2 ([msm_bls12_bucket_clear_wp]): buckets_* := identity.
      - Leaf 3 ([msm_bls12_distribute_wp]): scalars accumulated into buckets.
      - Two [store_zero] calls: run/ws := identity.
      - Leaf 4 ([msm_bls12_reduce_wp]): ws := scaled_sum buckets.
      - Final [curve_add] via [HCurveAdd].

      Postcondition closure [outer_inv (Z.of_nat w) out1]:  unfolds to
      [out1 = partial_msm_from (num_windows - w - 1) identity ss ps].
      The [S k] step of [partial_msm_from] shows this equals
      [partial_msm_from (num_windows - S w - 1)
         (g1_add (iter c double out0) (process_window ... w)) ss ps],
      which matches the precondition [outer_inv (S w) out0] followed
      by the final [curve_add]. *)
  Lemma msm_bls12_outer_body_wp :
    forall functions
      (HCurveAdd    : CurveAddAliasedOK    functions)
      (HCurveDouble : CurveDoubleInplaceOK functions)
      (HStoreZero   : StoreZero3OK         functions)
      (* --- pointers (arguments + stackallocs) --- *)
      (outx outy outz : word)
      (buckets_x buckets_y buckets_z : word)
      (runx runy runz : word)
      (wsx wsy wsz : word)
      (scalars_p pointsx pointsy pointsz n_w : word)
      (* --- current abstract window counter [w] (local "w" = S w before
         the body's header decrement, which sets local "w" to [w]).      *)
      (w : nat)
      (* --- Gallina state --- *)
      (out0 : G1_F)
      (bs_x bs_y bs_z : list F)
      (run0x run0y run0z : F)
      (ws0x ws0y ws0z : F)
      (scalars : list (list word))
      (px py pz : list F)
      (R : mem -> Prop) (tr : Semantics.trace) (mem0 : mem) (l0 : locals),
      (* --- pre-bounds --- *)
      (S w <= Z.to_nat num_windows)%nat ->
      word.unsigned n_w = Z.of_nat (length scalars) ->
      length scalars = length px ->
      length px = length py ->
      length py = length pz ->
      Z.of_nat (length bs_x) = num_buckets ->
      Z.of_nat (length bs_y) = num_buckets ->
      Z.of_nat (length bs_z) = num_buckets ->
      (* --- outer invariant at [S w] (before this iteration processes
         window [w]). *)
      outer_inv (Z.of_nat (S w)) out0
                (scalars_to_Z scalars) (points_of px py pz) ->
      (* --- memory sep: 3 output FElems, 3 bucket arrays, 6 run/ws
         FElems, scalars array, points arrays, and frame [R]. *)
      (let '(Ox, Oy, Oz) := out0 in
       FElem (Some tight_bounds) outx Ox
       * FElem (Some tight_bounds) outy Oy
       * FElem (Some tight_bounds) outz Oz
       * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_x bs_x
       * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_y bs_y
       * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_z bs_z
       * FElem None runx run0x
       * FElem None runy run0y
       * FElem None runz run0z
       * FElem None wsx  ws0x
       * FElem None wsy  ws0y
       * FElem None wsz  ws0z
       * ScalarsArray scalars_p scalars
       * G1Array3 pointsx pointsy pointsz px py pz
       * R)%sep mem0 ->
      (* --- locals: the 17 pointer/counter bindings used by the body. *)
      map.get l0 "outx"      = Some outx ->
      map.get l0 "outy"      = Some outy ->
      map.get l0 "outz"      = Some outz ->
      map.get l0 "buckets_x" = Some buckets_x ->
      map.get l0 "buckets_y" = Some buckets_y ->
      map.get l0 "buckets_z" = Some buckets_z ->
      map.get l0 "runx"      = Some runx ->
      map.get l0 "runy"      = Some runy ->
      map.get l0 "runz"      = Some runz ->
      map.get l0 "wsx"       = Some wsx ->
      map.get l0 "wsy"       = Some wsy ->
      map.get l0 "wsz"       = Some wsz ->
      map.get l0 "scalars"   = Some scalars_p ->
      map.get l0 "pointsx"   = Some pointsx ->
      map.get l0 "pointsy"   = Some pointsy ->
      map.get l0 "pointsz"   = Some pointsz ->
      map.get l0 "n"         = Some n_w ->
      map.get l0 "w"         = Some (word.of_Z (Z.of_nat (S w))) ->
      WeakestPrecondition.cmd functions
        outer_body_cmd
        tr mem0 l0
        (fun tr' mem' l' =>
           tr = tr' /\
           exists (out1 : G1_F)
                  (bs_x' bs_y' bs_z' : list F)
                  (run1x run1y run1z : F)
                  (ws1x ws1y ws1z : F),
             (* outer_inv advances by one abstract window. *)
             outer_inv (Z.of_nat w) out1
                       (scalars_to_Z scalars) (points_of px py pz) /\
             Z.of_nat (length bs_x') = num_buckets /\
             Z.of_nat (length bs_y') = num_buckets /\
             Z.of_nat (length bs_z') = num_buckets /\
             (let '(Ox', Oy', Oz') := out1 in
              FElem (Some tight_bounds) outx Ox'
              * FElem (Some tight_bounds) outy Oy'
              * FElem (Some tight_bounds) outz Oz'
              * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_x bs_x'
              * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_y bs_y'
              * array (FElem None) (word.of_Z felem_size_in_bytes) buckets_z bs_z'
              * FElem (Some tight_bounds) runx run1x
              * FElem (Some tight_bounds) runy run1y
              * FElem (Some tight_bounds) runz run1z
              * FElem (Some tight_bounds) wsx  ws1x
              * FElem (Some tight_bounds) wsy  ws1y
              * FElem (Some tight_bounds) wsz  ws1z
              * ScalarsArray scalars_p scalars
              * G1Array3 pointsx pointsy pointsz px py pz
              * R)%sep mem' /\
             map.get l' "outx"      = Some outx /\
             map.get l' "outy"      = Some outy /\
             map.get l' "outz"      = Some outz /\
             map.get l' "buckets_x" = Some buckets_x /\
             map.get l' "buckets_y" = Some buckets_y /\
             map.get l' "buckets_z" = Some buckets_z /\
             map.get l' "runx"      = Some runx /\
             map.get l' "runy"      = Some runy /\
             map.get l' "runz"      = Some runz /\
             map.get l' "wsx"       = Some wsx /\
             map.get l' "wsy"       = Some wsy /\
             map.get l' "wsz"       = Some wsz /\
             map.get l' "scalars"   = Some scalars_p /\
             map.get l' "pointsx"   = Some pointsx /\
             map.get l' "pointsy"   = Some pointsy /\
             map.get l' "pointsz"   = Some pointsz /\
             map.get l' "n"         = Some n_w /\
             map.get l' "w"         = Some (word.of_Z (Z.of_nat w))).
  Proof.
    (* =================================================================
       Composition skeleton of leaf 5 (real, mechanized outline).
       =================================================================
       The outer-body command [outer_body_cmd] decomposes into 7
       sequenced segments, each closed by one of the sub-leaves.  The
       proof skeleton below introduces the 41 quantified variables,
       unfolds [outer_body_cmd] to expose the seven segments, and
       documents the leaf (L1 Qed; L2/L3/L4 Admitted with matching WP
       triples) or callee-spec hypothesis that discharges each segment.
       Each segment-level gap — the sep/locals projection into the
       leaf's pre-shape and the re-assembly into the 14-cell post sep
       after each leaf — plus the single Gallina closure on
       [outer_inv] / [partial_msm_from], is left as one [admit] tagged
       with the segment it discharges.

       Trust chain for the closed proof:
         * L1 [msm_bls12_double_shift_wp]  : Qed, cmd matches prefix.
         * L2 [msm_bls12_bucket_clear_wp]  : Admitted, cmd matches.
         * L3 [msm_bls12_distribute_wp]    : Admitted, cmd matches.
         * L4 [msm_bls12_reduce_wp]        : Admitted, cmd matches.
         * [HCurveAdd] / [HStoreZero]       : hypotheses.
         * The [S k] step of [partial_msm_from]
           + [reduce_buckets_eq_scaled_sum] (Qed, IteratedSepPoints). *)
    intros functions HCurveAdd HCurveDouble HStoreZero
           outx outy outz bx_p by_p bz_p
           runx runy runz wsx wsy wsz
           scalars_p pointsx pointsy pointsz n_w
           w out0 bs_x bs_y bs_z
           run0x run0y run0z ws0x ws0y ws0z scalars px py pz
           R tr mem0 l0
           Hw_bd Hn_len Hlen_sx Hlen_xy Hlen_yz
           Hbs_x_len Hbs_y_len Hbs_z_len Houter_inv Hsep
           Hloutx Hlouty Hloutz Hlbx Hlby Hlbz
           Hlrx Hlry Hlrz Hlwx Hlwy Hlwz
           Hlsc Hlpx Hlpy Hlpz Hln Hlw.
    (* Unfold [outer_body_cmd] to expose the sequential composition
       [cmd.set "w" ...; while(i); while(i); while(i); call; call;
       while(i); call], so each segment can be discharged in turn.

       Segment 1 : [cmd.set "w" (w - 1)].  Pure locals update:
         l1 = map.put l0 "w" (word.sub old_w (word.of_Z 1))
             = map.put l0 "w" (word.of_Z (Z.of_nat w)).
       Discharged by unfolding [WeakestPrecondition.cmd]+[eexists]+
       [word.sub] on the literal-1 operand with the small-modulus
       [word.wrap] reduction.

       Segment 2 : double-shift loop.  Apply
       [msm_bls12_double_shift_wp] to the [cmd.while "i" ...] prefix
       after the preceding [cmd.set "i" c].  Pre-condition: project
       the three [FElem (Some tight_bounds)] (outx,outy,outz) cells
       out of [Hsep] (frame = remaining 11 sep cells).  Post-condition:
       [(Ox,Oy,Oz) = Nat.iter c g1_double_spec out0].

       Segment 3 : bucket-clear loop.  Apply
       [msm_bls12_bucket_clear_wp] to the [cmd.while "i" ...] prefix
       after [cmd.set "i" num_buckets].  Pre: project the three bucket
       [array (FElem None)] cells + frame.  Post: three updated lists
       [bs_x'/bs_y'/bs_z'] with every cell at [g1_identity].

       Segment 4 : distribute loop.  Apply [msm_bls12_distribute_wp]
       with [w := Z.of_nat w] (the decremented window index).  Pre:
       project bucket arrays + scalars + points arrays.  Post:
       [distribute_inv w 0 (points_of bs_x' bs_y' bs_z') ...].

       Segment 5a : [store_zero [runx;runy;runz]] via [HStoreZero].
       Segment 5b : [store_zero [wsx;wsy;wsz]]  via [HStoreZero].

       Segment 6 : reduce loop.  Apply [msm_bls12_reduce_wp].
       Post: [wsx/wsy/wsz] equal to [scaled_sum bs_*]
       (= [reduce_buckets bs_*] via [reduce_buckets_eq_scaled_sum]).

       Segment 7 : final [curve_add
         [outx;wsx;outy;wsy;outz;wsz;outx;outy;outz]]
       via [HCurveAdd] with (pb{i},pp{i}) = (out{i},ws{i}).

       Gallina closure: re-establish [outer_inv (Z.of_nat w) out1].
       Unfold [outer_inv] to
         [out1 = partial_msm_from (num_windows - w - 1) identity ss ps]
       and apply [partial_msm_from]'s [S k] step to the precondition
         [out0 = partial_msm_from (num_windows - S w - 1) identity ss ps]
       yielding [out1 = partial_msm_from (num_windows - w - 1) ...]
       since [num_windows - w - 1 = S (num_windows - S w - 1)] when
       [S w <= num_windows] (Hw_bd).  The [process_window] Gallina
       value matches segment-6's [scaled_sum] via
       [reduce_buckets_eq_scaled_sum] (Qed). *)
    unfold outer_body_cmd.
    (* Segment 1 (peel outer seq for [cmd.set "w" (w-1)]).  Use
       [unfold1_cmd_goal] (peel ONE [cmd] layer) rather than
       [cbv [cmd cmd_body]] (which cascade-unfolds into
       [Semantics.exec.exec] via the top-level fixpoint).  After the
       peel, we have [cmd e (cmd.set "w" ...) tr mem l0 (fun _ _ l =>
       cmd e REST_1 ...)].  Unfolding a second layer exposes the
       [cmd.set] existential. *)
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eexists. split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
           WeakestPrecondition.expr_body WeakestPrecondition.literal
           WeakestPrecondition.get dlet.dlet].
      eexists; split; [exact Hlw | reflexivity]. }
    cbv [dlet.dlet].
    (* Segment 2: same shape for [cmd.set "i" c]. *)
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    unfold1_cmd_goal; cbv beta match delta [WeakestPrecondition.cmd_body].
    eexists. split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
           WeakestPrecondition.expr_body WeakestPrecondition.literal
           WeakestPrecondition.get dlet.dlet].
      reflexivity. }
    cbv [dlet.dlet].
    (* After segments 1-2 (cmd.set "w", cmd.set "i"), the remaining goal
       is [cmd e (cmd.seq SEG3 REST) tr mem0 l2 post], where [l2] has
       [map.put l0 "w" ...] composed with [map.put _ "i" (word.of_Z c)].
       We peel each subsequent segment in turn, citing the matching
       leaf lemma (L1..L4 + HStoreZero/HCurveAdd), and close the
       Gallina postcondition via [partial_msm_from]'s [S k] step.

       The remaining work decomposes as:

       Seg 3  (L1 [msm_bls12_double_shift_wp])  : [out] := [Nat.iter c
              g1_double_spec out0].  Pre: project (outx,outy,outz)
              FElems at [tight_bounds] + 11-cell frame from [Hsep].
              Post: (Ox',Oy',Oz') in out, tight_bounds preserved,
              frame unchanged.

       Seg 4  (L2 [msm_bls12_bucket_clear_wp])  : buckets_{x,y,z}
              := g1_identity arrays.  Pre: project the 3 bucket arrays
              at [FElem None] + remaining frame.  Post: [bs_x',bs_y',
              bs_z'] all g1_identity pointwise.

       Seg 5  (L3 [msm_bls12_distribute_wp])    : scalars accumulated
              into buckets per window [w].  Pre: 3 bucket arrays + 3
              point arrays + ScalarsArray.  Post: [distribute_inv w 0]
              holds on [bs_x'',bs_y'',bs_z''].

       Seg 6a (HStoreZero on run{x,y,z})        : 3 FElems := identity.
       Seg 6b (HStoreZero on ws{x,y,z})         : 3 FElems := identity.

       Seg 7  (L4 [msm_bls12_reduce_wp])        : ws := scaled_sum
              buckets.  Requires bucket arrays at [tight_bounds] —
              bridged from [FElem None] (L3 exit) via the
              [distribute_inv]+[clear_inv] observation that every cell
              is either g1_identity (from L2) or g1_add_spec-chained
              from input [px,py,pz] (pre-bounds).  See the [Seg 7
              bounds-bridge] note below.

       Seg 8  (HCurveAdd)                        : out := out + ws
              with (pb,pp) = (out,ws).

       Seg 9  (Gallina closure)                  : re-establish
              [outer_inv (Z.of_nat w) out1] using [partial_msm_from]'s
              [S k] unfolding and [reduce_buckets_eq_scaled_sum]. *)

    (* Seg 3 bounds-bridge note: L2 exits with [array (FElem None)]
       at every bucket cell, which is exactly what L3's pre-shape
       requires.  Between L3 exit and L4 entry, we need to upgrade
       to [array (FElem (Some tight_bounds))]; this is the
       "None→tight" direction that is NOT generically sound (None
       allows any limb pattern, not just tight).  The bridge relies
       on per-cell knowledge: every bucket cell at L3 exit is either
       [g1_identity] (for untouched buckets) or the result of
       [curve_add_name] calls (inplace on bucket_* + ppoint), whose
       post from CurveAddAliasedOK is [FElem (Some tight_bounds)].
       A fully mechanized bridge would need L3's post strengthened
       to [FElem (Some tight_bounds)] throughout (the callee's
       natural post).  Deferred to a future L3 revision. *)

    (* ================================================================
       Segment 3: double-shift while.  Peel one seq layer via
       [unfold1_cmd_goal] (one-level-cmd unfolding without over-unfolding
       the while body), then use [Proper_cmd] to weaken the sub-post
       and eapply L1.

       NOTE: a bare [cbv [cmd cmd_body]; fold cmd] here over-unfolds
       into [Semantics.exec.exec] because by this point the containing
       post contains [cmd e REST ...] inside [Semantics.exec]-shaped
       obligations produced from the seg-1/seg-2 peels.  Use
       [unfold1_cmd_goal] to keep the goal at [WeakestPrecondition.cmd]
       for the top [cmd.seq] without diving into the while.
       ================================================================ *)
    destruct out0 as [[Ox Oy] Oz].
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    (* Goal: cmd e W3 tr mem0 l2 (fun tr' m' l' => cmd e REST tr' m' l' post).
       Wrap L1 with frame_locals_wp_list on the 15 non-L1 locals, so
       the post also includes their preservation across L1's execution. *)
    eapply WeakestPreconditionProperties.Proper_cmd;
      [ |
        eapply frame_locals_wp_list with
          (xs := ["buckets_x"; "buckets_y"; "buckets_z";
                  "runx"; "runy"; "runz";
                  "wsx";  "wsy";  "wsz";
                  "scalars"; "pointsx"; "pointsy"; "pointsz";
                  "n"; "w"]);
          [ (* Forall (~ In x (cmd_writes L1)): cmd_writes = ["i"]. *)
            do 15 (apply List.Forall_cons; [cbn; intuition discriminate|]);
            apply List.Forall_nil
          | (* Forall (exists v, map.get l2 x = Some v).  First 14
               locals (non-"w") use !map.get_put_diff to skip both puts.
               "w" was put by seg 1, so map.get_put_diff (once) then
               map.get_put_same. *)
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlbx|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlby|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlbz|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlrx|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlry|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlrz|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlwx|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlwy|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlwz|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlsc|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlpx|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlpy|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hlpz|];
            apply List.Forall_cons; [eexists; rewrite !map.get_put_diff by congruence; exact Hln|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence;
                                     rewrite map.get_put_same; reflexivity|];
            apply List.Forall_nil
          | eapply msm_bls12_double_shift_wp with
              (Xe := Ox) (Ye := Oy) (Ze := Oz)
              (R := (array (FElem None) (word.of_Z felem_size_in_bytes) bx_p bs_x
                     * array (FElem None) (word.of_Z felem_size_in_bytes) by_p bs_y
                     * array (FElem None) (word.of_Z felem_size_in_bytes) bz_p bs_z
                     * FElem None runx run0x
                     * FElem None runy run0y
                     * FElem None runz run0z
                     * FElem None wsx  ws0x
                     * FElem None wsy  ws0y
                     * FElem None wsz  ws0z
                     * ScalarsArray scalars_p scalars
                     * G1Array3 pointsx pointsy pointsz px py pz
                     * R)%sep);
              [ exact HCurveDouble
              | ecancel_assumption
              | rewrite !map.get_put_diff by congruence; exact Hloutx
              | rewrite !map.get_put_diff by congruence; exact Hlouty
              | rewrite !map.get_put_diff by congruence; exact Hloutz
              | rewrite map.get_put_same; reflexivity ]
          ]
      ].
    cbv beta.
    intros tr3 mem3 l3 [HF HL1].
    destruct HL1 as [Htr3 [Hsep3 [Hlo3x [Hlo3y Hlo3z]]]].
    subst tr3.
    (* Name the post state (Xf,Yf,Zf) from the iter result. *)
    set (st3 := Nat.iter (Z.to_nat c) g1_double_spec (Ox, Oy, Oz)) in *.
    destruct st3 as [[Xf Yf] Zf] eqn:Hst3.

    (* ================================================================
       Locals-preservation via [frame_locals_wp].

       L1's post only exposes [map.get l3 "outx/y/z"].  All other 14
       locals ("buckets_x/y/z", "runx/y/z", "wsx/y/z", "scalars",
       "pointsx/y/z", "n", "w") are required by L2/L3/L4.  They ARE
       preserved in the concrete execution (the body only writes "i"
       and calls with empty binds), but the leaf spec does not state
       it.

       Bridge: [frame_locals_wp] (in [Bedrock.FrameLocalsWP]) proves
       that for any unwritten local [x] with [map.get l x = Some v]
       at entry, we can conjoin [map.get l' x = Some v] to the post
       of [WeakestPrecondition.cmd].  We invoke it retroactively on
       [l3] — not possible directly, but we extract each of the 14
       preservations by observing that the REST command does not
       write them (a [cmd_writes] computation) and that L1's concrete
       body (the inner [while] body) also does not (verified by
       simple [cbn]).

       To keep the structural proof focused on composition STRUCTURE
       (the task), we cite the preservation of each of the 14 locals
       as hypotheses [Hlo3_bx], [Hlo3_by], ..., extracted via the
       frame-locals discipline.  The extraction is a short admit per
       local, each proved by a one-liner [eapply frame_locals_wp] +
       [cbn [cmd_writes]; intuition discriminate] when
       [frame_locals_wp] is Qed (currently Admitted in
       [FrameLocalsWP.v]; lands the same trust chain).

       The following [assert]s make the state legible and cite the
       bridge; we close each with [admit] since closing requires
       rewinding the [Proper_cmd]/L1 application to wrap it in
       [frame_locals_wp] (a proof refactoring worth its own commit). *)

    (* Typical citation pattern using [Bedrock.FrameLocalsWP.frame_locals_wp]:
       if [frame_locals_wp] were applied BEFORE consuming L1's post, we
       would obtain a conjunct [map.get l3 "buckets_x" = Some bx_p] on
       the L1 post, since [bx_p] is in [l2] (the locals after seg 1/2)
       and "buckets_x" is NOT in [cmd_writes (cmd.while double_shift)].

       A fully mechanised version rewinds [eapply Proper_cmd] in seg 3,
       wraps the L1 call with [frame_locals_wp_list] on the list of 14
       locals, then destructs both the Forall preservation and L1's
       post in [destruct HL1 as [HF [Htr3 [Hsep3 ...]]]].  Each
       preservation [map.get l3 "foo" = map.get l0 "foo"] combines with
       the pre-condition [Hl*] to yield [map.get l3 "foo" = Some ...].

       We cite [frame_locals_wp] as the trust target and provide the
       conclusions via [admit]; the citation below is a ghost reference
       proving the lemma we would apply. *)
    (* Extract the 15 locals-preservation hypotheses from HF (a Forall
       of 15 [map.get l2 x = map.get l3 x] facts).  Destructure one at
       a time; each combined with the pre-condition Hl* (via map.get_put_diff
       to skip the "w" and "i" puts in l2) yields Hlo3_*. *)
    inversion HF as [|? ? Hp_bx HF1]; subst; clear HF.
    inversion HF1 as [|? ? Hp_by HF2]; subst; clear HF1.
    inversion HF2 as [|? ? Hp_bz HF3]; subst; clear HF2.
    inversion HF3 as [|? ? Hp_rx HF4]; subst; clear HF3.
    inversion HF4 as [|? ? Hp_ry HF5]; subst; clear HF4.
    inversion HF5 as [|? ? Hp_rz HF6]; subst; clear HF5.
    inversion HF6 as [|? ? Hp_wx HF7]; subst; clear HF6.
    inversion HF7 as [|? ? Hp_wy HF8]; subst; clear HF7.
    inversion HF8 as [|? ? Hp_wz HF9]; subst; clear HF8.
    inversion HF9 as [|? ? Hp_sc HF10]; subst; clear HF9.
    inversion HF10 as [|? ? Hp_px HF11]; subst; clear HF10.
    inversion HF11 as [|? ? Hp_py HF12]; subst; clear HF11.
    inversion HF12 as [|? ? Hp_pz HF13]; subst; clear HF12.
    inversion HF13 as [|? ? Hp_n  HF14]; subst; clear HF13.
    inversion HF14 as [|? ? Hp_w  _]; subst; clear HF14.
    assert (Hlo3_bx : map.get l3 "buckets_x" = Some bx_p).
    { rewrite <- Hp_bx, !map.get_put_diff by congruence. exact Hlbx. }
    assert (Hlo3_by : map.get l3 "buckets_y" = Some by_p).
    { rewrite <- Hp_by, !map.get_put_diff by congruence. exact Hlby. }
    assert (Hlo3_bz : map.get l3 "buckets_z" = Some bz_p).
    { rewrite <- Hp_bz, !map.get_put_diff by congruence. exact Hlbz. }
    assert (Hlo3_rx : map.get l3 "runx" = Some runx).
    { rewrite <- Hp_rx, !map.get_put_diff by congruence. exact Hlrx. }
    assert (Hlo3_ry : map.get l3 "runy" = Some runy).
    { rewrite <- Hp_ry, !map.get_put_diff by congruence. exact Hlry. }
    assert (Hlo3_rz : map.get l3 "runz" = Some runz).
    { rewrite <- Hp_rz, !map.get_put_diff by congruence. exact Hlrz. }
    assert (Hlo3_wx : map.get l3 "wsx" = Some wsx).
    { rewrite <- Hp_wx, !map.get_put_diff by congruence. exact Hlwx. }
    assert (Hlo3_wy : map.get l3 "wsy" = Some wsy).
    { rewrite <- Hp_wy, !map.get_put_diff by congruence. exact Hlwy. }
    assert (Hlo3_wz : map.get l3 "wsz" = Some wsz).
    { rewrite <- Hp_wz, !map.get_put_diff by congruence. exact Hlwz. }
    assert (Hlo3_sc : map.get l3 "scalars" = Some scalars_p).
    { rewrite <- Hp_sc, !map.get_put_diff by congruence. exact Hlsc. }
    assert (Hlo3_px : map.get l3 "pointsx" = Some pointsx).
    { rewrite <- Hp_px, !map.get_put_diff by congruence. exact Hlpx. }
    assert (Hlo3_py : map.get l3 "pointsy" = Some pointsy).
    { rewrite <- Hp_py, !map.get_put_diff by congruence. exact Hlpy. }
    assert (Hlo3_pz : map.get l3 "pointsz" = Some pointsz).
    { rewrite <- Hp_pz, !map.get_put_diff by congruence. exact Hlpz. }
    assert (Hlo3_n  : map.get l3 "n" = Some n_w).
    { rewrite <- Hp_n, !map.get_put_diff by congruence. exact Hln. }
    (* "w" path: l2's "w" is [word.sub (word.of_Z (Z.of_nat (S w)))
       (word.of_Z 1)], which equals [word.of_Z (Z.of_nat w)] by the
       word-ring morphism.  Bridge via Hp_w and simplify. *)
    assert (Hlo3_w : map.get l3 "w" = Some (word.of_Z (Z.of_nat w))).
    { rewrite <- Hp_w.
      rewrite map.get_put_diff by congruence.
      rewrite map.get_put_same.
      f_equal.
      cbn [Semantics.interp_binop].
      rewrite <- word.ring_morph_sub.
      f_equal. rewrite Nat2Z.inj_succ. ring. }

    (* ================================================================
       Segment 4 (= L2 bucket_clear):  cmd.set "i" num_buckets;
                                       cmd.while (...).
       Peel the two layers to expose the [cmd.set "i" num_buckets]
       prefix, then apply [Proper_cmd] with L2 on the while.  Note the
       set of [i] produces the exact local value L2's precondition
       expects: [map.get l "i" = Some (word.of_Z num_buckets)]. *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    eexists. split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
           WeakestPrecondition.expr_body WeakestPrecondition.literal
           WeakestPrecondition.get dlet.dlet].
      reflexivity. }
    cbv [dlet.dlet].
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    eapply WeakestPreconditionProperties.Proper_cmd;
      [ |
        eapply frame_locals_wp_list with
          (xs := ["outx"; "outy"; "outz";
                  "runx"; "runy"; "runz";
                  "wsx";  "wsy";  "wsz";
                  "scalars"; "pointsx"; "pointsy"; "pointsz";
                  "n"; "w"]);
          [ (* Forall (~ In x (cmd_writes L2)): L2's cmd_writes is
               ["i"; "bpx"; "bpy"; "bpz"]; none of our 15 match. *)
            do 15 (apply List.Forall_cons; [cbn; intuition discriminate|]);
            apply List.Forall_nil
          | (* Forall (exists v, map.get l3_after_seti x = Some v).
               l3' = map.put l3 "i" _; skip via map.get_put_diff. *)
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3x|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3y|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3z|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_rx|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_ry|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_rz|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_wx|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_wy|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_wz|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_sc|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_px|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_py|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_pz|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_n|];
            apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo3_w|];
            apply List.Forall_nil
          | eapply msm_bls12_bucket_clear_wp with
              (R := (FElem (Some tight_bounds) outx Xf
                     * FElem (Some tight_bounds) outy Yf
                     * FElem (Some tight_bounds) outz Zf
                     * FElem None runx run0x
                     * FElem None runy run0y
                     * FElem None runz run0z
                     * FElem None wsx  ws0x
                     * FElem None wsy  ws0y
                     * FElem None wsz  ws0z
                     * ScalarsArray scalars_p scalars
                     * G1Array3 pointsx pointsy pointsz px py pz
                     * R)%sep);
              [ exact HStoreZero
              | exact Hbs_x_len
              | exact Hbs_y_len
              | exact Hbs_z_len
              | ecancel_assumption
              | rewrite map.get_put_diff by congruence; exact Hlo3_bx
              | rewrite map.get_put_diff by congruence; exact Hlo3_by
              | rewrite map.get_put_diff by congruence; exact Hlo3_bz
              | rewrite map.get_put_same; reflexivity ]
          ]
      ].
    cbv beta.
    intros tr4 mem4 l4 [HF4 HL2].
    destruct HL2 as
      [Htr4 [bs_x4 [bs_y4 [bs_z4 [Hlen4x [Hlen4y [Hlen4z
       [Hid4 [Hsep4 [Hlo4_bx [Hlo4_by Hlo4_bz]]]]]]]]]]].
    subst tr4.

    (* Extract 15 locals preservations from HF4 (Forall of l3'→l4 equalities).
       Each Hp4_* says map.get l3_after_seti x = map.get l4 x; combined with
       Hlo3_* (via map.get_put_diff over the "i" put) it yields Hlo4_*. *)
    inversion HF4 as [|? ? Hp4_ox  HF4_1];  subst; clear HF4.
    inversion HF4_1 as [|? ? Hp4_oy  HF4_2];  subst; clear HF4_1.
    inversion HF4_2 as [|? ? Hp4_oz  HF4_3];  subst; clear HF4_2.
    inversion HF4_3 as [|? ? Hp4_rx  HF4_4];  subst; clear HF4_3.
    inversion HF4_4 as [|? ? Hp4_ry  HF4_5];  subst; clear HF4_4.
    inversion HF4_5 as [|? ? Hp4_rz  HF4_6];  subst; clear HF4_5.
    inversion HF4_6 as [|? ? Hp4_wx  HF4_7];  subst; clear HF4_6.
    inversion HF4_7 as [|? ? Hp4_wy  HF4_8];  subst; clear HF4_7.
    inversion HF4_8 as [|? ? Hp4_wz  HF4_9];  subst; clear HF4_8.
    inversion HF4_9 as [|? ? Hp4_sc  HF4_10]; subst; clear HF4_9.
    inversion HF4_10 as [|? ? Hp4_px  HF4_11]; subst; clear HF4_10.
    inversion HF4_11 as [|? ? Hp4_py  HF4_12]; subst; clear HF4_11.
    inversion HF4_12 as [|? ? Hp4_pz  HF4_13]; subst; clear HF4_12.
    inversion HF4_13 as [|? ? Hp4_n   HF4_14]; subst; clear HF4_13.
    inversion HF4_14 as [|? ? Hp4_w   _];      subst; clear HF4_14.
    assert (Hlo4_ox : map.get l4 "outx" = Some outx).
    { rewrite <- Hp4_ox, map.get_put_diff by congruence. exact Hlo3x. }
    assert (Hlo4_oy : map.get l4 "outy" = Some outy).
    { rewrite <- Hp4_oy, map.get_put_diff by congruence. exact Hlo3y. }
    assert (Hlo4_oz : map.get l4 "outz" = Some outz).
    { rewrite <- Hp4_oz, map.get_put_diff by congruence. exact Hlo3z. }
    assert (Hlo4_rx : map.get l4 "runx" = Some runx).
    { rewrite <- Hp4_rx, map.get_put_diff by congruence. exact Hlo3_rx. }
    assert (Hlo4_ry : map.get l4 "runy" = Some runy).
    { rewrite <- Hp4_ry, map.get_put_diff by congruence. exact Hlo3_ry. }
    assert (Hlo4_rz : map.get l4 "runz" = Some runz).
    { rewrite <- Hp4_rz, map.get_put_diff by congruence. exact Hlo3_rz. }
    assert (Hlo4_wx : map.get l4 "wsx" = Some wsx).
    { rewrite <- Hp4_wx, map.get_put_diff by congruence. exact Hlo3_wx. }
    assert (Hlo4_wy : map.get l4 "wsy" = Some wsy).
    { rewrite <- Hp4_wy, map.get_put_diff by congruence. exact Hlo3_wy. }
    assert (Hlo4_wz : map.get l4 "wsz" = Some wsz).
    { rewrite <- Hp4_wz, map.get_put_diff by congruence. exact Hlo3_wz. }
    assert (Hlo4_sc : map.get l4 "scalars" = Some scalars_p).
    { rewrite <- Hp4_sc, map.get_put_diff by congruence. exact Hlo3_sc. }
    assert (Hlo4_px : map.get l4 "pointsx" = Some pointsx).
    { rewrite <- Hp4_px, map.get_put_diff by congruence. exact Hlo3_px. }
    assert (Hlo4_py : map.get l4 "pointsy" = Some pointsy).
    { rewrite <- Hp4_py, map.get_put_diff by congruence. exact Hlo3_py. }
    assert (Hlo4_pz : map.get l4 "pointsz" = Some pointsz).
    { rewrite <- Hp4_pz, map.get_put_diff by congruence. exact Hlo3_pz. }
    assert (Hlo4_n : map.get l4 "n" = Some n_w).
    { rewrite <- Hp4_n, map.get_put_diff by congruence. exact Hlo3_n. }
    assert (Hlo4_w : map.get l4 "w" = Some (word.of_Z (Z.of_nat w))).
    { rewrite <- Hp4_w, map.get_put_diff by congruence. exact Hlo3_w. }

    (* ================================================================
       Segments 5-9: citation skeleton.

       The L3/L4 applications and the final curve_add follow the same
       tactical pattern as segment 4 (L2) above: unfold outer seq,
       close [cmd.set "i" ...] via [eexists; split; reflexivity], then
       [eapply WeakestPreconditionProperties.Proper_cmd; [ | eapply
       msm_bls12_{distribute,reduce}_wp with (R := ...); [...discharge
       premises...] ] ].  Each leaf's post yields the next Hsep + its
       own locals; the 14 non-leaf locals are re-established via
       [frame_locals_wp] (citation stubs, analogous to the [Hlo4_*]
       assertions above).

       Segment 5 ([msm_bls12_distribute_wp]):
         After L2 exit, peel [cmd.set "i" n] via [eexists; split;
         exact Hlo4_n], then [Proper_cmd] + L3 with premises:
           * [0 <= Z.of_nat w < num_windows] from [Hw_bd].
           * Bucket lengths [Hlen4x/y/z].
           * [length bs_x = length bs_y], [length bs_y = length bs_z]
             by [Lia] from length equalities.
           * [word.unsigned n_w = Z.of_nat (length scalars)] from [Hn_len].
           * [length scalars = length px/y/z] chained from [Hlen_sx].
           * [distribute_inv w n_w (points_of bs_x4 bs_y4 bs_z4)
             (scalars_to_Z scalars) (points_of px py pz)] — initial
             case where the bucket slice is [skipn n_w] = [], yielding
             trivially [fold_left _ [] = g1_identity].  Combined with
             [Hid4] (every bucket cell = g1_identity) this is a pure
             Gallina fact (admitted).
           * Sep: [ecancel_assumption] on [Hsep4] (L2 exit).
           * Locals: 8 [Hlo4_*] + [map.get_put_same] on "i" = n_w after
             [map.put ... "i" n_w].

       Segment 6a/6b ([HStoreZero]):
         Direct citation of [HStoreZero runx runy runz ...] with R
         the whole remaining 12-cell frame; after the call,
         [map.putmany_of_list_zip [] [] l = Some l] trivially,
         re-establishing locals.

       Segment 7 ([msm_bls12_reduce_wp]):
         Peel [cmd.set "i" num_buckets], then apply L4.  Bucket
         arrays (which L3 left at [FElem None]) are tightened to
         [FElem (Some tight_bounds)] via the helper
         [array_FElem_tighten_at_identity] above (now Qed, parametrised
         by an [identity_bounded] hypothesis + a [Forall (= g1_identity)]
         witness).  Both are discharged at the concrete BLS12-381
         instantiation:  [Forall (= g1_identity)] comes from L3's post
         (untouched buckets stay at identity); [identity_bounded] is
         the constant-limb computation [(0, 1, 0) tight-bounded].
         For cells touched by [g1_add_spec] we instead cite the
         tight-bounds post-condition of [curve_add] directly.
         Post: [wsx/y/z] at
         [tight_bounds] with values [scaled_sum (points_of bs_x5 ...)]
         = [reduce_buckets ...] via [reduce_buckets_eq_scaled_sum]
         (Qed in [IteratedSepPoints.v]).

       Segment 8 ([HCurveAdd]):
         Direct citation of [HCurveAdd outx wsx outy wsy outz wsz
         outx outy outz].  Post: [outx/y/z] at tight bounds with
         values [g1_add_spec (Xf, Yf, Zf) (WXf, WYf, WZf)].

       Gallina closure [outer_inv (Z.of_nat w) out1]:
         Unfold [outer_inv] to
           [out1 = partial_msm_from (num_windows - w - 1) identity
                     (scalars_to_Z scalars) (points_of px py pz)].
         Use [Hw_bd] (S w <= num_windows) to rewrite
           [num_windows - w - 1 = S (num_windows - S w - 1)],
         then apply [partial_msm_from]'s [S k] step to the
         precondition [outer_inv (S w) out0]:
           out0 = partial_msm_from (num_windows - S w - 1) identity ss ps.
         The [S k] step gives
           partial_msm_from (num_windows - w - 1) identity ss ps
             = partial_msm_from (num_windows - S w - 1)
                 (g1_add_spec (iter c double out0) (process_window ...))
                 ss ps
             = g1_add_spec (Xf, Yf, Zf) (process_window (scalars_to_Z scalars)
                                                        (points_of px py pz)
                                                        w c num_buckets).
         The [process_window] expression equals [reduce_buckets (iter w
         (fun bkts (s,p) => ...) (repeat identity num_buckets))] which,
         by [reduce_buckets_eq_scaled_sum] applied to L4's exit post
         (which states [wsx/y/z = scaled_sum bs_x5/y5/z5]), matches
         [(WXf, WYf, WZf)]. *)

    (* ================================================================
       BLOCKER (discovered 2026-04-19 by seg 5 audit): L3's statement
       ([msm_bls12_distribute_wp], ~ line 2200-2350) has the [cmd.while]
       body with the "val := (load(scalar_ptr + limb*8) >> shift)" load
       INLINED, i.e. without the intermediate [cmd.set "load_off1"] /
       [cmd.set "load_addr1"] / [cmd.set "load_off2"] / [cmd.set "load_addr2"]
       prelude that [msm_bls12] (and [outer_body_cmd]) DO emit.

       The load_off/addr sets were added to the bedrock2 source (line
       217-228 and 3292-3300) for Rust extraction (ToRustString's
       [rust_ptr_varlit] only handles literals and variables — not
       arithmetic expressions — so the load address must be a named
       local).  L3's cmd statement was NOT synced.

       Consequence: the while body in [outer_body_cmd] and the while
       body in L3's statement are NOT syntactically equal, so
       [eapply msm_bls12_distribute_wp] after peeling the outer-body
       [cmd.set "i" n] fails unification.

       Required fix (NOT included in this commit, outside the seg-5
       composition scope): update [msm_bls12_distribute_wp] (L3)
       statement at line ~2261 to match outer_body_cmd.  Replace
         (cmd.set "val"
            (expr.op bopname.sru
               (expr.load access_size.word
                  (expr.op bopname.add (expr.var "scalar_ptr")
                     (expr.op bopname.mul (expr.var "limb") (expr.literal 8))))
               (expr.var "shift")))
       with
         (cmd.seq (cmd.set "load_off1"
                   (expr.op bopname.mul (expr.var "limb") (expr.literal 8)))
          (cmd.seq (cmd.set "load_addr1"
                    (expr.op bopname.add (expr.var "scalar_ptr") (expr.var "load_off1")))
                   (cmd.set "val"
                    (expr.op bopname.sru
                       (expr.load access_size.word (expr.var "load_addr1"))
                       (expr.var "shift")))))
       and analogously for the load_off2/addr2 inside the cross-limb
       [cmd.cond] at line ~2273-2281.  Since L3 is [Admitted] today
       (line 2515), the edit is cheap: the statement changes, the
       intended proof strategy is unchanged.

       Once L3 matches, the seg-5 tactic (drafted inline in the git
       history of this file, reverted here) is:

         unfold1_cmd_goal; cbv beta match delta [cmd_body].
         unfold1_cmd_goal; cbv beta match delta [cmd_body].
         eexists. split.
         { cbv [WeakestPrecondition.dexpr ... ].
           eexists; split; [exact Hlo4_n | reflexivity]. }
         cbv [dlet.dlet].
         unfold1_cmd_goal; cbv beta match delta [cmd_body].
         eapply WeakestPreconditionProperties.Proper_cmd;
           [ | eapply frame_locals_wp_list with
                 (xs := ["outx";"outy";"outz";"runx";"runy";"runz";
                         "wsx";"wsy";"wsz";"n"]);
               [ do 10 (apply List.Forall_cons; [cbn; intuition discriminate|]);
                 apply List.Forall_nil
               | (* 10 preservation witnesses, each
                    [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_*] *)
                 ...
               | eapply msm_bls12_distribute_wp with
                   (w := Z.of_nat w) (n_w := n_w)
                   (buckets_x := bx_p) (buckets_y := by_p) (buckets_z := bz_p)
                   (bs_x := bs_x4) (bs_y := bs_y4) (bs_z := bs_z4)
                   (R := (FElem (Some tight_bounds) outx Xf
                          * FElem (Some tight_bounds) outy Yf
                          * FElem (Some tight_bounds) outz Zf
                          * FElem None runx run0x
                          * FElem None runy run0y
                          * FElem None runz run0z
                          * FElem None wsx  ws0x
                          * FElem None wsy  ws0y
                          * FElem None wsz  ws0z
                          * R)%sep);
                   [ ...20 premises in order: HCurveAdd,
                       [0<=Z.of_nat w<num_windows] (from Hw_bd),
                       Hlen4x/y/z, length bs_x4=bs_y4 via Lia, ditto
                       y/z, Hn_len, Hlen_sx/xy/yz, distribute_inv
                       entry (from Hid4 + skipn_all), ecancel on Hsep4,
                       8 locals rewrites via map.get_put_diff,
                       map.get_put_same for "i"... ]
               ] ].

       After L3's post is destructed (pattern [HF5 HL3], inner
       [Htr5 [bs_x5 bs_y5 bs_z5 ...] ...]) and HF5 is inverted 10
       times to extract Hlo5_* preservations, proceed to seg 6a/b
       (HStoreZero calls), seg 7 (L4 reduce), seg 8 (HCurveAdd),
       and seg 9 (Gallina closure via partial_msm_from's [S k] step
       + reduce_buckets_eq_scaled_sum). *)

    (* ============================================================
       Segment 5 (L3 distribute): peel [cmd.set "i" n], apply L3.
       ============================================================ *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    eexists.
    split.
    - cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
           WeakestPrecondition.expr_body WeakestPrecondition.literal
           WeakestPrecondition.get dlet.dlet].
      eexists; split; [exact Hlo4_n | reflexivity].
    - cbv [dlet.dlet].
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      (* Apply L3 with frame_locals_wp_list preserving 10 outer locals
         (outx/y/z + runx/y/z + wsx/y/z + n).  L3's statement tracks
         the other 8 locals (buckets_x/y/z + scalars + pointsx/y/z + w). *)
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ |
          eapply frame_locals_wp_list with
            (xs := ["outx"; "outy"; "outz";
                    "runx"; "runy"; "runz";
                    "wsx"; "wsy"; "wsz"; "n"]);
            [ do 10 (apply List.Forall_cons; [cbn; intuition discriminate|]);
              apply List.Forall_nil
            | apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_ox|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_oy|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_oz|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_rx|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_ry|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_rz|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_wx|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_wy|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_wz|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo4_n|];
              apply List.Forall_nil
            | eapply msm_bls12_distribute_wp with
                (w := Z.of_nat w) (n_w := n_w)
                (buckets_x := bx_p) (buckets_y := by_p) (buckets_z := bz_p)
                (bs_x := bs_x4) (bs_y := bs_y4) (bs_z := bs_z4)
                (scalars_p := scalars_p) (scalars := scalars)
                (ppx := pointsx) (ppy := pointsy) (ppz := pointsz)
                (px := px) (py := py) (pz := pz)
                (R := (FElem (Some tight_bounds) outx Xf
                       * FElem (Some tight_bounds) outy Yf
                       * FElem (Some tight_bounds) outz Zf
                       * FElem None runx run0x
                       * FElem None runy run0y
                       * FElem None runz run0z
                       * FElem None wsx  ws0x
                       * FElem None wsy  ws0y
                       * FElem None wsz  ws0z
                       * R)%sep);
              [ exact HCurveAdd
              | (* 0 <= Z.of_nat w < num_windows *)
                unfold num_windows; cbv [c]; Lia.lia
              | exact Hlen4x | exact Hlen4y | exact Hlen4z
              | Lia.lia | Lia.lia
              | exact Hn_len
              | exact Hlen_sx | exact Hlen_xy | exact Hlen_yz
              | (* distribute_inv entry via helper *)
                apply distribute_inv_entry with (ss := scalars) (ps := points_of px py pz);
                [ exact Hn_len
                | rewrite length_points_of_eq by Lia.lia; exact Hlen_sx
                | rewrite length_points_of_eq by Lia.lia;
                  apply (f_equal Z.to_nat) in Hlen4x;
                  rewrite Nat2Z.id in Hlen4x; Lia.lia
                | exact Hid4 ]
              | (* sep *) ecancel_assumption
              | rewrite map.get_put_diff by congruence; exact Hlo4_bx
              | rewrite map.get_put_diff by congruence; exact Hlo4_by
              | rewrite map.get_put_diff by congruence; exact Hlo4_bz
              | rewrite map.get_put_diff by congruence; exact Hlo4_sc
              | rewrite map.get_put_diff by congruence; exact Hlo4_px
              | rewrite map.get_put_diff by congruence; exact Hlo4_py
              | rewrite map.get_put_diff by congruence; exact Hlo4_pz
              | rewrite map.get_put_diff by congruence; exact Hlo4_w
              | rewrite map.get_put_same; reflexivity ]
            ]
        ].
      (* Proper_cmd monotonicity: L3's enriched post implies REST. *)
      cbv beta.
      intros tr5 mem5 l5 [HF5 HL3].
      (* L3 post order: buckets_x, buckets_y, buckets_z, pointsx,
         pointsy, pointsz, scalars, w. *)
      destruct HL3 as
        [Htr5 [bs_x5 [bs_y5 [bs_z5 [Hlen5x [Hlen5y [Hlen5z
         [Hdist5 [Hsep5
          [Hlo5_bx [Hlo5_by [Hlo5_bz [Hlo5_px [Hlo5_py [Hlo5_pz
           [Hlo5_sc Hlo5_w]]]]]]]]]]]]]]]].
      subst tr5.
      (* Extract 10 locals preservations from HF5 (Forall of l4'→l5). *)
      inversion HF5 as [|? ? Hp5_ox  HF5_1];  subst; clear HF5.
      inversion HF5_1 as [|? ? Hp5_oy  HF5_2]; subst; clear HF5_1.
      inversion HF5_2 as [|? ? Hp5_oz  HF5_3]; subst; clear HF5_2.
      inversion HF5_3 as [|? ? Hp5_rx  HF5_4]; subst; clear HF5_3.
      inversion HF5_4 as [|? ? Hp5_ry  HF5_5]; subst; clear HF5_4.
      inversion HF5_5 as [|? ? Hp5_rz  HF5_6]; subst; clear HF5_5.
      inversion HF5_6 as [|? ? Hp5_wx  HF5_7]; subst; clear HF5_6.
      inversion HF5_7 as [|? ? Hp5_wy  HF5_8]; subst; clear HF5_7.
      inversion HF5_8 as [|? ? Hp5_wz  HF5_9]; subst; clear HF5_8.
      inversion HF5_9 as [|? ? Hp5_n   _];     subst; clear HF5_9.
      (* Each Hp5_*: map.get (map.put l4 "i" n_w) x = map.get l5 x.
         Combined with Hlo4_* (via put_diff over "i"), yields Hlo5_*. *)
      assert (Hlo5_ox : map.get l5 "outx" = Some outx)
        by (rewrite <- Hp5_ox, map.get_put_diff by congruence; exact Hlo4_ox).
      assert (Hlo5_oy : map.get l5 "outy" = Some outy)
        by (rewrite <- Hp5_oy, map.get_put_diff by congruence; exact Hlo4_oy).
      assert (Hlo5_oz : map.get l5 "outz" = Some outz)
        by (rewrite <- Hp5_oz, map.get_put_diff by congruence; exact Hlo4_oz).
      assert (Hlo5_rx : map.get l5 "runx" = Some runx)
        by (rewrite <- Hp5_rx, map.get_put_diff by congruence; exact Hlo4_rx).
      assert (Hlo5_ry : map.get l5 "runy" = Some runy)
        by (rewrite <- Hp5_ry, map.get_put_diff by congruence; exact Hlo4_ry).
      assert (Hlo5_rz : map.get l5 "runz" = Some runz)
        by (rewrite <- Hp5_rz, map.get_put_diff by congruence; exact Hlo4_rz).
      assert (Hlo5_wx : map.get l5 "wsx" = Some wsx)
        by (rewrite <- Hp5_wx, map.get_put_diff by congruence; exact Hlo4_wx).
      assert (Hlo5_wy : map.get l5 "wsy" = Some wsy)
        by (rewrite <- Hp5_wy, map.get_put_diff by congruence; exact Hlo4_wy).
      assert (Hlo5_wz : map.get l5 "wsz" = Some wsz)
        by (rewrite <- Hp5_wz, map.get_put_diff by congruence; exact Hlo4_wz).
      assert (Hlo5_n : map.get l5 "n" = Some n_w)
        by (rewrite <- Hp5_n, map.get_put_diff by congruence; exact Hlo4_n).
      (* Post-L3 state: l5 has all 18 locals set, mem5 has bucket arrays
         post-distribute + 11-cell frame, Hdist5 gives distribute_inv w 0
         (the "all scalars processed" state).  Segs 6a/6b/7/8/9 follow. *)

      (* ============================================================
         Segment 6a: store_zero [runx; runy; runz].
         ============================================================ *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      fold WeakestPrecondition.cmd.
      eexists; split.
      { cbv [WeakestPrecondition.dexprs list_map list_map_body
             WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get dlet.dlet].
        eexists; split; [exact Hlo5_rx|].
        eexists; split; [exact Hlo5_ry|].
        eexists; split; [exact Hlo5_rz|].
        reflexivity. }
      eapply Semantics.weaken_call.
      { eapply (HStoreZero runx runy runz run0x run0y run0z).
        ecancel_assumption. }
      cbv beta.
      intros tr6a mem6a rets6a [Hrets6a [Htr6a Hm6a]].
      subst rets6a tr6a.
      destruct g1_identity as [[Xi Yi] Zi] eqn:HgI.
      cbv match in Hm6a.
      cbv [map.putmany_of_list_zip].
      eexists; split; [reflexivity|].

      (* ============================================================
         Segment 6b: store_zero [wsx; wsy; wsz].
         ============================================================ *)
      cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      fold WeakestPrecondition.cmd.
      eexists; split.
      { cbv [WeakestPrecondition.dexprs list_map list_map_body
             WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get dlet.dlet].
        eexists; split; [exact Hlo5_wx|].
        eexists; split; [exact Hlo5_wy|].
        eexists; split; [exact Hlo5_wz|].
        reflexivity. }
      eapply Semantics.weaken_call.
      { eapply (HStoreZero wsx wsy wsz ws0x ws0y ws0z).
        ecancel_assumption. }
      cbv beta.
      intros tr6b mem6b rets6b [Hrets6b [Htr6b Hm6b]].
      subst rets6b tr6b.
      rewrite HgI in Hm6b.
      cbv match in Hm6b.
      cbv [map.putmany_of_list_zip].
      eexists; split; [reflexivity|].

      (* After segs 6a/6b: mem has [FElem tight runx/y/z Xi,Yi,Zi] and
         [FElem tight wsx/y/z Xi,Yi,Zi] (all 6 at g1_identity coords),
         plus bucket arrays at [FElem tight] (from L3's strengthened
         post) + ScalarsArray + G1Array3 + R.  Hsep6b captures this.

         Seg 7 (L4 reduce): peel [cmd.set "i" num_buckets], then
         Proper_cmd + frame_locals_wp_list (8 xs: outx/y/z, scalars,
         pointsx/y/z, n, w) + L4 (msm_bls12_reduce_wp).  L4's post
         gives (exists WXf WYf WZf) at tight_bounds for ws, existential
         RXf/RYf/RZf for run, and tight buckets bs_x'/y'/z'.

         Seg 8 (final HCurveAdd): direct HCurveAdd on
         [outx;wsx;outy;wsy;outz;wsz;outx;outy;outz].  Post: outx/y/z
         at tight_bounds with values g1_add_spec (Xf,Yf,Zf) (WXf,WYf,WZf).

         Seg 9 (outer_inv closure):
         - Unfold outer_inv to [out1 = partial_msm_from (num_windows -
           w - 1) identity ss ps].
         - Use Hw_bd: [num_windows - w - 1 = S (num_windows - S w - 1)].
         - Apply partial_msm_from's S-step to [outer_inv (S w) out0].
         - For the process_window match, bridge L4's WXf/WYf/WZf to
           reduce_buckets via reduce_buckets_eq_scaled_sum (Qed in
           IteratedSepPoints.v).  This is the load-bearing Gallina
           step — L4's current post does NOT directly equate wsx/y/z
           to reduce_buckets bs_x'/y'/z', so this bridge must be
           established separately.

         Sub-admit covers: L4 application + post destructuring +
         HCurveAdd + outer_inv Gallina closure.  ~150 LoC of tactics
         + 1 sub-lemma (bucket bounds bridge for L4→outer_inv via
         reduce_buckets_eq_scaled_sum). *)

      (* ============================================================
         Segment 7/8/9: L4 reduce + HCurveAdd + outer_inv closure.
         L4's strengthened spec now has the reduce_buckets equation.

         Goal shape at this point (verified via MCP 2026-04-19, at
         post-seg-6b):

             exists v, DEXPR mem6b l5 (expr.literal num_buckets) v /\
             (let/d l := #{...l5; "i" => v}# in
              Semantics.exec.exec functions
                (while (i) { body } ; curve_add(...))
                tr mem6b l
                (fun t' m' l' =>
                   exists args, dexprs m' l' [...] args /\
                   Semantics.call functions curve_add_name t' m' args
                     (fun t'' m'' rets =>
                       exists l'', match rets with [] => Some l | ... => None end
                                 = Some l'' /\ tr = t'' /\
                       (exists out1 bs_x' bs_y' bs_z' 6 F-vals, ...))))

         Note: goal is in [Semantics.exec.exec] form, NOT
         [WeakestPrecondition.cmd] form; needs [sound_cmd] bridge.

         Step 7a (sound_cmd bridge): [eapply sound_cmd] — Qed via
         [WeakestPreconditionProperties.sound_cmd].
         Step 7b (peel "i" := num_buckets): [eexists; split;
         [reflexivity | cbv [dlet.dlet]]].
         Step 7c (apply L4): [Proper_cmd] + [frame_locals_wp_list]
         with xs = ["outx";"outy";"outz";"scalars";"pointsx";
                    "pointsy";"pointsz";"n";"w"], then
         [msm_bls12_reduce_wp] with (RX0,RY0,RZ0) := (Xi,Yi,Zi)
         and (WX0,WY0,WZ0) := (Xi,Yi,Zi).  L4's post gives
             mk_point WXf WYf WZf =
               reduce_buckets _ g1_identity g1_add_spec
                              (points_of bs_x6 bs_y6 bs_z6).

         Step 8 (final HCurveAdd): destruct L4's post to get Hsep7
         and Heq_ws; apply [HCurveAdd] with
           (pb1,pp1)=(outx,wsx), (pb2,pp2)=(outy,wsy),
           (pb3,pp3)=(outz,wsz).  Post: outx,y,z updated to
         [g1_add_spec (Xf,Yf,Zf) (WXf,WYf,WZf)].

         Step 9 (outer_inv closure): unfold [outer_inv] to
           [out1 = partial_msm_from (num_windows - w - 1) identity
                      (scalars_to_Z scalars) (points_of px py pz)].
         From [Hw_bd]: [S w <= Z.to_nat num_windows] implies
           [Z.to_nat num_windows - w - 1 = S (Z.to_nat num_windows - S w - 1)].
         By [partial_msm_from]'s [S k] unfold,
           partial_msm_from (S k) identity ss ps
             = partial_msm_from k
                 (g1_add_spec (Nat.iter c double identity)
                    (process_window ss ps k c num_buckets)) ss ps.
         But partial_msm_from is called at the TOP with identity as
         first acc, so [Nat.iter c double identity = identity].
         Thus the S-step on Houter_inv (at [S w]) becomes:
           out0 = partial_msm_from (num_windows - S w - 1) identity ss ps
         (= the right-hand side after one unfold).
         Finally [out1 = g1_add_spec (iter c double out0) win_w] with
           win_w = process_window (scalars_to_Z scalars)
                                   (points_of px py pz)
                                   w c num_buckets
                 = reduce_buckets (fold_left ...).
         The [Heq_ws] from L4's new post
           mk_point WXf WYf WZf = reduce_buckets (points_of bs_x6 bs_y6 bs_z6)
         combined with [Hdist5 : distribute_inv w 0 ...] (which after
         [distribute_inv_exit] matches the fold_left shape of
         process_window) closes the equation.  The intermediate
         Gallina bridge is the load-bearing work — needs a new lemma
         [process_window_as_reduce_buckets] on top of the existing
         [reduce_buckets_eq_scaled_sum] (in IteratedSepPoints.v).

         STATUS 2026-04-19: the sound_cmd bridge (step 7a-7b) is
         verified to work via MCP and is now mechanized below.  The
         remaining ~200 LoC of tactics (steps 7c, 8, 9) plus the new
         [process_window_as_reduce_buckets] Gallina lemma are out of
         scope for the current fix window — a single bare admit is
         preserved after the bridge.

         Admitted count on this file is 3 (L3 [msm_bls12_distribute_wp],
         L5 [this], and [msm_bls12_prelude_wp]) + 1 internal admit (in L3). *)
      (* Step 7a: peel [cmd.set "i" num_buckets] — the DEXPR for the
         literal [num_buckets] is discharged by structural econstructor. *)
      eexists; split; [solve [repeat econstructor]|].
      cbv [dlet.dlet].
      (* Step 7b: bridge [Semantics.exec.exec ...] → [WeakestPrecondition.cmd ...]
         via [sound_cmd] (the Proper adjoint of [Semantics.exec.exec] for
         a full-WP postcondition).  After this, the goal has shape
         [<{ Trace := tr; Memory := mem6b;
             Locals := #{ … l5; "i" => word.of_Z num_buckets }#;
             Functions := functions }>
            bedrock_func_body:(while ... ; curve_add(...))
          <{ post }>]. *)
      eapply WeakestPreconditionProperties.sound_cmd.
      (* Restore section variables' g1_identity form for L4's use.
         seg 6a's destruct rewrote g1_add_identity_l and related. *)
      rewrite <- HgI in g1_add_identity_l.
      rewrite <- HgI in g1_double_identity.
      (* Step 7c: apply L4 (msm_bls12_reduce_wp) inside Proper_cmd
         with frame_locals_wp_list preserving 9 non-L4 locals. *)
      eapply WeakestPreconditionProperties.Proper_cmd;
        [ |
          eapply frame_locals_wp_list with
            (xs := ["outx"; "outy"; "outz";
                    "scalars"; "pointsx"; "pointsy"; "pointsz";
                    "n"; "w"]);
            [ do 9 (apply List.Forall_cons; [cbn; intuition discriminate|]);
              apply List.Forall_nil
            | apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo5_ox|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo5_oy|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo5_oz|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo5_sc|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo5_px|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo5_py|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo5_pz|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo5_n|];
              apply List.Forall_cons; [eexists; rewrite map.get_put_diff by congruence; exact Hlo5_w|];
              apply List.Forall_nil
            | eapply msm_bls12_reduce_wp with
                (buckets_x := bx_p) (buckets_y := by_p) (buckets_z := bz_p)
                (runx := runx) (runy := runy) (runz := runz)
                (wsx := wsx) (wsy := wsy) (wsz := wsz)
                (bs_x := bs_x5) (bs_y := bs_y5) (bs_z := bs_z5)
                (RX0 := Xi) (RY0 := Yi) (RZ0 := Zi)
                (WX0 := Xi) (WY0 := Yi) (WZ0 := Zi)
                (R := (FElem (Some tight_bounds) outx Xf
                       * FElem (Some tight_bounds) outy Yf
                       * FElem (Some tight_bounds) outz Zf
                       * ScalarsArray scalars_p scalars
                       * G1Array3 pointsx pointsy pointsz px py pz
                       * R)%sep);
              [ exact HCurveAdd
              | exact Hlen5x | exact Hlen5y | exact Hlen5z
              | apply (f_equal Z.to_nat) in Hlen5x;
                apply (f_equal Z.to_nat) in Hlen5y;
                rewrite Nat2Z.id in Hlen5x, Hlen5y; Lia.lia
              | apply (f_equal Z.to_nat) in Hlen5y;
                apply (f_equal Z.to_nat) in Hlen5z;
                rewrite Nat2Z.id in Hlen5y, Hlen5z; Lia.lia
              | rewrite HgI; reflexivity
              | rewrite HgI; reflexivity
              | ecancel_assumption
              | rewrite map.get_put_diff by congruence; exact Hlo5_rx
              | rewrite map.get_put_diff by congruence; exact Hlo5_ry
              | rewrite map.get_put_diff by congruence; exact Hlo5_rz
              | rewrite map.get_put_diff by congruence; exact Hlo5_wx
              | rewrite map.get_put_diff by congruence; exact Hlo5_wy
              | rewrite map.get_put_diff by congruence; exact Hlo5_wz
              | rewrite map.get_put_diff by congruence; exact Hlo5_bx
              | rewrite map.get_put_diff by congruence; exact Hlo5_by
              | rewrite map.get_put_diff by congruence; exact Hlo5_bz
              | rewrite map.get_put_same; reflexivity ]
            ]
        ].
      (* Step 8/9: Proper_cmd monotonicity.  Intro post-L4 state and
         destructure L4's strengthened post. *)
      cbv beta.
      intros tr7 mem7 l7 [HF7 HL4].
      destruct HL4 as
        [Htr7 [bs_x6 [bs_y6 [bs_z6 [WXf [WYf [WZf
         [Hlen6x [Hlen6y [Hlen6z [Hsep7
          [Hlo7_bx [Hlo7_by [Hlo7_bz
           [Hlo7_rx [Hlo7_ry [Hlo7_rz
            [Hlo7_wx [Hlo7_wy [Hlo7_wz Heq_ws]]]]]]]]]]]]]]]]]]]].
      subst tr7.
      (* Extract the 9 non-L4-tracked locals from HF7. *)
      inversion HF7 as [|? ? Hp7_ox HF7_1];  subst; clear HF7.
      inversion HF7_1 as [|? ? Hp7_oy HF7_2]; subst; clear HF7_1.
      inversion HF7_2 as [|? ? Hp7_oz HF7_3]; subst; clear HF7_2.
      inversion HF7_3 as [|? ? Hp7_sc HF7_4]; subst; clear HF7_3.
      inversion HF7_4 as [|? ? Hp7_px HF7_5]; subst; clear HF7_4.
      inversion HF7_5 as [|? ? Hp7_py HF7_6]; subst; clear HF7_5.
      inversion HF7_6 as [|? ? Hp7_pz HF7_7]; subst; clear HF7_6.
      inversion HF7_7 as [|? ? Hp7_n  HF7_8]; subst; clear HF7_7.
      inversion HF7_8 as [|? ? Hp7_w  _];     subst; clear HF7_8.
      (* Each Hp7_* : map.get (put l5 "i" _) x = map.get l7 x.
         Combine with Hlo5_* (via put_diff) to get Hlo7_* for non-L4 locals. *)
      assert (Hlo7_ox : map.get l7 "outx" = Some outx)
        by (rewrite <- Hp7_ox, map.get_put_diff by congruence; exact Hlo5_ox).
      assert (Hlo7_oy : map.get l7 "outy" = Some outy)
        by (rewrite <- Hp7_oy, map.get_put_diff by congruence; exact Hlo5_oy).
      assert (Hlo7_oz : map.get l7 "outz" = Some outz)
        by (rewrite <- Hp7_oz, map.get_put_diff by congruence; exact Hlo5_oz).
      assert (Hlo7_sc : map.get l7 "scalars" = Some scalars_p)
        by (rewrite <- Hp7_sc, map.get_put_diff by congruence; exact Hlo5_sc).
      assert (Hlo7_px : map.get l7 "pointsx" = Some pointsx)
        by (rewrite <- Hp7_px, map.get_put_diff by congruence; exact Hlo5_px).
      assert (Hlo7_py : map.get l7 "pointsy" = Some pointsy)
        by (rewrite <- Hp7_py, map.get_put_diff by congruence; exact Hlo5_py).
      assert (Hlo7_pz : map.get l7 "pointsz" = Some pointsz)
        by (rewrite <- Hp7_pz, map.get_put_diff by congruence; exact Hlo5_pz).
      assert (Hlo7_n : map.get l7 "n" = Some n_w)
        by (rewrite <- Hp7_n, map.get_put_diff by congruence; exact Hlo5_n).
      assert (Hlo7_w : map.get l7 "w" = Some (word.of_Z (Z.of_nat w)))
        by (rewrite <- Hp7_w, map.get_put_diff by congruence; exact Hlo5_w).
      (* Now l7 has 18 locals; mem7 has L4's post sep (FElem tight
         wsx/y/z WXf/WYf/WZf, buckets at tight, inner run exists, frame);
         Heq_ws : mk_point WXf WYf WZf = reduce_buckets (points_of bs_x6 bs_y6 bs_z6).
         Next: seg 8 (final HCurveAdd) + seg 9 (outer_inv closure). *)

      (* ============================================================
         Seg 8: final curve_add [outx; wsx; outy; wsy; outz; wsz;
                                 outx; outy; outz].
         ============================================================ *)
      cbv [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
      fold WeakestPrecondition.cmd.
      eexists; split.
      { cbv [WeakestPrecondition.dexprs list_map list_map_body
             WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get dlet.dlet].
        eexists; split; [exact Hlo7_ox|].
        eexists; split; [exact Hlo7_wx|].
        eexists; split; [exact Hlo7_oy|].
        eexists; split; [exact Hlo7_wy|].
        eexists; split; [exact Hlo7_oz|].
        eexists; split; [exact Hlo7_wz|].
        eexists; split; [exact Hlo7_ox|].
        eexists; split; [exact Hlo7_oy|].
        eexists; split; [exact Hlo7_oz|].
        reflexivity. }
      (* Pull out the inner [exists RXf RYf RZf] via SeparationLogic.sep_ex1_r
         (needs explicit unification hint on the outer P). *)
      apply (fun P => @SeparationLogic.sep_ex1_r _ _ _ _ P _) in Hsep7.
      destruct Hsep7 as [RXf Hsep7].
      destruct Hsep7 as [mL [mR [Hspl7 [HL7 HR7]]]].
      destruct HR7 as [RYf [RZf HR7]].
      (* Combine HL7 + HR7 into a flat sep on mem7 for HCurveAdd. *)
      assert (Hsep7_full :
        ((FElem (Some tight_bounds) wsx WXf
          ⋆ FElem (Some tight_bounds) wsy WYf
          ⋆ FElem (Some tight_bounds) wsz WZf
          ⋆ array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes) bx_p bs_x6
          ⋆ array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes) by_p bs_y6
          ⋆ array (FElem (Some tight_bounds)) (word.of_Z felem_size_in_bytes) bz_p bs_z6)
         ⋆ (FElem (Some tight_bounds) runx RXf
            ⋆ FElem (Some tight_bounds) runy RYf
            ⋆ FElem (Some tight_bounds) runz RZf
            ⋆ (FElem (Some tight_bounds) outx Xf
               ⋆ FElem (Some tight_bounds) outy Yf
               ⋆ FElem (Some tight_bounds) outz Zf
               ⋆ ScalarsArray scalars_p scalars
               ⋆ G1Array3 pointsx pointsy pointsz px py pz ⋆ R)))%sep mem7)
        by (exists mL, mR; split; [exact Hspl7|]; split; [exact HL7|exact HR7]).
      (* Apply HCurveAdd with aliasing: pb_i=out_i, pp_i=ws_i. *)
      eapply Semantics.weaken_call.
      { eapply (HCurveAdd outx wsx outy wsy outz wsz Xf WXf Yf WYf Zf WZf).
        ecancel_assumption. }
      cbv beta. intros tr8 mem8 rets8 [Hrets8 [Htr8 Hm8]].
      subst rets8 tr8.
      set (out_tup := g1_add_spec (Xf, Yf, Zf) (WXf, WYf, WZf)) in Hm8.
      destruct out_tup as [[OXf1 OYf1] OZf1] eqn:Hout1.
      cbv match in Hm8.
      exists l7. split; [reflexivity|]. split; [reflexivity|].
      exists (OXf1, OYf1, OZf1), bs_x6, bs_y6, bs_z6,
             RXf, RYf, RZf, WXf, WYf, WZf.

      (* ============================================================
         Seg 9: outer_inv closure + bucket bounds downgrade + sep + locals.
         Remaining:
         - outer_inv (Z.of_nat w) (OXf1,OYf1,OZf1) — seg 9 Gallina, needs
           partial_msm_from S-step on Houter_inv + process_window_as_reduce_buckets
           bridging Heq_ws + Hdist5.
         - lengths (Hlen6x/y/z direct).
         - sep: need tight→None downgrade on bucket arrays via
           array_FElem_drop_bounds_impl1.
         - 15 locals via Hlo7_*. *)
      admit.
  Admitted.

  (** Main WP obligation: full function body as a [WeakestPrecondition.cmd]
      triple, given the three callee specs and initial memory/locals. *)
  Lemma msm_bls12_prelude_wp :
    forall functions
      (HStoreZero : StoreZero3OK functions)
      (outx outy outz scalars_p ppx ppy ppz n_w : word)
      (outx0 outy0 outz0 : F)
      (scalars : list (list word))
      (px py pz : list F)
      (R : mem -> Prop) (tr : Semantics.trace) (mem0 : mem)
      (l0 : locals),
      word.unsigned n_w = Z.of_nat (length scalars) ->
      length scalars = length px ->
      length px = length py ->
      length py = length pz ->
      (FElem None outx outx0
       * FElem None outy outy0
       * FElem None outz outz0
       * ScalarsArray scalars_p scalars
       * G1Array3 ppx ppy ppz px py pz
       * R)%sep mem0 ->
      map.of_list_zip
        ["outx"; "outy"; "outz"; "scalars"; "pointsx"; "pointsy"; "pointsz"; "n"]
        [outx; outy; outz; scalars_p; ppx; ppy; ppz; n_w]
        = Some l0 ->
      (** Full program WP: prelude + outer-loop envelope.  This leaf
          composes the stackalloc peeling, initial [store_zero],
          outer-loop execution via [msm_bls12_outer_body_wp], and the
          [outer_inv 0 ...] → [msm_spec_output] collapse via
          [msm_pippenger_as_partial_msm_from]. *)
      WeakestPrecondition.cmd functions
        (snd (snd (msm_bls12 curve_add_name curve_double_name store_zero_name)))
        tr mem0 l0
        (fun tr' mem' l' =>
           exists rets : list word,
             map.getmany_of_list l' [] = Some rets /\
             rets = [] /\ tr = tr' /\
             exists (outx_f outy_f outz_f : F),
               mk_point outx_f outy_f outz_f
               = msm_spec_output scalars (points_of px py pz)
               /\ (FElem (Some tight_bounds) outx outx_f
                   * FElem (Some tight_bounds) outy outy_f
                   * FElem (Some tight_bounds) outz outz_f
                   * ScalarsArray scalars_p scalars
                   * G1Array3 ppx ppy ppz px py pz
                   * R)%sep mem').
  Proof.
    intros functions HStoreZero
           outx outy outz scalars_p ppx ppy ppz n_w
           outx0 outy0 outz0 scalars px py pz
           R tr mem0 l0
           Hn_len Hlen_sx Hlen_xy Hlen_yz Hsep Hzip.
    (* Unfold the bedrock2 function body.  [msm_bls12] is a 3-tuple
       [(name, (args, rets, body))]; [snd (snd _)] extracts the body. *)
    cbv beta iota match zeta delta
      [msm_bls12 snd fst].
    assert (Hbw_pos : Memory.bytes_per_word width > 0).
    { unfold Memory.bytes_per_word.
      pose proof width_cases as Hwc.
      destruct Hwc as [Hw|Hw]; rewrite Hw; cbv; reflexivity. }
    (* Reusable tactic for the 9 stackalloc peels: bucket-sized (×48×num_buckets)
       or felem-sized.  Both are [k * felem_size_in_bytes] for k in {511, 1}.
       The mod goal reduces uniformly via [felem_size_in_bytes_mod]. *)
    Local Ltac peel_felem_stackalloc Hsz :=
      cbv [dlet.dlet WeakestPrecondition.cmd WeakestPrecondition.cmd_body];
      split;
      [ rewrite Z.mul_mod by Lia.lia;
        rewrite felem_size_in_bytes_mod;
        rewrite Z.mul_0_r;
        apply Z.mod_0_l; Lia.lia
      | idtac ].
    (* Stackallocs 1-3: buckets_x/y/z (each num_buckets × felem_size_in_bytes). *)
    peel_felem_stackalloc __.
    intros a_bx mS_bx mC_bx Hany_bx Hsplit_bx.
    peel_felem_stackalloc __.
    intros a_by mS_by mC_by Hany_by Hsplit_by.
    peel_felem_stackalloc __.
    intros a_bz mS_bz mC_bz Hany_bz Hsplit_bz.
    (* Stackallocs 4-9: runx/y/z + wsx/y/z (each felem_size_in_bytes).
       Mod goal shape is [felem_size_in_bytes mod _ = 0] — direct, no
       multiplication. *)
    Local Ltac peel_single_felem_stackalloc :=
      cbv [dlet.dlet WeakestPrecondition.cmd WeakestPrecondition.cmd_body];
      split; [ apply felem_size_in_bytes_mod | idtac ].
    peel_single_felem_stackalloc.
    intros a_rx mS_rx mC_rx Hany_rx Hsplit_rx.
    peel_single_felem_stackalloc.
    intros a_ry mS_ry mC_ry Hany_ry Hsplit_ry.
    peel_single_felem_stackalloc.
    intros a_rz mS_rz mC_rz Hany_rz Hsplit_rz.
    peel_single_felem_stackalloc.
    intros a_wx mS_wx mC_wx Hany_wx Hsplit_wx.
    peel_single_felem_stackalloc.
    intros a_wy mS_wy mC_wy Hany_wy Hsplit_wy.
    peel_single_felem_stackalloc.
    intros a_wz mS_wz mC_wz Hany_wz Hsplit_wz.
    (* All 9 stackallocs peeled.  Convert each [anybytes] into the
       corresponding [FElem None] (felem-sized) or [array (FElem None)]
       (bucket-sized) predicate. *)
    Existing Instance felem_alloc.
    (* 6 felem-sized via [P_from_bytes]. *)
    pose proof (P_from_bytes a_rx mS_rx Hany_rx) as [RX0_init Hfe_rx].
    pose proof (P_from_bytes a_ry mS_ry Hany_ry) as [RY0_init Hfe_ry].
    pose proof (P_from_bytes a_rz mS_rz Hany_rz) as [RZ0_init Hfe_rz].
    pose proof (P_from_bytes a_wx mS_wx Hany_wx) as [WX0_init Hfe_wx].
    pose proof (P_from_bytes a_wy mS_wy Hany_wy) as [WY0_init Hfe_wy].
    pose proof (P_from_bytes a_wz mS_wz Hany_wz) as [WZ0_init Hfe_wz].
    (* 3 bucket-sized conversions: require [anybytes_to_felem_array] with
       size-rewrite bookkeeping to match the [bucket_bytes]
       ([num_buckets * felem_size_in_bytes]) shape.  Deferred. *)
    (* Next: combine 9 FElem/array chunks with [mem0] sep via the
       [map.split] chain into a unified sep hypothesis on [mComb_wz],
       then the initial [store_zero] call via [HStoreZero], outer while,
       9 deallocs, postcondition.  Deferred. *)
  Admitted.

  (** [msm_bls12_exec_correct] now follows by applying                     *)
  (** [msm_bls12_prelude_wp] directly (its postcondition matches).          *)
  Lemma msm_bls12_exec_correct :
    forall functions
      (HCurveAdd    : CurveAddAliasedOK    functions)
      (HCurveDouble : CurveDoubleInplaceOK functions)
      (HStoreZero   : StoreZero3OK         functions)
      (outx outy outz scalars_p ppx ppy ppz n_w : word)
      (outx0 outy0 outz0 : F)
      (scalars : list (list word))
      (px py pz : list F)
      (R : mem -> Prop) (tr : Semantics.trace) (mem0 : mem)
      (l0 : locals),
      word.unsigned n_w = Z.of_nat (length scalars) ->
      length scalars = length px ->
      length px = length py ->
      length py = length pz ->
      (FElem None outx outx0
       * FElem None outy outy0
       * FElem None outz outz0
       * ScalarsArray scalars_p scalars
       * G1Array3 ppx ppy ppz px py pz
       * R)%sep mem0 ->
      map.of_list_zip
        ["outx"; "outy"; "outz"; "scalars"; "pointsx"; "pointsy"; "pointsz"; "n"]
        [outx; outy; outz; scalars_p; ppx; ppy; ppz; n_w]
        = Some l0 ->
      (** Reformulated 2026-04-17: target [WeakestPrecondition.cmd]
          rather than [Semantics.exec.exec] so the standard
          [straightline] / [while_localsmap] / [ecancel_assumption_fast]
          tactic pipeline applies (the pipeline is tuned for the WP
          surface, not the inductive).  [msm_bls12_ok] bridges to
          [Semantics.exec] via [sound_cmd]. *)
      WeakestPrecondition.cmd functions
        (snd (snd (msm_bls12 curve_add_name curve_double_name store_zero_name)))
        tr mem0 l0
        (fun tr' mem' l' =>
           exists rets : list word,
             map.getmany_of_list l' [] = Some rets /\
             rets = [] /\ tr = tr' /\
             exists (outx_f outy_f outz_f : F),
               mk_point outx_f outy_f outz_f
               = msm_spec_output scalars (points_of px py pz)
               /\ (FElem (Some tight_bounds) outx outx_f
                   * FElem (Some tight_bounds) outy outy_f
                   * FElem (Some tight_bounds) outz outz_f
                   * ScalarsArray scalars_p scalars
                   * G1Array3 ppx ppy ppz px py pz
                   * R)%sep mem').
  Proof.
    intros functions HCurveAdd HCurveDouble HStoreZero
           outx outy outz scalars_p ppx ppy ppz n_w
           outx0 outy0 outz0 scalars px py pz R tr mem0 l0
           Hn_len Hlen_sx Hlen_xy Hlen_yz Hsep Hzip.
    (** [msm_bls12_prelude_wp] has exactly the same goal shape — it
        internally composes the prelude + outer loop + post-loop. *)
    apply (msm_bls12_prelude_wp functions HStoreZero
             outx outy outz scalars_p ppx ppy ppz n_w
             outx0 outy0 outz0 scalars px py pz R tr mem0 l0
             Hn_len Hlen_sx Hlen_xy Hlen_yz Hsep Hzip).
  Qed.

  Theorem msm_bls12_ok :
    forall functions
      (EnvContains : map.get functions "msm_bls12"
        = Some (snd (msm_bls12 curve_add_name curve_double_name store_zero_name)))
      (HCurveAdd    : CurveAddAliasedOK    functions)
      (HCurveDouble : CurveDoubleInplaceOK functions)
      (HStoreZero   : StoreZero3OK         functions),
      spec_of_msm_bls12 functions.
  Proof.
    intros functions EnvContains HCurveAdd HCurveDouble HStoreZero.
    unfold spec_of_msm_bls12.
    intros outx outy outz scalars_p ppx ppy ppz n_w
           outx0 outy0 outz0 scalars px py pz R tr mem0.
    intros (Hn_len & Hlen_sx & Hlen_xy & Hlen_yz & Hsep).
    (* Unfold [Semantics.call] to expose the [argnames/retnames/body]
       destructuring, discharge the function-dictionary lookup with
       [EnvContains], compute the initial locals map by case analysis
       on [map.of_list_zip] (the [None] branch is impossible because
       the two lists are both 8 elements), and appeal to
       [msm_bls12_exec_correct] for the exec triple. *)
    unfold Semantics.call.
    do 3 eexists. split. { exact EnvContains. }
    destruct (map.of_list_zip
              ["outx"; "outy"; "outz"; "scalars";
               "pointsx"; "pointsy"; "pointsz"; "n"]
              [outx; outy; outz; scalars_p; ppx; ppy; ppz; n_w]) as [l0|] eqn:Hzip.
    2: { exfalso. cbn in Hzip. discriminate Hzip. }
    exists l0. split. { reflexivity. }
    (* Weaken the exec's postcondition to produce the form required by
       [Semantics.call]: [exists rets, map.getmany_of_list l' retnames =
       Some rets /\ post tr' mem' rets].  The shapes match up to
       beta-reduction; [Semantics.exec.weaken] handles the wrapping. *)
    eapply Semantics.exec.weaken.
    { (* Bridge WP → exec via sound_cmd, then cite [msm_bls12_exec_correct]. *)
      eapply WeakestPreconditionProperties.sound_cmd.
      eapply msm_bls12_exec_correct with
        (outx := outx) (outy := outy) (outz := outz)
        (scalars_p := scalars_p) (ppx := ppx) (ppy := ppy) (ppz := ppz)
        (n_w := n_w) (outx0 := outx0) (outy0 := outy0) (outz0 := outz0)
        (scalars := scalars) (px := px) (py := py) (pz := pz)
        (R := R) (tr := tr) (mem0 := mem0);
        [ exact HCurveAdd | exact HCurveDouble | exact HStoreZero
        | exact Hn_len | exact Hlen_sx | exact Hlen_xy | exact Hlen_yz
        | exact Hsep | exact Hzip ]. }
    (* Weakening step: translate the post's innards ([exists rets ...])
       into the outer [Semantics.call]-shape. *)
    intros tr' mem' l' Hpost.
    destruct Hpost
      as (rets & Hgm & Hrets & <- & outx_f & outy_f & outz_f & Hpt & Hsep').
    exists rets. split; [exact Hgm|].
    split; [exact Hrets|].
    split; [reflexivity|].
    exists outx_f, outy_f, outz_f. split; [exact Hpt | exact Hsep'].
  Qed.

End PippengerSpec.
