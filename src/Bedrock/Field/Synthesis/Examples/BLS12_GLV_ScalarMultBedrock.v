(** * BLS12-381 GLV Shamir scalar multiplication -- bedrock2 implementation.

    Implements Shamir's trick for the GLV two-scalar multiplication:
      [k]P = [k1]P + [k2]phi(P)
    where (k1, k2) = glv_decompose(k), with k1, k2 each at most 129 bits.

    The function takes phi(P) as a precomputed input (caller multiplies
    P_x by omega) so the loop body avoids loading the omega constant.

    Scalars k1, k2 are pointers to 2-word (128-bit) bignums.
    The loop runs 129 iterations (MSB to LSB via shift-and-test),
    matching the Gallina [shamir_mult 129 k1 k2 P phi_P zero].

    Prerequisites (all compile under Rocq 9):
    - BLS12_GLV_ScalarMult.v   -- Gallina shamir_mult + correctness
    - BLS12_Endomorphism.v     -- omega, lambda constants
    - BLS12_GLV_Decompose.v    -- k1 = k mod lambda, k2 = k div lambda
    - ScalarMult.v             -- existing 256-bit scalar mult (pattern)
    - LoopBody.v               -- per-iteration body pattern
    - BLS12_G1.v               -- BLS12 curve_add (ladderstep)
*)

From Stdlib Require Import ZArith Lia.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import bedrock2.Loops.
Require Import bedrock2.NotationsCustomEntry.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

(* ================================================================== *)
(** * Section 1: Generic Shamir loop body (parametric over width)      *)
(* ================================================================== *)

Section GLV_Shamir_Generic.
  Context {width : Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}
          {group_cmov_alt : string}
          {store_zero : string}.

  Local Notation F := (F M_pos).
  Local Notation Fzero := (F.of_Z M_pos 0).
  Local Notation Fone := (F.of_Z M_pos 1).

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (curve_add_name : string).
  Context (curve_double_name : string).

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  (* GLV scalars are 2-word (128-bit) bignums on a 64-bit machine *)
  Let glv_scalar_words : nat := 2.

  (* 129 iterations: max(bits(k1), bits(k2)) where k1 < lambda < 2^128
     and k2 <= lambda+1 < 2^129 *)
  Let glv_iterations : Z := 129.

  Local Notation eval_bignum n x :=
    (Positional.eval (uweight width) n (List.map word.unsigned x)).

  (* Local spec for shift_scalar (from BignumShift.v, not compiled).
     shift_scalar extracts the low bit and right-shifts a bignum by 1. *)
  Local Instance spec_of_shift_scalar : spec_of "shift_scalar" :=
    fnspec! "shift_scalar"
          (pc px : word)
          / c x R,
    { requires tr mem :=
        (Bignum.Bignum glv_scalar_words px x ⋆ scalar pc c ⋆ R) mem;
      ensures tr' mem' :=
        exists c' x',
          tr = tr'
          /\ eval_bignum glv_scalar_words x / 2 = eval_bignum glv_scalar_words x'
          /\ eval_bignum glv_scalar_words x mod 2 = word.unsigned c'
          /\ ((Bignum.Bignum glv_scalar_words px x' ⋆ scalar pc c' ⋆ R) mem')}.

  (* The Gallina-level curve_add operation (from ladderstep) *)
  Context {curve_add : (F * F * F) -> (F * F * F) -> (F * F * F)}.
  Context {curve_add_id_r : forall x y z, curve_add (x, y, z) (Fzero, Fone, Fzero) = (x, y, z)}.
  Context {curve_add_id_l : forall x y z, curve_add (Fzero, Fone, Fzero) (x, y, z) = (x, y, z)}.
  Context {curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R}.
  Context {curve_add_comm : forall P Q, curve_add P Q = curve_add Q P}.

  (* Connection: the abstract curve_add equals the bedrock2 ladderstep.
     Uses let-destruction to bridge P2.prod and Datatypes.prod. *)
  Context {curve_add_ladderstep : forall X1 X2 Y1 Y2 Z1 Z2 : F,
    let r := @ladderstep_gallina _ three_b_val X1 X2 Y1 Y2 Z1 Z2 in
    curve_add (X1, Y1, Z1) (X2, Y2, Z2) = (P2.car r, P2.car (P2.cdr r), P2.cdr (P2.cdr r))}.

  (* Gallina scalar multiplication via repeated addition *)
  Fixpoint scmul_glv (n : nat) (P : F * F * F) : F * F * F :=
    match n with
    | O => (Fzero, Fone, Fzero)
    | S m => curve_add P (scmul_glv m P)
    end.

  (* Gallina Shamir double-and-add (MSB-first, 129 iterations).
     This mirrors BLS12_GLV_ScalarMult.shamir_mult but is specialized to
     our concrete curve_add. We restate it here to avoid pulling in the
     abstract group algebra infrastructure. *)

  Definition b2z (b : bool) : Z := if b then 1 else 0.

  (* cond_add c P Q = if c then curve_add P Q else P *)
  Definition cond_add (c : bool) (acc P : F * F * F) : F * F * F :=
    if c then curve_add acc P else acc.

  (* Single Shamir iteration: double acc, conditionally add P, conditionally add Q *)
  Definition shamir_step (k1 k2 : Z) (i : nat) (P Q acc : F * F * F) : F * F * F :=
    let acc' := curve_add acc acc in                            (* double *)
    let acc'' := cond_add (Z.testbit k1 (Z.of_nat i)) acc' P in (* cond add P *)
    cond_add (Z.testbit k2 (Z.of_nat i)) acc'' Q.               (* cond add Q *)

  (* Full Shamir loop: bits iterations from (bits-1) down to 0 *)
  Fixpoint shamir_loop (bits : nat) (k1 k2 : Z) (P Q acc : F * F * F) : F * F * F :=
    match bits with
    | O => acc
    | S n => shamir_loop n k1 k2 P Q (shamir_step k1 k2 n P Q acc)
    end.

  (* ================================================================== *)
  (** * Section 2: bedrock2 function definition                         *)
  (* ================================================================== *)

  (** The GLV Shamir scalar multiplication function.

      Arguments:
        outx, outy, outz   -- output point (Jacobian)
        px, py, pz         -- input point P (Jacobian, tight bounds)
        phix, phiy, phiz   -- phi(P) = (omega*P_x, P_y, P_z) (tight bounds)
        pk1                -- pointer to 2-word bignum for k1
        pk2                -- pointer to 2-word bignum for k2

      Algorithm:
        out = (0, 1, 0)    // identity in Jacobian
        for iter = 0 to 128:
          // Extract low bit of k1, shift k1 right
          shift_scalar(cond1, pk1)
          // Extract low bit of k2, shift k2 right
          shift_scalar(cond2, pk2)
          // Double: out = out + out
          curve_add(outx, outx, outy, outy, outz, outz, outx, outy, outz)
          // Conditional add P: aux = cond1 ? P : identity; out = out + aux
          store_zero(auxx, auxy, auxz)
          group_cmov_alt(auxx, auxy, auxz, auxx, auxy, auxz, px, py, pz, cond1)
          curve_add(outx, auxx, outy, auxy, outz, auxz, outx, outy, outz)
          // Conditional add phi(P): aux = cond2 ? phi(P) : identity; out = out + aux
          store_zero(auxx, auxy, auxz)
          group_cmov_alt(auxx, auxy, auxz, auxx, auxy, auxz, phix, phiy, phiz, cond2)
          curve_add(outx, auxx, outy, auxy, outz, auxz, outx, outy, outz)

      NOTE: This processes bits LSB-first (via shift_scalar) which means
      the loop processes k from bit 0 up to bit 128. The doubling of P
      (and phi(P)) at each iteration is handled implicitly through the
      point accumulator. However, the standard Shamir trick is MSB-first.

      For an LSB-first variant we need:
        out = identity
        P_acc = P, Q_acc = phi(P)
        for i = 0 to 128:
          bit1 = k1 & 1; k1 >>= 1
          bit2 = k2 & 1; k2 >>= 1
          if bit1: out += P_acc
          if bit2: out += Q_acc
          P_acc = 2*P_acc    // double P accumulator
          Q_acc = 2*Q_acc    // double Q accumulator

      This requires 3 doublings per iteration (out, P_acc, Q_acc) in the
      worst case, vs 1 doubling + 2 conditional adds for MSB-first.
      But LSB-first matches the existing shift_scalar infrastructure.

      Actually, the existing LoopBody.v already uses the pattern:
        1. shift_scalar to extract low bit
        2. cmov + curve_add to conditionally add
        3. curve_add(P, P) to double the point accumulator
      This means LoopBody.v IS LSB-first! The invariant tracks:
        out = scmul(n mod 2^iter, P_init)
        P   = scmul(2^iter, P_init)  = [2^iter]P_init
      So at each step, P doubles and out conditionally gets P added.

      For Shamir we need TWO such accumulators (P doubles, phi(P) doubles)
      plus the output. The bedrock2 function body follows this pattern:
        - out accumulates the result
        - P doubles each iteration (so P = [2^iter]P_init)
        - phi(P) doubles each iteration (so phi(P) = [2^iter]phi(P_init))
        - At each step: extract bit of k1 and k2, conditionally add P or phi(P)
  *)

  Definition glv_shamir_func : function_t :=
    ("bls12_glv_shamir",
     (["outx"; "outy"; "outz";
       "px"; "py"; "pz";
       "phix"; "phiy"; "phiz";
       "pk1"; "pk2"],
      []:list String.string,
      bedrock_func_body:(
        (* Stack allocations for auxiliary point and condition words *)
        stackalloc felem_size_in_bytes as auxx;
        stackalloc felem_size_in_bytes as auxy;
        stackalloc felem_size_in_bytes as auxz;
        stackalloc (Memory.bytes_per_word width) as cond1;
        stackalloc (Memory.bytes_per_word width) as cond2;
        stackalloc (Memory.bytes_per_word width) as iter;

        (* Initialize output to identity point O = (0, 1, 0) *)
        coq:(cmd.call [] "store_zero"
               [expr.var "outx"; expr.var "outy"; expr.var "outz"]);

        (* Initialize loop counter *)
        coq:(cmd.store access_size.word (expr.var "iter") (expr.literal 0));

        (* Main loop: 129 iterations (bits 0..128) *)
        while (coq:(expr.op bopname.ltu
                      (expr.load access_size.word (expr.var "iter"))
                      (expr.literal glv_iterations))) {
          (* Increment iteration counter *)
          coq:(cmd.store access_size.word (expr.var "iter")
                 (expr.op bopname.add
                    (expr.load access_size.word (expr.var "iter"))
                    (expr.literal 1)));

          (* Extract low bit of k1 and shift k1 right by 1 *)
          coq:(cmd.call [] "shift_scalar"
                 [expr.var "cond1"; expr.var "pk1"]);

          (* Extract low bit of k2 and shift k2 right by 1 *)
          coq:(cmd.call [] "shift_scalar"
                 [expr.var "cond2"; expr.var "pk2"]);

          (* Conditional add P to output:
             aux = cond1 ? P : identity; out = out + aux *)
          coq:(cmd.call [] "store_zero"
                 [expr.var "auxx"; expr.var "auxy"; expr.var "auxz"]);
          coq:(cmd.call [] group_cmov_alt
                 [expr.var "auxx"; expr.var "auxy"; expr.var "auxz";
                  expr.var "auxx"; expr.var "auxy"; expr.var "auxz";
                  expr.var "px"; expr.var "py"; expr.var "pz";
                  expr.var "cond1"]);
          coq:(cmd.call [] curve_add_name
                 [expr.var "outx"; expr.var "auxx";
                  expr.var "outy"; expr.var "auxy";
                  expr.var "outz"; expr.var "auxz";
                  expr.var "outx"; expr.var "outy"; expr.var "outz"]);

          (* Conditional add phi(P) to output:
             aux = cond2 ? phi(P) : identity; out = out + aux *)
          coq:(cmd.call [] "store_zero"
                 [expr.var "auxx"; expr.var "auxy"; expr.var "auxz"]);
          coq:(cmd.call [] group_cmov_alt
                 [expr.var "auxx"; expr.var "auxy"; expr.var "auxz";
                  expr.var "auxx"; expr.var "auxy"; expr.var "auxz";
                  expr.var "phix"; expr.var "phiy"; expr.var "phiz";
                  expr.var "cond2"]);
          coq:(cmd.call [] curve_add_name
                 [expr.var "outx"; expr.var "auxx";
                  expr.var "outy"; expr.var "auxy";
                  expr.var "outz"; expr.var "auxz";
                  expr.var "outx"; expr.var "outy"; expr.var "outz"]);

          (* Double P: px = 2*px via curve_double(px, px) *)
          coq:(cmd.call [] curve_double_name
                 [expr.var "px"; expr.var "py"; expr.var "pz";
                  expr.var "px"; expr.var "py"; expr.var "pz"]);

          (* Double phi(P): phix = 2*phix via curve_double(phix, phix) *)
          coq:(cmd.call [] curve_double_name
                 [expr.var "phix"; expr.var "phiy"; expr.var "phiz";
                  expr.var "phix"; expr.var "phiy"; expr.var "phiz"])
        }
      ))).

  (* ================================================================== *)
  (** * Section 3: WP specification                                     *)
  (* ================================================================== *)

  Local Notation eval n x := (Positional.eval (uweight width) n (List.map word.unsigned x)).

  (* eval of a 2-word list is non-negative (word.unsigned >= 0, weights > 0) *)
  Local Lemma eval_nonneg_2 (x : list word) : 0 <= eval 2 x.
  Proof.
    unfold Positional.eval, Positional.to_associational, Associational.eval.
    destruct x as [|w0 [|w1 rest]]; simpl;
    unfold uweight, ModOps.weight; simpl;
    try (pose proof (word.unsigned_range w0));
    try (pose proof (word.unsigned_range w1));
    try (assert (0 < 2 ^ width) by (apply Z.pow_pos_nonneg; lia));
    try nia; lia.
  Qed.

  Instance spec_of_glv_shamir : spec_of "bls12_glv_shamir" :=
    fnspec! "bls12_glv_shamir"
      (pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2 : word)
      / (Outx Outy Outz Px Py Pz Phix Phiy Phiz : F)
        (k1_words k2_words : list word) R,
      { requires tr mem :=
          0 <= eval glv_scalar_words k1_words < 2 ^ glv_iterations
          /\ 0 <= eval glv_scalar_words k2_words < 2 ^ glv_iterations
          /\ (FElem (Some tight_bounds) pOutx Outx
           * FElem (Some tight_bounds) pOuty Outy
           * FElem (Some tight_bounds) pOutz Outz
           * FElem (Some tight_bounds) pPx Px
           * FElem (Some tight_bounds) pPy Py
           * FElem (Some tight_bounds) pPz Pz
           * FElem (Some tight_bounds) pPhix Phix
           * FElem (Some tight_bounds) pPhiy Phiy
           * FElem (Some tight_bounds) pPhiz Phiz
           * Bignum.Bignum glv_scalar_words pk1 k1_words
           * Bignum.Bignum glv_scalar_words pk2 k2_words
           * R)%sep mem
      ;
        ensures tr' mem' :=
          tr = tr'
          /\ exists Outxnew Outynew Outznew
                    Pxnew Pynew Pznew
                    Phixnew Phiynew Phiznew : F,
             exists k1new k2new : list word,
               (* The output is the Shamir double-scalar multiplication.
                  Using LSB-first accumulation, the result is:
                    out = [k1]P + [k2]phi(P)
                  where k1 = eval(k1_words) and k2 = eval(k2_words).

                  Specifically, the loop invariant ensures:
                    out   = scmul_glv(k1 mod 2^iter, P_init)
                              + scmul_glv(k2 mod 2^iter, phi(P_init))
                    P     = scmul_glv(2^iter, P_init)
                    phi   = scmul_glv(2^iter, phi(P_init))
                  After 129 iterations with k1, k2 < 2^129:
                    out = [k1]P_init + [k2]phi(P_init) *)
               let k1_val := Z.to_nat (eval glv_scalar_words k1_words) in
               let k2_val := Z.to_nat (eval glv_scalar_words k2_words) in
               (Outxnew, Outynew, Outznew) =
                 curve_add (scmul_glv k1_val (Px, Py, Pz))
                           (scmul_glv k2_val (Phix, Phiy, Phiz))
               /\ (FElem (Some tight_bounds) pOutx Outxnew
                  * FElem (Some tight_bounds) pOuty Outynew
                  * FElem (Some tight_bounds) pOutz Outznew
                  * FElem (Some tight_bounds) pPx Pxnew
                  * FElem (Some tight_bounds) pPy Pynew
                  * FElem (Some tight_bounds) pPz Pznew
                  * FElem (Some tight_bounds) pPhix Phixnew
                  * FElem (Some tight_bounds) pPhiy Phiynew
                  * FElem (Some tight_bounds) pPhiz Phiznew
                  * Bignum.Bignum glv_scalar_words pk1 k1new
                  * Bignum.Bignum glv_scalar_words pk2 k2new
                  * R)%sep mem'}.

  (* ================================================================== *)
  (** * Section 4: Loop invariant                                       *)
  (* ================================================================== *)

  (** The LSB-first Shamir loop invariant.

      After [iter] iterations (iter = 0, 1, ..., 129):
      - k1_current = k1_init >> iter  (remaining bits of k1)
      - k2_current = k2_init >> iter  (remaining bits of k2)
      - out = scmul_glv(k1_init mod 2^iter, P_init)
              + scmul_glv(k2_init mod 2^iter, phi_init)
              (accumulated result from processed bits)
      - P_current = scmul_glv(2^iter, P_init)
              = [2^iter]P_init (doubled iter times)
      - phi_current = scmul_glv(2^iter, phi_init)
              = [2^iter]phi_init (doubled iter times)

      This follows the LoopBody.v pattern extended to two scalars. *)

  (* Grouped point predicate: 3 FElems at given pointers *)
  Definition Point3 bnd (px py pz : word) (X Y Z : F) : mem -> Prop :=
    (FElem bnd px X ⋆ FElem bnd py Y ⋆ FElem bnd pz Z)%sep.

  Definition glv_loop_inv
    (pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz : word)
    (pk1 pk2 : word) (a_auxx a_auxy a_auxz a_cond1 a_cond2 a_iter : word)
    (Px_init Py_init Pz_init Phix_init Phiy_init Phiz_init : F)
    (k1_init k2_init : Z)
    (R : mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\
    exists (Outx Outy Outz Px Py Pz Phix Phiy Phiz
            Auxx Auxy Auxz : F)
           (k1_words k2_words : list word)
           (c1 c2 : word) (iter_word : word),
      let iter := (129 - Z.of_nat v)%Z in
      (* Scalar invariants *)
      eval glv_scalar_words k1_words = Z.shiftr k1_init iter
      /\ eval glv_scalar_words k2_words = Z.shiftr k2_init iter
      (* Accumulator invariant *)
      /\ (Outx, Outy, Outz) =
           curve_add
             (scmul_glv (Z.to_nat (k1_init mod 2 ^ iter)) (Px_init, Py_init, Pz_init))
             (scmul_glv (Z.to_nat (k2_init mod 2 ^ iter)) (Phix_init, Phiy_init, Phiz_init))
      (* Point doubling invariants *)
      /\ (Px, Py, Pz) = scmul_glv (Z.to_nat (2 ^ iter)) (Px_init, Py_init, Pz_init)
      /\ (Phix, Phiy, Phiz) = scmul_glv (Z.to_nat (2 ^ iter)) (Phix_init, Phiy_init, Phiz_init)
      (* Memory layout — grouped into Point3 triples to reduce sep conjuncts *)
      /\ (Point3 (Some tight_bounds) pOutx pOuty pOutz Outx Outy Outz
         * Point3 (Some tight_bounds) pPx pPy pPz Px Py Pz
         * Point3 (Some tight_bounds) pPhix pPhiy pPhiz Phix Phiy Phiz
         * Point3 None a_auxx a_auxy a_auxz Auxx Auxy Auxz
         * Bignum.Bignum glv_scalar_words pk1 k1_words
         * Bignum.Bignum glv_scalar_words pk2 k2_words
         * scalar a_cond1 c1
         * scalar a_cond2 c2
         * scalar a_iter iter_word
         * R)%sep m
      (* Locals bindings *)
      /\ map.get l "outx" = Some pOutx
      /\ map.get l "outy" = Some pOuty
      /\ map.get l "outz" = Some pOutz
      /\ map.get l "px" = Some pPx
      /\ map.get l "py" = Some pPy
      /\ map.get l "pz" = Some pPz
      /\ map.get l "phix" = Some pPhix
      /\ map.get l "phiy" = Some pPhiy
      /\ map.get l "phiz" = Some pPhiz
      /\ map.get l "pk1" = Some pk1
      /\ map.get l "pk2" = Some pk2
      /\ map.get l "auxx" = Some a_auxx
      /\ map.get l "auxy" = Some a_auxy
      /\ map.get l "auxz" = Some a_auxz
      /\ map.get l "cond1" = Some a_cond1
      /\ map.get l "cond2" = Some a_cond2
      /\ map.get l "iter" = Some a_iter
      /\ word.unsigned iter_word = iter
      (* Measure: v counts down from 129 to 0 *)
      /\ v = Z.to_nat (glv_iterations - iter).

  Opaque felem_size_in_bytes.
  Opaque Memory.bytes_per_word.
  Opaque glv_scalar_words.
  Opaque glv_iterations.

  (* ================================================================== *)
  (** * Section 5: Correctness lemma                                    *)
  (* ================================================================== *)

  (** Resolve map.get on abstract locals using hypotheses *)
  Local Ltac resolve_map_get :=
    match goal with
    | |- map.get (map.put ?m ?k ?v) ?k' = Some ?e =>
      first
      [ unify k k';
        rewrite map.get_put_same; exact eq_refl
      | rewrite map.get_put_diff by congruence;
        resolve_map_get ]
    | |- map.get ?m ?k = Some ?e =>
      first
      [ assumption
      | match goal with
        | H : map.get m k = Some _ |- _ => exact H
        end ]
    end.

  (** Evaluate dexprs with abstract locals *)
  Local Ltac eval_dexprs_abstract :=
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | eexists; split; [resolve_map_get |]
      | eexists; split; [exact eq_refl |]
      ]).

  (** Process cmd.seq/set with abstract locals *)
  Local Ltac glv_straightline :=
    match goal with
    | |- WeakestPrecondition.cmd _ (cmd.seq _ _) _ _ _ _ =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body]
    | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |]
    | |- WeakestPrecondition.cmd _ cmd.skip _ _ _ ?post =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body]
    end.

  (** The WP proof for the GLV Shamir function.

      PROOF STRATEGY:
      1. Function entry: start_func, process 6 stackallocs
         (3 felem + 3 word-sized), convert anybytes to FElem/scalar.
      2. Initialization: process store_zero(outx,outy,outz) call,
         then store iter=0.
      3. While loop: apply Loops.while_localsmap with glv_loop_inv.
      4. Loop body: 11 calls per iteration.
      5. Post-loop: stack deallocation + postcondition.

      Callee specs are taken as hypotheses since this is in a
      generic section.  The function body uses:
        "store_zero"    -- literal string
        "shift_scalar"  -- literal string
        group_cmov_alt  -- section variable
        curve_add_name  -- section variable *)

  Context (Hcaname : curve_add_name = "curve_add").

  Lemma glv_shamir_ok :
    forall functions
      (EnvContains : map.get functions "bls12_glv_shamir" =
         Some (snd glv_shamir_func))
      (HStoreZero : @StoreZero.spec_of_store_zero
         _ _ _ _ _ _ field_parameters field_representation functions)
      (HShiftScalar : spec_of_shift_scalar functions)
      (HCmovAlt : @CondMoveGroup.spec_of_group_cmov_alt
         _ _ _ _ _ _ field_parameters field_representation
         group_cmov_alt functions)
      (HCurveAdd : @CurveAdd.spec_of_ladderstep
         _ _ _ _ _ _ field_parameters field_representation
         three_b functions)
      (* Aliased curve_add: input1 = output (sound: ladderstep reads before writing) *)
      (HCurveAddInplace : forall pXo pX2 pYo pY2 pZo pZ2
         (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
         (FElem (Some tight_bounds) pXo X ⋆ FElem (Some tight_bounds) pYo Y
          ⋆ FElem (Some tight_bounds) pZo Z ⋆ FElem (Some tight_bounds) pX2 X2'
          ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
          ⋆ R0) m0 ->
         WeakestPrecondition.call functions curve_add_name tr0 m0
           [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
           (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
              let '(Xo', Yo', Zo') := curve_add (X, Y, Z) (X2', Y2', Z2') in
              (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pYo Yo'
               ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pX2 X2'
               ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
               ⋆ R0) m')))
      (* Dedicated in-place doubling: curve_double(P, P) *)
      (HCurveDouble : forall pX pY pZ
         (X Y Z : F) R0 tr0 m0,
         (FElem (Some tight_bounds) pX X ⋆ FElem (Some tight_bounds) pY Y
          ⋆ FElem (Some tight_bounds) pZ Z ⋆ R0) m0 ->
         Semantics.call functions curve_double_name tr0 m0
           [pX; pY; pZ; pX; pY; pZ]
           (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
              let '(Xo, Yo, Zo) := curve_add (X, Y, Z) (X, Y, Z) in
              (FElem (Some tight_bounds) pX Xo ⋆ FElem (Some tight_bounds) pY Yo
               ⋆ FElem (Some tight_bounds) pZ Zo ⋆ R0) m'))),
    spec_of_glv_shamir functions.
  Proof.
    intros.
    unfold spec_of_glv_shamir.
    intros pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
           Outx Outy Outz Px Py Pz Phix Phiy Phiz
           k1_words k2_words R tr mem0 [Hk1_bound [Hk2_bound Hsep]].

    (* === Phase 1: Function entry === *)
    eapply WeakestPreconditionProperties.start_func;
      [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold glv_shamir_func. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* === Phase 2: Process 6 stackallocs === *)
    (* Stackalloc 1: auxx (felem-sized) *)
    repeat straightline.
    split. { apply felem_size_in_bytes_mod. }
    intros a_auxx mStack_auxx mComb_auxx Hany_auxx Hsplit_auxx.
    repeat straightline.

    (* Stackalloc 2: auxy (felem-sized) *)
    split. { apply felem_size_in_bytes_mod. }
    intros a_auxy mStack_auxy mComb_auxy Hany_auxy Hsplit_auxy.
    repeat straightline.

    (* Stackalloc 3: auxz (felem-sized) *)
    split. { apply felem_size_in_bytes_mod. }
    intros a_auxz mStack_auxz mComb_auxz Hany_auxz Hsplit_auxz.
    repeat straightline.

    (* Stackalloc 4: cond1 (word-sized) *)
    split. { apply Z_mod_same_full. }
    intros a_cond1 mStack_cond1 mComb_cond1 Hany_cond1 Hsplit_cond1.
    repeat straightline.

    (* Stackalloc 5: cond2 (word-sized) *)
    split. { apply Z_mod_same_full. }
    intros a_cond2 mStack_cond2 mComb_cond2 Hany_cond2 Hsplit_cond2.
    repeat straightline.

    (* Stackalloc 6: iter (word-sized) *)
    split. { apply Z_mod_same_full. }
    intros a_iter mStack_iter mComb_iter Hany_iter Hsplit_iter.

    (* Convert felem anybytes to FElem None using P_from_bytes from felem_alloc.
       P_from_bytes : forall px, impl1 (anybytes px sz) (ex1 (FElem None px))
       i.e., forall px m, anybytes px sz m -> exists x, FElem None px x m *)
    pose proof (P_from_bytes a_auxx mStack_auxx Hany_auxx)
      as [Auxx_init Hfe_auxx].
    pose proof (P_from_bytes a_auxy mStack_auxy Hany_auxy)
      as [Auxy_init Hfe_auxy].
    pose proof (P_from_bytes a_auxz mStack_auxz Hany_auxz)
      as [Auxz_init Hfe_auxz].

    (* Convert word-sized anybytes to scalars *)
    apply anybytes_to_scalar in Hany_cond1 as [c1_init Hsc_cond1].
    apply anybytes_to_scalar in Hany_cond2 as [c2_init Hsc_cond2].
    apply anybytes_to_scalar in Hany_iter as [iter_init Hsc_iter].

    (* === Phase 3: Process store_zero initialization ===

       The goal is a WP for:
         cmd.seq (cmd.call "store_zero" [outx; outy; outz])
           (cmd.seq (cmd.store iter 0) (cmd.while ...))
       followed by 6 stack deallocations.

       The memory mComb_iter contains:
       - Original inputs (FElem tight for out/p/phi, Bignum for k1/k2, R)
         embedded in the map.split chain from stackallocs
       - Stack FElems (FElem None for auxx/auxy/auxz)
       - Stack scalars (scalar for cond1/cond2/iter)

       We process the store_zero call:
       1. cmd.seq → expose the call
       2. dexprs for arguments [outx; outy; outz]
       3. weaken_call with HStoreZero
       4. Precondition: need FElem None, have FElem (Some tight_bounds)
          → use drop_bounds_FElem to weaken
       5. Postcondition: FElem tight with Fzero/Fone/Fzero (identity)

       Then process store(iter, 0) via straightline.

       Then apply Loops.while_localsmap with glv_loop_inv.

       === Phase 4: while_localsmap application ===
       Apply with:
       - measure v0 := 129 (nat)
       - lt := Nat.lt, well_founded := lt_wf
       - invariant := glv_loop_inv with initial P/phi/k1/k2 values

       Initial invariant (v0=129, iter=0):
       - k1/k2 unchanged (shiftr by 0 = identity)
       - out = identity = curve_add (scmul 0 P) (scmul 0 phi)
       - P = P_init = scmul (2^0) P_init
       - phi = phi_init = scmul (2^0) phi_init

       === Phase 5: Loop body (11 function calls/iteration) ===
       For measure v, the body processes:
       a. store iter = iter + 1
       b. shift_scalar(cond1, pk1): extract k1's low bit, shift k1
       c. shift_scalar(cond2, pk2): extract k2's low bit, shift k2
       d. store_zero(aux) + group_cmov_alt(aux,aux,P,cond1):
          aux = cond1 ? P : O
       e. curve_add(out, aux, out): out += aux
       f. store_zero(aux) + group_cmov_alt(aux,aux,phi,cond2):
          aux = cond2 ? phi : O
       g. curve_add(out, aux, out): out += aux
       h. curve_add(P, P, P): P = 2*P
       i. curve_add(phi, phi, phi): phi = 2*phi

       Each call: glv_straightline + unfold cmd.call + dexprs_abstract
       + weaken_call + sep manipulation. (~300 lines total)

       Invariant preservation: Z arithmetic for scalar decomposition
       (k_init mod 2^(iter+1) decomposition) + scmul_glv properties.

       === Phase 6: Post-loop ===
       After 129 iterations: out = [k1]P + [k2]phi.
       6 stack deallocations (FElem→anybytes, scalar→anybytes).
       Final postcondition: existentials + sep.
       (~100 lines following MillerLoop.v lines 1701-1800) *)

    (* === Tactic: gcall processes one function call end-to-end === *)
    (* Modeled on WPTactics.wp_call + BLS12_377 MillerLoop mcall.
       Handles binop (curve_add), custom fnspec (store_zero, cmov_alt),
       and shift_scalar specs. Avoids repeat straightline. *)
    (* Custom postcall: beta-reduce before matching (fixes abstract locals) *)
    Local Ltac glv_postcall :=
      let t := fresh "t" in let m := fresh "m" in let rets := fresh "rets" in
      let H := fresh "Hpost" in
      intros t m rets H;
      cbv beta in H;
      lazymatch type of H with
      | ?A /\ ?B =>
        let Hrets := fresh "Hrets" in let Hrest := fresh "Hrest" in
        destruct H as [Hrets Hrest];
        subst rets;
        lazymatch type of Hrest with
        | ?C /\ ?D =>
          let Htr := fresh "Htr" in let Hrem := fresh "Hrem" in
          destruct Hrest as [Htr Hrem];
          first [ symmetry in Htr; subst t | subst t | idtac ];
          cbv [map.putmany_of_list_zip];
          (try (eexists; split; [ exact eq_refl | ]))
        | _ =>
          first [ subst t | idtac ];
          cbv [map.putmany_of_list_zip];
          (try (eexists; split; [ exact eq_refl | ]))
        end
      end.

    (* Fast cancel for impl1: match syntactically unifiable non-evar
       conjuncts. Standard cancel_step only handles iff1, not impl1.
       ecancel_step_by_implication can't match equal pairs either
       (it relies on ecancel_impl hints which don't include reflexivity). *)
    Local Ltac cancel_impl_step :=
      let RHS := lazymatch goal with
                 | |- Lift1Prop.impl1 (seps _) (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (idtac; let y := rdelta_var y in is_evar y);
      let LHS := lazymatch goal with
                 | |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
      let i := find_syntactic_unify_deltavar LHS y in
      cancel_seps_at_indices_by_implication i j;
      [exact (impl1_refl _)|].

    (* ecancel with fast impl1 syntactic pre-pass *)
    Local Ltac ecancel_fast :=
      cancel;
      lazymatch goal with
      | |- Lift1Prop.impl1 _ _ =>
        repeat cancel_impl_step;
        repeat ecancel_step_by_implication;
        cbv [seps]; exact impl1_refl
      | |- Lift1Prop.iff1 _ _ =>
        ecancel_steps_at O;
        ecancel_done
      end.

    (* ecancel_assumption using the fast impl1 path.
       Copies the hypothesis first (like ecancel_assumption_with_copy)
       so multi-sep specs (e.g., cmov_alt) can reuse it.
       Handles let-match bindings from curve_add postconditions
       (let '(X,Y,Z) := curve_add ... in sep) by destructing the pair. *)
    Local Ltac ecancel_assumption_fast :=
      multimatch goal with
      | |- ?PG ?m1 =>
        multimatch goal with
        | H: _ ?m2 |- _ =>
          syntactic_unify_deltavar m1 m2;
          let H' := fresh "Hcopy" in
          pose proof H as H';
          cbv beta iota zeta in H';
          lazymatch type of H' with
          | (_ * _)%sep _ =>
            refine (Morphisms.subrelation_refl
                      Lift1Prop.impl1 _ _ _ _ H');
            clear H';
            ecancel_fast
          end
        end
      end.

    Local Ltac gcall spec :=
      try glv_straightline;
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |];
      eapply Semantics.weaken_call;
      [ let H := fresh "Hcall" in pose proof spec as H; eapply H;
        first
        [ wp_binop_precond solve_bounds_auto
        | wp_unop_precond solve_bounds_auto
        | split; ecancel_assumption_fast
        | ecancel_assumption_fast
        | repeat (first
            [ solve_bounds_auto
            | ecancel_assumption_fast
            | split ])
        ]
      | glv_postcall ];
      (* Destruct postcondition existentials *)
      repeat match goal with
      | H : exists _, _ |- _ => destruct H
      end;
      repeat match goal with
      | H : _ /\ _ |- _ =>
          lazymatch type of H with
          | _ = _ /\ _ => destruct H
          | _ /\ _ => destruct H
          end
      end;
      try match goal with
      | H : ?tr = ?t |- _ => first [ subst t | subst tr | idtac ]
      end.

    (* === Phase 3: Process store_zero call + store iter=0 === *)
    (* Process let/d and peel cmd.seq for the store_zero call *)
    cbv [dlet.dlet]. set (l4 := map.put l3 "iter" a_iter).
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    (* Call store_zero. The sep is fragmented across map.split chains.
       Reassemble into a single sep on mComb_iter, then use ecancel_assumption_impl
       which handles FElem (Some tight) -> FElem None via drop_bounds_FElem hint. *)
    destruct Hsplit_auxx as [Heq_auxx Hd_auxx].
    destruct Hsplit_auxy as [Heq_auxy Hd_auxy].
    destruct Hsplit_auxz as [Heq_auxz Hd_auxz].
    destruct Hsplit_cond1 as [Heq_cond1 Hd_cond1].
    destruct Hsplit_cond2 as [Heq_cond2 Hd_cond2].
    destruct Hsplit_iter as [Heq_iter Hd_iter].
    subst mComb_iter mComb_cond2 mComb_cond1 mComb_auxz mComb_auxy mComb_auxx.
    (* Build combined sep using sep_from_put/sep witnesses *)
    assert (HsepAll :
      (FElem (Some tight_bounds) pOutx Outx
       ⋆ FElem (Some tight_bounds) pOuty Outy
       ⋆ FElem (Some tight_bounds) pOutz Outz
       ⋆ FElem (Some tight_bounds) pPx Px
       ⋆ FElem (Some tight_bounds) pPy Py
       ⋆ FElem (Some tight_bounds) pPz Pz
       ⋆ FElem (Some tight_bounds) pPhix Phix
       ⋆ FElem (Some tight_bounds) pPhiy Phiy
       ⋆ FElem (Some tight_bounds) pPhiz Phiz
       ⋆ Bignum glv_scalar_words pk1 k1_words
       ⋆ Bignum glv_scalar_words pk2 k2_words
       ⋆ R
       ⋆ Compilation2.FElem None a_auxx Auxx_init
       ⋆ Compilation2.FElem None a_auxy Auxy_init
       ⋆ Compilation2.FElem None a_auxz Auxz_init
       ⋆ scalar a_cond1 c1_init
       ⋆ scalar a_cond2 c2_init
       ⋆ scalar a_iter iter_init)
      (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy) mStack_auxz) mStack_cond1) mStack_cond2) mStack_iter)).
    { (* Each putmany step: (P * Q)(putmany m1 m2) from P m1 and Q m2 and disjoint m1 m2 *)
      (* iter *)
      exists (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy) mStack_auxz) mStack_cond1) mStack_cond2), mStack_iter.
      split. { split; [reflexivity | exact Hd_iter]. }
      split; [| exact Hsc_iter].
      (* cond2 *)
      exists (map.putmany (map.putmany (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy) mStack_auxz) mStack_cond1), mStack_cond2.
      split. { split; [reflexivity | exact Hd_cond2]. }
      split; [| exact Hsc_cond2].
      (* cond1 *)
      exists (map.putmany (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy) mStack_auxz), mStack_cond1.
      split. { split; [reflexivity | exact Hd_cond1]. }
      split; [| exact Hsc_cond1].
      (* auxz *)
      exists (map.putmany (map.putmany mem0 mStack_auxx) mStack_auxy), mStack_auxz.
      split. { split; [reflexivity | exact Hd_auxz]. }
      split; [| exact Hfe_auxz].
      (* auxy *)
      exists (map.putmany mem0 mStack_auxx), mStack_auxy.
      split. { split; [reflexivity | exact Hd_auxy]. }
      split; [| exact Hfe_auxy].
      (* auxx *)
      exists mem0, mStack_auxx.
      split. { split; [reflexivity | exact Hd_auxx]. }
      split; [ecancel_assumption | exact Hfe_auxx]. }

    exists [pOutx; pOuty; pOutz]. split.
    { cbv [dexprs list_map list_map_body WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet].
      repeat (first [exact eq_refl | eexists; split; [subst l4 l3 l2 l1 l0 l; resolve_map_get |]]). }
    eapply Semantics.weaken_call.
    1: { eapply HStoreZero. ecancel_assumption_impl. }
    (* Manual postcall processing (wp_postcall_auto can't match this shape) *)
    intros t'0 m'0 rets0 [Hrets0 [Htr0 Hsep0]].
    subst rets0. symmetry in Htr0. subst t'0.
    cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
    (* store iter = 0: resolve DEXPR + memory store manually *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    letexists. split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
           WeakestPrecondition.expr_body WeakestPrecondition.get dlet.dlet].
      eexists. split; [subst l4; rewrite map.get_put_same; exact eq_refl
                       | exact eq_refl]. }
    letexists. split.
    { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
           WeakestPrecondition.expr_body WeakestPrecondition.literal dlet.dlet].
      exact eq_refl. }
    eapply store_word_of_sep.
    { pose proof Hsep0 as H'. ecancel_assumption. }
    intros m_store Hsep_store.

    (* === Phase 4: Apply Loops.while_localsmap === *)

    eapply Loops.while_localsmap
      with (v0 := 129%nat)
           (lt := Nat.lt)
           (invariant := glv_loop_inv
                    pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz
                    pk1 pk2 a_auxx a_auxy a_auxz a_cond1 a_cond2 a_iter
                    Px Py Pz Phix Phiy Phiz
                    (eval glv_scalar_words k1_words) (eval glv_scalar_words k2_words)
                    R tr).

    (* Well-foundedness *)
    { exact lt_wf. }

    (* Initial invariant (v0 = 129, iter = 0) *)
    { unfold glv_loop_inv.
      split; [reflexivity |].
      (* After store_zero: outx=Fzero, outy=Fone, outz=Fzero (identity).
         After store iter=0: iter_word = word.of_Z 0.
         k1/k2 unchanged, P/phi unchanged, aux/cond unchanged.

         Provide existential witnesses: the current values of all fields.
         Identity point: (Fzero, Fone, Fzero)
         P unchanged: (Px, Py, Pz)
         phi unchanged: (Phix, Phiy, Phiz)
         aux: initial values from P_from_bytes
         k1/k2: unchanged from input
         cond1/cond2: initial from anybytes_to_scalar
         iter_word: word.of_Z 0 (from the store we just did)

         Scalar invariants at iter=0:
         - Z.shiftr k1_init 0 = k1_init = eval k1_words  (OK)
         - Z.shiftr k2_init 0 = k2_init = eval k2_words  (OK)
         - k1_init mod 2^0 = 0, so scmul_glv 0 P = identity  (OK)
         - k2_init mod 2^0 = 0, so scmul_glv 0 phi = identity  (OK)
         - curve_add identity identity = identity  (need id properties)
         - 2^0 = 1, scmul_glv 1 P = curve_add P identity = P  (OK)

         The sep and locals follow from the current state after
         store_zero + store iter. *)
      (* Witnesses: identity output, unchanged P/phi/aux/k/cond, iter=0 *)
      exists Fzero, Fone, Fzero, Px, Py, Pz, Phix, Phiy, Phiz,
             Auxx_init, Auxy_init, Auxz_init,
             k1_words, k2_words, c1_init, c2_init, (word.of_Z 0).
      cbv [glv_iterations]. cbv beta.
      (* Scalar: Z.shiftr k 0 = k *)
      rewrite !Z.shiftr_0_r.
      (* Accumulator: k mod 1 = 0, scmul_glv 0 = identity *)
      rewrite !Z.mod_1_r. simpl scmul_glv.
      rewrite curve_add_id_l.
      (* Points: scmul_glv 1 P = curve_add P identity = P *)
      rewrite !curve_add_id_r.
      subst a v.
      repeat split; try reflexivity.
      (* Sep: change Compilation2.FElem to FElem, unfold Point3 for ecancel *)
      all: try (change Compilation2.FElem with FElem in Hsep_store;
                unfold Point3; ecancel_assumption).
      (* Locals *)
      all: try (subst l4 l3 l2 l1 l0 l; resolve_map_get).
      (* iter word value *)
      all: try (change (Z.of_nat 129) with 129%Z;
                rewrite word.unsigned_of_Z; cbv; reflexivity). }

    (* Loop body + post-loop: Loops.while_localsmap generates 2 subgoals:
       1. Loop body: forall vi, invariant vi -> exists br,
            expr ... br /\
            (br <> 0 -> body; exists vi', invariant vi' /\ vi' < vi) /\
            (br = 0  -> postcondition)
       2. (already handled by well_founded + initial invariant above)

       Actually, while_localsmap generates 3 subgoals:
       a. well_founded (done above)
       b. initial invariant (done above)
       c. forall v t m l, invariant v t m l ->
            exists br, expr ... br /\
            (br <> 0 -> loop body WP) /\
            (br = 0  -> post-loop WP)

       So we have ONE subgoal here combining body and post-loop. *)
    { intros vi ti mi li Hinv.
      unfold glv_loop_inv in Hinv.
      destruct Hinv as [Htr_i Hinv_body].
      destruct Hinv_body as [Outx_i [Outy_i [Outz_i [Px_i [Py_i [Pz_i
        [Phix_i [Phiy_i [Phiz_i [Auxx_i [Auxy_i [Auxz_i
        [k1w_i [k2w_i [c1_i [c2_i [iw_i
        Hinv_conj]]]]]]]]]]]]]]]]].
      subst ti.

      (* Destruct all conjuncts from the invariant *)
      destruct Hinv_conj as
        [Hk1_i [Hk2_i [Hout_i [Hp_i [Hphi_i
        [Hsep_i
        [Hl_outx [Hl_outy [Hl_outz
        [Hl_px [Hl_py [Hl_pz
        [Hl_phix [Hl_phiy [Hl_phiz
        [Hl_pk1 [Hl_pk2
        [Hl_auxx [Hl_auxy [Hl_auxz
        [Hl_cond1 [Hl_cond2 [Hl_iter
        [Hiter_val Hv_eq]]]]]]]]]]]]]]]]]]]]]]]].

      (* Evaluate branch condition:
         expr.op bopname.ltu
           (expr.load access_size.word (expr.var "iter"))
           (expr.literal glv_iterations)
         This loads the iter counter from memory, compares with 129.
         Result is word.b2w (word.ltu iter_word (word.of_Z 129)). *)

      (* The branch value is computed from memory (load from a_iter).
         We need to provide the value and show the expression evaluates to it.
         From Hsep_i: (scalar a_iter iw_i ⋆ ...) mi
         From Hiter_val: word.unsigned iw_i = 129 - Z.of_nat vi *)

      (* Provide branch value: word encoding of (iter < 129) *)
      exists (word.b2w (word.ltu iw_i (word.of_Z glv_iterations))).
      split.
      { (* Evaluate branch expression:
           expr.op bopname.ltu (expr.load access_size.word (expr.var "iter")) (expr.literal glv_iterations)
           The load reads iw_i from scalar a_iter, then compares with 129. *)
        cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.load dlet.dlet].
        rewrite Hl_iter.
        (* Need to show: load from (scalar a_iter iw_i) yields iw_i *)
        eexists. split. { exact eq_refl. }
        eexists. split.
        { eapply load_word_of_sep. ecancel_assumption. }
        cbv [Semantics.interp_binop literal dlet.dlet word.b2w Z.b2z].
        destruct (word.ltu iw_i (word.of_Z glv_iterations)); exact eq_refl. }

      split.
      { (* TRUE branch: iter < 129, i.e. vi > 0 *)
        intro Hne.

        (* Process store: iter = iter + 1 *)
        glv_straightline.  (* cmd.seq — peel to expose store + rest *)
        (* cmd.store iter (iter+1): manual resolution for abstract locals *)
        straightline. straightline.
        exists a_iter. split.
        { cbv [WeakestPrecondition.dexpr WeakestPrecondition.expr
               WeakestPrecondition.expr_body WeakestPrecondition.get dlet.dlet].
          eexists. split; [exact Hl_iter | exact eq_refl]. }
        (* Evaluate load(iter) + 1, then store *)
        eexists. split.
        { (* DEXPR: load(iter) + 1 *)
          eexists. split. { exact Hl_iter. }
          eexists. split. { eapply load_word_of_sep. ecancel_assumption. }
          cbv [Semantics.interp_binop].
          exact eq_refl. }
        eapply store_word_of_sep. { ecancel_assumption. }
        intros m_iter Hsep_iter.

        (* Flatten right-associated sep from store_word_of_sep.
           Build a flat sep hypothesis via ecancel from Hsep_i + the iter store. *)
        (* Hsep_iter from store_word_of_sep is right-assoc with scalar a_iter at front.
           Don't flatten — just keep it and let gcall_explicit use the slow cancel path
           for the first call, then impl1_refl for subsequent same-order calls. *)

        (* === Loop body: 10 function calls + invariant restoration === *)

        (* Memory optimization: clear all stale stackalloc/init hypotheses.
           After the while loop setup, only the loop invariant's sep (Hsep_i
           destructed into Hk1_i..Hv_eq) and the iter store (Hsep_iter → m_iter)
           matter. Everything from Phase 1-3 is dead weight. *)
        (* Aggressive cleanup: keep only what the 10 gcalls need. *)
        clear - functions HStoreZero HShiftScalar HCmovAlt
                HCurveAddInplace HCurveDouble
                pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
                a_auxx a_auxy a_auxz a_cond1 a_cond2 a_iter
                vi li
                Outx_i Outy_i Outz_i Px_i Py_i Pz_i
                Phix_i Phiy_i Phiz_i
                Auxx_i Auxy_i Auxz_i k1w_i k2w_i c1_i c2_i iw_i
                Hk1_i Hk2_i Hout_i Hp_i Hphi_i
                Hl_outx Hl_outy Hl_outz Hl_px Hl_py Hl_pz
                Hl_phix Hl_phiy Hl_phiz Hl_pk1 Hl_pk2
                Hl_auxx Hl_auxy Hl_auxz Hl_cond1 Hl_cond2 Hl_iter
                Hiter_val Hv_eq Hne
                m_iter mi Hsep_iter Hsep_i
                Px Py Pz Phix Phiy Phiz R tr
                curve_add_id_r curve_add_id_l curve_add_assoc curve_add_comm
                mem_ok word_ok locals_ok env_ok ext_spec_ok.

        (* Memory optimization: clear stale sep hypotheses after each call.
           Each gcall produces a fresh sep on new memory; old seps are dead weight. *)
        Local Ltac clear_stale_seps :=
          lazymatch goal with
          | |- WeakestPrecondition.cmd _ _ _ ?mcur _ _ =>
            repeat match goal with
            | H : _ ?m |- _ =>
              lazymatch type of H with
              | context[Separation.sep] =>
                lazymatch m with mcur => fail | _ => clear H end
              | context[FElem] =>
                lazymatch m with mcur => fail | _ => clear H end
              end
            end
          | _ => idtac
          end.

        (* Helper: solve store_zero FElem None precondition from FElem tight.
           Must destruct curve_add let-bindings first so sep unifies. *)
        Local Ltac solve_store_zero_pre_impl :=
          (* Destruct curve_add let-bindings in hypotheses only *)
          repeat match goal with
          | H : context[curve_add (?a, ?b, ?c) (?d, ?e, ?ff)] |- _ =>
            destruct (curve_add (a, b, c) (d, e, ff)) as [[? ?] ?] eqn:? in H
          end;
          match goal with
          | Hrem : (_ ⋆ _) ?m |- (_ ⋆ _) ?m =>
            refine (Morphisms.subrelation_refl Lift1Prop.impl1 _ _ _ m Hrem);
            cancel;
            repeat ecancel_step_by_implication;
            try (cbn [seps]; apply impl1_refl)
          end.

        (* Flatten right-associated sep hypotheses to left-associated *)
        Local Ltac flatten_seps :=
          repeat match goal with
          | H : (_ ⋆ _) ?m |- _ =>
            lazymatch type of H with
            | Separation.sep _ (Separation.sep _ _) _ =>
              apply sep_assoc in H
            end
          end.

        Local Ltac gcall_clean spec :=
          gcall spec;
          try lazymatch goal with
          | |- WeakestPrecondition.cmd _ _ _ _ _ _ => idtac
          end.

        (* Tactic for calls with explicit spec args *)
        Local Ltac gcall_explicit spec pc px c x :=
          try glv_straightline;
          unfold1_cmd_goal; cbv beta match delta [cmd_body];
          letexists; split; [solve [eval_dexprs_abstract] |];
          eapply Semantics.weaken_call;
          [ pose proof (spec pc px c x) as HS; eapply HS;
            ecancel_assumption_fast
          | glv_postcall ];
          repeat match goal with
          | H : exists _, _ |- _ => destruct H
          end;
          repeat match goal with
          | H : _ /\ _ |- _ =>
              lazymatch type of H with
              | _ = _ /\ _ => destruct H
              | _ /\ _ => destruct H
              end
          end;
          try match goal with
          | H : ?tr = ?t |- _ => first [ subst t | subst tr | idtac ]
          end;
          idtac.

        (* === Process all 10 loop body calls === *)

        (* Flatten the right-associated sep from store_word_of_sep and
           unfold Point3 so that ecancel can match individual FElems.
           This is critical for resolving frame evars during gcall. *)
        unfold Point3 in Hsep_iter.
        flatten_seps.

        (* Call 1: shift_scalar(cond1, pk1) *)
        gcall_explicit HShiftScalar a_cond1 pk1 c1_i k1w_i.
        (* Call 2: shift_scalar(cond2, pk2) *)
        gcall_explicit HShiftScalar a_cond2 pk2 c2_i k2w_i.
        (* Call 3: store_zero(aux) *)
        gcall_clean HStoreZero.
        (* Call 4: cmov_alt(aux, aux, P, cond1) *)
        gcall HCmovAlt.
        all: try (unfold ZRange.is_bounded_by_bool; simpl;
            rewrite Bool.andb_true_iff; split; apply Z.leb_le;
            match goal with
            | H : _ mod 2 = word.unsigned _ |- _ => rewrite <- H
            end;
            pose proof (Z.mod_pos_bound
              (eval glv_scalar_words k1w_i) 2 ltac:(lia)); lia).
        (* Call 5: curve_add(out, aux, out) *)
        gcall_clean HCurveAddInplace.
        (* Destruct curve_add let-bindings BEFORE call 6:
           1) puts result variables in scope for evar resolution
           2) preserves equations for algebraic goals *)
        Opaque curve_add.
        repeat match goal with
        | H : context[curve_add (?a, ?b, ?c) (?d, ?e, ?ff)] |- _ =>
          let r := fresh "ca" in
          set (r := curve_add (a, b, c) (d, e, ff)) in H;
          let Heq := fresh "Hca_eq" in
          destruct r as [[? ?] ?] eqn:Heq;
          symmetry in Heq
        end.
        Transparent curve_add.
        (* Call 6: store_zero(aux) *)
        gcall_clean HStoreZero.
        (* Call 7: cmov_alt(aux, aux, phi, cond2) *)
        gcall HCmovAlt.
        all: try (unfold ZRange.is_bounded_by_bool; simpl;
            rewrite Bool.andb_true_iff; split; apply Z.leb_le;
            match goal with
            | H : _ mod 2 = word.unsigned _ |- _ => rewrite <- H
            end;
            pose proof (Z.mod_pos_bound
              (eval glv_scalar_words k2w_i) 2 ltac:(lia)); lia).
        (* Call 8: curve_add(out, aux, out) *)
        gcall_clean HCurveAddInplace.
        (* Destruct curve_add let-bindings before calls 9-10 *)
        Opaque curve_add.
        repeat match goal with
        | H : context[curve_add (?a, ?b, ?c) (?d, ?e, ?ff)] |- _ =>
          let r := fresh "ca" in
          set (r := curve_add (a, b, c) (d, e, ff)) in H;
          let Heq := fresh "Hca_eq" in
          destruct r as [[? ?] ?] eqn:Heq;
          symmetry in Heq
        end.
        Transparent curve_add.
        (* Call 9: curve_add(P, P, P) — P = 2P *)
        gcall_clean HCurveDouble.
        (* Destruct curve_add let-binding before call 10 *)
        Opaque curve_add.
        repeat match goal with
        | H : context[curve_add (?a, ?b, ?c) (?d, ?e, ?ff)] |- _ =>
          let r := fresh "ca" in
          set (r := curve_add (a, b, c) (d, e, ff)) in H;
          let Heq := fresh "Hca_eq" in
          destruct r as [[? ?] ?] eqn:Heq;
          symmetry in Heq
        end.
        Transparent curve_add.
        (* Call 10: curve_add(phi, phi, phi) — phi = 2*phi *)
        gcall_clean HCurveDouble.

        (* === Loop invariant restoration === *)
        Redirect "/tmp/glv_after_calls" Show.
        (* Provide the decreasing variant *)
        exists (vi - 1)%nat. unfold Markers.split.
        (* Establish vi > 0 before splitting — needed in both branches *)
        assert (Hvi_gt0 : (vi > 0)%nat).
        { rewrite (@word.unsigned_b2w _ _ word_ok) in Hne.
          pose proof (@word.unsigned_ltu _ _ word_ok iw_i (word.of_Z glv_iterations)) as Hltu.
          destruct (word.ltu iw_i (word.of_Z glv_iterations)) eqn:Eb;
            [| exfalso; apply Hne; cbn; reflexivity].
          symmetry in Hltu; apply Z.ltb_lt in Hltu.
          rewrite Hiter_val, word.unsigned_of_Z in Hltu.
          cbv [glv_iterations] in Hltu. unfold word.wrap in Hltu.
          destruct (width_cases) as [Hw|Hw]; rewrite Hw in Hltu;
            (change (129 mod 2 ^ 32) with 129 in Hltu
             || change (129 mod 2 ^ 64) with 129 in Hltu); lia. }
        split.
        2: { lia. }
        (* Provide the loop invariant *)
        unfold glv_loop_inv. subst. split. { reflexivity. }
        (* Destruct call 10's curve_add let-binding in Hrem4 *)
        Opaque curve_add.
        match goal with
        | H : context[curve_add (?a, ?b, ?c) (?d, ?e, ?ff)] |- _ =>
          let r := fresh "ca" in
          set (r := curve_add (a, b, c) (d, e, ff)) in H;
          let Heq := fresh "Hca_eq" in
          destruct r as [[? ?] ?] eqn:Heq;
          symmetry in Heq
        end.
        Transparent curve_add.
        (* Variable mapping (from auto-naming):
           - f2, f3, f4   = Out final (call 8 curve_add_inplace, = f11,f12,f13 = ca1)
           - f8, f9, f10  = P doubled (call 9 curve_add_double)
           - f14, f15, f16 = Phi doubled (call 10 curve_add_double)
           - x6, x7, x8   = Aux (cmov_alt call 7)
           - x0/x2 = k1/k2 words, x/x1 = cond1/cond2 *)
        exists f2, f3, f4, f8, f9, f10, f14, f15, f16, x6, x7, x8.
        exists x0, x2, x, x1, (word.add iw_i (word.of_Z 1)).
        (* Split the big conjunction *)
        repeat split.
        (* Sep: unfold Point3, use ecancel_assumption_fast on Hrem4 (m8) *)
        all: try match goal with |- (_ ⋆ _) ?m =>
          unfold Point3;
          ecancel_assumption_fast
        end.
        (* Locals *)
        all: try resolve_map_get.
        (* Normalize Z.of_nat (vi-1) to Z.of_nat vi - 1 in all goals *)
        all: try (rewrite (Nat2Z.inj_sub vi 1) by lia;
                  change (Z.of_nat 1) with 1%Z).
        (* Scalar shifts: use transitivity + shiftr_from_div2 *)
        all: try (
          transitivity (Z.shiftr (eval glv_scalar_words k1_words) ((129 - Z.of_nat vi) + 1));
          [rewrite <- H0, Hk1_i;
           apply (shiftr_from_div2 _ _ (129 - Z.of_nat vi));
           [pose proof (word.unsigned_range iw_i); lia | reflexivity]
          | replace ((129 - Z.of_nat vi) + 1) with (129 - (Z.of_nat vi - 1)) by lia;
            reflexivity]).
        all: try (
          transitivity (Z.shiftr (eval glv_scalar_words k2_words) ((129 - Z.of_nat vi) + 1));
          [rewrite <- H4, Hk2_i;
           apply (shiftr_from_div2 _ _ (129 - Z.of_nat vi));
           [pose proof (word.unsigned_range iw_i); lia | reflexivity]
          | replace ((129 - Z.of_nat vi) + 1) with (129 - (Z.of_nat vi - 1)) by lia;
            reflexivity]).
        (* Word arithmetic *)
        all: try (rewrite word.unsigned_add; rewrite Hiter_val;
                  rewrite word.unsigned_of_Z_1; unfold word.wrap;
                  destruct (width_cases) as [Hw|Hw]; rewrite Hw;
                  change (1 mod 2 ^ 32) with 1; change (1 mod 2 ^ 64) with 1;
                  rewrite Z.mod_small by
                    (pose proof (word.unsigned_range iw_i); lia);
                  pose proof (word.unsigned_range iw_i); lia).
        (* Nat arithmetic *)
        all: try (
          cbv [glv_iterations];
          replace (Z.of_nat vi - 1) with (Z.of_nat (vi - 1)) by
            (rewrite Nat2Z.inj_sub by lia; change (Z.of_nat 1) with 1%Z; ring);
          replace (129 - (129 - Z.of_nat (vi - 1))) with (Z.of_nat (vi - 1)) by
            (pose proof (word.unsigned_range iw_i); lia);
          rewrite Nat2Z.id; reflexivity).
        (* Remaining: accumulator, P doubling, Phi doubling *)
        (* P doubling: (f8, f9, f10) = scmul_glv (2^...) P *)
        2: { change scmul_glv with (scmul Fzero Fone curve_add) in Hp_i.
             rewrite Hca_eq2, Hp_i.
             replace (129 - (Z.of_nat vi - 1)) with ((129 - Z.of_nat vi) + 1) by lia.
             symmetry.
             apply scmul_pow2_succ; try assumption;
             pose proof (word.unsigned_range iw_i); lia. }
        (* Phi doubling: (f14, f15, f16) = scmul_glv (2^...) Phi *)
        2: { change scmul_glv with (scmul Fzero Fone curve_add) in Hphi_i.
             unfold ca in Hca_eq4.
             rewrite Hca_eq4, Hphi_i.
             replace (129 - (Z.of_nat vi - 1)) with ((129 - Z.of_nat vi) + 1) by lia.
             symmetry.
             apply scmul_pow2_succ; try assumption;
             pose proof (word.unsigned_range iw_i); lia. }
        (* Accumulator: (f2, f3, f4) = curve_add (scmul k1' P) (scmul k2' Phi) *)
        (* Rewrite through the equation chain to expose the curve_add structure *)
        rewrite Hca_eq0, Hca_eq3. unfold ca1.
        rewrite Hca_eq, Hca_eq1. unfold ca0.
        (* Now: curve_add (curve_add (Outx_i,...) (x3,x4,x5)) (x6,x7,x8) = ... *)
        change scmul_glv with (scmul Fzero Fone curve_add) in *.
        rewrite Hout_i.
        (* Connect cmov_alt outputs to scmul: x3x4x5 = scmul b1 P_i, x6x7x8 = scmul b2 Phi_i *)
        set (iter := 129 - Z.of_nat vi) in *.
        (* Connect condition bits to Z.b2z form *)
        assert (Hb1 : word.unsigned x =
                Z.b2z (Z.testbit (eval glv_scalar_words k1_words) iter)).
        { rewrite <- H1, Hk1_i.
          apply Z_shiftr_mod2_b2z; [|unfold iter; pose proof (word.unsigned_range iw_i); lia].
          exact (eval_nonneg_2 _). }
        assert (Hb2 : word.unsigned x1 =
                Z.b2z (Z.testbit (eval glv_scalar_words k2_words) iter)).
        { rewrite <- H5, Hk2_i.
          apply Z_shiftr_mod2_b2z; [|unfold iter; pose proof (word.unsigned_range iw_i); lia].
          exact (eval_nonneg_2 _). }
        (* Case analysis on bit values to show (x3,x4,x5) = scmul b1 P_i *)
        assert (Hcmov1 : (x3, x4, x5) =
          scmul Fzero Fone curve_add
            (Z.to_nat (Z.b2z (Z.testbit (eval glv_scalar_words k1_words) iter)))
            (Px_i, Py_i, Pz_i)).
        { destruct (word.unsigned x =? 1) eqn:Hbit1.
          - (* bit = 1: scmul 1 P_i = P_i *)
            apply Z.eqb_eq in Hbit1.
            replace (Z.b2z _) with 1 by (rewrite <- Hb1; symmetry; exact Hbit1).
            simpl. rewrite curve_add_id_r. rewrite H7, H9, H10. reflexivity.
          - (* bit = 0: scmul 0 P_i = id *)
            assert (Hx0 : word.unsigned x = 0).
            { pose proof (Z.mod_pos_bound (eval glv_scalar_words k1w_i) 2 ltac:(lia)).
              rewrite H1 in *. apply Z.eqb_neq in Hbit1. lia. }
            replace (Z.b2z _) with 0 by (rewrite <- Hb1; symmetry; exact Hx0).
            simpl. rewrite H7, H9, H10. reflexivity. }
        assert (Hcmov2 : (x6, x7, x8) =
          scmul Fzero Fone curve_add
            (Z.to_nat (Z.b2z (Z.testbit (eval glv_scalar_words k2_words) iter)))
            (Phix_i, Phiy_i, Phiz_i)).
        { destruct (word.unsigned x1 =? 1) eqn:Hbit2.
          - apply Z.eqb_eq in Hbit2.
            replace (Z.b2z _) with 1 by (rewrite <- Hb2; symmetry; exact Hbit2).
            simpl. rewrite curve_add_id_r. rewrite H11, H13, H14. reflexivity.
          - assert (Hx10 : word.unsigned x1 = 0).
            { pose proof (Z.mod_pos_bound (eval glv_scalar_words k2w_i) 2 ltac:(lia)).
              rewrite H5 in *. apply Z.eqb_neq in Hbit2. lia. }
            replace (Z.b2z _) with 0 by (rewrite <- Hb2; symmetry; exact Hx10).
            simpl. rewrite H11, H13, H14. reflexivity. }
        rewrite Hcmov1, Hcmov2, Hp_i, Hphi_i.
        replace (129 - (Z.of_nat vi - 1)) with (iter + 1) by (unfold iter; lia).
        eapply glv_loop_step; unfold iter in *.
        all: try (pose proof (word.unsigned_range iw_i); lia).
        all: try reflexivity.
        all: try assumption.
        all: exact (eval_nonneg_2 _). }

      { (* FALSE branch: iter >= 129, i.e. vi = 0 *)
        intro Hcond.
        (* The while condition is false: NOT (iter < 129), so iter >= 129.
           From Hiter_val: word.unsigned iw_i = 129 - Z.of_nat vi.
           From Hcond: word.unsigned (word.b2w (word.ltu ...)) = 0.
           This means NOT (iw_i < 129), so iw_i >= 129.
           Combined with iter = 129 - Z.of_nat vi, we get vi = 0.

           Post-loop goal: WP for 6 stack deallocations, then postcondition.
           After the while loop, there's no more code in the function body
           (the while is the last statement before the stack deallocs).

           The stack deallocs are automatic from the stackalloc construct:
           they require providing anybytes for each stack buffer.

           We need to convert:
           - FElem None a_auxx/y/z → anybytes (via FElem_to_bytes)
           - scalar a_cond1/2 → anybytes (via scalar_to_anybytes)
           - scalar a_iter → anybytes (via scalar_to_anybytes)

           Then provide the final postcondition existentials. *)

        (* vi = 0 means iter = 129, all bits processed *)

        (* --- Dealloc level 1: iter (word-sized scalar → anybytes) --- *)
        eassert (Hiter_sep : (_ ⋆ scalar a_iter _) mi).
        { pose proof Hsep_i as H'. ecancel_assumption. }
        destruct Hiter_sep as [m_rest_iter [m_stk_iter [[Heq_iter' Hd_iter'] [Hrest_iter Hstk_iter]]]].
        eapply scalar_to_anybytes in Hstk_iter.
        exists m_rest_iter, m_stk_iter.
        split. { exact Hstk_iter. }
        split. { split; [exact Heq_iter' | exact Hd_iter']. }

        (* --- Dealloc level 2: cond2 (word-sized scalar → anybytes) --- *)
        eassert (Hcond2_sep : (_ ⋆ scalar a_cond2 _) m_rest_iter).
        { pose proof Hrest_iter as H'. ecancel_assumption. }
        destruct Hcond2_sep as [m_rest_cond2 [m_stk_cond2 [[Heq_cond2' Hd_cond2'] [Hrest_cond2 Hstk_cond2]]]].
        eapply scalar_to_anybytes in Hstk_cond2.
        exists m_rest_cond2, m_stk_cond2.
        split. { exact Hstk_cond2. }
        split. { split; [exact Heq_cond2' | exact Hd_cond2']. }

        (* --- Dealloc level 3: cond1 (word-sized scalar → anybytes) --- *)
        eassert (Hcond1_sep : (_ ⋆ scalar a_cond1 _) m_rest_cond2).
        { pose proof Hrest_cond2 as H'. ecancel_assumption. }
        destruct Hcond1_sep as [m_rest_cond1 [m_stk_cond1 [[Heq_cond1' Hd_cond1'] [Hrest_cond1 Hstk_cond1]]]].
        eapply scalar_to_anybytes in Hstk_cond1.
        exists m_rest_cond1, m_stk_cond1.
        split. { exact Hstk_cond1. }
        split. { split; [exact Heq_cond1' | exact Hd_cond1']. }

        (* --- Dealloc level 4: auxz (felem-sized FElem None → anybytes) --- *)
        eassert (Hauxz_sep : (_ ⋆ FElem None a_auxz _) m_rest_cond1).
        { change Compilation2.FElem with FElem in Hrest_cond1.
          unfold Point3 in Hrest_cond1.
          pose proof Hrest_cond1 as H'. ecancel_assumption. }
        destruct Hauxz_sep as [m_rest_auxz [m_stk_auxz [[Heq_auxz' Hd_auxz'] [Hrest_auxz Hstk_auxz]]]].
        exists m_rest_auxz, m_stk_auxz.
        split. { exact (P_to_bytes a_auxz _ m_stk_auxz Hstk_auxz). }
        split. { split; [exact Heq_auxz' | exact Hd_auxz']. }

        (* --- Dealloc level 5: auxy (felem-sized FElem None → anybytes) --- *)
        eassert (Hauxy_sep : (_ ⋆ FElem None a_auxy _) m_rest_auxz).
        { change Compilation2.FElem with FElem in Hrest_auxz.
          unfold Point3 in Hrest_auxz.
          pose proof Hrest_auxz as H'. ecancel_assumption. }
        destruct Hauxy_sep as [m_rest_auxy [m_stk_auxy [[Heq_auxy' Hd_auxy'] [Hrest_auxy Hstk_auxy]]]].
        exists m_rest_auxy, m_stk_auxy.
        split. { exact (P_to_bytes a_auxy _ m_stk_auxy Hstk_auxy). }
        split. { split; [exact Heq_auxy' | exact Hd_auxy']. }

        (* --- Dealloc level 6: auxx (felem-sized FElem None → anybytes) --- *)
        eassert (Hauxx_sep : (_ ⋆ FElem None a_auxx _) m_rest_auxy).
        { change Compilation2.FElem with FElem in Hrest_auxy.
          unfold Point3 in Hrest_auxy.
          pose proof Hrest_auxy as H'. ecancel_assumption. }
        destruct Hauxx_sep as [m_rest_auxx [m_stk_auxx' [[Heq_auxx' Hd_auxx'] [Hrest_auxx Hstk_auxx]]]].
        exists m_rest_auxx, m_stk_auxx'.
        split. { exact (P_to_bytes a_auxx _ m_stk_auxx' Hstk_auxx). }
        split. { split; [exact Heq_auxx' | exact Hd_auxx']. }

        (* --- Final postcondition --- *)
        cbv [list_map list_map_body].
        split. { exact eq_refl. }
        split. { exact eq_refl. }
        (* Provide existential witnesses for output values *)
        exists Outx_i, Outy_i, Outz_i,
               Px_i, Py_i, Pz_i,
               Phix_i, Phiy_i, Phiz_i.
        exists k1w_i, k2w_i.
        split.
        { (* Accumulator equation: out = [k1]P + [k2]phi(P) *)
          (* Step 1: derive vi = 0 from the false branch condition *)
          rewrite (@word.unsigned_b2w _ _ word_ok) in Hcond.
          assert (Hltu_false : word.ltu iw_i (word.of_Z glv_iterations) = false).
          { destruct (word.ltu iw_i (word.of_Z glv_iterations));
            [cbn in Hcond; lia | reflexivity]. }
          pose proof (@word.unsigned_ltu _ _ word_ok iw_i (word.of_Z glv_iterations)) as Hltu_eq.
          rewrite Hltu_false in Hltu_eq. symmetry in Hltu_eq.
          apply Z.ltb_ge in Hltu_eq.
          rewrite Hiter_val, word.unsigned_of_Z in Hltu_eq.
          cbv [glv_iterations] in Hltu_eq.
          unfold word.wrap in Hltu_eq.
          destruct (width_cases) as [Hw|Hw]; rewrite Hw in Hltu_eq;
            (change (129 mod 2 ^ 32) with 129 in Hltu_eq
             || change (129 mod 2 ^ 64) with 129 in Hltu_eq);
            assert (Hvi0 : vi = 0%nat) by (pose proof Znat.Nat2Z.is_nonneg vi; lia);
            subst vi;
            change (Z.of_nat 0) with 0 in Hout_i;
            change (129 - 0) with 129 in Hout_i;
            cbv [glv_iterations] in *;
            rewrite !Z.mod_small in Hout_i by lia;
            exact Hout_i. }
        (* Sep: the remaining memory satisfies the postcondition *)
        change Compilation2.FElem with FElem in Hrest_auxx.
        unfold Point3 in Hrest_auxx.
        ecancel_assumption. } }
  Qed.

End GLV_Shamir_Generic.

(* ================================================================== *)
(** * Section 6: BLS12-381 instantiation                               *)
(* ================================================================== *)

(** To instantiate for BLS12-381:

    Require Import Bedrock.Field.Synthesis.Examples.BLS12_G1.
    Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
    Require Import Bedrock.Field.Synthesis.Examples.bls12_three_b.
    Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
    Require Import coqutil.Word.Bitwidth64.
    Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.

    Definition bls12_glv_shamir :=
      @glv_shamir_func _ _ _ _ _ _ _ _ _ _
        bls12_field_parameters bls12_frep
        "group_cmov_alt" "store_zero"
        "curve_add" "bls12_three_b".

    The full program would link:
    - bls12_glv_shamir
    - curve_add (= bls12_G1_add from BLS12_G1.v)
    - store_zero
    - group_cmov_alt (= cmov_alt_func from CondMoveGroup.v)
    - shift_scalar (= shift_scalar from BignumShift.v, scalar_words:=2)
    - All Fp operations (mul, add, sub, opp, square, selectznz, felem_copy, ...)
    - zero, one (field constant loaders)

    The caller is responsible for:
    1. Reducing k mod r (via BLS12_ScalarReduce)
    2. Decomposing k into (k1, k2) via glv_decompose
    3. Computing phi(P) = (omega * P_x, P_y, P_z)
    4. Calling bls12_glv_shamir with the precomputed inputs
*)
