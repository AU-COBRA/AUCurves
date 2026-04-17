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
(** * Part 2: bedrock2 ExprImp program (scaffold)                       *)
(*                                                                      *)
(*    The bedrock2 program mirrors the Gallina spec above.              *)
(*    It uses:                                                          *)
(*      - stackalloc for the bucket array (num_buckets × g1_bytes)      *)
(*      - while loops for the outer window and inner point loops        *)
(*      - calls to g1_add, g1_double, g1_set_identity, g1_copy          *)
(*                                                                      *)
(*    Signature: msm_bls12(out, scalars, points, n)                     *)
(*      out     : pointer to G1 result (144 bytes)                      *)
(*      scalars : pointer to n × 32 bytes (256-bit scalars)             *)
(*      points  : pointer to n × 144 bytes (Jacobian G1)                *)
(*      n       : number of scalar/point pairs                          *)
(*                                                                      *)
(*    The window size c is a compile-time constant (9 for n ≈ 4096).    *)
(*                                                                      *)
(*    SCAFFOLD: body and WP proof are TODO.                             *)
(* =================================================================== *)

(* Bedrock2 imports deferred until the program body is written,
   to avoid heavy imports on an empty scaffold:

From coqutil Require Import Word.Interface Map.Interface.
From bedrock2 Require Import Syntax Semantics ProgramLogic.
Require Import Crypto.Bedrock.Field.Common.Types.

Section PippengerBedrock2.
  Context {width : Z} {BW : Bitwidth width}
          {word : word.word width} {mem : map.map word Byte.byte}.
  ...
End PippengerBedrock2.
*)
