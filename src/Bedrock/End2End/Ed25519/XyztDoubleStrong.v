(** * XyztDoubleStrong — strengthened functional contract for
 *                       [xyzt_double_body_decomposed].
 *
 *  Companion to [XyztAddStrong.v], built by the same method.
 *
 *  ## What was wrong with [XyztDoubleBodyDecomposed.xyzt_double_body_decomposed_correct]
 *
 *  The [rexec_call] constructor of [rust_exec_ed]
 *  ([SafeRustEd25519Sim.v], around line 854) defers the entire state
 *  transition to the oracle predicate [callee_post].  The hypothesis
 *  [fe25519_callees_honoured_dbl] constrains only [loc_type] and two
 *  list lengths, so it admits an oracle that relates [rs1] to an
 *  arbitrary [rs2] — including [rs2 = rs1], which never writes the
 *  destination.  [stale_pair_honours_old_dbl] below exhibits exactly
 *  such a pair, which makes the old statement refutable.
 *
 *  The repair, as in [XyztAddStrong.v], is a per-leaf contract that
 *  pins BOTH the value AND the frame:
 *
 *      exists limbs, length limbs = 5
 *        /\ limbs_eval limbs = f xa xb mod ed25519_p
 *        /\ rs2 = set_fp rs1 dst.(loc_var) limbs
 *
 *  The third conjunct is the ingredient whose absence made the old
 *  statement false.  [limbs_eval], [fp_slot], [set_fp],
 *  [bytes200_slot], [fp_unop_contract], [fp_binop_contract],
 *  [unpack_xyzt5_contract] and [pack_xyzt5_contract] are imported
 *  from [XyztAddStrong.v] unchanged; only the ternary leaf
 *  [fe25519_sqr_sub2] needs a new [fp_ternop_contract].
 *
 *  ## Freshness side conditions
 *
 *  The [REdLetZero] prologue of the double body writes
 *  [rs_set_tower_ed] unconditionally over its thirteen scratch names
 *
 *      X  Y  Z  Ta  Tb  A  B  C  E  F  G  H  XpY
 *
 *  (read off the prologue at [XyztDoubleBodyDecomposed.v:97-110]).
 *  If the input point's [loc_var] aliased one of these, the prologue
 *  would clobber it before the unpack reads it, so the theorem
 *  additionally requires [P.(loc_type) = TBytes 200] and
 *  [~ In P.(loc_var) xyzt_double_scratch_vars].
 *
 *  ## Reference used
 *
 *  The theorem is stated against [ed25519_xyzt_double_gallina_fixed],
 *  which is the Hisil-Wong-Carter-Dawson DEDICATED doubling the body
 *  actually computes.  It is NOT
 *  [XyztDoubleVerified.ed25519_xyzt_double_gallina]; see §G for the
 *  two reasons why that spec cannot be met byte-for-byte.
 *
 *  ## Status
 *
 *  0 Admitted, 0 admit, 0 Axiom, 0 Parameter.  Every headline result
 *  carries a [Print Assumptions] line.
 *
 *  NB: this file Requires [XyztDoubleBodyDecomposed.v], which still
 *  contains the old, refuted [xyzt_double_body_decomposed_correct] as
 *  an [Admitted].  That admitted statement is therefore an axiom in
 *  the ambient environment, but no proof here depends on it, so it
 *  does not appear in any [Print Assumptions] below.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Ed25519.XyztDoubleVerified.
Require Import Bedrock.End2End.Ed25519.XyztDoubleBodyDecomposed.
Require Import Bedrock.End2End.Ed25519.XyztAddStrong.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §A.  The one new per-leaf contract shape                          *)
(* ================================================================ *)

(** [fe25519_sqr_sub2 E [XpY; A; B]] is the only ternary leaf in the
    double body; [XyztAddStrong.v] has no analogue.  Value + frame,
    exactly as in [fp_binop_contract]. *)
Definition fp_ternop_contract
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop)
    (fname : String.string) (f : Z -> Z -> Z -> Z) : Prop :=
  forall dst a b c rs1 rs2 xa xb xc,
    callee_post fname [a; b; c] dst rs1 rs2 ->
    a.(loc_type)   = TFp25519 ->
    b.(loc_type)   = TFp25519 ->
    c.(loc_type)   = TFp25519 ->
    dst.(loc_type) = TFp25519 ->
    fp_slot rs1 a.(loc_var) xa ->
    fp_slot rs1 b.(loc_var) xb ->
    fp_slot rs1 c.(loc_var) xc ->
    exists limbs,
      length limbs = 5%nat
      /\ limbs_eval limbs = (f xa xb xc) mod ed25519_p
      /\ rs2 = set_fp rs1 dst.(loc_var) limbs.

(* ================================================================ *)
(* §B.  Strengthened callees-honoured predicate                      *)
(* ================================================================ *)

(** One clause per leaf the body invokes, in body order:
      unpack, sqr, sqr, sqr_scale2, add, sqr_sub2, sub, neg_add,
      sub, mul, mul, mul, pack. *)
Definition fe25519_callees_honoured_dbl_strong
    (callee_post   : String.string -> list located_ed -> located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop)
    (callee_post_n : String.string -> list located_ed ->
                     list located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop) : Prop :=
     unpack_xyzt5_contract callee_post_n
  /\ pack_xyzt5_contract   callee_post_n
  /\ fp_unop_contract   callee_post "fe25519_sqr"        (fun a => a * a)
  /\ fp_unop_contract   callee_post "fe25519_sqr_scale2" (fun a => 2 * (a * a))
  /\ fp_binop_contract  callee_post "fe25519_add"        (fun a b => a + b)
  /\ fp_ternop_contract callee_post "fe25519_sqr_sub2"
                          (fun a b c => a * a - b - c)
  /\ fp_binop_contract  callee_post "fe25519_sub"        (fun a b => a - b)
  /\ fp_binop_contract  callee_post "fe25519_neg_add"    (fun a b => - (a + b))
  /\ fp_binop_contract  callee_post "fe25519_mul"        (fun a b => a * b).

(** The thirteen names the [REdLetZero] prologue of
    [xyzt_double_body_decomposed] allocates, in prologue order. *)
Definition xyzt_double_scratch_vars : list String.string :=
  ["X"; "Y"; "Z"; "Ta"; "Tb";
   "A"; "B"; "C"; "E"; "F"; "G"; "H"; "XpY"].

(** The reference the body actually computes: Hisil et al. §3.3
    dedicated doubling for a = -1, with the cached T stored as
    (Ta3, Tb3) = (E, H). *)
Definition ed25519_xyzt_double_gallina_fixed
    (p : list Byte.byte) : list Byte.byte :=
  if Nat.eqb (length p) 200 then
    let '(x, y, z, _, _) := parse_xyzt5 p in
    let a   := (x * x) mod ed25519_p in
    let b   := (y * y) mod ed25519_p in
    let c   := (2 * (z * z)) mod ed25519_p in
    let xpy := (x + y) mod ed25519_p in
    let e   := (xpy * xpy - a - b) mod ed25519_p in
    let g   := (b - a) mod ed25519_p in
    let h   := (- (a + b)) mod ed25519_p in
    let f   := (g - c) mod ed25519_p in
    let x3  := (e * f) mod ed25519_p in
    let y3  := (g * h) mod ed25519_p in
    let z3  := (f * g) mod ed25519_p in
    pack_xyzt5 x3 y3 z3 e h
  else
    List.repeat Byte.x00 200.

(* ================================================================ *)
(* §C.  Prologue framing                                             *)
(* ================================================================ *)

Lemma notin_dbl_scratch_neq : forall v w,
  ~ In v xyzt_double_scratch_vars -> In w xyzt_double_scratch_vars -> v <> w.
Proof. intros v w Hn Hi Heq. subst. contradiction. Qed.

Ltac solve_neq_scratch_dbl :=
  match goal with
  | [ H : ~ In ?v xyzt_double_scratch_vars |- ?v <> _ ] =>
      apply (notin_dbl_scratch_neq _ _ H);
      cbv [xyzt_double_scratch_vars]; cbn; tauto
  end.

Lemma dbl_strip_lets :
  forall callee_post callee_post_n function_table (c : rust_cmd_ed) rs1 rs2,
  rust_exec_ed callee_post callee_post_n function_table
    (REdLetZero "X"  TFp25519 (REdLetZero "Y"  TFp25519 (
     REdLetZero "Z"  TFp25519 (REdLetZero "Ta" TFp25519 (
     REdLetZero "Tb" TFp25519 (REdLetZero "A"  TFp25519 (
     REdLetZero "B"  TFp25519 (REdLetZero "C"  TFp25519 (
     REdLetZero "E"  TFp25519 (REdLetZero "F"  TFp25519 (
     REdLetZero "G"  TFp25519 (REdLetZero "H"  TFp25519 (
     REdLetZero "XpY" TFp25519 c
     )))))))))))))
    rs1 rs2 ->
  exists rsL,
    rust_exec_ed callee_post callee_post_n function_table c rsL rs2
    /\ (forall v, ~ In v xyzt_double_scratch_vars ->
          rs_get_tower_ed rsL v = rs_get_tower_ed rs1 v).
Proof.
  intros cp cpn ft c rs1 rs2 H.
  repeat (apply (add_letzero_inv cp cpn ft) in H; destruct H as [? [? H]]).
  eexists. split; [ exact H | ].
  intros v Hv.
  repeat (rewrite rs_get_set_neq by solve_neq_scratch_dbl).
  reflexivity.
Qed.

(* ================================================================ *)
(* §D.  Correctness theorem                                          *)
(* ================================================================ *)

Theorem xyzt_double_body_decomposed_correct_strong :
  forall callee_post callee_post_n function_table
         (P dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (p_bs : list Byte.byte),
    fe25519_callees_honoured_dbl_strong callee_post callee_post_n ->
    length p_bs = 200%nat ->
    P.(loc_type)    = TBytes 200 ->
    dest.(loc_type) = TBytes 200 ->
    ~ In P.(loc_var) xyzt_double_scratch_vars ->
    bytes200_slot rs1 P.(loc_var) p_bs ->
    rust_exec_ed callee_post callee_post_n function_table
                 (xyzt_double_body_decomposed dest [P]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_xyzt_double_gallina_fixed p_bs))).
Proof.
  intros cp cpn ft P dest rs1 rs2 p_bs
         Hhon Hl Htp Htd Hni Hb Hexec.
  cbv [xyzt_double_body_decomposed] in Hexec.
  apply dbl_strip_lets in Hexec.
  destruct Hexec as [rsL [Hexec Hframe]].
  cbv [XyztDoubleBodyDecomposed.LE_TFp25519] in Hexec.
  destruct Hhon as [Hunp [Hpk [Hsqr [Hsqr2 [Hadd [Hss2 [Hsub [Hneg Hmul]]]]]]]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r1  [C1  Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r2  [C2  Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r3  [C3  Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r4  [C4  Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r5  [C5  Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r6  [C6  Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r7  [C7  Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r8  [C8  Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r9  [C9  Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r10 [C10 Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r11 [C11 Hexec]].
  apply (add_seq_inv cp cpn ft) in Hexec; destruct Hexec as [r12 [C12 Hexec]].
  rename Hexec into C13.
  apply (add_calln_inv cp cpn ft) in C1.
  apply (add_calln_inv cp cpn ft) in C13.
  apply (add_call_inv cp cpn ft) in C2.
  apply (add_call_inv cp cpn ft) in C3.
  apply (add_call_inv cp cpn ft) in C4.
  apply (add_call_inv cp cpn ft) in C5.
  apply (add_call_inv cp cpn ft) in C6.
  apply (add_call_inv cp cpn ft) in C7.
  apply (add_call_inv cp cpn ft) in C8.
  apply (add_call_inv cp cpn ft) in C9.
  apply (add_call_inv cp cpn ft) in C10.
  apply (add_call_inv cp cpn ft) in C11.
  apply (add_call_inv cp cpn ft) in C12.
  assert (HbL : bytes200_slot rsL (loc_var P) p_bs)
    by (unfold bytes200_slot in *; rewrite Hframe by assumption; exact Hb).
  clear Hframe Hb.
  edestruct (Hunp _ _ _ _ _ _ _ _ _ C1 Htp HbL Hl
               eq_refl eq_refl eq_refl eq_refl eq_refl)
    as [lx [ly [lz [lta [ltb [Lx [Ly [Lz [Lta [Ltb [Hev Hr1]]]]]]]]]]].
  cbn in Hr1.
  clear C1 HbL Htp Hni.
  destruct (parse_xyzt5 p_bs) as [[[[x y] z] ta] tb] eqn:Hp.
  destruct Hev as [Ex [Ey [Ez [Eta Etb]]]].
  (* A = X^2 *)
  eassert (Sa : fp_slot r1 "X" _)
    by (apply (fp_slot_intro _ _ lx); [ fp_lookup | exact Lx | exact Ex ]).
  edestruct (Hsqr _ _ _ _ _ C2 eq_refl eq_refl Sa) as [l2 [L2 [E2 Hr2]]].
  cbn in Hr2. cbv beta in E2. clear Sa C2.
  (* B = Y^2 *)
  eassert (Sa : fp_slot r2 "Y" _)
    by (apply (fp_slot_intro _ _ ly); [ fp_lookup | exact Ly | exact Ey ]).
  edestruct (Hsqr _ _ _ _ _ C3 eq_refl eq_refl Sa) as [l3 [L3 [E3 Hr3]]].
  cbn in Hr3. cbv beta in E3. clear Sa C3.
  (* C = 2 Z^2 *)
  eassert (Sa : fp_slot r3 "Z" _)
    by (apply (fp_slot_intro _ _ lz); [ fp_lookup | exact Lz | exact Ez ]).
  edestruct (Hsqr2 _ _ _ _ _ C4 eq_refl eq_refl Sa) as [l4 [L4 [E4 Hr4]]].
  cbn in Hr4. cbv beta in E4. clear Sa C4.
  (* XpY = X + Y *)
  eassert (Sa : fp_slot r4 "X" _)
    by (apply (fp_slot_intro _ _ lx); [ fp_lookup | exact Lx | exact Ex ]).
  eassert (Sb : fp_slot r4 "Y" _)
    by (apply (fp_slot_intro _ _ ly); [ fp_lookup | exact Ly | exact Ey ]).
  edestruct (Hadd _ _ _ _ _ _ _ C5 eq_refl eq_refl eq_refl Sa Sb)
    as [l5 [L5 [E5 Hr5]]].
  cbn in Hr5. cbv beta in E5. clear Sa Sb C5.
  (* E = XpY^2 - A - B *)
  eassert (Sa : fp_slot r5 "XpY" _)
    by (apply (fp_slot_intro _ _ l5); [ fp_lookup | exact L5 | exact E5 ]).
  eassert (Sb : fp_slot r5 "A" _)
    by (apply (fp_slot_intro _ _ l2); [ fp_lookup | exact L2 | exact E2 ]).
  eassert (Sc : fp_slot r5 "B" _)
    by (apply (fp_slot_intro _ _ l3); [ fp_lookup | exact L3 | exact E3 ]).
  edestruct (Hss2 _ _ _ _ _ _ _ _ _ C6 eq_refl eq_refl eq_refl eq_refl Sa Sb Sc)
    as [l6 [L6 [E6 Hr6]]].
  cbn in Hr6. cbv beta in E6. clear Sa Sb Sc C6.
  (* G = B - A *)
  eassert (Sa : fp_slot r6 "B" _)
    by (apply (fp_slot_intro _ _ l3); [ fp_lookup | exact L3 | exact E3 ]).
  eassert (Sb : fp_slot r6 "A" _)
    by (apply (fp_slot_intro _ _ l2); [ fp_lookup | exact L2 | exact E2 ]).
  edestruct (Hsub _ _ _ _ _ _ _ C7 eq_refl eq_refl eq_refl Sa Sb)
    as [l7 [L7 [E7 Hr7]]].
  cbn in Hr7. cbv beta in E7. clear Sa Sb C7.
  (* H = -(A + B) *)
  eassert (Sa : fp_slot r7 "A" _)
    by (apply (fp_slot_intro _ _ l2); [ fp_lookup | exact L2 | exact E2 ]).
  eassert (Sb : fp_slot r7 "B" _)
    by (apply (fp_slot_intro _ _ l3); [ fp_lookup | exact L3 | exact E3 ]).
  edestruct (Hneg _ _ _ _ _ _ _ C8 eq_refl eq_refl eq_refl Sa Sb)
    as [l8 [L8 [E8 Hr8]]].
  cbn in Hr8. cbv beta in E8. clear Sa Sb C8.
  (* F = G - C *)
  eassert (Sa : fp_slot r8 "G" _)
    by (apply (fp_slot_intro _ _ l7); [ fp_lookup | exact L7 | exact E7 ]).
  eassert (Sb : fp_slot r8 "C" _)
    by (apply (fp_slot_intro _ _ l4); [ fp_lookup | exact L4 | exact E4 ]).
  edestruct (Hsub _ _ _ _ _ _ _ C9 eq_refl eq_refl eq_refl Sa Sb)
    as [l9 [L9 [E9 Hr9]]].
  cbn in Hr9. cbv beta in E9. clear Sa Sb C9.
  (* X3 = E * F *)
  eassert (Sa : fp_slot r9 "E" _)
    by (apply (fp_slot_intro _ _ l6); [ fp_lookup | exact L6 | exact E6 ]).
  eassert (Sb : fp_slot r9 "F" _)
    by (apply (fp_slot_intro _ _ l9); [ fp_lookup | exact L9 | exact E9 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C10 eq_refl eq_refl eq_refl Sa Sb)
    as [l10 [L10 [E10 Hr10]]].
  cbn in Hr10. cbv beta in E10. clear Sa Sb C10.
  (* Y3 = G * H *)
  eassert (Sa : fp_slot r10 "G" _)
    by (apply (fp_slot_intro _ _ l7); [ fp_lookup | exact L7 | exact E7 ]).
  eassert (Sb : fp_slot r10 "H" _)
    by (apply (fp_slot_intro _ _ l8); [ fp_lookup | exact L8 | exact E8 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C11 eq_refl eq_refl eq_refl Sa Sb)
    as [l11 [L11 [E11 Hr11]]].
  cbn in Hr11. cbv beta in E11. clear Sa Sb C11.
  (* Z3 = F * G *)
  eassert (Sa : fp_slot r11 "F" _)
    by (apply (fp_slot_intro _ _ l9); [ fp_lookup | exact L9 | exact E9 ]).
  eassert (Sb : fp_slot r11 "G" _)
    by (apply (fp_slot_intro _ _ l7); [ fp_lookup | exact L7 | exact E7 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C12 eq_refl eq_refl eq_refl Sa Sb)
    as [l12 [L12 [E12 Hr12]]].
  cbn in Hr12. cbv beta in E12. clear Sa Sb C12.
  (* pack [X3; Y3; Z3; E; H] *)
  eassert (SX : fp_slot r12 "X" _)
    by (apply (fp_slot_intro _ _ l10); [ fp_lookup | exact L10 | exact E10 ]).
  eassert (SY : fp_slot r12 "Y" _)
    by (apply (fp_slot_intro _ _ l11); [ fp_lookup | exact L11 | exact E11 ]).
  eassert (SZ : fp_slot r12 "Z" _)
    by (apply (fp_slot_intro _ _ l12); [ fp_lookup | exact L12 | exact E12 ]).
  eassert (SE : fp_slot r12 "E" _)
    by (apply (fp_slot_intro _ _ l6); [ fp_lookup | exact L6 | exact E6 ]).
  eassert (SH : fp_slot r12 "H" _)
    by (apply (fp_slot_intro _ _ l8); [ fp_lookup | exact L8 | exact E8 ]).
  pose proof (Hpk _ _ _ _ _ _ _ _ _ _ _ _ _ C13 Htd
                 eq_refl eq_refl eq_refl eq_refl eq_refl
                 SX SY SZ SE SH) as Hrs2.
  rewrite Hrs2, rs_get_set_eq.
  match goal with
  | [ |- Some (exist_tval_ed (TBytes 200) (VBytes 200 ?A))
       = Some (exist_tval_ed (TBytes 200) (VBytes 200 ?B)) ] =>
      assert (Hbe : A = B)
  end.
  { cbv [ed25519_xyzt_double_gallina_fixed].
    rewrite Hl, Nat.eqb_refl.
    rewrite Hp. cbv beta iota zeta.
    f_equal; push_Zmod; pull_Zmod; try reflexivity; f_equal; ring. }
  rewrite Hbe. reflexivity.
Qed.

Print Assumptions xyzt_double_body_decomposed_correct_strong.

(* ================================================================ *)
(* §E.  Anti-vacuity: a concrete state-transforming oracle pair      *)
(*      that honours the strengthened predicate.                     *)
(* ================================================================ *)

(** [fp_enc], [dec_fp], [dec_bytes200], [ed_unop_post],
    [ed_binop_post], [ed_unpack_post], [ed_pack_post] and
    [witness_cpn] are reused verbatim from [XyztAddStrong.v]; the
    ternary leaf needs one more. *)
Definition ed_ternop_post (f : Z -> Z -> Z -> Z)
    (args : list located_ed) (dst : located_ed)
    (rs1 rs2 : rust_state_ed) : Prop :=
  match args with
  | [a; b; c] =>
      rs2 = set_fp rs1 dst.(loc_var)
              (fp_enc (f (dec_fp rs1 a.(loc_var))
                         (dec_fp rs1 b.(loc_var))
                         (dec_fp rs1 c.(loc_var))))
  | _ => False
  end.

(** Each disjunct reads its argument slots through [dec_fp], computes,
    and writes the destination through [set_fp]: a genuine state
    transformer, not a type assertion. *)
Definition witness_cp_dbl (fname : String.string) (args : list located_ed)
    (dst : located_ed) (rs1 rs2 : rust_state_ed) : Prop :=
     (fname = "fe25519_sqr"
        /\ ed_unop_post (fun a => a * a) args dst rs1 rs2)
  \/ (fname = "fe25519_sqr_scale2"
        /\ ed_unop_post (fun a => 2 * (a * a)) args dst rs1 rs2)
  \/ (fname = "fe25519_add"
        /\ ed_binop_post (fun a b => a + b) args dst rs1 rs2)
  \/ (fname = "fe25519_sqr_sub2"
        /\ ed_ternop_post (fun a b c => a * a - b - c) args dst rs1 rs2)
  \/ (fname = "fe25519_sub"
        /\ ed_binop_post (fun a b => a - b) args dst rs1 rs2)
  \/ (fname = "fe25519_neg_add"
        /\ ed_binop_post (fun a b => - (a + b)) args dst rs1 rs2)
  \/ (fname = "fe25519_mul"
        /\ ed_binop_post (fun a b => a * b) args dst rs1 rs2).

Theorem witness_honours_dbl :
  fe25519_callees_honoured_dbl_strong witness_cp_dbl witness_cpn.
Proof.
  pose proof witness_honours_add as Hadd.
  destruct Hadd as [Hunp [Hpk _]].
  unfold fe25519_callees_honoured_dbl_strong. repeat apply conj.
  - exact Hunp.
  - exact Hpk.
  - (* fe25519_sqr *)
    intros dst a rs1 rs2 xa Hc _ _ Sa.
    destruct Hc as [[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[He Hc]]]]]]];
      try discriminate.
    cbv [ed_unop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* fe25519_sqr_scale2 *)
    intros dst a rs1 rs2 xa Hc _ _ Sa.
    destruct Hc as [[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[He Hc]]]]]]];
      try discriminate.
    cbv [ed_unop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* fe25519_add *)
    intros dst a b rs1 rs2 xa xb Hc _ _ _ Sa Sb.
    destruct Hc as [[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[He Hc]]]]]]];
      try discriminate.
    cbv [ed_binop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa), (dec_fp_correct _ _ _ Sb) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* fe25519_sqr_sub2 *)
    intros dst a b c rs1 rs2 xa xb xc Hc _ _ _ _ Sa Sb Sc.
    destruct Hc as [[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[He Hc]]]]]]];
      try discriminate.
    cbv [ed_ternop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa), (dec_fp_correct _ _ _ Sb),
            (dec_fp_correct _ _ _ Sc) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* fe25519_sub *)
    intros dst a b rs1 rs2 xa xb Hc _ _ _ Sa Sb.
    destruct Hc as [[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[He Hc]]]]]]];
      try discriminate.
    cbv [ed_binop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa), (dec_fp_correct _ _ _ Sb) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* fe25519_neg_add *)
    intros dst a b rs1 rs2 xa xb Hc _ _ _ Sa Sb.
    destruct Hc as [[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[He Hc]]]]]]];
      try discriminate.
    cbv [ed_binop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa), (dec_fp_correct _ _ _ Sb) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* fe25519_mul *)
    intros dst a b rs1 rs2 xa xb Hc _ _ _ Sa Sb.
    destruct Hc as [[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[[He Hc]|[He Hc]]]]]]];
      try discriminate.
    cbv [ed_binop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa), (dec_fp_correct _ _ _ Sb) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
Qed.

Print Assumptions witness_honours_dbl.

(* ================================================================ *)
(* §F.  The strengthened predicate excludes the stale oracles        *)
(* ================================================================ *)

(** [stale_cp] (from [XyztAddStrong.v]) asserts only the destination's
    type and leaves the state alone.  Its N-ary companion does the
    same for unpack / pack. *)
Definition stale_cpn (fname : String.string) (dests args : list located_ed)
    (rs1 rs2 : rust_state_ed) : Prop :=
     (fname = "fe25519_unpack_xyzt5"
        /\ length dests = 5%nat
        /\ (forall d, In d dests -> d.(loc_type) = TFp25519)
        /\ rs2 = rs1)
  \/ (fname = "fe25519_pack_xyzt5"
        /\ length dests = 1%nat
        /\ rs2 = rs1).

(** (a) The OLD obligation is satisfied by a pair that never writes
    anything.  This is the refutation of the old keystone: nothing in
    [fe25519_callees_honoured_dbl] forces the destination to change. *)
Lemma stale_pair_honours_old_dbl :
  fe25519_callees_honoured_dbl stale_cp stale_cpn.
Proof.
  unfold fe25519_callees_honoured_dbl. repeat apply conj.
  - intros dests args rs1 rs2 Hc.
    destruct Hc as [[_ [Hlen [Ht _]]] | [Hbad _]]; [ split; assumption | discriminate ].
  - intros dests args rs1 rs2 Hc.
    destruct Hc as [[Hbad _] | [_ [Hlen _]]]; [ discriminate | exact Hlen ].
  - intros fname dst args rs1 rs2 _ [Ht _]. exact Ht.
Qed.

Lemma stale_pair_never_writes :
  (forall fname args dst rs1 rs2, stale_cp fname args dst rs1 rs2 -> rs2 = rs1)
  /\ (forall fname dests args rs1 rs2, stale_cpn fname dests args rs1 rs2 -> rs2 = rs1).
Proof.
  split.
  - intros fname args dst rs1 rs2 [_ H]. exact H.
  - intros fname dests args rs1 rs2 [[_ [_ [_ H]]] | [_ [_ H]]]; exact H.
Qed.

(** (b) ... but the strengthened per-leaf contract excludes it. *)
Lemma stale_cp_violates_new_dbl_contract :
  ~ fp_unop_contract stale_cp "fe25519_sqr" (fun a => a * a).
Proof.
  intro H.
  pose (LA := {| loc_var := "a"; loc_type := TFp25519 |}).
  pose (LD := {| loc_var := "d"; loc_type := TFp25519 |}).
  pose (rs := set_fp (set_fp rs_empty_ed "a" [2;0;0;0;0]) "d" [0;0;0;0;0]).
  assert (Sa : fp_slot rs "a" 2).
  { apply (fp_slot_intro _ _ [2;0;0;0;0]).
    - subst rs. unfold set_fp.
      rewrite rs_get_set_neq by discriminate.
      apply rs_get_set_eq.
    - reflexivity.
    - cbv [limbs_eval]; cbn [List.nth]; f_equal; ring. }
  destruct (H LD LA rs rs 2 (conj eq_refl eq_refl) eq_refl eq_refl Sa)
    as [l [Hl [He Hr]]].
  assert (Hd : dec_fp rs LD.(loc_var) = limbs_eval l)
    by (rewrite Hr at 1; apply dec_fp_set_eq).
  rewrite He in Hd.
  subst rs. cbv [dec_fp set_fp] in Hd. rewrite rs_get_set_eq in Hd.
  cbv [limbs_eval] in Hd. cbn [List.nth] in Hd.
  vm_compute in Hd. discriminate.
Qed.

(** The same for the pack leaf, which is the one that writes the
    200-byte output the theorem is about. *)
Lemma stale_cpn_violates_pack_contract :
  ~ pack_xyzt5_contract stale_cpn.
Proof.
  intro H.
  pose (LS := {| loc_var := "s";   loc_type := TFp25519 |}).
  pose (LO := {| loc_var := "out"; loc_type := TBytes 200 |}).
  pose (rs := set_fp rs_empty_ed "s" [1;0;0;0;0]).
  assert (Ss : fp_slot rs "s" 1).
  { apply (fp_slot_intro _ _ [1;0;0;0;0]).
    - subst rs. apply rs_get_set_eq.
    - reflexivity.
    - cbv [limbs_eval]; cbn [List.nth]; f_equal; ring. }
  pose proof (H LO LS LS LS LS LS rs rs 1 1 1 1 1
                (or_intror (conj eq_refl (conj eq_refl eq_refl)))
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                Ss Ss Ss Ss Ss) as Hr.
  assert (Hout : rs_get_tower_ed rs "out" = None)
    by (subst rs; reflexivity).
  rewrite Hr in Hout at 1.
  rewrite rs_get_set_eq in Hout.
  discriminate.
Qed.

Print Assumptions stale_pair_honours_old_dbl.
Print Assumptions stale_cp_violates_new_dbl_contract.
Print Assumptions stale_cpn_violates_pack_contract.

(* ================================================================ *)
(* §G.  Verdict on [XyztDoubleVerified.ed25519_xyzt_double_gallina]  *)
(* ================================================================ *)

(** [ed25519_xyzt_double_gallina] is defined as
    [ed25519_xyzt_add_spec p p], i.e. the unified addition applied
    twice to the same point. *)
Lemma double_spec_is_add_spec_at_pp :
  forall p, ed25519_xyzt_double_gallina p = ed25519_xyzt_add_spec p p.
Proof. reflexivity. Qed.

(** Consequently it carries TWO defects with respect to what the
    decomposed double body computes.

    (1) INHERITED [extended_T] DEFECT.  [ed25519_xyzt_add_gallina]
        computes its cached T as [extended_T ta tb z
        = ta * tb * z^(p-2) mod p], but writes its OUTPUT cached T as
        the plain pair (E, H), i.e. with no z-inverse.  The convention
        does not round-trip; the same observation motivated
        [XyztAddStrong.ed25519_xyzt_add_gallina_fixed].  The double
        spec inherits it verbatim through the definition above.

    (2) WRONG FORMULA FAMILY, independent of (1).  The body computes
        the DEDICATED Hisil et al. §3.3 doubling
          A=X^2, B=Y^2, C=2Z^2, E=(X+Y)^2-A-B, G=B-A, H=-(A+B), F=G-C,
          X3=E*F, Y3=G*H, Z3=F*G, (Ta3,Tb3)=(E,H),
        whereas the spec computes the UNIFIED addition at (P, P).
        For a point on the curve those two agree only PROJECTIVELY.
        Writing (ua, ub, uc, ud, ...) for the unified branch's
        intermediates and (bE, bG, bH, bC, bF) for the dedicated one,
        the lemma below shows

          e_unified = 2 * E_dedicated       g_unified = 2 * G_dedicated
          h_unified = -2 * H_dedicated      f_unified = -2 * F_dedicated

        hence X3, Y3, Z3 differ by a factor of -4 and (Ta3, Tb3) by
        (2, -2).  Byte-for-byte equality is therefore impossible in
        general, whatever is done about (1).

    VERDICT: yes, [XyztDoubleVerified.v] shares the [extended_T]
    defect, and it additionally cannot serve as a byte-level reference
    for this body.  Both are the user's call; nothing here modifies
    [XyztAddVerified.v] or [XyztDoubleVerified.v]. *)
Lemma dbl_dedicated_vs_unified_scaling :
  forall x y z t dd,
    y * y - x * x = z * z + dd * (t * t) ->
    let bE := (x + y) * (x + y) - x * x - y * y in
    let bG := y * y - x * x in
    let bH := - (x * x + y * y) in
    let bC := 2 * (z * z) in
    let bF := bG - bC in
    let ua := (y - x) * (y - x) in
    let ub := (y + x) * (y + x) in
    let uc := t * (2 * dd) * t in
    let ud := 2 * z * z in
       ub - ua = 2 * bE
    /\ ud + uc = 2 * bG
    /\ ub + ua = -2 * bH
    /\ ud - uc = -2 * bF.
Proof.
  intros x y z t dd Hcurve. cbv zeta.
  repeat apply conj; try ring; rewrite Hcurve; ring.
Qed.

Print Assumptions dbl_dedicated_vs_unified_scaling.
