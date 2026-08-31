(** Strengthened functional contract for xyzt_add_body_decomposed. *)

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
Require Import Bedrock.End2End.Ed25519.XyztAddBodyDecomposed.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §A.  Slot-level decoder and predicates                            *)
(* ================================================================ *)

Definition limbs_eval (l : list Z) : Z :=
  (List.nth 0 l 0
   + 2^51  * List.nth 1 l 0
   + 2^102 * List.nth 2 l 0
   + 2^153 * List.nth 3 l 0
   + 2^204 * List.nth 4 l 0) mod ed25519_p.

Definition fp_slot (rs : rust_state_ed) (v : String.string) (x : Z) : Prop :=
  exists limbs,
    rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
    /\ length limbs = 5%nat
    /\ limbs_eval limbs = x mod ed25519_p.

Definition set_fp (rs : rust_state_ed) (v : String.string) (limbs : list Z)
  : rust_state_ed :=
  rs_set_tower_ed rs v (exist_tval_ed TFp25519 (VFp25519 limbs)).

Definition bytes200_slot (rs : rust_state_ed) (v : String.string)
                         (bs : list Byte.byte) : Prop :=
  rs_get_tower_ed rs v = Some (exist_tval_ed (TBytes 200) (VBytes 200 bs)).

(* ================================================================ *)
(* §B.  Per-leaf functional contracts (value + frame)                *)
(* ================================================================ *)

Definition fp_binop_contract
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop)
    (fname : String.string) (f : Z -> Z -> Z) : Prop :=
  forall dst a b rs1 rs2 xa xb,
    callee_post fname [a; b] dst rs1 rs2 ->
    a.(loc_type)   = TFp25519 ->
    b.(loc_type)   = TFp25519 ->
    dst.(loc_type) = TFp25519 ->
    fp_slot rs1 a.(loc_var) xa ->
    fp_slot rs1 b.(loc_var) xb ->
    exists limbs,
      length limbs = 5%nat
      /\ limbs_eval limbs = (f xa xb) mod ed25519_p
      /\ rs2 = set_fp rs1 dst.(loc_var) limbs.

Definition fp_unop_contract
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop)
    (fname : String.string) (f : Z -> Z) : Prop :=
  forall dst a rs1 rs2 xa,
    callee_post fname [a] dst rs1 rs2 ->
    a.(loc_type)   = TFp25519 ->
    dst.(loc_type) = TFp25519 ->
    fp_slot rs1 a.(loc_var) xa ->
    exists limbs,
      length limbs = 5%nat
      /\ limbs_eval limbs = (f xa) mod ed25519_p
      /\ rs2 = set_fp rs1 dst.(loc_var) limbs.

Definition unpack_xyzt5_contract
    (callee_post_n : String.string -> list located_ed -> list located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall dx dy dz dta dtb src rs1 rs2 bs,
    callee_post_n "fe25519_unpack_xyzt5" [dx; dy; dz; dta; dtb] [src] rs1 rs2 ->
    src.(loc_type) = TBytes 200 ->
    bytes200_slot rs1 src.(loc_var) bs ->
    length bs = 200%nat ->
    dx.(loc_type)  = TFp25519 -> dy.(loc_type)  = TFp25519 ->
    dz.(loc_type)  = TFp25519 -> dta.(loc_type) = TFp25519 ->
    dtb.(loc_type) = TFp25519 ->
    exists lx ly lz lta ltb,
      length lx = 5%nat /\ length ly = 5%nat /\ length lz = 5%nat
      /\ length lta = 5%nat /\ length ltb = 5%nat
      /\ (let '(x, y, z, ta, tb) := parse_xyzt5 bs in
            limbs_eval lx  = x  mod ed25519_p
         /\ limbs_eval ly  = y  mod ed25519_p
         /\ limbs_eval lz  = z  mod ed25519_p
         /\ limbs_eval lta = ta mod ed25519_p
         /\ limbs_eval ltb = tb mod ed25519_p)
      /\ rs2 = set_fp (set_fp (set_fp (set_fp (set_fp rs1
                   dx.(loc_var)  lx)
                   dy.(loc_var)  ly)
                   dz.(loc_var)  lz)
                   dta.(loc_var) lta)
                   dtb.(loc_var) ltb.

Definition pack_xyzt5_contract
    (callee_post_n : String.string -> list located_ed -> list located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall d sx sy sz sta stb rs1 rs2 x y z ta tb,
    callee_post_n "fe25519_pack_xyzt5" [d] [sx; sy; sz; sta; stb] rs1 rs2 ->
    d.(loc_type)   = TBytes 200 ->
    sx.(loc_type)  = TFp25519 -> sy.(loc_type)  = TFp25519 ->
    sz.(loc_type)  = TFp25519 -> sta.(loc_type) = TFp25519 ->
    stb.(loc_type) = TFp25519 ->
    fp_slot rs1 sx.(loc_var)  x  ->
    fp_slot rs1 sy.(loc_var)  y  ->
    fp_slot rs1 sz.(loc_var)  z  ->
    fp_slot rs1 sta.(loc_var) ta ->
    fp_slot rs1 stb.(loc_var) tb ->
    rs2 = rs_set_tower_ed rs1 d.(loc_var)
            (exist_tval_ed (TBytes 200)
               (VBytes 200 (pack_xyzt5 (x  mod ed25519_p) (y  mod ed25519_p)
                                       (z  mod ed25519_p) (ta mod ed25519_p)
                                       (tb mod ed25519_p)))).

Definition fe25519_callees_honoured_add
    (callee_post   : String.string -> list located_ed -> located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop)
    (callee_post_n : String.string -> list located_ed ->
                     list located_ed ->
                     rust_state_ed -> rust_state_ed -> Prop) : Prop :=
     unpack_xyzt5_contract callee_post_n
  /\ pack_xyzt5_contract   callee_post_n
  /\ fp_binop_contract callee_post "fe25519_mul"    (fun a b => a * b)
  /\ fp_binop_contract callee_post "fe25519_add"    (fun a b => a + b)
  /\ fp_binop_contract callee_post "fe25519_sub"    (fun a b => a - b)
  /\ fp_unop_contract  callee_post "fe25519_mul_d2" (fun a => 2 * ed25519_d * a)
  /\ fp_unop_contract  callee_post "fe25519_mul_2"  (fun a => 2 * a).

Definition xyzt_add_scratch_vars : list String.string :=
  ["X1"; "Y1"; "Z1"; "Ta1"; "Tb1";
   "X2"; "Y2"; "Z2"; "Ta2"; "Tb2";
   "T1"; "T2";
   "A"; "B"; "C"; "D"; "E"; "F"; "G"; "H"; "X3"; "Y3"; "Z3"].

(** Corrected reference: Hisil's cached T is [Ta * Tb], with NO
    z-inverse.  See the report for why [XyztAddVerified.extended_T]'s
    [pow_mod z (p-2) p] factor is a spec defect. *)
Definition ed25519_xyzt_add_gallina_fixed
    (p1 p2 : list Byte.byte) : list Byte.byte :=
  if andb (Nat.eqb (length p1) 200) (Nat.eqb (length p2) 200) then
    let '(x1, y1, z1, ta1, tb1) := parse_xyzt5 p1 in
    let '(x2, y2, z2, ta2, tb2) := parse_xyzt5 p2 in
    let t1 := (ta1 * tb1) mod ed25519_p in
    let t2 := (ta2 * tb2) mod ed25519_p in
    let a  := ((y1 - x1) * (y2 - x2)) mod ed25519_p in
    let b  := ((y1 + x1) * (y2 + x2)) mod ed25519_p in
    let c  := (t1 * (2 * ed25519_d) * t2) mod ed25519_p in
    let d  := (2 * z1 * z2) mod ed25519_p in
    let e  := (b - a) mod ed25519_p in
    let f  := (d - c) mod ed25519_p in
    let g  := (d + c) mod ed25519_p in
    let h  := (b + a) mod ed25519_p in
    let x3 := (e * f) mod ed25519_p in
    let y3 := (g * h) mod ed25519_p in
    let z3 := (f * g) mod ed25519_p in
    pack_xyzt5 x3 y3 z3 e h
  else
    List.repeat Byte.x00 200.

(* ================================================================ *)
(* §C.  State-lookup infrastructure                                  *)
(* ================================================================ *)

Lemma rs_get_set_eq : forall rs x v,
  rs_get_tower_ed (rs_set_tower_ed rs x v) x = Some v.
Proof.
  intros rs x v. unfold rs_get_tower_ed, rs_set_tower_ed. cbn.
  apply lookup_t_ed_update_at.
Qed.

Lemma rs_get_set_neq : forall rs x v y,
  y <> x ->
  rs_get_tower_ed (rs_set_tower_ed rs x v) y = rs_get_tower_ed rs y.
Proof.
  intros rs x v y Hne. unfold rs_get_tower_ed, rs_set_tower_ed. cbn.
  apply lookup_t_ed_update_other; exact Hne.
Qed.

Lemma fp_slot_intro : forall rs v l x,
  rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 l)) ->
  length l = 5%nat ->
  limbs_eval l = x mod ed25519_p ->
  fp_slot rs v x.
Proof. intros rs v l x H1 H2 H3. exists l. auto. Qed.

Lemma fp_slot_set_eq : forall rs w limbs x,
  length limbs = 5%nat ->
  limbs_eval limbs = x mod ed25519_p ->
  fp_slot (set_fp rs w limbs) w x.
Proof.
  intros rs w limbs x Hlen Hev.
  apply (fp_slot_intro _ _ limbs); [ apply rs_get_set_eq | exact Hlen | exact Hev ].
Qed.

Lemma fp_slot_set_other : forall rs v x w limbs,
  v <> w -> fp_slot rs v x -> fp_slot (set_fp rs w limbs) v x.
Proof.
  intros rs v x w limbs Hne [l [Hg [Hl He]]].
  exists l. split; [| split; assumption].
  unfold set_fp. rewrite rs_get_set_neq by exact Hne. exact Hg.
Qed.

Lemma bytes200_slot_set_tower_other : forall rs v bs w tv,
  v <> w -> bytes200_slot rs v bs -> bytes200_slot (rs_set_tower_ed rs w tv) v bs.
Proof.
  intros rs v bs w tv Hne Hb. unfold bytes200_slot in *.
  rewrite rs_get_set_neq by exact Hne. exact Hb.
Qed.

Lemma bytes200_slot_set_fp_other : forall rs v bs w limbs,
  v <> w -> bytes200_slot rs v bs -> bytes200_slot (set_fp rs w limbs) v bs.
Proof.
  intros. unfold set_fp. apply bytes200_slot_set_tower_other; assumption.
Qed.

Lemma notin_scratch_neq : forall v w,
  ~ In v xyzt_add_scratch_vars -> In w xyzt_add_scratch_vars -> v <> w.
Proof. intros v w Hn Hi Heq. subst. contradiction. Qed.

Ltac solve_neq_scratch :=
  match goal with
  | [ H : ~ In ?v xyzt_add_scratch_vars |- ?v <> _ ] =>
      apply (notin_scratch_neq _ _ H); cbv [xyzt_add_scratch_vars]; cbn; tauto
  end.

Ltac fp_lookup :=
  repeat first
    [ apply rs_get_set_eq
    | rewrite rs_get_set_neq by discriminate
    | match goal with
      | [ H : ?r = _ |- context[rs_get_tower_ed ?r _] ] => rewrite H; unfold set_fp
      end ].

Ltac bytes_lookup :=
  repeat first
    [ eassumption
    | match goal with
      | [ H : ?r = _ |- bytes200_slot ?r _ _ ] => rewrite H
      end
    | apply bytes200_slot_set_fp_other; [ solve_neq_scratch | ] ].

Section AddInv.
  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec := (rust_exec_ed callee_post callee_post_n function_table).

  Lemma add_seq_inv : forall c1 c2 rs1 rs3,
    Hexec (REdSeq c1 c2) rs1 rs3 -> exists rs2, Hexec c1 rs1 rs2 /\ Hexec c2 rs2 rs3.
  Proof. intros c1 c2 rs1 rs3 H. inversion H; subst. eexists; eauto. Qed.

  Lemma add_letzero_inv : forall x t c rs1 rs2,
    Hexec (REdLetZero x t c) rs1 rs2 ->
    exists v, well_formed_ed v /\
      Hexec c (rs_set_tower_ed rs1 x (exist_tval_ed t v)) rs2.
  Proof.
    intros x t c rs1 rs2 H. inversion H; subst. eexists; split; eassumption.
  Qed.

  Lemma add_call_inv : forall fname dst args rs1 rs2,
    Hexec (REdCall fname dst args) rs1 rs2 -> callee_post fname args dst rs1 rs2.
  Proof. intros. inversion H; subst; assumption. Qed.

  Lemma add_calln_inv : forall fname dests args rs1 rs2,
    Hexec (REdCallN fname dests args) rs1 rs2 -> callee_post_n fname dests args rs1 rs2.
  Proof. intros. inversion H; subst; assumption. Qed.
End AddInv.

Lemma add_strip_lets :
  forall callee_post callee_post_n function_table (c : rust_cmd_ed) rs1 rs2,
  rust_exec_ed callee_post callee_post_n function_table
    (REdLetZero "X1"  TFp25519 (REdLetZero "Y1"  TFp25519 (
     REdLetZero "Z1"  TFp25519 (REdLetZero "Ta1" TFp25519 (
     REdLetZero "Tb1" TFp25519 (REdLetZero "X2"  TFp25519 (
     REdLetZero "Y2"  TFp25519 (REdLetZero "Z2"  TFp25519 (
     REdLetZero "Ta2" TFp25519 (REdLetZero "Tb2" TFp25519 (
     REdLetZero "T1"  TFp25519 (REdLetZero "T2"  TFp25519 (
     REdLetZero "A"   TFp25519 (REdLetZero "B"   TFp25519 (
     REdLetZero "C"   TFp25519 (REdLetZero "D"   TFp25519 (
     REdLetZero "E"   TFp25519 (REdLetZero "F"   TFp25519 (
     REdLetZero "G"   TFp25519 (REdLetZero "H"   TFp25519 (
     REdLetZero "X3"  TFp25519 (REdLetZero "Y3"  TFp25519 (
     REdLetZero "Z3"  TFp25519 c
     )))))))))))))))))))))))
    rs1 rs2 ->
  exists rsL,
    rust_exec_ed callee_post callee_post_n function_table c rsL rs2
    /\ (forall v, ~ In v xyzt_add_scratch_vars ->
          rs_get_tower_ed rsL v = rs_get_tower_ed rs1 v).
Proof.
  intros cp cpn ft c rs1 rs2 H.
  repeat (apply add_letzero_inv in H; destruct H as [? [? H]]).
  eexists. split; [ exact H | ].
  intros v Hv.
  repeat (rewrite rs_get_set_neq by solve_neq_scratch).
  reflexivity.
Qed.

(* ================================================================ *)
(* §D.  Correctness theorem                                          *)
(* ================================================================ *)

Theorem xyzt_add_body_decomposed_correct :
  forall callee_post callee_post_n function_table
         (P1 P2 dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (p1_bs p2_bs : list Byte.byte),
    fe25519_callees_honoured_add callee_post callee_post_n ->
    length p1_bs = 200%nat ->
    length p2_bs = 200%nat ->
    P1.(loc_type)   = TBytes 200 ->
    P2.(loc_type)   = TBytes 200 ->
    dest.(loc_type) = TBytes 200 ->
    ~ In P1.(loc_var) xyzt_add_scratch_vars ->
    ~ In P2.(loc_var) xyzt_add_scratch_vars ->
    bytes200_slot rs1 P1.(loc_var) p1_bs ->
    bytes200_slot rs1 P2.(loc_var) p2_bs ->
    rust_exec_ed callee_post callee_post_n function_table
                 (xyzt_add_body_decomposed dest [P1; P2]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_xyzt_add_gallina_fixed p1_bs p2_bs))).
Proof.
  intros cp cpn ft P1 P2 dest rs1 rs2 p1_bs p2_bs
         Hhon Hl1 Hl2 Ht1 Ht2 Htd Hni1 Hni2 Hb1 Hb2 Hexec.
  cbv [xyzt_add_body_decomposed] in Hexec.
  apply add_strip_lets in Hexec.
  destruct Hexec as [rsL [Hexec Hframe]].
  cbv [XyztAddBodyDecomposed.LE_TFp25519] in Hexec.
  destruct Hhon as [Hunp [Hpk [Hmul [Hadd [Hsub [Hd2 Hm2]]]]]].
  apply add_seq_inv in Hexec; destruct Hexec as [r1  [C1  Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r2  [C2  Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r3  [C3  Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r4  [C4  Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r5  [C5  Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r6  [C6  Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r7  [C7  Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r8  [C8  Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r9  [C9  Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r10 [C10 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r11 [C11 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r12 [C12 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r13 [C13 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r14 [C14 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r15 [C15 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r16 [C16 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r17 [C17 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r18 [C18 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r19 [C19 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r20 [C20 Hexec]].
  apply add_seq_inv in Hexec; destruct Hexec as [r21 [C21 Hexec]].
  rename Hexec into C22.
  apply add_calln_inv in C1. apply add_calln_inv in C2. apply add_calln_inv in C22.
  apply add_call_inv in C3.  apply add_call_inv in C4.  apply add_call_inv in C5.
  apply add_call_inv in C6.  apply add_call_inv in C7.  apply add_call_inv in C8.
  apply add_call_inv in C9.  apply add_call_inv in C10. apply add_call_inv in C11.
  apply add_call_inv in C12. apply add_call_inv in C13. apply add_call_inv in C14.
  apply add_call_inv in C15. apply add_call_inv in C16. apply add_call_inv in C17.
  apply add_call_inv in C18. apply add_call_inv in C19. apply add_call_inv in C20.
  apply add_call_inv in C21.
  assert (Hb1L : bytes200_slot rsL (loc_var P1) p1_bs)
    by (unfold bytes200_slot in *; rewrite Hframe by assumption; exact Hb1).
  assert (Hb2L : bytes200_slot rsL (loc_var P2) p2_bs)
    by (unfold bytes200_slot in *; rewrite Hframe by assumption; exact Hb2).
  clear Hframe Hb1 Hb2.
  edestruct (Hunp _ _ _ _ _ _ _ _ _ C1 Ht1 Hb1L Hl1
               eq_refl eq_refl eq_refl eq_refl eq_refl)
    as [lx1 [ly1 [lz1 [lta1 [ltb1 [Lx1 [Ly1 [Lz1 [Lta1 [Ltb1 [Hev1 Hr1]]]]]]]]]]].
  cbn in Hr1.
  assert (Hb2r1 : bytes200_slot r1 (loc_var P2) p2_bs) by bytes_lookup.
  edestruct (Hunp _ _ _ _ _ _ _ _ _ C2 Ht2 Hb2r1 Hl2
               eq_refl eq_refl eq_refl eq_refl eq_refl)
    as [lx2 [ly2 [lz2 [lta2 [ltb2 [Lx2 [Ly2 [Lz2 [Lta2 [Ltb2 [Hev2 Hr2]]]]]]]]]]].
  cbn in Hr2.
  clear C1 C2 Hb1L Hb2L Hb2r1 Ht1 Ht2 Hni1 Hni2.
  destruct (parse_xyzt5 p1_bs) as [[[[x1 y1] z1] ta1] tb1] eqn:Hp1.
  destruct (parse_xyzt5 p2_bs) as [[[[x2 y2] z2] ta2] tb2] eqn:Hp2.
  destruct Hev1 as [Ex1 [Ey1 [Ez1 [Eta1 Etb1]]]].
  destruct Hev2 as [Ex2 [Ey2 [Ez2 [Eta2 Etb2]]]].
  eassert (Sa : fp_slot r2 "Ta1" _)
    by (apply (fp_slot_intro _ _ lta1); [ fp_lookup | exact Lta1 | exact Eta1 ]).
  eassert (Sb : fp_slot r2 "Tb1" _)
    by (apply (fp_slot_intro _ _ ltb1); [ fp_lookup | exact Ltb1 | exact Etb1 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C3 eq_refl eq_refl eq_refl Sa Sb)
    as [l3 [L3 [E3 Hr3]]].
  cbn in Hr3. cbv beta in E3. clear Sa Sb C3.
  eassert (Sa : fp_slot r3 "Ta2" _)
    by (apply (fp_slot_intro _ _ lta2); [ fp_lookup | exact Lta2 | exact Eta2 ]).
  eassert (Sb : fp_slot r3 "Tb2" _)
    by (apply (fp_slot_intro _ _ ltb2); [ fp_lookup | exact Ltb2 | exact Etb2 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C4 eq_refl eq_refl eq_refl Sa Sb)
    as [l4 [L4 [E4 Hr4]]].
  cbn in Hr4. cbv beta in E4. clear Sa Sb C4.
  eassert (Sa : fp_slot r4 "Y1" _)
    by (apply (fp_slot_intro _ _ ly1); [ fp_lookup | exact Ly1 | exact Ey1 ]).
  eassert (Sb : fp_slot r4 "X1" _)
    by (apply (fp_slot_intro _ _ lx1); [ fp_lookup | exact Lx1 | exact Ex1 ]).
  edestruct (Hsub _ _ _ _ _ _ _ C5 eq_refl eq_refl eq_refl Sa Sb)
    as [l5 [L5 [E5 Hr5]]].
  cbn in Hr5. cbv beta in E5. clear Sa Sb C5.
  eassert (Sa : fp_slot r5 "Y2" _)
    by (apply (fp_slot_intro _ _ ly2); [ fp_lookup | exact Ly2 | exact Ey2 ]).
  eassert (Sb : fp_slot r5 "X2" _)
    by (apply (fp_slot_intro _ _ lx2); [ fp_lookup | exact Lx2 | exact Ex2 ]).
  edestruct (Hsub _ _ _ _ _ _ _ C6 eq_refl eq_refl eq_refl Sa Sb)
    as [l6 [L6 [E6 Hr6]]].
  cbn in Hr6. cbv beta in E6. clear Sa Sb C6.
  eassert (Sa : fp_slot r6 "Y3" _)
    by (apply (fp_slot_intro _ _ l5); [ fp_lookup | exact L5 | exact E5 ]).
  eassert (Sb : fp_slot r6 "Z3" _)
    by (apply (fp_slot_intro _ _ l6); [ fp_lookup | exact L6 | exact E6 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C7 eq_refl eq_refl eq_refl Sa Sb)
    as [l7 [L7 [E7 Hr7]]].
  cbn in Hr7. cbv beta in E7. clear Sa Sb C7.
  eassert (Sa : fp_slot r7 "Y1" _)
    by (apply (fp_slot_intro _ _ ly1); [ fp_lookup | exact Ly1 | exact Ey1 ]).
  eassert (Sb : fp_slot r7 "X1" _)
    by (apply (fp_slot_intro _ _ lx1); [ fp_lookup | exact Lx1 | exact Ex1 ]).
  edestruct (Hadd _ _ _ _ _ _ _ C8 eq_refl eq_refl eq_refl Sa Sb)
    as [l8 [L8 [E8 Hr8]]].
  cbn in Hr8. cbv beta in E8. clear Sa Sb C8.
  eassert (Sa : fp_slot r8 "Y2" _)
    by (apply (fp_slot_intro _ _ ly2); [ fp_lookup | exact Ly2 | exact Ey2 ]).
  eassert (Sb : fp_slot r8 "X2" _)
    by (apply (fp_slot_intro _ _ lx2); [ fp_lookup | exact Lx2 | exact Ex2 ]).
  edestruct (Hadd _ _ _ _ _ _ _ C9 eq_refl eq_refl eq_refl Sa Sb)
    as [l9 [L9 [E9 Hr9]]].
  cbn in Hr9. cbv beta in E9. clear Sa Sb C9.
  eassert (Sa : fp_slot r9 "Y3" _)
    by (apply (fp_slot_intro _ _ l8); [ fp_lookup | exact L8 | exact E8 ]).
  eassert (Sb : fp_slot r9 "Z3" _)
    by (apply (fp_slot_intro _ _ l9); [ fp_lookup | exact L9 | exact E9 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C10 eq_refl eq_refl eq_refl Sa Sb)
    as [l10 [L10 [E10 Hr10]]].
  cbn in Hr10. cbv beta in E10. clear Sa Sb C10.
  eassert (Sa : fp_slot r10 "T1" _)
    by (apply (fp_slot_intro _ _ l3); [ fp_lookup | exact L3 | exact E3 ]).
  edestruct (Hd2 _ _ _ _ _ C11 eq_refl eq_refl Sa) as [l11 [L11 [E11 Hr11]]].
  cbn in Hr11. cbv beta in E11. clear Sa C11.
  eassert (Sa : fp_slot r11 "Y3" _)
    by (apply (fp_slot_intro _ _ l11); [ fp_lookup | exact L11 | exact E11 ]).
  eassert (Sb : fp_slot r11 "T2" _)
    by (apply (fp_slot_intro _ _ l4); [ fp_lookup | exact L4 | exact E4 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C12 eq_refl eq_refl eq_refl Sa Sb)
    as [l12 [L12 [E12 Hr12]]].
  cbn in Hr12. cbv beta in E12. clear Sa Sb C12.
  eassert (Sa : fp_slot r12 "Z1" _)
    by (apply (fp_slot_intro _ _ lz1); [ fp_lookup | exact Lz1 | exact Ez1 ]).
  eassert (Sb : fp_slot r12 "Z2" _)
    by (apply (fp_slot_intro _ _ lz2); [ fp_lookup | exact Lz2 | exact Ez2 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C13 eq_refl eq_refl eq_refl Sa Sb)
    as [l13 [L13 [E13 Hr13]]].
  cbn in Hr13. cbv beta in E13. clear Sa Sb C13.
  eassert (Sa : fp_slot r13 "Y3" _)
    by (apply (fp_slot_intro _ _ l13); [ fp_lookup | exact L13 | exact E13 ]).
  edestruct (Hm2 _ _ _ _ _ C14 eq_refl eq_refl Sa) as [l14 [L14 [E14 Hr14]]].
  cbn in Hr14. cbv beta in E14. clear Sa C14.
  eassert (Sa : fp_slot r14 "B" _)
    by (apply (fp_slot_intro _ _ l10); [ fp_lookup | exact L10 | exact E10 ]).
  eassert (Sb : fp_slot r14 "A" _)
    by (apply (fp_slot_intro _ _ l7); [ fp_lookup | exact L7 | exact E7 ]).
  edestruct (Hsub _ _ _ _ _ _ _ C15 eq_refl eq_refl eq_refl Sa Sb)
    as [l15 [L15 [E15 Hr15]]].
  cbn in Hr15. cbv beta in E15. clear Sa Sb C15.
  eassert (Sa : fp_slot r15 "D" _)
    by (apply (fp_slot_intro _ _ l14); [ fp_lookup | exact L14 | exact E14 ]).
  eassert (Sb : fp_slot r15 "C" _)
    by (apply (fp_slot_intro _ _ l12); [ fp_lookup | exact L12 | exact E12 ]).
  edestruct (Hsub _ _ _ _ _ _ _ C16 eq_refl eq_refl eq_refl Sa Sb)
    as [l16 [L16 [E16 Hr16]]].
  cbn in Hr16. cbv beta in E16. clear Sa Sb C16.
  eassert (Sa : fp_slot r16 "D" _)
    by (apply (fp_slot_intro _ _ l14); [ fp_lookup | exact L14 | exact E14 ]).
  eassert (Sb : fp_slot r16 "C" _)
    by (apply (fp_slot_intro _ _ l12); [ fp_lookup | exact L12 | exact E12 ]).
  edestruct (Hadd _ _ _ _ _ _ _ C17 eq_refl eq_refl eq_refl Sa Sb)
    as [l17 [L17 [E17 Hr17]]].
  cbn in Hr17. cbv beta in E17. clear Sa Sb C17.
  eassert (Sa : fp_slot r17 "B" _)
    by (apply (fp_slot_intro _ _ l10); [ fp_lookup | exact L10 | exact E10 ]).
  eassert (Sb : fp_slot r17 "A" _)
    by (apply (fp_slot_intro _ _ l7); [ fp_lookup | exact L7 | exact E7 ]).
  edestruct (Hadd _ _ _ _ _ _ _ C18 eq_refl eq_refl eq_refl Sa Sb)
    as [l18 [L18 [E18 Hr18]]].
  cbn in Hr18. cbv beta in E18. clear Sa Sb C18.
  eassert (Sa : fp_slot r18 "E" _)
    by (apply (fp_slot_intro _ _ l15); [ fp_lookup | exact L15 | exact E15 ]).
  eassert (Sb : fp_slot r18 "F" _)
    by (apply (fp_slot_intro _ _ l16); [ fp_lookup | exact L16 | exact E16 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C19 eq_refl eq_refl eq_refl Sa Sb)
    as [l19 [L19 [E19 Hr19]]].
  cbn in Hr19. cbv beta in E19. clear Sa Sb C19.
  eassert (Sa : fp_slot r19 "G" _)
    by (apply (fp_slot_intro _ _ l17); [ fp_lookup | exact L17 | exact E17 ]).
  eassert (Sb : fp_slot r19 "H" _)
    by (apply (fp_slot_intro _ _ l18); [ fp_lookup | exact L18 | exact E18 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C20 eq_refl eq_refl eq_refl Sa Sb)
    as [l20 [L20 [E20 Hr20]]].
  cbn in Hr20. cbv beta in E20. clear Sa Sb C20.
  eassert (Sa : fp_slot r20 "F" _)
    by (apply (fp_slot_intro _ _ l16); [ fp_lookup | exact L16 | exact E16 ]).
  eassert (Sb : fp_slot r20 "G" _)
    by (apply (fp_slot_intro _ _ l17); [ fp_lookup | exact L17 | exact E17 ]).
  edestruct (Hmul _ _ _ _ _ _ _ C21 eq_refl eq_refl eq_refl Sa Sb)
    as [l21 [L21 [E21 Hr21]]].
  cbn in Hr21. cbv beta in E21. clear Sa Sb C21.
  eassert (SX3 : fp_slot r21 "X3" _)
    by (apply (fp_slot_intro _ _ l19); [ fp_lookup | exact L19 | exact E19 ]).
  eassert (SY3 : fp_slot r21 "Y3" _)
    by (apply (fp_slot_intro _ _ l20); [ fp_lookup | exact L20 | exact E20 ]).
  eassert (SZ3 : fp_slot r21 "Z3" _)
    by (apply (fp_slot_intro _ _ l21); [ fp_lookup | exact L21 | exact E21 ]).
  eassert (SE : fp_slot r21 "E" _)
    by (apply (fp_slot_intro _ _ l15); [ fp_lookup | exact L15 | exact E15 ]).
  eassert (SH : fp_slot r21 "H" _)
    by (apply (fp_slot_intro _ _ l18); [ fp_lookup | exact L18 | exact E18 ]).
  pose proof (Hpk _ _ _ _ _ _ _ _ _ _ _ _ _ C22 Htd
                 eq_refl eq_refl eq_refl eq_refl eq_refl
                 SX3 SY3 SZ3 SE SH) as Hrs2.
  rewrite Hrs2, rs_get_set_eq.
  match goal with
  | [ |- Some (exist_tval_ed (TBytes 200) (VBytes 200 ?A))
       = Some (exist_tval_ed (TBytes 200) (VBytes 200 ?B)) ] =>
      assert (Hbe : A = B)
  end.
  { cbv [ed25519_xyzt_add_gallina_fixed].
    rewrite Hl1, Hl2, Nat.eqb_refl. cbn [andb].
    rewrite Hp1, Hp2. cbv beta iota zeta.
    f_equal; push_Zmod; pull_Zmod; try reflexivity; f_equal; ring. }
  rewrite Hbe. reflexivity.
Qed.

Print Assumptions xyzt_add_body_decomposed_correct.

(* ================================================================ *)
(* §E.  Anti-vacuity: a concrete oracle pair that honours the        *)
(*      strengthened predicate.                                      *)
(* ================================================================ *)

Definition fp_enc (x : Z) : list Z := [x mod ed25519_p; 0; 0; 0; 0].

Lemma fp_enc_len : forall x, length (fp_enc x) = 5%nat.
Proof. reflexivity. Qed.

Lemma fp_enc_eval : forall x, limbs_eval (fp_enc x) = x mod ed25519_p.
Proof.
  intros x. cbv [fp_enc limbs_eval]. cbn [List.nth].
  assert (Hr : x mod ed25519_p + 2 ^ 51 * 0 + 2 ^ 102 * 0 + 2 ^ 153 * 0
                 + 2 ^ 204 * 0 = x mod ed25519_p) by ring.
  rewrite Hr. apply Zmod_mod.
Qed.

Definition dec_fp (rs : rust_state_ed) (v : String.string) : Z :=
  match rs_get_tower_ed rs v with
  | Some (exist_tval_ed TFp25519 (VFp25519 l)) => limbs_eval l
  | _ => 0
  end.

Definition dec_bytes200 (rs : rust_state_ed) (v : String.string)
  : list Byte.byte :=
  match rs_get_tower_ed rs v with
  | Some (exist_tval_ed (TBytes _) (VBytes _ bs)) => bs
  | _ => List.repeat Byte.x00 200
  end.

Lemma dec_fp_correct : forall rs v x,
  fp_slot rs v x -> dec_fp rs v = x mod ed25519_p.
Proof.
  intros rs v x [l [Hg [_ He]]]. unfold dec_fp. rewrite Hg. exact He.
Qed.

Lemma dec_fp_set_eq : forall rs w l, dec_fp (set_fp rs w l) w = limbs_eval l.
Proof.
  intros rs w l. unfold dec_fp, set_fp. rewrite rs_get_set_eq. reflexivity.
Qed.

Lemma dec_bytes200_correct : forall rs v bs,
  bytes200_slot rs v bs -> dec_bytes200 rs v = bs.
Proof.
  intros rs v bs Hb. unfold dec_bytes200, bytes200_slot in *.
  rewrite Hb. reflexivity.
Qed.

Definition ed_binop_post (f : Z -> Z -> Z)
    (args : list located_ed) (dst : located_ed)
    (rs1 rs2 : rust_state_ed) : Prop :=
  match args with
  | [a; b] =>
      rs2 = set_fp rs1 dst.(loc_var)
              (fp_enc (f (dec_fp rs1 a.(loc_var)) (dec_fp rs1 b.(loc_var))))
  | _ => False
  end.

Definition ed_unop_post (f : Z -> Z)
    (args : list located_ed) (dst : located_ed)
    (rs1 rs2 : rust_state_ed) : Prop :=
  match args with
  | [a] => rs2 = set_fp rs1 dst.(loc_var) (fp_enc (f (dec_fp rs1 a.(loc_var))))
  | _ => False
  end.

Definition ed_unpack_post (dests args : list located_ed)
    (rs1 rs2 : rust_state_ed) : Prop :=
  match dests, args with
  | [dx; dy; dz; dta; dtb], [src] =>
      let '(x, y, z, ta, tb) := parse_xyzt5 (dec_bytes200 rs1 src.(loc_var)) in
      rs2 = set_fp (set_fp (set_fp (set_fp (set_fp rs1
                dx.(loc_var)  (fp_enc x))
                dy.(loc_var)  (fp_enc y))
                dz.(loc_var)  (fp_enc z))
                dta.(loc_var) (fp_enc ta))
                dtb.(loc_var) (fp_enc tb)
  | _, _ => False
  end.

Definition ed_pack_post (dests args : list located_ed)
    (rs1 rs2 : rust_state_ed) : Prop :=
  match dests, args with
  | [d], [sx; sy; sz; sta; stb] =>
      rs2 = rs_set_tower_ed rs1 d.(loc_var)
              (exist_tval_ed (TBytes 200)
                 (VBytes 200 (pack_xyzt5 (dec_fp rs1 sx.(loc_var))
                                         (dec_fp rs1 sy.(loc_var))
                                         (dec_fp rs1 sz.(loc_var))
                                         (dec_fp rs1 sta.(loc_var))
                                         (dec_fp rs1 stb.(loc_var)))))
  | _, _ => False
  end.

Definition witness_cp (fname : String.string) (args : list located_ed)
    (dst : located_ed) (rs1 rs2 : rust_state_ed) : Prop :=
     (fname = "fe25519_mul"    /\ ed_binop_post (fun a b => a * b) args dst rs1 rs2)
  \/ (fname = "fe25519_add"    /\ ed_binop_post (fun a b => a + b) args dst rs1 rs2)
  \/ (fname = "fe25519_sub"    /\ ed_binop_post (fun a b => a - b) args dst rs1 rs2)
  \/ (fname = "fe25519_mul_d2" /\ ed_unop_post (fun a => 2 * ed25519_d * a) args dst rs1 rs2)
  \/ (fname = "fe25519_mul_2"  /\ ed_unop_post (fun a => 2 * a) args dst rs1 rs2).

Definition witness_cpn (fname : String.string) (dests args : list located_ed)
    (rs1 rs2 : rust_state_ed) : Prop :=
     (fname = "fe25519_unpack_xyzt5" /\ ed_unpack_post dests args rs1 rs2)
  \/ (fname = "fe25519_pack_xyzt5"   /\ ed_pack_post dests args rs1 rs2).

Theorem witness_honours_add :
  fe25519_callees_honoured_add witness_cp witness_cpn.
Proof.
  unfold fe25519_callees_honoured_add. repeat apply conj.
  - (* unpack *)
    intros dx dy dz dta dtb src rs1 rs2 bs Hc Hsrc Hb Hlen _ _ _ _ _.
    destruct Hc as [[_ Hc] | [Hbad _]]; [| discriminate].
    cbv [ed_unpack_post] in Hc.
    rewrite (dec_bytes200_correct _ _ _ Hb) in Hc.
    destruct (parse_xyzt5 bs) as [[[[x y] z] ta] tb] eqn:Hp.
    exists (fp_enc x), (fp_enc y), (fp_enc z), (fp_enc ta), (fp_enc tb).
    repeat apply conj;
      first [ apply fp_enc_len | apply fp_enc_eval | exact Hc ].
  - (* pack *)
    intros d sx sy sz sta stb rs1 rs2 x y z ta tb Hc Hd _ _ _ _ _ Sx Sy Sz Sta Stb.
    destruct Hc as [[Hbad _] | [_ Hc]]; [ discriminate |].
    cbv [ed_pack_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sx), (dec_fp_correct _ _ _ Sy),
            (dec_fp_correct _ _ _ Sz), (dec_fp_correct _ _ _ Sta),
            (dec_fp_correct _ _ _ Stb) in Hc.
    exact Hc.
  - (* mul *)
    intros dst a b rs1 rs2 xa xb Hc _ _ _ Sa Sb.
    destruct Hc as [[_ Hc]|[[Hbad _]|[[Hbad _]|[[Hbad _]|[Hbad _]]]]];
      try discriminate.
    cbv [ed_binop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa), (dec_fp_correct _ _ _ Sb) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* add *)
    intros dst a b rs1 rs2 xa xb Hc _ _ _ Sa Sb.
    destruct Hc as [[Hbad _]|[[_ Hc]|[[Hbad _]|[[Hbad _]|[Hbad _]]]]];
      try discriminate.
    cbv [ed_binop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa), (dec_fp_correct _ _ _ Sb) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* sub *)
    intros dst a b rs1 rs2 xa xb Hc _ _ _ Sa Sb.
    destruct Hc as [[Hbad _]|[[Hbad _]|[[_ Hc]|[[Hbad _]|[Hbad _]]]]];
      try discriminate.
    cbv [ed_binop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa), (dec_fp_correct _ _ _ Sb) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* mul_d2 *)
    intros dst a rs1 rs2 xa Hc _ _ Sa.
    destruct Hc as [[Hbad _]|[[Hbad _]|[[Hbad _]|[[_ Hc]|[Hbad _]]]]];
      try discriminate.
    cbv [ed_unop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
  - (* mul_2 *)
    intros dst a rs1 rs2 xa Hc _ _ Sa.
    destruct Hc as [[Hbad _]|[[Hbad _]|[[Hbad _]|[[Hbad _]|[_ Hc]]]]];
      try discriminate.
    cbv [ed_unop_post] in Hc.
    rewrite (dec_fp_correct _ _ _ Sa) in Hc.
    eexists. repeat apply conj; [ apply fp_enc_len | | exact Hc ].
    rewrite fp_enc_eval. push_Zmod; pull_Zmod; reflexivity.
Qed.

Print Assumptions witness_honours_add.

(* ================================================================ *)
(* §F.  The strengthened predicate excludes the stale-dest oracle    *)
(* ================================================================ *)

(** (b1) Under the strengthened predicate, the destination really is
    written with the mathematically right value. *)
Lemma honoured_mul_writes_dest :
  forall cp cpn,
    fe25519_callees_honoured_add cp cpn ->
    forall dst a b rs1 rs2 xa xb,
      cp "fe25519_mul" [a; b] dst rs1 rs2 ->
      a.(loc_type) = TFp25519 -> b.(loc_type) = TFp25519 ->
      dst.(loc_type) = TFp25519 ->
      fp_slot rs1 a.(loc_var) xa -> fp_slot rs1 b.(loc_var) xb ->
      fp_slot rs2 dst.(loc_var) (xa * xb).
Proof.
  intros cp cpn Hhon dst a b rs1 rs2 xa xb Hc Ha Hb Hd Sa Sb.
  destruct Hhon as [_ [_ [Hmul _]]].
  edestruct (Hmul _ _ _ _ _ _ _ Hc Ha Hb Hd Sa Sb) as [l [Hl [He Hr]]].
  subst rs2. apply fp_slot_set_eq; [ exact Hl | exact He ].
Qed.

(** (b2) The old, type-only obligation admits an oracle that never
    touches the destination. *)
Definition stale_cp (fname : String.string) (args : list located_ed)
    (dst : located_ed) (rs1 rs2 : rust_state_ed) : Prop :=
  dst.(loc_type) = TFp25519 /\ rs2 = rs1.

Lemma stale_cp_satisfies_old_type_clause :
  forall fname dst args rs1 rs2,
    In fname ["fe25519_mul"; "fe25519_sub"; "fe25519_add";
              "fe25519_mul_d2"; "fe25519_mul_2"] ->
    stale_cp fname args dst rs1 rs2 ->
    dst.(loc_type) = TFp25519.
Proof. intros fname dst args rs1 rs2 _ [H _]. exact H. Qed.

(** (b3) ... but it does NOT satisfy the strengthened one. *)
Lemma stale_cp_violates_new_contract :
  ~ fp_binop_contract stale_cp "fe25519_mul" (fun a b => a * b).
Proof.
  intro H.
  pose (LA := {| loc_var := "a"; loc_type := TFp25519 |}).
  pose (LB := {| loc_var := "b"; loc_type := TFp25519 |}).
  pose (LD := {| loc_var := "d"; loc_type := TFp25519 |}).
  pose (rs := set_fp (set_fp (set_fp rs_empty_ed "a" [1;0;0;0;0])
                             "b" [1;0;0;0;0]) "d" [0;0;0;0;0]).
  assert (Sa : fp_slot rs "a" 1).
  { apply (fp_slot_intro _ _ [1;0;0;0;0]).
    - subst rs. unfold set_fp.
      rewrite rs_get_set_neq by discriminate.
      rewrite rs_get_set_neq by discriminate.
      apply rs_get_set_eq.
    - reflexivity.
    - cbv [limbs_eval]; cbn [List.nth]; f_equal; ring. }
  assert (Sb : fp_slot rs "b" 1).
  { apply (fp_slot_intro _ _ [1;0;0;0;0]).
    - subst rs. unfold set_fp.
      rewrite rs_get_set_neq by discriminate.
      apply rs_get_set_eq.
    - reflexivity.
    - cbv [limbs_eval]; cbn [List.nth]; f_equal; ring. }
  destruct (H LD LA LB rs rs 1 1 (conj eq_refl eq_refl)
              eq_refl eq_refl eq_refl Sa Sb) as [l [Hl [He Hr]]].
  assert (Hd : dec_fp rs LD.(loc_var) = limbs_eval l)
    by (rewrite Hr at 1; apply dec_fp_set_eq).
  rewrite He in Hd.
  subst rs. cbv [dec_fp set_fp] in Hd. rewrite rs_get_set_eq in Hd.
  cbv [limbs_eval] in Hd. cbn [List.nth] in Hd.
  vm_compute in Hd. discriminate.
Qed.

Print Assumptions stale_cp_violates_new_contract.

(* ================================================================ *)
(* §G.  The extended_T defect: bridge to the unmodified spec         *)
(* ================================================================ *)

Lemma mod3_l : forall a b c n, ((a mod n) * b * c) mod n = (a * b * c) mod n.
Proof.
  intros a b c n. rewrite <- Z.mul_assoc, Zmult_mod_idemp_l, Z.mul_assoc.
  reflexivity.
Qed.

Lemma mod3_r : forall a b c n, (a * b * (c mod n)) mod n = (a * b * c) mod n.
Proof. intros a b c n. apply Zmult_mod_idemp_r. Qed.

(** [XyztAddVerified.extended_T ta tb z = (ta*tb*z^(p-2)) mod p] carries a
    spurious z-inverse: the body computes a plain [Ta*Tb].  The two
    references agree exactly when the two z-inverses multiply to 1
    (in particular when Z1 = Z2 = 1). *)
Lemma add_gallina_fixed_eq_gallina :
  forall p1 p2 x1 y1 z1 ta1 tb1 x2 y2 z2 ta2 tb2,
    length p1 = 200%nat -> length p2 = 200%nat ->
    parse_xyzt5 p1 = (x1, y1, z1, ta1, tb1) ->
    parse_xyzt5 p2 = (x2, y2, z2, ta2, tb2) ->
    (pow_mod z1 (ed25519_p - 2) ed25519_p
     * pow_mod z2 (ed25519_p - 2) ed25519_p) mod ed25519_p = 1 ->
    ed25519_xyzt_add_gallina_fixed p1 p2 = ed25519_xyzt_add_gallina p1 p2.
Proof.
  intros p1 p2 x1 y1 z1 ta1 tb1 x2 y2 z2 ta2 tb2 Hl1 Hl2 Hp1 Hp2 Hinv.
  assert (Hc : (extended_T ta1 tb1 z1 * (2 * ed25519_d) * extended_T ta2 tb2 z2)
                 mod ed25519_p
             = ((ta1 * tb1) mod ed25519_p * (2 * ed25519_d)
                * ((ta2 * tb2) mod ed25519_p)) mod ed25519_p).
  { cbv [extended_T].
    rewrite !mod3_l, !mod3_r.
    assert (Hre : forall a b u c d v : Z,
              a * b * u * c * (d * v) = a * b * c * d * (u * v))
      by (intros; ring).
    rewrite Hre.
    rewrite (Zmult_mod (ta1 * tb1 * (2 * ed25519_d) * (ta2 * tb2))
                       (pow_mod z1 (ed25519_p - 2) ed25519_p
                        * pow_mod z2 (ed25519_p - 2) ed25519_p) ed25519_p).
    rewrite Hinv, Z.mul_1_r, Zmod_mod. reflexivity. }
  cbv [ed25519_xyzt_add_gallina_fixed ed25519_xyzt_add_gallina].
  rewrite Hl1, Hl2, Nat.eqb_refl. cbn [andb].
  rewrite Hp1, Hp2. cbv beta iota zeta.
  rewrite Hc. reflexivity.
Qed.

(** Restated theorem against the UNMODIFIED [ed25519_xyzt_add_gallina],
    at the cost of the extra z-inverse precondition. *)
Corollary xyzt_add_body_decomposed_correct_orig_spec :
  forall callee_post callee_post_n function_table
         (P1 P2 dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (p1_bs p2_bs : list Byte.byte)
         x1 y1 z1 ta1 tb1 x2 y2 z2 ta2 tb2,
    fe25519_callees_honoured_add callee_post callee_post_n ->
    length p1_bs = 200%nat ->
    length p2_bs = 200%nat ->
    P1.(loc_type)   = TBytes 200 ->
    P2.(loc_type)   = TBytes 200 ->
    dest.(loc_type) = TBytes 200 ->
    ~ In P1.(loc_var) xyzt_add_scratch_vars ->
    ~ In P2.(loc_var) xyzt_add_scratch_vars ->
    bytes200_slot rs1 P1.(loc_var) p1_bs ->
    bytes200_slot rs1 P2.(loc_var) p2_bs ->
    parse_xyzt5 p1_bs = (x1, y1, z1, ta1, tb1) ->
    parse_xyzt5 p2_bs = (x2, y2, z2, ta2, tb2) ->
    (pow_mod z1 (ed25519_p - 2) ed25519_p
     * pow_mod z2 (ed25519_p - 2) ed25519_p) mod ed25519_p = 1 ->
    rust_exec_ed callee_post callee_post_n function_table
                 (xyzt_add_body_decomposed dest [P1; P2]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_xyzt_add_gallina p1_bs p2_bs))).
Proof.
  intros cp cpn ft P1 P2 dest rs1 rs2 p1_bs p2_bs
         x1 y1 z1 ta1 tb1 x2 y2 z2 ta2 tb2
         Hhon Hl1 Hl2 Ht1 Ht2 Htd Hni1 Hni2 Hb1 Hb2 Hp1 Hp2 Hinv Hexec.
  rewrite <- (add_gallina_fixed_eq_gallina _ _ _ _ _ _ _ _ _ _ _ _
                Hl1 Hl2 Hp1 Hp2 Hinv).
  apply (xyzt_add_body_decomposed_correct cp cpn ft P1 P2 dest rs1 rs2
           p1_bs p2_bs Hhon Hl1 Hl2 Ht1 Ht2 Htd Hni1 Hni2 Hb1 Hb2 Hexec).
Qed.

Print Assumptions add_gallina_fixed_eq_gallina.
Print Assumptions xyzt_add_body_decomposed_correct_orig_spec.
