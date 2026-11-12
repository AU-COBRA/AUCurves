(** * Carry arithmetic: fiat's word-level carries against Jasmin's [waddcarry]/[wsubcarry],
    and the functional semantics of flattened bedrock2 bodies. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Jasmin Require Import utils wsize word.
From Stdlib Require Import ZArith Lia String.
Require coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require coqutil.Map.Interface coqutil.Map.Properties coqutil.Decidable.
Require bedrock2.Syntax bedrock2.Semantics.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Carry.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.
Import bedrock2.Syntax.
Module map := coqutil.Map.Interface.map.

Section A.
  Context {W : coqutil.Word.Interface.word.word 64} {W_ok : coqutil.Word.Interface.word.ok W}.
  Local Notation w64 := (@CW.rep 64 W).

  Definition b2w (b : bool) : w64 := if b then CW.of_Z 1 else CW.of_Z 0.
  Definition ltw (a b : w64) : w64 := if CW.ltu a b then CW.of_Z 1 else CW.of_Z 0.

  Lemma M64 : 2 ^ 64 = 18446744073709551616. Proof. reflexivity. Qed.

  Lemma uns (a : w64) : 0 <= CW.unsigned a < 2 ^ 64.
  Proof. exact: CWP.unsigned_range. Qed.

  Lemma u_of_Z_small z : 0 <= z < 2 ^ 64 -> CW.unsigned (CW.of_Z (word:=W) z) = z.
  Proof. move=> h; rewrite CW.unsigned_of_Z /CW.wrap Z.mod_small //. Qed.

  Lemma u_b2w b : CW.unsigned (b2w b) = Z.b2z b.
  Proof. by case: b; rewrite /b2w u_of_Z_small //; rewrite M64; lia. Qed.

  Lemma u_ltw a b : CW.unsigned (ltw a b) = Z.b2z (CW.unsigned a <? CW.unsigned b).
  Proof. by rewrite /ltw CW.unsigned_ltu; case: Z.ltb; rewrite u_of_Z_small //; rewrite M64; lia. Qed.

  Lemma wrap_cases z : 0 <= z < 2 * 2 ^ 64 ->
    CW.wrap (width:=64) z = if z <? 2 ^ 64 then z else z - 2 ^ 64.
  Proof.
    move=> h; rewrite /CW.wrap; case: Z.ltb_spec => hz.
    - by rewrite Z.mod_small //; lia.
    - have -> : z = (z - 2 ^ 64) + 1 * 2 ^ 64 by lia.
      rewrite Z.mod_add; last lia.
      rewrite Z.mod_small; lia.
  Qed.

  Lemma wrap_sub_cases z : - 2 ^ 64 <= z < 2 ^ 64 ->
    CW.wrap (width:=64) z = if z <? 0 then z + 2 ^ 64 else z.
  Proof.
    move=> h; rewrite /CW.wrap; case: Z.ltb_spec => hz.
    - have -> : z = (z + 2 ^ 64) + (-1) * 2 ^ 64 by lia.
      rewrite Z.mod_add; last lia.
      rewrite Z.mod_small; lia.
    - by rewrite Z.mod_small //; lia.
  Qed.

  Lemma uinj (x y : w64) : CW.unsigned x = CW.unsigned y -> x = y.
  Proof. exact: CWP.unsigned_inj. Qed.

  Lemma Zb2z_01 (c : bool) : 0 <= Z.b2z c <= 1. Proof. by case: c; simpl; lia. Qed.
  Lemma b2z_cases (c : bool) : Z.b2z c = 0 \/ Z.b2z c = 1. Proof. by case: c; [right | left]. Qed.

  Lemma jw_unsigned (x : w64) z : CW.unsigned x = z -> jw x = wrepr U64 z.
  Proof. by move=> <-. Qed.

  Ltac zcases :=
    repeat match goal with
    | |- context [Z.ltb ?x ?y] => case: (Z.ltb_spec x y)
    | |- context [Z.leb ?x ?y] => case: (Z.leb_spec x y)
    | h : context [Z.ltb ?x ?y] |- _ => move: h; case: (Z.ltb_spec x y)
    end; intros; try lia.

  Lemma add_small (x y : w64) : CW.unsigned x + CW.unsigned y < 2 ^ 64 ->
    CW.unsigned (CW.add x y) = CW.unsigned x + CW.unsigned y.
  Proof. move=> h; rewrite CW.unsigned_add /CW.wrap Z.mod_small //; have := uns x; have := uns y; lia. Qed.

  Lemma jw_b2w c : jw (b2w c) = wrepr U64 (Z.b2z c).
  Proof. by rewrite /jw u_b2w. Qed.

  (** addcarryx: [s = c + a; r = s + b], carry [s <u a + r <u b]. *)
  Lemma addcarry2 (a b : w64) (c : bool) :
    let s := CW.add (b2w c) a in let r := CW.add s b in
    jw r = (waddcarry (jw a) (jw b) c).2 /\
    CW.add (ltw s a) (ltw r b) = b2w (waddcarry (jw a) (jw b) c).1.
  Proof.
    move=> s r; rewrite /waddcarry /= !wunsigned_jw wbase64.
    have [ha hb] := (uns a, uns b).
    have hs : CW.unsigned s = CW.wrap (Z.b2z c + CW.unsigned a) by rewrite /s CW.unsigned_add u_b2w.
    have hr : CW.unsigned r = CW.wrap (CW.unsigned s + CW.unsigned b) by rewrite /r CW.unsigned_add.
    rewrite wrap_cases in hs; last by have := Zb2z_01 c; lia.
    rewrite wrap_cases in hr; last by have := uns s; lia.
    split.
    - rewrite /r /s !jw_add jw_b2w /jw -!wrepr_add; congr wrepr; lia.
    - apply: uinj.
      have hc := b2z_cases c.
      rewrite add_small !u_ltw; last by case: Z.ltb; case: Z.ltb; simpl; rewrite ?M64; lia.
      rewrite /b2w; move: hs hr; zcases.
      all: rewrite ?u_of_Z_small /=; try (rewrite ?M64; lia).
  Qed.

  (** subborrowx: [s = a - b; r = s - c], borrow [a <u s + s <u r]. *)
  Lemma subborrow2 (a b : w64) (c : bool) :
    let s := CW.sub a b in let r := CW.sub s (b2w c) in
    jw r = (wsubcarry (jw a) (jw b) c).2 /\
    CW.add (ltw a s) (ltw s r) = b2w (wsubcarry (jw a) (jw b) c).1.
  Proof.
    move=> s r; rewrite /wsubcarry /= !wunsigned_jw.
    have [ha hb] := (uns a, uns b).
    have hs : CW.unsigned s = CW.wrap (CW.unsigned a - CW.unsigned b) by rewrite /s CW.unsigned_sub.
    have hr : CW.unsigned r = CW.wrap (CW.unsigned s - Z.b2z c) by rewrite /r CW.unsigned_sub u_b2w.
    rewrite wrap_sub_cases in hs; last lia.
    rewrite wrap_sub_cases in hr; last by have := uns s; have := Zb2z_01 c; lia.
    split.
    - rewrite /r /s !jw_sub jw_b2w /jw -!wrepr_sub; congr wrepr; lia.
    - apply: uinj.
      have hc := b2z_cases c.
      rewrite add_small !u_ltw; last by case: Z.ltb; case: Z.ltb; simpl; rewrite ?M64; lia.
      rewrite /b2w; move: hs hr; zcases.
      all: rewrite ?u_of_Z_small /=; try (rewrite ?M64; lia).
  Qed.

  (** one-word forms: [r = c + a] (carry [r <u a]) and [r = a - c] (borrow [a <u r]) *)
  Lemma addcarry1 (a : w64) (c : bool) :
    let r := CW.add (b2w c) a in
    jw r = (waddcarry (jw a) (wrepr U64 0) c).2 /\ ltw r a = b2w (waddcarry (jw a) (wrepr U64 0) c).1.
  Proof.
    move=> r; rewrite /waddcarry /= wunsigned_jw wrepr0 wunsigned0 wbase64.
    have ha := uns a.
    have hr : CW.unsigned r = CW.wrap (Z.b2z c + CW.unsigned a) by rewrite /r CW.unsigned_add u_b2w.
    rewrite wrap_cases in hr; last by have := Zb2z_01 c; lia.
    split.
    - rewrite /r jw_add jw_b2w /jw -wrepr_add; congr wrepr; lia.
    - apply: uinj; rewrite u_ltw /b2w.
      have hc := b2z_cases c.
      move: hr; zcases.
      all: rewrite ?u_of_Z_small /=; try (rewrite ?M64; lia).
  Qed.

  Lemma subborrow1 (a : w64) (c : bool) :
    let r := CW.sub a (b2w c) in
    jw r = (wsubcarry (jw a) (wrepr U64 0) c).2 /\ ltw a r = b2w (wsubcarry (jw a) (wrepr U64 0) c).1.
  Proof.
    move=> r; rewrite /wsubcarry /= wunsigned_jw wrepr0 wunsigned0.
    have ha := uns a.
    have hr : CW.unsigned r = CW.wrap (CW.unsigned a - Z.b2z c) by rewrite /r CW.unsigned_sub u_b2w.
    rewrite wrap_sub_cases in hr; last by have := Zb2z_01 c; lia.
    split.
    - rewrite /r jw_sub jw_b2w /jw -wrepr_sub; congr wrepr; lia.
    - apply: uinj; rewrite u_ltw /b2w.
      have hc := b2z_cases c.
      move: hr; zcases.
      all: rewrite ?u_of_Z_small /=; try (rewrite ?M64; lia).
  Qed.

  (** first word: [r = a + b] (carry [r <u a]) and [r = a - b] (borrow [a <u r]) *)
  Lemma addcarry0 (a b : w64) :
    let r := CW.add a b in
    jw r = (waddcarry (jw a) (jw b) false).2 /\ ltw r a = b2w (waddcarry (jw a) (jw b) false).1.
  Proof.
    move=> r; rewrite /waddcarry /= !wunsigned_jw wbase64.
    have [ha hb] := (uns a, uns b).
    have hr : CW.unsigned r = CW.wrap (CW.unsigned a + CW.unsigned b) by rewrite /r CW.unsigned_add.
    rewrite wrap_cases in hr; last lia.
    split.
    - rewrite /r jw_add /jw -wrepr_add; congr wrepr; lia.
    - apply: uinj; rewrite u_ltw /b2w.
      move: hr; zcases.
      all: rewrite ?u_of_Z_small /=; try (rewrite ?M64; lia).
  Qed.

  Lemma subborrow0 (a b : w64) :
    let r := CW.sub a b in
    jw r = (wsubcarry (jw a) (jw b) false).2 /\ ltw a r = b2w (wsubcarry (jw a) (jw b) false).1.
  Proof.
    move=> r; rewrite /wsubcarry /= !wunsigned_jw.
    have [ha hb] := (uns a, uns b).
    have hr : CW.unsigned r = CW.wrap (CW.unsigned a - CW.unsigned b) by rewrite /r CW.unsigned_sub.
    rewrite wrap_sub_cases in hr; last lia.
    split.
    - rewrite /r jw_sub /jw -wrepr_sub; congr wrepr; lia.
    - apply: uinj; rewrite u_ltw /b2w.
      move: hr; zcases.
      all: rewrite ?u_of_Z_small /=; try (rewrite ?M64; lia).
  Qed.

  (** [a <u (a - c)] is the borrow of [a - c]. *)
  Lemma subborrow_ltw (a : w64) (c : bool) :
    ltw a (CW.sub a (b2w c)) = b2w (wsubcarry (jw a) (wrepr U64 0) c).1.
  Proof. by have [_ ->] := subborrow1 a c. Qed.

  (** fiat's mask [-1 + (c == 0)] is [- c]. *)
  Lemma eqb10 : CW.eqb (word:=W) (CW.of_Z 1) (CW.of_Z 0) = false.
  Proof. by rewrite CW.unsigned_eqb !u_of_Z_small //; rewrite M64; lia. Qed.
  Lemma eqb00 : CW.eqb (word:=W) (CW.of_Z 0) (CW.of_Z 0) = true.
  Proof. by rewrite CW.unsigned_eqb Z.eqb_refl. Qed.

  Lemma mask_b2w (c : bool) :
    CW.add (CW.opp (CW.of_Z 1)) (if CW.eqb (b2w c) (CW.of_Z 0) then CW.of_Z 1 else CW.of_Z 0)
    = CW.opp (b2w c).
  Proof.
    apply: uinj; case: c; rewrite /b2w ?eqb10 ?eqb00 CW.unsigned_add !CW.unsigned_opp !u_of_Z_small;
      try (rewrite M64; lia).
    all: rewrite /CW.wrap; reflexivity.
  Qed.

  Lemma jw_mask (c : bool) : jw (CW.opp (b2w c)) = (wsubcarry (wrepr U64 0) (wrepr U64 0) c).2.
  Proof. by rewrite jw_opp jw_b2w; case: c; apply/eqP; vm_compute. Qed.

  (** fiat's select [(a & m) | (b & ~m)] with [m = -1 + (c == 0)]. *)
  Lemma ones64 : 2 ^ 64 - 1 = Z.ones 64. Proof. reflexivity. Qed.

  Lemma select_b2w (c : bool) (a b : w64) :
    let m := CW.add (CW.opp (CW.of_Z 1)) (if CW.eqb (b2w c) (CW.of_Z 0) then CW.of_Z 1 else CW.of_Z 0) in
    CW.or (CW.and a m) (CW.and b (CW.xor m (CW.of_Z (2 ^ 64 - 1)))) = if c then a else b.
  Proof.
    rewrite /= mask_b2w; apply: uinj.
    have [h0 h1] := uns a; have [h2 h3] := uns b.
    rewrite CWP.unsigned_or_nowrap !CWP.unsigned_and_nowrap CWP.unsigned_xor_nowrap CW.unsigned_opp.
    rewrite (u_of_Z_small (2 ^ 64 - 1)); last by rewrite M64; lia.
    case: c; rewrite /b2w ?u_of_Z_small; try (rewrite M64; lia).
    - have -> : CW.wrap (width:=64) (- 1) = Z.ones 64 by reflexivity.
      rewrite ones64 Z.lxor_nilpotent Z.land_0_r Z.lor_0_r Z.land_ones; last lia.
      by rewrite Z.mod_small.
    - have -> : CW.wrap (width:=64) (- 0) = 0 by reflexivity.
      rewrite Z.land_0_r Z.lor_0_l Z.lxor_0_l ones64 Z.land_ones; last lia.
      by rewrite Z.mod_small.
  Qed.
End A.
