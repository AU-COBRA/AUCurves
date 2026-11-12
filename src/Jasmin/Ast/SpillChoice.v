(** * Spill hints from liveness (unverified heuristic: any choice js correct).

    As AUCurves' [Bedrock.Jasmin.SpillLiveness] for the [.jazz] printers: a register-pressure
    model of the spill pseudo-instructions ([Carry.wrap]: a spilled variable js unspilled before
    every group that reads it and spilled after every group that writes it, so it occupies a
    register only in those groups; any other variable occupies one from its first to its last
    occurrence), and a greedy choice: while some group needs more than [budget] registers,
    spill the variable live there, not used there, whose next occurrence js farthest
    (Belady). *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Stdlib Require Import String ZArith.
From Jasmin Require Import utils expr arch_extra x86_extra.
Require Import bedrock2.Syntax.
Require Import JasminBridge.Ast.Carry.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

Section S.
  Context {atoI : arch_toIdent}.
  Variable name : string -> Ident.ident.
  Variable cfn : Ident.ident.
  (** occurrences: variable -> increasing list of group indices *)
  Fixpoint add_occ (x : string) (i : Z) (occ : list (string * list Z)) : list (string * list Z) :=
    match occ with
    | [::] => [:: (x, [:: i])]
    | (y, js) :: occ' =>
        if String.eqb x y then (y, if js is j :: _ then (if Z.eqb j i then js else i :: js) else [:: i]) :: occ'
        else (y, js) :: add_occ x i occ'
    end.

  Fixpoint occs (i : Z) (gs : list (list string * list string)) (acc : list (string * list Z)) :=
    match gs with
    | [::] => acc
    | (rs, ws) :: gs => occs (Z.succ i) gs (foldl (fun a x => add_occ x i a) acc (rs ++ ws))
    end.

  Fixpoint lastz (d : Z) (l : list Z) : Z := match l with [::] => d | x :: l => lastz x l end.

  (** each entry: variable, first, last, occurrences (increasing) *)
  Definition intervals (ps : list string) (gs : list (list string * list string)) :=
    let occ := occs 1 gs (foldl (fun a x => add_occ x 0 a) [::] ps) in
    [seq let js := rev o.2 in (o.1, head 0%Z js, lastz 0%Z js, js) | o <- occ].

  Definition occupies (sp : list string) (iv : string * Z * Z * list Z) (i : Z) : bool :=
    let '(x, f, l, js) := iv in
    if has (String.eqb x) sp then has (Z.eqb i) js else (f <=? i) && (i <=? l).

  Definition pressure (sp : list string) (ivs : list (string * Z * Z * list Z)) (i : Z) : nat :=
    count (fun iv => occupies sp iv i) ivs.

  Fixpoint upto (i n : nat) : list Z := match n with O => [::] | S n => Z.of_nat i :: upto i.+1 n end.

  Definition maxpoint (sp : list string) ivs (pts : list Z) : Z * nat :=
    foldl (fun acc i => let p := pressure sp ivs i in if (acc.2 < p)%nat then (i, p) else acc) (0, 0%nat) pts.

  Definition next_after (i : Z) (js : list Z) : Z :=
    head 1000000%Z [seq j <- js | i <? j].

  Definition pick (sp : list string) (ivs : list (string * Z * Z * list Z)) (i : Z) : option string :=
    match foldl (fun acc iv =>
      let '(x, f, l, js) := iv in
      if ~~ has (String.eqb x) sp && (f <=? i) && (i <=? l) && ~~ has (Z.eqb i) js then
        match acc with
        | Some (y, ny) => let nx := next_after i js in if ny <? nx then Some (x, nx) else acc
        | None => Some (x, next_after i js)
        end
      else acc) None ivs with Some (x, _) => Some x | None => None end.

  Fixpoint choose (fuel : nat) (budget : nat) ivs (pts : list Z) (sp : list string) : list string :=
    match fuel with
    | O => sp
    | S fuel =>
        let '(i, p) := maxpoint sp ivs pts in
        if (p <= budget)%nat then sp
        else match pick sp ivs i with
             | Some x => choose fuel budget ivs pts (x :: sp)
             | None => sp
             end
    end.

  Definition spill_live (budget : nat) (ps : list string) (b : cmd) : string -> bool :=
    let gs := cmd_groups name cfn ps b in
    let ivs := intervals ps gs in
    let sp := choose (size ivs) budget ivs (upto 0 (size gs).+1) [::] in
    fun x => has (String.eqb x) sp.
End S.
