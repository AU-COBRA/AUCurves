Ltac letexists_ v :=
  hnf; (* NOTE: jgross says hnf is fragile but idk how else to get ?P *)
  lazymatch goal with
  | |- exists x, ?P =>
    let x' := fresh x in
    refine (let x' := v in ex_intro (fun x => P) x' _)
  end.
Tactic Notation "letexists" open_constr(v) :=
  letexists_ v.
Tactic Notation "letexists" :=
  letexists _.

Ltac letexists_as v x' :=
  hnf; (* NOTE: jgross says hnf is fragile but idk how else to get ?P *)
  lazymatch goal with
  | |- exists x, ?P =>
    refine (let x' := v in ex_intro (fun x => P) x' _)
  end.

Tactic Notation "letexists" open_constr(v) "as" ident(x) :=
  letexists_as v x.