Require Coq.Program.Tactics.
Ltac rapply term := Coq.Program.Tactics.rapply term; shelve_unifiable.
