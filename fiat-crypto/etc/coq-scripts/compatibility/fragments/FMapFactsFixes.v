Module Export FSets.
Module FMapFacts.
Import Coq.FSets.FMapFacts.
Module WFacts_fun (E:DecidableType)(Import M:WSfun E).
  Notation option_map := option_map (compat "8.4").
  Module Coq_FSets_FMapFacts_WFacts_fun := Coq.FSets.FMapFacts.WFacts_fun E M.
  Include Coq_FSets_FMapFacts_WFacts_fun.
End WFacts_fun.
Module WFacts (M:WS) := WFacts_fun M.E M.
Module Facts := WFacts.
End FMapFacts.
End FSets.
