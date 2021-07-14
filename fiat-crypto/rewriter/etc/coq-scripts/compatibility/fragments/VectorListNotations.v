(** Add Coq 8.4+8.5 notations, so that we don't accidentally make use of Coq 8.4-only notations *)
Require Coq.Lists.List.
Require Coq.Vectors.Vector.
Module Export LocalListNotations.
Notation " [ ] " := nil (format "[ ]") : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.
Notation " [ x ; y ; .. ; z ] " := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End LocalListNotations.
Module Export LocalVectorNotations.
Notation " [ ] " := (Vector.nil _) (format "[ ]") : vector_scope.
Notation " [ x ; .. ; y ] " := (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) ..) : vector_scope.
Notation " [ x ; y ; .. ; z ] " := (Vector.cons _ x _ (Vector.cons _ y _ .. (Vector.cons _ z _ (Vector.nil _)) ..)) : vector_scope.
End LocalVectorNotations.
