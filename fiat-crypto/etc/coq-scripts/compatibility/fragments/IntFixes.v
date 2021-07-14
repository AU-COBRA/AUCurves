Module Export ZArith.
  Module Int.
    Module Z_as_Int.
      Include Coq.ZArith.Int.Z_as_Int.
      Notation plus := Coq.ZArith.Int.Z_as_Int.add (only parsing).
      Notation minus := Coq.ZArith.Int.Z_as_Int.sub (only parsing).
      Notation mult := Coq.ZArith.Int.Z_as_Int.mul (only parsing).
    End Z_as_Int.
  End Int.
End ZArith.
