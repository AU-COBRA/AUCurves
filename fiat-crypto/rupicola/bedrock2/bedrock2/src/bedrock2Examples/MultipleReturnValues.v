Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry Coq.Lists.List.

Import BinInt String ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section MultipleReturnValues.
  Local Coercion literal (z : Z) : expr := expr.literal z.
  Local Coercion var (x : String.string) : expr := expr.var x.
  Local Coercion name_of_func (f : function) := fst f.

  Example addsub : func :=
    let a := "a" in let b := "b" in  let x := "x" in let y := "y" in
    ("addsub", ([a;b], [x;y], bedrock_func_body:(
    x = a + b;
    y = a - b
  ))).

  Example addsub_test : func :=
    let ret := "ret" in
    ("addsub_test", ([], [ret], bedrock_func_body:(
    unpack! ret, ret = addsub(coq:(14), coq:(7));
    ret = ret - coq:(7)
  ))).
End MultipleReturnValues.

Require Import bedrock2.ToCString.

Example addsub_c_string := Eval compute in c_func addsub.
Example addsub_test_c_string := Eval compute in c_func addsub_test.

(*
Print addsub_c_string.
Print addsub_test_c_string.
*)

(*
uintptr_t addsub(uintptr_t a, uintptr_t b, uintptr_t* _x) {
  uintptr_t x, y;
  x = (a)+(b);
  y = (a)-(b);
  *_x = x;
  return y;
}

uintptr_t addsub_test() {
  uintptr_t ret;
  ret = addsub(14ULL, 7ULL, &ret);
  ret = (ret)-(7ULL);
  return ret;
}
*)
