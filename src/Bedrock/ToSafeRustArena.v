(** * ToSafeRustArena — bedrock2 functions to safe Rust over an explicit memory.

    A direct, statement-for-statement printer from bedrock2 [Syntax.cmd]
    to Rust.  Unlike [Bedrock.ToSafeRustBody], which maps bedrock2
    pointers to Rust struct references and therefore only handles
    straight-line tower code, this printer keeps bedrock2's memory model:

      - every bedrock2 local is a Rust [u64] (bedrock2 has one type, the
        64-bit word), declared up front and initialised to 0;
      - memory is one value [m : &mut Mem] (a hand-written, safe runtime
        in the consuming crate: a bounds-checked word array addressed by
        bedrock2 byte addresses);
      - [expr.load]/[cmd.store] become [m.load*]/[m.store*];
      - [cmd.stackalloc x n body] becomes [x = m.alloc(n); body; m.free(n)];
      - [cmd.call binds f args] evaluates the arguments left to right into
        fresh temporaries, then calls the Rust function [f(m, ...)], which
        is either another printed bedrock2 function or a runtime leaf;
      - word operations follow coqutil's word semantics; the ones whose
        corner cases Rust does not match directly (shifts by >= 64,
        division by 0, signed comparison) go through runtime helpers
        [rt_sru], [rt_slu], [rt_srs], [rt_divu], [rt_remu], [rt_lts].

    So pointer arithmetic, loops and loads of runtime-length arrays (the
    Pippenger MSM) print as they are, and the emitted Rust contains no
    [unsafe]: a wrong address is a bounds-check panic, never undefined
    behaviour.

    The printer is a trusted pretty-printer, like [ToSafeRustBody] and
    bedrock2's own [ToCString]; nothing here is proved.  It is
    deliberately one clause per bedrock2 constructor so it can be read
    against [bedrock2.Semantics.exec].

    Unsupported constructs print as a compile error ([compile_error!]),
    never silently: [cmd.interact], and [expr.inlinetable] with an access
    size other than [word] or [one]. *)

From Stdlib Require Import String List ZArith Ascii.
Require Import bedrock2.Syntax.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(** List append; [++] is string append in this file. *)
Local Infix "+++" := List.app (right associativity, at level 60).

Module ToSafeRustArena.

Definition LF : string := String (Ascii.ascii_of_nat 10) EmptyString.

Fixpoint join (sep : string) (xs : list string) : string :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: r => x ++ sep ++ join sep r
  end.

(** Decimal printing of a natural / integer.  [Z] literals are printed
    reduced modulo 2^64, as [word.of_Z] does. *)
Fixpoint digits_aux (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | O => acc
  | S f =>
      let d := Z.modulo z 10 in
      let c := Ascii.ascii_of_nat (48 + Z.to_nat d) in
      let q := Z.div z 10 in
      if Z.eqb q 0 then String c acc else digits_aux f q (String c acc)
  end.

Definition z_dec (z : Z) : string := digits_aux 40 z "".

Definition word_lit (z : Z) : string :=
  z_dec (Z.modulo z (2 ^ 64)) ++ "u64".

(** Identifier escaping.  bedrock2 names are arbitrary strings; locals
    get the prefix [v_] (so no bedrock2 name can collide with a Rust
    keyword or with [m]), functions keep their name with every
    character outside [A-Za-z0-9_] replaced by [_]. *)
Definition ident_char (c : ascii) : ascii :=
  let n := Ascii.nat_of_ascii c in
  if (orb (andb (Nat.leb 48 n) (Nat.leb n 57))
     (orb (andb (Nat.leb 65 n) (Nat.leb n 90))
     (orb (andb (Nat.leb 97 n) (Nat.leb n 122)) (Nat.eqb n 95))))
  then c else "_"%char.

Fixpoint ident (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c r => String (ident_char c) (ident r)
  end.

Definition var (x : string) : string := "v_" ++ ident x.
Definition fn_name (f : string) : string := ident f.

Definition size_suffix (sz : access_size) : string :=
  match sz with
  | access_size.one => "8"
  | access_size.two => "16"
  | access_size.four => "32"
  | access_size.word => "64"
  end.

Definition bop (op : bopname) (a b : string) : string :=
  match op with
  | bopname.add => "(" ++ a ++ ").wrapping_add(" ++ b ++ ")"
  | bopname.sub => "(" ++ a ++ ").wrapping_sub(" ++ b ++ ")"
  | bopname.mul => "(" ++ a ++ ").wrapping_mul(" ++ b ++ ")"
  | bopname.mulhuu => "rt_mulhuu(" ++ a ++ ", " ++ b ++ ")"
  | bopname.divu => "rt_divu(" ++ a ++ ", " ++ b ++ ")"
  | bopname.remu => "rt_remu(" ++ a ++ ", " ++ b ++ ")"
  | bopname.and => "(" ++ a ++ " & " ++ b ++ ")"
  | bopname.or => "(" ++ a ++ " | " ++ b ++ ")"
  | bopname.xor => "(" ++ a ++ " ^ " ++ b ++ ")"
  | bopname.sru => "rt_sru(" ++ a ++ ", " ++ b ++ ")"
  | bopname.slu => "rt_slu(" ++ a ++ ", " ++ b ++ ")"
  | bopname.srs => "rt_srs(" ++ a ++ ", " ++ b ++ ")"
  | bopname.lts => "rt_lts(" ++ a ++ ", " ++ b ++ ")"
  | bopname.ltu => "((" ++ a ++ " < " ++ b ++ ") as u64)"
  | bopname.eq => "((" ++ a ++ " == " ++ b ++ ") as u64)"
  end.

Definition byte_lit (b : Byte.byte) : string :=
  z_dec (Z.of_nat (Byte.to_nat b)) ++ "u8".

Fixpoint expr (e : Syntax.expr) : string :=
  match e with
  | expr.literal z => word_lit z
  | expr.var x => var x
  | expr.load sz a => "m.load" ++ size_suffix sz ++ "(" ++ expr a ++ ")"
  | expr.inlinetable sz t i =>
      match sz with
      | access_size.one =>
          "rt_table8(&[" ++ join ", " (List.map byte_lit t) ++ "], " ++ expr i ++ ")"
      | access_size.word =>
          "rt_table64(&[" ++ join ", " (List.map byte_lit t) ++ "], " ++ expr i ++ ")"
      | _ => "compile_error!(""inlinetable access size"")"
      end
  | expr.op1 op1.not a => "(!(" ++ expr a ++ "))"
  | expr.op1 op1.opp a => "(" ++ expr a ++ ").wrapping_neg()"
  | expr.op op a b => bop op (expr a) (expr b)
  | expr.ite c a b =>
      "(if " ++ expr c ++ " != 0 { " ++ expr a ++ " } else { " ++ expr b ++ " })"
  end.

(** Statements, as a list of lines (each line already indented and
    without its newline): concatenating at the end keeps the
    string work linear under [vm_compute]. *)
Fixpoint arg_temps (k : nat) (ind : string) (es : list Syntax.expr)
  : list string * list string :=
  match es with
  | [] => ([], [])
  | e :: r =>
      let t := "a" ++ z_dec (Z.of_nat k) in
      let '(ls, ns) := arg_temps (S k) ind r in
      ((ind ++ "let " ++ t ++ ": u64 = " ++ expr e ++ ";") :: ls, t :: ns)
  end.

Fixpoint assign_rets (k : nat) (ind : string) (bs : list string) : list string :=
  match bs with
  | [] => []
  | b :: r =>
      (ind ++ var b ++ " = r[" ++ z_dec (Z.of_nat k) ++ "];")
        :: assign_rets (S k) ind r
  end.

Definition ind4 (ind : string) : string := "    " ++ ind.

Fixpoint cmd (ind : string) (c : Syntax.cmd) : list string :=
  match c with
  | cmd.skip => []
  | cmd.set x e => [ind ++ var x ++ " = " ++ expr e ++ ";"]
  | cmd.unset _ => []
  | cmd.store sz a v =>
      [ind ++ "{ let a: u64 = " ++ expr a ++ "; let v: u64 = " ++ expr v
           ++ "; m.store" ++ size_suffix sz ++ "(a, v); }"]
  | cmd.stackalloc x n body =>
      [ind ++ var x ++ " = m.alloc(" ++ z_dec n ++ ");"]
        +++ cmd ind body
        +++ [ind ++ "m.free(" ++ z_dec n ++ ");"]
  | cmd.cond t a b =>
      [ind ++ "if " ++ expr t ++ " != 0 {"]
        +++ cmd (ind4 ind) a
        +++ [ind ++ "} else {"]
        +++ cmd (ind4 ind) b
        +++ [ind ++ "}"]
  | cmd.seq a b => cmd ind a +++ cmd ind b
  | cmd.while t body =>
      [ind ++ "while " ++ expr t ++ " != 0 {"]
        +++ cmd (ind4 ind) body
        +++ [ind ++ "}"]
  | cmd.call bs f es =>
      let '(ls, ns) := arg_temps 0 (ind4 ind) es in
      let call := fn_name f ++ "(m" ++
                  String.concat "" (List.map (fun n => ", " ++ n) ns) ++ ")" in
      match bs with
      | [] => [ind ++ "{"] +++ ls +++ [ind4 ind ++ call ++ ";"; ind ++ "}"]
      | _ => [ind ++ "{"] +++ ls +++ [ind4 ind ++ "let r = " ++ call ++ ";"]
               +++ assign_rets 0 (ind4 ind) bs ++ [ind ++ "}"]
      end
  | cmd.interact _ _ _ => [ind ++ "compile_error!(""bedrock2 interact"");"]
  end.

(** Every local the body assigns, without duplicates, in first-use order. *)
Fixpoint cmd_vars (c : Syntax.cmd) : list string :=
  match c with
  | cmd.set x _ => [x]
  | cmd.stackalloc x _ b => x :: cmd_vars b
  | cmd.cond _ a b => cmd_vars a +++ cmd_vars b
  | cmd.seq a b => cmd_vars a +++ cmd_vars b
  | cmd.while _ b => cmd_vars b
  | cmd.call bs _ _ => bs
  | _ => []
  end.

Fixpoint dedup (seen : list string) (xs : list string) : list string :=
  match xs with
  | [] => []
  | x :: r =>
      if List.existsb (String.eqb x) seen then dedup seen r
      else x :: dedup (x :: seen) r
  end.

Definition function_t : Type :=
  (string * (list string * list string * Syntax.cmd))%type.

(** One Rust function per bedrock2 function: arguments are the bedrock2
    argument words, the result is the array of bedrock2 return words
    (omitted when there are none). *)
Definition rust_fn (f : function_t) : list string :=
  let '(name, (args, rets, body)) := f in
  let locals := dedup args (cmd_vars body +++ rets) in
  let params := String.concat ""
                  (List.map (fun a => ", mut " ++ var a ++ ": u64") args) in
  let ret_ty := match rets with
                | [] => ""
                | _ => " -> [u64; " ++ z_dec (Z.of_nat (List.length rets)) ++ "]"
                end in
  ["pub fn " ++ fn_name name ++ "(m: &mut Mem" ++ params ++ ")" ++ ret_ty ++ " {"]
    +++ List.map (fun x => "    let mut " ++ var x ++ ": u64 = 0;") locals
    +++ cmd "    " body
    +++ match rets with
       | [] => []
       | _ => ["    [" ++ join ", " (List.map var rets) ++ "]"]
       end
    +++ ["}"].

(** A module: a header (comment lines and [use] lines supplied by the
    caller), then the functions separated by blank lines. *)
Definition rust_module (header : list string) (fs : list function_t) : string :=
  String.concat LF
    (header +++ List.concat (List.map (fun f => "" :: rust_fn f) fs) ++ [""]).

End ToSafeRustArena.
