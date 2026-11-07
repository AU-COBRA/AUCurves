(** * BN446ParamsCheck: the curve data of [bn446_params], checked by computation.

    [bn446_params] (Curves/BN446_params.v): seed u = 2^110 + 2^36 + 1, p and r the BN
    polynomials at u, E : y^2 = x^3 + 257, Fp2 = Fp[u]/(u^2+1), xi = 1 + 9u, D-twist
    E' : y^2 = x^3 + 257/xi.  Each lemma below is one kernel-checked computation:

      - [bn446_chk_seed]: p, r, |6u+2|, a, b, beta, xi and the twist kind of the record;
      - [bn446_g1_on_curve], [bn446_g1_order_r]: G1 = (-1, 16) lies on E and
        [r-1] G1 = -G1, i.e. [r] G1 = O with G1 <> O;
      - [bn446_g2_on_twist], [bn446_g2_order_r]: G2 below lies on E' (as xi y^2 = xi x^3 + 257)
        and [r-1] G2 = -G2;  [bn446_g2_mul_control]: [3] G2 <> -G2 (the test can fail).

    BN446FrobCheck.v checks the FrobConstants gammas and that xi is neither a square nor a
    cube in Fp2; BN446TwistCheck.v checks that the gammas give the Frobenius of this twist
    (psi(G2) = [p] G2).  The literal gamma values are defined here.

    r is a probable prime (Miller-Rabin, scripts/bn446/params_check.py);
    AUCurves has no Rocq primality certificate for r, so here "[r] G = O, G <> O" says that
    the order of G is a divisor of r other than 1.

    The scalar multiplications use Jacobian formulas (a = 0: dbl-2009-l, madd-2007-bl) over
    ZModTower's Fp and Fp2 arithmetic on [Z].  They are a computation, not a proof of the
    group law; the inputs avoid the degenerate cases (the multiples k G to which G is added
    have 2 <= k + 1 < r - 1, and E[r] has no 2-torsion).  The two 446-bit scalar
    multiplications are checked by the kernel's native conversion ([native_cast_no_check];
    about 22 s for G1 and 84 s for G2). *)

From Stdlib Require Import ZArith.ZArith.

Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.Curves.BN446_params.

Local Open Scope Z_scope.

Definition bn446_chk_p : Z := prime_p bn446_params.
Definition bn446_chk_r : Z := scalar_r bn446_params.
Definition bn446_chk_xi : Fp2_Z := (xi_re bn446_params, xi_im bn446_params).

(** ** Jacobian double-and-add over any field given by its operations (a = 0). *)
Section Jacobian.
  Context {F : Type} (add sub mul : F -> F -> F) (one : F).

  Definition jdbl (P : F * F * F) : F * F * F :=
    let '(X1, Y1, Z1) := P in
    let A := mul X1 X1 in
    let B := mul Y1 Y1 in
    let C := mul B B in
    let t := add X1 B in
    let d := sub (sub (mul t t) A) C in
    let D := add d d in
    let E := add (add A A) A in
    let X3 := sub (mul E E) (add D D) in
    let c2 := add C C in let c4 := add c2 c2 in let c8 := add c4 c4 in
    let Y3 := sub (mul E (sub D X3)) c8 in
    let yz := mul Y1 Z1 in
    (X3, Y3, add yz yz).

  Definition jmadd (P : F * F * F) (x2 y2 : F) : F * F * F :=
    let '(X1, Y1, Z1) := P in
    let Z1Z1 := mul Z1 Z1 in
    let U2 := mul x2 Z1Z1 in
    let S2 := mul y2 (mul Z1 Z1Z1) in
    let H := sub U2 X1 in
    let HH := mul H H in
    let h2 := add HH HH in let I := add h2 h2 in
    let J := mul H I in
    let s := sub S2 Y1 in let rr := add s s in
    let V := mul X1 I in
    let X3 := sub (sub (mul rr rr) J) (add V V) in
    let yj := mul Y1 J in
    let Y3 := sub (mul rr (sub V X3)) (add yj yj) in
    let zh := add Z1 H in
    (X3, Y3, sub (sub (mul zh zh) Z1Z1) HH).

  (** [jmul x y k] = [k] (x, y), most significant bit first. *)
  Fixpoint jmul (x y : F) (k : positive) : F * F * F :=
    match k with
    | xH => (x, y, one)
    | xO k' => jdbl (jmul x y k')
    | xI k' => jmadd (jdbl (jmul x y k')) x y
    end.

  (** The Jacobian point (X, Y, Z) with Z <> 0 is the affine point (x, y). *)
  Definition jeq (zero : F) (eqb : F -> F -> bool) (P : F * F * F) (x y : F) : bool :=
    let '(X, Y, Z) := P in
    let ZZ := mul Z Z in
    (negb (eqb Z zero) && eqb X (mul x ZZ) && eqb Y (mul y (mul Z ZZ)))%bool.
End Jacobian.

(** ** [k] (x, y) = (x', y') on E(Fp), resp. E'(Fp2) (u^2 = -1), as a boolean *)

Definition fp2_eqb (a b : Fp2_Z) : bool := ((fst a =? fst b) && (snd a =? snd b))%bool.

Definition g1_mul_is (x y : Z) (k : Z) (x' y' : Z) : bool :=
  jeq (zfp_mul bn446_chk_p) 0 Z.eqb
    (jmul (zfp_add bn446_chk_p) (zfp_sub bn446_chk_p) (zfp_mul bn446_chk_p) 1 x y (Z.to_pos k))
    x' y'.
Definition g2_mul_is (x y : Fp2_Z) (k : Z) (x' y' : Fp2_Z) : bool :=
  jeq (zfp2_mul bn446_chk_p) (0, 0) fp2_eqb
    (jmul (zfp2_add bn446_chk_p) (zfp2_sub bn446_chk_p) (zfp2_mul bn446_chk_p) (1, 0)
       x y (Z.to_pos k))
    x' y'.

(** ** The parameters *)

Lemma bn446_chk_seed :
  bn446_chk_p = 36 * (2^110 + 2^36 + 1)^4 + 36 * (2^110 + 2^36 + 1)^3
                + 24 * (2^110 + 2^36 + 1)^2 + 6 * (2^110 + 2^36 + 1) + 1 /\
  bn446_chk_r = 36 * (2^110 + 2^36 + 1)^4 + 36 * (2^110 + 2^36 + 1)^3
                + 18 * (2^110 + 2^36 + 1)^2 + 6 * (2^110 + 2^36 + 1) + 1 /\
  loop_abs bn446_params = 6 * (2^110 + 2^36 + 1) + 2 /\ loop_neg bn446_params = false /\
  curve_a bn446_params = 0 /\ curve_b bn446_params = 257 /\
  fp2_beta bn446_params = -1 /\ bn446_chk_xi = (1, 9) /\ twist bn446_params = Dtwist.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** G1 = (-1, 16) *)

Definition bn446_g1_x : Z := bn446_chk_p - 1.
Definition bn446_g1_y : Z := 16.

Lemma bn446_g1_on_curve :
  zfp_mul bn446_chk_p bn446_g1_y bn446_g1_y
  = zfp_add bn446_chk_p
      (zfp_mul bn446_chk_p bn446_g1_x (zfp_mul bn446_chk_p bn446_g1_x bn446_g1_x))
      (curve_b bn446_params).
Proof. vm_compute. reflexivity. Qed.

(** [r-1] G1 = -G1, hence [r] G1 = O. *)
Lemma bn446_g1_order_r :
  g1_mul_is bn446_g1_x bn446_g1_y (bn446_chk_r - 1) bn446_g1_x (zfp_neg bn446_chk_p bn446_g1_y)
  = true.
Proof. native_cast_no_check (eq_refl true). Qed.

(** ** G2 on the D-twist y^2 = x^3 + 257/xi
    (from params_check.py: the first x = k + u, k = 1, 2, ..., with x^3 + 257/xi a square in
    Fp2, times the cofactor 2p - r) *)

Definition bn446_g2_x : Fp2_Z :=
  (82911037241206280655704079970105836742771347846629953036131733198260114277930523665647897604308699198422490064790488203675996357601122,
   59174831877271502507360271110772145476220564183525006573420611307673594547994093941088085299774219227728941115079022029737027953637869).
Definition bn446_g2_y : Fp2_Z :=
  (101740047366358746995720822855336202520934966009962008574102766449180161037184083825596429879691953863334233950284282291711146734047144,
   70014261043671511237618751548779351874104258998178231175276234711972058766137367031307941737720013151213413835576148402777888831719641).

(** On the twist, multiplied through by xi: xi y^2 = xi x^3 + 257. *)
Lemma bn446_g2_on_twist :
  zfp2_mul bn446_chk_p bn446_chk_xi (zfp2_mul bn446_chk_p bn446_g2_y bn446_g2_y)
  = zfp2_add bn446_chk_p
      (zfp2_mul bn446_chk_p bn446_chk_xi
         (zfp2_mul bn446_chk_p bn446_g2_x (zfp2_mul bn446_chk_p bn446_g2_x bn446_g2_x)))
      (curve_b bn446_params, 0).
Proof. vm_compute. reflexivity. Qed.

(** [r-1] G2 = -G2, hence [r] G2 = O. *)
Lemma bn446_g2_order_r :
  g2_mul_is bn446_g2_x bn446_g2_y (bn446_chk_r - 1) bn446_g2_x (zfp2_neg bn446_chk_p bn446_g2_y)
  = true.
Proof. native_cast_no_check (eq_refl true). Qed.

(** Control: the test can fail; [3] G2 <> -G2. *)
Lemma bn446_g2_mul_control :
  g2_mul_is bn446_g2_x bn446_g2_y 3 bn446_g2_x (zfp2_neg bn446_chk_p bn446_g2_y) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The Frobenius constants, as literals (BN446FrobCheck.v: = FrobConstants at [bn446_params]) *)

Definition bn446_gamma1_lit : Fp2_Z :=
  (69419342512250743188586778123456642835272075410629227187347716783683605682075608606947078707821061174729037384674500337315756151199311,
   40936526513231153730907443617299810434904596907333813796840519203813069956546682475306112588951396374991161978987481875956436777225350).
Definition bn446_gamma2_lit : Fp2_Z :=
  (24742296868757182588038128182208961567180513030185943648687121601555825556665693567655107714264733683223921584333535935892168805419010,
   79083637487813587062059485811549287690882073520005226137821212797968392202171617502193586994754895635748333142027709288054499610486772).
Definition bn446_w_frob_c1_lit : Fp2_Z :=
  (67174616516197365609159982754940470457545461324931387635503936106706701393639976871963056349736276017914131421989849780155626144843278,
   44277646944902070042984952300556888693937520070394783206963684426059265490384140114216558653108947130405964091387345029205611510402587).
Definition bn446_gamma1_p2_lit : Fp2_Z :=
  (102211695604069718983520304652693835625126462366514966190987237263671765711603564810480238817169377321276281862275597492335222372433976, 0).
Definition bn446_gamma2_p2_lit : Fp2_Z :=
  (39370513046094214638711292860936120970669925098166405844133061722780077418403084822103936090966589486, 0).
Definition bn446_w_frob_p2_c1_lit : Fp2_Z :=
  (102211695604069718983520304652693835625126462366514966190987237263671765711603564810480238817169377321276281862275597492335222372433977, 0).
Definition bn446_gamma_y_lit : Fp2_Z :=
  (62929740315363061021464516066763340648466452263640589674402657104455048972159168899212936998137110743961476607707164211550089129741897,
   41062758569730246441336158891649440626153886405092156042360327967092584235193906425541242872092267894224730822643158111151558794090254).
