(** * Hash-to-Curve specification for BLS12-381 G1.

    Implements the Simplified SWU (Shallue-Woestijne-Ulas) map
    from RFC 9380 section 6.6.2, the 11-isogeny from E' to E
    (Appendix E.2), and the full hash_to_curve pipeline
    (section 3).

    BLS12-381 G1 uses an isogenous curve E': y^2 = x^3 + A'*x + B'
    with Simplified SWU (Z = 11), then maps back to E: y^2 = x^3 + 4
    via an 11-isogeny.

    References:
    - RFC 9380: Hashing to Elliptic Curves
    - Suite: BLS12381G1_XMD:SHA-256_SSWU_RO_
*)

From Stdlib Require Import ZArith BinPos List Bool.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.SHA256_axiom.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * BLS12-381 field prime                                            *)
(* ================================================================== *)

(** The BLS12-381 base field prime p. *)
Definition p : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition p_pos : positive :=
  Eval vm_compute in (Z.to_pos p).

Lemma p_val : Z.pos p_pos = p.
Proof. vm_compute. reflexivity. Qed.

(** Field type and notations. *)
Local Notation Fp := (F p_pos).
Local Notation "x +f y" := (@F.add p_pos x y) (at level 50, left associativity).
Local Notation "x *f y" := (@F.mul p_pos x y) (at level 40, left associativity).
Local Notation "x -f y" := (@F.sub p_pos x y) (at level 50, left associativity).
Local Notation "-f x" := (@F.opp p_pos x) (at level 35, right associativity).
Local Notation "0f" := (@F.zero p_pos).
Local Notation "1f" := (@F.one p_pos).
Local Notation inv := (@F.inv p_pos).
Local Notation of_Z := (F.of_Z p_pos).

(** Boolean equality on Fp: compares the canonical Z representatives. *)
Definition fp_eqb (x y : Fp) : bool :=
  BinInt.Z.eqb (F.to_Z x) (F.to_Z y).

(** Helper: square an element. *)
Definition sqr (x : Fp) : Fp := x *f x.

(** Helper: cube an element. *)
Definition cube (x : Fp) : Fp := x *f x *f x.

(* ================================================================== *)
(** * sgn0: sign of a field element (RFC 9380 section 4.1)             *)
(* ================================================================== *)

(** For GF(p) with m = 1, sgn0(x) = x mod 2.
    This extracts the parity bit: 0 for even, 1 for odd. *)
Definition sgn0 (x : Fp) : Z :=
  F.to_Z x mod 2.

(* ================================================================== *)
(** * Simplified SWU map (RFC 9380 section 6.6.2)                      *)
(* ================================================================== *)

(** The Simplified SWU map for a curve y^2 = x^3 + A*x + B.
    Precondition: A <> 0 and B <> 0.

    Input: u in Fp (a hash output)
    Output: (x, y) on the curve y^2 = x^3 + A*x + B

    The map uses a distinguished nonsquare Z in Fp. *)

Section SimplifiedSWU.
  Variable swu_a : Fp.   (** Curve coefficient A (must be nonzero). *)
  Variable swu_b : Fp.   (** Curve coefficient B (must be nonzero). *)
  Variable swu_z : Fp.   (** SWU constant (a nonsquare in Fp). *)

  (** is_square: true when x is a quadratic residue in Fp.
      We define this via the Euler criterion: x^((p-1)/2) = 1.
      NOTE: not using `Eval vm_compute` here — the kernel would otherwise
      have to traverse a 380-bit literal during conversion-checking, making
      Qed verification of dependent lemmas pathologically slow. *)
  Definition legendre_exp : BinInt.Z := ((p - 1) / 2)%Z.

  Definition is_square (x : Fp) : bool :=
    let e := F.pow x (BinInt.Z.to_N legendre_exp) in
    if fp_eqb e 1f then true
    else if fp_eqb x 0f then true   (* 0 is a square *)
    else false.

  (** Square root via x^((p+1)/4), valid since p = 3 (mod 4). *)
  Definition sqrt_exp : BinInt.Z := ((p + 1) / 4)%Z.

  Definition fp_sqrt (x : Fp) : Fp :=
    F.pow x (BinInt.Z.to_N sqrt_exp).

  (** Evaluate the curve equation RHS: x^3 + A*x + B. *)
  Definition curve_rhs (x : Fp) : Fp :=
    cube x +f swu_a *f x +f swu_b.

  (** The Simplified SWU map.

      From RFC 9380 section 6.6.2:

      1.  tv1 = inv0(Z^2 * u^4 + Z * u^2)
      2.  x1  = (-B / A) * (1 + tv1)
      3.  If tv1 == 0, set x1 = B / (Z * A)
      4.  gx1 = x1^3 + A * x1 + B
      5.  x2  = Z * u^2 * x1
      6.  gx2 = x2^3 + A * x2 + B
      7.  If is_square(gx1), set x = x1 and y = sqrt(gx1)
      8.  Else set x = x2 and y = sqrt(gx2)
      9.  If sgn0(u) != sgn0(y), set y = -y
      10. Return (x, y)

      Note: inv0 is the field inverse that returns 0 for 0.
      F.inv already satisfies inv(0) = 0 by inv_with_spec. *)
  Definition map_to_curve_simple_swu (u : Fp) : Fp * Fp :=
    let u2 := sqr u in
    let u4 := sqr u2 in
    let z2 := sqr swu_z in
    (* Step 1: tv1 = inv0(Z^2 * u^4 + Z * u^2) *)
    let tv1 := inv (z2 *f u4 +f swu_z *f u2) in
    (* Step 2: x1 = (-B / A) * (1 + tv1) *)
    let neg_B_over_A := (-f swu_b) *f inv swu_a in
    let x1_normal := neg_B_over_A *f (1f +f tv1) in
    (* Step 3: if tv1 == 0 then x1 = B / (Z * A) *)
    let x1 :=
      if fp_eqb tv1 0f
      then swu_b *f inv (swu_z *f swu_a)
      else x1_normal in
    (* Step 4: gx1 = x1^3 + A * x1 + B *)
    let gx1 := curve_rhs x1 in
    (* Step 5: x2 = Z * u^2 * x1 *)
    let x2 := swu_z *f u2 *f x1 in
    (* Step 6: gx2 = x2^3 + A * x2 + B *)
    let gx2 := curve_rhs x2 in
    (* Steps 7-8: choose (x, y) based on which gx is a square *)
    let '(x, y) :=
      if is_square gx1
      then (x1, fp_sqrt gx1)
      else (x2, fp_sqrt gx2) in
    (* Step 9: fix sign of y *)
    let y_final :=
      if BinInt.Z.eqb (sgn0 u) (sgn0 y)
      then y
      else -f y in
    (* Step 10 *)
    (x, y_final).

End SimplifiedSWU.

(* ================================================================== *)
(** * BLS12-381 G1 isogenous curve E' and SWU constants                *)
(* ================================================================== *)

(** The target curve E: y^2 = x^3 + 4 has A = 0, so Simplified SWU
    cannot be applied directly. RFC 9380 section 8.8.1 uses the
    isogenous curve E': y^2 = x^3 + A'*x + B' with an 11-isogeny
    phi: E' -> E.

    Constants from RFC 9380 section 8.8.1 and Appendix E.2. *)

Definition iso_A : Fp := of_Z
  0x144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1d.

Definition iso_B : Fp := of_Z
  0x12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0.

(** Z = 11 for the SWU map on E'. *)
Definition swu_Z : Fp := of_Z 11.

(* ================================================================== *)
(** * 11-isogeny map E' -> E (RFC 9380 Appendix E.2)                   *)
(* ================================================================== *)

(** The 11-isogeny phi: E' -> E is given by rational maps:
      x_E = x_num(x') / x_den(x')
      y_E = y' * y_num(x') / y_den(x')
    where x_num, x_den, y_num, y_den are polynomials in x'.

    Coefficients from RFC 9380 Appendix E.2, verified against
    the noble-curves reference implementation. *)

(** x_num coefficients: degree-11 polynomial, k_(1,0) .. k_(1,11).
    x_num(x') = sum_{i=0}^{11} xnum_i * x'^i *)
Definition iso_xnum : list Fp := map of_Z [
  0x11a05f2b1e833340b809101dd99815856b303e88a2d7005ff2627b56cdb4e2c85610c2d5f2e62d6eaeac1662734649b7;
  0x17294ed3e943ab2f0588bab22147a81c7c17e75b2f6a8417f565e33c70d1e86b4838f2a6f318c356e834eef1b3cb83bb;
  0xd54005db97678ec1d1048c5d10a9a1bce032473295983e56878e501ec68e25c958c3e3d2a09729fe0179f9dac9edcb0;
  0x1778e7166fcc6db74e0609d307e55412d7f5e4656a8dbf25f1b33289f1b330835336e25ce3107193c5b388641d9b6861;
  0xe99726a3199f4436642b4b3e4118e5499db995a1257fb3f086eeb65982fac18985a286f301e77c451154ce9ac8895d9;
  0x1630c3250d7313ff01d1201bf7a74ab5db3cb17dd952799b9ed3ab9097e68f90a0870d2dcae73d19cd13c1c66f652983;
  0xd6ed6553fe44d296a3726c38ae652bfb11586264f0f8ce19008e218f9c86b2a8da25128c1052ecaddd7f225a139ed84;
  0x17b81e7701abdbe2e8743884d1117e53356de5ab275b4db1a682c62ef0f2753339b7c8f8c8f475af9ccb5618e3f0c88e;
  0x80d3cf1f9a78fc47b90b33563be990dc43b756ce79f5574a2c596c928c5d1de4fa295f296b74e956d71986a8497e317;
  0x169b1f8e1bcfa7c42e0c37515d138f22dd2ecb803a0c5c99676314baf4bb1b7fa3190b2edc0327797f241067be390c9e;
  0x10321da079ce07e272d8ec09d2565b0dfa7dccdde6787f96d50af36003b14866f69b771f8c285decca67df3f1605fb7b;
  0x6e08c248e260e70bd1e962381edee3d31d79d7e22c837bc23c0bf1bc24c6b68c24b1b80b64d391fa9c8ba2e8ba2d229
].

(** x_den coefficients: degree-9 polynomial + implicit leading 1.
    x_den(x') = x'^10 + sum_{i=0}^{9} xden_i * x'^i *)
Definition iso_xden : list Fp := map of_Z [
  0x8ca8d548cff19ae18b2e62f4bd3fa6f01d5ef4ba35b48ba9c9588617fc8ac62b558d681be343df8993cf9fa40d21b1c;
  0x12561a5deb559c4348b4711298e536367041e8ca0cf0800c0126c2588c48bf5713daa8846cb026e9e5c8276ec82b3bff;
  0xb2962fe57a3225e8137e629bff2991f6f89416f5a718cd1fca64e00b11aceacd6a3d0967c94fedcfcc239ba5cb83e19;
  0x3425581a58ae2fec83aafef7c40eb545b08243f16b1655154cca8abc28d6fd04976d5243eecf5c4130de8938dc62cd8;
  0x13a8e162022914a80a6f1d5f43e7a07dffdfc759a12062bb8d6b44e833b306da9bd29ba81f35781d539d395b3532a21e;
  0xe7355f8e4e667b955390f7f0506c6e9395735e9ce9cad4d0a43bcef24b8982f7400d24bc4228f11c02df9a29f6304a5;
  0x772caacf16936190f3e0c63e0596721570f5799af53a1894e2e073062aede9cea73b3538f0de06cec2574496ee84a3a;
  0x14a7ac2a9d64a8b230b3f5b074cf01996e7f63c21bca68a81996e1cdf9822c580fa5b9489d11e2d311f7d99bbdcc5a5e;
  0xa10ecf6ada54f825e920b3dafc7a3cce07f8d1d7161366b74100da67f39883503826692abba43704776ec3a79a1d641;
  0x95fc13ab9e92ad4476d6e3eb3a56680f682b4ee96f7d03776df533978f31c1593174e4b4b7865002d6384d168ecdd0a
].

(** y_num coefficients: degree-15 polynomial, k_(3,0) .. k_(3,15).
    y_num(x') = sum_{i=0}^{15} ynum_i * x'^i *)
Definition iso_ynum : list Fp := map of_Z [
  0x90d97c81ba24ee0259d1f094980dcfa11ad138e48a869522b52af6c956543d3cd0c7aee9b3ba3c2be9845719707bb33;
  0x134996a104ee5811d51036d776fb46831223e96c254f383d0f906343eb67ad34d6c56711962fa8bfe097e75a2e41c696;
  0xcc786baa966e66f4a384c86a3b49942552e2d658a31ce2c344be4b91400da7d26d521628b00523b8dfe240c72de1f6;
  0x1f86376e8981c217898751ad8746757d42aa7b90eeb791c09e4a3ec03251cf9de405aba9ec61deca6355c77b0e5f4cb;
  0x8cc03fdefe0ff135caf4fe2a21529c4195536fbe3ce50b879833fd221351adc2ee7f8dc099040a841b6daecf2e8fedb;
  0x16603fca40634b6a2211e11db8f0a6a074a7d0d4afadb7bd76505c3d3ad5544e203f6326c95a807299b23ab13633a5f0;
  0x4ab0b9bcfac1bbcb2c977d027796b3ce75bb8ca2be184cb5231413c4d634f3747a87ac2460f415ec961f8855fe9d6f2;
  0x987c8d5333ab86fde9926bd2ca6c674170a05bfe3bdd81ffd038da6c26c842642f64550fedfe935a15e4ca31870fb29;
  0x9fc4018bd96684be88c9e221e4da1bb8f3abd16679dc26c1e8b6e6a1f20cabe69d65201c78607a360370e577bdba587;
  0xe1bba7a1186bdb5223abde7ada14a23c42a0ca7915af6fe06985e7ed1e4d43b9b3f7055dd4eba6f2bafaaebca731c30;
  0x19713e47937cd1be0dfd0b8f1d43fb93cd2fcbcb6caf493fd1183e416389e61031bf3a5cce3fbafce813711ad011c132;
  0x18b46a908f36f6deb918c143fed2edcc523559b8aaf0c2462e6bfe7f911f643249d9cdf41b44d606ce07c8a4d0074d8e;
  0xb182cac101b9399d155096004f53f447aa7b12a3426b08ec02710e807b4633f06c851c1919211f20d4c04f00b971ef8;
  0x245a394ad1eca9b72fc00ae7be315dc757b3b080d4c158013e6632d3c40659cc6cf90ad1c232a6442d9d3f5db980133;
  0x5c129645e44cf1102a159f748c4a3fc5e673d81d7e86568d9ab0f5d396a7ce46ba1049b6579afb7866b1e715475224b;
  0x15e6be4e990f03ce4ea50b3b42df2eb5cb181d8f84965a3957add4fa95af01b2b665027efec01c7704b456be69c8b604
].

(** y_den coefficients: degree-14 polynomial + implicit leading 1.
    y_den(x') = x'^15 + sum_{i=0}^{14} yden_i * x'^i *)
Definition iso_yden : list Fp := map of_Z [
  0x16112c4c3a9c98b252181140fad0eae9601a6de578980be6eec3232b5be72e7a07f3688ef60c206d01479253b03663c1;
  0x1962d75c2381201e1a0cbd6c43c348b885c84ff731c4d59ca4a10356f453e01f78a4260763529e3532f6102c2e49a03d;
  0x58df3306640da276faaae7d6e8eb15778c4855551ae7f310c35a5dd279cd2eca6757cd636f96f891e2538b53dbf67f2;
  0x16b7d288798e5395f20d23bf89edb4d1d115c5dbddbcd30e123da489e726af41727364f2c28297ada8d26d98445f5416;
  0xbe0e079545f43e4b00cc912f8228ddcc6d19c9f0f69bbb0542eda0fc9dec916a20b15dc0fd2ededda39142311a5001d;
  0x8d9e5297186db2d9fb266eaac783182b70152c65550d881c5ecd87b6f0f5a6449f38db9dfa9cce202c6477faaf9b7ac;
  0x166007c08a99db2fc3ba8734ace9824b5eecfdfa8d0cf8ef5dd365bc400a0051d5fa9c01a58b1fb93d1a1399126a775c;
  0x16a3ef08be3ea7ea03bcddfabba6ff6ee5a4375efa1f4fd7feb34fd206357132b920f5b00801dee460ee415a15812ed9;
  0x1866c8ed336c61231a1be54fd1d74cc4f9fb0ce4c6af5920abc5750c4bf39b4852cfe2f7bb9248836b233d9d55535d4a;
  0x167a55cda70a6e1cea820597d94a84903216f763e13d87bb5308592e7ea7d4fbc7385ea3d529b35e346ef48bb8913f55;
  0x4d2f259eea405bd48f010a01ad2911d9c6dd039bb61a6290e591b36e636a5c871a5c29f4f83060400f8b49cba8f6aa8;
  0xaccbb67481d033ff5852c1e48c50c477f94ff8aefce42d28c0f9a88cea7913516f968986f7ebbea9684b529e2561092;
  0xad6b9514c767fe3c3613144b45f1496543346d98adf02267d5ceef9a00d9b8693000763e3b90ac11e99b138573345cc;
  0x2660400eb2e4f3b628bdd0d53cd76f2bf565b94e72927c1cb748df27942480e420517bd8714cc80d1fadc1326ed06f7;
  0xe0fa1d816ddc03e6b24255e0d7819c171c40f65e273b853324efcd6356caa205ca2f570f13497804415473a1d634b8f
].

(** Evaluate a polynomial given as a list of coefficients [c0, c1, ..., cn]
    using Horner's method: c0 + x*(c1 + x*(c2 + ... + x*cn)...).
    We use a right fold after reversing. *)
Fixpoint horner_eval (cs : list Fp) (x : Fp) : Fp :=
  match cs with
  | [] => 0f
  | [c] => c
  | c :: cs' => c +f x *f horner_eval cs' x
  end.

(** Evaluate a monic polynomial x^(n+1) + sum_{i=0}^n cs_i * x^i,
    where cs has n+1 coefficients. The leading coefficient 1 is implicit. *)
Definition horner_eval_monic (cs : list Fp) (x : Fp) : Fp :=
  horner_eval (cs ++ [1f]) x.

(** The 11-isogeny map phi: E'(x', y') -> E(x, y).

    Uses projective computation internally to handle kernel points
    (where xden = 0) correctly. The projective image is
      (X, Y, Z) = (xnum * yden, y' * ynum * xden, xden * yden)
    which is converted to affine (X/Z, Y/Z) when Z ≠ 0.
    When Z = 0 (kernel points), the image is the point at infinity,
    represented as (0, 2) since (0, 2) ∈ E: y² = x³ + 4. *)
Definition iso_map (pt : Fp * Fp) : Fp * Fp :=
  let '(x', y') := pt in
  let xn := horner_eval iso_xnum x' in
  let xd := horner_eval_monic iso_xden x' in
  let yn := horner_eval iso_ynum x' in
  let yd := horner_eval_monic iso_yden x' in
  let z := xd *f yd in
  if fp_eqb z 0f then
    (0f, of_Z 2)
  else
    (xn *f yd *f inv z, y' *f yn *f xd *f inv z).

(* ================================================================== *)
(** * map_to_curve for BLS12-381 G1                                    *)
(* ================================================================== *)

(** The full map_to_curve composes SWU on E' with the isogeny to E.

    map_to_curve_g1(u) =
      iso_map(map_to_curve_simple_swu(iso_A, iso_B, swu_Z, u))
*)
Definition map_to_curve_g1 (u : Fp) : Fp * Fp :=
  iso_map (map_to_curve_simple_swu iso_A iso_B swu_Z u).

(* ================================================================== *)
(** * Point addition on E: y^2 = x^3 + 4 (affine coordinates)         *)
(* ================================================================== *)

(** Affine point: either a pair (x, y) or the point at infinity. *)
Definition affine_point := option (Fp * Fp).

Definition point_at_infinity : affine_point := None.

(** The curve coefficient b = 4 for BLS12-381 G1. *)
Definition bls12_b : Fp := of_Z 4.

(** Affine point addition on E: y^2 = x^3 + 4.
    This is the textbook formula; for the spec we only need it
    to define the hash_to_curve output. *)
Definition point_add (P Q : affine_point) : affine_point :=
  match P, Q with
  | None, _ => Q
  | _, None => P
  | Some (x1, y1), Some (x2, y2) =>
    if fp_eqb x1 x2
    then
      (* x1 = x2 *)
      if fp_eqb y1 (-f y2)
      then point_at_infinity  (* P + (-P) = O *)
      else
        (* doubling: lambda = 3*x1^2 / (2*y1) (since a = 0) *)
        let lambda := of_Z 3 *f sqr x1 *f inv (of_Z 2 *f y1) in
        let x3 := sqr lambda -f x1 -f x2 in
        let y3 := lambda *f (x1 -f x3) -f y1 in
        Some (x3, y3)
    else
      (* general addition: lambda = (y2 - y1) / (x2 - x1) *)
      let lambda := (y2 -f y1) *f inv (x2 -f x1) in
      let x3 := sqr lambda -f x1 -f x2 in
      let y3 := lambda *f (x1 -f x3) -f y1 in
      Some (x3, y3)
  end.

(* ================================================================== *)
(** * Scalar multiplication                                            *)
(* ================================================================== *)

Fixpoint scalar_mul (n : nat) (P : affine_point) : affine_point :=
  match n with
  | O => point_at_infinity
  | S n' => point_add P (scalar_mul n' P)
  end.

(* ================================================================== *)
(** * Cofactor clearing (RFC 9380 section 8.8.1)                       *)
(* ================================================================== *)

(** The effective cofactor h_eff for BLS12-381 G1.
    From RFC 9380 section 8.8.1:
      h_eff = 0xd201000000010001
    This equals x^2 - 1 where x is the BLS parameter (negated),
    and is chosen for compatibility with the Budroni-Pintore fast
    cofactor clearing method. Note: for G1 the actual cofactor is
    h = (x - 1)^2 / 3, but h_eff is used because [h_eff]P and
    [h]P yield the same result for points on the curve. *)
Definition h_eff : Z := 0xd201000000010001.

Definition clear_cofactor (P : affine_point) : affine_point :=
  scalar_mul (Z.to_nat h_eff) P.

(* ================================================================== *)
(** * hash_to_curve pipeline (RFC 9380 section 3)                      *)
(* ================================================================== *)

(** The domain separation tag for BLS12-381 G1 with SHA-256. *)
Definition dst_g1 : list Byte.byte :=
  (* "BLS_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_NUL_" *)
  (* Users should supply their own DST; this is a placeholder. *)
  [].

(** hash_to_curve: the full pipeline from RFC 9380 section 3.

    hash_to_curve(msg, DST) =
      1. u0, u1 = hash_to_field(msg, DST, 2)
      2. Q0 = map_to_curve(u0)
      3. Q1 = map_to_curve(u1)
      4. R  = Q0 + Q1
      5. P  = clear_cofactor(R)
      6. return P
*)
Definition hash_to_curve (msg : list Byte.byte) (dst : list Byte.byte)
  : affine_point :=
  let us := hash_to_field p_pos msg dst 2 in
  match us with
  | [u0; u1] =>
    let Q0 := map_to_curve_g1 u0 in
    let Q1 := map_to_curve_g1 u1 in
    let R := point_add (Some Q0) (Some Q1) in
    clear_cofactor R
  | _ => point_at_infinity  (* unreachable: hash_to_field returns exactly 2 *)
  end.

(** encode_to_curve: the nonuniform variant from RFC 9380 section 3.

    encode_to_curve(msg, DST) =
      1. u = hash_to_field(msg, DST, 1)
      2. Q = map_to_curve(u)
      3. P = clear_cofactor(Q)
      4. return P
*)
Definition encode_to_curve (msg : list Byte.byte) (dst : list Byte.byte)
  : affine_point :=
  let us := hash_to_field p_pos msg dst 1 in
  match us with
  | [u0] =>
    let Q := map_to_curve_g1 u0 in
    clear_cofactor (Some Q)
  | _ => point_at_infinity
  end.

(* ================================================================== *)
(** * Well-formedness properties                                       *)
(* ================================================================== *)

(** A point is on the target curve E: y^2 = x^3 + 4. *)
Definition on_curve_E (pt : Fp * Fp) : Prop :=
  let '(x, y) := pt in
  sqr y = cube x +f bls12_b.

(** A point is on the isogenous curve E': y^2 = x^3 + A'*x + B'. *)
Definition on_curve_Eprime (pt : Fp * Fp) : Prop :=
  let '(x, y) := pt in
  sqr y = cube x +f iso_A *f x +f iso_B.

(** The SWU map should produce points on E'. *)
Definition swu_maps_to_Eprime : Prop :=
  forall u : Fp,
    on_curve_Eprime (map_to_curve_simple_swu iso_A iso_B swu_Z u).

(** The isogeny should map E' points to E points. *)
Definition iso_maps_Eprime_to_E : Prop :=
  forall pt : Fp * Fp,
    on_curve_Eprime pt -> on_curve_E (iso_map pt).

(** The full map should produce points on E. *)
Definition map_produces_curve_points : Prop :=
  forall u : Fp,
    on_curve_E (map_to_curve_g1 u).
