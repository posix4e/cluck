import Evm.Sign.Curve
import JauneConsensus.Crypto.HashToCurve

/-! A message made a point of G2, by this project's own field arithmetic.

A signature is the key times the point a message hashes to (RFC 9380, the suite
`BLS12381G2_XMD:SHA-256_SSWU_RO_`). Nothing here is secret: the message is a bid, which is public, and so
is its point. It is here and not left to `JauneConsensus` for what it costs. That library works on `Nat`,
with a division in the field for every addition of points, and took 20 to 28 ms a message where a bid was
being signed, as much as running the block's transactions; this takes a tenth of that, and it is one
thing fewer that a third party's code does for a bid.

What is `JauneConsensus`'s still: the message stretched into two field elements (`hashToFieldFp2`,
SHA-256), and the constants, which are read from `Jaune`'s tables and not written out again. What is
done here: each element mapped to the curve the standard's way (the simplified SWU map onto a curve
three-isogenous to this one, then the isogeny), the two points added, and the cofactor cleared with the
endomorphism `psi` and two multiplications by the curve's 64-bit parameter (RFC 9380 appendix G.3). The
map follows `Jaune`'s `optimizedSwuG2` step for step, and `bls-test` holds the point to
`JauneConsensus.hashToG2`'s for the standard's vectors and for messages made up there.

The branches here are on public values, and say so in their names (`isZeroPublic`, `sgn0Public`,
`powPublic`). The key never comes near this file: `Evm/Sign.lean` multiplies the point it returns. -/

namespace Evm.Sign

open Jaune JauneConsensus

/-- Three times the `4 + 4u` of the curve signatures are on. -/
def b3G2 : Fp2 := ⟨Fp.ofPublic 12, Fp.ofPublic 12⟩

namespace Fp2

def neg (a : Fp2) : Fp2 := ⟨Fp.neg a.c0, Fp.neg a.c1⟩

/-- `a ^ p`: the other root of `u^2 = -1` in place of `u`. -/
def conj (a : Fp2) : Fp2 := ⟨a.c0, Fp.neg a.c1⟩

/-- An element that is not a secret. -/
def ofPublic (x : Bls12Fp2) : Fp2 :=
  let (c0, c1) := blsF2Coeffs x
  ⟨Fp.ofPublic c0.val, Fp.ofPublic c1.val⟩

/-- Whether an element that is not a secret is zero. -/
def isZeroPublic (a : Fp2) : Bool := a.c0.toPublic == 0 && a.c1.toPublic == 0

/-- `a ^ e` for an exponent that is public, given as its bits from the top. -/
def powPublic (a : Fp2) (bits : List Bool) : Fp2 :=
  bits.foldl (fun r bit => let s := mul r r; if bit then mul s a else s) one

/-- The standard's `sgn0` of an element that is not a secret. -/
def sgn0Public (a : Fp2) : Nat :=
  let c0 := a.c0.toPublic
  if c0 % 2 == 1 then 1 else if c0 == 0 then a.c1.toPublic % 2 else 0

end Fp2

namespace Hash

local instance : Add Fp2 := ⟨Fp2.add⟩
local instance : Sub Fp2 := ⟨Fp2.sub⟩
local instance : Mul Fp2 := ⟨Fp2.mul⟩

def constant (c : Nat × Nat) : Fp2 := Fp2.ofPublic (blsToF2 c)

/-- The isogenous curve `y^2 = x^3 + a x + b`, and the `Z` of the map onto it. -/
def a : Fp2 := constant BLSConst.iso3A
def b : Fp2 := constant BLSConst.iso3B
def z : Fp2 := constant BLSConst.iso3Z

/-- `(p^2 - 9) / 16`, as its bits from the top. -/
def rootExponent : List Bool :=
  let e := BLSConst.pMinus9Div16
  (List.range (e.log2 + 1)).reverse.map fun i => e.testBit i

def eighthRoots : List Fp2 := BLSConst.eighthRoots.map constant
def etas : List Fp2 := BLSConst.etas.map constant
def xNum : List Fp2 := BLSConst.iso3XNum.map constant
def xDen : List Fp2 := BLSConst.iso3XDen.map constant
def yNum : List Fp2 := BLSConst.iso3YNum.map constant
def yDen : List Fp2 := BLSConst.iso3YDen.map constant
def psiX : Fp2 := Fp2.ofPublic psiCoefficientX
def psiY : Fp2 := Fp2.ofPublic psiCoefficientY

/-- The curve's parameter without its sign, `0xd201000000010000`, as its bits from the top. -/
def parameter : List Bool := (List.range 64).reverse.map fun i => blsAteLoopCount.testBit i

/-- A square root of `u / v` when there is one: whether, and the root or what the caller mends. -/
def sqrtDivision (u v : Fp2) : Bool × Fp2 :=
  let v2 := v * v
  let v4 := v2 * v2
  let temp1 := u * (v4 * v2 * v)
  let temp2 := temp1 * (v4 * v4)
  let gamma := Fp2.powPublic temp2 rootExponent * temp1
  let found := eighthRoots.findSome? fun root =>
    let candidate := root * gamma
    if (candidate * candidate * v - u).isZeroPublic then some candidate else none
  match found with
  | some candidate => (true, candidate)
  | none => (false, gamma)

/-- The simplified SWU map: a point `(numerator / denominator, y)` of the isogenous curve. -/
def swu (t : Fp2) : Fp2 × Fp2 × Fp2 :=
  let t2 := t * t
  let zt2 := z * t2
  let temp := zt2 + zt2 * zt2
  let denominator0 := Fp2.neg (a * temp)
  let numerator0 := b * (temp + Fp2.one)
  let denominator := if denominator0.isZeroPublic then z * a else denominator0
  let d2 := denominator * denominator
  let v := d2 * denominator
  let u0 := numerator0 * numerator0 * numerator0 + a * numerator0 * d2 + b * v
  let (success, candidate0) := sqrtDivision u0 v
  let y1 :=
    if success then candidate0 else
    let candidate := candidate0 * (t2 * t)
    let u := zt2 * zt2 * zt2 * u0
    let mended := etas.findSome? fun eta =>
      let scaled := eta * candidate
      if (scaled * scaled * v - u).isZeroPublic then some scaled else none
    mended.getD candidate0
  let numerator := if success then numerator0 else numerator0 * zt2
  let y := if t.sgn0Public != y1.sgn0Public then Fp2.neg y1 else y1
  (numerator, denominator, y)

def horner (coefficients : List Fp2) (x : Fp2) : Fp2 :=
  coefficients.foldr (fun c sum => sum * x + c) Fp2.zero

/-- A field element mapped to the curve: the SWU map, then the isogeny. Not yet in G2. -/
def onCurve (t : Fp2) : Point Fp2 :=
  let (numerator, denominator, y) := swu t
  let x := numerator * denominator.inv
  let xd := horner xDen x
  let yd := horner yDen x
  if (xd * yd).isZeroPublic then Point.infinity
  else ⟨horner xNum x * yd, y * horner yNum x * xd, xd * yd⟩

def negate (p : Point Fp2) : Point Fp2 := ⟨p.x, Fp2.neg p.y, p.z⟩

/-- The endomorphism `psi`: Frobenius on each coordinate, and the twist's two constants. -/
def psi (p : Point Fp2) : Point Fp2 := ⟨p.x.conj * psiX, p.y.conj * psiY, p.z.conj⟩

/-- The curve's parameter times a point that is not a secret. -/
def timesParameter (p : Point Fp2) : Point Fp2 :=
  parameter.foldl (fun sum bit =>
    let doubled := Point.add b3G2 sum sum
    if bit then Point.add b3G2 doubled p else doubled) Point.infinity

/-- A point of the curve taken into G2: `h_eff` times it, by RFC 9380's appendix G.3. -/
def clear (p : Point Fp2) : Point Fp2 :=
  let plus := Point.add b3G2
  -- The parameter is negative.
  let c1 (x : Point Fp2) : Point Fp2 := negate (timesParameter x)
  let t1 := c1 p
  let t2 := psi p
  let t3 := psi (psi (plus p p))
  let t3 := plus t3 (negate t2)
  let t2 := c1 (plus t1 t2)
  let t3 := plus t3 t2
  let t3 := plus t3 (negate t1)
  plus t3 (negate p)

/-- The point of G2 a message hashes to under a tag. -/
def toPoint (message tag : Bytes) : Except String (Point Fp2) := do
  match ← hashToFieldFp2 message tag 2 with
  | [u0, u1] => pure (clear (Point.add b3G2 (onCurve (Fp2.ofPublic u0)) (onCurve (Fp2.ofPublic u1))))
  | _ => throw "hash_to_field: wrong output count"

end Hash

end Evm.Sign
