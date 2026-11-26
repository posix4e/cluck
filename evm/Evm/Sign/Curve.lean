import Evm.Sign.Field

/-! The key times a point, in time that does not depend on the key.

A BLS signature is the secret key times a point of the curve, and a public key is the secret key times the
generator. This file is that multiplication and nothing else, over `Fp` (`Evm/Sign/Field.lean`) for public
keys and over its quadratic extension for signatures.

- **Points are projective and the addition is complete.** `add` is the formula of Renes, Costello and
  Batina ("Complete addition formulas for prime order elliptic curves", 2015, algorithm 7, for curves
  `y^2 = x^3 + b`). It is one sequence of field operations that is right for every pair of points: equal,
  opposite, either one the point at infinity. So nothing has to ask which case it is in, and which case it
  is in is exactly what would tell an observer about the key.
- **The multiplication does the same work for every key.** The key is taken four bits at a time, from
  the top: double four times, then add the point times those four bits, which is one of sixteen multiples
  worked out beforehand. Which of the sixteen is never looked up: every one is gone through, and each is
  kept or passed over by `Secret.select` on every limb, on a truth value made from the four bits by
  arithmetic alone (`Scalar.is`). Which four bits are being looked at is public; what they are decides no
  branch and no address. Adding the multiple that is nothing, when the four bits are, is the same
  addition as any other (the formula is complete). Until 2026-11-26 it was a doubling and an addition for
  each bit, with the addition's formula used for the doubling too: 510 additions where there are now 256
  doublings, each two thirds of an addition, and 79 additions.
- **Leaving projective form is a secret operation too.** The three coordinates the multiplication ends
  with depend on the key in ways the affine point does not, so the division by the third is by a fixed
  sequence of products (`Fp.inv`), and only its result is made public.

`bls-test` holds `add` and `mul` to `Jaune`'s arithmetic on `Nat`, and the signatures and public keys made
with them to `JauneConsensus`'s. -/

namespace Evm.Sign

/-- What the curve arithmetic needs of a field: sums, differences and products, and a choice between two
elements that does not branch. -/
class Field (F : Type) where
  zero : F
  one : F
  add : F → F → F
  sub : F → F → F
  mul : F → F → F
  select : Bool → F → F → F

instance : Field Fp := ⟨Fp.zero, Fp.one, Fp.add, Fp.sub, Fp.mul, Fp.select⟩

/-- The quadratic extension, `c0 + c1 u` with `u^2 = -1`. -/
structure Fp2 where
  c0 : Fp
  c1 : Fp

namespace Fp2

def zero : Fp2 := ⟨Fp.zero, Fp.zero⟩
def one : Fp2 := ⟨Fp.one, Fp.zero⟩
def add (a b : Fp2) : Fp2 := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
def sub (a b : Fp2) : Fp2 := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
def mul (a b : Fp2) : Fp2 := ⟨a.c0 * b.c0 - a.c1 * b.c1, a.c0 * b.c1 + a.c1 * b.c0⟩
def select (c : Bool) (x y : Fp2) : Fp2 := ⟨Fp.select c x.c0 y.c0, Fp.select c x.c1 y.c1⟩

/-- `1 / a`: the conjugate over the norm, the norm inverted in `Fp`. -/
def inv (a : Fp2) : Fp2 :=
  let n := (a.c0 * a.c0 + a.c1 * a.c1).inv
  ⟨a.c0 * n, Fp.neg (a.c1 * n)⟩

end Fp2

instance : Field Fp2 := ⟨Fp2.zero, Fp2.one, Fp2.add, Fp2.sub, Fp2.mul, Fp2.select⟩

/-- A point `(x/z, y/z)`, or the point at infinity when `z` is zero. -/
structure Point (F : Type) where
  x : F
  y : F
  z : F

namespace Point

variable {F : Type} [Field F]

local instance : Add F := ⟨Field.add⟩
local instance : Sub F := ⟨Field.sub⟩
local instance : Mul F := ⟨Field.mul⟩

def infinity : Point F := ⟨Field.zero, Field.one, Field.zero⟩

def ofAffine (x y : F) : Point F := ⟨x, y, Field.one⟩

def select (c : Bool) (p q : Point F) : Point F :=
  ⟨Field.select c p.x q.x, Field.select c p.y q.y, Field.select c p.z q.z⟩

/-- The sum of any two points of `y^2 = x^3 + b`, given `3b`. -/
def add (b3 : F) (p q : Point F) : Point F :=
  let t0 := p.x * q.x
  let t1 := p.y * q.y
  let t2 := p.z * q.z
  let t3 := (p.x + p.y) * (q.x + q.y)
  let t3 := t3 - (t0 + t1)
  let t4 := (p.y + p.z) * (q.y + q.z)
  let t4 := t4 - (t1 + t2)
  let y3 := (p.x + p.z) * (q.x + q.z)
  let y3 := y3 - (t0 + t2)
  let t0 := (t0 + t0) + t0
  let t2 := b3 * t2
  let z3 := t1 + t2
  let t1 := t1 - t2
  let y3 := b3 * y3
  let x3 := t3 * t1 - t4 * y3
  let y3 := t1 * z3 + y3 * t0
  let z3 := z3 * t4 + t0 * t3
  ⟨x3, y3, z3⟩

/-- Twice any point of `y^2 = x^3 + b`, given `3b`: the same paper's algorithm 9. One sequence of field
operations that is right for every point, the point at infinity too, as `add` is; `add p p` gives the
same point for half as much again. -/
def double (b3 : F) (p : Point F) : Point F :=
  let t0 := p.y * p.y
  let z3 := t0 + t0
  let z3 := z3 + z3
  let z3 := z3 + z3
  let t1 := p.y * p.z
  let t2 := p.z * p.z
  let t2 := b3 * t2
  let x3 := t2 * z3
  let y3 := t0 + t2
  let z3 := t1 * z3
  let t1 := t2 + t2
  let t2 := t1 + t2
  let t0 := t0 - t2
  let y3 := t0 * y3
  let y3 := x3 + y3
  let t1 := p.x * p.y
  let x3 := t0 * t1
  let x3 := x3 + x3
  ⟨x3, y3, z3⟩

end Point

/-- A key: a number below `2^255` as four 64-bit words, low first. -/
structure Scalar where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64

/-- Bit `i` of a key, for a public `i`. -/
def Scalar.bit (k : Scalar) (i : Nat) : Bool :=
  let word := if i < 64 then k.w0 else if i < 128 then k.w1 else if i < 192 then k.w2 else k.w3
  (word >>> (i % 64).toUInt64) &&& 1 == 1

/-- Four bits of a key, bits `4w` to `4w + 3` for a public `w`: a number from 0 to 15, as secret as
the key. -/
def Scalar.four (k : Scalar) (w : Nat) : UInt64 :=
  let i := 4 * w
  let word := if i < 64 then k.w0 else if i < 128 then k.w1 else if i < 192 then k.w2 else k.w3
  (word >>> (i % 64).toUInt64) &&& 15

/-- Whether a secret number is the public `j`, by arithmetic and not by comparing the two: their
difference bit by bit, the top bit of that or of its negation (set unless it is nothing), and that bit
against a constant, as `Scalar.bit` ends. The truth value is for `Secret.select` and nothing else. -/
def Scalar.is (secret j : UInt64) : Bool :=
  let x := secret ^^^ j
  ((x ||| (0 - x)) >>> 63) &&& 1 == 0

/-- `k` times `p`: for each four bits of the key four doublings and an addition, whatever the bits are. -/
def Point.mul {F : Type} [Field F] (b3 : F) (k : Scalar) (p : Point F) : Point F :=
  -- Nothing, `p`, twice `p`, and so on to fifteen times `p`. `p` is not secret, and neither are these.
  let multiples : Array (Point F) :=
    (List.range 15).foldl (fun found _ => found.push (Point.add b3 (found.getD (found.size - 1) Point.infinity) p))
      #[Point.infinity]
  (List.range 64).foldl (fun acc i =>
    let acc := Point.double b3 (Point.double b3 (Point.double b3 (Point.double b3 acc)))
    let four := k.four (63 - i)
    -- Every multiple is gone through; the one the four bits name is kept.
    let chosen := (List.range 16).foldl (fun chosen j =>
      Point.select (Scalar.is four j.toUInt64) (multiples.getD j Point.infinity) chosen) Point.infinity
    Point.add b3 acc chosen) Point.infinity

end Evm.Sign
