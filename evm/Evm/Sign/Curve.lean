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
- **The multiplication does the same work for every key.** For each of the key's 255 bits, from the top:
  double, add the point, and keep the sum or the double as the bit says, chosen by `Secret.select` on every
  limb. Which bit is being looked at is public; what the bit is decides no branch and no address.
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

/-- `k` times `p`: for each of 255 bits a doubling and an addition, whatever the bits are. -/
def Point.mul {F : Type} [Field F] (b3 : F) (k : Scalar) (p : Point F) : Point F :=
  (List.range 255).foldl (fun acc i =>
    let doubled := Point.add b3 acc acc
    Point.select (k.bit (254 - i)) (Point.add b3 doubled p) doubled) Point.infinity

end Evm.Sign
