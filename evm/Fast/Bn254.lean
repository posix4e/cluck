import Fast.Word

/-! The curve bn254 (alt_bn128) on machine words, for the three precompiled contracts that use it: addition
and multiplication of points (EIP-196) and the pairing check (EIP-197).

Numbers modulo the field's prime are four machine words in Montgomery form, and the arithmetic on them is
written to be inlined: an element of the quadratic extension is eight machine words in one object, and a
product in it is three products of the base field worked out in variables. Above that the tower is the
usual one, cubic over quadratic and quadratic over that, and the pairing is the optimal ate pairing as
Naehrig, Niederhagen and Schwabe describe it, laid out as in the Go implementation that go-ethereum
carries (`bn256`): the same formulas for the two line functions, the same order of steps in the final
exponentiation.

The constants below were worked out from the curve's prime, its order and the number it is made from, not
copied from anywhere, and `bn254-test` checks the arithmetic against `Nat` and the three contracts against
Jaune's. Nothing here is proved. Nothing here is secret, and nothing here is constant time. -/

namespace Fast.Bn254

/-- A number modulo the field's prime, as four machine words, least significant first. Except where it is
said otherwise it is in Montgomery form: the number times 2^256. -/
structure Fp where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  deriving BEq, Inhabited

/-- A number of the quadratic extension, `x i + y` with `i² = -1`: the eight words of `x` and `y`. -/
structure Fp2 where
  x0 : UInt64
  x1 : UInt64
  x2 : UInt64
  x3 : UInt64
  y0 : UInt64
  y1 : UInt64
  y2 : UInt64
  y3 : UInt64
  deriving BEq, Inhabited

namespace Fp

/-- The field's prime, least significant word first. -/
def prime : Fp := ⟨0x3c208c16d87cfd47, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029⟩
/-- What a product is multiplied by to clear its low word: minus the inverse of the prime, modulo 2^64. -/
def primeInverse : UInt64 := 0x87d20782e4866389
/-- 2^512 modulo the prime: what turns a number into its Montgomery form. -/
def rSquared : Fp := ⟨0xf32cfc5b538afa89, 0xb5e71911d44501fb, 0x47ab1eff0a417ff6, 0x06d89f71cab8351f⟩
def one : Fp := ⟨0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f⟩
def three : Fp := ⟨0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e⟩
/-- The prime less two, not in Montgomery form: the power that inverts. -/
def primeMinusTwo : Fp := ⟨0x3c208c16d87cfd45, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029⟩
/-- The order of the groups, not in Montgomery form. -/
def order : Fp := ⟨0x43e1f593f0000001, 0x2833e84879b97091, 0xb85045b68181585d, 0x30644e72e131a029⟩
/-- The number the curve is made from. -/
def parameter : UInt64 := 4965661367192848881
/-- Six times that number and two more, in digits of -1, 0 and 1 with no two beside each other, lowest first:
what the Miller loop steps through. A digit is held as 0, 1, or 2 for -1. -/
def loopDigits : Array UInt8 := #[0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2, 0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 1]
def zero : Fp := ⟨0, 0, 0, 0⟩

@[inline] def isZero (a : Fp) : Bool := (a.a0 ||| a.a1 ||| a.a2 ||| a.a3) == 0

/-- `t` less the prime if that is not negative, and `t` otherwise: for a `t` under twice the prime. Done
without a branch, so that nothing has to be built where two ways would meet. -/
@[inline] def reduce (t0 t1 t2 t3 : UInt64) : Fp :=
  let d0 := t0 - prime.a0
  let b0 := Word.borrow t0 prime.a0 d0
  let d1 := t1 - prime.a1 - b0
  let b1 := Word.borrow t1 prime.a1 d1
  let d2 := t2 - prime.a2 - b1
  let b2 := Word.borrow t2 prime.a2 d2
  let d3 := t3 - prime.a3 - b2
  let b3 := Word.borrow t3 prime.a3 d3
  -- All ones if the subtraction went under, which keeps `t`.
  let keep := 0 - b3
  ⟨(t0 &&& keep) ||| (d0 &&& ~~~keep), (t1 &&& keep) ||| (d1 &&& ~~~keep),
   (t2 &&& keep) ||| (d2 &&& ~~~keep), (t3 &&& keep) ||| (d3 &&& ~~~keep)⟩

@[inline] def add (a b : Fp) : Fp :=
  let s0 := a.a0 + b.a0
  let c0 := Word.carry a.a0 b.a0 s0
  let s1 := a.a1 + b.a1 + c0
  let c1 := Word.carry a.a1 b.a1 s1
  let s2 := a.a2 + b.a2 + c1
  let c2 := Word.carry a.a2 b.a2 s2
  reduce s0 s1 s2 (a.a3 + b.a3 + c2)

@[inline] def sub (a b : Fp) : Fp :=
  let d0 := a.a0 - b.a0
  let b0 := Word.borrow a.a0 b.a0 d0
  let d1 := a.a1 - b.a1 - b0
  let b1 := Word.borrow a.a1 b.a1 d1
  let d2 := a.a2 - b.a2 - b1
  let b2 := Word.borrow a.a2 b.a2 d2
  let d3 := a.a3 - b.a3 - b2
  let b3 := Word.borrow a.a3 b.a3 d3
  -- The prime is added back if the subtraction went under.
  let back := 0 - b3
  let s0 := d0 + (prime.a0 &&& back)
  let c0 := Word.carry d0 (prime.a0 &&& back) s0
  let s1 := d1 + (prime.a1 &&& back) + c0
  let c1 := Word.carry d1 (prime.a1 &&& back) s1
  let s2 := d2 + (prime.a2 &&& back) + c1
  let c2 := Word.carry d2 (prime.a2 &&& back) s2
  ⟨s0, s1, s2, d3 + (prime.a3 &&& back) + c2⟩

@[inline] def neg (a : Fp) : Fp := sub zero a
@[inline] def double (a : Fp) : Fp := add a a

/-- One round of Montgomery's multiplication: `t + a * b`, then a multiple of the prime added that clears
the low word, and the whole moved down a word. `t` stays under twice the prime, the prime being two bits
short of 256, so four words and the carry between the two passes are all there is. -/
@[inline] def round {α : Type} (a : Fp) (b t0 t1 t2 t3 : UInt64) (k : UInt64 → UInt64 → UInt64 → UInt64 → α) : α :=
  Word.mac a.a0 b t0 0 fun t0 c =>
  Word.mac a.a1 b t1 c fun t1 c =>
  Word.mac a.a2 b t2 c fun t2 c =>
  Word.mac a.a3 b t3 c fun t3 t4 =>
  let m := t0 * primeInverse
  Word.mac m prime.a0 t0 0 fun _ c =>
  Word.mac m prime.a1 t1 c fun t0 c =>
  Word.mac m prime.a2 t2 c fun t1 c =>
  Word.mac m prime.a3 t3 c fun t2 c =>
  k t0 t1 t2 (t4 + c)

/-- The product, in Montgomery form when both are. -/
@[inline] def mul (a b : Fp) : Fp :=
  round a b.a0 0 0 0 0 fun t0 t1 t2 t3 =>
  round a b.a1 t0 t1 t2 t3 fun t0 t1 t2 t3 =>
  round a b.a2 t0 t1 t2 t3 fun t0 t1 t2 t3 =>
  round a b.a3 t0 t1 t2 t3 fun t0 t1 t2 t3 =>
  reduce t0 t1 t2 t3

@[inline] def square (a : Fp) : Fp := mul a a

/-- A product for code that is not itself inlined into something bigger. -/
@[noinline] def times (a b : Fp) : Fp := mul a b

/-- The bit numbered `i` of a number of four words. -/
@[inline] def bit (e : Fp) (i : Nat) : Bool :=
  let word := if i < 64 then e.a0 else if i < 128 then e.a1 else if i < 192 then e.a2 else e.a3
  (word >>> (i % 64).toUInt64) &&& 1 == 1

/-- `a` to the power `e`, where `e` is a plain number of four words: `left` bits of it from the top. -/
def power (a e : Fp) : Nat → Fp → Fp
  | 0, acc => acc
  | left + 1, acc =>
    let acc := times acc acc
    power a e left (if bit e left then times acc a else acc)

/-- The inverse, by the power that is the prime less two; nothing for nothing. -/
def inverse (a : Fp) : Fp := power a primeMinusTwo 256 one

/-- A number into Montgomery form, and out of it. -/
def toMontgomery (a : Fp) : Fp := times a rSquared
def fromMontgomery (a : Fp) : Fp := times a ⟨1, 0, 0, 0⟩

/-- Whether a plain number of four words is under the prime. -/
def canonical (a : Fp) : Bool :=
  if a.a3 != prime.a3 then a.a3 < prime.a3 else if a.a2 != prime.a2 then a.a2 < prime.a2
  else if a.a1 != prime.a1 then a.a1 < prime.a1 else a.a0 < prime.a0

/-- A number from 32 bytes, most significant first, at `off`: none if the bytes are not there or spell a
number that is not under the prime. -/
def read (b : @& ByteArray) (off : Nat) : Option Fp :=
  if off + 32 > b.size then none else
  let word (at_ : Nat) : UInt64 :=
    (List.range 8).foldl (fun n i => (n <<< 8) ||| (b.get! (at_ + i)).toUInt64) 0
  let plain : Fp := ⟨word (off + 24), word (off + 16), word (off + 8), word off⟩
  if canonical plain then some (toMontgomery plain) else none

/-- The 32 bytes of a number, most significant first, added to `out`. -/
def write (out : ByteArray) (a : Fp) : ByteArray :=
  let plain := fromMontgomery a
  [plain.a3, plain.a2, plain.a1, plain.a0].foldl (fun out word =>
    (List.range 8).foldl (fun out i => out.push (word >>> (56 - 8 * i).toUInt64).toUInt8) out) out

end Fp

namespace Fp2

@[inline] def im (a : Fp2) : Fp := ⟨a.x0, a.x1, a.x2, a.x3⟩
@[inline] def re (a : Fp2) : Fp := ⟨a.y0, a.y1, a.y2, a.y3⟩
@[inline] def of (x y : Fp) : Fp2 := ⟨x.a0, x.a1, x.a2, x.a3, y.a0, y.a1, y.a2, y.a3⟩

def zero : Fp2 := of Fp.zero Fp.zero
def one : Fp2 := of Fp.zero Fp.one
/-- The twist's constant: 3 over ξ. -/
def twistB : Fp2 := ⟨0x38e7ecccd1dcff67, 0x65f0b37d93ce0d3e, 0xd749d0dd22ac00aa, 0x0141b9ce4a688d4d, 0x3bf938e377b802a8, 0x020b1b273633535d, 0x26b7edf049755260, 0x2514c6324384a86d⟩
/-- ξ to the power (p-1)/6. -/
def xiToPMinus1Over6 : Fp2 := ⟨0xa222ae234c492d72, 0xd00f02a4565de15b, 0xdc2ff3a253dfc926, 0x10a75716b3899551, 0xaf9ba69633144907, 0xca6b1d7387afb78a, 0x11bded5ef08a2087, 0x02f34d751a1f3a7c⟩
/-- ξ to the power (p-1)/3. -/
def xiToPMinus1Over3 : Fp2 := ⟨0x6e849f1ea0aa4757, 0xaa1c7b6d89f89141, 0xb6e713cdfae0ca3a, 0x26694fbb4e82ebc3, 0xb5773b104563ab30, 0x347f91c8a9aa6454, 0x7a007127242e0991, 0x1956bcd8118214ec⟩
/-- ξ to the power (p-1)/2. -/
def xiToPMinus1Over2 : Fp2 := ⟨0xa1d77ce45ffe77c7, 0x07affd117826d1db, 0x6d16bd27bb7edc6b, 0x2c87200285defecc, 0xe4bbdd0c2936b629, 0xbb30f162e133bacb, 0x31a9d1b6f9645366, 0x253570bea500f8dd⟩
/-- ξ to the power (2p-2)/3. -/
def xiTo2PMinus2Over3 : Fp2 := ⟨0x5dddfd154bd8c949, 0x62cb29a5a4445b60, 0x37bc870a0c7dd2b9, 0x24830a9d3171f0fd, 0x7361d77f843abe92, 0xa5bb2bd3273411fb, 0x9c941f314b3e2399, 0x15df9cddbb9fd3ec⟩
/-- ξ to the power (p²-1)/3, which lies in the base field. -/
def xiToPSquaredMinus1Over3 : Fp := ⟨0x3350c88e13e80b9c, 0x7dce557cdb5e56b9, 0x6001b4b8b615564a, 0x2682e617020217e0⟩
/-- ξ to the power (2p²-2)/3, which lies in the base field. -/
def xiTo2PSquaredMinus2Over3 : Fp := ⟨0x71930c11d782e155, 0xa6bb947cffbe3323, 0xaa303344d4741444, 0x2c3b3f0d26594943⟩
/-- ξ to the power (p²-1)/6, which lies in the base field. -/
def xiToPSquaredMinus1Over6 : Fp := ⟨0xca8d800500fa1bf2, 0xf0c5d61468b39769, 0x0e201271ad0d4418, 0x04290f65bad856e6⟩

@[inline] def isZero (a : Fp2) : Bool := (a.x0 ||| a.x1 ||| a.x2 ||| a.x3 ||| a.y0 ||| a.y1 ||| a.y2 ||| a.y3) == 0

def add (a b : Fp2) : Fp2 := of (a.im.add b.im) (a.re.add b.re)
def sub (a b : Fp2) : Fp2 := of (a.im.sub b.im) (a.re.sub b.re)
def neg (a : Fp2) : Fp2 := of a.im.neg a.re.neg
def double (a : Fp2) : Fp2 := of a.im.double a.re.double
/-- The conjugate: `-x i + y`. -/
def conj (a : Fp2) : Fp2 := of a.im.neg a.re

/-- `(x i + y)(x' i + y') = (x y' + y x') i + (y y' - x x')`, with three products. -/
def mul (a b : Fp2) : Fp2 :=
  let tx := (a.im.add a.re).mul (b.im.add b.re)
  let xx := a.im.mul b.im
  let yy := a.re.mul b.re
  of ((tx.sub xx).sub yy) (yy.sub xx)

/-- `(x i + y)² = 2 x y i + (y + x)(y - x)`. -/
def square (a : Fp2) : Fp2 :=
  let t := a.im.mul a.re
  of (t.add t) ((a.re.add a.im).mul (a.re.sub a.im))

/-- By a number of the base field. -/
def scale (a : Fp2) (k : Fp) : Fp2 := of (a.im.mul k) (a.re.mul k)

/-- By ξ = i + 9: `(x i + y)(i + 9) = (9 x + y) i + (9 y - x)`. -/
def mulXi (a : Fp2) : Fp2 :=
  let x := a.im
  let y := a.re
  let x8 := x.double.double.double
  let y8 := y.double.double.double
  of ((x8.add x).add y) ((y8.add y).sub x)

/-- The inverse: the conjugate over the norm `x² + y²`. -/
def inverse (a : Fp2) : Fp2 :=
  let t := Fp.inverse ((Fp.times a.im a.im).add (Fp.times a.re a.re))
  of (Fp.times a.im.neg t) (Fp.times a.re t)

end Fp2

/-- A number of the cubic extension over the quadratic: `x τ² + y τ + z` with `τ³ = ξ`. -/
structure Fp6 where
  x : Fp2
  y : Fp2
  z : Fp2
  deriving BEq, Inhabited

namespace Fp6

def zero : Fp6 := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩
def one : Fp6 := ⟨Fp2.zero, Fp2.zero, Fp2.one⟩

def add (a b : Fp6) : Fp6 := ⟨a.x.add b.x, a.y.add b.y, a.z.add b.z⟩
def sub (a b : Fp6) : Fp6 := ⟨a.x.sub b.x, a.y.sub b.y, a.z.sub b.z⟩
def neg (a : Fp6) : Fp6 := ⟨a.x.neg, a.y.neg, a.z.neg⟩

/-- Karatsuba's way with three terms ("Multiplication and Squaring on Pairing-Friendly Fields"). -/
def mul (a b : Fp6) : Fp6 :=
  let v0 := a.z.mul b.z
  let v1 := a.y.mul b.y
  let v2 := a.x.mul b.x
  let tz := ((((a.x.add a.y).mul (b.x.add b.y)).sub v1).sub v2).mulXi.add v0
  let ty := ((((a.y.add a.z).mul (b.y.add b.z)).sub v0).sub v1).add v2.mulXi
  let tx := ((((a.x.add a.z).mul (b.x.add b.z)).sub v0).add v1).sub v2
  ⟨tx, ty, tz⟩

def square (a : Fp6) : Fp6 :=
  let v0 := a.z.square
  let v1 := a.y.square
  let v2 := a.x.square
  let c0 := ((((a.x.add a.y).square).sub v1).sub v2).mulXi.add v0
  let c1 := ((((a.y.add a.z).square).sub v0).sub v1).add v2.mulXi
  let c2 := ((((a.x.add a.z).square).sub v0).add v1).sub v2
  ⟨c2, c1, c0⟩

/-- By a number of the quadratic extension. -/
def scale (a : Fp6) (k : Fp2) : Fp6 := ⟨a.x.mul k, a.y.mul k, a.z.mul k⟩
/-- By a number of the base field. -/
def scaleBase (a : Fp6) (k : Fp) : Fp6 := ⟨a.x.scale k, a.y.scale k, a.z.scale k⟩

/-- By τ: `τ (x τ² + y τ + z) = y τ² + z τ + x ξ`. -/
def mulTau (a : Fp6) : Fp6 := ⟨a.y, a.z, a.x.mulXi⟩

/-- The inverse ("Implementing cryptographic pairings", M. Scott, 3.2): three numbers `A`, `B`, `C` whose
product with this one is its norm, a number of the quadratic extension, which is then inverted there. -/
def inverse (a : Fp6) : Fp6 :=
  let A := a.z.square.sub (a.x.mul a.y).mulXi
  let B := a.x.square.mulXi.sub (a.y.mul a.z)
  let C := a.y.square.sub (a.x.mul a.z)
  let F := (((C.mul a.y).mulXi).add (A.mul a.z)).add (B.mul a.x).mulXi
  let f := F.inverse
  ⟨C.mul f, B.mul f, A.mul f⟩

/-- The power `p`. -/
def frobenius (a : Fp6) : Fp6 :=
  ⟨a.x.conj.mul Fp2.xiTo2PMinus2Over3, a.y.conj.mul Fp2.xiToPMinus1Over3, a.z.conj⟩

/-- The power `p²`. -/
def frobeniusP2 (a : Fp6) : Fp6 :=
  ⟨a.x.scale Fp2.xiTo2PSquaredMinus2Over3, a.y.scale Fp2.xiToPSquaredMinus1Over3, a.z⟩

end Fp6

/-- A number of the field the pairing lands in: `x ω + y` with `ω² = τ`. -/
structure Fp12 where
  x : Fp6
  y : Fp6
  deriving BEq, Inhabited

namespace Fp12

def one : Fp12 := ⟨Fp6.zero, Fp6.one⟩

def mul (a b : Fp12) : Fp12 :=
  ⟨(a.x.mul b.y).add (b.x.mul a.y), (a.y.mul b.y).add (a.x.mul b.x).mulTau⟩

def square (a : Fp12) : Fp12 :=
  let v0 := a.x.mul a.y
  let ty := (((a.x.add a.y).mul (a.x.mulTau.add a.y)).sub v0).sub v0.mulTau
  ⟨v0.add v0, ty⟩

/-- The conjugate, which is also the power `p⁶`. -/
def conj (a : Fp12) : Fp12 := ⟨a.x.neg, a.y⟩

def inverse (a : Fp12) : Fp12 :=
  let t := (a.y.square.sub a.x.square.mulTau).inverse
  ⟨a.x.neg.mul t, a.y.mul t⟩

def frobenius (a : Fp12) : Fp12 := ⟨a.x.frobenius.scale Fp2.xiToPMinus1Over6, a.y.frobenius⟩
def frobeniusP2 (a : Fp12) : Fp12 := ⟨a.x.frobeniusP2.scaleBase Fp2.xiToPSquaredMinus1Over6, a.y.frobeniusP2⟩

/-- To the power of the number the curve is made from, by squaring: `left` bits of it from the top. -/
def powerOfParameter (a : Fp12) : Nat → Fp12 → Fp12
  | 0, acc => acc
  | left + 1, acc =>
    let acc := acc.square
    powerOfParameter a left (if (Fp.parameter >>> left.toUInt64) &&& 1 == 1 then acc.mul a else acc)

def exp (a : Fp12) : Fp12 := powerOfParameter a 63 one

end Fp12

/-! ## The curve, y² = x³ + 3 -/

/-- A point of the curve over the base field, in Jacobian coordinates: `(x / z², y / z³)`, and the point
at infinity when `z` is nothing. -/
structure G1 where
  x : Fp
  y : Fp
  z : Fp
  deriving Inhabited

namespace G1

def infinity : G1 := ⟨Fp.one, Fp.one, Fp.zero⟩

def double (p : G1) : G1 :=
  if p.z.isZero then p else
  let a := Fp.times p.x p.x
  let b := Fp.times p.y p.y
  let c := Fp.times b b
  let t := (p.x.add b)
  let d := (((Fp.times t t).sub a).sub c).double
  let e := (a.double).add a
  let f := Fp.times e e
  let x := f.sub d.double
  ⟨x, (Fp.times e (d.sub x)).sub c.double.double.double, (Fp.times p.y p.z).double⟩

def add (p q : G1) : G1 :=
  if p.z.isZero then q else if q.z.isZero then p else
  let z1z1 := Fp.times p.z p.z
  let z2z2 := Fp.times q.z q.z
  let u1 := Fp.times p.x z2z2
  let u2 := Fp.times q.x z1z1
  let s1 := Fp.times (Fp.times p.y q.z) z2z2
  let s2 := Fp.times (Fp.times q.y p.z) z1z1
  let h := u2.sub u1
  let r := (s2.sub s1).double
  if h.isZero then (if r.isZero then double p else infinity) else
  let i := Fp.times h.double h.double
  let j := Fp.times h i
  let v := Fp.times u1 i
  let x := ((Fp.times r r).sub j).sub v.double
  let zz := p.z.add q.z
  ⟨x, (Fp.times r (v.sub x)).sub (Fp.times s1 j).double, Fp.times (((Fp.times zz zz).sub z1z1).sub z2z2) h⟩

/-- `p` times a plain number of four words: `left` bits of it from the top. -/
def times (p : G1) (n : Fp) : Nat → G1 → G1
  | 0, acc => acc
  | left + 1, acc =>
    let acc := acc.double
    times p n left (if Fp.bit n left then acc.add p else acc)

def mul (p : G1) (n : Fp) : G1 := times p n 256 infinity

/-- The point as two numbers, and (0, 0) for the point at infinity. -/
def affine (p : G1) : Fp × Fp :=
  if p.z.isZero then (Fp.zero, Fp.zero) else
  let zi := p.z.inverse
  let zi2 := Fp.times zi zi
  (Fp.times p.x zi2, Fp.times p.y (Fp.times zi2 zi))

/-- A point from the 64 bytes at `off`: two numbers under the prime that are on the curve, or two zeros
for the point at infinity. Bytes that are not there count as zeros. -/
def read (b : @& ByteArray) (off : Nat) : Option G1 := do
  let padded := if off + 64 ≤ b.size then b else b ++ ByteArray.mk (Array.replicate (off + 64 - b.size) 0)
  let x ← Fp.read padded off
  let y ← Fp.read padded (off + 32)
  if x.isZero && y.isZero then pure infinity
  else if Fp.times y y == (Fp.times (Fp.times x x) x).add Fp.three then pure ⟨x, y, Fp.one⟩
  else none

def write (out : ByteArray) (p : G1) : ByteArray :=
  let (x, y) := p.affine
  Fp.write (Fp.write out x) y

end G1

/-- A point of the twisted curve over the quadratic extension, `y² = x³ + 3/ξ`, in Jacobian coordinates
with `t = z²` kept beside them. -/
structure G2 where
  x : Fp2
  y : Fp2
  z : Fp2
  t : Fp2
  deriving Inhabited

namespace G2

def infinity : G2 := ⟨Fp2.one, Fp2.one, Fp2.zero, Fp2.zero⟩

def double (p : G2) : G2 :=
  if p.z.isZero then p else
  let a := p.x.square
  let b := p.y.square
  let c := b.square
  let d := ((((p.x.add b).square).sub a).sub c).double
  let e := a.double.add a
  let f := e.square
  let x := f.sub d.double
  let z := (p.y.mul p.z).double
  ⟨x, (e.mul (d.sub x)).sub c.double.double.double, z, z.square⟩

def add (p q : G2) : G2 :=
  if p.z.isZero then q else if q.z.isZero then p else
  let z1z1 := p.z.square
  let z2z2 := q.z.square
  let u1 := p.x.mul z2z2
  let u2 := q.x.mul z1z1
  let s1 := (p.y.mul q.z).mul z2z2
  let s2 := (q.y.mul p.z).mul z1z1
  let h := u2.sub u1
  let r := (s2.sub s1).double
  if h.isZero then (if r.isZero then double p else infinity) else
  let i := h.double.square
  let j := h.mul i
  let v := u1.mul i
  let x := (r.square.sub j).sub v.double
  let z := ((((p.z.add q.z).square).sub z1z1).sub z2z2).mul h
  ⟨x, (r.mul (v.sub x)).sub (s1.mul j).double, z, z.square⟩

def times (p : G2) (n : Fp) : Nat → G2 → G2
  | 0, acc => acc
  | left + 1, acc =>
    let acc := acc.double
    times p n left (if Fp.bit n left then acc.add p else acc)

def mul (p : G2) (n : Fp) : G2 := times p n 256 infinity

/-- A point from the 128 bytes at `off`, as the pairing contract is given it: the two parts of `x`, the
imaginary first, then of `y`. It must be on the twisted curve and in the subgroup the pairing is defined
on, which is checked the long way, by multiplying by the group's order. -/
def read (b : @& ByteArray) (off : Nat) : Option G2 := do
  let xi ← Fp.read b off
  let xr ← Fp.read b (off + 32)
  let yi ← Fp.read b (off + 64)
  let yr ← Fp.read b (off + 96)
  let x := Fp2.of xi xr
  let y := Fp2.of yi yr
  if x.isZero && y.isZero then pure infinity
  else if y.square != (x.square.mul x).add Fp2.twistB then none
  else
    let p : G2 := ⟨x, y, Fp2.one, Fp2.one⟩
    if (p.mul Fp.order).z.isZero then pure p else none

end G2

/-! ## The pairing -/

/-- What a step of the Miller loop gives: three coefficients of the line through the points, and the point
moved on. -/
structure Line where
  a : Fp2
  b : Fp2
  c : Fp2
  r : G2

/-- The line through `r` and `p`, both on the twist, at `q` (by its two plain coordinates `qx`, `qy`), and
their sum: the mixed addition of "Faster Computation of the Tate Pairing" (Arène, Lange, Naehrig,
Ritzenthaler). `p` has `z = 1`; `r2` is the square of its `y`. -/
def lineAdd (r p : G2) (qx qy : Fp) (r2 : Fp2) : Line :=
  let B := p.x.mul r.t
  let D := ((((p.y.add r.z).square).sub r2).sub r.t).mul r.t
  let H := B.sub r.x
  let I := H.square
  let E := I.double.double
  let J := H.mul E
  let L1 := (D.sub r.y).sub r.y
  let V := r.x.mul E
  let x := (L1.square.sub J).sub V.double
  let z := (((r.z.add H).square).sub r.t).sub I
  let y := ((V.sub x).mul L1).sub (r.y.mul J).double
  let t := z.square
  let a := (L1.mul p.x).double.sub ((((p.y.add z).square).sub r2).sub t)
  ⟨a, (L1.neg.scale qx).double, (z.scale qy).double, ⟨x, y, z, t⟩⟩

/-- The tangent at `r` on the twist, at `q`, and `r` doubled. -/
def lineDouble (r : G2) (qx qy : Fp) : Line :=
  let A := r.x.square
  let B := r.y.square
  let C := B.square
  let D := ((((r.x.add B).square).sub A).sub C).double
  let E := A.double.add A
  let G := E.square
  let x := G.sub D.double
  let z := (((r.y.add r.z).square).sub B).sub r.t
  let y := ((D.sub x).mul E).sub C.double.double.double
  let t := z.square
  let a := ((((r.x.add E).square).sub A).sub G).sub B.double.double
  ⟨a, ((E.mul r.t).double.neg).scale qx, ((z.mul r.t).double).scale qy, ⟨x, y, z, t⟩⟩

/-- `f` times a line, which as a number of the big field has only three coefficients that are not nothing. -/
def mulLine (f : Fp12) (l : Line) : Fp12 :=
  let a2 : Fp6 := (⟨Fp2.zero, l.a, l.b⟩ : Fp6).mul f.x
  let t3 := f.y.scale l.c
  let t2 : Fp6 := ⟨Fp2.zero, l.a, l.b.add l.c⟩
  let x := (((f.x.add f.y).mul t2).sub a2).sub t3
  ⟨x, t3.add a2.mulTau⟩

/-- The Miller loop for one pair: `q` on the twist with `z = 1`, `p` on the curve by its two plain
coordinates. `i` counts down through the digits of the loop's number. -/
def loop (q minusQ : G2) (px py : Fp) (r2 : Fp2) : Nat → G2 → Fp12 → G2 × Fp12
  | 0, r, f => (r, f)
  | i + 1, r, f =>
    let l := lineDouble r px py
    let f := mulLine (if i + 2 == Fp.loopDigits.size then f else f.square) l
    let digit := Fp.loopDigits[i]!
    if digit == 1 then
      let l2 := lineAdd l.r q px py r2
      loop q minusQ px py r2 i l2.r (mulLine f l2)
    else if digit == 2 then
      let l2 := lineAdd l.r minusQ px py r2
      loop q minusQ px py r2 i l2.r (mulLine f l2)
    else loop q minusQ px py r2 i l.r f

/-- The Miller loop and the two steps after it, for a `q` and a `p` neither of which is the point at
infinity, both with `z = 1`. -/
def miller (q : G2) (px py : Fp) : Fp12 :=
  let minusQ : G2 := { q with y := q.y.neg }
  let (r, f) := loop q minusQ px py q.y.square (Fp.loopDigits.size - 1) q Fp12.one
  -- `q` raised to the power `p`, and the negative of `q` raised to `p²`, each brought back to the twist.
  let q1 : G2 := ⟨q.x.conj.mul Fp2.xiToPMinus1Over3, q.y.conj.mul Fp2.xiToPMinus1Over2, Fp2.one, Fp2.one⟩
  let minusQ2 : G2 := ⟨q.x.scale Fp2.xiToPSquaredMinus1Over3, q.y, Fp2.one, Fp2.one⟩
  let l := lineAdd r q1 px py q1.y.square
  let f := mulLine f l
  let l2 := lineAdd l.r minusQ2 px py minusQ2.y.square
  mulLine f l2

/-- The power `(p¹² - 1) / r`, which takes what the Miller loop gives to a number that depends only on the
pairing: an easy part by conjugation and one inverse, then the hard part by the chain of Devegili, Scott
and Dahab, with three powers of the curve's number. -/
def finalExponentiation (f : Fp12) : Fp12 :=
  let t1 := f.conj.mul f.inverse
  let t1 := t1.mul t1.frobeniusP2
  let fp := t1.frobenius
  let fp2 := t1.frobeniusP2
  let fp3 := fp2.frobenius
  let fu := t1.exp
  let fu2 := fu.exp
  let fu3 := fu2.exp
  let y3 := fu.frobenius.conj
  let fu2p := fu2.frobenius
  let fu3p := fu3.frobenius
  let y2 := fu2.frobeniusP2
  let y0 := (fp.mul fp2).mul fp3
  let y1 := t1.conj
  let y5 := fu2.conj
  let y4 := (fu.mul fu2p).conj
  let y6 := (fu3.mul fu3p).conj
  let t0 := (y6.square.mul y4).mul y5
  let t1 := (y3.mul y5).mul t0
  let t0 := t0.mul y2
  let t1 := (t1.square.mul t0).square
  let t0 := t1.mul y1
  let t1 := t1.mul y0
  t0.square.mul t1

/-! ## The three contracts -/

/-- ECADD: two points of 64 bytes each, their sum. None if either is not a point. -/
def addPoints (input : @& ByteArray) : Option ByteArray := do
  let p ← G1.read input 0
  let q ← G1.read input 64
  pure (G1.write (ByteArray.emptyWithCapacity 64) (p.add q))

/-- ECMUL: a point and a number of 32 bytes, the point that many times. None if it is not a point. -/
def mulPoint (input : @& ByteArray) : Option ByteArray := do
  let p ← G1.read input 0
  let padded := if 96 ≤ input.size then input else input ++ ByteArray.mk (Array.replicate (96 - input.size) 0)
  let word (at_ : Nat) : UInt64 := (List.range 8).foldl (fun n i => (n <<< 8) ||| (padded.get! (at_ + i)).toUInt64) 0
  pure (G1.write (ByteArray.emptyWithCapacity 64) (p.mul ⟨word 88, word 80, word 72, word 64⟩))

/-- The pairs of a pairing check, multiplied together before the one final exponentiation: `left` of them
from `off`. None if a point is not one. -/
def pairs (input : @& ByteArray) : Nat → Nat → Fp12 → Option Fp12
  | 0, _, f => some f
  | left + 1, off, f => do
    let p ← G1.read input off
    let q ← G2.read input (off + 64)
    if p.z.isZero || q.z.isZero then pairs input left (off + 192) f
    else
      let px := p.x
      let py := p.y
      pairs input left (off + 192) (f.mul (miller q px py))

/-- The pairing check: pairs of 192 bytes, a point of the curve and a point of the twist; whether the
product of their pairings is one. None if the input is not whole pairs or a point is not one. -/
def pairingCheck (input : @& ByteArray) : Option Bool := do
  if input.size % 192 != 0 then none
  let f ← pairs input (input.size / 192) 0 Fp12.one
  pure (finalExponentiation f == Fp12.one)

end Fast.Bn254
