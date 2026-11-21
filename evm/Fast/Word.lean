/-! The EVM's 256-bit word for the fast engine: four machine words, the least significant first, and the
arithmetic on them that needs no division. Everything here is meant to be inlined into the interpreter's
loop, where a word lives in four variables and is never built as an object. `fast-word-test` holds each
operation to the same one on `Nat`. -/

namespace Fast

structure Word where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving BEq, Inhabited

namespace Word

@[inline] def zero : Word := ⟨0, 0, 0, 0⟩
@[inline] def one : Word := ⟨1, 0, 0, 0⟩
@[inline] def ones : Word := ⟨0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff⟩
@[inline] def ofUInt64 (x : UInt64) : Word := ⟨x, 0, 0, 0⟩
@[inline] def ofBool (b : Bool) : Word := ⟨if b then 1 else 0, 0, 0, 0⟩

def toNat (x : Word) : Nat :=
  x.w0.toNat + x.w1.toNat <<< 64 + x.w2.toNat <<< 128 + x.w3.toNat <<< 192

def ofNat (n : Nat) : Word :=
  ⟨n.toUInt64, (n >>> 64).toUInt64, (n >>> 128).toUInt64, (n >>> 192).toUInt64⟩

@[inline] def isZero (x : Word) : Bool := (x.w0 ||| x.w1 ||| x.w2 ||| x.w3) == 0

/-- Whether the word is a number under 2^64, which is what an offset, a length or a count must be to be
usable at all. -/
@[inline] def small (x : Word) : Bool := (x.w1 ||| x.w2 ||| x.w3) == 0

@[inline] def negative (x : Word) : Bool := x.w3 >>> 63 == 1

/-- The carry out of `x + y + c` whose sum, cut to 64 bits, is `s`. -/
@[inline] def carry (x y s : UInt64) : UInt64 := ((x &&& y) ||| ((x ||| y) &&& ~~~s)) >>> 63

/-- The borrow out of `x - y - b` whose difference, cut to 64 bits, is `d`. -/
@[inline] def borrow (x y d : UInt64) : UInt64 := ((~~~x &&& y) ||| ((~~~x ||| y) &&& d)) >>> 63

@[inline] def add (x y : Word) : Word :=
  let s0 := x.w0 + y.w0
  let c0 := carry x.w0 y.w0 s0
  let s1 := x.w1 + y.w1 + c0
  let c1 := carry x.w1 y.w1 s1
  let s2 := x.w2 + y.w2 + c1
  let c2 := carry x.w2 y.w2 s2
  ⟨s0, s1, s2, x.w3 + y.w3 + c2⟩

@[inline] def sub (x y : Word) : Word :=
  let d0 := x.w0 - y.w0
  let b0 := borrow x.w0 y.w0 d0
  let d1 := x.w1 - y.w1 - b0
  let b1 := borrow x.w1 y.w1 d1
  let d2 := x.w2 - y.w2 - b1
  let b2 := borrow x.w2 y.w2 d2
  ⟨d0, d1, d2, x.w3 - y.w3 - b2⟩

@[inline] def neg (x : Word) : Word := sub zero x

@[inline] def lt (x y : Word) : Bool :=
  if x.w3 != y.w3 then x.w3 < y.w3 else if x.w2 != y.w2 then x.w2 < y.w2
  else if x.w1 != y.w1 then x.w1 < y.w1 else x.w0 < y.w0

@[inline] def gt (x y : Word) : Bool := lt y x

/-- Less than, as two's-complement numbers. -/
@[inline] def slt (x y : Word) : Bool :=
  if x.negative != y.negative then x.negative else lt x y

@[inline] def sgt (x y : Word) : Bool := slt y x

@[inline] def eq (x y : Word) : Bool :=
  ((x.w0 ^^^ y.w0) ||| (x.w1 ^^^ y.w1) ||| (x.w2 ^^^ y.w2) ||| (x.w3 ^^^ y.w3)) == 0

@[inline] def and (x y : Word) : Word := ⟨x.w0 &&& y.w0, x.w1 &&& y.w1, x.w2 &&& y.w2, x.w3 &&& y.w3⟩
@[inline] def or (x y : Word) : Word := ⟨x.w0 ||| y.w0, x.w1 ||| y.w1, x.w2 ||| y.w2, x.w3 ||| y.w3⟩
@[inline] def xor (x y : Word) : Word := ⟨x.w0 ^^^ y.w0, x.w1 ^^^ y.w1, x.w2 ^^^ y.w2, x.w3 ^^^ y.w3⟩
@[inline] def not (x : Word) : Word := ⟨~~~x.w0, ~~~x.w1, ~~~x.w2, ~~~x.w3⟩

/-- The machine word numbered `i`, and nothing for a number that names none. -/
@[inline] def limb (x : Word) (i : UInt64) : UInt64 :=
  if i == 0 then x.w0 else if i == 1 then x.w1 else if i == 2 then x.w2 else if i == 3 then x.w3 else 0

/-- `x` moved up by `whole` machine words and `bits` bits, `bits` under 64: the machine word `i` of the
result. A shift of a machine word by 64 is no shift to the processor, so no bits is its own case. -/
@[inline] def upLimb (x : Word) (whole bits i : UInt64) : UInt64 :=
  if i < whole then 0 else
  let high := x.limb (i - whole) <<< bits
  if bits == 0 || i == whole then high else high ||| (x.limb (i - whole - 1) >>> (64 - bits))

@[inline] def downLimb (x : Word) (whole bits i : UInt64) : UInt64 :=
  let low := x.limb (i + whole) >>> bits
  if bits == 0 then low else low ||| (x.limb (i + whole + 1) <<< (64 - bits))

/-- `x` shifted left by `n` bits, for `n` under 256. -/
@[inline] def shlSmall (x : Word) (n : UInt64) : Word :=
  let whole := n >>> 6
  let bits := n &&& 63
  ⟨x.upLimb whole bits 0, x.upLimb whole bits 1, x.upLimb whole bits 2, x.upLimb whole bits 3⟩

/-- `x` shifted right by `n` bits, for `n` under 256. -/
@[inline] def shrSmall (x : Word) (n : UInt64) : Word :=
  let whole := n >>> 6
  let bits := n &&& 63
  ⟨x.downLimb whole bits 0, x.downLimb whole bits 1, x.downLimb whole bits 2, x.downLimb whole bits 3⟩

/-- SHL: `x` shifted left by `shift` bits. -/
@[inline] def shl (shift x : Word) : Word :=
  if shift.small && shift.w0 < 256 then x.shlSmall shift.w0 else zero

/-- SHR: `x` shifted right by `shift` bits, nothing coming in at the top. -/
@[inline] def shr (shift x : Word) : Word :=
  if shift.small && shift.w0 < 256 then x.shrSmall shift.w0 else zero

/-- SAR: `x` shifted right by `shift` bits, its sign coming in at the top. -/
@[inline] def sar (shift x : Word) : Word :=
  if shift.small && shift.w0 < 256 then
    let moved := x.shrSmall shift.w0
    if x.negative && shift.w0 != 0 then moved.or (ones.shlSmall (256 - shift.w0)) else moved
  else if x.negative then ones else zero

/-- BYTE: the byte numbered `i` of `x`, counted from the most significant, and nothing past the 32nd. -/
@[inline] def byte (i x : Word) : Word :=
  if i.small && i.w0 < 32 then ofUInt64 ((x.shrSmall ((31 - i.w0) <<< 3)).w0 &&& 0xff) else zero

/-- SIGNEXTEND: `x` read as a number of `b + 1` bytes and widened with its sign. -/
@[inline] def signExtend (b x : Word) : Word :=
  if b.small && b.w0 < 31 then
    let bit := (b.w0 <<< 3) + 7
    let low := ones.shrSmall (255 - bit)
    if ((x.shrSmall bit).w0 &&& 1) == 1 then x.or low.not else x.and low
  else x

/-- The zero bits above the highest one of a machine word, 64 for nothing. -/
@[inline] def leadingZeros (x : UInt64) : UInt64 :=
  if x == 0 then 64 else
  let n : UInt64 := 0
  let (n, x) := if x >>> 32 == 0 then (n + 32, x <<< 32) else (n, x)
  let (n, x) := if x >>> 48 == 0 then (n + 16, x <<< 16) else (n, x)
  let (n, x) := if x >>> 56 == 0 then (n + 8, x <<< 8) else (n, x)
  let (n, x) := if x >>> 60 == 0 then (n + 4, x <<< 4) else (n, x)
  let (n, x) := if x >>> 62 == 0 then (n + 2, x <<< 2) else (n, x)
  if x >>> 63 == 0 then n + 1 else n

/-- CLZ: the zero bits above the highest one, 256 for nothing. -/
@[inline] def clz (x : Word) : Word :=
  ofUInt64 (
    if x.w3 != 0 then leadingZeros x.w3 else if x.w2 != 0 then 64 + leadingZeros x.w2
    else if x.w1 != 0 then 128 + leadingZeros x.w1 else 192 + leadingZeros x.w0)

/-- The bits of `x` in use: 0 for nothing, 256 for a set top bit. -/
@[inline] def bits (x : Word) : UInt64 := 256 - (clz x).w0

/-- The 128 bits of a product of machine words, low half first, handed to what follows: there is no such
multiplication to call, so it is made of four of 32 bits by 32. -/
@[inline] def mulWide {α : Type} (x y : UInt64) (k : UInt64 → UInt64 → α) : α :=
  let m : UInt64 := 0xffffffff
  let x0 := x &&& m
  let x1 := x >>> 32
  let y0 := y &&& m
  let y1 := y >>> 32
  let p00 := x0 * y0
  let p01 := x0 * y1
  let p10 := x1 * y0
  let p11 := x1 * y1
  let mid := (p00 >>> 32) + (p01 &&& m) + (p10 &&& m)
  k ((p00 &&& m) ||| (mid <<< 32)) (p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32))

/-- `x * y + c + d` as 128 bits, low half first: it always fits. -/
@[inline] def mac {α : Type} (x y c d : UInt64) (k : UInt64 → UInt64 → α) : α :=
  mulWide x y fun lo hi =>
  let s := lo + c
  let hi := hi + (if s < lo then 1 else 0)
  let t := s + d
  k t (hi + (if t < s then 1 else 0))

/-- MUL: the low 256 bits of the product. -/
def mul (x y : Word) : Word :=
  mac x.w0 y.w0 0 0 fun r0 c =>
  mac x.w0 y.w1 c 0 fun r1 c =>
  mac x.w0 y.w2 c 0 fun r2 c =>
  let r3 := x.w0 * y.w3 + c
  mac x.w1 y.w0 r1 0 fun r1 c =>
  mac x.w1 y.w1 r2 c fun r2 c =>
  let r3 := x.w1 * y.w2 + r3 + c
  mac x.w2 y.w0 r2 0 fun r2 c =>
  let r3 := x.w2 * y.w1 + r3 + c
  ⟨r0, r1, r2, x.w3 * y.w0 + r3⟩

/-- EXP: `x` to the power `e`, cut to 256 bits, by squaring. -/
def exp (x e : Word) : Word := Id.run do
  let mut result := one
  let mut base := x
  let mut e := e
  for _ in [0:256] do
    if e.isZero then break
    if e.w0 &&& 1 == 1 then result := mul result base
    base := mul base base
    e := e.shrSmall 1
  return result

/-- The bytes a number takes, none for nothing: what EXP's exponent is charged by. -/
@[inline] def byteLength (x : Word) : UInt64 := (x.bits + 7) >>> 3

end Word
end Fast
