import Fast.Word

/-! Division for the fast engine's words, and the two operations that need more than 256 bits on the way
(ADDMOD and MULMOD). Numbers here are arrays of 32-bit digits, least significant first, which the runtime
holds without a box for each; the division is the long division of Knuth's algorithm D on those digits,
with 64-bit arithmetic for a digit at a time. Every loop is a function that calls itself with its numbers
as arguments, because a `for` over several changing variables builds a tuple at each turn. These are the
costly operations and they allocate a few small arrays each, which the cheap ones in `Fast/Word.lean` never
do. `fast-word-test` holds each to `Nat`. -/

namespace Fast

/-- A number as 32-bit digits, least significant first. -/
abbrev Digits := Array UInt32

namespace Digits

@[inline] def digit (d : @& Digits) (i : Nat) : UInt64 := (d.getD i 0).toUInt64

def ofWord (x : Word) : Digits :=
  #[x.w0.toUInt32, (x.w0 >>> 32).toUInt32, x.w1.toUInt32, (x.w1 >>> 32).toUInt32,
    x.w2.toUInt32, (x.w2 >>> 32).toUInt32, x.w3.toUInt32, (x.w3 >>> 32).toUInt32]

@[inline] def pair (d : @& Digits) (i : Nat) : UInt64 := d.digit i ||| (d.digit (i + 1) <<< 32)

/-- The 256 bits from digit `i` up. -/
def toWord (d : @& Digits) (i : Nat := 0) : Word := ⟨d.pair i, d.pair (i + 2), d.pair (i + 4), d.pair (i + 6)⟩

/-- How many of the first `n` digits are in use: `n` without the zeros at the top. -/
def used (d : @& Digits) : Nat → Nat
  | 0 => 0
  | n + 1 => if d.digit n == 0 then used d n else n + 1

/-- The digits of `d` under `len`, shifted up by `s` bits (`s` under 32), written from `at` in `out`,
`count` of them from digit `i`: one more than `len` holds the bits that leave the top. -/
def shiftInto (d : @& Digits) (len : Nat) (s : UInt64) (start : Nat) : Nat → Nat → Digits → Digits
  | 0, _, out => out
  | count + 1, i, out =>
    let high := if i < len then d.digit i else 0
    let low := if i == 0 then 0 else d.digit (i - 1)
    shiftInto d len s start count (i + 1) (out.set! (start + i) ((((high <<< 32) ||| low) <<< s) >>> 32).toUInt32)

/-- One digit as divisor, the long division of school: the quotient's digits written from `j` down, then
the remainder at `m`. -/
def byOne (u : @& Digits) (d : UInt64) (m : Nat) : Nat → UInt64 → Digits → Digits
  | 0, k, q => q.set! m k.toUInt32
  | j + 1, k, q =>
    let t := (k <<< 32) ||| u.digit j
    byOne u d m j (t % d) (q.set! j (t / d).toUInt32)

/-- The divisor added back to what is left, when a digit of the quotient was guessed one too high. -/
def addBack (vn : @& Digits) (n j : Nat) : Nat → UInt64 → Digits → Digits
  | 0, c, w => w.set! (j + n) (w.digit (j + n) + c).toUInt32
  | left + 1, c, w =>
    let i := n - (left + 1)
    let t := w.digit (i + j) + vn.digit i + c
    addBack vn n j left (t >>> 32) (w.set! (i + j) t.toUInt32)

/-- The guess `qhat` times the divisor taken off what is left, from digit `j`; then the digit of the
quotient written at `qAt`, one less with the divisor added back if the guess was one too high. -/
def takeOff (vn : @& Digits) (n j qAt : Nat) (qhat : UInt64) : Nat → UInt64 → UInt64 → Digits → Digits
  | 0, carry, borrow, w =>
    let t := w.digit (j + n) - carry - borrow
    let w := w.set! (j + n) t.toUInt32
    if (t >>> 32) &&& 1 == 1 then (addBack vn n j n 0 w).set! qAt (qhat - 1).toUInt32
    else w.set! qAt qhat.toUInt32
  | left + 1, carry, borrow, w =>
    let i := n - (left + 1)
    let p := qhat * vn.digit i + carry
    let t := w.digit (i + j) - (p &&& 0xffffffff) - borrow
    takeOff vn n j qAt qhat left (p >>> 32) ((t >>> 32) &&& 1) (w.set! (i + j) t.toUInt32)

/-- A guess at a digit of the quotient from the top two digits of what is left, brought down while it is
too big: at most twice. -/
@[inline] def guess (num v1 v2 next : UInt64) : UInt64 :=
  let b : UInt64 := 0x100000000
  let qhat := num / v1
  let rhat := num % v1
  if qhat ≥ b || qhat * v2 > ((rhat <<< 32) ||| next) then
    let qhat := qhat - 1
    let rhat := rhat + v1
    if rhat < b && (qhat ≥ b || qhat * v2 > ((rhat <<< 32) ||| next)) then qhat - 1 else qhat
  else qhat

/-- The digits of the quotient, from the top one down, written from `qAt` in `w`, whose first digits hold
what is left of the dividend. -/
def steps (vn : @& Digits) (n qAt : Nat) (v1 v2 : UInt64) : Nat → Digits → Digits
  | 0, w => w
  | j + 1, w =>
    let num := (w.digit (j + n) <<< 32) ||| w.digit (j + n - 1)
    let qhat := guess num v1 v2 (w.digit (j + n - 2))
    steps vn n qAt v1 v2 j (takeOff vn n j (qAt + j) qhat n 0 0 w)

/-- The first `n` digits shifted down by `s` bits, the digit above them coming in at the top; that digit,
which a remainder does not have, is cleared after. -/
def unshift (w : Digits) (n : Nat) (s : UInt64) (i : Nat) : Digits :=
  if i < n then unshift (w.set! i (w.pair i >>> s).toUInt32) n s (i + 1) else w.set! n 0
termination_by n - i

/-- The quotient and the remainder of `u` by `v`, for `v` not zero. Knuth's algorithm D (The Art of
Computer Programming, volume 2, 4.3.1), as Warren's `divmnu` lays it out, on 32-bit digits. The answer is
one array and a place in it: the remainder is the digits from the bottom, with nothing above it for at
least eight digits, and the quotient is the digits from that place. -/
def divRem (u v : @& Digits) : Digits × Nat :=
  let n := v.used v.size
  let m := u.used u.size
  if n == 0 then (#[], 0)
  else if m < n then (u.extract 0 m, max m 8)
  else if n == 1 then
    let q := byOne u (v.digit 0) m m 0 (Array.replicate (m + 1) 0)
    (((Array.replicate 8 0 : Digits).set! 0 (q.getD m 0)) ++ q.extract 0 m, 8)
  else
    -- Both are shifted left until the divisor's top digit has its top bit set, which keeps each guess at
    -- a digit of the quotient within two of the truth.
    let s : UInt64 := Word.leadingZeros (v.digit (n - 1)) - 32
    let vn := shiftInto v n s 0 n 0 (Array.replicate n 0)
    let qAt := max (m + 1) 8
    let w := shiftInto u m s 0 (m + 1) 0 (Array.replicate (qAt + (m - n + 1)) 0)
    let w := steps vn n qAt (vn.digit (n - 1)) (vn.digit (n - 2)) (m - n + 1) w
    -- What is left, shifted back down, is the remainder, where it lies.
    (unshift w n s 0, qAt)

/-- The remainder as a word. -/
def remainder (u v : @& Digits) : Word := (divRem u v).1.toWord 0

/-- The low 256 bits of the quotient. -/
def quotient (u v : @& Digits) : Word :=
  let (w, start) := divRem u v
  w.toWord start

end Digits

namespace Word

/-- The 512 bits of a product, as sixteen digits. -/
def mulFull (x y : Word) : Digits :=
  mac x.w0 y.w0 0 0 fun r0 c =>
  mac x.w0 y.w1 c 0 fun r1 c =>
  mac x.w0 y.w2 c 0 fun r2 c =>
  mac x.w0 y.w3 c 0 fun r3 r4 =>
  mac x.w1 y.w0 r1 0 fun r1 c =>
  mac x.w1 y.w1 r2 c fun r2 c =>
  mac x.w1 y.w2 r3 c fun r3 c =>
  mac x.w1 y.w3 r4 c fun r4 r5 =>
  mac x.w2 y.w0 r2 0 fun r2 c =>
  mac x.w2 y.w1 r3 c fun r3 c =>
  mac x.w2 y.w2 r4 c fun r4 c =>
  mac x.w2 y.w3 r5 c fun r5 r6 =>
  mac x.w3 y.w0 r3 0 fun r3 c =>
  mac x.w3 y.w1 r4 c fun r4 c =>
  mac x.w3 y.w2 r5 c fun r5 c =>
  mac x.w3 y.w3 r6 c fun r6 r7 =>
  #[r0.toUInt32, (r0 >>> 32).toUInt32, r1.toUInt32, (r1 >>> 32).toUInt32,
    r2.toUInt32, (r2 >>> 32).toUInt32, r3.toUInt32, (r3 >>> 32).toUInt32,
    r4.toUInt32, (r4 >>> 32).toUInt32, r5.toUInt32, (r5 >>> 32).toUInt32,
    r6.toUInt32, (r6 >>> 32).toUInt32, r7.toUInt32, (r7 >>> 32).toUInt32]

/-- DIV: the quotient, and nothing when dividing by nothing. -/
def div (x y : Word) : Word :=
  if y.isZero then zero
  else if x.small && y.small then ofUInt64 (x.w0 / y.w0)
  else if lt x y then zero
  else Digits.quotient (Digits.ofWord x) (Digits.ofWord y)

/-- MOD: the remainder, and nothing when dividing by nothing. -/
def mod (x y : Word) : Word :=
  if y.isZero then zero
  else if x.small && y.small then ofUInt64 (x.w0 % y.w0)
  else if lt x y then x
  else Digits.remainder (Digits.ofWord x) (Digits.ofWord y)

@[inline] def abs (x : Word) : Word := if x.negative then x.neg else x

/-- SDIV: the quotient of two's-complement numbers, rounded toward zero. -/
def sdiv (x y : Word) : Word :=
  let q := div x.abs y.abs
  if x.negative != y.negative then q.neg else q

/-- SMOD: the remainder of two's-complement numbers, with the sign of the dividend. -/
def smod (x y : Word) : Word :=
  let r := mod x.abs y.abs
  if x.negative then r.neg else r

/-- ADDMOD: the sum, which can take 257 bits, modulo `n`; nothing for a modulus of nothing. -/
def addmod (x y n : Word) : Word :=
  if n.isZero then zero else
  let s := add x y
  if lt s x then
    -- The sum ran past 256 bits: nine digits, the top one a one.
    Digits.remainder ((Digits.ofWord s).push 1) (Digits.ofWord n)
  else mod s n

/-- MULMOD: the product, which can take 512 bits, modulo `n`; nothing for a modulus of nothing. -/
def mulmod (x y n : Word) : Word :=
  if n.isZero then zero
  else if x.isZero || y.isZero then zero
  else Digits.remainder (mulFull x y) (Digits.ofWord n)

end Word
end Fast
