import Fast.Wide
import Platform

/-! The fast engine's word arithmetic against the same arithmetic on `Nat`: every operation, on every pair
of a list of awkward values and on values drawn at random in several shapes. Prints how many cases each
operation was put through and a sum of the answers, so that the two runtimes can be compared on what they
computed. -/
open Fast

def M : Nat := 2 ^ 256

/-- Whether a word is a negative number in two's complement, and its size without the sign. The answers
for signed operations are worked out on these, in `Nat` alone: the minimal runtime has no division of big
integers with a sign, and a test is no reason to give it one. -/
def negative (n : Nat) : Bool := n ≥ 2 ^ 255
def size (n : Nat) : Nat := if negative n then M - n else n
def minus (n : Nat) : Nat := (M - n) % M
/-- A two's-complement number moved so that order as numbers is order as `Nat`s. -/
def lifted (n : Nat) : Nat := (n + 2 ^ 255) % M

def say (s : String) : IO Unit := Platform.write (s ++ "\n").toUTF8

/-- A generator of numbers anyone can run again: xorshift on 64 bits. -/
def next (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A word drawn in one of several shapes: any bits, one machine word, a few bits, nearly all bits, a power
of two and its neighbours. -/
def draw (s : UInt64) : Word × UInt64 :=
  let a := next s
  let b := next a
  let c := next b
  let d := next c
  let e := next d
  let w : Word :=
    match e % 8 with
    | 0 | 1 | 2 => ⟨a, b, c, d⟩
    | 3 => ⟨a, 0, 0, 0⟩
    | 4 => ⟨a, b, 0, 0⟩
    | 5 => Word.ofNat (2 ^ (a % 256).toNat + (b % 3).toNat - 1)
    | 6 => (Word.ofNat (2 ^ (a % 256).toNat)).not
    | _ => ⟨a &&& b &&& c, 0, d &&& a, if (b >>> 9) % 2 == 0 then 0 else c ||| d⟩
  (w, e)

def edges : List Nat :=
  [0, 1, 2, 3, 7, 255, 256, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1, 2 ^ 96 - 1, 2 ^ 127,
   2 ^ 128 - 1, 2 ^ 128, 2 ^ 160 - 1, 2 ^ 192, 2 ^ 224 + 2 ^ 32, 2 ^ 255 - 1, 2 ^ 255, 2 ^ 255 + 1, M - 2 ^ 128,
   M - 2 ^ 64, M - 3, M - 2, M - 1]

def powMod (x e : Nat) : Nat := Id.run do
  let mut result := 1
  let mut base := x % M
  let mut e := e
  for _ in [0:256] do
    if e == 0 then break
    if e % 2 == 1 then result := result * base % M
    base := base * base % M
    e := e / 2
  return result

/-- Each operation of two words with what `Nat` says it is. -/
def binary : List (String × (Word → Word → Word) × (Nat → Nat → Nat)) := [
  ("add", Word.add, fun x y => (x + y) % M),
  ("sub", Word.sub, fun x y => (x + M - y) % M),
  ("mul", Word.mul, fun x y => x * y % M),
  ("div", Word.div, fun x y => if y == 0 then 0 else x / y),
  ("mod", Word.mod, fun x y => if y == 0 then 0 else x % y),
  ("sdiv", Word.sdiv, fun x y =>
    if y == 0 then 0 else if negative x != negative y then minus (size x / size y) else size x / size y),
  ("smod", Word.smod, fun x y =>
    if y == 0 then 0 else if negative x then minus (size x % size y) else size x % size y),
  ("lt", fun x y => Word.ofBool (Word.lt x y), fun x y => if x < y then 1 else 0),
  ("gt", fun x y => Word.ofBool (Word.gt x y), fun x y => if x > y then 1 else 0),
  ("slt", fun x y => Word.ofBool (Word.slt x y), fun x y => if lifted x < lifted y then 1 else 0),
  ("sgt", fun x y => Word.ofBool (Word.sgt x y), fun x y => if lifted x > lifted y then 1 else 0),
  ("eq", fun x y => Word.ofBool (Word.eq x y), fun x y => if x == y then 1 else 0),
  ("and", Word.and, fun x y => x &&& y),
  ("or", Word.or, fun x y => x ||| y),
  ("xor", Word.xor, fun x y => (x ||| y) - (x &&& y)),
  ("shl", Word.shl, fun s x => if s ≥ 256 then 0 else (x <<< s) % M),
  ("shr", Word.shr, fun s x => if s ≥ 256 then 0 else x >>> s),
  ("sar", Word.sar, fun s x =>
    if s ≥ 256 then (if negative x then M - 1 else 0)
    else if negative x then M - 1 - ((M - 1 - x) >>> s) else x >>> s),
  ("byte", Word.byte, fun i x => if i ≥ 32 then 0 else (x >>> (8 * (31 - i))) % 256),
  ("signextend", Word.signExtend, fun b x =>
    if b ≥ 31 then x else
    let low := x % 2 ^ (8 * (b + 1))
    if low ≥ 2 ^ (8 * (b + 1) - 1) then low + (M - 2 ^ (8 * (b + 1))) else low),
  ("exp", Word.exp, powMod)]

def unary : List (String × (Word → Word) × (Nat → Nat)) := [
  ("not", Word.not, fun x => M - 1 - x),
  ("neg", Word.neg, fun x => (M - x) % M),
  ("iszero", fun x => Word.ofBool x.isZero, fun x => if x == 0 then 1 else 0),
  ("clz", Word.clz, fun x => if x == 0 then 256 else 255 - Nat.log2 x),
  ("bytelength", fun x => Word.ofUInt64 x.byteLength, fun x => if x == 0 then 0 else Nat.log2 x / 8 + 1),
  ("round trip", fun x => Word.ofNat x.toNat, fun x => x)]

def ternary : List (String × (Word → Word → Word → Word) × (Nat → Nat → Nat → Nat)) := [
  ("addmod", Word.addmod, fun x y n => if n == 0 then 0 else (x + y) % n),
  ("mulmod", Word.mulmod, fun x y n => if n == 0 then 0 else x * y % n)]

def main : IO UInt32 := do
  -- The words every operation sees: the awkward ones, then 400 drawn.
  let mut words : Array Word := (edges.map Word.ofNat).toArray
  let mut seed : UInt64 := 0x9e3779b97f4a7c15
  for _ in [0:400] do
    let (w, s) := draw seed
    words := words.push w
    seed := s
  -- Second operands also include what a shift, a byte index or an exponent is likely to be.
  let mut seconds := words
  for n in [4, 8, 9, 15, 16, 30, 31, 32, 33, 63, 64, 65, 127, 128, 129, 191, 192, 193, 254, 257, 300] do
    seconds := seconds.push (Word.ofNat n)
  let mut failures := 0
  for (name, f, g) in unary do
    let mut sum : UInt64 := 0
    for x in words do
      let got := f x
      sum := sum * 31 + got.w0 + got.w3
      if got.toNat != g x.toNat then
        failures := failures + 1
        if failures < 20 then say s!"{name} {x.toNat}: {got.toNat}, not {g x.toNat}"
    say s!"{name}: {words.size} cases, sum {sum}"
  for (name, f, g) in binary do
    let mut sum : UInt64 := 0
    let mut cases := 0
    for x in seconds do
      for y in words do
        let got := f x y
        cases := cases + 1
        sum := sum * 31 + got.w0 + got.w3
        if got.toNat != g x.toNat y.toNat then
          failures := failures + 1
          if failures < 20 then say s!"{name} {x.toNat} {y.toNat}: {got.toNat}, not {g x.toNat y.toNat}"
    say s!"{name}: {cases} cases, sum {sum}"
  for (name, f, g) in ternary do
    let mut sum : UInt64 := 0
    let mut cases := 0
    for i in [0:words.size] do
      for j in [0:words.size] do
        -- Every modulus for the awkward pairs; for the rest, a few moduli chosen by position.
        let moduli := if i < edges.length && j < edges.length then words.size else 3
        for k in [0:moduli] do
          let x := words[i]!
          let y := words[j]!
          let n := if moduli == 3 then words[(i * 7 + j * 13 + k * 101) % words.size]! else words[k]!
          let got := f x y n
          cases := cases + 1
          sum := sum * 31 + got.w0 + got.w3
          if got.toNat != g x.toNat y.toNat n.toNat then
            failures := failures + 1
            if failures < 20 then
              say s!"{name} {x.toNat} {y.toNat} {n.toNat}: {got.toNat}, not {g x.toNat y.toNat n.toNat}"
    say s!"{name}: {cases} cases, sum {sum}"
  if failures == 0 then say "fast-word-test: all checks passed" else say s!"fast-word-test: {failures} FAILED"
  return if failures == 0 then 0 else 1
