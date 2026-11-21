import Secret

/-! BLS12-381's base field for arithmetic on a secret: fifteen limbs of 26 bits in machine words.

`Jaune` and `JauneConsensus` hold a field element as a `Nat`, and their arithmetic takes time that depends
on the numbers. That is fine for everything a builder verifies and for everything public, and it is what
this repository's rule forbids for a key: secrets never pass through `Nat` or `Int`. A signature is the
key times a point, so the coordinates of every point on the way are secrets too, and this is the field
they are computed in.

- An element is `l0 + l1 2^26 + ... + l14 2^364`, each limb below `2^26`, the whole below the prime, held
  in Montgomery form: the element `x` is stored as `x 2^390` modulo the prime. A product of limbs fits a
  64-bit word with room to add thirty of them, so nothing here overflows and nothing is a big number.
- No function has a branch, an index or a division that depends on an element's value. Where the value
  decides something (whether the prime still has to come off, whether a difference went below zero) both
  answers are computed and `Secret.select` chooses, which is the OS's checked choice without a branch
  (`Mini/Secret.lean`). The only `if`s are on public things: the bits of a fixed exponent.
- `ofPublic` and `toPublic` are the two ways in and out through `Nat`, and are for values that are not
  secret: a point hashed from a public message on the way in, a finished signature on the way out.

What is not claimed: that the machine code has no such branch. The Lean compiler and the C compiler are
between this text and the machine. `bls-test` holds the arithmetic to `Nat`; the machine code is read, not
proved (`THREAT_MODEL.md`).

The straight-line parts (the column sums and the reduction) were written by a program from the prime; the
tests are what hold them to it. -/

namespace Evm.Sign

/-- An element of the field, in Montgomery form. -/
structure Fp where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
  l6 : UInt64
  l7 : UInt64
  l8 : UInt64
  l9 : UInt64
  l10 : UInt64
  l11 : UInt64
  l12 : UInt64
  l13 : UInt64
  l14 : UInt64

namespace Fp

def mask : UInt64 := 0x3FFFFFF

/-- Zero. -/
def zero : Fp := ⟨0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0⟩

/-- One: `2^390` modulo the prime. -/
def one : Fp := ⟨0xd1ff2e, 0x1800000, 0xac467, 0xde6d20, 0x84b803, 0x22090c7, 0x19a7e0e, 0x373e037, 0x2d0b683, 0x3b09b09, 0x23c4a5e, 0x3c515d9, 0x2804b29, 0x2659fcf, 0x15de⟩

/-- `2^780` modulo the prime, which takes an ordinary number into Montgomery form. -/
def r2 : Fp := ⟨0x110070f, 0x19070d1, 0x2243aec, 0x30e804c, 0x36ea66e, 0x37d41eb, 0x3ee07b1, 0x6c517b, 0x121eed2, 0x290510a, 0x2d32f70, 0x24005dc, 0x1918c97, 0x3b812b3, 0xf696⟩

/-- `x` if `c`, otherwise `y`, without a branch on `c`. -/
def select (c : Bool) (x y : Fp) : Fp :=
  ⟨Secret.select c x.l0 y.l0, Secret.select c x.l1 y.l1, Secret.select c x.l2 y.l2, Secret.select c x.l3 y.l3, Secret.select c x.l4 y.l4, Secret.select c x.l5 y.l5, Secret.select c x.l6 y.l6, Secret.select c x.l7 y.l7, Secret.select c x.l8 y.l8, Secret.select c x.l9 y.l9, Secret.select c x.l10 y.l10, Secret.select c x.l11 y.l11, Secret.select c x.l12 y.l12, Secret.select c x.l13 y.l13, Secret.select c x.l14 y.l14⟩

/-- The element that fifteen limbs below `2^26` stand for, when they are below twice the prime. -/
def reduce (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 : UInt64) : Fp :=
  let b : UInt64 := 0
  let s0 := r0 + 0x5555 - b; let b := (1 : UInt64) - (s0 >>> 26); let s0 := s0 &&& mask
  let s1 := r1 + 0x400001 - b; let b := (1 : UInt64) - (s1 >>> 26); let s1 := s1 &&& mask
  let s2 := r2 + 0x461 - b; let b := (1 : UInt64) - (s2 >>> 26); let s2 := s2 &&& mask
  let s3 := r3 + 0x53ab1 - b; let b := (1 : UInt64) - (s3 >>> 26); let s3 := s3 &&& mask
  let s4 := r4 + 0x3e15401 - b; let b := (1 : UInt64) - (s4 >>> 26); let s4 := s4 &&& mask
  let s5 := r5 + 0x253c277 - b; let b := (1 : UInt64) - (s5 >>> 26); let s5 := s5 &&& mask
  let s6 := r6 + 0xf2d5f1 - b; let b := (1 : UInt64) - (s6 >>> 26); let s6 := s6 &&& mask
  let s7 := r7 + 0x3b50264 - b; let b := (1 : UInt64) - (s7 >>> 26); let s7 := s7 &&& mask
  let s8 := r8 + 0x7b0c7b - b; let b := (1 : UInt64) - (s8 >>> 26); let s8 := s8 &&& mask
  let s9 := r9 + 0x226e22e - b; let b := (1 : UInt64) - (s9 >>> 26); let s9 := s9 &&& mask
  let s10 := r10 + 0x3cb4533 - b; let b := (1 : UInt64) - (s10 >>> 26); let s10 := s10 &&& mask
  let s11 := r11 + 0x3916127 - b; let b := (1 : UInt64) - (s11 >>> 26); let s11 := s11 &&& mask
  let s12 := r12 + 0x1965b5 - b; let b := (1 : UInt64) - (s12 >>> 26); let s12 := s12 &&& mask
  let s13 := r13 + 0x38571a1 - b; let b := (1 : UInt64) - (s13 >>> 26); let s13 := s13 &&& mask
  let s14 := r14 + 0x3fe5fef - b; let b := (1 : UInt64) - (s14 >>> 26); let s14 := s14 &&& mask
  let keep := b == 1
  ⟨Secret.select keep r0 s0, Secret.select keep r1 s1, Secret.select keep r2 s2, Secret.select keep r3 s3, Secret.select keep r4 s4, Secret.select keep r5 s5, Secret.select keep r6 s6, Secret.select keep r7 s7, Secret.select keep r8 s8, Secret.select keep r9 s9, Secret.select keep r10 s10, Secret.select keep r11 s11, Secret.select keep r12 s12, Secret.select keep r13 s13, Secret.select keep r14 s14⟩

def add (a b : Fp) : Fp :=
  let r0 := a.l0 + b.l0
  let r1 := a.l1 + b.l1
  let r2 := a.l2 + b.l2
  let r3 := a.l3 + b.l3
  let r4 := a.l4 + b.l4
  let r5 := a.l5 + b.l5
  let r6 := a.l6 + b.l6
  let r7 := a.l7 + b.l7
  let r8 := a.l8 + b.l8
  let r9 := a.l9 + b.l9
  let r10 := a.l10 + b.l10
  let r11 := a.l11 + b.l11
  let r12 := a.l12 + b.l12
  let r13 := a.l13 + b.l13
  let r14 := a.l14 + b.l14
  let r1 := r1 + (r0 >>> 26); let r0 := r0 &&& mask
  let r2 := r2 + (r1 >>> 26); let r1 := r1 &&& mask
  let r3 := r3 + (r2 >>> 26); let r2 := r2 &&& mask
  let r4 := r4 + (r3 >>> 26); let r3 := r3 &&& mask
  let r5 := r5 + (r4 >>> 26); let r4 := r4 &&& mask
  let r6 := r6 + (r5 >>> 26); let r5 := r5 &&& mask
  let r7 := r7 + (r6 >>> 26); let r6 := r6 &&& mask
  let r8 := r8 + (r7 >>> 26); let r7 := r7 &&& mask
  let r9 := r9 + (r8 >>> 26); let r8 := r8 &&& mask
  let r10 := r10 + (r9 >>> 26); let r9 := r9 &&& mask
  let r11 := r11 + (r10 >>> 26); let r10 := r10 &&& mask
  let r12 := r12 + (r11 >>> 26); let r11 := r11 &&& mask
  let r13 := r13 + (r12 >>> 26); let r12 := r12 &&& mask
  let r14 := r14 + (r13 >>> 26); let r13 := r13 &&& mask
  reduce r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14

/-- `a - b`: the difference limb by limb with a borrow, and with the prime added, one of which is the
answer according to whether the difference went below zero. -/
def sub (a b : Fp) : Fp :=
  let w : UInt64 := 0
  let d0 := a.l0 + 0x4000000 - b.l0 - w; let w := (1 : UInt64) - (d0 >>> 26); let d0 := d0 &&& mask
  let d1 := a.l1 + 0x4000000 - b.l1 - w; let w := (1 : UInt64) - (d1 >>> 26); let d1 := d1 &&& mask
  let d2 := a.l2 + 0x4000000 - b.l2 - w; let w := (1 : UInt64) - (d2 >>> 26); let d2 := d2 &&& mask
  let d3 := a.l3 + 0x4000000 - b.l3 - w; let w := (1 : UInt64) - (d3 >>> 26); let d3 := d3 &&& mask
  let d4 := a.l4 + 0x4000000 - b.l4 - w; let w := (1 : UInt64) - (d4 >>> 26); let d4 := d4 &&& mask
  let d5 := a.l5 + 0x4000000 - b.l5 - w; let w := (1 : UInt64) - (d5 >>> 26); let d5 := d5 &&& mask
  let d6 := a.l6 + 0x4000000 - b.l6 - w; let w := (1 : UInt64) - (d6 >>> 26); let d6 := d6 &&& mask
  let d7 := a.l7 + 0x4000000 - b.l7 - w; let w := (1 : UInt64) - (d7 >>> 26); let d7 := d7 &&& mask
  let d8 := a.l8 + 0x4000000 - b.l8 - w; let w := (1 : UInt64) - (d8 >>> 26); let d8 := d8 &&& mask
  let d9 := a.l9 + 0x4000000 - b.l9 - w; let w := (1 : UInt64) - (d9 >>> 26); let d9 := d9 &&& mask
  let d10 := a.l10 + 0x4000000 - b.l10 - w; let w := (1 : UInt64) - (d10 >>> 26); let d10 := d10 &&& mask
  let d11 := a.l11 + 0x4000000 - b.l11 - w; let w := (1 : UInt64) - (d11 >>> 26); let d11 := d11 &&& mask
  let d12 := a.l12 + 0x4000000 - b.l12 - w; let w := (1 : UInt64) - (d12 >>> 26); let d12 := d12 &&& mask
  let d13 := a.l13 + 0x4000000 - b.l13 - w; let w := (1 : UInt64) - (d13 >>> 26); let d13 := d13 &&& mask
  let d14 := a.l14 + 0x4000000 - b.l14 - w; let w := (1 : UInt64) - (d14 >>> 26); let d14 := d14 &&& mask
  let below := w == 1
  let c : UInt64 := 0
  let e0 := d0 + 0x3ffaaab + c; let c : UInt64 := e0 >>> 26; let e0 := e0 &&& mask
  let e1 := d1 + 0x3bfffff + c; let c : UInt64 := e1 >>> 26; let e1 := e1 &&& mask
  let e2 := d2 + 0x3fffb9f + c; let c : UInt64 := e2 >>> 26; let e2 := e2 &&& mask
  let e3 := d3 + 0x3fac54f + c; let c : UInt64 := e3 >>> 26; let e3 := e3 &&& mask
  let e4 := d4 + 0x1eabff + c; let c : UInt64 := e4 >>> 26; let e4 := e4 &&& mask
  let e5 := d5 + 0x1ac3d89 + c; let c : UInt64 := e5 >>> 26; let e5 := e5 &&& mask
  let e6 := d6 + 0x30d2a0f + c; let c : UInt64 := e6 >>> 26; let e6 := e6 &&& mask
  let e7 := d7 + 0x4afd9c + c; let c : UInt64 := e7 >>> 26; let e7 := e7 &&& mask
  let e8 := d8 + 0x384f385 + c; let c : UInt64 := e8 >>> 26; let e8 := e8 &&& mask
  let e9 := d9 + 0x1d91dd2 + c; let c : UInt64 := e9 >>> 26; let e9 := e9 &&& mask
  let e10 := d10 + 0x34bacd + c; let c : UInt64 := e10 >>> 26; let e10 := e10 &&& mask
  let e11 := d11 + 0x6e9ed9 + c; let c : UInt64 := e11 >>> 26; let e11 := e11 &&& mask
  let e12 := d12 + 0x3e69a4b + c; let c : UInt64 := e12 >>> 26; let e12 := e12 &&& mask
  let e13 := d13 + 0x7a8e5f + c; let c : UInt64 := e13 >>> 26; let e13 := e13 &&& mask
  let e14 := d14 + 0x1a011 + c; let c : UInt64 := e14 >>> 26; let e14 := e14 &&& mask
  ⟨Secret.select below e0 d0, Secret.select below e1 d1, Secret.select below e2 d2, Secret.select below e3 d3, Secret.select below e4 d4, Secret.select below e5 d5, Secret.select below e6 d6, Secret.select below e7 d7, Secret.select below e8 d8, Secret.select below e9 d9, Secret.select below e10 d10, Secret.select below e11 d11, Secret.select below e12 d12, Secret.select below e13 d13, Secret.select below e14 d14⟩

def neg (a : Fp) : Fp := sub zero a

/-- The Montgomery product, `a b / 2^390`: the product of two elements in Montgomery form, in that form.
Column `k` is the sum of the products of limbs whose places add to `k`. Then, for each of the fifteen low
columns in turn, the multiple of the prime that makes that column's low 26 bits zero is added, and the
column's carry moves up; what is left in the fifteen high columns is the answer or the answer plus the
prime. -/
def mul (a b : Fp) : Fp :=
  let t0 := a.l0 * b.l0
  let t1 := a.l0 * b.l1 + a.l1 * b.l0
  let t2 := a.l0 * b.l2 + a.l1 * b.l1 + a.l2 * b.l0
  let t3 := a.l0 * b.l3 + a.l1 * b.l2 + a.l2 * b.l1 + a.l3 * b.l0
  let t4 := a.l0 * b.l4 + a.l1 * b.l3 + a.l2 * b.l2 + a.l3 * b.l1 + a.l4 * b.l0
  let t5 := a.l0 * b.l5 + a.l1 * b.l4 + a.l2 * b.l3 + a.l3 * b.l2 + a.l4 * b.l1 + a.l5 * b.l0
  let t6 := a.l0 * b.l6 + a.l1 * b.l5 + a.l2 * b.l4 + a.l3 * b.l3 + a.l4 * b.l2 + a.l5 * b.l1 + a.l6 * b.l0
  let t7 := a.l0 * b.l7 + a.l1 * b.l6 + a.l2 * b.l5 + a.l3 * b.l4 + a.l4 * b.l3 + a.l5 * b.l2 + a.l6 * b.l1 + a.l7 * b.l0
  let t8 := a.l0 * b.l8 + a.l1 * b.l7 + a.l2 * b.l6 + a.l3 * b.l5 + a.l4 * b.l4 + a.l5 * b.l3 + a.l6 * b.l2 + a.l7 * b.l1 + a.l8 * b.l0
  let t9 := a.l0 * b.l9 + a.l1 * b.l8 + a.l2 * b.l7 + a.l3 * b.l6 + a.l4 * b.l5 + a.l5 * b.l4 + a.l6 * b.l3 + a.l7 * b.l2 + a.l8 * b.l1 + a.l9 * b.l0
  let t10 := a.l0 * b.l10 + a.l1 * b.l9 + a.l2 * b.l8 + a.l3 * b.l7 + a.l4 * b.l6 + a.l5 * b.l5 + a.l6 * b.l4 + a.l7 * b.l3 + a.l8 * b.l2 + a.l9 * b.l1 + a.l10 * b.l0
  let t11 := a.l0 * b.l11 + a.l1 * b.l10 + a.l2 * b.l9 + a.l3 * b.l8 + a.l4 * b.l7 + a.l5 * b.l6 + a.l6 * b.l5 + a.l7 * b.l4 + a.l8 * b.l3 + a.l9 * b.l2 + a.l10 * b.l1 + a.l11 * b.l0
  let t12 := a.l0 * b.l12 + a.l1 * b.l11 + a.l2 * b.l10 + a.l3 * b.l9 + a.l4 * b.l8 + a.l5 * b.l7 + a.l6 * b.l6 + a.l7 * b.l5 + a.l8 * b.l4 + a.l9 * b.l3 + a.l10 * b.l2 + a.l11 * b.l1 + a.l12 * b.l0
  let t13 := a.l0 * b.l13 + a.l1 * b.l12 + a.l2 * b.l11 + a.l3 * b.l10 + a.l4 * b.l9 + a.l5 * b.l8 + a.l6 * b.l7 + a.l7 * b.l6 + a.l8 * b.l5 + a.l9 * b.l4 + a.l10 * b.l3 + a.l11 * b.l2 + a.l12 * b.l1 + a.l13 * b.l0
  let t14 := a.l0 * b.l14 + a.l1 * b.l13 + a.l2 * b.l12 + a.l3 * b.l11 + a.l4 * b.l10 + a.l5 * b.l9 + a.l6 * b.l8 + a.l7 * b.l7 + a.l8 * b.l6 + a.l9 * b.l5 + a.l10 * b.l4 + a.l11 * b.l3 + a.l12 * b.l2 + a.l13 * b.l1 + a.l14 * b.l0
  let t15 := a.l1 * b.l14 + a.l2 * b.l13 + a.l3 * b.l12 + a.l4 * b.l11 + a.l5 * b.l10 + a.l6 * b.l9 + a.l7 * b.l8 + a.l8 * b.l7 + a.l9 * b.l6 + a.l10 * b.l5 + a.l11 * b.l4 + a.l12 * b.l3 + a.l13 * b.l2 + a.l14 * b.l1
  let t16 := a.l2 * b.l14 + a.l3 * b.l13 + a.l4 * b.l12 + a.l5 * b.l11 + a.l6 * b.l10 + a.l7 * b.l9 + a.l8 * b.l8 + a.l9 * b.l7 + a.l10 * b.l6 + a.l11 * b.l5 + a.l12 * b.l4 + a.l13 * b.l3 + a.l14 * b.l2
  let t17 := a.l3 * b.l14 + a.l4 * b.l13 + a.l5 * b.l12 + a.l6 * b.l11 + a.l7 * b.l10 + a.l8 * b.l9 + a.l9 * b.l8 + a.l10 * b.l7 + a.l11 * b.l6 + a.l12 * b.l5 + a.l13 * b.l4 + a.l14 * b.l3
  let t18 := a.l4 * b.l14 + a.l5 * b.l13 + a.l6 * b.l12 + a.l7 * b.l11 + a.l8 * b.l10 + a.l9 * b.l9 + a.l10 * b.l8 + a.l11 * b.l7 + a.l12 * b.l6 + a.l13 * b.l5 + a.l14 * b.l4
  let t19 := a.l5 * b.l14 + a.l6 * b.l13 + a.l7 * b.l12 + a.l8 * b.l11 + a.l9 * b.l10 + a.l10 * b.l9 + a.l11 * b.l8 + a.l12 * b.l7 + a.l13 * b.l6 + a.l14 * b.l5
  let t20 := a.l6 * b.l14 + a.l7 * b.l13 + a.l8 * b.l12 + a.l9 * b.l11 + a.l10 * b.l10 + a.l11 * b.l9 + a.l12 * b.l8 + a.l13 * b.l7 + a.l14 * b.l6
  let t21 := a.l7 * b.l14 + a.l8 * b.l13 + a.l9 * b.l12 + a.l10 * b.l11 + a.l11 * b.l10 + a.l12 * b.l9 + a.l13 * b.l8 + a.l14 * b.l7
  let t22 := a.l8 * b.l14 + a.l9 * b.l13 + a.l10 * b.l12 + a.l11 * b.l11 + a.l12 * b.l10 + a.l13 * b.l9 + a.l14 * b.l8
  let t23 := a.l9 * b.l14 + a.l10 * b.l13 + a.l11 * b.l12 + a.l12 * b.l11 + a.l13 * b.l10 + a.l14 * b.l9
  let t24 := a.l10 * b.l14 + a.l11 * b.l13 + a.l12 * b.l12 + a.l13 * b.l11 + a.l14 * b.l10
  let t25 := a.l11 * b.l14 + a.l12 * b.l13 + a.l13 * b.l12 + a.l14 * b.l11
  let t26 := a.l12 * b.l14 + a.l13 * b.l13 + a.l14 * b.l12
  let t27 := a.l13 * b.l14 + a.l14 * b.l13
  let t28 := a.l14 * b.l14
  let t29 : UInt64 := 0
  let m := ((t0 &&& mask) * 0x3fcfffd) &&& mask
  let t0 := t0 + m * 0x3ffaaab
  let t1 := t1 + m * 0x3bfffff
  let t2 := t2 + m * 0x3fffb9f
  let t3 := t3 + m * 0x3fac54f
  let t4 := t4 + m * 0x1eabff
  let t5 := t5 + m * 0x1ac3d89
  let t6 := t6 + m * 0x30d2a0f
  let t7 := t7 + m * 0x4afd9c
  let t8 := t8 + m * 0x384f385
  let t9 := t9 + m * 0x1d91dd2
  let t10 := t10 + m * 0x34bacd
  let t11 := t11 + m * 0x6e9ed9
  let t12 := t12 + m * 0x3e69a4b
  let t13 := t13 + m * 0x7a8e5f
  let t14 := t14 + m * 0x1a011
  let t1 := t1 + (t0 >>> 26)
  let m := ((t1 &&& mask) * 0x3fcfffd) &&& mask
  let t1 := t1 + m * 0x3ffaaab
  let t2 := t2 + m * 0x3bfffff
  let t3 := t3 + m * 0x3fffb9f
  let t4 := t4 + m * 0x3fac54f
  let t5 := t5 + m * 0x1eabff
  let t6 := t6 + m * 0x1ac3d89
  let t7 := t7 + m * 0x30d2a0f
  let t8 := t8 + m * 0x4afd9c
  let t9 := t9 + m * 0x384f385
  let t10 := t10 + m * 0x1d91dd2
  let t11 := t11 + m * 0x34bacd
  let t12 := t12 + m * 0x6e9ed9
  let t13 := t13 + m * 0x3e69a4b
  let t14 := t14 + m * 0x7a8e5f
  let t15 := t15 + m * 0x1a011
  let t2 := t2 + (t1 >>> 26)
  let m := ((t2 &&& mask) * 0x3fcfffd) &&& mask
  let t2 := t2 + m * 0x3ffaaab
  let t3 := t3 + m * 0x3bfffff
  let t4 := t4 + m * 0x3fffb9f
  let t5 := t5 + m * 0x3fac54f
  let t6 := t6 + m * 0x1eabff
  let t7 := t7 + m * 0x1ac3d89
  let t8 := t8 + m * 0x30d2a0f
  let t9 := t9 + m * 0x4afd9c
  let t10 := t10 + m * 0x384f385
  let t11 := t11 + m * 0x1d91dd2
  let t12 := t12 + m * 0x34bacd
  let t13 := t13 + m * 0x6e9ed9
  let t14 := t14 + m * 0x3e69a4b
  let t15 := t15 + m * 0x7a8e5f
  let t16 := t16 + m * 0x1a011
  let t3 := t3 + (t2 >>> 26)
  let m := ((t3 &&& mask) * 0x3fcfffd) &&& mask
  let t3 := t3 + m * 0x3ffaaab
  let t4 := t4 + m * 0x3bfffff
  let t5 := t5 + m * 0x3fffb9f
  let t6 := t6 + m * 0x3fac54f
  let t7 := t7 + m * 0x1eabff
  let t8 := t8 + m * 0x1ac3d89
  let t9 := t9 + m * 0x30d2a0f
  let t10 := t10 + m * 0x4afd9c
  let t11 := t11 + m * 0x384f385
  let t12 := t12 + m * 0x1d91dd2
  let t13 := t13 + m * 0x34bacd
  let t14 := t14 + m * 0x6e9ed9
  let t15 := t15 + m * 0x3e69a4b
  let t16 := t16 + m * 0x7a8e5f
  let t17 := t17 + m * 0x1a011
  let t4 := t4 + (t3 >>> 26)
  let m := ((t4 &&& mask) * 0x3fcfffd) &&& mask
  let t4 := t4 + m * 0x3ffaaab
  let t5 := t5 + m * 0x3bfffff
  let t6 := t6 + m * 0x3fffb9f
  let t7 := t7 + m * 0x3fac54f
  let t8 := t8 + m * 0x1eabff
  let t9 := t9 + m * 0x1ac3d89
  let t10 := t10 + m * 0x30d2a0f
  let t11 := t11 + m * 0x4afd9c
  let t12 := t12 + m * 0x384f385
  let t13 := t13 + m * 0x1d91dd2
  let t14 := t14 + m * 0x34bacd
  let t15 := t15 + m * 0x6e9ed9
  let t16 := t16 + m * 0x3e69a4b
  let t17 := t17 + m * 0x7a8e5f
  let t18 := t18 + m * 0x1a011
  let t5 := t5 + (t4 >>> 26)
  let m := ((t5 &&& mask) * 0x3fcfffd) &&& mask
  let t5 := t5 + m * 0x3ffaaab
  let t6 := t6 + m * 0x3bfffff
  let t7 := t7 + m * 0x3fffb9f
  let t8 := t8 + m * 0x3fac54f
  let t9 := t9 + m * 0x1eabff
  let t10 := t10 + m * 0x1ac3d89
  let t11 := t11 + m * 0x30d2a0f
  let t12 := t12 + m * 0x4afd9c
  let t13 := t13 + m * 0x384f385
  let t14 := t14 + m * 0x1d91dd2
  let t15 := t15 + m * 0x34bacd
  let t16 := t16 + m * 0x6e9ed9
  let t17 := t17 + m * 0x3e69a4b
  let t18 := t18 + m * 0x7a8e5f
  let t19 := t19 + m * 0x1a011
  let t6 := t6 + (t5 >>> 26)
  let m := ((t6 &&& mask) * 0x3fcfffd) &&& mask
  let t6 := t6 + m * 0x3ffaaab
  let t7 := t7 + m * 0x3bfffff
  let t8 := t8 + m * 0x3fffb9f
  let t9 := t9 + m * 0x3fac54f
  let t10 := t10 + m * 0x1eabff
  let t11 := t11 + m * 0x1ac3d89
  let t12 := t12 + m * 0x30d2a0f
  let t13 := t13 + m * 0x4afd9c
  let t14 := t14 + m * 0x384f385
  let t15 := t15 + m * 0x1d91dd2
  let t16 := t16 + m * 0x34bacd
  let t17 := t17 + m * 0x6e9ed9
  let t18 := t18 + m * 0x3e69a4b
  let t19 := t19 + m * 0x7a8e5f
  let t20 := t20 + m * 0x1a011
  let t7 := t7 + (t6 >>> 26)
  let m := ((t7 &&& mask) * 0x3fcfffd) &&& mask
  let t7 := t7 + m * 0x3ffaaab
  let t8 := t8 + m * 0x3bfffff
  let t9 := t9 + m * 0x3fffb9f
  let t10 := t10 + m * 0x3fac54f
  let t11 := t11 + m * 0x1eabff
  let t12 := t12 + m * 0x1ac3d89
  let t13 := t13 + m * 0x30d2a0f
  let t14 := t14 + m * 0x4afd9c
  let t15 := t15 + m * 0x384f385
  let t16 := t16 + m * 0x1d91dd2
  let t17 := t17 + m * 0x34bacd
  let t18 := t18 + m * 0x6e9ed9
  let t19 := t19 + m * 0x3e69a4b
  let t20 := t20 + m * 0x7a8e5f
  let t21 := t21 + m * 0x1a011
  let t8 := t8 + (t7 >>> 26)
  let m := ((t8 &&& mask) * 0x3fcfffd) &&& mask
  let t8 := t8 + m * 0x3ffaaab
  let t9 := t9 + m * 0x3bfffff
  let t10 := t10 + m * 0x3fffb9f
  let t11 := t11 + m * 0x3fac54f
  let t12 := t12 + m * 0x1eabff
  let t13 := t13 + m * 0x1ac3d89
  let t14 := t14 + m * 0x30d2a0f
  let t15 := t15 + m * 0x4afd9c
  let t16 := t16 + m * 0x384f385
  let t17 := t17 + m * 0x1d91dd2
  let t18 := t18 + m * 0x34bacd
  let t19 := t19 + m * 0x6e9ed9
  let t20 := t20 + m * 0x3e69a4b
  let t21 := t21 + m * 0x7a8e5f
  let t22 := t22 + m * 0x1a011
  let t9 := t9 + (t8 >>> 26)
  let m := ((t9 &&& mask) * 0x3fcfffd) &&& mask
  let t9 := t9 + m * 0x3ffaaab
  let t10 := t10 + m * 0x3bfffff
  let t11 := t11 + m * 0x3fffb9f
  let t12 := t12 + m * 0x3fac54f
  let t13 := t13 + m * 0x1eabff
  let t14 := t14 + m * 0x1ac3d89
  let t15 := t15 + m * 0x30d2a0f
  let t16 := t16 + m * 0x4afd9c
  let t17 := t17 + m * 0x384f385
  let t18 := t18 + m * 0x1d91dd2
  let t19 := t19 + m * 0x34bacd
  let t20 := t20 + m * 0x6e9ed9
  let t21 := t21 + m * 0x3e69a4b
  let t22 := t22 + m * 0x7a8e5f
  let t23 := t23 + m * 0x1a011
  let t10 := t10 + (t9 >>> 26)
  let m := ((t10 &&& mask) * 0x3fcfffd) &&& mask
  let t10 := t10 + m * 0x3ffaaab
  let t11 := t11 + m * 0x3bfffff
  let t12 := t12 + m * 0x3fffb9f
  let t13 := t13 + m * 0x3fac54f
  let t14 := t14 + m * 0x1eabff
  let t15 := t15 + m * 0x1ac3d89
  let t16 := t16 + m * 0x30d2a0f
  let t17 := t17 + m * 0x4afd9c
  let t18 := t18 + m * 0x384f385
  let t19 := t19 + m * 0x1d91dd2
  let t20 := t20 + m * 0x34bacd
  let t21 := t21 + m * 0x6e9ed9
  let t22 := t22 + m * 0x3e69a4b
  let t23 := t23 + m * 0x7a8e5f
  let t24 := t24 + m * 0x1a011
  let t11 := t11 + (t10 >>> 26)
  let m := ((t11 &&& mask) * 0x3fcfffd) &&& mask
  let t11 := t11 + m * 0x3ffaaab
  let t12 := t12 + m * 0x3bfffff
  let t13 := t13 + m * 0x3fffb9f
  let t14 := t14 + m * 0x3fac54f
  let t15 := t15 + m * 0x1eabff
  let t16 := t16 + m * 0x1ac3d89
  let t17 := t17 + m * 0x30d2a0f
  let t18 := t18 + m * 0x4afd9c
  let t19 := t19 + m * 0x384f385
  let t20 := t20 + m * 0x1d91dd2
  let t21 := t21 + m * 0x34bacd
  let t22 := t22 + m * 0x6e9ed9
  let t23 := t23 + m * 0x3e69a4b
  let t24 := t24 + m * 0x7a8e5f
  let t25 := t25 + m * 0x1a011
  let t12 := t12 + (t11 >>> 26)
  let m := ((t12 &&& mask) * 0x3fcfffd) &&& mask
  let t12 := t12 + m * 0x3ffaaab
  let t13 := t13 + m * 0x3bfffff
  let t14 := t14 + m * 0x3fffb9f
  let t15 := t15 + m * 0x3fac54f
  let t16 := t16 + m * 0x1eabff
  let t17 := t17 + m * 0x1ac3d89
  let t18 := t18 + m * 0x30d2a0f
  let t19 := t19 + m * 0x4afd9c
  let t20 := t20 + m * 0x384f385
  let t21 := t21 + m * 0x1d91dd2
  let t22 := t22 + m * 0x34bacd
  let t23 := t23 + m * 0x6e9ed9
  let t24 := t24 + m * 0x3e69a4b
  let t25 := t25 + m * 0x7a8e5f
  let t26 := t26 + m * 0x1a011
  let t13 := t13 + (t12 >>> 26)
  let m := ((t13 &&& mask) * 0x3fcfffd) &&& mask
  let t13 := t13 + m * 0x3ffaaab
  let t14 := t14 + m * 0x3bfffff
  let t15 := t15 + m * 0x3fffb9f
  let t16 := t16 + m * 0x3fac54f
  let t17 := t17 + m * 0x1eabff
  let t18 := t18 + m * 0x1ac3d89
  let t19 := t19 + m * 0x30d2a0f
  let t20 := t20 + m * 0x4afd9c
  let t21 := t21 + m * 0x384f385
  let t22 := t22 + m * 0x1d91dd2
  let t23 := t23 + m * 0x34bacd
  let t24 := t24 + m * 0x6e9ed9
  let t25 := t25 + m * 0x3e69a4b
  let t26 := t26 + m * 0x7a8e5f
  let t27 := t27 + m * 0x1a011
  let t14 := t14 + (t13 >>> 26)
  let m := ((t14 &&& mask) * 0x3fcfffd) &&& mask
  let t14 := t14 + m * 0x3ffaaab
  let t15 := t15 + m * 0x3bfffff
  let t16 := t16 + m * 0x3fffb9f
  let t17 := t17 + m * 0x3fac54f
  let t18 := t18 + m * 0x1eabff
  let t19 := t19 + m * 0x1ac3d89
  let t20 := t20 + m * 0x30d2a0f
  let t21 := t21 + m * 0x4afd9c
  let t22 := t22 + m * 0x384f385
  let t23 := t23 + m * 0x1d91dd2
  let t24 := t24 + m * 0x34bacd
  let t25 := t25 + m * 0x6e9ed9
  let t26 := t26 + m * 0x3e69a4b
  let t27 := t27 + m * 0x7a8e5f
  let t28 := t28 + m * 0x1a011
  let t15 := t15 + (t14 >>> 26)
  let r0 := t15
  let r1 := t16
  let r2 := t17
  let r3 := t18
  let r4 := t19
  let r5 := t20
  let r6 := t21
  let r7 := t22
  let r8 := t23
  let r9 := t24
  let r10 := t25
  let r11 := t26
  let r12 := t27
  let r13 := t28
  let r14 := t29
  let r1 := r1 + (r0 >>> 26); let r0 := r0 &&& mask
  let r2 := r2 + (r1 >>> 26); let r1 := r1 &&& mask
  let r3 := r3 + (r2 >>> 26); let r2 := r2 &&& mask
  let r4 := r4 + (r3 >>> 26); let r3 := r3 &&& mask
  let r5 := r5 + (r4 >>> 26); let r4 := r4 &&& mask
  let r6 := r6 + (r5 >>> 26); let r5 := r5 &&& mask
  let r7 := r7 + (r6 >>> 26); let r6 := r6 &&& mask
  let r8 := r8 + (r7 >>> 26); let r7 := r7 &&& mask
  let r9 := r9 + (r8 >>> 26); let r8 := r8 &&& mask
  let r10 := r10 + (r9 >>> 26); let r9 := r9 &&& mask
  let r11 := r11 + (r10 >>> 26); let r10 := r10 &&& mask
  let r12 := r12 + (r11 >>> 26); let r11 := r11 &&& mask
  let r13 := r13 + (r12 >>> 26); let r12 := r12 &&& mask
  let r14 := r14 + (r13 >>> 26); let r13 := r13 &&& mask
  reduce r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14

instance : Add Fp := ⟨add⟩
instance : Sub Fp := ⟨sub⟩
instance : Mul Fp := ⟨mul⟩

/-- `a ^ e` for an exponent that is public, given as its bits from the top. The branches are on those bits. -/
def powPublic (a : Fp) (bits : List Bool) : Fp :=
  bits.foldl (fun r bit => let s := r * r; if bit then s * a else s) one

/-- The bits of the prime less two, from the top. -/
def inverseExponent : List Bool :=
  let e : Nat := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaa9
  (List.range 381).reverse.map fun i => e.testBit i

/-- `1 / a` as `a ^ (p - 2)`, a fixed sequence of products whatever `a` is; zero for zero. -/
def inv (a : Fp) : Fp := powPublic a inverseExponent

/-- A number that is not a secret, as an element. -/
def ofPublic (n : Nat) : Fp :=
  let n := n % 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
  let limb (i : Nat) : UInt64 := (n >>> (26 * i)).toUInt64 &&& mask
  mul ⟨limb 0, limb 1, limb 2, limb 3, limb 4, limb 5, limb 6, limb 7, limb 8, limb 9, limb 10, limb 11, limb 12, limb 13, limb 14⟩ r2

/-- An element that is no longer a secret, as a number below the prime. -/
def toPublic (a : Fp) : Nat :=
  let x := mul a ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  [x.l0, x.l1, x.l2, x.l3, x.l4, x.l5, x.l6, x.l7, x.l8, x.l9, x.l10, x.l11, x.l12, x.l13, x.l14].foldr (fun l n => n * 2 ^ 26 + l.toNat) 0

end Fp

end Evm.Sign
