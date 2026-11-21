import Fast.Bytes
import Secret

/-! X25519 (RFC 7748): the key exchange on Curve25519. A number modulo 2^255 - 19 is ten limbs, of 26 and
25 bits by turns, in machine words; the ladder does the same additions and multiplications for every bit
of the key and chooses between its two points with the OS's `Secret.select`, never a branch. The key never
becomes a `Nat`. The power that inverts is a fixed public number, and following its bits is no secret.
`tls-test` holds this to the RFC's examples and to OpenSSL's on random keys. -/

namespace Tls.X25519

/-- A number modulo 2^255 - 19: ten limbs, the even ones of 26 bits and the odd of 25. Carried, each limb
is within its size but for a little in the lowest two. -/
structure Fe where
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

namespace Fe

def zero : Fe := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def one : Fe := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Each limb's overflow moved up to the next, and the top's brought round to the bottom times 19. -/
@[inline] def carry (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : UInt64) : Fe :=
  let m26 : UInt64 := 0x3ffffff
  let m25 : UInt64 := 0x1ffffff
  let h1 := h1 + (h0 >>> 26)
  let h2 := h2 + (h1 >>> 25)
  let h3 := h3 + (h2 >>> 26)
  let h4 := h4 + (h3 >>> 25)
  let h5 := h5 + (h4 >>> 26)
  let h6 := h6 + (h5 >>> 25)
  let h7 := h7 + (h6 >>> 26)
  let h8 := h8 + (h7 >>> 25)
  let h9 := h9 + (h8 >>> 26)
  let h0 := (h0 &&& m26) + (h9 >>> 25) * 19
  let h1 := (h1 &&& m25) + (h0 >>> 26)
  ⟨h0 &&& m26, h1, h2 &&& m26, h3 &&& m25, h4 &&& m26, h5 &&& m25, h6 &&& m26, h7 &&& m25, h8 &&& m26, h9 &&& m25⟩

def add (a b : Fe) : Fe :=
  carry (a.l0 + b.l0) (a.l1 + b.l1) (a.l2 + b.l2) (a.l3 + b.l3) (a.l4 + b.l4) (a.l5 + b.l5) (a.l6 + b.l6)
    (a.l7 + b.l7) (a.l8 + b.l8) (a.l9 + b.l9)

/-- `a - b`, with twice the modulus added first so that no limb goes under. -/
def sub (a b : Fe) : Fe :=
  carry (a.l0 + 0x7ffffda - b.l0) (a.l1 + 0x3fffffe - b.l1) (a.l2 + 0x7fffffe - b.l2) (a.l3 + 0x3fffffe - b.l3)
    (a.l4 + 0x7fffffe - b.l4) (a.l5 + 0x3fffffe - b.l5) (a.l6 + 0x7fffffe - b.l6) (a.l7 + 0x3fffffe - b.l7)
    (a.l8 + 0x7fffffe - b.l8) (a.l9 + 0x3fffffe - b.l9)

/-- The product. A limb times a limb fits a machine word many times over; where two odd limbs meet, their
places add up to one bit more than the place they land in, hence the twos, and what passes 2^255 comes
round times 19. -/
def mul (a b : Fe) : Fe :=
  let h0 := a.l0 * (b.l0) + a.l1 * (b.l9 * 38) + a.l2 * (b.l8 * 19) + a.l3 * (b.l7 * 38) + a.l4 * (b.l6 * 19) + a.l5 * (b.l5 * 38) + a.l6 * (b.l4 * 19) + a.l7 * (b.l3 * 38) + a.l8 * (b.l2 * 19) + a.l9 * (b.l1 * 38)
  let h1 := a.l0 * (b.l1) + a.l1 * (b.l0) + a.l2 * (b.l9 * 19) + a.l3 * (b.l8 * 19) + a.l4 * (b.l7 * 19) + a.l5 * (b.l6 * 19) + a.l6 * (b.l5 * 19) + a.l7 * (b.l4 * 19) + a.l8 * (b.l3 * 19) + a.l9 * (b.l2 * 19)
  let h2 := a.l0 * (b.l2) + a.l1 * (b.l1 * 2) + a.l2 * (b.l0) + a.l3 * (b.l9 * 38) + a.l4 * (b.l8 * 19) + a.l5 * (b.l7 * 38) + a.l6 * (b.l6 * 19) + a.l7 * (b.l5 * 38) + a.l8 * (b.l4 * 19) + a.l9 * (b.l3 * 38)
  let h3 := a.l0 * (b.l3) + a.l1 * (b.l2) + a.l2 * (b.l1) + a.l3 * (b.l0) + a.l4 * (b.l9 * 19) + a.l5 * (b.l8 * 19) + a.l6 * (b.l7 * 19) + a.l7 * (b.l6 * 19) + a.l8 * (b.l5 * 19) + a.l9 * (b.l4 * 19)
  let h4 := a.l0 * (b.l4) + a.l1 * (b.l3 * 2) + a.l2 * (b.l2) + a.l3 * (b.l1 * 2) + a.l4 * (b.l0) + a.l5 * (b.l9 * 38) + a.l6 * (b.l8 * 19) + a.l7 * (b.l7 * 38) + a.l8 * (b.l6 * 19) + a.l9 * (b.l5 * 38)
  let h5 := a.l0 * (b.l5) + a.l1 * (b.l4) + a.l2 * (b.l3) + a.l3 * (b.l2) + a.l4 * (b.l1) + a.l5 * (b.l0) + a.l6 * (b.l9 * 19) + a.l7 * (b.l8 * 19) + a.l8 * (b.l7 * 19) + a.l9 * (b.l6 * 19)
  let h6 := a.l0 * (b.l6) + a.l1 * (b.l5 * 2) + a.l2 * (b.l4) + a.l3 * (b.l3 * 2) + a.l4 * (b.l2) + a.l5 * (b.l1 * 2) + a.l6 * (b.l0) + a.l7 * (b.l9 * 38) + a.l8 * (b.l8 * 19) + a.l9 * (b.l7 * 38)
  let h7 := a.l0 * (b.l7) + a.l1 * (b.l6) + a.l2 * (b.l5) + a.l3 * (b.l4) + a.l4 * (b.l3) + a.l5 * (b.l2) + a.l6 * (b.l1) + a.l7 * (b.l0) + a.l8 * (b.l9 * 19) + a.l9 * (b.l8 * 19)
  let h8 := a.l0 * (b.l8) + a.l1 * (b.l7 * 2) + a.l2 * (b.l6) + a.l3 * (b.l5 * 2) + a.l4 * (b.l4) + a.l5 * (b.l3 * 2) + a.l6 * (b.l2) + a.l7 * (b.l1 * 2) + a.l8 * (b.l0) + a.l9 * (b.l9 * 38)
  let h9 := a.l0 * (b.l9) + a.l1 * (b.l8) + a.l2 * (b.l7) + a.l3 * (b.l6) + a.l4 * (b.l5) + a.l5 * (b.l4) + a.l6 * (b.l3) + a.l7 * (b.l2) + a.l8 * (b.l1) + a.l9 * (b.l0)
  carry h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

def square (a : Fe) : Fe := mul a a

/-- By the curve's constant, 121665. -/
def mulSmall (a : Fe) : Fe :=
  carry (a.l0 * 121665) (a.l1 * 121665) (a.l2 * 121665) (a.l3 * 121665) (a.l4 * 121665) (a.l5 * 121665)
    (a.l6 * 121665) (a.l7 * 121665) (a.l8 * 121665) (a.l9 * 121665)

/-- `a` if `c`, otherwise `b`, limb by limb, without a branch on `c`. -/
def select (c : Bool) (a b : Fe) : Fe :=
  ⟨Secret.select c a.l0 b.l0, Secret.select c a.l1 b.l1, Secret.select c a.l2 b.l2, Secret.select c a.l3 b.l3,
   Secret.select c a.l4 b.l4, Secret.select c a.l5 b.l5, Secret.select c a.l6 b.l6, Secret.select c a.l7 b.l7,
   Secret.select c a.l8 b.l8, Secret.select c a.l9 b.l9⟩

/-- The inverse: the power 2^255 - 21, whose bits are all ones but the third and the fifth from the
bottom. `left` counts the bits still to come, from the top. -/
def inverse (a : Fe) : Fe :=
  go a 255 one
where
  go (a : Fe) : Nat → Fe → Fe
    | 0, acc => acc
    | left + 1, acc =>
      let acc := square acc
      go a left (if left == 2 || left == 4 then acc else mul acc a)

/-- A number from 32 bytes, least significant first, the top bit left out as the RFC has it. -/
def read (b : @& ByteArray) : Fe :=
  let word (i : Nat) : UInt64 := (List.range 8).foldl (fun n j => n ||| ((Fast.byte b (i + j)).toUInt64 <<< (8 * j).toUInt64)) 0
  let w0 := word 0
  let w1 := word 8
  let w2 := word 16
  let w3 := word 24 &&& 0x7fffffffffffffff
  ⟨w0 &&& 0x3ffffff, (w0 >>> 26) &&& 0x1ffffff, ((w0 >>> 51) ||| (w1 <<< 13)) &&& 0x3ffffff,
   (w1 >>> 13) &&& 0x1ffffff, (w1 >>> 38) &&& 0x3ffffff, w2 &&& 0x1ffffff, (w2 >>> 25) &&& 0x3ffffff,
   ((w2 >>> 51) ||| (w3 <<< 13)) &&& 0x1ffffff, (w3 >>> 12) &&& 0x3ffffff, (w3 >>> 38) &&& 0x1ffffff⟩

/-- The 32 bytes of a number, least significant first, the number being brought under the modulus first:
19 is added to see whether that passes 2^255, and if it does, 19 is what the number is less the modulus
short of, so it is added for good and the bit above dropped. No branch. -/
def write (a : Fe) : ByteArray :=
  let a := carry a.l0 a.l1 a.l2 a.l3 a.l4 a.l5 a.l6 a.l7 a.l8 a.l9
  let a := carry a.l0 a.l1 a.l2 a.l3 a.l4 a.l5 a.l6 a.l7 a.l8 a.l9
  let q := (a.l0 + 19) >>> 26
  let q := (a.l1 + q) >>> 25
  let q := (a.l2 + q) >>> 26
  let q := (a.l3 + q) >>> 25
  let q := (a.l4 + q) >>> 26
  let q := (a.l5 + q) >>> 25
  let q := (a.l6 + q) >>> 26
  let q := (a.l7 + q) >>> 25
  let q := (a.l8 + q) >>> 26
  let q := (a.l9 + q) >>> 25
  let h0 := a.l0 + 19 * q
  let h1 := a.l1 + (h0 >>> 26)
  let h2 := a.l2 + (h1 >>> 25)
  let h3 := a.l3 + (h2 >>> 26)
  let h4 := a.l4 + (h3 >>> 25)
  let h5 := a.l5 + (h4 >>> 26)
  let h6 := a.l6 + (h5 >>> 25)
  let h7 := a.l7 + (h6 >>> 26)
  let h8 := a.l8 + (h7 >>> 25)
  let h9 := a.l9 + (h8 >>> 26)
  let h0 := h0 &&& 0x3ffffff
  let h1 := h1 &&& 0x1ffffff
  let h2 := h2 &&& 0x3ffffff
  let h3 := h3 &&& 0x1ffffff
  let h4 := h4 &&& 0x3ffffff
  let h5 := h5 &&& 0x1ffffff
  let h6 := h6 &&& 0x3ffffff
  let h7 := h7 &&& 0x1ffffff
  let h8 := h8 &&& 0x3ffffff
  let h9 := h9 &&& 0x1ffffff
  let w0 := h0 ||| (h1 <<< 26) ||| (h2 <<< 51)
  let w1 := (h2 >>> 13) ||| (h3 <<< 13) ||| (h4 <<< 38)
  let w2 := h5 ||| (h6 <<< 25) ||| (h7 <<< 51)
  let w3 := (h7 >>> 13) ||| (h8 <<< 12) ||| (h9 <<< 38)
  Fast.store (Fast.store (Fast.store (Fast.store (ByteArray.mk (Array.replicate 32 0)) 0 w0) 8 w1) 16 w2) 24 w3

end Fe

/-- Bit `i` of a 32-byte key, as a word that is 0 or 1, for a public `i`, after the clamping the RFC
requires: the lowest three bits clear, the top bit clear, the one under it set. -/
def keyBit (key : @& ByteArray) (i : Nat) : UInt64 :=
  if i < 3 || i == 255 then 0
  else if i == 254 then 1
  else (Fast.byte key (i / 8) >>> (i % 8).toUInt8).toUInt64 &&& 1

/-- The ladder: for each bit of the key from the top, the two points are swapped or not by the bit, both
are moved on, and the swap is remembered for the next bit. Whether to swap is worked out as arithmetic on
two words, the last bit and this one, and only ever handed to `Fe.select`: written with the truth values
themselves it was compiled to a branch on the key's bit. -/
def ladder (key : @& ByteArray) (x1 : Fe) : Nat → UInt64 → Fe → Fe → Fe → Fe → Fe
  | 0, swap, x2, z2, x3, z3 =>
    let x2 := Fe.select (swap == 1) x3 x2
    let z2 := Fe.select (swap == 1) z3 z2
    Fe.mul x2 z2.inverse
  | t + 1, swap, x2, z2, x3, z3 =>
    let bit := keyBit key t
    let cross := (swap ^^^ bit) == 1
    let a2 := Fe.select cross x3 x2
    let a3 := Fe.select cross x2 x3
    let c2 := Fe.select cross z3 z2
    let c3 := Fe.select cross z2 z3
    let A := a2.add c2
    let AA := A.square
    let B := a2.sub c2
    let BB := B.square
    let E := AA.sub BB
    let C := a3.add c3
    let D := a3.sub c3
    let DA := D.mul A
    let CB := C.mul B
    let x3 := (DA.add CB).square
    let z3 := x1.mul (DA.sub CB).square
    let x2 := AA.mul BB
    let z2 := E.mul (AA.add E.mulSmall)
    ladder key x1 t bit x2 z2 x3 z3

/-- X25519: the 32-byte `key` times the point whose coordinate is the 32 bytes `point`. -/
def x25519 (key point : @& ByteArray) : ByteArray :=
  let x1 := Fe.read point
  (ladder key x1 255 0 Fe.one Fe.zero x1 Fe.one).write

/-- The public key of a private one: the key times the curve's base point, 9. -/
def publicKey (key : @& ByteArray) : ByteArray :=
  x25519 key ((ByteArray.mk (Array.replicate 32 0)).set! 0 9)

end Tls.X25519
