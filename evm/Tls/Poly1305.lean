import Fast.Bytes

/-! Poly1305 (RFC 8439): a message authenticated under a one-time key, as arithmetic modulo 2^130 - 5 on
five 26-bit limbs in machine words. No branch and no index depends on the key or the message, only how
many blocks there are; the last reduction chooses between two candidates with a mask. -/

namespace Tls.Poly1305

/-- The accumulator: five limbs of 26 bits. -/
structure Acc where
  h0 : UInt64
  h1 : UInt64
  h2 : UInt64
  h3 : UInt64
  h4 : UInt64

def mask : UInt64 := 0x3ffffff

/-- Sixteen bytes of `b` at `off`, least significant first, as two words; bytes not there are nothing. -/
@[inline] def twoWords (b : @& ByteArray) (off : Nat) : UInt64 × UInt64 :=
  let word (i : Nat) : UInt64 := (List.range 8).foldl (fun n j => n ||| ((Fast.byte b (i + j)).toUInt64 <<< (8 * j).toUInt64)) 0
  (word off, word (off + 8))

/-- One block taken in: the accumulator plus the block (with `high`, the bit above its sixteen bytes),
times `r`, reduced. `s1..s4` are five times `r1..r4`. -/
@[inline] def step (a : Acc) (t0 t1 high r0 r1 r2 r3 r4 s1 s2 s3 s4 : UInt64) : Acc :=
  let h0 := a.h0 + (t0 &&& mask)
  let h1 := a.h1 + ((t0 >>> 26) &&& mask)
  let h2 := a.h2 + (((t0 >>> 52) ||| (t1 <<< 12)) &&& mask)
  let h3 := a.h3 + ((t1 >>> 14) &&& mask)
  let h4 := a.h4 + ((t1 >>> 40) ||| high)
  let d0 := h0 * r0 + h1 * s4 + h2 * s3 + h3 * s2 + h4 * s1
  let d1 := h0 * r1 + h1 * r0 + h2 * s4 + h3 * s3 + h4 * s2
  let d2 := h0 * r2 + h1 * r1 + h2 * r0 + h3 * s4 + h4 * s3
  let d3 := h0 * r3 + h1 * r2 + h2 * r1 + h3 * r0 + h4 * s4
  let d4 := h0 * r4 + h1 * r3 + h2 * r2 + h3 * r1 + h4 * r0
  let d1 := d1 + (d0 >>> 26)
  let d2 := d2 + (d1 >>> 26)
  let d3 := d3 + (d2 >>> 26)
  let d4 := d4 + (d3 >>> 26)
  let h0 := (d0 &&& mask) + (d4 >>> 26) * 5
  let h1 := (d1 &&& mask) + (h0 >>> 26)
  ⟨h0 &&& mask, h1, d2 &&& mask, d3 &&& mask, d4 &&& mask⟩

/-- The whole blocks of `message` from `off`, `left` of them. -/
def blocks (message : @& ByteArray) (r0 r1 r2 r3 r4 : UInt64) : Nat → Nat → Acc → Acc
  | 0, _, a => a
  | left + 1, off, a =>
    let (t0, t1) := twoWords message off
    blocks message r0 r1 r2 r3 r4 left (off + 16) (step a t0 t1 0x1000000 r0 r1 r2 r3 r4 (r1 * 5) (r2 * 5) (r3 * 5) (r4 * 5))

/-- The 16-byte tag of `message` under a 32-byte one-time `key`. -/
def tag (key message : @& ByteArray) : ByteArray :=
  -- `r`, with the bits the algorithm requires to be clear cleared.
  let (k0, k1) := twoWords key 0
  let k0 := k0 &&& 0x0ffffffc0fffffff
  let k1 := k1 &&& 0x0ffffffc0ffffffc
  let r0 := k0 &&& mask
  let r1 := (k0 >>> 26) &&& mask
  let r2 := ((k0 >>> 52) ||| (k1 <<< 12)) &&& mask
  let r3 := (k1 >>> 14) &&& mask
  let r4 := k1 >>> 40
  let whole := message.size / 16
  let a := blocks message r0 r1 r2 r3 r4 whole 0 ⟨0, 0, 0, 0, 0⟩
  -- What is left, with a one after it and zeros to sixteen bytes, and no bit above.
  let left := message.size - whole * 16
  let a :=
    if left == 0 then a
    else
      let last := (message.extract (whole * 16) message.size).push 1 ++ ByteArray.mk (Array.replicate (15 - left) 0)
      let (t0, t1) := twoWords last 0
      step a t0 t1 0 r0 r1 r2 r3 r4 (r1 * 5) (r2 * 5) (r3 * 5) (r4 * 5)
  -- Carried all the way, then the accumulator less the modulus if that is not negative.
  let h2 := a.h2 + (a.h1 >>> 26)
  let h1 := a.h1 &&& mask
  let h3 := a.h3 + (h2 >>> 26)
  let h2 := h2 &&& mask
  let h4 := a.h4 + (h3 >>> 26)
  let h3 := h3 &&& mask
  let h0 := a.h0 + (h4 >>> 26) * 5
  let h4 := h4 &&& mask
  let h1 := h1 + (h0 >>> 26)
  let h0 := h0 &&& mask
  let g0 := h0 + 5
  let g1 := h1 + (g0 >>> 26)
  let g2 := h2 + (g1 >>> 26)
  let g3 := h3 + (g2 >>> 26)
  let g4 : UInt64 := h4 + (g3 >>> 26) - 0x4000000
  -- All ones if the subtraction did not go under, and then the candidate is taken.
  let take : UInt64 := (g4 >>> 63) - 1
  let pick (h g : UInt64) : UInt64 := (h &&& ~~~take) ||| (g &&& mask &&& take)
  let h0 := pick h0 g0
  let h1 := pick h1 g1
  let h2 := pick h2 g2
  let h3 := pick h3 g3
  let h4 := (h4 &&& ~~~take) ||| (g4 &&& take)
  -- As two words of 64 bits, and `s`, the second half of the key, added.
  let low := h0 ||| (h1 <<< 26) ||| (h2 <<< 52)
  let high := (h2 >>> 12) ||| (h3 <<< 14) ||| (h4 <<< 40)
  let (s0, s1) := twoWords key 16
  let out0 := low + s0
  -- The carry between the two words, worked out from their top bits and not asked as a question.
  let out1 := high + s1 + (((low &&& s0) ||| ((low ||| s0) &&& ~~~out0)) >>> 63)
  Fast.store (Fast.store (ByteArray.mk (Array.replicate 16 0)) 0 out0) 8 out1

end Tls.Poly1305
