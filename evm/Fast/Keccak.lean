import Fast.Bytes

/-! Keccak-256 for the fast engine: the permutation on 25 machine words held in variables, and the sponge
around it reading its input from a byte array where it lies. One loop does both, a round or a block at a
step, so that a hash allocates its last padded block and its answer and nothing else. Jaune's, which the
trie and the EVM use today, keeps the 25 words in an array of boxed numbers. Nothing proves this equal to
Jaune's or to the standard: `evm-test` holds it to Jaune's at every length to 300 bytes. -/

namespace Fast.Keccak

/-- A 256-bit digest as the sponge gives it: four words, the first holding the first eight bytes with the
first byte least significant. -/
structure Digest where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving BEq

@[inline] def rotl (x : UInt64) (n : UInt64) : UInt64 := (x <<< n) ||| (x >>> (64 - n))

/-- The constant of round `i`. -/
@[inline] def roundConstant (i : UInt8) : UInt64 :=
  match i with
  | 0 => 0x0000000000000001
  | 1 => 0x0000000000008082
  | 2 => 0x800000000000808a
  | 3 => 0x8000000080008000
  | 4 => 0x000000000000808b
  | 5 => 0x0000000080000001
  | 6 => 0x8000000080008081
  | 7 => 0x8000000000008009
  | 8 => 0x000000000000008a
  | 9 => 0x0000000000000088
  | 10 => 0x0000000080008009
  | 11 => 0x000000008000000a
  | 12 => 0x000000008000808b
  | 13 => 0x800000000000008b
  | 14 => 0x8000000000008089
  | 15 => 0x8000000000008003
  | 16 => 0x8000000000008002
  | 17 => 0x8000000000000080
  | 18 => 0x000000000000800a
  | 19 => 0x800000008000000a
  | 20 => 0x8000000080008081
  | 21 => 0x8000000000008080
  | 22 => 0x0000000080000001
  | _ => 0x8000000080008008

/-- The bytes a block takes in: 136 for a 256-bit digest. -/
def rate : Nat := 136

/-- The sponge as one loop. `round` under 24 is a round of the permutation still to do; at 24 the next
block is taken in, from `src` while it has a whole one before `stop`, then the padded `last`, and after
that the digest is read off. -/
def go (src last : @& ByteArray) (stop : USize) : Nat → USize → Bool → UInt8 →
    UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Digest
  | 0, _, _, _, a0, a1, a2, a3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => ⟨a0, a1, a2, a3⟩
  | fuel + 1, off, final, round, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24 =>
    if round < 24 then
      let c0 := a0 ^^^ a5 ^^^ a10 ^^^ a15 ^^^ a20
      let c1 := a1 ^^^ a6 ^^^ a11 ^^^ a16 ^^^ a21
      let c2 := a2 ^^^ a7 ^^^ a12 ^^^ a17 ^^^ a22
      let c3 := a3 ^^^ a8 ^^^ a13 ^^^ a18 ^^^ a23
      let c4 := a4 ^^^ a9 ^^^ a14 ^^^ a19 ^^^ a24
      let d0 := c4 ^^^ rotl c1 1
      let d1 := c0 ^^^ rotl c2 1
      let d2 := c1 ^^^ rotl c3 1
      let d3 := c2 ^^^ rotl c4 1
      let d4 := c3 ^^^ rotl c0 1
      let b0 := (a0 ^^^ d0)
      let b1 := rotl (a6 ^^^ d1) 44
      let b2 := rotl (a12 ^^^ d2) 43
      let b3 := rotl (a18 ^^^ d3) 21
      let b4 := rotl (a24 ^^^ d4) 14
      let b5 := rotl (a3 ^^^ d3) 28
      let b6 := rotl (a9 ^^^ d4) 20
      let b7 := rotl (a10 ^^^ d0) 3
      let b8 := rotl (a16 ^^^ d1) 45
      let b9 := rotl (a22 ^^^ d2) 61
      let b10 := rotl (a1 ^^^ d1) 1
      let b11 := rotl (a7 ^^^ d2) 6
      let b12 := rotl (a13 ^^^ d3) 25
      let b13 := rotl (a19 ^^^ d4) 8
      let b14 := rotl (a20 ^^^ d0) 18
      let b15 := rotl (a4 ^^^ d4) 27
      let b16 := rotl (a5 ^^^ d0) 36
      let b17 := rotl (a11 ^^^ d1) 10
      let b18 := rotl (a17 ^^^ d2) 15
      let b19 := rotl (a23 ^^^ d3) 56
      let b20 := rotl (a2 ^^^ d2) 62
      let b21 := rotl (a8 ^^^ d3) 55
      let b22 := rotl (a14 ^^^ d4) 39
      let b23 := rotl (a15 ^^^ d0) 41
      let b24 := rotl (a21 ^^^ d1) 2
      go src last stop fuel off final (round + 1)
        ((b0 ^^^ (~~~b1 &&& b2)) ^^^ roundConstant round) (b1 ^^^ (~~~b2 &&& b3)) (b2 ^^^ (~~~b3 &&& b4))
        (b3 ^^^ (~~~b4 &&& b0)) (b4 ^^^ (~~~b0 &&& b1)) (b5 ^^^ (~~~b6 &&& b7))
        (b6 ^^^ (~~~b7 &&& b8)) (b7 ^^^ (~~~b8 &&& b9)) (b8 ^^^ (~~~b9 &&& b5))
        (b9 ^^^ (~~~b5 &&& b6)) (b10 ^^^ (~~~b11 &&& b12)) (b11 ^^^ (~~~b12 &&& b13))
        (b12 ^^^ (~~~b13 &&& b14)) (b13 ^^^ (~~~b14 &&& b10)) (b14 ^^^ (~~~b10 &&& b11))
        (b15 ^^^ (~~~b16 &&& b17)) (b16 ^^^ (~~~b17 &&& b18)) (b17 ^^^ (~~~b18 &&& b19))
        (b18 ^^^ (~~~b19 &&& b15)) (b19 ^^^ (~~~b15 &&& b16)) (b20 ^^^ (~~~b21 &&& b22))
        (b21 ^^^ (~~~b22 &&& b23)) (b22 ^^^ (~~~b23 &&& b24)) (b23 ^^^ (~~~b24 &&& b20))
        (b24 ^^^ (~~~b20 &&& b21))
    else if final then ⟨a0, a1, a2, a3⟩
    else if h : off.toNat + 135 < src.size ∧ off.toNat + 135 < stop.toNat then
      go src last stop fuel (off + 136) false 0
        (a0 ^^^ loadAt src off 0 (by omega)) (a1 ^^^ loadAt src off 8 (by omega)) (a2 ^^^ loadAt src off 16 (by omega))
        (a3 ^^^ loadAt src off 24 (by omega)) (a4 ^^^ loadAt src off 32 (by omega)) (a5 ^^^ loadAt src off 40 (by omega))
        (a6 ^^^ loadAt src off 48 (by omega)) (a7 ^^^ loadAt src off 56 (by omega)) (a8 ^^^ loadAt src off 64 (by omega))
        (a9 ^^^ loadAt src off 72 (by omega)) (a10 ^^^ loadAt src off 80 (by omega)) (a11 ^^^ loadAt src off 88 (by omega))
        (a12 ^^^ loadAt src off 96 (by omega)) (a13 ^^^ loadAt src off 104 (by omega)) (a14 ^^^ loadAt src off 112 (by omega))
        (a15 ^^^ loadAt src off 120 (by omega)) (a16 ^^^ loadAt src off 128 (by omega))
        a17 a18 a19 a20 a21 a22 a23 a24
    else if h : 135 < last.size then
      go src last stop fuel off true 0
        (a0 ^^^ loadAt last 0 0 (by simp; omega)) (a1 ^^^ loadAt last 0 8 (by simp; omega)) (a2 ^^^ loadAt last 0 16 (by simp; omega))
        (a3 ^^^ loadAt last 0 24 (by simp; omega)) (a4 ^^^ loadAt last 0 32 (by simp; omega)) (a5 ^^^ loadAt last 0 40 (by simp; omega))
        (a6 ^^^ loadAt last 0 48 (by simp; omega)) (a7 ^^^ loadAt last 0 56 (by simp; omega)) (a8 ^^^ loadAt last 0 64 (by simp; omega))
        (a9 ^^^ loadAt last 0 72 (by simp; omega)) (a10 ^^^ loadAt last 0 80 (by simp; omega)) (a11 ^^^ loadAt last 0 88 (by simp; omega))
        (a12 ^^^ loadAt last 0 96 (by simp; omega)) (a13 ^^^ loadAt last 0 104 (by simp; omega)) (a14 ^^^ loadAt last 0 112 (by simp; omega))
        (a15 ^^^ loadAt last 0 120 (by simp; omega)) (a16 ^^^ loadAt last 0 128 (by simp; omega))
        a17 a18 a19 a20 a21 a22 a23 a24
    else ⟨a0, a1, a2, a3⟩

/-- A block of nothing, which every last block starts as. -/
def zeroBlock : ByteArray := ByteArray.mk (Array.replicate rate 0)

/-- The last block: what is left of the input after its whole blocks, then the padding. -/
def lastBlock (bytes : @& ByteArray) (start size : Nat) : ByteArray :=
  let whole := size / rate * rate
  let left := size - whole
  let padded := bytes.copySlice (start + whole) zeroBlock 0 left
  let padded := padded.set! left (padded.get! left ||| 0x01)
  padded.set! (rate - 1) (padded.get! (rate - 1) ||| 0x80)

/-- Keccak-256 of the `size` bytes of `bytes` from `start`. Bytes past the end of the array are not there to
read, so a range that runs past it is cut to what exists. -/
def hash (bytes : @& ByteArray) (start size : Nat) : Digest :=
  let size := min size (bytes.size - start)
  let stop := start + size / rate * rate
  go bytes (lastBlock bytes start size) stop.toUSize ((size / rate + 2) * 25) start.toUSize false 24
    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

/-- The digest as its 32 bytes. -/
def Digest.bytes (d : Digest) : ByteArray :=
  store (store (store (store (ByteArray.mk (Array.replicate 32 0)) 0 d.w0) 8 d.w1) 16 d.w2) 24 d.w3

end Fast.Keccak
