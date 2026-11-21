import Fast.Bytes

/-! ChaCha20 (RFC 8439): the block function on sixteen 32-bit words in variables, and the stream it makes
laid over a message eight bytes at a time. Additions, rotations and exclusive-ors only: nothing here
depends on the key or the message but the values computed. -/

namespace Tls.ChaCha20

/-- The sixteen words a block ends with, before the starting words are added back. -/
structure Words where
  x0 : UInt32
  x1 : UInt32
  x2 : UInt32
  x3 : UInt32
  x4 : UInt32
  x5 : UInt32
  x6 : UInt32
  x7 : UInt32
  x8 : UInt32
  x9 : UInt32
  x10 : UInt32
  x11 : UInt32
  x12 : UInt32
  x13 : UInt32
  x14 : UInt32
  x15 : UInt32

@[inline] def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- A quarter round, on four of the words, handed on. -/
@[inline] def quarter {α : Type} (a b c d : UInt32) (k : UInt32 → UInt32 → UInt32 → UInt32 → α) : α :=
  let a := a + b
  let d := rotl (d ^^^ a) 16
  let c := c + d
  let b := rotl (b ^^^ c) 12
  let a := a + b
  let d := rotl (d ^^^ a) 8
  let c := c + d
  let b := rotl (b ^^^ c) 7
  k a b c d

/-- Ten double rounds: down the columns, then down the diagonals. -/
def rounds : Nat → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 →
    UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → Words
  | 0, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15 =>
    ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩
  | left + 1, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15 =>
    quarter x0 x4 x8 x12 fun x0 x4 x8 x12 =>
    quarter x1 x5 x9 x13 fun x1 x5 x9 x13 =>
    quarter x2 x6 x10 x14 fun x2 x6 x10 x14 =>
    quarter x3 x7 x11 x15 fun x3 x7 x11 x15 =>
    quarter x0 x5 x10 x15 fun x0 x5 x10 x15 =>
    quarter x1 x6 x11 x12 fun x1 x6 x11 x12 =>
    quarter x2 x7 x8 x13 fun x2 x7 x8 x13 =>
    quarter x3 x4 x9 x14 fun x3 x4 x9 x14 =>
    rounds left x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15

/-- A 32-bit word from four bytes of `b` at `i`, least significant first; nothing for bytes not there. -/
@[inline] def word (b : @& ByteArray) (i : Nat) : UInt32 :=
  (Fast.byte b i).toUInt32 ||| ((Fast.byte b (i + 1)).toUInt32 <<< 8) ||| ((Fast.byte b (i + 2)).toUInt32 <<< 16) |||
    ((Fast.byte b (i + 3)).toUInt32 <<< 24)

/-- The 64 bytes of stream for a block, as eight 64-bit words to lay over eight bytes each. `key` is 32
bytes and `nonce` 12. -/
def block (key nonce : @& ByteArray) (counter : UInt32) : Array UInt64 :=
  let k0 := word key 0
  let k1 := word key 4
  let k2 := word key 8
  let k3 := word key 12
  let k4 := word key 16
  let k5 := word key 20
  let k6 := word key 24
  let k7 := word key 28
  let n0 := word nonce 0
  let n1 := word nonce 4
  let n2 := word nonce 8
  let w := rounds 10 0x61707865 0x3320646e 0x79622d32 0x6b206574 k0 k1 k2 k3 k4 k5 k6 k7 counter n0 n1 n2
  let pair (lo hi : UInt32) : UInt64 := lo.toUInt64 ||| (hi.toUInt64 <<< 32)
  #[pair (w.x0 + 0x61707865) (w.x1 + 0x3320646e), pair (w.x2 + 0x79622d32) (w.x3 + 0x6b206574),
    pair (w.x4 + k0) (w.x5 + k1), pair (w.x6 + k2) (w.x7 + k3), pair (w.x8 + k4) (w.x9 + k5),
    pair (w.x10 + k6) (w.x11 + k7), pair (w.x12 + counter) (w.x13 + n0), pair (w.x14 + n1) (w.x15 + n2)]

/-- The first `n` bytes of a block's stream. -/
def stream (key nonce : @& ByteArray) (counter : UInt32) (n : Nat) : ByteArray :=
  let words := block key nonce counter
  (ByteArray.mk ((List.range n).map fun i => ((words.getD (i / 8) 0) >>> (8 * (i % 8)).toUInt64).toUInt8).toArray)

/-- `data` with the stream laid over it from block `counter` on: encryption and decryption alike. -/
def apply (key nonce : @& ByteArray) (counter : UInt32) (data : ByteArray) : ByteArray :=
  go key nonce (data.size / 64 + 1) counter 0 data
where
  go (key nonce : @& ByteArray) : Nat → UInt32 → USize → ByteArray → ByteArray
    | 0, _, _, data => data
    | left + 1, counter, off, data =>
      if off.toNat ≥ data.size then data
      else
        let words := block key nonce counter
        if off.toNat + 63 < data.size then
          -- A whole block: eight words read, crossed with the stream, and written back where they were.
          let data := (List.range 8).foldl (fun data j =>
            let at_ := off + USize.ofNat (8 * j)
            if h8 : at_.toNat + 7 < data.size then Fast.store data at_ (Fast.load data at_ h8 ^^^ words.getD j 0) else data) data
          go key nonce left (counter + 1) (off + 64) data
        else
          -- The end of the message, a byte at a time.
          (List.range (data.size - off.toNat)).foldl (fun data i =>
            data.set! (off.toNat + i) (Fast.byte data (off.toNat + i) ^^^ ((words.getD (i / 8) 0) >>> (8 * (i % 8)).toUInt64).toUInt8)) data

end Tls.ChaCha20
