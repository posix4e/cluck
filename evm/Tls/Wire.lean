import Fast.Bytes

/-! Reading and writing what goes on a wire: numbers of a fixed width most significant byte first, runs of
bytes with their length before them, and a place in a run of bytes that moves as things are read from it.
A read that would run past the end gives nothing. -/

namespace Tls

/-- A name with its capital letters made small. -/
def lower (name : @& ByteArray) : ByteArray :=
  ByteArray.mk (name.data.map fun c => if c ≥ 0x41 && c ≤ 0x5a then c + 0x20 else c)

def u16 (n : Nat) : ByteArray := ByteArray.mk #[(n >>> 8).toUInt8, n.toUInt8]
def u24 (n : Nat) : ByteArray := ByteArray.mk #[(n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]

/-- `b` with its length before it, in one, two or three bytes. -/
def framed8 (b : ByteArray) : ByteArray := ByteArray.mk #[b.size.toUInt8] ++ b
def framed16 (b : ByteArray) : ByteArray := u16 b.size ++ b
def framed24 (b : ByteArray) : ByteArray := u24 b.size ++ b

/-- A place in a run of bytes. -/
structure Cursor where
  bytes : ByteArray
  pos : Nat

namespace Cursor

def of (b : ByteArray) : Cursor := ⟨b, 0⟩

/-- Whether everything has been read. -/
def done (c : Cursor) : Bool := c.pos ≥ c.bytes.size

def take (c : Cursor) (n : Nat) : Option (ByteArray × Cursor) :=
  if c.pos + n > c.bytes.size then none else some (c.bytes.extract c.pos (c.pos + n), { c with pos := c.pos + n })

/-- A number of `width` bytes. -/
def number (c : Cursor) (width : Nat) : Option (Nat × Cursor) := do
  let (b, c) ← c.take width
  pure (b.foldl (fun n x => n * 256 + x.toNat) 0, c)

/-- A run of bytes whose length comes before it in `width` bytes. -/
def framed (c : Cursor) (width : Nat) : Option (ByteArray × Cursor) := do
  let (n, c) ← c.number width
  c.take n

end Cursor
end Tls
