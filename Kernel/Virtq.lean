/-! # A virtqueue's memory, as bytes

A virtio device and its driver pass buffers through a queue made of three tables in shared memory: the
descriptors (which buffers there are), the available ring (which ones the driver has offered) and the used
ring (which ones the device has finished with, and how many bytes it wrote). This file is where each field
of those tables lives and how it is spelt, as pure functions. `Kernel/Virtio.lean` does the reading and
writing.

The layout is virtio's split virtqueue, little-endian throughout. -/

namespace Kernel.Virtq

/-- `value` as `width` little-endian bytes. -/
def le (value width : Nat) : ByteArray :=
  (List.range width).foldl (fun out i => out.push (value >>> (8 * i)).toUInt8) ByteArray.empty

/-- The `width` little-endian bytes at `offset`, or 0 if `b` is too short to hold them. -/
def readLE (b : ByteArray) (offset width : Nat) : Nat :=
  if offset + width > b.size then 0 else
  (List.range width).foldl (fun acc i => acc ||| (b[offset + i]!.toNat <<< (8 * i))) 0

/-- Descriptor flags: another descriptor follows in the chain; the device may write to this buffer. -/
def flagNext : Nat := 1
def flagWrite : Nat := 2

/-- One descriptor: a buffer's address and length, its flags, and the next descriptor in its chain. -/
def descriptor (address : UInt64) (length : Nat) (flags next : Nat) : ByteArray :=
  le address.toNat 8 ++ le length 4 ++ le flags 2 ++ le next 2

def descriptorSize : Nat := 16

/-- Where the three tables of a queue of `size` entries go in one block of memory, and how large it is.
The used ring starts on a 4-byte boundary. -/
structure Layout where
  size : Nat
  descriptors : Nat
  available : Nat
  used : Nat
  bytes : Nat
  deriving Repr, Inhabited

def Layout.of (size : Nat) : Layout :=
  let available := descriptorSize * size
  let used := (available + 6 + 2 * size + 3) / 4 * 4
  { size, descriptors := 0, available, used, bytes := used + 6 + 8 * size }

/-- In the available ring: the index the driver will write next (free-running, 16 bits), and its slots. -/
def Layout.availableIndex (l : Layout) : Nat := l.available + 2
def Layout.availableSlot (l : Layout) (i : Nat) : Nat := l.available + 4 + 2 * (i % l.size)

/-- In the used ring: the index the device will write next, and its slots (descriptor id, bytes written). -/
def Layout.usedIndex (l : Layout) : Nat := l.used + 2
def Layout.usedSlot (l : Layout) (i : Nat) : Nat := l.used + 4 + 8 * (i % l.size)

end Kernel.Virtq
