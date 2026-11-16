/-! # Frames between the parent instance and the enclave

A frame is a 4-byte big-endian payload length followed by that many payload bytes. A payload is never empty
and never longer than `maxPayload`, so a reader knows from the header alone how much it will be asked to hold.

Everything here is pure: bytes in, payloads out. The same code reads frames from a pipe in the simulator and
from the vsock driver on bare metal, where bytes arrive in whatever pieces the parent chooses to send. -/

namespace Demo.Wire

/-- The longest payload a frame may carry. -/
def maxPayload : Nat := 65536

/-- `n` as four big-endian bytes. Only called with `n ≤ maxPayload`. -/
def u32be (n : Nat) : ByteArray :=
  ByteArray.empty
    |>.push (n >>> 24).toUInt8 |>.push (n >>> 16).toUInt8 |>.push (n >>> 8).toUInt8 |>.push n.toUInt8

/-- The four bytes at `i` as a big-endian number. Only called with `i + 4 ≤ b.size`. -/
def readU32be (b : ByteArray) (i : Nat) : Nat :=
  (b[i]!.toNat <<< 24) ||| (b[i + 1]!.toNat <<< 16) ||| (b[i + 2]!.toNat <<< 8) ||| b[i + 3]!.toNat

/-- A payload as one frame. -/
def frame (payload : ByteArray) : ByteArray := u32be payload.size ++ payload

/-- Why a byte stream stopped being frames. The connection is dropped; nothing is resynchronised. -/
inductive Fault where
  /-- A header announced an empty payload. -/
  | empty
  /-- A header announced more than `maxPayload` bytes. -/
  | tooLarge (announced : Nat)
  deriving Repr, BEq, DecidableEq

/-- Bytes received and not yet returned as a payload: at most one incomplete frame. -/
structure Decoder where
  pending : ByteArray := ByteArray.empty

/-- Takes whole frames off `buf` from `pos`. Returns where the first incomplete frame starts and the payloads
before it. `fuel` bounds the number of frames; each takes at least five bytes. -/
def drain (buf : ByteArray) : (fuel : Nat) → (pos : Nat) → Array ByteArray → Except Fault (Nat × Array ByteArray)
  | 0, pos, out => .ok (pos, out)
  | fuel + 1, pos, out =>
    if buf.size < pos + 4 then .ok (pos, out) else
    let n := readU32be buf pos
    if n == 0 then .error .empty
    else if n > maxPayload then .error (.tooLarge n)
    else if buf.size < pos + 4 + n then .ok (pos, out)
    else drain buf fuel (pos + 4 + n) (out.push (buf.extract (pos + 4) (pos + 4 + n)))

/-- Adds received bytes and returns every payload they complete, in order. A fault is decided from a header
alone, before any of its payload is buffered, so `pending` never exceeds one frame plus what one call adds. -/
def Decoder.feed (d : Decoder) (bytes : ByteArray) : Except Fault (Decoder × Array ByteArray) := do
  let buf := d.pending ++ bytes
  let (pos, payloads) ← drain buf (buf.size / 5 + 1) 0 #[]
  return ({ pending := buf.extract pos buf.size }, payloads)

end Demo.Wire
