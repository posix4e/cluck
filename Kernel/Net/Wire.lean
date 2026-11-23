import Kernel.Efi
import Kernel.Net.VirtioNet

/-! Ethernet frames one at a time, for the system's TCP (`Kernel/Net/Tcp.lean`) and whatever else takes
frames singly: from this program's own driver for the card (`Kernel/Net/VirtioNet.lean`) when the machine
has a card it drives, and from the firmware's driver (`Kernel/Efi.lean`) when it has not.

The firmware hands over one frame a call and tells the host of every one; a megabyte came in at six
megabytes a second that way. The driver here takes what the card has in one go and hands the frames on
from its own memory, and gives the card everything that is to be sent at once.

`start` says whether there is such a card and gives what stands for it, which whoever uses it keeps and
hands to `receive` and `sendAll` and takes back from them; there are no references in this runtime to
keep it in. With no such card the frames are the firmware's, as before. -/

namespace Kernel.Net.Wire

open Kernel Kernel.Net

/-- The card and what goes with it: frames taken from it and not yet handed on are in `batch` from `at_`
to `length`, each with its length in two bytes before it; `tx` is where frames to be sent are gathered. -/
structure Own where
  card : VirtioNet.Card
  rings : VirtioNet.Rings
  scratch : ByteArray
  batch : ByteArray
  length : USize
  at_ : USize
  tx : ByteArray

/-- The card taken from the firmware, if there is one this program drives. -/
def start : BaseIO (Option Own) := do
  match ← VirtioNet.start 256 with
  | none => return none
  | some (card, rings) =>
    return some { card, rings, scratch := VirtioNet.scratchFor card, batch := Flat.zeros (card.size.toNat * 1520),
                  length := 0, at_ := 0, tx := Flat.outbox 65536 }

/-- The card's Ethernet address, six bytes. -/
def mac (w : @& Own) : ByteArray :=
  let high := w.card.macHigh
  let low := w.card.macLow
  ByteArray.mk #[(high >>> 8).toUInt8, high.toUInt8, (low >>> 24).toUInt8, (low >>> 16).toUInt8, (low >>> 8).toUInt8, low.toUInt8]

/-- The next frame, or nothing when the card has none. Whoever calls this must hold `w` and nothing else
that holds it, so that the arrays in it have one owner and are changed where they lie. -/
def receive (w : Own) : BaseIO (Own × ByteArray) := do
  let ⟨card, rings, scratch, batch, length, at_, tx⟩ := w
  if at_ + 2 ≤ length then
    let n := (Flat.rd16 batch at_).toUSize
    let frame := batch.extract (at_ + 2).toNat (at_ + 2 + n).toNat
    return (⟨card, rings, scratch, batch, length, at_ + 2 + n, tx⟩, frame)
  else
    let (rings, scratch, batch, length) ← VirtioNet.receive card rings scratch batch
    if length < 2 then return (⟨card, rings, scratch, batch, 0, 0, tx⟩, ByteArray.empty)
    else
      let n := (Flat.rd16 batch 0).toUSize
      let frame := batch.extract 2 (2 + n).toNat
      return (⟨card, rings, scratch, batch, length, 2 + n, tx⟩, frame)

/-- `frames` from the `i`-th on gathered into `tx`, and given to the card whenever `tx` is full and at the
end. A frame no Ethernet could carry is left out. -/
partial def gather (card : @& VirtioNet.Card) (frames : @& Array ByteArray) (i : Nat) (rings : VirtioNet.Rings)
    (scratch tx : ByteArray) : BaseIO (VirtioNet.Rings × ByteArray × ByteArray) := do
  if h : i < frames.size then
    let frame := frames[i]
    let n := frame.usize
    let at_ := Flat.written tx
    if n < 14 || n > 1514 then gather card frames (i + 1) rings scratch tx
    else if at_ + 2 + n > tx.usize then
      let (rings, scratch) ← VirtioNet.transmit card rings scratch tx
      gather card frames i rings scratch (Flat.st64 tx 0 8)
    else
      let tx := frame.copySlice 0 (Flat.wr16 tx at_ n.toUInt16) (at_ + 2).toNat n.toNat
      gather card frames (i + 1) rings scratch (Flat.st64 tx 0 (at_ + 2 + n).toUInt64)
  else
    let (rings, scratch) ← VirtioNet.transmit card rings scratch tx
    return (rings, scratch, Flat.st64 tx 0 8)

/-- Frames sent, in order. -/
def sendAll (w : Own) (frames : @& Array ByteArray) : BaseIO Own := do
  let ⟨card, rings, scratch, batch, length, at_, tx⟩ := w
  let (rings, scratch, tx) ← gather card frames 0 rings scratch (Flat.st64 tx 0 8)
  return ⟨card, rings, scratch, batch, length, at_, tx⟩

end Kernel.Net.Wire
