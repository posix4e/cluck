import Kernel.Efi
import Kernel.Net.VirtioNet
import Kernel.Net.Gvnic

/-! Ethernet frames one at a time, for the system's TCP (`Kernel/Net/Tcp.lean`) and whatever else takes
frames singly: from this program's own driver for the card when the machine has a card it drives, and
from the firmware's driver (`Kernel/Efi.lean`) when it has not. Two cards are driven: the virtio card
QEMU gives a guest (`Kernel/Net/VirtioNet.lean`) and the card Google's machines have
(`Kernel/Net/Gvnic.lean`), looked for in that order.

The firmware hands over one frame a call and tells the host of every one; a megabyte came in at six
megabytes a second that way. The driver here takes what the card has in one go and hands the frames on
from its own memory, and gives the card everything that is to be sent at once.

`start` says whether there is such a card and gives what stands for it, which whoever uses it keeps and
hands to `receive` and `sendAll` and takes back from them; there are no references in this runtime to
keep it in. With no such card the frames are the firmware's, as before.

Which card is there also says where the machine is, and with that what is around it (`around`): the
way out, the name server, how large a packet the network carries. One image can then run in both
places. The card is the host's to show, so this is the host's word, like every answer of the network
it names. -/

namespace Kernel.Net.Wire

open Kernel Kernel.Net

inductive Driver where
  | virtio (card : VirtioNet.Card) (rings : VirtioNet.Rings)
  | gvnic (card : Gvnic.Card) (rings : Gvnic.Rings)

/-- The card and what goes with it: frames taken from it and not yet handed on are in `batch` from `at_`
to `length`, each with its length in two bytes before it; `tx` is where frames to be sent are gathered. -/
structure Own where
  driver : Driver
  scratch : ByteArray
  batch : ByteArray
  length : USize
  at_ : USize
  tx : ByteArray

/-- The network a card is taken to be on: the address everything not on the link goes by, how many
bits of this machine's address the link's other machines share with it, the name server, and the
largest TCP segment to ask for over IPv4. -/
structure Around where
  gateway : ByteArray
  onLink : Nat
  resolver : ByteArray
  mss : UInt16

/-- QEMU's own network for the virtio card. For Google's: the subnet's first address is the way out and
nothing else is on the link, names are asked of the metadata server, and a segment is forty bytes less
than the packet size the card gives (1,460 there), within what an Ethernet can carry. -/
def around (w : @& Own) : Around :=
  match w.driver with
  | .virtio _ _ => { gateway := ⟨#[10, 0, 2, 2]⟩, onLink := 24, resolver := ⟨#[10, 0, 2, 3]⟩, mss := 1460 }
  | .gvnic card _ =>
    let packet := min 1500 (max 576 card.mtu.toNat)
    { gateway := ⟨#[10, 0, 2, 1]⟩, onLink := 32, resolver := ⟨#[169, 254, 169, 254]⟩, mss := (packet - 40).toUInt16 }

/-- Whether Google's card is among the machine's devices. -/
private def googles : BaseIO Bool := do
  let mut found := false
  for i in [0:(← Hw.devices).toNat] do
    if (← Hw.config i.toUSize 0 4) == 0x00421ae0 then found := true
  return found

/-- The card taken from the firmware, if there is one this program drives, and a line about it. With no
card of either kind, nothing and no line; with one that could not be brought up, nothing and why. Only
one device can be taken, so the second kind is looked for only when the first is not there. -/
def start : BaseIO (Option Own × String) := do
  match ← VirtioNet.start 256 with
  | some (card, rings) =>
    return (some { driver := .virtio card rings, scratch := VirtioNet.scratchFor card,
                   batch := Flat.zeros (card.size.toNat * 1520), length := 0, at_ := 0, tx := Flat.outbox 65536 },
            "a virtio card")
  | none =>
    if !(← googles) then return (none, "")
    match ← Gvnic.start with
    | .error why => return (none, why)
    | .ok (card, rings, notes) =>
      -- The card hands frames over in places of 2,048 bytes; a batch has room for every place full.
      return (some { driver := .gvnic card rings, scratch := Gvnic.scratchFor card,
                     batch := Flat.zeros (card.rxSize.toNat * 2050), length := 0, at_ := 0, tx := Flat.outbox 65536 },
              s!"Google's card, packets of {card.mtu}: {notes}")

/-- The card's Ethernet address, six bytes. -/
def mac (w : @& Own) : ByteArray :=
  let (high, low) := match w.driver with
    | .virtio card _ => (card.macHigh, card.macLow)
    | .gvnic card _ => (card.macHigh, card.macLow)
  ByteArray.mk #[(high >>> 8).toUInt8, high.toUInt8, (low >>> 24).toUInt8, (low >>> 16).toUInt8, (low >>> 8).toUInt8, low.toUInt8]

/-- What the card has, taken into `batch`. -/
private def take (driver : Driver) (scratch batch : ByteArray) : BaseIO (Driver × ByteArray × ByteArray × USize) := do
  match driver with
  | .virtio card rings =>
    let (rings, scratch, batch, length) ← VirtioNet.receive card rings scratch batch
    return (.virtio card rings, scratch, batch, length)
  | .gvnic card rings =>
    let (rings, scratch, batch, length) ← Gvnic.receive card rings scratch batch
    return (.gvnic card rings, scratch, batch, length)

/-- What is gathered in `tx`, given to the card. -/
private def give (driver : Driver) (scratch : ByteArray) (tx : @& ByteArray) : BaseIO (Driver × ByteArray) := do
  match driver with
  | .virtio card rings =>
    let (rings, scratch) ← VirtioNet.transmit card rings scratch tx
    return (.virtio card rings, scratch)
  | .gvnic card rings =>
    let (rings, scratch) ← Gvnic.transmit card rings scratch tx
    return (.gvnic card rings, scratch)

/-- The next frame, or nothing when the card has none. Whoever calls this must hold `w` and nothing else
that holds it, so that the arrays in it have one owner and are changed where they lie. -/
def receive (w : Own) : BaseIO (Own × ByteArray) := do
  let ⟨driver, scratch, batch, length, at_, tx⟩ := w
  if at_ + 2 ≤ length then
    let n := (Flat.rd16 batch at_).toUSize
    let frame := batch.extract (at_ + 2).toNat (at_ + 2 + n).toNat
    return (⟨driver, scratch, batch, length, at_ + 2 + n, tx⟩, frame)
  else
    let (driver, scratch, batch, length) ← take driver scratch batch
    if length < 2 then return (⟨driver, scratch, batch, 0, 0, tx⟩, ByteArray.empty)
    else
      let n := (Flat.rd16 batch 0).toUSize
      let frame := batch.extract 2 (2 + n).toNat
      return (⟨driver, scratch, batch, length, 2 + n, tx⟩, frame)

/-- A card that says it wants to be started over, started over; and a line about it, or no line when it
wanted nothing, which is nearly always. Only Google's card asks. What it held either way is lost; the
frames already taken from it stay to be handed on. To be called now and then: asking costs a question
to the host. -/
def mend (w : Own) : BaseIO (Own × String) := do
  let ⟨driver, scratch, batch, length, at_, tx⟩ := w
  match driver with
  | .virtio card rings => return (⟨.virtio card rings, scratch, batch, length, at_, tx⟩, "")
  | .gvnic card rings =>
    if !(← Gvnic.wantsReset card) then return (⟨.gvnic card rings, scratch, batch, length, at_, tx⟩, "")
    match ← Gvnic.restart card with
    | .ok (card, rings, notes) =>
      return (⟨.gvnic card rings, Gvnic.scratchFor card, batch, length, at_, tx⟩,
              s!"the network card asked to be started over, and was: {notes}")
    | .error why =>
      return (⟨.gvnic card rings, scratch, batch, length, at_, tx⟩,
              s!"the network card asked to be started over and did not come up: {why}")

/-- `frames` from the `i`-th on gathered into `tx`, and given to the card whenever `tx` is full and at the
end. A frame no Ethernet could carry is left out. -/
partial def gather (frames : @& Array ByteArray) (i : Nat) (driver : Driver)
    (scratch tx : ByteArray) : BaseIO (Driver × ByteArray × ByteArray) := do
  if h : i < frames.size then
    let frame := frames[i]
    let n := frame.usize
    let at_ := Flat.written tx
    if n < 14 || n > 1514 then gather frames (i + 1) driver scratch tx
    else if at_ + 2 + n > tx.usize then
      let (driver, scratch) ← give driver scratch tx
      gather frames i driver scratch (Flat.st64 tx 0 8)
    else
      let tx := frame.copySlice 0 (Flat.wr16 tx at_ n.toUInt16) (at_ + 2).toNat n.toNat
      gather frames (i + 1) driver scratch (Flat.st64 tx 0 (at_ + 2 + n).toUInt64)
  else
    let (driver, scratch) ← give driver scratch tx
    return (driver, scratch, Flat.st64 tx 0 8)

/-- Frames sent, in order. -/
def sendAll (w : Own) (frames : @& Array ByteArray) : BaseIO Own := do
  let ⟨driver, scratch, batch, length, at_, tx⟩ := w
  let (driver, scratch, tx) ← gather frames 0 driver scratch (Flat.st64 tx 0 8)
  return ⟨driver, scratch, batch, length, at_, tx⟩

end Kernel.Net.Wire
