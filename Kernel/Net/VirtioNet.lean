import Kernel.Hw
import Kernel.Virtq
import Kernel.Net.Flat

/-! A driver for the virtio network card, for frames in batches: what `Kernel/Net/Flat.lean` needs under
it. Modern virtio over PCI, split queues, polled. It is not the system's virtio (`Kernel/Virtio.lean`),
which is another transport and is made for a few small messages; that one is left as it is.

How it is fast where the firmware's driver is not. The firmware's takes one frame a call and tells the
host about every frame, each way. Here:

* The buffers are set up once and never move: descriptor `i` is buffer `i`, for good, in each direction.
* `receive` takes everything the card has finished with in one go and copies each frame once, into the
  array the stack reads, with its length before it; then gives all those buffers back and tells the host
  once.
* `transmit` copies every frame the stack wrote into the next buffers in turn and tells the host once,
  and not even once when the card says it is already looking (`tell`).
* Nothing is allocated in either: what is read from the shared memory is read into arrays that are there
  already.

The host, which is the other end of the shared memory. It can write anything there at any time, and an
honest one writes there all the time: a queue's position is two bytes that the other side changes while
this side reads, so each is read and written in one go (`Hw.load16`, `Hw.store16`), never as two bytes one
after the other. So what is read from it is read once into this program's own memory and only that copy
is looked at: the count
of what the card has finished is cut to the queue's size, a buffer's number is taken modulo the size, a
length is cut to the buffer's. Descriptors are never read back. What the host can do by lying is lose
or spoil frames, which it can do anyway. No feature is asked for that would have the card hand over a
frame unfinished (no checksum or segmentation left to this end, no frame across several buffers).

Not done: more than one pair of queues; frames longer than one buffer. -/

namespace Kernel.Net.VirtioNet

open Kernel
open Kernel.Net.Flat (rd8 rd16 ld32 st32 wr8 wr16)

/-- Bytes to a buffer: the card's twelve of its own, then a frame, with room to spare. -/
def stride : USize := 2048

/-- What the card puts before each frame, and wants before each one sent: twelve bytes, all nothing here. -/
def header : USize := 12

@[inline] def le16 (b : @& ByteArray) (i : USize) : UInt16 :=
  (rd8 b i).toUInt16 ||| ((rd8 b (i + 1)).toUInt16 <<< 8)

@[inline] def putLe16 (b : ByteArray) (i : USize) (v : UInt16) : ByteArray :=
  wr8 (wr8 b i v.toUInt8) (i + 1) (v >>> 8).toUInt8

/-- What does not change once the card is set up. -/
structure Card where
  /-- Entries in each queue: a power of two. -/
  size : USize
  /-- Where the host is told that a queue has something for it. -/
  tellRx : UInt64
  tellTx : UInt64
  /-- In the shared memory: each queue's ring of what is offered, ring of what is finished, and buffers. -/
  rxOffered : UInt64
  rxFinished : UInt64
  rxBuffers : UInt64
  txOffered : UInt64
  txFinished : UInt64
  txBuffers : UInt64
  txDescriptors : UInt64
  /-- The card's Ethernet address: its first two bytes and its last four. -/
  macHigh : UInt16
  macLow : UInt32
  deriving Inhabited

/-- What changes: how far each ring has been used, by this end's own count. -/
structure Rings where
  /-- Receive: finished entries taken so far, and buffers offered so far. -/
  taken : UInt16 := 0
  given : UInt16 := 0
  /-- Transmit: frames offered so far, and those the card has finished with. -/
  sent : UInt16 := 0
  done : UInt16 := 0
  /-- Frames not sent because the card had not finished with any buffer in time. -/
  dropped : Nat := 0
  /-- Frames taken from the card and given to it, and the times the host was told of either: what leaving
  the guest costs is the second over the first. -/
  frames : Nat := 0
  calls : Nat := 0
  deriving Inhabited

/-- An array to read the shared memory into: room for one queue's ring of finished entries, then for the
numbers of the buffers given back. -/
def scratchFor (card : Card) : ByteArray := Flat.zeros (card.size.toNat * 10 + 16)

/-- The parts of a virtio card, found through the chain of capabilities in its configuration: where its
common registers are, where the host is told, by how much a queue's number is multiplied there, and where
the card's own settings are. Addresses are in the windows as `Kernel/Hw.lean` numbers them. -/
structure Parts where
  common : UInt64 := 0
  tell : UInt64 := 0
  multiplier : UInt32 := 0
  own : UInt64 := 0

def parts (index : USize) : BaseIO Parts := do
  let mut found : Parts := {}
  let mut at_ := (← Hw.config index 0x34 1) &&& 0xfc
  for _ in [0:48] do
    if at_ == 0 then break
    let kind ← Hw.config index at_ 1
    let next ← Hw.config index (at_ + 1) 1
    if kind == 9 then
      let part ← Hw.config index (at_ + 3) 1
      let window ← Hw.config index (at_ + 4) 1
      let offset ← Hw.config index (at_ + 8) 4
      let address := ((window.toUInt64 + 1) <<< 32) ||| offset.toUInt64
      if window < 6 then
        if part == 1 then found := { found with common := address }
        if part == 2 then found := { found with tell := address, multiplier := ← Hw.config index (at_ + 16) 4 }
        if part == 4 then found := { found with own := address }
    at_ := next &&& 0xfc
  return found

/-- The first virtio network card among the PCI devices, by its numbers. -/
def find : BaseIO (Option USize) := do
  for i in [0:(← Hw.devices).toNat] do
    if (← Hw.config i.toUSize 0 4) == 0x10411af4 then return some i.toUSize
  return none

/-- One queue made ready: its size agreed, its three tables put in shared memory and the card told where,
and the place the host is told about it. `writes` says whether the card writes into its buffers (receive)
or reads them. -/
def queue (p : Parts) (number : UInt16) (wanted : USize) (writes : Bool) :
    BaseIO (Option (USize × UInt64 × UInt64 × UInt64 × UInt64 × UInt64)) := do
  let c := p.common
  Hw.write (c + 22) 2 number.toUInt32
  let most := (← Hw.read (c + 24) 2).toUSize
  -- The largest power of two that both ends will take.
  let mut size : USize := 1
  while size * 2 ≤ wanted && size * 2 ≤ most do size := size * 2
  if most == 0 || size < 8 then return none
  Hw.write (c + 24) 2 size.toUInt32
  Hw.write (c + 26) 2 0xffff
  let layout := Virtq.Layout.of size.toNat
  let tables ← Hw.alloc layout.bytes.toUSize
  let buffers ← Hw.alloc (size * stride)
  if tables == 0 || buffers == 0 then return none
  -- Descriptor `i` is buffer `i`. For receive each is the whole buffer, for the card to write; for
  -- transmit the length is set when a frame is put there.
  let descriptors := (List.range size.toNat).foldl (fun out i =>
    out ++ Virtq.descriptor (buffers + (i.toUSize * stride).toUInt64) (if writes then stride.toNat else header.toNat)
      (if writes then Virtq.flagWrite else 0) 0) ByteArray.empty
  Hw.store (tables + layout.descriptors.toUInt64) descriptors
  -- The ring of what is offered: no interrupt wanted, and entry `i` naming buffer `i`.
  let offered := (List.range size.toNat).foldl (fun out i => out ++ Virtq.le i 2) (Virtq.le 1 2 ++ Virtq.le 0 2)
  Hw.store (tables + layout.available.toUInt64) offered
  let place (register : UInt64) (address : UInt64) : BaseIO Unit := do
    Hw.write register 4 address.toUInt32
    Hw.write (register + 4) 4 (address >>> 32).toUInt32
  place (c + 32) (tables + layout.descriptors.toUInt64)
  place (c + 40) (tables + layout.available.toUInt64)
  place (c + 48) (tables + layout.used.toUInt64)
  let where_ ← Hw.read (c + 30) 2
  Hw.write (c + 28) 2 1
  return some (size, p.tell + (where_ * p.multiplier).toUInt64, tables + layout.available.toUInt64,
               tables + layout.used.toUInt64, buffers, tables + layout.descriptors.toUInt64)

/-- The card found, taken from the firmware, and made ready with one queue each way of up to `wanted`
entries, every receive buffer offered. Nothing if there is no such card or it will not do. -/
def start (wanted : USize := 256) : BaseIO (Option (Card × Rings)) := do
  let some index ← find | return none
  let p ← parts index
  if p.common == 0 || p.tell == 0 || p.own == 0 then return none
  if !(← Hw.claim index) then return none
  let c := p.common
  -- Reset; say there is a driver; agree on what the card may do.
  Hw.write (c + 20) 1 0
  Hw.write (c + 20) 1 3
  Hw.write c 4 0
  let low ← Hw.read (c + 4) 4
  Hw.write c 4 1
  let high ← Hw.read (c + 4) 4
  -- It must be a modern card. Taken: that it has an Ethernet address, and, when it says so, that its
  -- memory is the kind the host is given on purpose (a trust domain). Nothing else.
  if high &&& 1 == 0 then return none
  Hw.write (c + 8) 4 0
  Hw.write (c + 12) 4 (low &&& 0x20)
  Hw.write (c + 8) 4 1
  Hw.write (c + 12) 4 ((high &&& 2) ||| 1)
  Hw.write (c + 20) 1 11
  if (← Hw.read (c + 20) 1) &&& 8 == 0 then return none
  let some (size, tellRx, rxOffered, rxFinished, rxBuffers, _) ← queue p 0 wanted true | return none
  let some (size', tellTx, txOffered, txFinished, txBuffers, txDescriptors) ← queue p 1 size false | return none
  if size' != size then return none
  let macHigh := ((← Hw.read p.own 1) <<< 8) ||| (← Hw.read (p.own + 1) 1)
  let macLow := ((← Hw.read (p.own + 2) 1) <<< 24) ||| ((← Hw.read (p.own + 3) 1) <<< 16) |||
    ((← Hw.read (p.own + 4) 1) <<< 8) ||| (← Hw.read (p.own + 5) 1)
  -- Every receive buffer is offered, and the card is told to go.
  Hw.store16 (rxOffered + 2) size.toUInt16
  Hw.write (c + 20) 1 15
  Hw.write tellRx 2 0
  return some ({ size, tellRx, tellTx, rxOffered, rxFinished, rxBuffers, txOffered, txFinished, txBuffers,
                 txDescriptors, macHigh := macHigh.toUInt16, macLow },
               { given := size.toUInt16 })

/-- The host told that queue `number` has something for it, unless the card says, in the first two bytes of
its ring of finished entries, that it is looking already and need not be told. Telling is the one thing
here that leaves the guest, and in a trust domain it is dear; a card that is kept busy says so nearly
all the time. It says so and then looks once more before it stops looking, and `Hw.store16`, by which it
was given what to look at, is seen by it before this reads its word: so nothing is missed. What comes
back is 1 if the host was told. -/
@[inline] def tell (register finished : UInt64) (number : UInt32) : BaseIO Nat := do
  if (← Hw.load16 finished) &&& 1 == 0 then
    Hw.write register 2 number
    return 1
  else return 0

/-- Everything the card has received since the last call, copied into `batch` as the stack takes it (two
bytes of length, then the frame, one after another), and the buffers given back. `scratch` is from
`scratchFor`. What comes back: the rings, `scratch`, `batch`, and how many bytes of `batch` are frames. -/
def receive (card : @& Card) (rings : Rings) (scratch batch : ByteArray) : BaseIO (Rings × ByteArray × ByteArray × USize) := do
  let size := card.size
  let mask := size - 1
  -- How many more the card says it has finished: its word, read in one go (it changes as we look) and cut
  -- to what there can be.
  let claimed := ((← Hw.load16 (card.rxFinished + 2)) - rings.taken).toUSize
  let count := if claimed > size then size else claimed
  if count == 0 then return (rings, scratch, batch, 0)
  -- Those entries of the ring, copied out once: eight bytes each, a buffer's number and a length.
  let first := rings.taken.toUSize &&& mask
  let run := if count < size - first then count else size - first
  let mut scratch ← Hw.loadInto (card.rxFinished + 4 + (first * 8).toUInt64) scratch 0 (run * 8)
  if run < count then scratch ← Hw.loadInto (card.rxFinished + 4) scratch (run * 8) ((count - run) * 8)
  let mut batch := batch
  let mut at_ : USize := 0
  let numbers := size * 8
  for k in [0:count.toNat] do
    let entry := k.toUSize * 8
    let buffer := (ld32 scratch entry).toUSize &&& mask
    let said := (ld32 scratch (entry + 4)).toUSize
    let length := (if said > stride then stride else said) - header
    -- A frame is at least an Ethernet header and no more than a buffer holds; anything else is skipped.
    if said ≥ header + 14 && at_ + 2 + length ≤ batch.usize then
      batch := wr16 batch at_ length.toUInt16
      batch ← Hw.loadInto (card.rxBuffers + (buffer * stride + header).toUInt64) batch (at_ + 2) length
      at_ := at_ + 2 + length
    scratch := putLe16 scratch (numbers + k.toUSize * 2) buffer.toUInt16
  -- The same buffers offered again, in the places after those already offered, and the host told once.
  let next := rings.given.toUSize &&& mask
  let run := if count < size - next then count else size - next
  Hw.storeFrom (card.rxOffered + 4 + (next * 2).toUInt64) scratch numbers (run * 2)
  if run < count then Hw.storeFrom (card.rxOffered + 4) scratch (numbers + run * 2) ((count - run) * 2)
  let given := rings.given + count.toUInt16
  Hw.store16 (card.rxOffered + 2) given
  let told ← tell card.tellRx card.rxFinished 0
  return ({ rings with taken := rings.taken + count.toUInt16, given, frames := rings.frames + count.toNat,
                       calls := rings.calls + told }, scratch, batch, at_)

/-- Every frame the stack wrote to `tx` (from its ninth byte to where its first eight say) put into the
card's buffers in turn, and the host told once. When every buffer is still with the card it is waited
for, asking `patience` times how far the card has got (some tens of milliseconds as it is set); what
cannot be sent then is dropped and counted, and the stack will send it again. A stack that writes more
in one go than the card has buffers leans on this wait: a frame dropped here costs its connection a
timer. -/
def transmit (card : @& Card) (rings : Rings) (scratch : ByteArray) (tx : @& ByteArray) (patience : Nat := 400000) :
    BaseIO (Rings × ByteArray) := do
  let stop := Flat.written tx
  if stop ≤ 8 then return (rings, scratch)
  let size := card.size
  let mask := size - 1
  let mut rings := rings
  let mut scratch := scratch
  let mut o : USize := 8
  let mut told := rings.sent
  while o + 2 ≤ stop do
    let length := (rd16 tx o).toUSize
    if length < 14 || length > stride - header || o + 2 + length > stop then break
    if (rings.sent - rings.done).toUSize ≥ size then
      -- Full. What is queued is handed over, and the card is asked how far it has got, a few thousand
      -- times at most.
      if told != rings.sent then
        Hw.store16 (card.txOffered + 2) rings.sent
        rings := { rings with calls := rings.calls + (← tell card.tellTx card.txFinished 1) }
        told := rings.sent
      let mut tries := 0
      while (rings.sent - rings.done).toUSize ≥ size && tries < patience do
        let finished ← Hw.load16 (card.txFinished + 2)
        -- Its word again: believed only if it is between what was known and what was sent.
        if (finished - rings.done) ≤ (rings.sent - rings.done) then rings := { rings with done := finished }
        if (rings.sent - rings.done).toUSize ≥ size then Hw.pause
        tries := tries + 1
      if (rings.sent - rings.done).toUSize ≥ size then
        rings := { rings with dropped := rings.dropped + 1 }
        o := o + 2 + length
        continue
    let buffer := rings.sent.toUSize &&& mask
    Hw.storeFrom (card.txBuffers + (buffer * stride + header).toUInt64) tx (o + 2) length
    scratch := st32 scratch 4 (header + length).toUInt32
    Hw.storeFrom (card.txDescriptors + (buffer * 16 + 8).toUInt64) scratch 4 4
    rings := { rings with sent := rings.sent + 1, frames := rings.frames + 1 }
    o := o + 2 + length
  if told != rings.sent then
    Hw.store16 (card.txOffered + 2) rings.sent
    rings := { rings with calls := rings.calls + (← tell card.tellTx card.txFinished 1) }
  -- How far the card has got, for next time.
  let finished ← Hw.load16 (card.txFinished + 2)
  if (finished - rings.done) ≤ (rings.sent - rings.done) then rings := { rings with done := finished }
  return (rings, scratch)

end Kernel.Net.VirtioNet
