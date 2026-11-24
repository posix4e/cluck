import Kernel.Hw
import Kernel.Net.Flat

/-! A driver for Google's virtual network card (gVNIC, PCI 1ae0:0042), the only card a trust domain on
Compute Engine has, in its plainest way of working: one queue each way, descriptors and counts most
significant byte first ("GQI"), and every frame copied through pages the card has been told of
beforehand ("queue page lists"). It asks the card for nothing by interrupt and looks instead, as
`Kernel/Net/VirtioNet.lean` does, and it gives its frames in the same batches, so that what runs on the
one runs on the other.

Written from the card's interface as Linux's driver for it sets it down (`drivers/net/ethernet/google/
gve`: its register, admin-queue and descriptor headers and its documentation), not from that driver's
code. It can only be tried where the card is: no emulator here has one.

How the card is brought up, in the order it wants:

* it is reset, and told where a page is in which commands will be put to it (the admin queue: 64 commands
  of 64 bytes, a count of commands put written to one register, a count of commands done read from
  another);
* it is asked to describe itself: how long its queues are, its Ethernet address, how many pages it will
  be told of;
* it is given a place for the counts it keeps and for the numbers of its interrupt doorbells, of which
  it wants two though none is ever used here;
* it is told the pages frames will be in: for sending, as many as it says; for receiving, one a place in
  the queue;
* it is told how long a packet may be, and the two queues are made;
* the interrupt doorbells are told to stay quiet, and for receiving every place but one is handed over
  (told that all are, the card takes it that none is).

**The two ways of working.** The above is the older (GQI), which the cards of older machines have and
no other (`n2-standard-2`: it sends and receives, and the trial TCP served pages over it). The cards of
the machines that can be trust domains (the C3 series) take the older way's commands and then move
nothing; they have a newer way (DQO, with addresses as they are), which is used when a card lists it.
In it nothing is told of beforehand, descriptors carry addresses of this driver's own shared memory,
everything is least significant byte first, and the card writes what it has sent and what has come into
rings of its own with a bit that says which turn of the ring an entry is of.

**Doorbells are written by the processor itself** (`Hw.writeDirect`), not by way of the firmware. In a
trust domain the firmware has the host carry out every register access; this card's doorbells are the
card's own hardware and do not hear of an access carried out that way, so that every command was taken
and nothing ever moved. Linux writes them directly too.

Sending: a frame is copied into the sending pages, which are cut into places of 2,048 bytes taken in
turn (the card gives few pages, 64 where this was written, so there are fewer places than descriptors,
and no more frames are with the card at once than there are places); then one or two descriptors say
where and how long (the first at most 182 bytes, as Linux has it; whether
the card would take one for a whole frame was not known when this was written), then the count of
descriptors is written to the queue's doorbell. How far the card has got is a count it keeps in memory.

Receiving: the card writes a descriptor for each frame with a number from 1 to 7 that goes round; a
descriptor is new when it carries the number expected. The frame is two bytes into its place's page.

Who is on the other side: the host. Every length and number of the card's is cut to what it can be before
it is used, and the memory shared with the card is the only memory any of it can name. A card that lies
gets frames lost or the machine stopped, as it can anyway.

**The card can start over by itself, or ask to be started over** (`bringUp` says what was seen). Either
way it is reset and made ready again from nothing in the same memory; whoever drives it asks now and
then whether that has happened (`wantsReset`, `restart`). Frames on their way at that moment are lost,
as on any network.

Not done: more than one queue; frames longer than a buffer (they are dropped); checksums or segmenting
left to the card. -/

namespace Kernel.Net.Gvnic

open Kernel
open Kernel.Net.Flat

@[inline] def swap32 (v : UInt32) : UInt32 :=
  (v >>> (24 : UInt32)) ||| ((v >>> (8 : UInt32)) &&& (0xff00 : UInt32)) ||| ((v <<< (8 : UInt32)) &&& (0xff0000 : UInt32)) ||| (v <<< (24 : UInt32))

@[inline] def swap16 (v : UInt16) : UInt16 := (v >>> (8 : UInt16)) ||| (v <<< (8 : UInt16))

/-- A register of the card's: four bytes, most significant first. -/
@[inline] def reg (address : UInt64) : BaseIO UInt32 := do return swap32 (← Hw.read address 4)

@[inline] def setReg (address : UInt64) (value : UInt32) : BaseIO Unit := Hw.write address 4 (swap32 value)

@[inline] def wr64 (b : ByteArray) (i : USize) (v : UInt64) : ByteArray :=
  wr32 (wr32 b i (v >>> 32).toUInt32) (i + 4) v.toUInt32

/-- The most a frame's first descriptor may say, as Linux's driver has it. -/
def firstMost : USize := 182

/-- What stays the same however often the card is started over: where its registers and doorbells are,
its revision, and the memory shared with it. `fixed` is three pages taken when the card is claimed (the
commands, what this driver is, what the card is); `rest` is everything whose size the card's own
description decides, taken the first time the card has described itself and laid out the same way
every time after, which `shape` (the sizes, in one number) holds it to. Shared memory is never given
back, so a card started over must be given the same memory again. -/
structure Ground where
  registers : UInt64 := 0
  doorbells : UInt64 := 0
  bellRoom : UInt64 := 0
  revision : UInt32 := 0
  fixed : UInt64 := 0
  rest : UInt64 := 0
  shape : UInt64 := 0
  deriving Inhabited

structure Card where
  ground : Ground := {}
  registers : UInt64
  doorbells : UInt64
  macHigh : UInt16
  macLow : UInt32
  mtu : UInt16
  /-- Sending: the descriptors, the pages frames are copied to, how many descriptors, how many places of
  2,048 bytes the pages make, the queue's doorbell, and where the card keeps its count of descriptors
  done. -/
  txRing : UInt64
  txPages : UInt64
  txSize : USize
  txSlots : USize
  txBell : UInt64
  txCount : UInt64
  /-- Receiving: the descriptors, the pages, how many places, the queue's doorbell. -/
  rxDesc : UInt64
  rxPages : UInt64
  rxSize : USize
  rxBell : UInt64
  /-- Whether the card is worked the newer way (below), and for that way: where it writes what it has
  done of what was sent, and where places for receiving are offered to it. -/
  newer : Bool := false
  txDone : UInt64 := 0
  rxOffer : UInt64 := 0
  /-- How many commands the card has been given, which is what its count of commands done reads for
  as long as it has not started over. -/
  asked : UInt32 := 0
  deriving Inhabited

structure Rings where
  /-- Sending: descriptors given to the card, those it has done, and frames given. -/
  posted : UInt32 := 0
  finished : UInt32 := 0
  serial : UInt32 := 0
  /-- Receiving: descriptors taken, the number the next must carry, and places handed over. -/
  taken : UInt32 := 0
  expected : UInt16 := 1
  filled : UInt32 := 0
  dropped : UInt64 := 0
  frames : UInt64 := 0
  calls : UInt64 := 0
  waits : UInt64 := 0
  /-- The newer way only: how far what the card has done of the sending has been read, which turn of that
  ring it is, and how many descriptors have gone since the card was last asked to say how far it is. -/
  doneAt : UInt32 := 0
  doneTurn : UInt16 := 1
  since : UInt32 := 0
  deriving Inhabited

/-- An array to make descriptors in: its first 32 bytes are written, those to 128 stay nothing and are
what a short frame is filled out with, and from 128 on there is a byte for each place frames are sent
from, 1 while a frame in it is still the card's (the newer way of working needs that kept). -/
def scratchFor (card : Card) : ByteArray := zeros (128 + card.txSlots.toNat)

/-- A command to the card: its number, then nothing, to be filled in. -/
def commandOf (opcode : UInt32) : ByteArray := wr32 (zeros 64) 0 opcode

/-- One command put to the card and waited for. `queue` is the page of commands and `count` how many
were put before this one. What comes back is what the card says of it: 1 is done, 0 that it never
answered. -/
def command (registers queue : UInt64) (count : UInt32) (body : ByteArray) : BaseIO (UInt32 × String) := do
  let slot := queue + (count &&& 63).toUInt64 * 64
  Hw.store slot (body.extract 0 64)
  setReg (registers + 20) (count + 1)
  -- Waited for by the processor's own count of time, a hundred and fifty thousand million of its ticks:
  -- most of a minute, where Linux gives a command two seconds. (In a trust domain one has been seen
  -- to go unanswered for ten.) A command still unanswered after a second or so has the card looked
  -- at: one whose count of commands done has gone back, or that says it wants to be started over,
  -- will answer nothing more, and is not waited for. What was seen is the second part of what comes
  -- back.
  let began ← Hw.ticks
  let mut done ← reg (registers + 24)
  let mut looked : UInt64 := 0
  let mut how := ""
  while done != count + 1 && (← Hw.ticks) - began < 150000000000 do
    for _ in [0:2000] do Hw.pause
    done ← reg (registers + 24)
    if done != count + 1 && ((← Hw.ticks) - began) / 2500000000 > looked then
      looked := looked + 1
      let status ← reg registers
      if done < count || status &&& (2 : UInt32) != 0 then
        return (0, s!"; command {count} unanswered, the card's count of them at {done} and its status {status}: it has started over")
  if done != count + 1 then return (0, s!"; command {count} never answered")
  if looked != 0 then how := s!"; command {count} answered late ({looked})"
  return (rd32 (← Hw.load (slot + 4) 4) 0, how)

/-- The card left alone for so many thousand million ticks (four hundred to the second, about), its count
of commands done looked at meanwhile: nothing when it stayed at `count`, and otherwise how many
million ticks in it was found changed, and to what. -/
def quiet (registers : UInt64) (count : UInt32) (ticks : UInt64) : BaseIO (Option (UInt64 × UInt32)) := do
  let began ← Hw.ticks
  let mut now := began
  while now - began < ticks do
    for _ in [0:2000] do Hw.pause
    let done ← reg (registers + 24)
    now ← Hw.ticks
    if done != count then return some ((now - began) / 1000000, done)
  return none

/-- `bytes` of the memory shared with the card, from `at_`, made nothing. -/
def wipe (at_ : UInt64) (bytes : USize) : BaseIO Unit := do
  let mut done : USize := 0
  let nothing := zeros 65536
  while done < bytes do
    let step := if bytes - done < 65536 then bytes - done else 65536
    Hw.storeFrom (at_ + done.toUInt64) nothing 0 step
    done := done + step

/-- The addresses of `pages` pages from `first` on, eight bytes each, written at `at_`: what the card is
given to be told of them. -/
def listAt (at_ first : UInt64) (pages : USize) : BaseIO Unit :=
  Hw.store at_ ((List.range pages.toNat).foldl (fun out i => wr64 out (i.toUSize * 8) (first + i.toUInt64 * 4096)) (zeros (pages.toNat * 8)))

/-- The card found and taken from the firmware, with the memory that does not depend on what it says of
itself; or why not. -/
def claim : BaseIO (Except String Ground) := do
  let mut found : Option USize := none
  for i in [0:(← Hw.devices).toNat] do
    if (← Hw.config i.toUSize 0 4) == 0x00421ae0 then found := some i.toUSize
  let some index := found | return .error "no card 1ae0:0042"
  let revision ← Hw.config index 8 1
  if !(← Hw.claim index) then return .error "the card could not be claimed from the firmware"
  let windows ← Hw.windows
  if windows.size < 3 then return .error "the card has fewer than three windows"
  if windows[0]!.size < 44 || windows[2]!.size < 8 then return .error "the card's windows are too small"
  let fixed ← Hw.alloc 12288
  if fixed == 0 then return .error "no shared memory"
  return .ok { registers := windows[0]!.base, doorbells := windows[2]!.base, bellRoom := windows[2]!.size, revision, fixed }

/-- The card reset and made ready from nothing, in the memory of `ground`; or why not. With either, the
ground as it now is (the first time through takes the rest of its memory); and with the card, in
words, what it said of itself, for whoever is finding out why one does not work. -/
def bring (ground : Ground) : BaseIO (Ground × Except String (Card × Rings × String)) := do
  let mut ground := ground
  let registers := ground.registers
  let doorbells := ground.doorbells
  let bellRoom := ground.bellRoom
  let revision := ground.revision
  -- Reset, and wait for it.
  if revision == 0 then setReg (registers + 16) 0 else setReg (registers + 4) 2
  let mut tries := 0
  let mut still := true
  while still && tries < 100000 do
    if revision == 0 then
      let left ← reg (registers + 16)
      still := left != 0
    else
      let status ← reg registers
      still := status &&& (0x10 : UInt32) == 0
    tries := tries + 1
  if still then return (ground, .error ("the card did not reset"))
  -- Who is driving it, a byte at a time, as it is used to being told.
  for byte in "GVE-1.0.0\n".toUTF8 do Hw.write (registers + 31) 1 byte.toUInt32
  -- The page of commands.
  let queue := ground.fixed
  wipe queue 12288
  if revision == 0 then setReg (registers + 16) (queue >>> 12).toUInt32
  else
    Hw.write (registers + 40) 2 (swap16 4096).toUInt32
    setReg (registers + 32) (queue >>> 32).toUInt32
    setReg (registers + 36) queue.toUInt32
    setReg (registers + 4) 1
  let mut put : UInt32 := 0
  -- What was seen of commands that were slow to be answered.
  let mut slow := ""
  -- What this driver is: one that knows the older way with pages told beforehand, and the newer with
  -- addresses as they are.
  let info := ground.fixed + 4096
  Hw.store info (wr64 (wr8 (wr8 (zeros 304) 0 1) 1 1) 16 9)
  let (said, how) ← command registers queue put (wr64 (wr64 (commandOf 0xf) 8 304) 16 info)
  slow := slow ++ how
  put := put + 1
  if said != 1 && said != 0xfffffffe then return (ground, .error (s!"the card would not have this driver ({said}{slow})"))
  -- What the card is.
  let about := ground.fixed + 8192
  let (said, how) ← command registers queue put (wr32 (wr32 (wr64 (commandOf 1) 8 about) 16 1) 20 4096)
  slow := slow ++ how
  put := put + 1
  if said != 1 then return (ground, .error (s!"the card would not describe itself ({said}{slow})"))
  let d ← Hw.load about 4096
  let most := (rd32 d 0).toUInt64 <<< 32 ||| (rd32 d 4).toUInt64
  let txSize := (rd16 d 10).toUSize
  let rxSize := (rd16 d 12).toUSize
  let mtu := rd16 d 16
  let counters := (rd16 d 18).toUSize
  let txCount := (rd16 d 20).toUSize
  let macHigh := rd16 d 24
  let macLow := rd32 d 26
  let power (n : USize) : Bool := n != 0 && n &&& (n - 1) == 0
  if !power txSize || !power rxSize || txSize < 64 || rxSize < 64 || txSize > 4096 || rxSize > 4096 then
    return (ground, .error (s!"queues of {txSize} and {rxSize} are not ones this driver takes"))
  -- Which way of working: the newer when the card lists it (option 4, asking nothing this driver has
  -- not), since the cards that list it move nothing the older way though they take its commands.
  let options := (rd16 d 30).toNat
  let mut newer := false
  let mut option : USize := 40
  for _ in [0:min options 16] do
    let size := (rd16 d (option + 2)).toUSize
    if rd16 d option == 4 && size ≥ 8 && rd32 d (option + 4) == 0 then newer := true
    option := option + 8 + size
  if counters == 0 || counters > 16384 then return (ground, .error (s!"{counters} counts are not what this driver takes"))
  if !newer && (txCount == 0 || txCount > 4096) then return (ground, .error (s!"{txCount} pages for sending are not what this driver takes"))
  if !newer && (txCount + rxSize).toUInt64 > most then return (ground, .error (s!"the card takes {most} pages and {txCount + rxSize} are needed"))
  let txSlots := if newer then (if txSize < 512 then txSize / 2 else 256) else if txCount * 2 < txSize then txCount * 2 else txSize
  if txSlots < 16 then return (ground, .error (s!"{txCount} pages for sending are too few"))
  -- Its counts, and its interrupt doorbells' numbers: two, which it wants and this never uses.
  -- The rest of the memory: so many bytes for each thing, each from a page of its own, in one run that
  -- is taken once and laid out the same way whenever the card is started over.
  let sizes : Array USize :=
    if newer then #[counters * 4, 4096, txSize * 16, txSize * 8, txSlots * 2048, rxSize * 32, rxSize * 32, rxSize * 2048, 4096]
    else #[counters * 4, 4096, txCount * 4096, rxSize * 4096, txCount * 8, rxSize * 8, txSize * 16, rxSize * 64, rxSize * 8, 4096]
  let pages (n : USize) : USize := (n + 4095) / 4096 * 4096
  let total := sizes.foldl (fun sum n => sum + pages n) 0
  let shape := sizes.foldl (fun mix n => mix * 1000003 + n.toUInt64) (if newer then 2 else 1)
  if ground.rest == 0 then
    let rest ← Hw.alloc total
    if rest == 0 then return (ground, .error (s!"no shared memory for {total} bytes"))
    ground := { ground with rest, shape }
  else if ground.shape != shape then
    return (ground, .error ("the card describes itself otherwise than when its memory was taken"))
  wipe ground.rest total
  let place (i : Nat) : UInt64 := ground.rest + ((sizes.extract 0 i).foldl (fun sum n => sum + pages n) 0).toUInt64
  let counts := place 0
  let bells := place 1
  let body := wr32 (wr32 (wr32 (wr64 (wr64 (commandOf 2) 8 counts) 16 bells) 24 counters.toUInt32) 28 2) 32 64
  let (said, how) ← command registers queue put (wr8 body 40 (if newer then 3 else 2))
  slow := slow ++ how
  put := put + 1
  if said != 1 then return (ground, .error (s!"the card would not take its counts and doorbells ({said}{slow})"))
  -- Left alone a moment and watched, before anything is built on it: a card that is going to start
  -- over by itself (below) has mostly done so by now.
  if let some (at_, to) ← quiet registers put 1000000000 then
    return (ground, .error (s!"left alone, the card's count of commands done went from {put} to {to} within {at_} million ticks"))
  let numbers ← Hw.load bells 128
  let mut notes := s!"the {if newer then "newer" else "older"} way; counts {counters}, pages for sending {txCount}, pages in all {most}, interrupt doorbells {rd32 numbers 0} and {rd32 numbers 64}"
  -- What ways of working the card says it has: each option's number, length, what it requires and its first word.
  let mut where_ : USize := 40
  notes := notes ++ s!"; {options} options:"
  for _ in [0:min options 16] do
    let size := (rd16 d (where_ + 2)).toUSize
    notes := notes ++ s!" [{rd16 d where_} length {size} requires {rd32 d (where_ + 4)} says {rd32 d (where_ + 8)}]"
    where_ := where_ + 8 + size
  if newer then
    -- The newer way. Nothing is told of beforehand: every descriptor carries an address. (Nor is the
    -- card told its packet size, as in the older way: in a trust domain it answered that by starting
    -- over, three times of three, and it has the size already.) For sending,
    -- descriptors and a ring the card writes what it has done into, and places of 2,048 bytes of this
    -- driver's own to copy frames to. For receiving, a ring of places offered and a ring the card
    -- writes what has come into, and a buffer of 2,048 bytes a place.
    let txRing := place 2
    let txDone := place 3
    let txPages := place 4
    let rxDesc := place 5
    let rxOffer := place 6
    let rxPages := place 7
    let about := place 8
    -- Place `i` is offered with buffer `i`, least significant byte first as everything of this way is.
    Hw.store rxOffer ((List.range rxSize.toNat).foldl (fun out i =>
      st64 (wr8 (wr8 out (i.toUSize * 32) i.toUInt8) (i.toUSize * 32 + 1) (i >>> 8).toUInt8) (i.toUSize * 32 + 8) (rxPages + i.toUInt64 * 2048))
      (zeros (rxSize.toNat * 32)))
    let body := wr64 (wr32 (wr32 (wr64 (wr64 (wr32 (commandOf 5) 8 0) 16 about) 24 txRing) 32 0xffffffff) 36 0) 40 txDone
    let (said, how) ← command registers queue put (wr16 (wr16 body 48 txSize.toUInt16) 50 txSize.toUInt16)
    slow := slow ++ how
    put := put + 1
    if said != 1 then return (ground, .error (s!"the card would not make the queue for sending ({said}{slow}); {notes}"))
    let body := wr64 (wr64 (wr64 (wr32 (wr32 (wr32 (commandOf 6) 8 0) 12 0) 20 1) 24 (about + 64)) 32 rxDesc) 40 rxOffer
    let body := wr16 (wr16 (wr16 (wr32 body 48 0xffffffff) 52 rxSize.toUInt16) 54 2048) 56 rxSize.toUInt16
    let (said, how) ← command registers queue put body
    slow := slow ++ how
    if said != 1 then return (ground, .error (s!"the card would not make the queue for receiving ({said}{slow}); {notes}"))
    let made ← Hw.load about 128
    let txBell : UInt64 := (rd32 made 0).toUInt64
    let rxBell : UInt64 := (rd32 made 64).toUInt64
    if txBell * (4 : UInt64) + (4 : UInt64) > bellRoom || rxBell * (4 : UInt64) + (4 : UInt64) > bellRoom then
      return (ground, .error (s!"the card named doorbells {txBell} and {rxBell}, which are not there; {notes}"))
    notes := notes ++ s!"; queue doorbells {txBell} and {rxBell}"
    -- No interrupt is wanted, said the way a driver that only looks says it; and every place for
    -- receiving but one is offered.
    for block in [0:2] do
      let bell : UInt64 := (rd32 numbers (block.toUSize * 64)).toUInt64
      if bell * (4 : UInt64) + (4 : UInt64) ≤ bellRoom then Hw.writeDirect (doorbells + bell * (4 : UInt64)) 0x40000018
    Hw.writeDirect (doorbells + rxBell * (4 : UInt64)) (rxSize.toUInt32 - 1)
    let card : Card :=
      { ground, registers, doorbells, macHigh, macLow, mtu, txRing, txPages, txSize, txSlots,
        txBell := doorbells + txBell * (4 : UInt64), txCount := 0,
        rxDesc, rxPages, rxSize, rxBell := doorbells + rxBell * (4 : UInt64), newer := true, txDone, rxOffer,
        asked := put + 1 }
    return (ground, .ok (card, { filled := rxSize.toUInt32 - 1 }, notes ++ slow))
  -- The pages frames go through, and the card told of them.
  let txPages := place 2
  let rxPages := place 3
  let txList := place 4
  let rxList := place 5
  listAt txList txPages txCount
  listAt rxList rxPages rxSize
  let rxId ← reg (registers + 8)
  let (said, how) ← command registers queue put (wr64 (wr64 (wr32 (wr32 (commandOf 3) 8 0) 12 txCount.toUInt32) 16 txList) 24 4096)
  slow := slow ++ how
  put := put + 1
  if said != 1 then return (ground, .error (s!"the card would not take the pages for sending ({said}{slow}); {notes}"))
  let (said, how) ← command registers queue put (wr64 (wr64 (wr32 (wr32 (commandOf 3) 8 rxId) 12 rxSize.toUInt32) 16 rxList) 24 4096)
  slow := slow ++ how
  put := put + 1
  if said != 1 then return (ground, .error (s!"the card would not take the pages for receiving ({said}{slow})"))
  -- How long a packet may be, which the card is told before it will have queues made.
  let (said, how) ← command registers queue put (wr64 (wr32 (commandOf 0xb) 8 1) 16 mtu.toUInt64)
  slow := slow ++ how
  put := put + 1
  if said != 1 then return (ground, .error (s!"the card would not be told its packet size ({said}{slow}); {notes}"))
  -- The queues.
  let txRing := place 6
  let rxDesc := place 7
  let rxData := place 8
  let about := place 9
  Hw.store rxData ((List.range rxSize.toNat).foldl (fun out i => wr64 out (i.toUSize * 8) (i.toUInt64 * 4096)) (zeros (rxSize.toNat * 8)))
  let body := wr64 (wr64 (wr32 (commandOf 5) 8 0) 16 about) 24 txRing
  let (said, how) ← command registers queue put (wr16 (wr32 (wr32 body 32 0) 36 0) 48 txSize.toUInt16)
  slow := slow ++ how
  put := put + 1
  if said != 1 then return (ground, .error (s!"the card would not make the queue for sending ({said}{slow})"))
  let body := wr64 (wr64 (wr64 (wr32 (wr32 (wr32 (commandOf 6) 8 0) 12 0) 20 1) 24 (about + 64)) 32 rxDesc) 40 rxData
  let (said, how) ← command registers queue put (wr16 (wr16 (wr32 body 48 rxId) 52 rxSize.toUInt16) 54 2048)
  slow := slow ++ how
  if said != 1 then return (ground, .error (s!"the card would not make the queue for receiving ({said}{slow})"))
  let made ← Hw.load about 128
  let txBell : UInt64 := (rd32 made 0).toUInt64
  let txCounter : UInt64 := (rd32 made 4).toUInt64
  let rxBell : UInt64 := (rd32 made 64).toUInt64
  if txBell * (4 : UInt64) + (4 : UInt64) > bellRoom || rxBell * (4 : UInt64) + (4 : UInt64) > bellRoom || txCounter ≥ counters.toUInt64 then
    return (ground, .error (s!"the card named doorbells {txBell} and {rxBell} and count {txCounter}, which are not there"))
  notes := notes ++ s!"; queue doorbells {txBell} and {rxBell}, count {txCounter}, and the receiving queue's count {rd32 made 68}"
  -- The two interrupt doorbells told that no interrupt is wanted, now that the queues are there.
  for block in [0:2] do
    let bell : UInt64 := (rd32 numbers (block.toUSize * 64)).toUInt64
    if bell * (4 : UInt64) + (4 : UInt64) ≤ bellRoom then Hw.writeDirect (doorbells + bell * (4 : UInt64)) (swap32 0x40000000)
  -- Every place for receiving but one is the card's from the start: told that all are, it takes it that
  -- none is, the count going round to where it began.
  Hw.writeDirect (doorbells + rxBell * (4 : UInt64)) (swap32 (rxSize.toUInt32 - 1))
  let card : Card :=
    { ground, registers, doorbells, macHigh, macLow, mtu, txRing, txPages, txSize, txSlots,
      txBell := doorbells + txBell * (4 : UInt64), txCount := counts + txCounter * (4 : UInt64),
      rxDesc, rxPages, rxSize, rxBell := doorbells + rxBell * (4 : UInt64), asked := put + 1 }
  return (ground, .ok (card, { filled := rxSize.toUInt32 - 1 }, notes ++ slow))

/-- The card brought up, and brought up again for as long as it does not stay up, for most of a minute.

**A card can start over by itself.** Seen on Compute Engine's trust domains on more than half the
starts, in the first seconds of a machine's life: with no command pending, a tenth of a second after
it had been given its counts and doorbells, its count of commands done was back at nothing, and
whatever was asked of it next went unanswered; a second later its status asked for a reset. Once it
did so twice running and came up the third time, once five times in five seconds. An operating system
gets to its card later than this does, and its driver allows for the same. So: a watched pause before
the queues are made, every command given up on as soon as the count has gone back, and the whole
bring-up tried again. -/
def bringUp (ground : Ground) : BaseIO (Except String (Card × Rings × String)) := do
  let mut ground := ground
  let mut tries := 0
  let mut first := ""
  let mut last := ""
  let began ← Hw.ticks
  while tries == 0 || (← Hw.ticks) - began < 150000000000 do
    let (g, got) ← bring ground
    ground := g
    match got with
    | .ok (card, rings, notes) =>
      return .ok (card, rings, if tries == 0 then notes else s!"{notes}; at try {tries + 1}, the first having ended: {first}")
    | .error why =>
      if tries == 0 then first := why
      last := why
      tries := tries + 1
  return .error s!"{tries} tries; the first ended: {first}; the last: {last}"

/-- The card found, taken from the firmware and made ready, or why not; and with the card, in words, what
it said of itself, for whoever is finding out why one does not work. -/
def start : BaseIO (Except String (Card × Rings × String)) := do
  match ← claim with
  | .error why => return .error why
  | .ok ground => bringUp ground

/-- Whether the card has started over or says it wants to be (its status, bit 1; or its count of
commands done no longer what it was given): asked of it now and then by whoever drives it. -/
def wantsReset (card : @& Card) : BaseIO Bool := do
  if (← reg card.registers) &&& (2 : UInt32) != 0 then return true
  return (← reg (card.registers + 24)) != card.asked

/-- The card started over in the memory it had. Whatever was on its way either way is lost, as on any
network; the rings begin again. -/
def restart (card : @& Card) : BaseIO (Except String (Card × Rings × String)) := bringUp card.ground

/-- The frames of up to `left` new descriptors copied into `batch` from `at_`, each with its length in
two bytes before it. What comes back, in one number: how many descriptors were taken (low 16 bits), the
number the next must carry (the 8 above), and how many were dropped (the 16 above those). -/
partial def takeEach (card : @& Card) (mask left : USize) (taken : UInt32) (expected : UInt16) (count dropped at_ : USize)
    (batch : ByteArray) : BaseIO (ByteArray × USize × USize) :=
  if left == 0 then pure (batch, at_, count ||| (expected.toUSize <<< 16) ||| (dropped <<< 24)) else do
  let slot := taken.toUSize &&& mask
  let here := card.rxDesc + (slot * 64).toUInt64
  let flags := swap16 (← Hw.load16 (here + 62))
  if flags &&& 7 != expected then pure (batch, at_, count ||| (expected.toUSize <<< 16) ||| (dropped <<< 24)) else do
  let said := (swap16 (← Hw.load16 (here + 60))).toUSize
  let next : UInt16 := if expected ≥ 7 then 1 else expected + 1
  -- One in error, one that goes on in another, one too short or too long to be a frame: let go.
  if flags &&& 0x2800 != 0 || said < 16 || said > 2048 || at_ + said > batch.usize then
    takeEach card mask (left - 1) (taken + 1) next (count + 1) (dropped + 1) at_ batch
  else
    let length := said - 2
    let batch ← Hw.loadInto (card.rxPages + (slot * 4096 + 2).toUInt64) (wr16 batch at_ length.toUInt16) (at_ + 2) length
    takeEach card mask (left - 1) (taken + 1) next (count + 1) dropped (at_ + 2 + length) batch

/-! The newer way of working (DQO, with addresses as they are). Everything in its rings is least
significant byte first. A ring the card writes has a bit in each entry that says which turn of the ring
the entry belongs to: 1 the first time round, the other the next, and so on; an entry is new when its
bit is the one expected. A ring this driver writes is told to the card as the place after the last
entry written, not as a count. -/

/-- What has come, the newer way: up to `left` entries of the ring the card writes, each a place's number
and a length; the frame copied into `batch`, and the place offered again at once. -/
partial def takeNewer (card : @& Card) (rings : Rings) (mask left at_ : USize) (turn : UInt16) (tail count dropped where_ : USize)
    (skipping : Bool) (batch : ByteArray) : BaseIO (Rings × ByteArray × USize) := do
  let here := card.rxDesc + (at_ * 32).toUInt64
  let said ← if left == 0 then pure 0 else Hw.load16 (here + 4)
  if left == 0 || (said >>> (14 : UInt16)) &&& (1 : UInt16) != turn then
    if count != 0 then Hw.writeDirect card.rxBell tail.toUInt32
    return ({ rings with taken := at_.toUInt32, expected := turn, filled := tail.toUInt32, dropped := rings.dropped + dropped.toUInt64,
                         frames := rings.frames + (count - dropped).toUInt64, calls := rings.calls + (if count != 0 then 1 else 0) },
            batch, where_)
  else
    let first ← Hw.load16 here
    let ends := (← Hw.load16 (here + 8)) &&& (2 : UInt16) != 0
    let place := (← Hw.load16 (here + 12)).toUSize
    let length := (said &&& (0x3fff : UInt16)).toUSize
    let next := (at_ + 1) &&& mask
    let turn : UInt16 := if next == 0 then turn ^^^ (1 : UInt16) else turn
    if place ≥ card.rxSize then takeNewer card rings mask (left - 1) next turn tail (count + 1) (dropped + 1) where_ (!ends) batch
    else
      -- The place is offered again with the same buffer, at the next entry of the ring of offers.
      let offer := card.rxOffer + (tail * 32).toUInt64
      Hw.store16 offer place.toUInt16
      let buffer := card.rxPages + (place * 2048).toUInt64
      Hw.store32 (offer + 8) buffer.toUInt32
      Hw.store32 (offer + 12) (buffer >>> 32).toUInt32
      let tail := (tail + 1) &&& mask
      -- In error, part of a frame in more than one buffer, too short or too long: let go.
      if first &&& (0x400 : UInt16) != 0 || skipping || !ends || length < 14 || length > 2048 || where_ + 2 + length > batch.usize then
        takeNewer card rings mask (left - 1) next turn tail (count + 1) (dropped + 1) where_ (!ends) batch
      else
        let batch ← Hw.loadInto buffer (wr16 batch where_ length.toUInt16) (where_ + 2) length
        takeNewer card rings mask (left - 1) next turn tail (count + 1) dropped (where_ + 2 + length) false batch

/-- What the card has done of the sending, the newer way, read from the ring it writes: a place's frame
gone (its byte in `scratch` cleared), or how far it has read the descriptors. What comes back, in one
number: how far it has read (low 16 bits), where reading the ring has got to (the next 16), and which
turn (the bit above). -/
partial def doneEach (card : @& Card) (mask left at_ : USize) (turn : UInt16) (head : USize) (scratch : ByteArray) :
    BaseIO (ByteArray × USize) := do
  let here := card.txDone + (at_ * 8).toUInt64
  let first ← if left == 0 then pure 0 else Hw.load16 here
  if left == 0 || first >>> (15 : UInt16) != turn then return (scratch, head ||| (at_ <<< 16) ||| (turn.toUSize <<< 32))
  else
    let second ← Hw.load16 (here + 2)
    let kind := (first >>> (11 : UInt16)) &&& (7 : UInt16)
    let scratch := if (kind == 2 || kind == 3) && second.toUSize < card.txSlots then wr8 scratch (128 + second.toUSize) 0 else scratch
    let head := if kind == 4 then second.toUSize &&& mask else head
    let next := (at_ + 1) &&& mask
    doneEach card mask (left - 1) next (if next == 0 then turn ^^^ (1 : UInt16) else turn) head scratch

/-- The first place from `at_` on with no frame of the card's in it; the number of places when all have. -/
partial def freePlace (scratch : @& ByteArray) (places at_ left : USize) : USize :=
  if left == 0 then places
  else if rd8 scratch (128 + at_) == 0 then at_
  else freePlace scratch places (if at_ + 1 == places then 0 else at_ + 1) (left - 1)

/-- The frames of `tx` from `o` to `stop` given to the card the newer way: each copied to a free place and
described by one descriptor that names the place, which the card names back when the frame has gone. -/
partial def giveNewer (card : @& Card) (rings : Rings) (tx : @& ByteArray) (stop : USize) (patience tries : UInt64) (o : USize)
    (tail head doneAt : USize) (turn : UInt16) (cursor : USize) (since : UInt32) (scratch : ByteArray)
    (dropped frames waits : UInt64) : BaseIO (Rings × ByteArray) := do
  let mask := card.txSize - 1
  let length := if o + 2 > stop then 0 else (rd16 tx o).toUSize
  if length < 14 || length > 1514 || o + 2 + length > stop then
    -- The end: the card told where the descriptors now end, and what it has done read for next time.
    if tail.toUInt32 != rings.posted then Hw.writeDirect card.txBell tail.toUInt32
    let (scratch, packed) ← doneEach card mask card.txSize doneAt turn head scratch
    return ({ rings with posted := tail.toUInt32, finished := (packed &&& 0xffff).toUInt32, serial := cursor.toUInt32,
                         doneAt := ((packed >>> 16) &&& 0xffff).toUInt32, doneTurn := ((packed >>> 32) &&& 1).toUInt16, since,
                         dropped, frames, waits, calls := rings.calls + (if tail.toUInt32 != rings.posted then 1 else 0) }, scratch)
  else
    let place := freePlace scratch card.txSlots cursor card.txSlots
    if ((tail - head) &&& mask) + 5 > card.txSize || place == card.txSlots then
      -- No descriptor to spare or no place free: what is queued is handed over, and the card's word read.
      if tail.toUInt32 != rings.posted then Hw.writeDirect card.txBell tail.toUInt32
      let rings := { rings with posted := tail.toUInt32 }
      let (scratch, packed) ← doneEach card mask card.txSize doneAt turn head scratch
      let head := packed &&& 0xffff
      let doneAt := (packed >>> 16) &&& 0xffff
      let turn := ((packed >>> 32) &&& 1).toUInt16
      if tries ≥ patience then giveNewer card rings tx stop patience 0 (o + 2 + length) tail head doneAt turn cursor since scratch (dropped + 1) frames waits
      else
        Hw.pause
        giveNewer card rings tx stop patience (tries + 1) o tail head doneAt turn cursor since scratch dropped frames (waits + 1)
    else
      let buffer := card.txPages + (place * 2048).toUInt64
      Hw.storeFrom buffer tx (o + 2) length
      let whole := if length < 60 then 60 else length
      if length < 60 then Hw.storeFrom (buffer + length.toUInt64) scratch 64 (60 - length)
      -- The card is asked to say how far it has read every so often, or it never does.
      let asks := since + 1 ≥ 32
      let scratch := st64 scratch 0 buffer
      let scratch := wr8 (wr8 (wr8 (wr8 scratch 8 (if asks then 0xac else 0x2c)) 9 0) 10 0) 11 0
      let scratch := wr8 (wr8 (wr8 (wr8 scratch 12 place.toUInt8) 13 (place >>> 8).toUInt8) 14 whole.toUInt8) 15 (whole >>> 8).toUInt8
      Hw.storeFrom (card.txRing + (tail * 16).toUInt64) scratch 0 16
      let scratch := wr8 scratch (128 + place) 1
      giveNewer card rings tx stop patience 0 (o + 2 + length) ((tail + 1) &&& mask) head doneAt turn
        (if place + 1 == card.txSlots then 0 else place + 1) (if asks then 0 else since + 1) scratch dropped (frames + 1) waits

/-- Everything the card has received since the last call, copied into `batch` as the stack takes it, and
the places handed back. What comes back: the rings, `scratch`, `batch`, and how many bytes of `batch`
are frames. -/
def receive (card : @& Card) (rings : Rings) (scratch batch : ByteArray) : BaseIO (Rings × ByteArray × ByteArray × USize) := do
  if card.newer then
    let (rings, batch, length) ← takeNewer card rings (card.rxSize - 1) card.rxSize rings.taken.toUSize rings.expected rings.filled.toUSize 0 0 0 false batch
    return (rings, scratch, batch, length)
  let (batch, length, packed) ← takeEach card (card.rxSize - 1) card.rxSize rings.taken rings.expected 0 0 0 batch
  let count := packed &&& 0xffff
  if count == 0 then return (rings, scratch, batch, 0)
  let dropped := packed >>> 24
  let filled := rings.filled + count.toUInt32
  Hw.writeDirect card.rxBell (swap32 filled)
  return ({ rings with taken := rings.taken + count.toUInt32, expected := ((packed >>> 16) &&& 0xff).toUInt16, filled,
                       dropped := rings.dropped + dropped.toUInt64, frames := rings.frames + (count - dropped).toUInt64,
                       calls := rings.calls + 1 }, scratch, batch, length)

/-- How far the card has got with what it was given to send, waited for up to `patience` times while there
is no room for two descriptors more. The count done, and above its 32 bits how many times it was asked. -/
partial def await (card : @& Card) (posted finished : UInt32) (tries patience : UInt64) : BaseIO UInt64 :=
  if (posted - finished).toUSize + 2 ≤ card.txSlots || tries ≥ patience then pure ((tries <<< 32) ||| finished.toUInt64) else do
  let done := swap32 (← Hw.load32 card.txCount)
  -- Its word: believed only if it is between what was known and what was given.
  let finished := if done - finished ≤ posted - finished then done else finished
  if (posted - finished).toUSize + 2 > card.txSlots then Hw.pause
  await card posted finished (tries + 1) patience

/-- The end of a sending: the card told how many descriptors there now are, and the rings as they are. -/
def closeOut (card : @& Card) (rings : Rings) (scratch : ByteArray) (posted finished serial : UInt32) (dropped frames waits : UInt64) :
    BaseIO (Rings × ByteArray) := do
  if posted != rings.posted then Hw.writeDirect card.txBell (swap32 posted)
  let done := swap32 (← Hw.load32 card.txCount)
  let finished := if done - finished ≤ posted - finished then done else finished
  return ({ rings with posted, finished, serial, dropped, frames, waits, calls := rings.calls + (if posted != rings.posted then 1 else 0) }, scratch)

/-- The frames of `tx` from `o` to `stop` copied into the sending pages and described to the card. No
more descriptors are with the card at once than there are places, so that a place is never written while
the frame that was in it is still the card's. -/
partial def giveEach (card : @& Card) (rings : Rings) (tx : @& ByteArray) (stop : USize) (patience : UInt64) (o : USize)
    (posted finished serial : UInt32) (scratch : ByteArray) (dropped frames waits : UInt64) : BaseIO (Rings × ByteArray) :=
  if o + 2 > stop then closeOut card rings scratch posted finished serial dropped frames waits else
  let length := (rd16 tx o).toUSize
  if length < 14 || length > 1514 || o + 2 + length > stop then closeOut card rings scratch posted finished serial dropped frames waits
  else if (posted - finished).toUSize + 2 > card.txSlots then do
    -- No room: what is queued is handed over, and the card waited for.
    if posted != rings.posted then Hw.writeDirect card.txBell (swap32 posted)
    let got ← await card posted finished 0 patience
    let finished := got.toUInt32
    let waits := waits + (got >>> 32)
    let rings := { rings with posted }
    if (posted - finished).toUSize + 2 > card.txSlots then giveEach card rings tx stop patience (o + 2 + length) posted finished serial scratch (dropped + 1) frames waits
    else giveEach card rings tx stop patience o posted finished serial scratch dropped frames waits
  else do
    let mask := card.txSize - 1
    let slot := posted.toUSize &&& mask
    let place := ((serial.toUSize % card.txSlots) * 2048).toUInt64
    Hw.storeFrom (card.txPages + place) tx (o + 2) length
    -- A frame shorter than Ethernet's least is filled out with nothing.
    let whole := if length < 60 then 60 else length
    if length < 60 then Hw.storeFrom (card.txPages + place + length.toUInt64) scratch 64 (60 - length)
    let first := if whole < firstMost then whole else firstMost
    let two := whole > firstMost
    let scratch := wr8 (wr8 (wr8 (wr8 scratch 0 0) 1 0) 2 0) 3 (if two then 2 else 1)
    let scratch := wr64 (wr16 (wr16 scratch 4 whole.toUInt16) 6 first.toUInt16) 8 place
    Hw.storeFrom (card.txRing + (slot * 16).toUInt64) scratch 0 16
    if two then
      let scratch := wr16 (wr16 (wr16 (wr8 (wr8 scratch 16 0x20) 17 0) 18 0) 20 0) 22 (whole - firstMost).toUInt16
      let scratch := wr64 scratch 24 (place + firstMost.toUInt64)
      Hw.storeFrom (card.txRing + (((posted + 1).toUSize &&& mask) * 16).toUInt64) scratch 16 16
      giveEach card rings tx stop patience (o + 2 + length) (posted + 2) finished (serial + 1) scratch dropped (frames + 1) waits
    else giveEach card rings tx stop patience (o + 2 + length) (posted + 1) finished (serial + 1) scratch dropped (frames + 1) waits

/-- Every frame the stack wrote to `tx` (from its ninth byte to where its first eight say) given to the
card, which is told once. With no room it is waited for, `patience` times; what cannot be sent then is
dropped and counted. -/
def transmit (card : @& Card) (rings : Rings) (scratch : ByteArray) (tx : @& ByteArray) (patience : UInt64 := 400000) :
    BaseIO (Rings × ByteArray) := do
  let stop := Flat.written tx
  if stop ≤ 8 then return (rings, scratch)
  if card.newer then
    return ← giveNewer card rings tx stop patience 0 8 rings.posted.toUSize rings.finished.toUSize rings.doneAt.toUSize rings.doneTurn
      rings.serial.toUSize rings.since scratch rings.dropped rings.frames rings.waits
  giveEach card rings tx stop patience 8 rings.posted rings.finished rings.serial scratch rings.dropped rings.frames rings.waits

end Kernel.Net.Gvnic
