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

**Where it works and where not** (2026-11-24). On an ordinary machine of Compute Engine (`n2-standard-2`)
it sends and receives, and the trial TCP served pages over it to the open Internet. On the machines that
can be trust domains (the C3 series) the card takes every command, offers this way of working among its
options, and then moves nothing: nothing sent is ever counted as done and nothing arrives. Those cards
also offer the newer way (DQO), which is what Linux and DPDK choose there, and which this driver has not
got. So in a trust domain on Compute Engine there is no network yet.

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

Not done: more than one queue; frames longer than a buffer (they are dropped); checksums or segmenting
left to the card; noticing that the card wants to be reset; the newer way of working (DQO). -/

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

structure Card where
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
  deriving Inhabited

/-- An array to make descriptors in: its first 32 bytes are written, the rest stay nothing and are what
a short frame is filled out with. -/
def scratchFor (_ : Card) : ByteArray := zeros 128

/-- A command to the card: its number, then nothing, to be filled in. -/
def commandOf (opcode : UInt32) : ByteArray := wr32 (zeros 64) 0 opcode

/-- One command put to the card and waited for. `queue` is the page of commands and `count` how many
were put before this one. What comes back is what the card says of it: 1 is done, 0 that it never
answered. -/
def command (registers queue : UInt64) (count : UInt32) (body : ByteArray) : BaseIO UInt32 := do
  let slot := queue + (count &&& 63).toUInt64 * 64
  Hw.store slot (body.extract 0 64)
  setReg (registers + 20) (count + 1)
  -- Waited for by the processor's own count of time, some tens of thousands of millions of its ticks:
  -- ten seconds or so, where Linux gives a command two.
  let began ← Hw.ticks
  let mut done ← reg (registers + 24)
  while done != count + 1 && (← Hw.ticks) - began < 30000000000 do
    for _ in [0:2000] do Hw.pause
    done ← reg (registers + 24)
  if done != count + 1 then return 0
  return rd32 (← Hw.load (slot + 4) 4) 0

/-- Memory shared with the card, with nothing in it; 0 when there is no more. -/
def blank (bytes : USize) : BaseIO UInt64 := do
  let at_ ← Hw.alloc bytes
  if at_ != 0 then
    let mut done : USize := 0
    let nothing := zeros 65536
    while done < bytes do
      let step := if bytes - done < 65536 then bytes - done else 65536
      Hw.storeFrom (at_ + done.toUInt64) nothing 0 step
      done := done + step
  return at_

/-- The addresses of `pages` pages from `first` on, eight bytes each, in shared memory: what the card is
given to be told of them. -/
def listOf (first : UInt64) (pages : USize) : BaseIO UInt64 := do
  let at_ ← Hw.alloc (pages * 8)
  if at_ == 0 then return 0
  let list := (List.range pages.toNat).foldl (fun out i => wr64 out (i.toUSize * 8) (first + i.toUInt64 * 4096)) (zeros (pages.toNat * 8))
  Hw.store at_ list
  return at_

/-- The card found, taken from the firmware and made ready, or why not; and with the card, in words, what
it said of itself, for whoever is finding out why one does not work. -/
def start : BaseIO (Except String (Card × Rings × String)) := do
  let mut found : Option USize := none
  for i in [0:(← Hw.devices).toNat] do
    if (← Hw.config i.toUSize 0 4) == 0x00421ae0 then found := some i.toUSize
  let some index := found | return .error "no card 1ae0:0042"
  let revision ← Hw.config index 8 1
  if !(← Hw.claim index) then return .error "the card could not be claimed from the firmware"
  let windows ← Hw.windows
  if windows.size < 3 then return .error "the card has fewer than three windows"
  let registers := windows[0]!.base
  let doorbells := windows[2]!.base
  let bellRoom : UInt64 := windows[2]!.size
  if windows[0]!.size < 44 || windows[2]!.size < 8 then return .error "the card's windows are too small"
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
  if still then return .error "the card did not reset"
  -- Who is driving it, a byte at a time, as it is used to being told.
  for byte in "GVE-1.0.0\n".toUTF8 do Hw.write (registers + 31) 1 byte.toUInt32
  -- The page of commands.
  let queue ← blank 4096
  if queue == 0 then return .error "no shared memory"
  if revision == 0 then setReg (registers + 16) (queue >>> 12).toUInt32
  else
    Hw.write (registers + 40) 2 (swap16 4096).toUInt32
    setReg (registers + 32) (queue >>> 32).toUInt32
    setReg (registers + 36) queue.toUInt32
    setReg (registers + 4) 1
  let mut put : UInt32 := 0
  -- What this driver is: the plainest kind only.
  let info ← blank 4096
  if info == 0 then return .error "no shared memory"
  Hw.store info (wr64 (wr8 (wr8 (zeros 304) 0 1) 1 1) 16 1)
  let said ← command registers queue put (wr64 (wr64 (commandOf 0xf) 8 304) 16 info)
  put := put + 1
  if said != 1 && said != 0xfffffffe then return .error s!"the card would not have this driver ({said})"
  -- What the card is.
  let about ← blank 4096
  if about == 0 then return .error "no shared memory"
  let said ← command registers queue put (wr32 (wr32 (wr64 (commandOf 1) 8 about) 16 1) 20 4096)
  put := put + 1
  if said != 1 then return .error s!"the card would not describe itself ({said})"
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
  if !power txSize || !power rxSize || txSize < 16 || rxSize < 16 || txSize > 4096 || rxSize > 4096 then
    return .error s!"queues of {txSize} and {rxSize} are not ones this driver takes"
  if counters == 0 || counters > 16384 || txCount == 0 || txCount > 4096 then
    return .error s!"{counters} counts and {txCount} pages for sending are not what this driver takes"
  if (txCount + rxSize).toUInt64 > most then return .error s!"the card takes {most} pages and {txCount + rxSize} are needed"
  let txSlots := if txCount * 2 < txSize then txCount * 2 else txSize
  if txSlots < 16 then return .error s!"{txCount} pages for sending are too few"
  -- Its counts, and its interrupt doorbells' numbers: two, which it wants and this never uses.
  let counts ← blank (counters * 4)
  let bells ← blank 4096
  if counts == 0 || bells == 0 then return .error "no shared memory"
  let body := wr32 (wr32 (wr32 (wr64 (wr64 (commandOf 2) 8 counts) 16 bells) 24 counters.toUInt32) 28 2) 32 64
  let said ← command registers queue put (wr8 body 40 2)
  put := put + 1
  if said != 1 then return .error s!"the card would not take its counts and doorbells ({said})"
  let numbers ← Hw.load bells 128
  let mut notes := s!"counts {counters}, pages for sending {txCount}, pages in all {most}, interrupt doorbells {rd32 numbers 0} and {rd32 numbers 64}"
  -- What ways of working the card says it has: each option's number, length, what it requires and its first word.
  let options := (rd16 d 30).toNat
  let mut where_ : USize := 40
  notes := notes ++ s!"; {options} options:"
  for _ in [0:min options 16] do
    let size := (rd16 d (where_ + 2)).toUSize
    notes := notes ++ s!" [{rd16 d where_} length {size} requires {rd32 d (where_ + 4)} says {rd32 d (where_ + 8)}]"
    where_ := where_ + 8 + size
  -- The pages frames go through, and the card told of them.
  let txPages ← Hw.alloc (txCount * 4096)
  let rxPages ← Hw.alloc (rxSize * 4096)
  if txPages == 0 || rxPages == 0 then return .error s!"no shared memory for {txCount + rxSize} pages"
  let txList ← listOf txPages txCount
  let rxList ← listOf rxPages rxSize
  if txList == 0 || rxList == 0 then return .error "no shared memory"
  let rxId ← reg (registers + 8)
  let said ← command registers queue put (wr64 (wr64 (wr32 (wr32 (commandOf 3) 8 0) 12 txCount.toUInt32) 16 txList) 24 4096)
  put := put + 1
  if said != 1 then return .error s!"the card would not take the pages for sending ({said}); {notes}"
  let said ← command registers queue put (wr64 (wr64 (wr32 (wr32 (commandOf 3) 8 rxId) 12 rxSize.toUInt32) 16 rxList) 24 4096)
  put := put + 1
  if said != 1 then return .error s!"the card would not take the pages for receiving ({said})"
  -- How long a packet may be, which the card is told before it will have queues made.
  let said ← command registers queue put (wr64 (wr32 (commandOf 0xb) 8 1) 16 mtu.toUInt64)
  put := put + 1
  if said != 1 then return .error s!"the card would not be told its packet size ({said}); {notes}"
  -- The queues.
  let txRing ← blank (txSize * 16)
  let rxDesc ← blank (rxSize * 64)
  let rxData ← Hw.alloc (rxSize * 8)
  let about ← blank 4096
  if txRing == 0 || rxDesc == 0 || rxData == 0 || about == 0 then return .error "no shared memory"
  Hw.store rxData ((List.range rxSize.toNat).foldl (fun out i => wr64 out (i.toUSize * 8) (i.toUInt64 * 4096)) (zeros (rxSize.toNat * 8)))
  let body := wr64 (wr64 (wr32 (commandOf 5) 8 0) 16 about) 24 txRing
  let said ← command registers queue put (wr16 (wr32 (wr32 body 32 0) 36 0) 48 txSize.toUInt16)
  put := put + 1
  if said != 1 then return .error s!"the card would not make the queue for sending ({said})"
  let body := wr64 (wr64 (wr64 (wr32 (wr32 (wr32 (commandOf 6) 8 0) 12 0) 20 1) 24 (about + 64)) 32 rxDesc) 40 rxData
  let said ← command registers queue put (wr16 (wr16 (wr32 body 48 rxId) 52 rxSize.toUInt16) 54 2048)
  if said != 1 then return .error s!"the card would not make the queue for receiving ({said})"
  let made ← Hw.load about 128
  let txBell : UInt64 := (rd32 made 0).toUInt64
  let txCounter : UInt64 := (rd32 made 4).toUInt64
  let rxBell : UInt64 := (rd32 made 64).toUInt64
  if txBell * (4 : UInt64) + (4 : UInt64) > bellRoom || rxBell * (4 : UInt64) + (4 : UInt64) > bellRoom || txCounter ≥ counters.toUInt64 then
    return .error s!"the card named doorbells {txBell} and {rxBell} and count {txCounter}, which are not there"
  notes := notes ++ s!"; queue doorbells {txBell} and {rxBell}, count {txCounter}, and the receiving queue's count {rd32 made 68}"
  -- The two interrupt doorbells told that no interrupt is wanted, now that the queues are there.
  for block in [0:2] do
    let bell : UInt64 := (rd32 numbers (block.toUSize * 64)).toUInt64
    if bell * (4 : UInt64) + (4 : UInt64) ≤ bellRoom then setReg (doorbells + bell * (4 : UInt64)) 0x40000000
  -- Every place for receiving but one is the card's from the start: told that all are, it takes it that
  -- none is, the count going round to where it began.
  setReg (doorbells + rxBell * (4 : UInt64)) (rxSize.toUInt32 - 1)
  return .ok ({ registers, doorbells, macHigh, macLow, mtu, txRing, txPages, txSize, txSlots,
                txBell := doorbells + txBell * (4 : UInt64), txCount := counts + txCounter * (4 : UInt64),
                rxDesc, rxPages, rxSize, rxBell := doorbells + rxBell * (4 : UInt64) },
              { filled := rxSize.toUInt32 - 1 }, notes)

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

/-- Everything the card has received since the last call, copied into `batch` as the stack takes it, and
the places handed back. What comes back: the rings, `scratch`, `batch`, and how many bytes of `batch`
are frames. -/
def receive (card : @& Card) (rings : Rings) (scratch batch : ByteArray) : BaseIO (Rings × ByteArray × ByteArray × USize) := do
  let (batch, length, packed) ← takeEach card (card.rxSize - 1) card.rxSize rings.taken rings.expected 0 0 0 batch
  let count := packed &&& 0xffff
  if count == 0 then return (rings, scratch, batch, 0)
  let dropped := packed >>> 24
  let filled := rings.filled + count.toUInt32
  setReg card.rxBell filled
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
  if posted != rings.posted then setReg card.txBell posted
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
    if posted != rings.posted then setReg card.txBell posted
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
  giveEach card rings tx stop patience 8 rings.posted rings.finished rings.serial scratch rings.dropped rings.frames rings.waits

end Kernel.Net.Gvnic
