/-! A TCP for many short connections, as a trial of how fast one written in Lean can be. It is not the
system's TCP (`Kernel/Net/Tcp.lean`) and is in no image.

What is different from the system's, and why each thing is so:

* **Frames come and go in batches**, many to an array, each with its length in two bytes before it. A
  network card hands over dozens at a time, and a call a frame is what a fast stack cannot afford.
* **Nothing is allocated for a frame.** A frame is read where it lies; an answer is written into an array
  that was there before, at a place kept in that array's first eight bytes; a connection is 128 bytes in
  one flat table (what every frame needs in the first 64), found by a keyed hash of its addresses and changed in place. Lean changes an array in
  place when nothing else holds it, and everything here is written to keep it so.
* **A connection costs nothing until it is real.** The answer to a SYN is worked out from a keyed hash of
  the addresses and a clock (a SYN cookie), with the peer's largest segment in its two lowest bits, how
  the peer scales its window in the four above, and the clock in steps of 64 ms in the four above those, and
  nothing is kept; the table gets an entry only when the third packet of the handshake comes back with
  that number in it, and how long it took to come back is the connection's first round trip.
* **Time is a sweep.** Every entry carries the time by which something must have happened to it. `tick`
  looks at a part of the table each time it is called, so that the whole is looked at once every
  `sweepMs`, and acts on entries whose time has come: what was sent and not acknowledged is sent again,
  with the wait doubled, a connection that is open and has been asked nothing for too long is closed,
  and one that owes or is owed something and has said nothing for too long is reset and forgotten.
  How long is waited is worked out from how long acknowledgements have been taking (`measure`,
  `waitOf`), between `waitLeast` and `waitMost`.
  Timers are therefore late by up to `sweepMs`, and cost the same whether one connection is open or a
  million.
* **What can be tuned is in one place**, `Tuning`.

What it does: the handshake by cookie; data in, in order; an answer of any length out, cut to the
peer's largest segment and kept within the peer's window, scaled as the peer said, and a window of its
own: one segment more for every acknowledgement until a segment is first lost, half of that when one is
seen to be lost, one segment when a timer fires, and from then on a segment more a round trip once it
is back to half of where it was (Reno, as RFC 5681 has it, without the inflating); and when a segment
has been seen to be lost, every acknowledgement that moves without reaching what had been sent by then
shows the next one lost, which is sent again at once (RFC 6582), so that several lost out of one
window cost no timer; sending again on a timer, and at once when the same acknowledgement has come `repeats` times
(after a timer everything from the oldest unacknowledged byte is taken for lost and sent again as the
window reopens, so a run of lost segments costs one timer and not one each);
both orders of closing; a reset for a segment that belongs to nothing.

A window the peer has shut to nothing is tried with one byte, again and again at the pace of the timer,
for as long as the peer answers; one that stops answering is reset like any other.

What it does not do, and a TCP must or should: keep segments that come out of order (it asks again for
the next byte); any option but the largest segment and the
window's scale (so no timestamps or selective acknowledgement), and its own window is never scaled;
IPv6; IP options or fragments.

**The application** is a function and a list of answers. What a connection sends is always one whole
answer out of the list, an array of bytes that does not change, and then either the end of the stream
or, if the function said so (`sendOn`), nothing, the connection staying open for the next request: so a
connection holds a number and not a copy, a thousand connections sending the same megabyte hold it once,
and what must be sent again is read from where it always was. The function, `respond`, is shown each
run of bytes that arrives, where it lies in the frame, with a number of its own that the connection
keeps for it between runs; it says which answer to send, or that it wants more, and what its number is
now. Bytes are not kept for it: what it needs from an earlier run it must have put in its number. This
suits a server that answers requests from a store of ready answers, and nothing else. While an answer
is on its way on a connection that stays open, what the peer sends is not taken (it will send it again):
a peer that sends its next request before it has the answer to the last waits a timer for it.

Laid out:

    table   128 bytes of counters and marks, then 2^slotBits entries of 128 bytes
            eight bytes each: 0 live, 8 accepted, 16 closed, 24 SYNs, 32 dropped, 40 out of order,
            48 resets taken, 56 no room, 64 where the sweep has got to, 72 sent again, 80 timed out,
            88 resets sent, 96 sent again on repeated acknowledgements, 104 times an answer was held
            back for want of room to write frames, 112 SYNs not answered because too many
            connections were open, 120 round trips measured
    entry   0 state (0 free, 1 open, 2 answering and closing, 3 waiting out its end)
            1 flags (1: the peer has closed; 2: there is no answer, only the end; 4: a byte is being
              timed; 8: lost segments are being made good; 16: the connection stays open after
              the answer)
            2 times sent again without an acknowledgement   3 acknowledgements repeated
            4 the time by which something must happen
            8 the key: remote address, remote port, local port
            16 next to send   20 oldest unacknowledged   24 next expected   28 where the answer began
            32 the furthest ever sent   36 the peer's window   38 the peer's largest segment
            40 the peer's Ethernet address   46 when the byte being timed was sent (sixteen bits of
            the clock)   48 this end's window of its own
            52 the round trip as measured: sixteen bits of eight times its smoothed length, then
            sixteen of four times how far it strays, in milliseconds; nothing until one is measured
            56 which answer is being sent   60 the application's own number
            64 the byte being timed   68 where this end's window stops opening a segment an
            acknowledgement   72 how many places the peer's window is shifted
            76 how far had been sent when a segment was seen to be lost   the rest is not used
    out     eight bytes saying where the next frame goes, then frames -/

namespace Kernel.Net.Flat

structure Tuning where
  /-- The table has two to this many entries, and takes new connections until half are in use. -/
  slotBits : USize := 20
  localIp : UInt32 := 0x0a000002
  localPort : UInt16 := 80
  /-- This end's Ethernet address: its first two bytes and its last four. -/
  macHigh : UInt16 := 0x0200
  macLow : UInt32 := 0x00000002
  /-- The largest segment this end says it will take, and the largest it will send. -/
  mss : UInt16 := 1460
  /-- The window this end advertises. -/
  window : UInt16 := 65535
  /-- Whether checksums are checked coming in and made going out. A card that does both can be told to,
  and then this is false. -/
  checksums : Bool := true
  /-- How many segments may be on their way unacknowledged when a connection begins to answer, and the
  most that may ever be. One more is allowed for each acknowledgement that takes something off. -/
  firstWindow : UInt32 := 10
  mostWindow : UInt32 := 64
  /-- Milliseconds before what was sent and not acknowledged is sent again, while no round trip has been
  measured on the connection. Once one has, the wait is the smoothed round trip and four times how far
  it strays, and no less than `waitLeast`. Either is doubled each time it runs out, up to `waitMost`;
  after `tries` times the connection is reset. -/
  wait : UInt32 := 200
  waitLeast : UInt32 := 200
  waitMost : UInt32 := 3000
  /-- Whether round trips are measured. When not, the wait is always `wait`, doubled as it runs out. -/
  measures : Bool := true
  tries : UInt8 := 5
  /-- How many times the same acknowledgement must come, with something still unacknowledged, before
  the segment after it is taken for lost and sent again without waiting for the timer. 0 for never. -/
  repeats : UInt8 := 3
  /-- Milliseconds a connection may say nothing new before it is reset. -/
  idle : UInt32 := 10000
  /-- Milliseconds an entry is kept after both ends have closed, to answer a last segment sent again. -/
  linger : UInt32 := 0
  /-- Milliseconds in which the whole table is looked over for entries whose time has come. -/
  sweepMs : UInt32 := 256
  /-- With more connections open than this, a SYN is not answered: the connections there are are finished
  before more are begun. Without it, asked for more than the path can carry, this end goes on answering
  every SYN while what it has begun cannot finish, and gets less done the more it is asked. 0 for no
  such limit. -/
  busy : UInt64 := 0
  /-- Whether a segment that belongs to no connection is answered with a reset, as a TCP should, or with
  nothing, which costs less under a flood. -/
  resetStrays : Bool := true
  /-- The key of the hash: of the table's, so that nobody outside can aim connections at one place in it,
  and of the cookies', so that nobody can make up the third packet of a handshake. -/
  key0 : UInt64 := 0x0706050403020100
  key1 : UInt64 := 0x0f0e0d0c0b0a0908

theorem within {n : Nat} {off : USize} (k : Nat) (h : off.toNat + k < n) : (off + USize.ofNat k).toNat < n := by
  have h1 : (off + USize.ofNat k).toNat ≤ off.toNat + (USize.ofNat k).toNat := by
    rw [USize.toNat_add]; exact Nat.mod_le _ _
  have h2 : (USize.ofNat k).toNat ≤ k := by
    rw [USize.toNat_ofNat']; exact Nat.mod_le _ _
  omega

theorem size_uset (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) : (a.uset i v h).size = a.size := by
  cases a; simp [ByteArray.uset, ByteArray.size]

@[inline] def set1 {n : Nat} (a : {a : ByteArray // a.size = n}) (off : USize) (v : UInt8) (h : off.toNat < n) :
    {a : ByteArray // a.size = n} :=
  ⟨a.1.uset off v (by rw [a.2]; exact h), by rw [size_uset]; exact a.2⟩

/-! Reading. A place past the end reads as nothing. The first of several bytes is the most significant
(`rd`), as on the wire, or the least (`ld`), for what only this code reads. -/

@[inline] def rd8 (a : @& ByteArray) (i : USize) : UInt8 := if h : i.toNat < a.size then a.uget i h else 0

@[inline] def rd16 (a : @& ByteArray) (i : USize) : UInt16 :=
  if h : i.toNat + 1 < a.size then
    ((a.uget i (by omega)).toUInt16 <<< 8) ||| (a.uget (i + USize.ofNat 1) (within 1 h)).toUInt16
  else 0

@[inline] def rd32 (a : @& ByteArray) (i : USize) : UInt32 :=
  if h : i.toNat + 3 < a.size then
    ((a.uget i (by omega)).toUInt32 <<< 24) ||| ((a.uget (i + USize.ofNat 1) (within 1 (by omega))).toUInt32 <<< 16) |||
    ((a.uget (i + USize.ofNat 2) (within 2 (by omega))).toUInt32 <<< 8) ||| (a.uget (i + USize.ofNat 3) (within 3 h)).toUInt32
  else 0

@[inline] def ld32 (a : @& ByteArray) (i : USize) : UInt32 :=
  if h : i.toNat + 3 < a.size then
    (a.uget i (by omega)).toUInt32 ||| ((a.uget (i + USize.ofNat 1) (within 1 (by omega))).toUInt32 <<< 8) |||
    ((a.uget (i + USize.ofNat 2) (within 2 (by omega))).toUInt32 <<< 16) ||| ((a.uget (i + USize.ofNat 3) (within 3 h)).toUInt32 <<< 24)
  else 0

@[inline] def ld64 (a : @& ByteArray) (i : USize) : UInt64 :=
  if h : i.toNat + 7 < a.size then
    (a.uget i (by omega)).toUInt64 |||
    ((a.uget (i + USize.ofNat 1) (within 1 (by omega))).toUInt64 <<< 8) |||
    ((a.uget (i + USize.ofNat 2) (within 2 (by omega))).toUInt64 <<< 16) |||
    ((a.uget (i + USize.ofNat 3) (within 3 (by omega))).toUInt64 <<< 24) |||
    ((a.uget (i + USize.ofNat 4) (within 4 (by omega))).toUInt64 <<< 32) |||
    ((a.uget (i + USize.ofNat 5) (within 5 (by omega))).toUInt64 <<< 40) |||
    ((a.uget (i + USize.ofNat 6) (within 6 (by omega))).toUInt64 <<< 48) |||
    ((a.uget (i + USize.ofNat 7) (within 7 h)).toUInt64 <<< 56)
  else 0

/-! Writing, in place when the array has one owner. A place past the end is not written. -/

@[inline] def wr8 (a : ByteArray) (i : USize) (v : UInt8) : ByteArray := if h : i.toNat < a.size then a.uset i v h else a

@[inline] def wr16 (a : ByteArray) (i : USize) (v : UInt16) : ByteArray :=
  if h : i.toNat + 1 < a.size then
    let r : {b : ByteArray // b.size = a.size} := ⟨a, rfl⟩
    let r := set1 r i (v >>> 8).toUInt8 (by omega)
    (set1 r (i + USize.ofNat 1) v.toUInt8 (within 1 h)).1
  else a

@[inline] def wr32 (a : ByteArray) (i : USize) (v : UInt32) : ByteArray :=
  if h : i.toNat + 3 < a.size then
    let r : {b : ByteArray // b.size = a.size} := ⟨a, rfl⟩
    let r := set1 r i (v >>> 24).toUInt8 (by omega)
    let r := set1 r (i + USize.ofNat 1) (v >>> 16).toUInt8 (within 1 (by omega))
    let r := set1 r (i + USize.ofNat 2) (v >>> 8).toUInt8 (within 2 (by omega))
    (set1 r (i + USize.ofNat 3) v.toUInt8 (within 3 h)).1
  else a

@[inline] def st32 (a : ByteArray) (i : USize) (v : UInt32) : ByteArray :=
  if h : i.toNat + 3 < a.size then
    let r : {b : ByteArray // b.size = a.size} := ⟨a, rfl⟩
    let r := set1 r i v.toUInt8 (by omega)
    let r := set1 r (i + USize.ofNat 1) (v >>> 8).toUInt8 (within 1 (by omega))
    let r := set1 r (i + USize.ofNat 2) (v >>> 16).toUInt8 (within 2 (by omega))
    (set1 r (i + USize.ofNat 3) (v >>> 24).toUInt8 (within 3 h)).1
  else a

@[inline] def st64 (a : ByteArray) (i : USize) (v : UInt64) : ByteArray :=
  if h : i.toNat + 7 < a.size then
    let r : {b : ByteArray // b.size = a.size} := ⟨a, rfl⟩
    let r := set1 r i v.toUInt8 (by omega)
    let r := set1 r (i + USize.ofNat 1) (v >>> 8).toUInt8 (within 1 (by omega))
    let r := set1 r (i + USize.ofNat 2) (v >>> 16).toUInt8 (within 2 (by omega))
    let r := set1 r (i + USize.ofNat 3) (v >>> 24).toUInt8 (within 3 (by omega))
    let r := set1 r (i + USize.ofNat 4) (v >>> 32).toUInt8 (within 4 (by omega))
    let r := set1 r (i + USize.ofNat 5) (v >>> 40).toUInt8 (within 5 (by omega))
    let r := set1 r (i + USize.ofNat 6) (v >>> 48).toUInt8 (within 6 (by omega))
    (set1 r (i + USize.ofNat 7) (v >>> 56).toUInt8 (within 7 h)).1
  else a

/-! SipHash-2-4 of two words: the hash Linux makes its SYN cookies and keys its tables with. -/

@[inline] def rotl (x : UInt64) (r : UInt64) : UInt64 := (x <<< r) ||| (x >>> (64 - r))

@[inline] def sipRound (v0 v1 v2 v3 : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let v0 := v0 + v1
  let v1 := rotl v1 13 ^^^ v0
  let v0 := rotl v0 32
  let v2 := v2 + v3
  let v3 := rotl v3 16 ^^^ v2
  let v0 := v0 + v3
  let v3 := rotl v3 21 ^^^ v0
  let v2 := v2 + v1
  let v1 := rotl v1 17 ^^^ v2
  let v2 := rotl v2 32
  (v0, v1, v2, v3)

def sip (k0 k1 m0 m1 : UInt64) : UInt64 :=
  let v0 := k0 ^^^ 0x736f6d6570736575
  let v1 := k1 ^^^ 0x646f72616e646f6d
  let v2 := k0 ^^^ 0x6c7967656e657261
  let v3 := k1 ^^^ 0x7465646279746573
  let v3 := v3 ^^^ m0
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  let v0 := v0 ^^^ m0
  let v3 := v3 ^^^ m1
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  let v0 := v0 ^^^ m1
  -- The last word: sixteen bytes were hashed.
  let b : UInt64 := (16 : UInt64) <<< 56
  let v3 := v3 ^^^ b
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  let v0 := v0 ^^^ b
  let v2 := v2 ^^^ 0xff
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  let (v0, v1, v2, v3) := sipRound v0 v1 v2 v3
  v0 ^^^ v1 ^^^ v2 ^^^ v3

@[inline] def rd64 (a : @& ByteArray) (i : USize) : UInt64 :=
  if h : i.toNat + 7 < a.size then
    ((a.uget i (by omega)).toUInt64 <<< 56) |||
    ((a.uget (i + USize.ofNat 1) (within 1 (by omega))).toUInt64 <<< 48) |||
    ((a.uget (i + USize.ofNat 2) (within 2 (by omega))).toUInt64 <<< 40) |||
    ((a.uget (i + USize.ofNat 3) (within 3 (by omega))).toUInt64 <<< 32) |||
    ((a.uget (i + USize.ofNat 4) (within 4 (by omega))).toUInt64 <<< 24) |||
    ((a.uget (i + USize.ofNat 5) (within 5 (by omega))).toUInt64 <<< 16) |||
    ((a.uget (i + USize.ofNat 6) (within 6 (by omega))).toUInt64 <<< 8) |||
    (a.uget (i + USize.ofNat 7) (within 7 h)).toUInt64
  else 0

/-- What a word of 32 bits adds to the sum a checksum is made of: its two halves. -/
@[inline] def halves (w : UInt32) : UInt64 := (w >>> 16).toUInt64 + (w &&& 0xffff).toUInt64

/-- The sum the Internet checksum is made of, over the bytes from `i` to `stop`: eight at a time while
there are eight, as two halves so that nothing is lost off the top, then two at a time. -/
partial def sum16 (a : @& ByteArray) (i stop : USize) (acc : UInt64) : UInt64 :=
  if i + 8 ≤ stop then
    let w := rd64 a i
    sum16 a (i + 8) stop (acc + (w >>> 32) + (w &&& 0xffffffff))
  else if i + 1 < stop then sum16 a (i + 2) stop (acc + (rd16 a i).toUInt64)
  else if i < stop then acc + ((rd8 a i).toUInt64 <<< 8)
  else acc

@[inline] def fold (s : UInt64) : UInt16 :=
  let s : UInt64 := (s &&& (0xffffffff : UInt64)) + (s >>> (32 : UInt64))
  let s : UInt64 := (s &&& (0xffff : UInt64)) + (s >>> (16 : UInt64))
  let s : UInt64 := (s &&& (0xffff : UInt64)) + (s >>> (16 : UInt64))
  let s : UInt64 := (s &&& (0xffff : UInt64)) + (s >>> (16 : UInt64))
  ~~~ s.toUInt16

/-- `n` bytes of nothing, made by doubling: a list of them first would be eight times the size. -/
def zeros (n : Nat) : ByteArray :=
  (go (ByteArray.mk (Array.replicate 64 0)) 64).extract 0 n
where
  go (b : ByteArray) : Nat → ByteArray
    | 0 => b
    | fuel + 1 => if b.size < n then go (b ++ b) fuel else b

/-- A fresh table, and a fresh array to write frames to. -/
def table (cfg : Tuning) : ByteArray := zeros (128 + (1 <<< cfg.slotBits.toNat) * 128)

def outbox (bytes : Nat) : ByteArray := st64 (zeros (8 + bytes)) 0 8

/-- How far the frames written reach. -/
@[inline] def written (tx : @& ByteArray) : USize := (ld64 tx 0).toUSize

@[inline] def bump (t : ByteArray) (counter : USize) : ByteArray := st64 t counter (ld64 t counter + 1)

@[inline] def keyOf (rip : UInt32) (rport lport : UInt16) : UInt64 :=
  (rip.toUInt64 <<< 32) ||| (rport.toUInt64 <<< 16) ||| lport.toUInt64

@[inline] def home (cfg : @& Tuning) (k : UInt64) : USize :=
  (sip cfg.key0 cfg.key1 k 0).toUSize &&& (((1 : USize) <<< cfg.slotBits) - 1)

/-- The number that answers a SYN, but for its ten lowest bits: nothing is kept, and the same number is
worked out again when the third packet comes. `tick` moves on every minute or so, and the one before is
still taken. `low` is what goes below it in the open (`lowOf`), hashed with the rest so that it cannot
be changed on the way. That leaves 22 bits to be guessed by someone who would open a connection from an
address that is not theirs (Linux's cookies leave 24): one guess in two million, with two ticks taken. -/
@[inline] def cookie (cfg : @& Tuning) (k : UInt64) (theirs tick low : UInt32) : UInt32 :=
  (sip cfg.key1 cfg.key0 k ((theirs.toUInt64 <<< 32) ||| (tick.toUInt64 <<< 10) ||| low.toUInt64)).toUInt32 &&& 0xfffffc00

/-- How a SYN says its sender's window is to be shifted: its options looked through for it. 255 when it
does not say (and then neither end scales), which is written 15. -/
partial def scaleOffered (rx : @& ByteArray) (i stop : USize) : UInt32 :=
  if i ≥ stop then 15 else
  let kind := rd8 rx i
  if kind == 0 then 15
  else if kind == 1 then scaleOffered rx (i + 1) stop
  else
    let size := (rd8 rx (i + 1)).toUSize
    if size < 2 || i + size > stop then 15
    else if kind == 3 && size == 3 then (let by_ := (rd8 rx (i + 2)).toUInt32; if by_ > 14 then 14 else by_)
    else scaleOffered rx (i + size) stop

/-- The ten lowest bits of the number that answers a SYN: four of the clock in steps of 64 ms, four for
the window's shift (15 for none), two for the largest segment. -/
@[inline] def lowOf (now : UInt32) (scale index : UInt32) : UInt32 := (((now >>> 6) &&& 15) <<< 6) ||| (scale <<< 2) ||| index

/-- The largest segments a cookie can remember, by its two lowest bits: the four Linux uses. -/
@[inline] def segmentOf (index : UInt32) : UInt16 :=
  if index == 0 then 536 else if index == 1 then 1300 else if index == 2 then 1440 else 1460

@[inline] def indexOf (mss : UInt16) : UInt32 :=
  if mss ≥ 1460 then 3 else if mss ≥ 1440 then 2 else if mss ≥ 1300 then 1 else 0

/-- The largest segment a SYN says its sender will take: its options are looked through for it. -/
partial def offered (rx : @& ByteArray) (i stop : USize) : UInt16 :=
  if i ≥ stop then 536 else
  let kind := rd8 rx i
  if kind == 0 then 536
  else if kind == 1 then offered rx (i + 1) stop
  else
    let size := (rd8 rx (i + 1)).toUSize
    if size < 2 || i + size > stop then 536
    else if kind == 2 && size == 4 then rd16 rx (i + 2)
    else offered rx (i + size) stop

/-- What is kept of the round trip, with one more of `sample` milliseconds taken in: as RFC 6298 has it,
an eighth of the way towards the new one, and how far it strays a quarter of the way towards how far this
one was off. The low sixteen bits are eight times the smoothed round trip and are never nothing once one
is measured; the high sixteen are four times the straying. -/
@[noinline] def measure (kept sample : UInt32) : UInt32 :=
  let sample := if sample > 8000 then 8000 else sample
  let smooth := kept &&& 0xffff
  let stray := kept >>> 16
  if smooth == 0 then
    let smooth := sample <<< 3
    ((sample <<< 1) <<< 16) ||| (if smooth == 0 then 1 else smooth)
  else
    let was := smooth >>> 3
    let off := if sample > was then sample - was else was - sample
    let stray := stray - (stray >>> 2) + off
    let smooth := smooth - (smooth >>> 3) + sample
    ((if stray > 0xffff then 0xffff else stray) <<< 16) ||| (if smooth > 0xffff then 0xffff else if smooth == 0 then 1 else smooth)

/-- The wait before sending again, from what is kept of the round trip and how many times the wait has
run out already. -/
@[inline] def waitOf (cfg : @& Tuning) (kept : UInt32) (tries : UInt8) : UInt32 :=
  let smooth := kept &&& 0xffff
  let stray := kept >>> 16
  let once :=
    if smooth == 0 then cfg.wait
    else
      let w := (smooth >>> 3) + (if stray == 0 then 1 else stray)
      if w < cfg.waitLeast then cfg.waitLeast else w
  let w := once <<< (if tries > 6 then 6 else tries).toUInt32
  if w > cfg.waitMost then cfg.waitMost else w

/-- Where the entry at place `i` begins in the table, and the place of the entry that begins at `off`. -/
@[inline] def place (i : USize) : USize := (i <<< 7) + 128
@[inline] def placeOf (off : USize) : USize := (off - 128) >>> 7

/-- Where the entry with this key is, looking on from place `i`; 0 when there is none. -/
partial def find (t : @& ByteArray) (mask : USize) (k : UInt64) (i : USize) : USize :=
  let off := place i
  if rd8 t off == 0 then 0
  else if ld64 t (off + 8) == k then off
  else find t mask k ((i + 1) &&& mask)

/-- The first free place from `i` on. The table is never more than half full. -/
partial def vacant (t : @& ByteArray) (mask : USize) (i : USize) : USize :=
  let off := place i
  if rd8 t off == 0 then off else vacant t mask ((i + 1) &&& mask)

/-- The entry at place `i` taken out. Those after it that were put there for want of their own place are
moved back, so that looking never has to step over a place that was once in use. -/
partial def remove (cfg : @& Tuning) (t : ByteArray) (mask : USize) (i j : USize) : ByteArray :=
  let hole := place i
  let off := place j
  if rd8 t off == 0 then wr8 t hole 0
  else
    let h := home cfg (ld64 t (off + 8))
    let stays := if i ≤ j then i < h && h ≤ j else i < h || h ≤ j
    if stays then remove cfg t mask i ((j + 1) &&& mask)
    else
      let t := st64 t hole (ld64 t off)
      let t := st64 t (hole + 8) (ld64 t (off + 8))
      let t := st64 t (hole + 16) (ld64 t (off + 16))
      let t := st64 t (hole + 24) (ld64 t (off + 24))
      let t := st64 t (hole + 32) (ld64 t (off + 32))
      let t := st64 t (hole + 40) (ld64 t (off + 40))
      let t := st64 t (hole + 48) (ld64 t (off + 48))
      let t := st64 t (hole + 56) (ld64 t (off + 56))
      let t := st64 t (hole + 64) (ld64 t (off + 64))
      let t := st64 t (hole + 72) (ld64 t (off + 72))
      remove cfg t mask j ((j + 1) &&& mask)

/-- The entry that begins at `off` taken out, and one fewer counted as live. -/
@[inline] def forget (cfg : @& Tuning) (t : ByteArray) (mask off : USize) : ByteArray :=
  let i := placeOf off
  let t := remove cfg t mask i ((i + 1) &&& mask)
  st64 t 0 (ld64 t 0 - 1)

/-- A frame written to `tx`: to this Ethernet and IP address and port, with these flags and numbers, and
`length` bytes of `payload` from `start`. Nothing is written when there is no room. -/
def emit (cfg : @& Tuning) (tx : ByteArray) (macHigh : UInt16) (macLow rip : UInt32) (rport : UInt16)
    (flags : UInt8) (seq ack : UInt32) (mssOption : Bool) (payload : @& ByteArray) (start length : USize)
    (scaleOption : Bool := false) : ByteArray :=
  let at_ := written tx
  let options : USize := if mssOption then (if scaleOption then 8 else 4) else 0
  let segment := 20 + options + length
  let total := 34 + segment
  if at_.toNat + 2 + total.toNat > tx.size then tx else
  let tx := wr16 tx at_ total.toUInt16
  let e := at_ + 2
  let tx := wr32 (wr16 tx e macHigh) (e + 2) macLow
  let tx := wr32 (wr16 tx (e + 6) cfg.macHigh) (e + 8) cfg.macLow
  let tx := wr16 tx (e + 12) 0x0800
  let ip := e + 14
  let tx := wr16 tx ip 0x4500
  let tx := wr16 tx (ip + 2) (20 + segment).toUInt16
  let tx := wr32 tx (ip + 4) 0x00004000
  let tx := wr16 tx (ip + 8) 0x4006
  let tx := wr16 tx (ip + 10) 0
  let tx := wr32 tx (ip + 12) cfg.localIp
  let tx := wr32 tx (ip + 16) rip
  let t := ip + 20
  let tx := wr16 tx t cfg.localPort
  let tx := wr16 tx (t + 2) rport
  let tx := wr32 tx (t + 4) seq
  let tx := wr32 tx (t + 8) ack
  let tx := wr8 tx (t + 12) (if mssOption then (if scaleOption then 0x70 else 0x60) else 0x50)
  let tx := wr8 tx (t + 13) flags
  let tx := wr16 tx (t + 14) cfg.window
  let tx := wr32 tx (t + 16) 0
  let tx := if mssOption then wr16 (wr16 tx (t + 20) 0x0204) (t + 22) cfg.mss else tx
  -- This end's own window is not scaled: the option is there, saying no places, so that the peer may
  -- scale its own.
  let tx := if mssOption && scaleOption then wr32 tx (t + 24) 0x01030300 else tx
  let tx := if length == 0 then tx else payload.copySlice start.toNat tx (t + 20 + options).toNat length.toNat
  let tx :=
    if cfg.checksums then
      -- The sums are made from the values that were written, which is the same as reading them back and
      -- costs a third of it; only the payload is read, from where it came.
      let addresses := halves cfg.localIp + halves rip
      let tx := wr16 tx (ip + 10) (fold (0x4500 + (20 + segment).toUInt64 + 0x4000 + 0x4006 + addresses))
      let first : UInt64 := if mssOption then (if scaleOption then 0x7000 else 0x6000) else 0x5000
      let opening : UInt64 := if mssOption then 0x0204 + cfg.mss.toUInt64 + (if scaleOption then 0x0103 + 0x0300 else 0) else 0
      let header := cfg.localPort.toUInt64 + rport.toUInt64 + halves seq + halves ack + (first ||| flags.toUInt64) +
        cfg.window.toUInt64 + opening
      let body := if length == 0 then 0 else sum16 payload start (start + length) 0
      wr16 tx (t + 16) (fold (addresses + 6 + segment.toUInt64 + header + body))
    else tx
  st64 tx 0 (at_ + 2 + total).toUInt64

/-- How far sending may go for an entry: the answer and then the end of the stream (which counts as one
more; `tail` is 1 when there is to be an end and 0 when the connection stays open), no further than the
peer's window and this end's own allow beyond what is acknowledged, and never back. The end goes with
the last of the answer, whatever the windows say, since it takes no room. -/
@[inline] def reach (sent unacked first size tail window own : UInt32) : UInt32 :=
  let last := first + size
  let allowed := if window < own then window else own
  -- What is left of the stream, its end counted: nothing once the last of it is acknowledged.
  let left := last + tail - unacked
  let to := if left == 0 then sent else if left - tail ≤ allowed then last + tail else unacked + allowed
  if to - unacked < sent - unacked then sent else to

/-- `to` brought back to what there is room in `tx` to write from `sent`: whole segments only. -/
@[inline] def fitting (tx : @& ByteArray) (sent to mss : UInt32) : UInt32 :=
  let room := (tx.usize - written tx) / (mss.toUSize + 64)
  let most := sent + room.toUInt32 * mss
  if room ≥ 4096 || to - sent ≤ most - sent then to else most

/-- The stream from `at_` to `to` put into segments and written: the answer's bytes, no more than `mss`
to a segment, and the end of the stream with the last of them when `to` is past the answer. -/
partial def segments (cfg : @& Tuning) (answer : @& ByteArray) (tx : ByteArray) (macHigh : UInt16) (macLow rip : UInt32)
    (rport : UInt16) (expected first size mss at_ to : UInt32) : ByteArray :=
  if at_ == to then tx else
  let last := first + size
  if at_ == last then
    emit cfg tx macHigh macLow rip rport 0x11 at_ expected false answer 0 0
  else
    let left := (if to - at_ ≤ last - at_ then to else last) - at_
    let length := if left < mss then left else mss
    let ends := at_ + length == last && to == last + 1
    let flags : UInt8 := if ends then 0x19 else if at_ + length == last then 0x18 else 0x10
    let tx := emit cfg tx macHigh macLow rip rport flags at_ expected false answer (at_ - first).toUSize length.toUSize
    segments cfg answer tx macHigh macLow rip rport expected first size mss (at_ + length + (if ends then 1 else 0)) to

/-- What `respond` says when it wants more before it answers, with its number to keep. -/
@[inline] def more (number : UInt32) : UInt64 := (number.toUInt64 <<< 32) ||| 0xffffffff

/-- What `respond` says to have answer `index` sent and then the stream ended, with its number to keep. -/
@[inline] def send (index number : UInt32) : UInt64 := (number.toUInt64 <<< 32) ||| index.toUInt64

/-- What `respond` says to have answer `index` sent and the connection left open for another request. Its
number is what it will be shown with the first bytes of that request. -/
@[inline] def sendOn (index number : UInt32) : UInt64 := (number.toUInt64 <<< 32) ||| index.toUInt64 ||| 0x80000000

/-! `loop` below is the dearer for every line in it, whether the line is reached or not, and dearest for
holding an answer, which it must then let go of on each of its many ways out. So what touches an answer
is in functions of its own, which `loop` calls with the answer's number. -/

/-- The answer to a SYN, written to `tx`: its options are from `i` to `stop` in `rx`. -/
@[noinline] def greet (cfg : @& Tuning) (rx : @& ByteArray) (i stop : USize) (k : UInt64) (seq now : UInt32) (tx : ByteArray)
    (macHigh : UInt16) (macLow rip : UInt32) (rport : UInt16) : ByteArray :=
  let theirs := offered rx i stop
  let scale := scaleOffered rx i stop
  let low := lowOf now scale (indexOf (if theirs < cfg.mss then theirs else cfg.mss))
  let ours := cookie cfg k seq (now >>> 16) low ||| low
  emit cfg tx macHigh macLow rip rport 0x12 ours (seq + 1) true ByteArray.empty 0 0 (scale != 15)

/-- Whether `theirs` is the cookie this end would have given for this connection, this tick or last. -/
@[noinline] def genuine (cfg : @& Tuning) (k : UInt64) (first tick theirs low : UInt32) : Bool :=
  theirs == cookie cfg k first tick low || theirs == cookie cfg k first (tick - 1) low

/-- A new entry at `off` for the connection whose handshake's third packet has just come: what it
acknowledges and its number, the window it gives, and `low`, the ten bits the cookie carried. -/
@[noinline] def admit (cfg : @& Tuning) (t : ByteArray) (off : USize) (k : UInt64) (acked seq : UInt32) (window : UInt16)
    (low : UInt32) (macHigh : UInt16) (macLow now : UInt32) : ByteArray :=
  let t := st64 t off 1
  let t := st64 t (off + 8) k
  let t := st32 (st32 t (off + 16) acked) (off + 20) acked
  let t := st32 (st32 (st32 t (off + 24) seq) (off + 28) 0) (off + 32) acked
  let t := wr16 (wr16 t (off + 36) window) (off + 38) (segmentOf (low &&& 3))
  let t := wr32 (wr16 t (off + 40) macHigh) (off + 42) macLow
  -- How long the handshake took, from the cookie, in steps of 64 ms and at most 15 of them: the first
  -- round trip, when it is a step or more. Less than that says nothing a setting does not say better.
  let steps := ((now >>> 6) - (low >>> 6)) &&& 15
  let timed := cfg.measures && steps != 0
  let t := st32 (st32 t (off + 48) 0) (off + 52) (if timed then measure 0 (steps <<< 6) else 0)
  let t := st64 t (off + 56) 0
  let t := st64 (st64 t (off + 64) 0) (off + 72) (if (low >>> 2) &&& (15 : UInt32) == 15 then (0 : UInt32) else (low >>> 2) &&& (15 : UInt32)).toUInt64
  let t := if timed then bump t 120 else t
  bump (bump t 0) 8

/-- How long answer `which` is. -/
@[noinline] def sizeAt (answers : @& Array ByteArray) (which : UInt32) : UInt32 :=
  (answers.getD which.toNat ByteArray.empty).size.toUInt32

/-- Whether the answer the entry at `off` is sending is acknowledged to its last byte by `unacked`. -/
@[noinline] def whole (answers : @& Array ByteArray) (t : @& ByteArray) (off : USize) (unacked : UInt32) : Bool :=
  unacked == ld32 t (off + 28) + sizeAt answers (ld32 t (off + 56))

/-- `segments` for answer `which`. -/
@[noinline] def segmentsOf (cfg : @& Tuning) (answers : @& Array ByteArray) (which : UInt32) (tx : ByteArray) (macHigh : UInt16)
    (macLow rip : UInt32) (rport : UInt16) (expected first size mss at_ to : UInt32) : ByteArray :=
  segments cfg (answers.getD which.toNat ByteArray.empty) tx macHigh macLow rip rport expected first size mss at_ to

/-- Every frame of `rx` from `o` to `stop` taken in turn. -/
@[specialize] partial def loop (cfg : @& Tuning) (answers : @& Array ByteArray)
    (respond : ByteArray → USize → USize → UInt32 → UInt64) (now : UInt32) (rx : @& ByteArray) (o stop : USize)
    (t tx : ByteArray) : ByteArray × ByteArray :=
  if o + 2 > stop then (t, tx) else
  let n := (rd16 rx o).toUSize
  let f := o + 2
  let next := f + n
  if next > stop then (t, tx) else
  -- Ethernet carrying IPv4 with no options carrying TCP, for this address and port; all else is dropped.
  if n < 54 || rd16 rx (f + 12) != 0x0800 || rd8 rx (f + 14) != 0x45 || rd8 rx (f + 23) != 6 ||
      rd32 rx (f + 30) != cfg.localIp || rd16 rx (f + 36) != cfg.localPort then
    loop cfg answers respond now rx next stop (bump t 32) tx
  else
  let ipLength := (rd16 rx (f + 16)).toUSize
  let header := ((rd8 rx (f + 46)) >>> 4).toUSize <<< 2
  if header < 20 || ipLength < 20 + header || 14 + ipLength > n then loop cfg answers respond now rx next stop (bump t 32) tx
  else
  let addresses := halves (rd32 rx (f + 26)) + halves (rd32 rx (f + 30))
  let sound := !cfg.checksums ||
    (fold (halves (rd32 rx (f + 14)) + halves (rd32 rx (f + 18)) + halves (rd32 rx (f + 22)) + addresses) == 0 &&
     fold (sum16 rx (f + 34) (f + 14 + ipLength) (addresses + 6 + (ipLength - 20).toUInt64)) == 0)
  if !sound then loop cfg answers respond now rx next stop (bump t 32) tx
  else
  let macHigh := rd16 rx (f + 6)
  let macLow := rd32 rx (f + 8)
  let rip := rd32 rx (f + 26)
  let rport := rd16 rx (f + 34)
  let seq := rd32 rx (f + 38)
  let acked := rd32 rx (f + 42)
  let flags := rd8 rx (f + 47)
  let length := (ipLength - 20 - header).toUInt32
  let k := keyOf rip rport cfg.localPort
  let mask : USize := ((1 : USize) <<< cfg.slotBits) - 1
  if flags &&& 0x02 != 0 then
    -- A SYN is answered from the cookie and nothing is kept. (One for a connection that is open is too:
    -- its answer will not fit that connection and the peer will see so.)
    if flags &&& 0x10 != 0 then loop cfg answers respond now rx next stop (bump t 32) tx
    else if cfg.busy != 0 && ld64 t 0 > cfg.busy then loop cfg answers respond now rx next stop (bump t 112) tx
    else loop cfg answers respond now rx next stop (bump t 24) (greet cfg rx (f + 54) (f + 34 + header) k seq now tx macHigh macLow rip rport)
  else
  let h := home cfg k
  let known := find t mask k h
  if flags &&& 0x04 != 0 then
    -- A reset is believed when it is exactly where the stream has got to.
    if known != 0 && seq == ld32 t (known + 24) then loop cfg answers respond now rx next stop (bump (forget cfg t mask known) 48) tx
    else loop cfg answers respond now rx next stop t tx
  else if flags &&& 0x10 == 0 then loop cfg answers respond now rx next stop (bump t 32) tx
  else
  -- The third packet of a handshake makes the entry, if its number is the cookie's and there is room.
  let tick := now >>> 16
  let theirs := (acked - 1) &&& 0xfffffc00
  let low := (acked - 1) &&& 0x3ff
  let fresh := if known != 0 then false else genuine cfg k (seq - 1) tick theirs low
  let room := ld64 t 0 < ((1 : USize) <<< (cfg.slotBits - 1)).toUInt64
  if known == 0 && !fresh then
    -- It belongs to nothing here: said so, unless told to keep quiet.
    if cfg.resetStrays then loop cfg answers respond now rx next stop (bump (bump t 32) 88) (emit cfg tx macHigh macLow rip rport 0x04 acked 0 false ByteArray.empty 0 0)
    else loop cfg answers respond now rx next stop (bump t 32) tx
  else if known == 0 && !room then loop cfg answers respond now rx next stop (bump t 56) tx
  else
  let off := if known != 0 then known else vacant t mask h
  let t := if known != 0 then t else admit cfg t off k acked seq (rd16 rx (f + 48)) low macHigh macLow now
  let state := rd8 t off
  let sent := ld32 t (off + 16)
  let was := ld32 t (off + 20)
  let expected := ld32 t (off + 24)
  let mss := (rd16 t (off + 38)).toUInt32
  -- An acknowledgement counts when it is of something sent, ever, and not yet acknowledged. After a
  -- timer `sent` has been put back, and the peer may acknowledge past it what it had all along: then
  -- sending goes on from there.
  let top := ld32 t (off + 32)
  let unacked := if acked - was ≤ top - was then acked else was
  let moved := unacked != was
  let sent := if sent - was < unacked - was then unacked else sent
  -- The peer's window, shut until now, is open, and the one byte that was tried against it is not
  -- acknowledged: it was not taken, and sending goes on from it.
  let reopened := known != 0 && !moved && rd16 t (off + 36) == 0 && rd16 rx (f + 48) != 0 && sent - unacked == 1
  let sent := if reopened then unacked else sent
  let fin := flags &&& 0x01 != 0
  if seq != expected then
    -- Not the next byte of the stream: kept is nothing, and the peer is told which byte is wanted.
    let t := st32 t (off + 20) unacked
    let t := if moved then wr8 (wr8 t (off + 1) (rd8 t (off + 1) &&& 0xf3)) (off + 2) 0 else t
    if length == 0 && !fin then loop cfg answers respond now rx next stop t tx
    else loop cfg answers respond now rx next stop (bump t 40) (emit cfg tx macHigh macLow rip rport 0x10 sent expected false ByteArray.empty 0 0)
  else
  if state == 3 then
    -- Both ends had closed. A last segment sent again is acknowledged again.
    loop cfg answers respond now rx next stop t (if fin then emit cfg tx macHigh macLow rip rport 0x10 sent expected false ByteArray.empty 0 0 else tx)
  else
  let marks := rd8 t (off + 1)
  -- An answer after which the connection stays open, all acknowledged by this very segment: the
  -- connection is as it was before the request, and what the segment carries is the next one. (A peer
  -- that has its answer sends the next request and the acknowledgement together.)
  let over := if state == 2 && marks &&& 16 != 0 then whole answers t off unacked else false
  let state : UInt8 := if over then 1 else state
  let marks := if over then marks &&& 1 else marks
  -- While an answer is on its way on a connection that stays open, nothing the peer sends is taken.
  let held := state == 2 && marks &&& 16 != 0 && length != 0
  let fin := fin && !held
  let length := if held then 0 else length
  let expected := expected + length + (if fin then 1 else 0)
  let peerClosed := fin || marks &&& 1 != 0
  -- The application is shown what has come, while it has not yet answered: it names an answer, or
  -- wants more. If the peer ends before it has named one, the end alone is sent.
  let said := if state == 1 && length != 0 then respond rx (f + 34 + header) length.toUSize (ld32 t (off + 60))
    else more (ld32 t (off + 60))
  let number := (said >>> 32).toUInt32
  let named := state == 1 && length != 0 && (said.toUInt32 &&& 0x7fffffff).toNat < answers.size
  let ends := state == 1 && !named && fin
  let begins := named || ends
  let state : UInt8 := if begins then 2 else state
  let bare := if ends then true else marks &&& 2 != 0
  let first := if begins then sent else ld32 t (off + 28)
  let top := if begins then sent else top
  let which := if named then said.toUInt32 &&& 0x7fffffff else ld32 t (off + 56)
  let size : UInt32 := if bare then 0 else sizeAt answers which
  -- Whether the connection stays open after the answer: as the application said, unless the peer has
  -- closed, when the answer is followed by this end's closing too.
  let stays := (if named then said.toUInt32 &&& 0x80000000 != 0 else marks &&& 16 != 0) && !peerClosed
  let tail : UInt32 := if stays then 0 else 1
  -- This end's own window: so many segments to begin with; one more for each acknowledgement that moves
  -- while it is below `limit`, which is where it was halved to when a segment was last lost; above that,
  -- one more a window's worth of acknowledgements.
  let own := ld32 t (off + 48)
  let limit := if begins then cfg.mostWindow * mss else ld32 t (off + 68)
  -- Making good what was lost: begun when a segment is seen to be lost, over when everything sent by
  -- then is acknowledged. An acknowledgement that moves but stops short of that says the segment it
  -- stops at was lost too.
  let mending := marks &&& 8 != 0 && !begins
  let mark := ld32 t (off + 76)
  let reached := mark == unacked || mark - unacked ≥ 0x80000000
  let part := mending && moved && !reached
  let mending := mending && !(moved && reached)
  let own := if begins then cfg.firstWindow * mss
    else if moved && !part && own != 0 && own < cfg.mostWindow * mss then
      (if own < limit then own + mss else own + (if mss * mss / own == 0 then 1 else mss * mss / own))
    else own
  let window := (rd16 rx (f + 48)).toUInt32 <<< ((rd8 t (off + 72)).toUInt32 &&& 15)
  -- The same acknowledgement again, with nothing else in the segment and something still owed: counted,
  -- and at the count set, the segment after it is sent again and this end's window halved.
  -- (An acknowledgement that says the window is shut is the answer to a byte tried against it, and says
  -- nothing was lost.)
  let repeated := state == 2 && !begins && !moved && length == 0 && !fin && acked == was && sent != was && window != 0
  let count := rd8 t (off + 3)
  let count : UInt8 := if moved || begins then 0 else if repeated && count < 255 then count + 1 else count
  let again := repeated && cfg.repeats != 0 && count == cfg.repeats && !mending
  let half := if own / 2 < 2 * mss then 2 * mss else own / 2
  let limit := if again then half else limit
  let own := if again then half else own
  let tx :=
    if again || part then
      let one := reach unacked unacked first size tail mss mss
      segmentsOf cfg answers which tx macHigh macLow rip rport expected first size mss unacked (if one - unacked ≤ sent - unacked then one else sent)
    else tx
  let t := if again || part then bump t 96 else t
  let t := if again then st32 t (off + 76) top else t
  let mending := mending || again
  let wanted := if state == 2 then reach sent unacked first size tail window own else sent
  -- No further than there is room to write: what is held back goes when an acknowledgement or the sweep
  -- comes round to this connection again, and is not taken for sent.
  let to := fitting tx sent wanted mss
  let t := if to != wanted then bump t 104 else t
  -- The round trip. One byte at a time is timed: the first of something sent for the first time. When an
  -- acknowledgement passes it, how long that took is taken in; if anything is sent again meanwhile the
  -- timing is dropped, since which sending was acknowledged cannot then be told.
  let kept := ld32 t (off + 52)
  let timing := marks &&& 4 != 0 && !begins
  let timed := ld32 t (off + 64)
  let passed := cfg.measures && timing && moved && unacked - was > timed - was
  let kept := if passed then measure kept (now.toUInt16 - rd16 t (off + 46)).toUInt32 else kept
  let t := if passed then bump t 120 else t
  let timing := timing && !passed && !again && !part
  let starts := !timing && !mending && to != sent && sent == top
  let timed := if starts then sent else timed
  let t := if starts then wr16 t (off + 46) now.toUInt16 else t
  let timing := timing || starts
  let top := if to - unacked > top - unacked then to else top
  let tx :=
    if to != sent then segmentsOf cfg answers which tx macHigh macLow rip rport expected first size mss sent to
    else if length != 0 || fin then emit cfg tx macHigh macLow rip rport 0x10 sent expected false ByteArray.empty 0 0
    else tx
  if state == 2 && !stays && unacked == first + size + 1 && peerClosed then
    -- Both ends have closed and ours is acknowledged: the entry goes, at once or after `linger`.
    if cfg.linger == 0 then loop cfg answers respond now rx next stop (bump (forget cfg t mask off) 16) tx
    else
      let t := st32 (wr8 t off 3) (off + 4) (now + cfg.linger)
      let t := st32 (st32 (st32 t (off + 16) to) (off + 20) unacked) (off + 24) expected
      loop cfg answers respond now rx next stop (bump t 16) tx
  else
    let wait := waitOf cfg kept (if moved then 0 else rd8 t (off + 2))
    -- Something is owed an acknowledgement, or there is more to send that was held back: looked at
    -- again soon. Otherwise the connection has `idle` to say something.
    -- An answer after which the connection stays open, all acknowledged: the connection is as it was
    -- before the request, and waits for the next.
    let answered := state == 2 && stays && unacked == first + size
    let state : UInt8 := if answered then 1 else state
    let due := now + (if unacked != to || (state == 2 && to != first + size + tail) then wait else cfg.idle)
    let t := wr8 (wr8 t off state) (off + 1) (if answered then (if peerClosed then 1 else 0) else
      (if peerClosed then 1 else 0) ||| (if bare then 2 else 0) ||| (if timing then 4 else 0) ||| (if mending then 8 else 0) |||
      (if stays then 16 else 0))
    -- A peer that answers with its window still shut is there, and is not given up on: the count of
    -- tries goes back to half of what is allowed, so that it takes several unanswered in a row, and
    -- not two, to give up on one that has been answering.
    let tries := rd8 t (off + 2)
    let t := if moved then wr8 t (off + 2) 0
      else if window == 0 && acked == was && length == 0 && tries > cfg.tries / 2 then wr8 t (off + 2) (cfg.tries / 2)
      else t
    let t := wr8 t (off + 3) count
    let t := st32 t (off + 4) due
    let t := st32 (st32 t (off + 16) to) (off + 20) unacked
    let t := st32 (st32 (st32 t (off + 24) expected) (off + 28) first) (off + 32) top
    let t := wr16 t (off + 36) (rd16 rx (f + 48))
    let t := st32 t (off + 48) own
    let t := if passed then st32 t (off + 52) kept else t
    let t := st32 (st32 t (off + 56) which) (off + 60) number
    -- What few frames change is written only when it has changed.
    let t := if starts then st32 t (off + 64) timed else t
    let t := if begins || again then st32 t (off + 68) limit else t
    loop cfg answers respond now rx next stop t tx

/-- The frames in the first `length` bytes of `rx` taken in, the table changed, and the answers written
to `tx` from its start. -/
@[specialize] def process (cfg : @& Tuning) (answers : @& Array ByteArray)
    (respond : ByteArray → USize → USize → UInt32 → UInt64) (now : UInt32) (rx : @& ByteArray) (length : USize)
    (t tx : ByteArray) : ByteArray × ByteArray :=
  loop cfg answers respond now rx 0 length t (st64 tx 0 8)

/-- `left` places of the table looked at from place `i` on, and what is due there done. -/
partial def sweep (cfg : @& Tuning) (answers : @& Array ByteArray) (now : UInt32) (mask i left : USize) (t tx : ByteArray) :
    ByteArray × ByteArray :=
  if left == 0 then (st64 t 64 i.toUInt64, tx) else
  let off := place i
  let state := rd8 t off
  let onward := (i + 1) &&& mask
  if state == 0 || now - ld32 t (off + 4) ≥ 0x80000000 then sweep cfg answers now mask onward (left - 1) t tx
  else if state == 3 then
    -- Waited out. What moves into this place is looked at next, in this same place.
    sweep cfg answers now mask i (left - 1) (forget cfg t mask off) tx
  else
    let k := ld64 t (off + 8)
    let rip := (k >>> 32).toUInt32
    let rport := (k >>> 16).toUInt16
    let macHigh := rd16 t (off + 40)
    let macLow := rd32 t (off + 42)
    let sent := ld32 t (off + 16)
    let unacked := ld32 t (off + 20)
    let expected := ld32 t (off + 24)
    let tries := rd8 t (off + 2)
    let first := ld32 t (off + 28)
    let which := ld32 t (off + 56)
    let size : UInt32 := if rd8 t (off + 1) &&& 2 != 0 then 0 else sizeAt answers which
    let mss := (rd16 t (off + 38)).toUInt32
    let tail : UInt32 := if rd8 t (off + 1) &&& 16 != 0 then 0 else 1
    if state == 2 && unacked == sent && sent != first + size + tail then
      -- Nothing is on its way and there is more to send: it was held back for want of room, or the
      -- peer's window was shut. It goes on from here, as far as the windows and the room allow.
      let wanted := reach sent unacked first size tail ((rd16 t (off + 36)).toUInt32 <<< ((rd8 t (off + 72)).toUInt32 &&& 15)) (ld32 t (off + 48))
      let to := fitting tx sent wanted mss
      -- A window shut to nothing is tried with one byte: if the word that it had opened was lost, this
      -- is how it is heard again. The byte is then owed an acknowledgement like any other.
      let to := if to == sent && rd16 t (off + 36) == 0 then sent + 1 else to
      let tx := if to != sent then segmentsOf cfg answers which tx macHigh macLow rip rport expected first size mss sent to else tx
      let top := ld32 t (off + 32)
      let t := st32 (st32 t (off + 16) to) (off + 4) (now + waitOf cfg (ld32 t (off + 52)) 0)
      let t := if to - unacked > top - unacked then st32 t (off + 32) to else t
      sweep cfg answers now mask onward (left - 1) t tx
    else if state == 1 && unacked == sent then
      -- Open, with nothing asked of it for `idle`: this end closes, as it would after an answer with
      -- nothing in it, and the peer's closing or a timer finishes it.
      let tx := emit cfg tx macHigh macLow rip rport 0x11 sent expected false ByteArray.empty 0 0
      let t := wr8 (wr8 (wr8 t off 2) (off + 1) ((rd8 t (off + 1) &&& 1) ||| 2)) (off + 2) 0
      let t := st32 (st32 (st32 t (off + 16) (sent + 1)) (off + 28) sent) (off + 32) (sent + 1)
      let t := st32 t (off + 4) (now + waitOf cfg (ld32 t (off + 52)) 0)
      sweep cfg answers now mask onward (left - 1) t tx
    else if unacked == sent || tries ≥ cfg.tries then
      -- Nothing was owed and nothing came, or what was owed was sent again often enough: given up.
      let tx := emit cfg tx macHigh macLow rip rport 0x14 sent expected false ByteArray.empty 0 0
      sweep cfg answers now mask i (left - 1) (bump (bump (forget cfg t mask off) 80) 88) tx
    else
      -- What was sent and not acknowledged is sent again, one segment of it, the wait doubled, and this
      -- end's own window shut to one segment, to open fast again only as far as half of what it was.
      -- Nothing is timed any more: an acknowledgement now could be of either sending.
      let to := reach unacked unacked first size tail mss mss
      let to := if to - unacked ≤ sent - unacked then to else sent
      let tx := segmentsOf cfg answers which tx macHigh macLow rip rport expected first size mss unacked to
      let wait := waitOf cfg (ld32 t (off + 52)) (tries + 1)
      -- Sending goes on from the end of what was just sent again: the rest of what was on its way is
      -- taken for lost with it, and follows as acknowledgements open the window.
      let t := st32 (wr8 (wr8 t (off + 1) (rd8 t (off + 1) &&& 0xf3)) (off + 2) (tries + 1)) (off + 4) (now + wait)
      let own := ld32 t (off + 48)
      let t := st32 t (off + 68) (if own / 2 < 2 * mss then 2 * mss else own / 2)
      let t := st32 (st32 t (off + 16) to) (off + 48) mss
      sweep cfg answers now mask onward (left - 1) (bump t 72) tx

/-- Time passing. `elapsed` is the milliseconds since this was last called: so much of the table is looked
at that the whole is looked at every `sweepMs`. What is sent goes to `tx` after what is there. -/
def tick (cfg : @& Tuning) (answers : @& Array ByteArray) (now elapsed : UInt32) (t tx : ByteArray) : ByteArray × ByteArray :=
  let slots : USize := (1 : USize) <<< cfg.slotBits
  let share := slots.toUInt64 * elapsed.toUInt64 / (if cfg.sweepMs == 0 then 1 else cfg.sweepMs).toUInt64 + 1
  let count := if share > slots.toUInt64 then slots else share.toUSize
  sweep cfg answers now (slots - 1) ((ld64 t 64).toUSize &&& (slots - 1)) count t tx

end Kernel.Net.Flat
