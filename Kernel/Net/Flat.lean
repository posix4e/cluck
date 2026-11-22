/-! A TCP for many short connections, as a trial of how fast one written in Lean can be. It is not the
system's TCP (`Kernel/Net/Tcp.lean`), is used by nothing, and does a part of what a TCP must.

What is different from the system's, and why each thing is so:

* **Frames come and go in batches**, many to an array, each with its length in two bytes before it. A
  network card hands over dozens at a time, and a call a frame is what a fast stack cannot afford.
* **Nothing is allocated for a frame.** A frame is read where it lies; an answer is written into an array
  that was there before, at a place kept in that array's first eight bytes; a connection is 64 bytes in
  one flat table, found by a keyed hash of its addresses and changed in place. Lean changes an array in
  place when nothing else holds it, and everything here is written to keep it so.
* **A connection costs nothing until it is real.** The answer to a SYN is worked out from a keyed hash of
  the addresses and a clock (a SYN cookie), and nothing is kept; the table gets an entry only when the
  third packet of the handshake comes back with that number in it.
* **What can be tuned is in one place**, `Tuning`.

What it does not do, and a TCP must: retransmit (there are no timers at all), reassemble segments that
come out of order (it asks again for the next byte), mind the peer's window or its MSS, negotiate any
option but its own MSS, wait out a connection it closed first, IPv6, or IP options. The application is
one fixed thing, for measuring: when `request` bytes have come it sends `answer` and closes.

Laid out:

    table   64 bytes of counters, then 2^slotBits entries of 64 bytes
            counters, eight bytes each: live, accepted, closed, SYNs, dropped, out of order, reset, full
    entry   0 state (0 free, 1 open, 2 closing)   1 flags (1: the peer has closed)
            8 the key: remote address, remote port, local port
            16 next to send   20 oldest unacknowledged   24 next expected   28 last heard   32 bytes got
    out     eight bytes saying where the next frame goes, then frames -/

namespace Kernel.Net.Flat

structure Tuning where
  /-- The table has two to this many entries, and takes new connections until half are in use. -/
  slotBits : USize := 20
  localIp : UInt32 := 0x0a000002
  localPort : UInt16 := 80
  /-- The largest segment this end says it will take. -/
  mss : UInt16 := 1460
  /-- The window this end advertises. -/
  window : UInt16 := 65535
  /-- Whether checksums are checked coming in and made going out. A card that does both can be told to,
  and then this is false. -/
  checksums : Bool := true
  /-- How many bytes the application waits for before it answers. -/
  request : UInt32 := 1
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

/-- The sum the Internet checksum is made of, over the bytes from `i` to `stop`, two at a time. -/
partial def sum16 (a : @& ByteArray) (i stop : USize) (acc : UInt64) : UInt64 :=
  if i + 1 < stop then sum16 a (i + 2) stop (acc + (rd16 a i).toUInt64)
  else if i < stop then acc + ((rd8 a i).toUInt64 <<< 8)
  else acc

@[inline] def fold (s : UInt64) : UInt16 :=
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
def table (cfg : Tuning) : ByteArray := zeros (64 + (1 <<< cfg.slotBits.toNat) * 64)

def outbox (bytes : Nat) : ByteArray := st64 (zeros (8 + bytes)) 0 8

/-- How far the frames written reach. -/
@[inline] def written (tx : @& ByteArray) : USize := (ld64 tx 0).toUSize

@[inline] def bump (t : ByteArray) (counter : USize) : ByteArray := st64 t counter (ld64 t counter + 1)

@[inline] def keyOf (rip : UInt32) (rport lport : UInt16) : UInt64 :=
  (rip.toUInt64 <<< 32) ||| (rport.toUInt64 <<< 16) ||| lport.toUInt64

@[inline] def home (cfg : @& Tuning) (k : UInt64) : USize :=
  (sip cfg.key0 cfg.key1 k 0).toUSize &&& (((1 : USize) <<< cfg.slotBits) - 1)

/-- The number that answers a SYN: nothing is kept, and the same number is worked out again when the
third packet comes. `tick` moves on every minute or so, and the one before is still taken. -/
@[inline] def cookie (cfg : @& Tuning) (k : UInt64) (theirs tick : UInt32) : UInt32 :=
  (sip cfg.key1 cfg.key0 k ((theirs.toUInt64 <<< 32) ||| tick.toUInt64)).toUInt32

/-- Where the entry at place `i` begins in the table. -/
@[inline] def place (i : USize) : USize := (i <<< 6) + 64

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
      remove cfg t mask j ((j + 1) &&& mask)

/-- A frame written in answer to the one at `f` in `rx`: to where that one came from, with these flags
and numbers and this much of `payload`. Nothing is written when there is no room. -/
def emit (cfg : @& Tuning) (rx : @& ByteArray) (f : USize) (tx : ByteArray) (flags : UInt8) (seq ack : UInt32)
    (mssOption : Bool) (payload : @& ByteArray) : ByteArray :=
  let at_ := written tx
  let options : USize := if mssOption then 4 else 0
  let segment := 20 + options + payload.usize
  let total := 34 + segment
  if at_.toNat + 2 + total.toNat > tx.size then tx else
  let tx := wr16 tx at_ total.toUInt16
  let e := at_ + 2
  -- Ethernet: back to the sender.
  let tx := wr16 tx e (rd16 rx (f + 6))
  let tx := wr32 tx (e + 2) (rd32 rx (f + 8))
  let tx := wr16 tx (e + 6) (rd16 rx f)
  let tx := wr32 tx (e + 8) (rd32 rx (f + 2))
  let tx := wr16 tx (e + 12) 0x0800
  -- IP.
  let ip := e + 14
  let tx := wr16 tx ip 0x4500
  let tx := wr16 tx (ip + 2) (20 + segment).toUInt16
  let tx := wr32 tx (ip + 4) 0x00004000
  let tx := wr16 tx (ip + 8) 0x4006
  let tx := wr16 tx (ip + 10) 0
  let tx := wr32 tx (ip + 12) cfg.localIp
  let tx := wr32 tx (ip + 16) (rd32 rx (f + 26))
  -- TCP.
  let t := ip + 20
  let tx := wr16 tx t (rd16 rx (f + 36))
  let tx := wr16 tx (t + 2) (rd16 rx (f + 34))
  let tx := wr32 tx (t + 4) seq
  let tx := wr32 tx (t + 8) ack
  let tx := wr8 tx (t + 12) (if mssOption then 0x60 else 0x50)
  let tx := wr8 tx (t + 13) flags
  let tx := wr16 tx (t + 14) cfg.window
  let tx := wr32 tx (t + 16) 0
  let tx := if mssOption then wr16 (wr16 tx (t + 20) 0x0204) (t + 22) cfg.mss else tx
  let tx := if payload.isEmpty then tx else payload.copySlice 0 tx (t + 20 + options).toNat payload.size
  let tx :=
    if cfg.checksums then
      let tx := wr16 tx (ip + 10) (fold (sum16 tx ip (ip + 20) 0))
      let pseudo := (sum16 tx (ip + 12) (ip + 20) 0) + 6 + segment.toUInt64
      wr16 tx (t + 16) (fold (sum16 tx t (t + segment) pseudo))
    else tx
  st64 tx 0 (at_ + 2 + total).toUInt64

/-- Every frame of `rx` from `o` to `stop` taken in turn. -/
partial def loop (cfg : @& Tuning) (answer : @& ByteArray) (now : UInt32) (rx : @& ByteArray) (o stop : USize)
    (t tx : ByteArray) : ByteArray × ByteArray :=
  if o + 2 > stop then (t, tx) else
  let n := (rd16 rx o).toUSize
  let f := o + 2
  let next := f + n
  if next > stop then (t, tx) else
  -- Ethernet carrying IPv4 with no options carrying TCP, for this address and port; all else is dropped.
  if n < 54 || rd16 rx (f + 12) != 0x0800 || rd8 rx (f + 14) != 0x45 || rd8 rx (f + 23) != 6 ||
      rd32 rx (f + 30) != cfg.localIp || rd16 rx (f + 36) != cfg.localPort then
    loop cfg answer now rx next stop (bump t 32) tx
  else
  let ipLength := (rd16 rx (f + 16)).toUSize
  let header := ((rd8 rx (f + 46)) >>> 4).toUSize <<< 2
  if header < 20 || ipLength < 20 + header || 14 + ipLength > n then loop cfg answer now rx next stop (bump t 32) tx
  else
  let sound := !cfg.checksums ||
    (fold (sum16 rx (f + 14) (f + 34) 0) == 0 &&
     fold (sum16 rx (f + 34) (f + 14 + ipLength) (sum16 rx (f + 26) (f + 34) 0 + 6 + (ipLength - 20).toUInt64)) == 0)
  if !sound then loop cfg answer now rx next stop (bump t 32) tx
  else
  let rip := rd32 rx (f + 26)
  let seq := rd32 rx (f + 38)
  let acked := rd32 rx (f + 42)
  let flags := rd8 rx (f + 47)
  let length := (ipLength - 20 - header).toUInt32
  let k := keyOf rip (rd16 rx (f + 34)) cfg.localPort
  let mask : USize := ((1 : USize) <<< cfg.slotBits) - 1
  if flags &&& 0x02 != 0 then
    -- A SYN is answered from the cookie and nothing is kept. (One for a connection that is open is too:
    -- its answer will not fit that connection and the peer will see so.)
    if flags &&& 0x10 != 0 then loop cfg answer now rx next stop (bump t 32) tx
    else loop cfg answer now rx next stop (bump t 24) (emit cfg rx f tx 0x12 (cookie cfg k seq (now >>> 16)) (seq + 1) true .empty)
  else
  let h := home cfg k
  let known := find t mask k h
  if flags &&& 0x04 != 0 then
    -- A reset is believed when it is exactly where the stream has got to.
    if known != 0 && seq == ld32 t (known + 24) then
      let t := remove cfg t mask ((known - 64) >>> 6) ((((known - 64) >>> 6) + 1) &&& mask)
      loop cfg answer now rx next stop (bump (st64 t 0 (ld64 t 0 - 1)) 48) tx
    else loop cfg answer now rx next stop t tx
  else if flags &&& 0x10 == 0 then loop cfg answer now rx next stop (bump t 32) tx
  else
  -- The third packet of a handshake makes the entry, if its number is the cookie's and there is room.
  let tick := now >>> 16
  let fresh := known == 0 && (acked - 1 == cookie cfg k (seq - 1) tick || acked - 1 == cookie cfg k (seq - 1) (tick - 1))
  let room := ld64 t 0 < ((1 : USize) <<< (cfg.slotBits - 1)).toUInt64
  if known == 0 && !fresh then loop cfg answer now rx next stop (bump t 32) tx
  else if known == 0 && !room then loop cfg answer now rx next stop (bump t 56) tx
  else
  let off := if known != 0 then known else vacant t mask h
  let t :=
    if known != 0 then t
    else
      let t := st64 t off 1
      let t := st64 t (off + 8) k
      let t := st32 (st32 t (off + 16) acked) (off + 20) acked
      let t := st64 (st32 t (off + 24) seq) (off + 28) 0
      bump (bump t 0) 8
  let state := rd8 t off
  let sent := ld32 t (off + 16)
  let unacked := ld32 t (off + 20)
  let expected := ld32 t (off + 24)
  -- An acknowledgement counts when it is of something sent and not yet acknowledged.
  let unacked := if acked - unacked ≤ sent - unacked then acked else unacked
  let fin := flags &&& 0x01 != 0
  if seq != expected then
    -- Not the next byte of the stream: kept is nothing, and the peer is told which byte is wanted.
    let t := st32 t (off + 20) unacked
    if length == 0 && !fin then loop cfg answer now rx next stop t tx
    else loop cfg answer now rx next stop (bump t 40) (emit cfg rx f tx 0x10 sent expected false .empty)
  else
  let got := ld32 t (off + 32) + length
  let expected := expected + length + (if fin then 1 else 0)
  let peerClosed := fin || rd8 t (off + 1) &&& 1 != 0
  -- The application: once the request is in, the answer and the end of the stream together; and if the
  -- peer ends first, the end.
  let answers := state == 1 && length != 0 && got ≥ cfg.request
  let ends := state == 1 && !answers && fin
  let tx :=
    if answers then emit cfg rx f tx 0x19 sent expected false answer
    else if ends then emit cfg rx f tx 0x11 sent expected false .empty
    else if length != 0 || fin then emit cfg rx f tx 0x10 sent expected false .empty
    else tx
  let sent := if answers then sent + answer.size.toUInt32 + 1 else if ends then sent + 1 else sent
  let state : UInt8 := if answers || ends then 2 else state
  if state == 2 && unacked == sent && peerClosed then
    -- Both ends have closed and ours is acknowledged: the entry goes.
    let i := (off - 64) >>> 6
    let t := remove cfg t mask i ((i + 1) &&& mask)
    loop cfg answer now rx next stop (bump (st64 t 0 (ld64 t 0 - 1)) 16) tx
  else
    let t := wr8 (wr8 t off state) (off + 1) (if peerClosed then 1 else 0)
    let t := st32 (st32 t (off + 16) sent) (off + 20) unacked
    let t := st32 (st32 (st32 t (off + 24) expected) (off + 28) now) (off + 32) got
    loop cfg answer now rx next stop t tx

/-- The frames in the first `length` bytes of `rx` taken in, the table changed, and the answers written
to `tx` from its start. -/
def process (cfg : @& Tuning) (answer : @& ByteArray) (now : UInt32) (rx : @& ByteArray) (length : USize)
    (t tx : ByteArray) : ByteArray × ByteArray :=
  loop cfg answer now rx 0 length t (st64 tx 0 8)

end Kernel.Net.Flat
