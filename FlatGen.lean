import Kernel.Efi
import Kernel.Net.VirtioNet
import Platform

/-! Something to ask `flat-os` for pages faster than Linux can: a guest on the same driver that opens
connections to 10.0.2.15, port 80, at a set rate and keeps nothing about any of them. Each frame that comes
back says by itself what to send next: a SYN-ACK is answered with the acknowledgement and the request,
an answer that ends the stream with this end's own end, and the numbers for both are in the frame. When a
connection was begun is put into its first sequence number, which comes back in every acknowledgement,
so how long each took is known without a table.

It opens from many addresses (10.1.0.0 and up) and ports. It works through a list of rates, some seconds
at each, and says once a second on the console what it opened, what was answered whole, what was reset,
and how long the answered ones took. It is only for measuring (`scripts/flat-load`). -/

open Kernel
open Kernel.Net
open Kernel.Net.Flat

def say (line : String) : IO Unit := Platform.write (line ++ "\n").toUTF8

def target : UInt32 := 0x0a00020f
def own : UInt32 := 0x0a000263

/-- Connections a second, each tried for `secondsEach` seconds, in turn. -/
def rates : Array Nat := #[100000, 200000, 300000, 400000, 500000, 600000, 700000, 800000, 1000000, 1500000]
def secondsEach : Nat := 4

/-- The question of whose Ethernet address `target` is, written to `tx`. -/
def ask (cfg : Tuning) (tx : ByteArray) : ByteArray :=
  let at_ := written tx
  let e := at_ + 2
  let tx := wr16 tx at_ 60
  let tx := wr32 (wr16 tx e 0xffff) (e + 2) 0xffffffff
  let tx := wr32 (wr16 tx (e + 6) cfg.macHigh) (e + 8) cfg.macLow
  let tx := wr16 tx (e + 12) 0x0806
  let tx := wr32 (wr32 tx (e + 14) 0x00010800) (e + 18) 0x06040001
  let tx := wr32 (wr16 tx (e + 22) cfg.macHigh) (e + 24) cfg.macLow
  let tx := wr32 tx (e + 28) own
  let tx := wr32 (wr16 tx (e + 32) 0) (e + 34) 0
  let tx := wr32 tx (e + 38) target
  let tx := wr32 (wr32 (wr32 (wr32 (wr16 tx (e + 42) 0) (e + 44) 0) (e + 48) 0) (e + 52) 0) (e + 56) 0
  st64 tx 0 (at_ + 62).toUInt64

/-- The Ethernet address in an answer to that question among the frames of `rx`, as one number, or 0. -/
partial def answered (rx : @& ByteArray) (o stop : USize) : UInt64 :=
  if o + 2 > stop then 0 else
  let n := (rd16 rx o).toUSize
  let f := o + 2
  if f + n > stop then 0 else
  if n ≥ 42 && rd16 rx (f + 12) == 0x0806 && rd16 rx (f + 20) == 2 && rd32 rx (f + 28) == target then
    ((rd16 rx (f + 22)).toUInt64 <<< 32) ||| (rd32 rx (f + 24)).toUInt64
  else answered rx (f + n) stop

/-- Every frame of `rx` answered as it asks to be. `stats` counts, eight bytes each: 0 answers that ended
the stream, 8 resets, 16 SYN-ACKs, and from 64 on how many of the ended ones took under 1, 2, 4, …
milliseconds. `now` is this machine's milliseconds. -/
partial def reflect (cfg : @& Tuning) (macHigh : UInt16) (macLow : UInt32) (request : @& ByteArray) (each now : UInt32)
    (rx : @& ByteArray) (o stop : USize) (tx stats : ByteArray) : ByteArray × ByteArray :=
  if o + 2 > stop then (tx, stats) else
  let n := (rd16 rx o).toUSize
  let f := o + 2
  let next := f + n
  if next > stop then (tx, stats) else
  if n < 54 || rd16 rx (f + 12) != 0x0800 || rd8 rx (f + 14) != 0x45 || rd8 rx (f + 23) != 6 || rd32 rx (f + 26) != target then
    reflect cfg macHigh macLow request each now rx next stop tx stats
  else
  let header := ((rd8 rx (f + 46)) >>> 4).toUSize <<< 2
  let length := ((rd16 rx (f + 16)).toUSize - 20 - header).toUInt32
  let seq := rd32 rx (f + 38)
  let acked := rd32 rx (f + 42)
  let flags := rd8 rx (f + 47)
  -- This end of the connection is whoever the frame is addressed to.
  let from_ : Tuning := { cfg with localIp := rd32 rx (f + 30), localPort := rd16 rx (f + 36) }
  if flags &&& 0x04 != 0 then reflect cfg macHigh macLow request each now rx next stop tx (bump stats 8)
  else if flags == 0x12 then
    let tx := emit from_ tx macHigh macLow target 80 0x10 acked (seq + 1) false request 0 0
    let tx := emit from_ tx macHigh macLow target 80 0x18 acked (seq + 1) false request 0 request.usize
    reflect cfg macHigh macLow request each now rx next stop tx (bump stats 16)
  else if each > 1 && flags &&& 0x01 != 0 then
    -- On a connection kept open this end closed first, and this is the server's closing after it.
    reflect cfg macHigh macLow request each now rx next stop
      (emit from_ tx macHigh macLow target 80 0x10 acked (seq + length + 1) false request 0 0) stats
  else if each > 1 && length != 0 && flags &&& 0x08 != 0 then
    -- An answer on a connection kept open. How many requests the server has had is in what it
    -- acknowledges, since the number this end began with has nothing in its twelve lowest bits: the next
    -- request goes with the acknowledgement, or after the last of them this end's closing.
    let had := ((acked - 1) &&& 0xfff) / request.size.toUInt32
    let tx := if had < each then emit from_ tx macHigh macLow target 80 0x18 acked (seq + length) false request 0 request.usize
      else emit from_ tx macHigh macLow target 80 0x11 acked (seq + length) false request 0 0
    reflect cfg macHigh macLow request each now rx next stop tx (bump stats 0)
  else if flags &&& 0x01 != 0 then
    let tx := emit from_ tx macHigh macLow target 80 0x11 acked (seq + length + 1) false request 0 0
    -- When it began is in the number it began with, which is what is acknowledged less the request.
    let began := (acked - 1 - request.size.toUInt32) >>> 12
    let took := (now - began) &&& 0xfffff
    let bucket : USize := if took < 1 then 0 else if took < 2 then 1 else if took < 4 then 2 else if took < 8 then 3
      else if took < 16 then 4 else if took < 32 then 5 else if took < 64 then 6 else if took < 128 then 7
      else if took < 256 then 8 else if took < 512 then 9 else if took < 1024 then 10 else 11
    reflect cfg macHigh macLow request each now rx next stop tx (bump (bump stats 0) (64 + bucket * 8))
  else if length != 0 then
    reflect cfg macHigh macLow request each now rx next stop
      (emit from_ tx macHigh macLow target 80 0x10 acked (seq + length) false request 0 0) stats
  else reflect cfg macHigh macLow request each now rx next stop tx stats

/-- `count` connections begun, each from the next address and port in turn. -/
partial def open_ (cfg : @& Tuning) (macHigh : UInt16) (macLow : UInt32) (now : UInt32) (serial count : Nat) (tx : ByteArray) : ByteArray :=
  if count == 0 then tx else
  let from_ : Tuning := { cfg with localIp := 0x0a010000 + (serial % 65536).toUInt32, localPort := (1024 + serial / 65536 % 60000).toUInt16 }
  let first : UInt32 := now <<< 12
  open_ cfg macHigh macLow now (serial + 1) (count - 1) (emit from_ tx macHigh macLow target 80 0x02 first 0 true ByteArray.empty 0 0)

def main : IO UInt32 := do
  let some (card, rings) ← VirtioNet.start 1024 | do say "flat-gen: no network card that will do"; return 1
  let cfg : Tuning := { localIp := own, macHigh := card.macHigh, macLow := card.macLow }
  -- How many requests a connection makes is said by whoever starts this guest, in the fourth byte of
  -- the card's Ethernet address: nothing there, or 1, is one request and then the end, as it always was.
  let each : UInt32 := let said := (card.macLow >>> 16) &&& 0xff; if said < 2 then 1 else if said > 100 then 100 else said
  let request := (if each > 1 then "GET / HTTP/1.1\r\nHost: 10.0.2.15\r\n\r\n" else "GET / HTTP/1.1\r\nHost: 10.0.2.15\r\nConnection: close\r\n\r\n").toUTF8
  let mut rings := rings
  let mut scratch := VirtioNet.scratchFor card
  let mut batch := Flat.zeros (card.size.toNat * 1520)
  let mut tx := outbox (1 <<< 22)
  let mut stats := Flat.zeros 256
  -- Whose Ethernet address the server's is: asked until it is said.
  let mut mac : UInt64 := 0
  let mut asked : UInt64 := 0
  say "flat-gen: looking for 10.0.2.15"
  while mac == 0 do
    let mut length : USize := 0
    (rings, scratch, batch, length) ← VirtioNet.receive card rings scratch batch
    mac := answered batch 0 length
    let clock ← Efi.millis
    if mac == 0 && clock ≥ asked + 200 then
      asked := clock
      tx := ask cfg (st64 tx 0 8)
      (rings, scratch) ← VirtioNet.transmit card rings scratch tx
  let macHigh := (mac >>> 32).toUInt16
  let macLow := mac.toUInt32
  say s!"flat-gen: found it; {rates.size} rates, {secondsEach} seconds each"
  -- How many of the processor's ticks make a second, by the firmware's clock over a twentieth of one:
  -- connections are opened by the tick, a few a turn, and not a millisecond's worth at once.
  let edge ← Efi.millis
  let mut clock0 ← Efi.millis
  while clock0 == edge do clock0 ← Efi.millis
  let ticks0 ← Hw.ticks
  let mut clock1 ← Efi.millis
  while clock1 < clock0 + 50 do clock1 ← Efi.millis
  let perSecond : UInt64 := ((← Hw.ticks) - ticks0) * 20
  let mut tick ← Hw.ticks
  let mut credit : UInt64 := 0
  let began ← Efi.millis
  let mut second := began
  let mut serial := 0
  let mut opened := 0
  let mut step := 0
  let mut turns := 0
  let mut idle := 0
  let mut waited : UInt64 := 0
  -- What there is to say each second is kept and said at the end: writing a line takes about a
  -- millisecond here, and the connections that millisecond owed would all be opened at once after it.
  let mut notes : Array String := #[]
  repeat
    let mut length : USize := 0
    (rings, scratch, batch, length) ← VirtioNet.receive card rings scratch batch
    let clock ← Efi.millis
    let now := clock.toUInt32
    tx := st64 tx 0 8
    if length != 0 then (tx, stats) := reflect cfg macHigh macLow request each now batch 0 length tx stats
    -- What the time since the last turn owes at the rate set, and whatever earlier turns could not be
    -- given room for, up to a fiftieth of a second's worth.
    -- With several requests a connection the rates are of requests, three times those listed.
    let wanted := if each > 1 then rates[step]! * 3 else rates[step]!
    let rate := (wanted / each.toNat).toUInt64
    let present ← Hw.ticks
    credit := credit + rate * (present - tick)
    tick := present
    let count := (min (credit / perSecond) 256).toNat
    credit := credit - count.toUInt64 * perSecond
    if credit > rate * (perSecond / 50) then credit := rate * (perSecond / 50)
    if count != 0 then
      tx := open_ cfg macHigh macLow now serial count tx
      serial := serial + count
      opened := opened + count
    (rings, scratch) ← VirtioNet.transmit card rings scratch tx
    turns := turns + 1
    if length == 0 then idle := idle + 1
    if clock ≥ second + 1000 then
      let times := (List.range 12).map fun b => toString (ld64 stats (64 + b.toUSize * 8))
      notes := notes.push s!"flat-gen: rate {wanted}: opened {opened * each.toNat}, answered {ld64 stats 0}, reset {ld64 stats 8}, not taken by the card {rings.dropped}, {turns} turns of which {idle} with nothing, {rings.waits - waited} waits for the card; under 1 2 4 8 16 32 64 128 256 512 1024 ms and over: {" ".intercalate times}"
      stats := Flat.zeros 256
      turns := 0
      idle := 0
      waited := rings.waits
      opened := 0
      second := clock
      if (clock - began) / 1000 ≥ ((step + 1) * secondsEach).toUInt64 then
        step := step + 1
        if step ≥ rates.size then
          for note in notes do say note
          say "flat-gen: done"
          break
  return 0
