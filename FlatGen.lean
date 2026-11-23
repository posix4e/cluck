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
def rates : Array Nat := #[50000, 100000, 200000, 300000, 400000, 500000, 600000, 800000, 1000000, 1500000]
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
partial def reflect (cfg : @& Tuning) (macHigh : UInt16) (macLow : UInt32) (request : @& ByteArray) (now : UInt32)
    (rx : @& ByteArray) (o stop : USize) (tx stats : ByteArray) : ByteArray × ByteArray :=
  if o + 2 > stop then (tx, stats) else
  let n := (rd16 rx o).toUSize
  let f := o + 2
  let next := f + n
  if next > stop then (tx, stats) else
  if n < 54 || rd16 rx (f + 12) != 0x0800 || rd8 rx (f + 14) != 0x45 || rd8 rx (f + 23) != 6 || rd32 rx (f + 26) != target then
    reflect cfg macHigh macLow request now rx next stop tx stats
  else
  let header := ((rd8 rx (f + 46)) >>> 4).toUSize <<< 2
  let length := ((rd16 rx (f + 16)).toUSize - 20 - header).toUInt32
  let seq := rd32 rx (f + 38)
  let acked := rd32 rx (f + 42)
  let flags := rd8 rx (f + 47)
  -- This end of the connection is whoever the frame is addressed to.
  let from_ : Tuning := { cfg with localIp := rd32 rx (f + 30), localPort := rd16 rx (f + 36) }
  if flags &&& 0x04 != 0 then reflect cfg macHigh macLow request now rx next stop tx (bump stats 8)
  else if flags == 0x12 then
    let tx := emit from_ tx macHigh macLow target 80 0x10 acked (seq + 1) false request 0 0
    let tx := emit from_ tx macHigh macLow target 80 0x18 acked (seq + 1) false request 0 request.usize
    reflect cfg macHigh macLow request now rx next stop tx (bump stats 16)
  else if flags &&& 0x01 != 0 then
    let tx := emit from_ tx macHigh macLow target 80 0x11 acked (seq + length + 1) false request 0 0
    -- When it began is in the number it began with, which is what is acknowledged less the request.
    let began := (acked - 1 - request.size.toUInt32) >>> 10
    let took := (now - began) &&& 0x3fffff
    let bucket : USize := if took < 1 then 0 else if took < 2 then 1 else if took < 4 then 2 else if took < 8 then 3
      else if took < 16 then 4 else if took < 32 then 5 else if took < 64 then 6 else if took < 128 then 7
      else if took < 256 then 8 else if took < 512 then 9 else if took < 1024 then 10 else 11
    reflect cfg macHigh macLow request now rx next stop tx (bump (bump stats 0) (64 + bucket * 8))
  else if length != 0 then
    reflect cfg macHigh macLow request now rx next stop
      (emit from_ tx macHigh macLow target 80 0x10 acked (seq + length) false request 0 0) stats
  else reflect cfg macHigh macLow request now rx next stop tx stats

/-- `count` connections begun, each from the next address and port in turn. -/
partial def open_ (cfg : @& Tuning) (macHigh : UInt16) (macLow : UInt32) (now : UInt32) (serial count : Nat) (tx : ByteArray) : ByteArray :=
  if count == 0 then tx else
  let from_ : Tuning := { cfg with localIp := 0x0a010000 + (serial % 65536).toUInt32, localPort := (1024 + serial / 65536 % 60000).toUInt16 }
  let first : UInt32 := (now <<< 10) ||| (serial % 1024).toUInt32
  open_ cfg macHigh macLow now (serial + 1) (count - 1) (emit from_ tx macHigh macLow target 80 0x02 first 0 true ByteArray.empty 0 0)

def main : IO UInt32 := do
  let some (card, rings) ← VirtioNet.start | do say "flat-gen: no network card that will do"; return 1
  let cfg : Tuning := { localIp := own, macHigh := card.macHigh, macLow := card.macLow }
  let request := "GET / HTTP/1.1\r\nHost: 10.0.2.15\r\n\r\n".toUTF8
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
  let began ← Efi.millis
  let mut last := began
  let mut second := began
  let mut serial := 0
  let mut owed := 0
  let mut opened := 0
  let mut step := 0
  repeat
    let mut length : USize := 0
    (rings, scratch, batch, length) ← VirtioNet.receive card rings scratch batch
    let clock ← Efi.millis
    let now := clock.toUInt32
    tx := st64 tx 0 8
    if length != 0 then (tx, stats) := reflect cfg macHigh macLow request now batch 0 length tx stats
    if clock != last then
      -- What this millisecond owes at the rate set, and whatever earlier ones could not be given room for.
      let rate := rates[step]!
      owed := owed + rate * (clock - last).toNat
      let count := min (owed / 1000) 3000
      owed := owed - count * 1000
      if owed > rate * 20 then owed := rate * 20
      tx := open_ cfg macHigh macLow now serial count tx
      serial := serial + count
      opened := opened + count
      last := clock
    (rings, scratch) ← VirtioNet.transmit card rings scratch tx
    if clock ≥ second + 1000 then
      let times := (List.range 12).map fun b => toString (ld64 stats (64 + b.toUSize * 8))
      say s!"flat-gen: rate {rates[step]!}: opened {opened}, answered {ld64 stats 0}, reset {ld64 stats 8}, not taken by the card {rings.dropped}; under 1 2 4 8 16 32 64 128 256 512 1024 ms and over: {" ".intercalate times}"
      stats := Flat.zeros 256
      opened := 0
      second := clock
      if (clock - began) / 1000 ≥ ((step + 1) * secondsEach).toUInt64 then
        step := step + 1
        if step ≥ rates.size then
          say "flat-gen: done"
          break
  return 0
