import Kernel.Efi
import Kernel.Net.VirtioNet
import Platform

/-! The trial TCP (`Kernel/Net/Flat.lean`) on a network card of its own (`Kernel/Net/VirtioNet.lean`), as
a guest: a small web server at 10.0.2.15, port 80. `GET /` gets a line, `GET /big` a megabyte, anything
else is not found. It is for trying and measuring the two together, in an emulator and in a trust domain
(`scripts/flat-linux-test --guest`); it serves nothing anyone depends on and is not the builder's image.

The loop: take everything the card has, hand it to the stack, hand the card everything the stack wrote,
and again, never waiting. Besides TCP it answers one thing, the question of whose Ethernet address
10.0.2.15 is (ARP), since nobody could reach it otherwise. -/

open Kernel
open Kernel.Net
open Kernel.Net.Flat

def say (line : String) : IO Unit := Platform.write (line ++ "\n").toUTF8

def page (status : String) (body : ByteArray) : ByteArray :=
  s!"HTTP/1.1 {status}\r\nContent-Type: text/plain\r\nContent-Length: {body.size}\r\nConnection: close\r\n\r\n".toUTF8 ++ body

def begins (rx : ByteArray) (at_ length : USize) (text : String) : Bool :=
  let want := text.toUTF8
  want.usize ≤ length && (List.range want.size).all fun i => rd8 rx (at_ + i.toUSize) == want[i]!

/-- For every frame of `rx` that asks whose Ethernet address `cfg.localIp` is, the answer written to `tx`
after what is there. -/
partial def neighbours (cfg : @& Tuning) (rx : @& ByteArray) (o stop : USize) (tx : ByteArray) : ByteArray :=
  if o + 2 > stop then tx else
  let n := (rd16 rx o).toUSize
  let f := o + 2
  if f + n > stop then tx else
  if n ≥ 42 && rd16 rx (f + 12) == 0x0806 && rd16 rx (f + 20) == 1 && rd32 rx (f + 38) == cfg.localIp then
    let at_ := written tx
    if at_.toNat + 62 > tx.size then tx else
    let e := at_ + 2
    let tx := wr16 tx at_ 60
    -- To the asker, from here; then the same question's fields turned round.
    let tx := wr32 (wr16 tx e (rd16 rx (f + 6))) (e + 2) (rd32 rx (f + 8))
    let tx := wr32 (wr16 tx (e + 6) cfg.macHigh) (e + 8) cfg.macLow
    let tx := wr16 tx (e + 12) 0x0806
    let tx := wr32 (wr32 tx (e + 14) 0x00010800) (e + 18) 0x06040002
    let tx := wr32 (wr16 tx (e + 22) cfg.macHigh) (e + 24) cfg.macLow
    let tx := wr32 tx (e + 28) cfg.localIp
    let tx := wr32 (wr16 tx (e + 32) (rd16 rx (f + 22))) (e + 34) (rd32 rx (f + 24))
    let tx := wr32 tx (e + 38) (rd32 rx (f + 28))
    -- The rest of the sixty bytes is nothing, and must be written so: the array is used again and again.
    let tx := wr32 (wr32 (wr32 (wr32 (wr16 tx (e + 42) 0) (e + 44) 0) (e + 48) 0) (e + 52) 0) (e + 56) 0
    neighbours cfg rx (f + n) stop (st64 tx 0 (at_ + 62).toUInt64)
  else neighbours cfg rx (f + n) stop tx

/-- How many of the frames in `rx` from `o` to `stop` look like SYNs: long enough, and with that flag and
not the acknowledging one where a TCP header's flags would be. Near enough for deciding whether to take
new connections; the TCP itself looks properly. -/
partial def synsIn (rx : @& ByteArray) (o stop : USize) (found : UInt64) : UInt64 :=
  if o + 2 > stop then found else
  let n := (rd16 rx o).toUSize
  synsIn rx (o + 2 + n) stop (if n ≥ 54 && rd8 rx (o + 2 + 47) &&& 0x12 == 0x02 then found + 1 else found)

def main : IO UInt32 := do
  let some (card, rings) ← VirtioNet.start 1024 | do say "flat-os: no network card that will do"; return 1
  let cfg : Tuning := { slotBits := 16, localIp := 0x0a00020f, macHigh := card.macHigh, macLow := card.macLow, busy := 8192 }
  -- The settings for when this end is falling behind because of new connections: this batch and the one
  -- before each found a quarter of the card's ring in use, and an eighth or more of this one is SYNs.
  -- Left alone the ring fills, and what does not fit is lost without regard to what it is. What can be
  -- done about it is not to begin anything new in this batch. (A ring in use alone is not it: thirty
  -- connections each being sent a megabyte fill it with acknowledgements, and those pace themselves.
  -- Nor is one such batch: after any pause there is one, and the next is small again.)
  let behind : Tuning := { cfg with busy := 1 }
  let mut pressed := false
  let pattern := ByteArray.mk ((Array.range 1000000).map fun i => (i % 251).toUInt8)
  let answers : Array ByteArray :=
    #[page "200 OK" "a TCP written in Lean\n".toUTF8, page "200 OK" pattern, page "404 Not Found" "nothing here\n".toUTF8]
  let respond (rx : ByteArray) (at_ length : USize) (_ : UInt32) : UInt64 :=
    if begins rx at_ length "GET / " then send 0 0
    else if begins rx at_ length "GET /big " then send 1 0
    else send 2 0
  let mut rings := rings
  let mut scratch := VirtioNet.scratchFor card
  let mut batch := Flat.zeros (card.size.toNat * 1520)
  let mut t := table cfg
  let mut tx := outbox (1 <<< 22)
  let mut last ← Efi.millis
  let mut told := last
  let mut seen : UInt64 := 0
  -- For whoever asks what the limit is: each second, how many times round, how many of them with nothing
  -- from the card, and how long the card was waited for.
  -- What there is to say is kept until a second goes by with no frames, and said then: writing a line
  -- takes about a millisecond here, in which a thousand frames come and some are lost.
  let mut notes : Array String := #[]
  let mut second := last
  let mut turns := 0
  let mut idle := 0
  let mut counted : UInt64 := 0
  let mut waited : UInt64 := 0
  -- And of the processor's time, how much went to taking frames from the card, to the TCP, to its
  -- timers, and to giving frames to the card; the rest is this loop.
  let mut mark ← Hw.ticks
  let mut taking : UInt64 := 0
  let mut thinking : UInt64 := 0
  let mut sweeping : UInt64 := 0
  let mut giving : UInt64 := 0
  say s!"flat-os: a card of {card.size} buffers each way; serving HTTP at 10.0.2.15, port 80"
  repeat
    let mut length : USize := 0
    let before := rings.frames
    let t0 ← Hw.ticks
    (rings, scratch, batch, length) ← VirtioNet.receive card rings scratch batch
    let t1 ← Hw.ticks
    let came := rings.frames - before
    let much := came * 4 ≥ card.size.toUInt64
    let shed := much && pressed && synsIn batch 0 length 0 * 8 ≥ came
    pressed := much
    let clock ← Efi.millis
    let now : UInt32 := clock.toUInt32 + ((1 : UInt32) <<< 20)
    tx := st64 tx 0 8
    if length != 0 then
      tx := neighbours cfg batch 0 length tx
      (t, tx) := loop (if shed then behind else cfg) answers respond now batch 0 length t tx
    let t2 ← Hw.ticks
    if clock != last then
      (t, tx) := tick cfg answers now (clock - last).toUInt32 t tx
      last := clock
    let t3 ← Hw.ticks
    (rings, scratch) ← VirtioNet.transmit card rings scratch tx
    let t4 ← Hw.ticks
    taking := taking + (t1 - t0)
    thinking := thinking + (t2 - t1)
    sweeping := sweeping + (t3 - t2)
    giving := giving + (t4 - t3)
    if length == 0 then Hw.pause
    turns := turns + 1
    if length == 0 then idle := idle + 1
    if clock - second ≥ 1000 then
      if rings.frames == counted then
        for note in notes do say note
        notes := #[]
      else
        let whole := (if t4 - mark == 0 then 1 else t4 - mark) / 1000
        notes := notes.push s!"flat-os: a second: {rings.frames - counted} frames, {turns} turns of which {idle} with nothing, {rings.waits - waited} waits for the card, SYNs let go {ld64 t 112}; of its time in thousandths: taking {taking / whole}, TCP {thinking / whole}, timers {sweeping / whole}, giving {giving / whole}"
      second := clock
      turns := 0
      idle := 0
      counted := rings.frames
      waited := rings.waits
      mark := t4
      taking := 0
      thinking := 0
      sweeping := 0
      giving := 0
    -- Every five seconds in which anything was accepted, how things stand, for whoever reads the console.
    if clock - told ≥ 5000 then
      told := clock
      if ld64 t 8 != seen then
        seen := ld64 t 8
        notes := notes.push s!"flat-os: accepted {ld64 t 8}, closed {ld64 t 16}, live {ld64 t 0}, dropped {ld64 t 32}, out of order {ld64 t 40}, sent again {ld64 t 72} and {ld64 t 96}, timed out {ld64 t 80}, resets sent {ld64 t 88}, held back {ld64 t 104}, SYNs let go {ld64 t 112}, frames the card would not take {rings.dropped}; {rings.frames} frames, the host told {rings.calls} times"
  return 0
