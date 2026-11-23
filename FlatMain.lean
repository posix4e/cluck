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

def main : IO UInt32 := do
  let some (card, rings) ← VirtioNet.start | do say "flat-os: no network card that will do"; return 1
  let cfg : Tuning := { slotBits := 16, localIp := 0x0a00020f, macHigh := card.macHigh, macLow := card.macLow }
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
  say s!"flat-os: a card of {card.size} buffers each way; serving HTTP at 10.0.2.15, port 80"
  repeat
    let mut length : USize := 0
    (rings, scratch, batch, length) ← VirtioNet.receive card rings scratch batch
    let clock ← Efi.millis
    let now : UInt32 := clock.toUInt32 + ((1 : UInt32) <<< 20)
    tx := st64 tx 0 8
    if length != 0 then
      tx := neighbours cfg batch 0 length tx
      (t, tx) := loop cfg answers respond now batch 0 length t tx
    if clock != last then
      (t, tx) := tick cfg answers now (clock - last).toUInt32 t tx
      last := clock
    (rings, scratch) ← VirtioNet.transmit card rings scratch tx
    if length == 0 then Hw.pause
    -- Every five seconds in which anything was accepted, how things stand, for whoever reads the console.
    if clock - told ≥ 5000 then
      told := clock
      if ld64 t 8 != seen then
        seen := ld64 t 8
        say s!"flat-os: accepted {ld64 t 8}, closed {ld64 t 16}, live {ld64 t 0}, dropped {ld64 t 32}, out of order {ld64 t 40}, sent again {ld64 t 72} and {ld64 t 96}, timed out {ld64 t 80}, resets sent {ld64 t 88}, held back {ld64 t 104}, frames the card would not take {rings.dropped}"
  return 0
