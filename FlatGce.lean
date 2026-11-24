import Kernel.Efi
import Kernel.Net.Gvnic
import Kernel.Net.FlatHttp
import Kernel.Net.FlatWire
import Platform

/-! The trial TCP (`Kernel/Net/Flat.lean`) on Google's network card (`Kernel/Net/Gvnic.lean`), as a guest
on Compute Engine: the same small web server as `flat-os`, at 10.0.2.15, port 80. The machine must be
given that address (a subnet 10.0.2.0/24 and `--private-network-ip 10.0.2.15`); nothing here asks the
network what its address is. Segments are kept to 1,420 bytes, since Compute Engine's networks carry
packets of 1,460 and no more.

It says on the console what the card said of itself, or why the card could not be brought up, and then
every five seconds in which anything came how things stand. It serves nothing anyone depends on.

    scripts/build-efi tdx flat-gce && scripts/gce-image .lake/build/efi/tdx/flat-gce/BOOTX64.EFI flat-gce.tar.gz -/

open Kernel
open Kernel.Net
open Kernel.Net.Flat
open Kernel.Net.FlatWire

def say (line : String) : IO Unit := Platform.write (line ++ "\n").toUTF8

def hex (n : Nat) (digits : Nat) : String :=
  let shown := Nat.toDigits 16 n
  String.ofList (List.replicate (digits - shown.length) '0' ++ shown)

/-- A frame asking whose Ethernet address `asked` is, put in `tx` after what is there: for seeing
whether anything sent arrives anywhere and anything comes back, when nothing else says. -/
def asking (cfg : Tuning) (asked : UInt32) (tx : ByteArray) : ByteArray :=
  let at_ := written tx
  if at_.toNat + 44 > tx.size then tx else
  let tx := wr16 tx at_ 42
  let e := at_ + 2
  let tx := wr32 (wr16 tx e 0xffff) (e + 2) 0xffffffff
  let tx := wr32 (wr16 tx (e + 6) cfg.macHigh) (e + 8) cfg.macLow
  let tx := wr16 tx (e + 12) 0x0806
  let tx := wr32 (wr32 tx (e + 14) 0x00010800) (e + 18) 0x06040001
  let tx := wr32 (wr16 tx (e + 22) cfg.macHigh) (e + 24) cfg.macLow
  let tx := wr32 tx (e + 28) cfg.localIp
  let tx := wr32 (wr16 tx (e + 32) 0) (e + 34) 0
  let tx := wr32 tx (e + 38) asked
  st64 tx 0 (at_ + 44).toUInt64

partial def asleep : IO UInt32 := do
  Efi.idle
  asleep

def main : IO UInt32 := do
  say "flat-gce: begun"
  match ← Gvnic.start with
  | .error why =>
    say s!"flat-gce: the card could not be brought up: {why}"
    asleep
  | .ok (card, rings, notes) =>
    say s!"flat-gce: {notes}"
    say s!"flat-gce: card {hex card.macHigh.toNat 4}{hex card.macLow.toNat 8}, packets of {card.mtu}, {card.txSize} descriptors and {card.txSlots} places for sending, {card.rxSize} places for receiving"
    let cfg : Tuning := { slotBits := 16, localIp := 0x0a00020f, macHigh := card.macHigh, macLow := card.macLow, busy := 8192, mss := 1420 }
    let answers := Kernel.Net.FlatHttp.pages (ByteArray.mk ((Array.range 1000000).map fun i => (i % 251).toUInt8))
    let respond := Kernel.Net.FlatHttp.respond
    let mut rings := rings
    let mut scratch := Gvnic.scratchFor card
    let mut batch := Flat.zeros (card.rxSize.toNat * 1520)
    let mut t := table cfg
    let mut tx := outbox (1 <<< 22)
    let mut last ← Efi.millis
    let mut told := last
    let mut seen : UInt64 := 0
    let mut looks := 0
    say "flat-gce: serving HTTP at 10.0.2.15, port 80"
    repeat
      let mut length : USize := 0
      (rings, scratch, batch, length) ← Gvnic.receive card rings scratch batch
      let clock ← Efi.millis
      let now : UInt32 := clock.toUInt32 + ((1 : UInt32) <<< 20)
      tx := st64 tx 0 8
      if length != 0 then
        tx := neighbours cfg batch 0 length tx
        (t, tx) := loop cfg answers respond now batch 0 length t tx
      if clock != last then
        (t, tx) := tick cfg answers now (clock - last).toUInt32 t tx
        last := clock
      if clock - told ≥ 5000 && looks < 12 then tx := asking cfg 0x0a000201 tx
      (rings, scratch) ← Gvnic.transmit card rings scratch tx
      if length == 0 then Hw.pause
      if clock - told ≥ 5000 then
        told := clock
        if looks < 12 then
          -- The first minute: how the card stands, whatever has or has not come.
          looks := looks + 1
          let status ← Gvnic.reg card.registers
          let first ← Hw.load (card.rxDesc + 48) 16
          let done ← Hw.load32 card.txCount
          say s!"flat-gce: looking: status {hex status.toNat 8}, sent {rings.posted} descriptors of which the card says {hex (Gvnic.swap32 done).toNat 8} done, taken {rings.taken}, expecting {rings.expected}, the first descriptor ends {String.join ((List.range 16).map fun i => hex (first.get! i).toNat 2)}"
        if rings.frames != seen then
          seen := rings.frames
          say s!"flat-gce: {rings.frames} frames in and out, {rings.dropped} dropped at the card; accepted {ld64 t 8}, closed {ld64 t 16}, live {ld64 t 0}, dropped {ld64 t 32}, sent again {ld64 t 72} and {ld64 t 96}, timed out {ld64 t 80}, resets sent {ld64 t 88}"
    return 0
