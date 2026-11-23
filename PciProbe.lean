import Kernel.Hw
import Platform

/-! Looks at the PCI devices the firmware offers on the EFI target and says what it finds, on the console:
every device by its numbers; the virtio network card's capabilities, read from its configuration; then,
having claimed that card from the firmware's drivers, its windows, what it offers and how many queues it
has, its Ethernet address, and whether a page of the memory shared with it holds what is put there.

It shows that `Kernel/Hw.lean` works on this target, in an emulator and in a trust domain, before a driver
depends on it. Never in an image that serves anything.

    scripts/build-efi dev pci-probe && scripts/run-efi dev pci-probe -/

open Kernel

def say (line : String) : IO Unit := Platform.write (line ++ "\n").toUTF8

def hex (n : Nat) (digits : Nat := 4) : String :=
  let shown := Nat.toDigits 16 n
  String.ofList (List.replicate (digits - shown.length) '0' ++ shown)

def main : IO UInt32 := do
  let count ← Hw.devices
  say s!"pci-probe: {count} PCI devices"
  let mut card : Option USize := none
  for i in [0:count.toNat] do
    let id ← Hw.config i.toUSize 0 4
    let kind ← Hw.config i.toUSize 8 4
    say s!"  {i}: vendor {hex (id &&& 0xffff).toNat} device {hex (id >>> 16).toNat} class {hex (kind >>> 8).toNat 6} revision {kind &&& 0xff}"
    if id == 0x10411af4 then card := some i.toUSize
  let some index := card | do say "pci-probe: no virtio network card (1af4:1041)"; return 1
  -- Its capabilities: a chain through its configuration, each saying where in which window a part of
  -- the device is.
  let mut at_ := (← Hw.config index 0x34 1) &&& 0xfc
  let mut common : UInt64 := 0
  let mut config : UInt64 := 0
  for _ in [0:48] do
    if at_ == 0 then break
    let kind ← Hw.config index at_ 1
    let next ← Hw.config index (at_ + 1) 1
    if kind == 9 then
      let part ← Hw.config index (at_ + 3) 1
      let window ← Hw.config index (at_ + 4) 1
      let offset ← Hw.config index (at_ + 8) 4
      let length ← Hw.config index (at_ + 12) 4
      let extra ← if part == 2 then Hw.config index (at_ + 16) 4 else pure 0
      say s!"  capability at {hex at_.toNat 2}: part {part} in window {window} at {hex offset.toNat 6}, {length} bytes{if part == 2 then s!", notify multiplier {extra}" else ""}"
      let address := ((window.toUInt64 + 1) <<< 32) ||| offset.toUInt64
      if part == 1 then common := address
      if part == 4 then config := address
    at_ := next &&& 0xfc
  if !(← Hw.claim index) then say "pci-probe: the card could not be claimed"; return 1
  say "pci-probe: claimed"
  for w in (← Hw.windows) do
    if w.size != 0 then say s!"  window at {hex w.base.toNat 12}: {w.size} bytes"
  if common == 0 || config == 0 then say "pci-probe: the card has no modern virtio parts"; return 1
  -- Reset, then what it offers, low half and high.
  Hw.write (common + 20) 1 0
  Hw.write common 4 0
  let low ← Hw.read (common + 4) 4
  Hw.write common 4 1
  let high ← Hw.read (common + 4) 4
  let queues ← Hw.read (common + 18) 2
  Hw.write (common + 22) 2 0
  let size ← Hw.read (common + 24) 2
  say s!"  offers {hex high.toNat 8}{hex low.toNat 8}, {queues} queues, the first of {size} entries"
  let mut mac := ""
  for i in [0:6] do
    mac := mac ++ (if i == 0 then "" else ":") ++ hex (← Hw.read (config + i.toUInt64) 1).toNat 2
  say s!"  Ethernet address {mac}"
  -- The shared memory: a page, written, read back, and read back into an array that was there.
  let page ← Hw.alloc 4096
  if page == 0 then say "pci-probe: no shared memory"; return 1
  let pattern := ByteArray.mk ((Array.range 64).map fun i => (i * 7 + 1).toUInt8)
  Hw.store (page + 100) pattern
  let back ← Hw.load (page + 100) 64
  -- An array made here and now, so that it has one owner: one written out in the program is shared.
  let into ← Hw.loadInto (page + 100) (ByteArray.mk (Array.replicate (64 + back.size) 0)) 32 64
  say s!"  shared memory at {hex page.toNat 12}: {if back == pattern && into.extract 32 96 == pattern && into.extract 0 32 == ByteArray.mk (Array.replicate 32 0) then "holds what is put there" else "DOES NOT hold what is put there"}"
  say "pci-probe: done"
  return 0
