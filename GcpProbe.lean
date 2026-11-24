import Kernel.Efi
import Kernel.Hw
import Platform

/-! What a machine gives this target, said on the console: written to be booted once on a cloud's
trust-domain machine (Google Compute Engine's, to begin with) to learn what a driver and an image for it
must be, before either is written. It serves nothing and keeps nothing.

In order: every PCI device by its numbers; the machine's measurements from a TDREPORT (which of them
holds the firmware and which this program says how an image there is to be checked); whether the firmware
has a network driver of its own for this program to use; and, if there is one of Google's network cards
(1ae0:0042), its windows and the first words of its registers after it is claimed from the firmware.

Then it stays as it is, asleep, so that a machine that starts again whatever ends does not go round.

    scripts/build-efi tdx gcp-probe && scripts/gce-image .lake/build/efi/tdx/gcp-probe/BOOTX64.EFI probe.tar.gz -/

open Kernel

def say (line : String) : IO Unit := Platform.write (line ++ "\n").toUTF8

def hex (n : Nat) (digits : Nat := 4) : String :=
  let shown := Nat.toDigits 16 n
  String.ofList (List.replicate (digits - shown.length) '0' ++ shown)

def hexOf (bytes : ByteArray) (from_ count : Nat) : String :=
  String.join ((List.range count).map fun i => hex (bytes.get! (from_ + i)).toNat 2)

partial def asleep : IO UInt32 := do
  Efi.idle
  asleep

def main : IO UInt32 := do
  say "gcp-probe: begun"
  let count ← Hw.devices
  say s!"gcp-probe: {count} PCI devices"
  let mut card : Option USize := none
  for i in [0:count.toNat] do
    let id ← Hw.config i.toUSize 0 4
    let kind ← Hw.config i.toUSize 8 4
    let sub ← Hw.config i.toUSize 0x2c 4
    say s!"  {i}: vendor {hex (id &&& 0xffff).toNat} device {hex (id >>> 16).toNat} class {hex (kind >>> 8).toNat 6} revision {kind &&& 0xff} subsystem {hex (sub &&& 0xffff).toNat}:{hex (sub >>> 16).toNat}"
    if id == 0x00421ae0 then card := some i.toUSize
  -- The measurements. In a TDREPORT the trust domain's own are from byte 512: sixteen bytes of
  -- attributes, then MRTD, three of the owner's, and the four run-time registers, 48 bytes each.
  let report ← Efi.report (ByteArray.mk (Array.replicate 64 0))
  if report.size == 1024 then
    say s!"gcp-probe: MRTD  {hexOf report 528 48}"
    for r in [0:4] do say s!"gcp-probe: RTMR{r} {hexOf report (720 + 48 * r) 48}"
    say s!"gcp-probe: attributes {hexOf report 512 8}, XFAM {hexOf report 520 8}"
  else say s!"gcp-probe: no TDREPORT ({report.size} bytes)"
  -- The firmware's own network driver, if it has one for what is here.
  try
    let mac ← Efi.mac
    say s!"gcp-probe: the firmware has a network driver; its address is {hexOf mac 0 mac.size}"
    let mut seen := 0
    for _ in [0:2000] do
      let frame ← Efi.receive
      if !frame.isEmpty then
        seen := seen + 1
        if seen ≤ 3 then say s!"  a frame of {frame.size} bytes, beginning {hexOf frame 0 (min 24 frame.size)}"
      else Efi.idle
    say s!"gcp-probe: {seen} frames came by it in two seconds"
  catch _ => say "gcp-probe: the firmware has no network driver for this machine (or it failed)"
  match card with
  | none => say "gcp-probe: no Google network card (1ae0:0042)"
  | some index =>
    for at_ in [0x10, 0x14, 0x18, 0x1c, 0x20, 0x24] do
      say s!"  its configuration at {hex at_ 2}: {hex (← Hw.config index at_.toUInt32 4).toNat 8}"
    if !(← Hw.claim index) then say "gcp-probe: the card could not be claimed"
    else
      say "gcp-probe: the card is claimed"
      let windows ← Hw.windows
      for w in windows do
        if w.size != 0 then say s!"  window at {hex w.base.toNat 12}: {w.size} bytes"
      -- The first window's first words, as they come (the card's are most significant byte first).
      if h : 0 < windows.size then
        if windows[0].size ≥ 48 then
          for word in [0:12] do
            say s!"  register {hex (word * 4) 2}: {hex (← Hw.read (windows[0].base + (word * 4).toUInt64) 4).toNat 8}"
      let page ← Hw.alloc 4096
      say s!"  memory shared with it: {if page == 0 then "none" else "a page at " ++ hex page.toNat 12}"
  say "gcp-probe: done"
  asleep
