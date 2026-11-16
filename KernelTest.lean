import Kernel.CommandLine
import Kernel.Virtq

/-! # Tests of the kernel's small pure pieces

The command line's words and values, and where each field of a virtqueue lives. Pure: no device. -/

open Kernel

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

def text (b : Option ByteArray) : Option String := b.map fun b => String.ofList (b.toList.map fun x => Char.ofNat x.toNat)

def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  let check (name : String) (holds : Bool) : IO Unit := do
    unless holds do
      failures.modify (· + 1)
      IO.eprintln s!"FAIL {name}"
  -- The command line.
  let line := "console=ttyS0  virtio_mmio.device=512@0xfeb00e00:12 silo.heartbeat=3:9000 quiet".toUTF8
  check "words" ((CommandLine.words line).length == 4)
  check "no words" ((CommandLine.words "   ".toUTF8).isEmpty && (CommandLine.words ByteArray.empty).isEmpty)
  check "a value" (text (CommandLine.value? line "silo.heartbeat") == some "3:9000")
  check "the first of two" (text (CommandLine.value? "a=1 a=2".toUTF8 "a") == some "1")
  check "an empty value" (text (CommandLine.value? "a= b=2".toUTF8 "a") == some "")
  check "a missing key" ((CommandLine.value? line "silo.other").isNone)
  check "a key is a whole word" ((CommandLine.value? "xsilo.heartbeat=1:2".toUTF8 "silo.heartbeat").isNone)
  check "a word without a value is not a value" ((CommandLine.value? line "quiet").isNone)
  check "decimal" (CommandLine.decimal? "9000".toUTF8 == some 9000 && CommandLine.decimal? "0".toUTF8 == some 0)
  check "not decimal" ((CommandLine.decimal? "0x10".toUTF8).isNone && (CommandLine.decimal? "".toUTF8).isNone &&
    (CommandLine.decimal? "12 ".toUTF8).isNone && (CommandLine.decimal? "-1".toUTF8).isNone)
  check "too long for a number" ((CommandLine.decimal? "12345678901234567890".toUTF8).isNone)
  check "an address" (CommandLine.address? "3:9000".toUTF8 == some (3, 9000))
  check "not an address" ((CommandLine.address? "3".toUTF8).isNone && (CommandLine.address? ":9000".toUTF8).isNone &&
    (CommandLine.address? "3:".toUTF8).isNone && (CommandLine.address? "3:9000:1".toUTF8).isNone &&
    (CommandLine.address? "three:9000".toUTF8).isNone)
  check "a port too large" ((CommandLine.address? "3:4294967296".toUTF8).isNone)
  -- A virtqueue's memory.
  check "little-endian" (hex (Virtq.le 0x0102030405060708 8) == "0807060504030201" && hex (Virtq.le 0x1234 2) == "3412")
  check "read back" (Virtq.readLE (Virtq.le 0xCAFEBABE 4) 0 4 == 0xCAFEBABE)
  check "reading past the end gives zero" (Virtq.readLE (Virtq.le 7 2) 1 2 == 0)
  check "a descriptor" (hex (Virtq.descriptor 0x1000 64 Virtq.flagWrite 0) ==
    "0010000000000000" ++ "40000000" ++ "0200" ++ "0000")
  check "a descriptor is 16 bytes" ((Virtq.descriptor 0 0 0 0).size == Virtq.descriptorSize)
  let l := Virtq.Layout.of 16
  check "layout of 16" (l.descriptors == 0 && l.available == 256 && l.used == 296 && l.bytes == 296 + 6 + 128)
  check "the used ring is aligned" ((Virtq.Layout.of 8).used % 4 == 0 && (Virtq.Layout.of 5).used % 4 == 0)
  check "ring slots wrap" (l.availableSlot 16 == l.availableSlot 0 && l.usedSlot 17 == l.usedSlot 1)
  check "ring fields" (l.availableIndex == 258 && l.availableSlot 1 == 262 && l.usedIndex == 298 && l.usedSlot 1 == 308)
  let failed ← failures.get
  if failed == 0 then
    IO.println "kernel-test: all checks passed"
    return 0
  else
    IO.eprintln s!"kernel-test: {failed} check(s) failed"
    return 1
