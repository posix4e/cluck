/-! # mkimage: the kernel image a Linux boot protocol loader is given

    mkimage <image.elf> <setup.bin> <out>

A loader that speaks the Linux boot protocol (a Nitro Enclave's is one) wants a kernel in Linux's "bzImage"
shape: a few 512-byte sectors of setup, whose header tells the loader what follows, and then the kernel
proper as one run of bytes to be put in memory as it is.

Here the setup sectors are `boot/setup.S`, linked flat, and the kernel proper is the image `scripts/build-bare`
links, taken out of its ELF file: every loadable segment at its place relative to the first, the gaps between
them zero, and nothing for memory that is not in the file (`boot/linux.S` and `boot/entry.S` see to that when
the image runs). Nothing is compressed.

Three fields of the header depend on the image and are filled in here: how many setup sectors there are, how
long the kernel proper is, and how much memory it needs from where it is loaded. The last has to cover the
image moving itself from the lowest place a loader puts it (`code32_start`, 1 MiB) to where it is linked to
run, so it is the distance from the one to the end of the image at the other.

The same inputs give the same bytes. -/

namespace MkImage

/-- The `width` little-endian bytes at `offset`. The caller has checked they are there. -/
def readLE (b : ByteArray) (offset width : Nat) : Nat :=
  (List.range width).foldl (fun acc i => acc ||| (b[offset + i]!.toNat <<< (8 * i))) 0

/-- `b` with `value` written at `offset` as `width` little-endian bytes. -/
def writeLE (b : ByteArray) (offset width value : Nat) : ByteArray :=
  (List.range width).foldl (fun out i => out.set! (offset + i) (value >>> (8 * i)).toUInt8) b

def zeros (count : Nat) : ByteArray := Id.run do
  let chunk := ByteArray.mk (Array.replicate 4096 0)
  let mut out := ByteArray.empty
  while out.size + chunk.size ≤ count do
    out := out ++ chunk
  return out ++ chunk.extract 0 (count - out.size)

def roundUp (value multiple : Nat) : Nat := (value + multiple - 1) / multiple * multiple

/-- A part of an ELF file that a loader puts in memory: `fileSize` bytes from `offset` in the file go to
`address`, and the part takes `memorySize` bytes there. -/
structure Segment where
  address : Nat
  offset : Nat
  fileSize : Nat
  memorySize : Nat
  deriving Repr, Inhabited

/-- The loadable segments of a 64-bit little-endian x86-64 ELF file. -/
def segments (elf : ByteArray) : Except String (Array Segment) := do
  unless elf.size ≥ 64 ∧ readLE elf 0 4 = 0x464c457f do throw "not an ELF file"
  unless elf[4]! = 2 ∧ elf[5]! = 1 ∧ readLE elf 0x12 2 = 62 do throw "not a 64-bit x86-64 ELF file"
  let table := readLE elf 0x20 8
  let entrySize := readLE elf 0x36 2
  let count := readLE elf 0x38 2
  unless entrySize ≥ 56 ∧ table + count * entrySize ≤ elf.size do throw "the program headers run off the file"
  let mut found := #[]
  for i in [0:count] do
    let at' := table + i * entrySize
    if readLE elf at' 4 = 1 then
      let segment : Segment :=
        { offset := readLE elf (at' + 8) 8, address := readLE elf (at' + 24) 8,
          fileSize := readLE elf (at' + 32) 8, memorySize := readLE elf (at' + 40) 8 }
      unless segment.offset + segment.fileSize ≤ elf.size ∧ segment.fileSize ≤ segment.memorySize do
        throw "a segment runs off the file"
      found := found.push segment
  if found.isEmpty then throw "nothing in the file is to be loaded"
  return found

/-! Where things are in the setup header (Linux's Documentation/arch/x86/boot.rst). -/

def offSetupSectors : Nat := 0x1f1
def offKernelSize : Nat := 0x1f4
def offMagic : Nat := 0x202
def offLowestLoad : Nat := 0x214
def offHome : Nat := 0x258
def offMemoryNeeded : Nat := 0x260
def headerEnd : Nat := 0x26c

structure Built where
  image : ByteArray
  setupSize : Nat
  kernelSize : Nat
  home : Nat
  memoryNeeded : Nat

/-- The kernel image made of `setup` and the loadable parts of `elf`. -/
def build (elf setup : ByteArray) : Except String Built := do
  let parts ← segments elf
  unless setup.size ≥ headerEnd ∧ readLE setup offMagic 4 = 0x53726448 do
    throw "the setup sectors do not have a setup header"
  let home := readLE setup offHome 8
  let lowest := readLE setup offLowestLoad 4
  let start := parts.foldl (fun least part => min least part.address) parts[0]!.address
  unless start = home do
    throw s!"the image is linked to run at {start}, but the setup header says {home}"
  unless lowest ≤ home do throw "the setup header's load address is above where the image runs"
  let fileEnd := parts.foldl (fun most part => max most (part.address + part.fileSize)) 0
  let memoryEnd := parts.foldl (fun most part => max most (part.address + part.memorySize)) 0
  let mut kernel := zeros (roundUp (fileEnd - start) 16)
  for part in parts do
    kernel := elf.copySlice part.offset kernel (part.address - start) part.fileSize
  let sectors := roundUp setup.size 512 / 512
  unless sectors ≥ 2 ∧ sectors ≤ 64 do throw "the setup sectors are too few or too many"
  let memoryNeeded := roundUp (memoryEnd - lowest) 4096
  unless kernel.size / 16 < 2 ^ 32 ∧ memoryNeeded < 2 ^ 32 do throw "the image is too large"
  let mut front := setup ++ zeros (sectors * 512 - setup.size)
  front := front.set! offSetupSectors (sectors - 1).toUInt8
  front := writeLE front offKernelSize 4 (kernel.size / 16)
  front := writeLE front offMemoryNeeded 4 memoryNeeded
  return { image := front ++ kernel, setupSize := front.size, kernelSize := kernel.size, home, memoryNeeded }

end MkImage

def main (args : List String) : IO UInt32 := do
  match args with
  | [elfPath, setupPath, outPath] =>
    let elf ← IO.FS.readBinFile elfPath
    let setup ← IO.FS.readBinFile setupPath
    match MkImage.build elf setup with
    | .ok built =>
      IO.FS.writeBinFile outPath built.image
      IO.eprintln s!"mkimage: {built.setupSize} bytes of setup, {built.kernelSize} of kernel to run at \
        {built.home}, needing {built.memoryNeeded} bytes from where it is loaded"
      return 0
    | .error why =>
      IO.eprintln s!"mkimage: {why}"
      return 1
  | _ =>
    IO.eprintln "usage: mkimage <image.elf> <setup.bin> <out>"
    return 2
