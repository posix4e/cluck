/-! # The machine, as far as Lean may touch it

Everything a driver does to hardware goes through the handful of functions here, implemented in C per
platform (`rt/bare/hw.c`). They are deliberately narrow:

  - device registers can be read and written only inside the windows the boot loader announced;
  - memory shared with devices comes from one arena set aside at boot, and bytes move in and out of it only
    as copies, checked to lie inside it.

So a mistake in a driver, or a device answering with a wild length, cannot reach the Lean heap, the stack or
the code: the worst a bad address does is stop the machine. No function here hands Lean a pointer.

All logic about what the registers and the shared memory mean is in Lean (`Kernel/Virtq.lean`,
`Kernel/Virtio.lean`). -/

namespace Kernel.Hw

/-- A device's registers as the boot loader announced them: where they are and how many bytes. -/
structure Window where
  base : UInt64
  size : UInt64
  deriving Repr, Inhabited, BEq

/-- The register windows, as `base₀, size₀, base₁, size₁, …`. -/
@[extern "silo_hw_windows"]
opaque windowsRaw : BaseIO (Array UInt64)

def windows : BaseIO (Array Window) := do
  let raw ← windowsRaw
  return (Array.range (raw.size / 2)).map fun i => { base := raw[2 * i]!, size := raw[2 * i + 1]! }

/-- A 32-bit device register. Stops the machine if `address` is not inside an announced window. -/
@[extern "silo_hw_read32"]
opaque read32 (address : UInt64) : BaseIO UInt32

@[extern "silo_hw_write32"]
opaque write32 (address : UInt64) (value : UInt32) : BaseIO Unit

/-- `size` bytes of zeroed memory a device can be pointed at, page-aligned and never freed. Zero if the
arena has no room left. -/
@[extern "silo_hw_alloc"]
opaque alloc (size : USize) : BaseIO UInt64

/-- A copy of `size` bytes of device memory. Stops the machine if they are not all inside the arena. -/
@[extern "silo_hw_load"]
opaque load (address : UInt64) (size : USize) : BaseIO ByteArray

/-- Copies `bytes` into device memory. Stops the machine if they would not all land inside the arena. -/
@[extern "silo_hw_store"]
opaque store (address : UInt64) (bytes : @& ByteArray) : BaseIO Unit

/-! ## A PCI device, where the firmware offers them (the EFI target)

There a driver first looks through the PCI devices by their configuration, claims one, and after that the
windows are that device's six address ranges (window `i` at the made-up address `(i + 1) <<< 32`), and the
shared memory is an arena got when it was claimed. Registers come in three widths. -/

/-- How many PCI devices the firmware found. -/
@[extern "silo_hw_devices"]
opaque devices : BaseIO USize

/-- `width` bytes (1, 2 or 4) of device `index`'s configuration at `offset`; all ones if it will not say. -/
@[extern "silo_hw_config"]
opaque config (index : USize) (offset : UInt32) (width : UInt8) : BaseIO UInt32

/-- Takes device `index` from the firmware's drivers for this program alone, lets it use memory, and sets
aside the memory shared with it. Once, for one device. Whether it worked. -/
@[extern "silo_hw_claim"]
opaque claim (index : USize) : BaseIO Bool

/-- A device register of `width` bytes (1, 2 or 4). Stops the machine if it is not inside a window. -/
@[extern "silo_hw_read"]
opaque read (address : UInt64) (width : UInt8) : BaseIO UInt32

@[extern "silo_hw_write"]
opaque write (address : UInt64) (width : UInt8) (value : UInt32) : BaseIO Unit

/-- `size` bytes of device memory copied into `bytes` from place `at_` on, where `bytes` is: nothing is
allocated. Stops the machine if `bytes` has another owner or is too short. -/
@[extern "silo_hw_load_into"]
opaque loadInto (address : UInt64) (bytes : ByteArray) (at_ size : USize) : BaseIO ByteArray

/-- `size` bytes of `bytes` from place `at_` on copied into device memory. -/
@[extern "silo_hw_store_from"]
opaque storeFrom (address : UInt64) (bytes : @& ByteArray) (at_ size : USize) : BaseIO Unit

/-- Two bytes of device memory at an even address, least significant first, read in one go: what a
position in a queue must be read with, since the device changes it while it is read, and bytes copied one
at a time can come out half old and half new. -/
@[extern "silo_hw_load16"]
opaque load16 (address : UInt64) : BaseIO UInt16

/-- The same, written in one go, and seen by the other side before anything this side reads next. -/
@[extern "silo_hw_store16"]
opaque store16 (address : UInt64) (value : UInt16) : BaseIO Unit

/-- The boot loader's command line, as the bytes it gave. -/
@[extern "silo_hw_command_line"]
opaque commandLine : BaseIO ByteArray

/-- Four bytes of device memory at an address that is a multiple of four, least significant first, read
in one go. -/
@[extern "silo_hw_load32"]
opaque load32 (address : UInt64) : BaseIO UInt32

/-- Four bytes of device memory at an address that is a multiple of four, least significant first,
written in one go. -/
@[extern "silo_hw_store32"]
opaque store32 (address : UInt64) (value : UInt32) : BaseIO Unit

/-- The processor's count of time, in units of its own: for comparing how long things take with one
another. Nothing says how many make a second. -/
@[extern "silo_hw_ticks"]
opaque ticks : BaseIO UInt64

/-- A hint to the processor that this is a wait loop. -/
@[extern "silo_hw_pause"]
opaque pause : BaseIO Unit

end Kernel.Hw
