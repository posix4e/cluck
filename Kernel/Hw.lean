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

/-- The boot loader's command line, as the bytes it gave. -/
@[extern "silo_hw_command_line"]
opaque commandLine : BaseIO ByteArray

/-- A hint to the processor that this is a wait loop. -/
@[extern "silo_hw_pause"]
opaque pause : BaseIO Unit

end Kernel.Hw
