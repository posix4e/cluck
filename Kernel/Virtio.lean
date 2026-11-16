import Kernel.Hw
import Kernel.Virtq

/-! # virtio devices behind memory-mapped registers

Finding a device, agreeing on features with it, and passing buffers through its queues. This is the
"virtio over MMIO" transport, version 2, and the split virtqueue, driven by polling: nothing here ever waits
for an interrupt, because none is enabled.

The device is the hypervisor's, which the enclave has to trust anyway. Even so, what it reports is treated
as numbers to be checked: a queue size is clamped, a length the device says it wrote is cut to the buffer's
size before anything is read, and an index is only ever used modulo the queue size. -/

namespace Kernel.Virtio

open Kernel

/-! ## Registers -/

def regMagic : UInt64 := 0x000
def regVersion : UInt64 := 0x004
def regDeviceId : UInt64 := 0x008
def regVendorId : UInt64 := 0x00c
def regDeviceFeatures : UInt64 := 0x010
def regDeviceFeaturesSel : UInt64 := 0x014
def regDriverFeatures : UInt64 := 0x020
def regDriverFeaturesSel : UInt64 := 0x024
def regQueueSel : UInt64 := 0x030
def regQueueNumMax : UInt64 := 0x034
def regQueueNum : UInt64 := 0x038
def regQueueReady : UInt64 := 0x044
def regQueueNotify : UInt64 := 0x050
def regStatus : UInt64 := 0x070
def regQueueDescLow : UInt64 := 0x080
def regQueueDescHigh : UInt64 := 0x084
def regQueueDriverLow : UInt64 := 0x090
def regQueueDriverHigh : UInt64 := 0x094
def regQueueDeviceLow : UInt64 := 0x0a0
def regQueueDeviceHigh : UInt64 := 0x0a4
def regConfig : UInt64 := 0x100

/-- "virt", little-endian. -/
def magic : UInt32 := 0x74726976

def statusAcknowledge : UInt32 := 1
def statusDriver : UInt32 := 2
def statusDriverOk : UInt32 := 4
def statusFeaturesOk : UInt32 := 8

/-- Device types this code knows by number. -/
def idEntropy : UInt32 := 4
def idSocket : UInt32 := 19
def idNitroSecureModule : UInt32 := 33

/-- A device that answered at a register window. -/
structure Device where
  base : UInt64
  id : UInt32
  deriving Repr, Inhabited

/-- Every announced window that holds a version-2 virtio device. An empty slot answers with device id 0. -/
def discover : BaseIO (Array Device) := do
  let mut found := #[]
  for window in ← Hw.windows do
    if window.size < 0x200 then continue
    if (← Hw.read32 (window.base + regMagic)) != magic then continue
    if (← Hw.read32 (window.base + regVersion)) != 2 then continue
    let id ← Hw.read32 (window.base + regDeviceId)
    if id != 0 then found := found.push { base := window.base, id }
  return found

/-- Starts talking to a device: reset it, say a driver is here, and accept the one feature this code needs
(the version-1 format, feature bit 32) and nothing else. `false` if the device will not have that. -/
def Device.negotiate (d : Device) : BaseIO Bool := do
  Hw.write32 (d.base + regStatus) 0
  Hw.write32 (d.base + regStatus) statusAcknowledge
  Hw.write32 (d.base + regStatus) (statusAcknowledge ||| statusDriver)
  Hw.write32 (d.base + regDeviceFeaturesSel) 1
  let high ← Hw.read32 (d.base + regDeviceFeatures)
  if high &&& 1 == 0 then return false
  Hw.write32 (d.base + regDriverFeaturesSel) 0
  Hw.write32 (d.base + regDriverFeatures) 0
  Hw.write32 (d.base + regDriverFeaturesSel) 1
  Hw.write32 (d.base + regDriverFeatures) 1
  let status := statusAcknowledge ||| statusDriver ||| statusFeaturesOk
  Hw.write32 (d.base + regStatus) status
  return (← Hw.read32 (d.base + regStatus)) &&& statusFeaturesOk != 0

/-- Says the driver is ready. Queues must be set up before this. -/
def Device.start (d : Device) : BaseIO Unit :=
  Hw.write32 (d.base + regStatus) (statusAcknowledge ||| statusDriver ||| statusFeaturesOk ||| statusDriverOk)

/-! ## Queues -/

/-- The most entries a queue of ours has, whatever the device offers. -/
def maxQueueSize : Nat := 16

/-- One queue: its tables, and one fixed buffer per entry. Entry `i` always uses descriptor `i` and buffer
`i`, so there is nothing to allocate or free while it runs. -/
structure Queue where
  device : Device
  index : UInt32
  layout : Virtq.Layout
  /-- Where the tables are in device memory. -/
  tables : UInt64
  /-- Where the buffers are, `bufferSize` bytes each. -/
  buffers : UInt64
  bufferSize : Nat
  /-- How many entries we have offered so far, modulo 2^16: the available ring's index. -/
  offered : Nat := 0
  /-- How many used entries we have taken so far, modulo 2^16. -/
  taken : Nat := 0
  deriving Repr, Inhabited

def Queue.bufferAddress (q : Queue) (slot : Nat) : UInt64 :=
  q.buffers + (slot % q.layout.size * q.bufferSize).toUInt64

/-- Sets up queue `index` of a device with buffers of `bufferSize` bytes. `none` if the device has no such
queue or device memory has run out. -/
def Queue.create (d : Device) (index : UInt32) (bufferSize : Nat) : BaseIO (Option Queue) := do
  Hw.write32 (d.base + regQueueSel) index
  let offered := (← Hw.read32 (d.base + regQueueNumMax)).toNat
  if offered == 0 then return none
  let size := min offered maxQueueSize
  let layout := Virtq.Layout.of size
  let tables ← Hw.alloc layout.bytes.toUSize
  let buffers ← Hw.alloc (size * bufferSize).toUSize
  if tables == 0 || buffers == 0 then return none
  Hw.write32 (d.base + regQueueNum) size.toUInt32
  let set (low high : UInt64) (address : UInt64) : BaseIO Unit := do
    Hw.write32 (d.base + low) address.toUInt32
    Hw.write32 (d.base + high) (address >>> 32).toUInt32
  set regQueueDescLow regQueueDescHigh (tables + layout.descriptors.toUInt64)
  set regQueueDriverLow regQueueDriverHigh (tables + layout.available.toUInt64)
  set regQueueDeviceLow regQueueDeviceHigh (tables + layout.used.toUInt64)
  Hw.write32 (d.base + regQueueReady) 1
  return some { device := d, index, layout, tables, buffers, bufferSize }

/-- Puts entry `slot` where the device will find it: `length` bytes of its buffer, for the device to read or
to write. The device is not told; `notify` does that, once for however many entries were posted. -/
def Queue.post (q : Queue) (slot length : Nat) (deviceWrites : Bool) : BaseIO Queue := do
  let slot := slot % q.layout.size
  let length := min length q.bufferSize
  Hw.store (q.tables + (q.layout.descriptors + Virtq.descriptorSize * slot).toUInt64)
    (Virtq.descriptor (q.bufferAddress slot) length (if deviceWrites then Virtq.flagWrite else 0) 0)
  Hw.store (q.tables + (q.layout.availableSlot q.offered).toUInt64) (Virtq.le slot 2)
  let offered := (q.offered + 1) % 65536
  Hw.store (q.tables + q.layout.availableIndex.toUInt64) (Virtq.le offered 2)
  return { q with offered }

/-- Tells the device there is something new in the queue. -/
def Queue.notify (q : Queue) : BaseIO Unit :=
  Hw.write32 (q.device.base + regQueueNotify) q.index

/-- Offers entry `slot` to the device: `length` bytes of its buffer, for the device to read or to write. -/
def Queue.offer (q : Queue) (slot length : Nat) (deviceWrites : Bool) : BaseIO Queue := do
  let q ← q.post slot length deviceWrites
  q.notify
  return q

/-- The next entry the device has finished with, if there is one: which slot, and how many bytes the device
says it wrote there (cut to the buffer's size). -/
def Queue.take? (q : Queue) : BaseIO (Option (Nat × Nat) × Queue) := do
  let index := Virtq.readLE (← Hw.load (q.tables + q.layout.usedIndex.toUInt64) 2) 0 2
  if index == q.taken then return (none, q)
  let entry ← Hw.load (q.tables + (q.layout.usedSlot q.taken).toUInt64) 8
  let slot := Virtq.readLE entry 0 4 % q.layout.size
  let written := min (Virtq.readLE entry 4 4) q.bufferSize
  return (some (slot, written), { q with taken := (q.taken + 1) % 65536 })

/-- Waits for the device to finish with an entry, for at most `patience` looks. -/
def Queue.await (q : Queue) (patience : Nat) : BaseIO (Option (Nat × Nat) × Queue) := do
  let mut q := q
  for _ in [0:patience] do
    let (done, q') ← q.take?
    q := q'
    if done.isSome then return (done, q)
    Hw.pause
  return (none, q)

/-- Fills entry `slot`'s buffer and offers it for the device to read. -/
def Queue.give (q : Queue) (slot : Nat) (bytes : ByteArray) : BaseIO Queue := do
  let bytes := bytes.extract 0 (min bytes.size q.bufferSize)
  Hw.store (q.bufferAddress slot) bytes
  q.offer slot bytes.size false

/-- What the device wrote into entry `slot`'s buffer: its first `written` bytes. -/
def Queue.read (q : Queue) (slot written : Nat) : BaseIO ByteArray :=
  Hw.load (q.bufferAddress slot) (min written q.bufferSize).toUSize

end Kernel.Virtio
