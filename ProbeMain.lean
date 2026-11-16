import BigTest
import Kernel.Virtio
import Kernel.Socket
import Kernel.SecureModule
import Kernel.CommandLine
import Platform

/-! # Looking at the machine

A bare-metal program that reports what it finds, over whatever `Platform.write` reaches (the serial port): the
boot loader's command line, every register window that was announced and what answers there, and then each
device it knows, driven as far as it can be without a parent:

  - an entropy device (an emulator has one): agree on features, set up its queue, ask for bytes twice;
  - a socket device: its address, and the boot heartbeat if the command line asks for one;
  - a Nitro Secure Module (an enclave has one): random bytes and an attestation document.

It exists for two things. Under an emulator it shows that the register access, the queue layout and the
polling work against a real device model, on the simplest device there is. In a real enclave started in debug
mode, it is how to find out what the machine looks like before anything depends on it.

Everything printed comes from the boot loader or a device, never from the parent. -/

open Kernel Kernel.Virtio

def say (line : String) : IO Unit := Platform.write (line ++ "\n").toUTF8

def hex (n : Nat) : String :=
  let digits := (Nat.toDigits 16 n)
  "0x" ++ String.ofList digits

def hexBytes (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

/-- Bytes as text, with anything that is not a plain printable character shown as `?`. -/
def printable (b : ByteArray) : String :=
  String.ofList (b.toList.map fun x => if 0x20 ≤ x ∧ x < 0x7f then Char.ofNat x.toNat else '?')

/-- Asks an entropy device for `count` bytes through `queue`. -/
def randomFrom (queue : Queue) (count : Nat) : BaseIO (Option ByteArray × Queue) := do
  let queue ← queue.offer 0 count true
  let (done, queue) ← queue.await 10000000
  match done with
  | some (slot, written) => return (some (← queue.read slot written), queue)
  | none => return (none, queue)

/-- Drives an entropy device. `true` if it gave bytes that look like entropy. -/
def probeEntropy (entropy : Device) : IO Bool := do
  unless ← entropy.negotiate do
    say "probe: the entropy device would not agree on features"
    return false
  let some queue ← Queue.create entropy 0 64
    | do say "probe: the entropy device's queue could not be set up"; return false
  entropy.start
  say s!"probe: entropy queue of {queue.layout.size} entries"
  let (first, queue) ← randomFrom queue 32
  let (second, _) ← randomFrom queue 32
  match first, second with
  | some a, some b =>
    say s!"probe: entropy gave {a.size} and {b.size} bytes"
    say s!"probe: {hexBytes a}"
    say s!"probe: {hexBytes b}"
    if a.size == 32 && b.size == 32 && a != b && a != ⟨Array.replicate 32 0⟩ then
      say "probe: the entropy device works"
      return true
    else
      say "probe: those bytes do not look like entropy"
      return false
  | _, _ =>
    say "probe: the entropy device did not answer"
    return false

/-- Asks a Secure Module for random bytes and for an attestation document. `true` if it gave both. -/
def probeSecureModule (device : Device) : IO Bool := do
  let some module ← SecureModule.start device
    | do say "probe: the secure module could not be started"; return false
  say s!"probe: secure module queue of {module.queue.layout.size} entries"
  let (bytes, module) ← module.random 32
  let some bytes := bytes
    | do say "probe: the secure module gave no random bytes"; return false
  say s!"probe: secure module random {hexBytes bytes}"
  let (document, _) ← module.attest (ByteArray.mk #[0x73, 0x69, 0x6c, 0x6f])
  let some document := document
    | do say "probe: the secure module gave no attestation document"; return false
  say s!"probe: attestation document of {document.size} bytes, starting {hexBytes (document.extract 0 16)}"
  say "probe: the secure module works"
  return true

/-- Tries the thing the command line names with `check=`, which the memory mapping is meant to forbid
(boot/checks.c). If the mapping holds, this does not return: the machine reports the fault and stops. -/
@[extern "silo_check"]
opaque forbidden : BaseIO UInt32

def main : IO UInt32 := do
  let line ← Hw.commandLine
  let devices ← discover
  -- A Nitro Enclave's parent takes it down unless it hears the boot heartbeat, and may not show what the
  -- enclave printed until it has. So if the command line asks for a heartbeat, that comes before the report.
  if let some text := CommandLine.value? line "silo.heartbeat" then
    match CommandLine.address? text, devices.find? (·.id == idSocket) with
    | some (parent, port), some device =>
      match ← Socket.start device 5005 with
      | none => say "probe: the socket device could not be started"
      | some socket =>
        let (answered, _, _) ← socket.heartbeat parent port
        if answered then say s!"probe: heartbeat answered by {parent}:{port}"
        else say s!"probe: no heartbeat answer from {parent}:{port}"
    | _, _ => say "probe: a heartbeat was asked for, but there is no socket device or the address is not cid:port"
  say s!"probe: command line: {printable line}"
  -- Asked to, the probe tries one forbidden thing, now that the parent has had its heartbeat and will show
  -- what is printed.
  if let some check := CommandLine.value? line "check" then
    -- `check=big` is not a forbidden thing but the big-number test, which a real enclave shows only from
    -- an image that has answered its parent.
    if check == "big".toUTF8 then return ← BigTest.report
    return ← forbidden
  let windows ← Hw.windows
  say s!"probe: {windows.size} register windows announced"
  for window in windows do
    if window.size < 0x200 then
      say s!"probe: window at {hex window.base.toNat} of {window.size} bytes: too small to look at"
    else
      let magic ← Hw.read32 (window.base + regMagic)
      let version ← Hw.read32 (window.base + regVersion)
      let id ← Hw.read32 (window.base + regDeviceId)
      let vendor ← Hw.read32 (window.base + regVendorId)
      say s!"probe: window at {hex window.base.toNat} of {window.size} bytes: magic {hex magic.toNat}, \
        version {version}, device {id}, vendor {hex vendor.toNat}"
  let mut tried := 0
  let mut worked := 0
  for device in devices do
    say s!"probe: virtio device {device.id} at {hex device.base.toNat}"
    if device.id == idEntropy then
      tried := tried + 1
      if ← probeEntropy device then worked := worked + 1
    else if device.id == idSocket then
      say s!"probe: socket device with address {← Hw.read32 (device.base + regConfig)}"
    else if device.id == idNitroSecureModule then
      tried := tried + 1
      if ← probeSecureModule device then worked := worked + 1
  if tried == 0 then
    say "probe: no device here that this can drive on its own"
    return 2
  return if worked == tried then 0 else 3
