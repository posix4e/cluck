import Kernel.Virtio
import Kernel.Nsm

/-! # The Nitro Secure Module's driver

The Secure Module is a virtio device with one queue. A request is two entries in that queue, posted together:
the request's bytes for the device to read, and an empty buffer for it to write the answer into. The device
hands both back; how much it wrote into the second is the answer's length. That is all of the transport, and
it is what Linux's driver does (`drivers/misc/nsm.c`). What the bytes say is `Kernel/Nsm.lean`.

One request is outstanding at a time, and the wait for its answer is bounded. A device that does not answer
leaves the queue in a state this code cannot vouch for, so after that the module is treated as gone: every
later request fails without touching it.

This has run in a real enclave, and runs in CI against the Secure Module QEMU emulates. -/

namespace Kernel

structure SecureModule where
  queue : Virtio.Queue
  /-- A request went unanswered; nothing more is asked of the device. -/
  gone : Bool := false

namespace SecureModule

/-- How many looks at the queue an answer is waited for. Signing an attestation document takes the device a
while; Linux allows it two minutes. -/
def patience : Nat := 200000000

/-- Which queue entries carry a request and its answer. -/
def requestSlot : Nat := 0
def answerSlot : Nat := 1

/-- Agrees on features with the device and sets up its queue. -/
def start (device : Virtio.Device) : BaseIO (Option SecureModule) := do
  unless ← device.negotiate do return none
  let some queue ← Virtio.Queue.create device 0 Nsm.maxResponse | return none
  if queue.layout.size < 2 then return none
  device.start
  return some { queue }

/-- Sends `request` and returns the device's answer as it came. -/
def exchange (m : SecureModule) (request : ByteArray) : BaseIO (Option ByteArray × SecureModule) := do
  if m.gone || request.size > Nsm.maxRequest then return (none, m)
  let mut queue := m.queue
  Hw.store (queue.bufferAddress requestSlot) request
  queue ← queue.post requestSlot request.size false
  queue ← queue.post answerSlot Nsm.maxResponse true
  queue.notify
  let mut written : Option Nat := none
  for _ in [0:2] do
    let (done, queue') ← queue.await patience
    queue := queue'
    match done with
    | none => return (none, { queue, gone := true })
    | some (slot, count) => if slot == answerSlot then written := some count
  match written with
  | none => return (none, { queue, gone := true })
  | some count => return (some (← queue.read answerSlot count), { queue })

/-- An attestation document carrying `nonce` and, if given, a statement of the image's own (`userData`) and a
public key of its own (`publicKey`): the document then says that an enclave with these measurements made
that statement and holds that key. -/
def attest (m : SecureModule) (nonce : ByteArray) (userData publicKey : Option ByteArray := none) :
    BaseIO (Option ByteArray × SecureModule) := do
  let some request := Nsm.attestation userData (some nonce) publicKey | return (none, m)
  let (answer, m) ← m.exchange request
  match answer.bind Nsm.Response.parse? with
  | some (.attestation document) => return (some document, m)
  | _ => return (none, m)

/-- The time, in seconds since 1970: the one the hypervisor writes into an attestation document asked for
now. -/
def time (m : SecureModule) : BaseIO (Option Nat × SecureModule) := do
  let some request := Nsm.attestation none none none | return (none, m)
  let (answer, m) ← m.exchange request
  match answer.bind Nsm.Response.parse? with
  | some (.attestation document) => return ((Nsm.documentTime? document).map (· / 1000), m)
  | _ => return (none, m)

/-- `count` random bytes. The device gives a few hundred at a time, so this asks until it has enough, a
bounded number of times. -/
def random (m : SecureModule) (count : Nat) : BaseIO (Option ByteArray × SecureModule) := do
  let mut m := m
  let mut out := ByteArray.empty
  for _ in [0:count + 1] do
    if out.size ≥ count then break
    let (answer, m') ← m.exchange Nsm.getRandom
    m := m'
    match answer.bind Nsm.Response.parse? with
    | some (.random bytes) =>
      if bytes.isEmpty then return (none, m)
      out := out ++ bytes
    | _ => return (none, m)
  if out.size ≥ count then return (some (out.extract 0 count), m) else return (none, m)

end SecureModule

end Kernel
