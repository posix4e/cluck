import Kernel.Virtio
import Kernel.Vsock

/-! # The socket device

The vsock protocol (`Kernel/Vsock.lean`) joined to a real device (`Kernel/Virtio.lean`): packets the device
delivers go into the protocol, packets the protocol wants sent go out through the device, and what is left
over are the events the service cares about.

Everything is polled and nothing waits forever: each wait has a bound, and running out of patience is
reported, not hidden. -/

namespace Kernel

open Kernel.Virtio

/-- Looks at a queue this many times before deciding the device is not going to answer. -/
def patience : Nat := 50000000

/-- Room in each buffer for a packet: its header and the most payload one carries. -/
def packetBuffer : Nat := 8192

structure Socket where
  receive : Queue
  transmit : Queue
  endpoint : Vsock.Endpoint
  /-- The device was handed a packet and did not take it in all the time it was given. Its one transmit
  buffer may still be the device's, so nothing more is sent, and whoever serves stops the machine. -/
  stuck : Bool := false
  deriving Inhabited

namespace Socket

/-- Takes over a socket device and listens on `port`. `none` if the device will not cooperate. -/
def start (device : Device) (port : UInt32) : BaseIO (Option Socket) := do
  unless ← device.negotiate do return none
  -- The device's configuration is one number: the address this machine has been given.
  let low ← Hw.read32 (device.base + regConfig)
  let high ← Hw.read32 (device.base + regConfig + 4)
  let cid := low.toUInt64 ||| (high.toUInt64 <<< 32)
  let some receive ← Queue.create device 0 packetBuffer | return none
  let some transmit ← Queue.create device 1 packetBuffer | return none
  -- The third queue carries notices we do not act on; it is set up so the device has all it expects.
  let _ ← Queue.create device 2 64
  device.start
  -- Every receive buffer is the device's to fill.
  let mut receive := receive
  for slot in [0:receive.layout.size] do
    receive ← receive.offer slot packetBuffer true
  return some { receive, transmit, endpoint := { cid, listenPort := port } }

/-- Hands one packet to the device and waits for it to be taken. If it is not taken, the socket is stuck:
the buffer cannot be used again while the device may still read it. -/
def put (s : Socket) (packet : ByteArray) : BaseIO Socket := do
  if s.stuck then return s
  let transmit ← s.transmit.give 0 packet
  let (taken, transmit) ← transmit.await patience
  return { s with transmit, stuck := taken.isNone }

/-- Sends what the protocol asked to have sent, and returns the rest of the events. -/
def deliver (s : Socket) (events : Array Vsock.Event) : BaseIO (Array Vsock.Event × Socket) := do
  let mut s := s
  let mut rest := #[]
  for event in events do
    match event with
    | .send packet => s ← s.put packet
    | other => rest := rest.push other
  return (rest, s)

/-- Runs one step of the protocol and carries out its sends. -/
def apply (s : Socket) (step : Vsock.Endpoint → Vsock.Endpoint × Array Vsock.Event) :
    BaseIO (Array Vsock.Event × Socket) := do
  let (endpoint, events) := step s.endpoint
  deliver { s with endpoint } events

/-- Takes one packet from the device, if one is waiting, and returns what it led to. -/
def poll (s : Socket) : BaseIO (Array Vsock.Event × Socket) := do
  let (arrived, receive) ← s.receive.take?
  let s := { s with receive }
  match arrived with
  | none => return (#[], s)
  | some (slot, written) =>
    let raw ← s.receive.read slot written
    let receive ← s.receive.offer slot packetBuffer true
    apply { s with receive } (·.receive raw)

/-- Sends `bytes` on a connection, waiting for the peer to make room as often as it takes. `false` if the
connection went away or the peer never made room. Events that arrive meanwhile are returned, not lost. -/
def send (s : Socket) (key : Vsock.Key) (bytes : ByteArray) : BaseIO (Bool × Array Vsock.Event × Socket) := do
  let mut s := s
  let mut events := #[]
  let mut done := 0
  let mut waited := 0
  while done < bytes.size do
    if (s.endpoint.find? key).isNone then return (false, events, s)
    let (endpoint, out, accepted) := s.endpoint.write key (bytes.extract done bytes.size)
    let (more, s') ← deliver { s with endpoint } out
    s := s'
    events := events ++ more
    done := done + accepted
    if accepted == 0 then
      waited := waited + 1
      if waited > patience then return (false, events, s)
      -- Nudge a peer that has not said for a while how much room it has.
      if waited % 100000 == 1 then
        let (more, s') ← s.apply (·.askForRoom key)
        s := s'
        events := events ++ more
      let (more, s') ← s.poll
      s := s'
      events := events ++ more
      Hw.pause
    else
      waited := 0
  return (true, events, s)

/-- Polls until `done` says an event settles the matter, for at most `patience` looks. Events that do not
are kept and returned, so that nothing that arrives meanwhile is lost. -/
def waitFor (s : Socket) (done : Vsock.Event → Option Bool) : BaseIO (Option Bool × Array Vsock.Event × Socket) := do
  let mut s := s
  let mut kept := #[]
  for _ in [0:patience] do
    let (events, s') ← s.poll
    s := s'
    let mut verdict := none
    for event in events do
      match verdict, done event with
      | none, some v => verdict := some v
      | _, _ => kept := kept.push event
    if verdict.isSome then return (verdict, kept, s)
    if events.isEmpty then Hw.pause
  return (none, kept, s)

/-- The port our end of the heartbeat connection uses. -/
def heartbeatPort : UInt32 := 49152

/-- The byte a Nitro Enclave sends its parent to say it has booted, and expects back. -/
def heartbeatByte : UInt8 := 0xB7

/-- Tells the parent this machine is up, the way a Nitro Enclave must: connect to `port` at `parent`, send one
byte, read the same byte back, close. `true` if all of that happened. Events for other connections that
arrive meanwhile are returned. -/
def heartbeat (s : Socket) (parent : UInt64) (port : UInt32) : BaseIO (Bool × Array Vsock.Event × Socket) := do
  let key : Vsock.Key := { peerCid := parent, peerPort := port, localPort := heartbeatPort }
  let (endpoint, events, asked) := s.endpoint.connect key
  unless asked do return (false, #[], s)
  let (_, s) ← deliver { s with endpoint } events
  -- Answered, or refused.
  let (opened, kept, s) ← s.waitFor fun
    | .opened k => if k == key then some true else none
    | .closed k => if k == key then some false else none
    | _ => none
  unless opened == some true do return (false, kept, s)
  let (sent, more, s) ← s.send key (ByteArray.empty.push heartbeatByte)
  let kept := kept ++ more
  unless sent do return (false, kept, s)
  -- The same byte back, and nothing else.
  let (echoed, more, s) ← s.waitFor fun
    | .data k bytes => if k == key then some (bytes == ByteArray.empty.push heartbeatByte) else none
    | .closed k => if k == key then some false else none
    | .finished k => if k == key then some false else none
    | _ => none
  let kept := kept ++ more
  -- Done with the connection either way. The parent's reset, when it comes, is handled like any other packet.
  let (more, s) ← s.apply (·.close key)
  return (echoed == some true, (kept ++ more).filter (fun | .closed k => k != key | _ => true), s)

end Socket
end Kernel
