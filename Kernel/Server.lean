import Kernel.Socket
import Kernel.SecureModule
import Kernel.CommandLine
import Platform

/-! # A machine that serves

What every service on this OS does the same way: bring the machine up (the socket device, the boot heartbeat
a Nitro Enclave owes its parent, the Secure Module), then listen, and hand each connection's bytes to the
service as they arrive. A service is a function from bytes to bytes with some state of its own and some per
connection; it never sees the socket.

Progress is printed on the serial port. Nothing the parent sends is ever printed. -/

namespace Kernel

def say (line : String) : IO Unit := Platform.write (line ++ "\n").toUTF8

/-- What a service is to the machine: `σ` is what it keeps for as long as the machine runs, `κ` what it keeps
for one connection. -/
structure Service (σ κ : Type) where
  /-- What a new connection starts with. -/
  fresh : κ
  /-- Bytes have arrived on a connection. Returns the service's state, the connection's (or `none` to hang
  up on it), and the bytes to send back. -/
  receive : σ → κ → ByteArray → IO (σ × Option κ × ByteArray)

/-- Everything the machine has while it serves. -/
structure Machine (σ κ : Type) where
  socket : Socket
  state : σ
  clients : Array (Vsock.Key × κ) := #[]

/-- Deals with everything in `pending`, including whatever dealing with it stirs up. -/
partial def settle {σ κ : Type} (service : Service σ κ) (machine : Machine σ κ) (pending : List Vsock.Event) :
    IO (Machine σ κ) := do
  match pending with
  | [] => return machine
  | event :: pending =>
    let without (key : Vsock.Key) := machine.clients.filter (·.1 != key)
    let hangUp (machine : Machine σ κ) (key : Vsock.Key) : IO (Machine σ κ × List Vsock.Event) := do
      let (more, socket) ← machine.socket.apply (·.close key)
      return ({ machine with socket, clients := without key }, more.toList)
    match event with
    | .send _ => settle service machine pending
    | .opened key => settle service { machine with clients := machine.clients.push (key, service.fresh) } pending
    | .closed key => settle service { machine with clients := without key } pending
    | .finished key =>
      -- The parent has said all it will; so have we, since every request is answered as it arrives.
      let (machine, more) ← hangUp machine key
      settle service machine (pending ++ more)
    | .data key bytes =>
      let some (_, connection) := machine.clients.find? (·.1 == key) | settle service machine pending
      let (state, connection, reply) ← service.receive machine.state connection bytes
      let (socket, stirred) ← if reply.isEmpty then pure (machine.socket, []) else do
        let (_, more, socket) ← machine.socket.send key reply
        pure (socket, more.toList)
      match connection with
      | some connection =>
        let clients := machine.clients.map fun c => if c.1 == key then (key, connection) else c
        settle service { socket, state, clients } (pending ++ stirred)
      | none =>
        -- The service wants no more of this connection; the others carry on.
        let (machine, more) ← hangUp { machine with socket, state } key
        settle service machine (pending ++ stirred ++ more)

/-- Serves for as long as the machine runs. -/
partial def serve {σ κ : Type} (service : Service σ κ) (machine : Machine σ κ) : IO UInt32 := do
  let (events, socket) ← machine.socket.poll
  if events.isEmpty then Hw.pause
  let machine ← settle service { machine with socket } events.toList
  if machine.socket.stuck then
    -- A packet the device never took. The parent has stopped listening or the device has failed; either
    -- way there is nobody to serve, and carrying on would mean writing over a buffer the device may read.
    say "silo: the socket device stopped taking packets"
    return 11
  serve service machine

/-- A machine that is up: its socket, listening; its Secure Module if it has one; and whatever arrived while
it was coming up. -/
structure Up where
  socket : Socket
  module : Option SecureModule
  early : Array Vsock.Event

/-- Brings the machine up to the point of listening on `port`, or returns the status to stop with. -/
def bringUp (port : UInt32) : IO (Except UInt32 Up) := do
  let devices ← Virtio.discover
  let some device := devices.find? (·.id == Virtio.idSocket)
    | do say "silo: no socket device"; return .error 2
  let some socket ← Socket.start device port
    | do say "silo: the socket device could not be started"; return .error 3
  -- A Nitro Enclave has to tell its parent that it booted, or the parent takes it down. Whoever builds the
  -- image says where to on the command line (`silo.heartbeat=3:9000` in an enclave); without that, none is
  -- sent. A heartbeat that was asked for and not answered stops the machine.
  let line ← Hw.commandLine
  let mut socket := socket
  let mut early : Array Vsock.Event := #[]
  if let some text := CommandLine.value? line "silo.heartbeat" then
    let some (parent, heartbeatPort) := CommandLine.address? text
      | do say "silo: the heartbeat address on the command line is not cid:port"; return .error 4
    let (answered, events, socket') ← socket.heartbeat parent heartbeatPort
    socket := socket'
    early := events
    unless answered do
      say s!"silo: no heartbeat answer from {parent}:{heartbeatPort}"
      return .error 5
    say s!"silo: heartbeat answered by {parent}:{heartbeatPort}"
  -- The Secure Module, for attestation and random bytes. An enclave has one; an emulator need not.
  let module ← match devices.find? (·.id == Virtio.idNitroSecureModule) with
    | none => do say "silo: no secure module: attest is unavailable, random is the processor's"; pure none
    | some device => do
      let some module ← SecureModule.start device
        | do say "silo: the secure module could not be started"; return .error 6
      say "silo: secure module ready"
      pure (some module)
  say s!"silo: listening on port {port} as address {socket.endpoint.cid}"
  return .ok { socket, module, early }

/-- Random bytes the way this machine has them: from the Secure Module on a machine that has one, where a
failure is a failure and nothing quietly falls back; from the processor's generator on a machine without. -/
def randomBytes (module : Option SecureModule) (count : Nat) : IO (Option ByteArray × Option SecureModule) :=
  match module with
  | none => do return (some (← Platform.random count.toUSize), none)
  | some m => do
    let (bytes, m) ← m.random count
    return (bytes, some m)

/-- Brings the machine up and serves on `port` until it stops. `start` makes the service's state once the
machine is up, given the Secure Module if there is one. -/
def run {σ κ : Type} (port : UInt32) (service : Service σ κ) (start : Option SecureModule → IO (Except UInt32 σ)) :
    IO UInt32 := do
  match ← bringUp port with
  | .error status => return status
  | .ok up =>
    match ← start up.module with
    | .error status => return status
    | .ok state => serve service (← settle service { socket := up.socket, state } up.early.toList)

end Kernel
