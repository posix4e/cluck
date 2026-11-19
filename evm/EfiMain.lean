import Evm
import Kernel.Efi
import Kernel.Net.Tcp
import Kernel.Net.Fragment

/-! The service as a whole machine: an EFI guest on the OS's Ethernet, IP and TCP, in Intel TDX or under an
emulator. This is `TdxMain.lean` with the demo taken out. Each TCP connection carries frames (a 4-byte
big-endian length, then that many bytes); each frame is a request and is answered with one frame holding the
69 bytes of the response. A request may be far longer than a demo payload, up to `maxRequest`.

The machine does nothing else while a request runs: no packet is read and no timer serviced until the import
returns, which for a hard block is many seconds. A second client waits, and its TCP waits with it. -/

open Kernel Kernel.Net

private def servicePort : UInt16 := 5005

/-- The longest request accepted. -/
private def maxRequest : Nat := 8 * 1024 * 1024

private structure Server where
  tcp : Tcp.Endpoint := { listenPort := servicePort }
  fragments : Fragment.Cache := {}
  nextIpId : UInt32 := 0
  clients : Array (Tcp.Key × ByteArray) := #[]

private def removeClient (s : Server) (key : Tcp.Key) : Server :=
  { s with clients := s.clients.filter (·.1 != key) }

private def length (b : ByteArray) : Nat :=
  (b[0]!.toNat <<< 24) ||| (b[1]!.toNat <<< 16) ||| (b[2]!.toNat <<< 8) ||| b[3]!.toNat

/-- Whole requests at the front of `pending`, and what is left. `none` when a header is not acceptable. -/
private partial def requests (pending : ByteArray) (out : Array ByteArray) :
    Option (ByteArray × Array ByteArray) :=
  if pending.size < 4 then some (pending, out) else
  let n := length pending
  if n == 0 || n > maxRequest then none
  else if pending.size < 4 + n then some (pending, out)
  else requests (pending.extract (4 + n) pending.size) (out.push (pending.extract 4 (4 + n)))

private def frame (payload : ByteArray) : ByteArray :=
  Evm.Service.be 4 payload.size ++ payload

private partial def settle (cfg : Internet.Config) (now : Nat)
    (s : Server) (events : List Tcp.Event) : IO Server := do
  let ev :: rest := events | return s
  match ev with
  | .emit peer segment =>
    if let some frame := Internet.tcpFrame cfg peer segment then Efi.send frame
    settle cfg now s rest
  | .opened key =>
    settle cfg now { s with clients := s.clients.push (key, .empty) } rest
  | .closed key => settle cfg now (removeClient s key) rest
  | .finished key =>
    let (tcp, more) := s.tcp.close now key
    settle cfg now { (removeClient s key) with tcp } (rest ++ more.toList)
  | .data key bytes =>
    let some (_, pending) := s.clients.find? (·.1 == key) | settle cfg now s rest
    match requests (pending ++ bytes) #[] with
    | none =>
      let (tcp, more) := s.tcp.close now key
      settle cfg now { (removeClient s key) with tcp } (rest ++ more.toList)
    | some (pending, whole) =>
      let mut replies := ByteArray.empty
      for request in whole do
        Platform.write s!"evm: request of {request.size} bytes\n".toUTF8
        let started ← Efi.millis
        let reply ← IO.lazyPure fun _ => Evm.Service.serve request
        let ended ← Efi.millis
        Platform.write s!"evm: status {reply[0]!}, {(ended - started).toNat} ms\n".toUTF8
        replies := replies ++ frame reply
      -- The clock moved while the service ran; the stack is told the time it is now.
      let after ← Efi.millis
      let now := if whole.isEmpty then now else after.toNat
      let (tcp, more) := s.tcp.send now key replies
      let clients := s.clients.map fun c => if c.1 == key then (key, pending) else c
      settle cfg now { s with tcp, clients } (rest ++ more.toList)

private def freshWord : IO UInt32 := do
  let b ← Platform.random 4
  return (length b).toUInt32

private def input (cfg : Internet.Config) (now : Nat) (s : Server)
    (frame : ByteArray) : IO Server := do
  let (fragments, event) := s.fragments.receive now cfg frame
  let s := { s with fragments }
  match event with
  | some (.transmit answer) => Efi.send answer
  | some (.fragmentReply peer proto body) =>
    for answer in Fragment.ipFrames cfg peer proto body s.nextIpId do Efi.send answer
    return { s with nextIpId := s.nextIpId + 1 }
  | some (.tcp peer segment) =>
    let iss ← if segment.size ≥ 20 && segment[13]! &&& 0x12 == 2 then do
      try pure (some (← freshWord))
      catch _ => pure none
    else pure (some 0)
    let some iss := iss | return s
    let (tcp, events) := s.tcp.receive now iss peer segment
    return ← settle cfg now { s with tcp } events.toList
  | _ => pure ()
  return s

private partial def serve (cfg : Internet.Config) (s : Server) (lastTick : Nat) : IO UInt32 := do
  let now := (← Efi.millis).toNat
  let frame ← Efi.receive
  let s ← if frame.isEmpty then pure s else input cfg now s frame
  let (s, lastTick) ← if now ≥ lastTick + 20 then do
    let (tcp, events) := s.tcp.tick now
    pure (← settle cfg now { s with tcp, fragments := s.fragments.expire now } events.toList, now)
  else pure (s, lastTick)
  if frame.isEmpty then Efi.idle
  serve cfg s lastTick

def main : IO UInt32 := do
  let mac ← Efi.mac
  if mac.size != 6 then return 2
  let cfg : Internet.Config := { mac }
  if let some announcement := Internet.solicit cfg cfg.ipv4 then Efi.send announcement
  Platform.write "evm: Ethernet ready, serving TCP 5005\n".toUTF8
  serve cfg {} 0
