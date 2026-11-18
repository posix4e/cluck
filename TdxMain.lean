import Demo
import SelfTest
import Kernel.Efi
import Kernel.Net.Tcp
import Kernel.Net.Fragment

/-! The TDX demo takes framed requests on TCP and echoes UDP datagrams on the
same port. Each TCP connection has its own incremental frame decoder. -/

open Kernel Kernel.Net Demo

private def servicePort : UInt16 := 5005

private structure Server where
  tcp : Tcp.Endpoint := { listenPort := servicePort }
  fragments : Fragment.Cache := {}
  nextIpId : UInt32 := 0
  clients : Array (Tcp.Key × Wire.Decoder) := #[]

private def perform (request : ByteArray) : IO ByteArray := do
  if request[0]? == some 5 then
    let data := body request
    if data.size != 64 then return refusal .malformed
    let result ← Efi.report data
    return if result.size == 1024 then ok 5 result else refusal .unavailable
  match decide request with
  | .reply payload => return payload
  | .selfTest => return ok cmdSelfTest SelfTest.digest
  | .random count =>
    try return ok cmdRandom (← Platform.random count.toUSize)
    catch _ => return refusal .unavailable
  | .attest _ => return refusal .unavailable

private def removeClient (s : Server) (key : Tcp.Key) : Server :=
  { s with clients := s.clients.filter (·.1 != key) }

private partial def settle (cfg : Internet.Config) (now : Nat)
    (s : Server) (events : List Tcp.Event) : IO Server := do
  let ev :: rest := events | return s
  match ev with
  | .emit peer segment =>
    if let some frame := Internet.tcpFrame cfg peer segment then Efi.send frame
    settle cfg now s rest
  | .opened key =>
    settle cfg now { s with clients := s.clients.push (key, {}) } rest
  | .closed key => settle cfg now (removeClient s key) rest
  | .finished key =>
    let (tcp, more) := s.tcp.close now key
    settle cfg now { (removeClient s key) with tcp } (rest ++ more.toList)
  | .data key bytes =>
    let some (_, decoder) := s.clients.find? (·.1 == key) | settle cfg now s rest
    match decoder.feed bytes with
    | .error _ =>
      let (tcp, more) := s.tcp.close now key
      settle cfg now { (removeClient s key) with tcp } (rest ++ more.toList)
    | .ok (decoder, requests) =>
      let mut replies := ByteArray.empty
      for request in requests do
        let payload ← perform request
        if replies.size + payload.size + 4 > Tcp.maxQueued then
          let (tcp, more) := s.tcp.close now key
          return ← settle cfg now { (removeClient s key) with tcp } (rest ++ more.toList)
        replies := replies ++ Wire.frame payload
      let (tcp, more) := s.tcp.send now key replies
      let clients := s.clients.map fun c => if c.1 == key then (key, decoder) else c
      settle cfg now { s with tcp, clients } (rest ++ more.toList)

private def freshWord : IO UInt32 := do
  return (Wire.readU32be (← Platform.random 4) 0).toUInt32

private def input (cfg : Internet.Config) (now : Nat) (s : Server)
    (frame : ByteArray) : IO Server := do
  let (fragments, event) := s.fragments.receive now cfg frame
  let s := { s with fragments }
  match event with
  | some (.transmit answer) => Efi.send answer
  | some (.fragmentReply peer proto body) =>
    for answer in Fragment.ipFrames cfg peer proto body s.nextIpId do Efi.send answer
    return { s with nextIpId := s.nextIpId + 1 }
  | some (.udp peer src dst bytes) =>
    if dst == servicePort then
      if let some answer := Internet.udpFrame cfg peer dst src bytes then Efi.send answer
      else
        for answer in Fragment.udpFrames cfg peer dst src bytes s.nextIpId do Efi.send answer
        return { s with nextIpId := s.nextIpId + 1 }
  | some (.tcp peer segment) =>
    -- Only a new SYN needs an initial sequence number. Dropped traffic and
    -- bulk data must not consume hardware entropy.
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
  -- Announce the static IPv4 address at link-up (RFC 5227). Routers can
  -- deliver an inbound connection immediately, before the first ARP lookup.
  if let some announcement := Internet.solicit cfg cfg.ipv4 then Efi.send announcement
  Platform.write "silo: Ethernet ready, serving TCP and UDP 5005\n".toUTF8
  serve cfg {} 0
