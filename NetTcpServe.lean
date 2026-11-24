import Kernel.Net.Tcp
import Kernel.Net.Internet

/-! The system's TCP (`Kernel/Net/Tcp.lean`) as a process, for trying it against another TCP over a path
with delay and loss, with no machine around it: the service the builder's guest has, in its shape, and
nothing of the builder.

On standard input, frames as a network would bring them: two bytes of length, then a frame of that
length; a length of nothing means only that time has passed. On standard output, the same way, the
frames it sends. Its address is 10.0.2.15, its port 5005.

    .lake/build/bin/net-tcp-serve

A request is four bytes of length and then so many bytes, of which the first four say how many bytes the
answer is to have; the answer is four bytes of length and then that many bytes, each the low byte of its
place. So a megabyte can be sent in and a few bytes asked back, or the other way about, up to what the
TCP will hold to send (`Tcp.maxQueued`). `scripts/tcp-linux-test` drives it. -/

open Kernel Kernel.Net

structure Server where
  tcp : Tcp.Endpoint := { listenPort := 5005 }
  /-- For each connection, what has come of the request it is in the middle of. -/
  clients : Array (Tcp.Key × ByteArray) := #[]
  out : ByteArray := .empty
  requests : Nat := 0
  refused : Nat := 0

def be32 (b : ByteArray) (i : Nat) : Nat :=
  (b[i]!.toNat <<< 24) ||| (b[i+1]!.toNat <<< 16) ||| (b[i+2]!.toNat <<< 8) ||| b[i+3]!.toNat

def put32 (n : Nat) : ByteArray :=
  ByteArray.mk #[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]

/-- The whole requests at the front of `held`, answered: the answers, what is left, and how many. -/
partial def answer (held : ByteArray) (answers : ByteArray) (count : Nat) : ByteArray × ByteArray × Nat :=
  if held.size < 4 then (answers, held, count) else
  let n := be32 held 0
  if held.size < 4 + n then (answers, held, count) else
  let wanted := if n ≥ 4 then min (be32 held 4) (Tcp.maxQueued - 4 - answers.size) else 0
  let body := ByteArray.mk ((Array.range wanted).map fun i => i.toUInt8)
  answer (held.extract (4 + n) held.size) (answers ++ put32 wanted ++ body) (count + 1)

partial def settle (cfg : Internet.Config) (now : Nat) (s : Server) (events : List Tcp.Event) : Server :=
  match events with
  | [] => s
  | .emit peer segment :: rest =>
    match Internet.tcpFrame cfg peer segment with
    | some frame => settle cfg now { s with out := s.out ++ ByteArray.mk #[(frame.size >>> 8).toUInt8, frame.size.toUInt8] ++ frame } rest
    | none => settle cfg now s rest
  | .opened key :: rest => settle cfg now { s with clients := s.clients.push (key, .empty) } rest
  | .closed key :: rest => settle cfg now { s with clients := s.clients.filter (·.1 != key) } rest
  | .finished key :: rest =>
    let (tcp, more) := s.tcp.close now key
    settle cfg now { s with tcp, clients := s.clients.filter (·.1 != key) } (rest ++ more.toList)
  | .data key bytes :: rest =>
    match s.clients.find? (·.1 == key) with
    | none => settle cfg now s rest
    | some (_, held) =>
      let (answers, left, count) := answer (held ++ bytes) .empty 0
      let clients := s.clients.map fun c => if c.1 == key then (key, left) else c
      if answers.isEmpty then settle cfg now { s with clients } rest
      else
        let (tcp, more) := s.tcp.send now key answers
        settle cfg now { s with tcp, clients, requests := s.requests + count } (rest ++ more.toList)

def main : IO UInt32 := do
  let cfg : Internet.Config := { mac := ByteArray.mk #[2, 0, 0, 0, 0, 2] }
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let began ← IO.monoMsNow
  let mut s : Server := {}
  let mut opened := 0
  repeat
    let head ← stdin.read 2
    if head.size < 2 then break
    let n := head[0]!.toNat * 256 + head[1]!.toNat
    let now := (← IO.monoMsNow) - began + 1000
    if n == 0 then
      let (tcp, events) := s.tcp.tick now
      s := settle cfg now { s with tcp } events.toList
    else
      let frame ← stdin.read n.toUSize
      if frame.size < n then break
      match Internet.receive cfg frame with
      | some (.transmit reply) => s := { s with out := s.out ++ ByteArray.mk #[(reply.size >>> 8).toUInt8, reply.size.toUInt8] ++ reply }
      | some (.tcp peer segment) =>
        -- A first number for a new connection: nobody is guessing at it here.
        opened := opened + 1
        let (tcp, events) := s.tcp.receive now (now.toUInt32 * 2654435761 + opened.toUInt32) peer segment
        s := settle cfg now { s with tcp } events.toList
      | _ => pure ()
    if !s.out.isEmpty then
      stdout.write s.out
      stdout.flush
      s := { s with out := .empty }
  IO.eprintln s!"net-tcp-serve: {s.requests} requests answered, {s.tcp.conns.size} connections left open"
  return 0
