import Kernel.Net.Tcp
import Kernel.Net.Dns
import Tls.Client
import Tls.Http

/-! A connection out: one question put to one server over TLS, from a name to an answer.

A call goes through what a program on an ordinary system has done for it: the name looked up
(`Kernel/Net/Dns.lean`), the Ethernet address of the way out found (`Kernel/Net/Route.lean`), a TCP
connection opened (`Kernel/Net/Tcp.lean`), TLS begun on it and the server's certificate checked
(`Tls/Client.lean`), the question sent, and the answer read (`Tls/Http.lean`). Like the things it is made
of it is a value: `Call.step` is given the time and whatever happened, and gives back the call as it now
stands, the machine's network state, and Ethernet frames to send. Who reads frames off the wire and who
has the clock is the caller's business (`Machine.lean`).

Everything a call learns before TLS has checked the certificate is the word of whoever carries the
packets: the address for a name, the Ethernet address of the way out, the bytes on the connection. None of
it is believed; the certificate is what says the far end is the server that was named. So a carrier can
make a call fail and cannot make it succeed with anyone else. -/

namespace Evm.Outbound

open Kernel.Net

/-- What the machine's connections share: its addresses, its ways out, its TCP, and the Ethernet addresses
it has learned. -/
structure Wire where
  cfg : Internet.Config
  routes : Route.Table := {}
  /-- The name server asked: QEMU's unless the machine is somewhere else. -/
  resolver : ByteArray := ⟨#[10, 0, 2, 3]⟩
  tcp : Tcp.Endpoint
  neighbors : Route.Neighbors := {}

inductive Outcome where
  | answered (status : Nat) (body : ByteArray)
  | failed (why : String)

inductive Phase where
  /-- The name is being looked up. -/
  | resolving (query : Dns.Query)
  /-- The Ethernet address of the way to this address is being found. -/
  | reaching (ip : ByteArray)
  /-- A connection has been asked for. -/
  | connecting (key : Tcp.Key)
  /-- TLS is on the connection: the handshake, the question, the answer. -/
  | talking (key : Tcp.Key) (client : Tls.Client)
  /-- The answer is had and this side has closed; the server's closing is waited for. -/
  | leaving (key : Tcp.Key) (outcome : Outcome)
  | done (outcome : Outcome)

structure Call where
  /-- The server's name: what is looked up, and what its certificate must be for. -/
  host : String
  port : UInt16
  anchors : Array Tls.X509.Anchor
  /-- The time certificates are judged at, in seconds since 1970. -/
  seconds : Nat
  /-- What is sent once TLS is up. -/
  question : ByteArray
  /-- The machine's time, in milliseconds, after which the call is given up. -/
  deadline : Nat
  /-- Bytes drawn for this call alone: 32 for TLS's random, 32 for its key, 4 for TCP's first sequence
  number, 2 for the port on this side. -/
  random : ByteArray
  phase : Phase
  asked : Bool := false
  /-- Sealed bytes not yet handed to TCP, which takes only so much at a time. -/
  outbox : ByteArray := .empty
  /-- The answer so far. -/
  got : ByteArray := .empty
  /-- The server has said it will send no more. -/
  ended : Bool := false
  /-- The most the answer's body may be. -/
  limit : Nat := 1024 * 1024
  /-- What is sent is made up to a whole number of this many bytes inside TLS; 0 for as it is. -/
  bucket : Nat := 0

/-- How many random bytes a call needs. -/
def randomSize : Nat := 70

inductive Input where
  /-- Time has passed. -/
  | tick
  /-- A datagram or a neighbour's address arrived. -/
  | internet (event : Internet.Event)
  /-- Something happened on this call's own connection. -/
  | tcp (event : Tcp.Event)

def Call.outcome? (c : Call) : Option Outcome :=
  match c.phase with
  | .leaving _ outcome | .done outcome => some outcome
  | _ => none

/-- The connection a call has, while it has one. -/
def Call.key? (c : Call) : Option Tcp.Key :=
  match c.phase with
  | .connecting key | .talking key _ | .leaving key _ => some key
  | _ => none

def Call.over (c : Call) : Bool := match c.phase with | .done _ => true | _ => false

/-- The frames TCP wants sent, out of what it reported. -/
def frames (w : Wire) (events : Array Tcp.Event) : Array ByteArray :=
  events.filterMap fun
    | .emit peer segment => Internet.tcpFrame w.cfg peer segment
    | _ => none

/-- A call that failed: its connection, if it has one, is given up at once. -/
def fail (c : Call) (w : Wire) (why : String) : Call × Wire × Array ByteArray :=
  match c.key? with
  | some key =>
    let (tcp, events) := w.tcp.abort key
    ({ c with phase := .done (.failed why), outbox := .empty, got := .empty }, { w with tcp }, frames w events)
  | none => ({ c with phase := .done (.failed why) }, w, #[])

/-- As much of what is waiting as TCP has room for, handed to it. -/
def flush (c : Call) (now : Nat) (w : Wire) : Call × Wire × Array ByteArray :=
  match c.key? with
  | none => (c, w, #[])
  | some key =>
    if c.outbox.isEmpty then (c, w, #[]) else
    match w.tcp.conns.find? (·.key == key) with
    | none => (c, w, #[])
    | some conn =>
      let size := min c.outbox.size (Tcp.maxQueued - min Tcp.maxQueued conn.held)
      if size == 0 || conn.phase != .established then (c, w, #[]) else
      let (tcp, events) := w.tcp.send now key (c.outbox.extract 0 size)
      ({ c with outbox := c.outbox.extract size c.outbox.size }, { w with tcp }, frames w events)

/-- The way to `ip` found, or asked after; with it, the connection asked for. -/
def reach (c : Call) (now : Nat) (w : Wire) (ip : ByteArray) : Call × Wire × Array ByteArray :=
  let (neighbors, lookup) := w.neighbors.lookup now w.routes w.cfg ip
  let w := { w with neighbors }
  let c := { c with phase := .reaching ip }
  match lookup with
  | .pending => (c, w, #[])
  | .solicit frame => (c, w, #[frame])
  | .unreachable => fail c w "no way to the server's address"
  | .ready peer =>
    let r := c.random
    let port := (49152 + (r[68]!.toNat * 256 + r[69]!.toNat) % 16384).toUInt16
    let iss := (r.extract 64 68).foldl (fun n b => n * 256 + b.toUInt32) (0 : UInt32)
    let (tcp, events) := w.tcp.connect now iss peer port c.port
    if events.isEmpty then
      -- Said with what the table holds, since this has happened once with nothing to say why: one block
      -- in 188 found no room when at most two connections should have been open.
      let (opened, ending, opening) := w.tcp.conns.foldl (fun (held : Nat × Nat × Nat) k =>
        if k.phase == .established then (held.1 + 1, held.2.1, held.2.2)
        else if k.phase == .timeWait then (held.1, held.2.1 + 1, held.2.2)
        else (held.1, held.2.1, held.2.2 + 1)) (0, 0, 0)
      fail c w s!"no room for another connection: {w.tcp.conns.size} held ({opened} open, {ending} ended and waited out, {opening} opening), port {port}"
    else ({ c with phase := .connecting ⟨peer.ip, c.port, port⟩ }, { w with tcp }, frames w events)

/-- A call begun: nothing has been sent yet, and the first `step` sends it. With an `address` the name is
not looked up; it is still what the certificate must be for. -/
def Call.start (now : Nat) (resolver : ByteArray) (host : String) (port : UInt16) (address : Option ByteArray)
    (anchors : Array Tls.X509.Anchor) (seconds : Nat) (question random : ByteArray) (allowed : Nat := 10000) : Call :=
  let begun (phase : Phase) : Call := { host, port, anchors, seconds, question, deadline := now + allowed, random, phase }
  if random.size != randomSize then begun (.done (.failed "no random bytes for the call"))
  else match address with
  | some ip => begun (.reaching ip)
  | none =>
    -- The lookup has its own port and number, taken from the same bytes TCP's are: a call makes one
    -- lookup and then one connection, never both at once.
    let port := (49152 + (random[68]!.toNat * 256 + random[69]!.toNat) % 16384).toUInt16
    let id := (random[64]!.toNat * 256 + random[65]!.toNat).toUInt16
    match Dns.Query.start now resolver port id host .a with
    | some query => begun (.resolving query)
    | none => begun (.done (.failed "a name that cannot be looked up"))

/-- What came out of TLS, looked at: the question sent once the handshake is done, the answer read when it
is whole, the call failed when TLS refused. -/
def talk (c : Call) (now : Nat) (w : Wire) (key : Tcp.Key) (client : Tls.Client) : Call × Wire × Array ByteArray :=
  match client.stage with
  | .failed why => fail c w s!"TLS: {why}"
  | _ =>
    let (client, c) :=
      if client.stage == .ready && !c.asked then
        let (client, sealed) := client.writePadded c.question c.bucket
        (client, { c with asked := true, outbox := c.outbox ++ sealed })
      else (client, c)
    let ended := c.ended || client.stage == .closed
    match Tls.Http.response c.got ended c.limit with
    | .broken why => fail c w s!"an answer that cannot be read: {why}"
    | .more =>
      if ended then fail c w (if c.asked then "the connection ended before the answer did" else "the connection ended before TLS was up")
      else flush { c with phase := .talking key client } now w
    | .whole answer _ =>
      let (_, bye) := client.close
      let outcome := Outcome.answered answer.status answer.body
      -- The goodbye, and then this side closes. When the server has closed too the place is freed.
      let (c, w, sent) := flush { c with phase := .leaving key outcome, outbox := c.outbox ++ bye, got := .empty } now w
      let (tcp, events) := w.tcp.close now key
      (c, { w with tcp }, sent ++ frames w events)

/-- One thing happened, or time passed. -/
def Call.step (c : Call) (now : Nat) (w : Wire) (input : Input) : Call × Wire × Array ByteArray :=
  if c.over then (c, w, #[])
  else if now ≥ c.deadline then
    match c.phase with
    -- An answer was had; only the server's goodbye was being waited for.
    | .leaving key outcome =>
      let (tcp, events) := w.tcp.abort key
      ({ c with phase := .done outcome }, { w with tcp }, frames w events)
    | _ =>
      -- Said with it, for finding out why: how far the call had got and how its connection stood.
      let stage := match c.phase with
        | .resolving _ => "looking the name up"
        | .reaching _ => "finding the way there"
        | .connecting _ => "connecting"
        | .talking _ _ => if c.asked then "the question sent" else "TLS not yet up"
        | .leaving _ _ => "leaving"
        | .done _ => "done"
      let stood := match c.key? with
        | some key => match w.tcp.conns.find? (fun (conn : Tcp.Conn) => conn.key == key) with
          | some conn => conn.describe now
          | none => "the connection gone"
        | none => "no connection yet"
      fail c w s!"no answer in the time allowed ({stage}, {c.outbox.size} bytes not yet handed to TCP, {c.got.size} had; {stood})"
  else match c.phase, input with
  | .resolving query, input =>
    let event := match input with | .internet event => some event | _ => none
    let (query, action) := query.step now w.cfg w.routes event
    let c := { c with phase := .resolving query }
    (match action with
    | .wait => (c, w, #[])
    | .transmit frame => (c, w, #[frame])
    | .done (.addresses ips) =>
      match ips[(c.random[66]!.toNat) % (max ips.size 1)]? with
      | some ip => reach c now w ip
      | none => fail c w "the name has no address"
    | .done _ => fail c w "the name was not found")
  | .reaching ip, _ => reach c now w ip
  | .connecting key, .tcp (.opened _) =>
    let (client, hello) := Tls.Client.start c.host.toUTF8 c.anchors c.seconds (c.random.extract 0 32) (c.random.extract 32 64)
    flush { c with phase := .talking key client, outbox := hello } now w
  | .connecting _, .tcp (.closed _) => ({ c with phase := .done (.failed "the server refused the connection") }, w, #[])
  | .talking key client, .tcp (.data _ bytes) =>
    let step := client.receive bytes
    if c.got.size + step.data.size > c.limit + 65536 then fail c w "an answer too long"
    else talk { c with got := c.got ++ step.data, outbox := c.outbox ++ step.send } now w key step.client
  | .talking key client, .tcp (.finished _) => talk { c with ended := true } now w key client
  | .talking _ _, .tcp (.closed _) => ({ c with phase := .done (.failed "the connection was lost") }, w, #[])
  | .talking _ _, .tick => flush c now w
  | .leaving key outcome, .tcp (.closed _) =>
    -- Both sides have closed. TCP would keep the connection's place a while longer, against stray
    -- packets of an old connection being taken for a new one's; every call has a port and a first
    -- number of its own, drawn at random, so the place is given back now.
    let (tcp, _) := w.tcp.abort key
    ({ c with phase := .done outcome }, { w with tcp }, #[])
  | _, _ => (c, w, #[])

end Evm.Outbound
