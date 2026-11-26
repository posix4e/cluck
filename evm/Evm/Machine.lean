import Evm
import Evm.Bid
import Evm.Ask
import Evm.Send
import Evm.Seal
import Evm.Follow
import Evm.Outbound
import Kernel.Efi
import Kernel.Quote
import Kernel.Net.Wire
import Kernel.Net.Tcp
import Kernel.Net.Fragment

/-! The service as a whole machine: an EFI guest on the OS's Ethernet, IP and TCP, in Intel TDX or under an
emulator. `EfiMain.lean` and `EfiShadow.lean` are this with a list of relays each.

In: each TCP connection to port 5005 carries frames (a 4-byte big-endian length, then that many bytes);
each frame is a request and is answered with one frame, in the order the requests came. A request may be
far longer than a demo payload, up to `maxRequest`, and what is held of requests still on their way in is
bounded over all clients (`maxHeld`).

Out: the machine opens connections of its own, to the relays its image names and to nobody else
(`Evm/Relays.lean`, `Evm/Outbound.lean`). A request to ask a relay something (`Evm/Ask.lean`) starts one,
and is answered when the relay has answered or the call has failed; until then that client's later
requests wait, so that its answers stay in order, and other clients' do not.

One thing runs at a time. Everything about the network is a value (`State`) and functions on it that
never do anything but compute; the loop reads a frame, hands it to them, sends the frames they give back,
and then runs whatever request is ready. While a request runs nothing else does, with one exception: a
request to build and bid looks at the network between transactions (`pump` inside `over`), so that a
connection out does not stand still for the seconds a block takes. Any other long request still stops
everything until it returns. -/

open Kernel Kernel.Net

namespace Evm.Machine

def servicePort : UInt16 := 5005

/-- The longest request accepted. A block of mainnet with its witness has been 2 to 22 MB (`TODO.md`), and
this is room for half as much again. The heap (256 MiB) has held the largest seen; what a request of this
length needs of it has not been measured. -/
def maxRequest : Nat := 32 * 1024 * 1024

/-- The most that is held of requests still arriving, over all clients together. Each client may be part
way through a request of `maxRequest`, and eight of those would be the whole heap: a client whose next
bytes would take the total past this is closed instead. -/
def maxHeld : Nat := 40 * 1024 * 1024

/-- The most a relay's answer to a question may be: with its heading it must fit what TCP will hold of an
answer to a client at once. -/
def maxAsked : Nat := 96 * 1024

/-- What a client has sent that is not yet a whole request: the pieces as they came, and how long they are
together. A request arrives as thousands of segments, and joining each to the last as it came would copy
the request thousands of times; they are joined once, when the last is here. The first piece is never
shorter than the four bytes of the length while there are four to be had. -/
structure Pending where
  pieces : Array ByteArray := #[]
  size : Nat := 0
  /-- When the first of the pieces came, by this machine's clock; 0 when that is not known (what came
  after an earlier request on the same connection). -/
  since : Nat := 0
  deriving Inhabited

def Pending.add (p : Pending) (bytes : ByteArray) (now : Nat := 0) : Pending :=
  if bytes.isEmpty then p
  else
    let since := if p.size == 0 then now else p.since
    if p.pieces.size == 1 && p.size < 4 then { pieces := #[p.pieces[0]! ++ bytes], size := p.size + bytes.size, since }
    else { pieces := p.pieces.push bytes, size := p.size + bytes.size, since }

def length (b : ByteArray) : Nat :=
  (b[0]!.toNat <<< 24) ||| (b[1]!.toNat <<< 16) ||| (b[2]!.toNat <<< 8) ||| b[3]!.toNat

inductive Front
  /-- The request at the front is not all here. -/
  | wait
  /-- Its length is not one that is accepted. -/
  | refuse
  /-- It is here, with when its first bytes came (0 when not known), and this is what came after it. -/
  | whole (request : ByteArray) (since : Nat) (rest : Pending)

/-- The request at the front of what a client has sent, joined into one array of exactly its length. -/
def Pending.front (p : Pending) : Front :=
  if p.size < 4 then .wait else
  let n := length p.pieces[0]!
  if n == 0 || n > maxRequest then .refuse
  else if p.size < 4 + n then .wait
  else Id.run do
    let mut request := ByteArray.emptyWithCapacity n
    let mut rest : Pending := {}
    let mut skip := 4
    for piece in p.pieces do
      let start := min skip piece.size
      skip := skip - start
      let stop := min piece.size (start + (n - request.size))
      request := piece.copySlice start request request.size (stop - start)
      rest := rest.add (piece.extract stop piece.size)
    return .whole request p.since rest

def frame (payload : ByteArray) : ByteArray :=
  Evm.Service.be 4 payload.size ++ payload

/-- Someone connected to the service's port. -/
structure Client where
  key : Tcp.Key
  pending : Pending := {}
  /-- It is owed the answer to a question put to a relay, and its later requests wait for that. -/
  waiting : Bool := false
  /-- It has said it will send no more; it is let go once it has been answered. -/
  leaving : Bool := false
  deriving Inhabited

/-- A call on its way to a relay, and whom its outcome is for: a client that asked a question, or a
block being sent to several relays at once. -/
structure Job where
  call : Outbound.Call
  client : Tcp.Key
  /-- The challenge and request, when the answer is to carry a report (`Evm/Attest.lean`). -/
  asked : Option ByteArray
  started : Nat
  /-- The relay's place in the image's list. -/
  place : Nat := 0
  /-- The sending this is part of, when it carries a block. -/
  sending : Option Nat := none
  told : Bool := false

/-- A block on its way to several relays: what each has said so far, and how many are still to say. -/
structure Sending where
  id : Nat
  client : Tcp.Key
  asked : Option ByteArray
  started : Nat
  /-- The answer to the request to build and bid, or what stands in its place. -/
  bid : ByteArray
  /-- What the witness lacked for transactions left out. -/
  wanted : Array Fast.Lack := #[]
  left : Nat
  told : Array (Nat × Outbound.Outcome) := #[]
  /-- The slot the block is for, the block it is built on, and what it pays. -/
  worth : Nat × ByteArray × Nat := (0, .empty, 0)

/-- An answer ready to go to the client that waits for it, and a line about it for the console. -/
structure Finished where
  client : Tcp.Key
  asked : Option ByteArray
  started : Nat
  reply : ByteArray
  said : String

structure State where
  key : Evm.Bid.Key
  /-- The key transactions are sealed to, and those that have been (`Evm/Seal.lean`). -/
  sealing : Seal.Key
  pool : Seal.Pool := {}
  /-- The last few blocks of the chain this machine has checked for itself (`Evm/Follow.lean`). -/
  chain : Follow.Chain := {}
  relays : Relays.Table
  /-- Which engines this machine has (`Evm.Serving`). -/
  serving : Evm.Serving
  anchors : Array Tls.X509.Anchor
  wire : Outbound.Wire
  /-- The network card, when this program drives it itself (`Kernel/Net/Wire.lean`); with none, frames
  are the firmware's. It is taken out of here while it is used and put back, so that its arrays have one
  owner. -/
  card : Option Kernel.Net.Wire.Own := none
  /-- Where requests for quotes are put for the host to see (`Kernel/Quote.lean`): nowhere until the
  first, and never again once the host has left one unfinished. -/
  quoteAt : UInt64 := 0
  quoteLost : Bool := false
  /-- When the card was last asked whether it wants to be started over. -/
  lookedAt : Nat := 0
  fragments : Fragment.Cache := {}
  nextIpId : UInt32 := 0
  clients : Array Client := #[]
  jobs : Array Job := #[]
  /-- Connections to relays left open by the last block sent to each, by the relay's place in the list
  (`Outbound.Line`): at most one a relay, taken out of here while a call uses it. -/
  lines : Array (Nat × Outbound.Line) := #[]
  /-- Connections once kept that are being closed: their place in TCP is given back when the relay has
  closed too. -/
  leaving : Array Tcp.Key := #[]
  sendings : Array Sending := #[]
  nextSending : Nat := 0
  finished : Array Finished := #[]
  lastTick : Nat := 0
  /-- The best block a relay has taken from this machine for the slot it last sent for: the slot, the
  block built on, and what the block pays. A block for the same slot on the same parent that pays no
  more is not sent (`send`): a relay keeps a builder's newest, and the newest must not be the worse. -/
  best : Option (Nat × ByteArray × Nat) := none
  /-- What is kept of the requests to build that are read with what was sent before
  (`Evm.Build.Kept`): trie nodes, codes and headers whoever feeds this machine has given it, so that it
  need not give them again. Taken out of here while a request is built and put back as the request
  leaves it. -/
  kept : Evm.Build.Kept := {}

namespace State

def removeClient (s : State) (key : Tcp.Key) : State :=
  { s with clients := s.clients.filter (·.key != key) }

def words (outcome : Outbound.Outcome) : String :=
  match outcome with
  | .answered status body => s!"status {status}, {body.size} bytes"
  | .failed why => s!"no answer: {why}"

/-- A call has its outcome. A question's goes to the client that asked. A block's is kept with those of
the other relays it went to, and when the last is in they go to the client together. -/
def heard (s : State) (job : Job) (outcome : Outbound.Outcome) : State :=
  match job.sending with
  | none =>
    let reply := match outcome with
      | .answered status body => Ask.answered status body
      | .failed why => Ask.unanswered why
    let done : Finished :=
      { client := job.client, asked := job.asked, started := job.started, reply, said := s!"a relay asked: {words outcome}" }
    { s with finished := s.finished.push done }
  | some id =>
    match s.sendings.findIdx? (·.id == id), s.sendings.find? (·.id == id) with
    | some i, some sending =>
      let sending := { sending with left := sending.left - 1, told := sending.told.push (job.place, outcome) }
      if sending.left > 0 then { s with sendings := s.sendings.set! i sending }
      else
        -- In the order of the image's list, whatever order they answered in.
        let told := sending.told.qsort (fun a b => a.1 < b.1)
        let said := ", ".intercalate (told.toList.map fun (place, outcome) => s!"relay {place}: {words outcome}")
        let done : Finished :=
          { client := sending.client, asked := sending.asked, started := sending.started,
            reply := Send.answer sending.bid told sending.wanted, said := s!"a block sent: {said}" }
        -- A block some relay took is the one to beat from now on. One no relay took is not: the same
        -- block, or one that pays as much, may be sent again.
        let taken := told.any fun (_, outcome) => match outcome with
          | .answered status _ => status == 200
          | .failed _ => false
        let better := match s.best with
          | some (slot, parent, value) => !(slot == sending.worth.1 && parent == sending.worth.2.1) || sending.worth.2.2 > value
          | none => true
        { s with sendings := s.sendings.eraseIdxIfInBounds i, finished := s.finished.push done,
                 best := if taken && better then some sending.worth else s.best }
    | _, _ => s

/-- One of the calls out is told something, and what it wants sent is collected. A call that has its
outcome hands it over once; one that is over is forgotten. -/
def stepJob (s : State) (now : Nat) (i : Nat) (input : Outbound.Input) (out : Array ByteArray) : State × Array ByteArray :=
  match s.jobs[i]? with
  | none => (s, out)
  | some job =>
    let (call, wire, frames) := job.call.step now s.wire input
    let s := { s with wire }
    let (job, s) := match call.outcome?, job.told with
      | some outcome, false => ({ job with call, told := true }, s.heard job outcome)
      | _, _ => ({ job with call }, s)
    let jobs := if call.over then s.jobs.eraseIdxIfInBounds i else s.jobs.set! i job
    -- A connection the call has left open is kept for the next block to that relay.
    let lines := match call.over, call.line with
      | true, some line => s.lines.push (job.place, line)
      | _, _ => s.lines
    ({ s with jobs, lines }, out ++ frames)

/-- A kept connection given up in good order: TLS's goodbye, and this side closed. -/
def leave (s : State) (now : Nat) (line : Outbound.Line) (out : Array ByteArray) : State × Array ByteArray :=
  if !s.wire.tcp.conns.any (·.key == line.key) then (s, out) else
  let (_, bye) := line.client.close
  let (tcp, sent) := s.wire.tcp.send now line.key bye
  let (tcp, more) := tcp.close now line.key
  let s := { s with wire := { s.wire with tcp }, leaving := s.leaving.push line.key }
  (s, out ++ Outbound.frames s.wire (sent ++ more))

/-- Something happened on a kept connection while no call had it. Nothing is expected on one: a relay
that closes it is answered in kind, and so is one that sends anything TLS does not take in silence. -/
def onLine (s : State) (now : Nat) (i : Nat) (event : Tcp.Event) (out : Array ByteArray) : State × Array ByteArray :=
  match s.lines[i]? with
  | none => (s, out)
  | some (place, line) =>
    let s := { s with lines := s.lines.eraseIdxIfInBounds i }
    match event with
    | .data _ bytes =>
      let step := line.client.receive bytes
      if step.client.stage == .ready && step.data.isEmpty && step.send.isEmpty then
        ({ s with lines := s.lines.push (place, { line with client := step.client }) }, out)
      else s.leave now { line with client := step.client } out
    | .finished _ => s.leave now line out
    | .closed key =>
      let (tcp, _) := s.wire.tcp.abort key
      ({ s with wire := { s.wire with tcp } }, out)
    | _ => ({ s with lines := s.lines.push (place, line) }, out)

/-- Every call out is told the same thing. -/
def stepJobs (s : State) (now : Nat) (input : Outbound.Input) (out : Array ByteArray) : State × Array ByteArray :=
  -- From the last to the first, so that one forgotten on the way does not move those still to come.
  (List.range s.jobs.size).reverse.foldl (fun (s, out) i => s.stepJob now i input out) (s, out)

/-- Bytes from a client, added to what it has sent. False when that would be more than is held, and the
client is to be closed. The client's pieces are taken out of the table while they are added to: held in
two places, every segment would copy the list of them. -/
def addData (s : State) (key : Tcp.Key) (bytes : ByteArray) (now : Nat := 0) : State × Bool :=
  let clients := s.clients
  let s := { s with clients := #[] }
  match clients.findIdx? (·.key == key) with
  | none => ({ s with clients }, true)
  | some i =>
    let client := clients[i]!
    let clients := clients.set! i default
    let pending := client.pending
    let client := { client with pending := {} }
    let others := clients.foldl (fun held other => held + other.pending.size) 0
    if others + pending.size + bytes.size > maxHeld then ({ s with clients := clients.set! i client }, false)
    else ({ s with clients := clients.set! i { client with pending := pending.add bytes now } }, true)

/-- What TCP reported, acted on: frames collected for sending, a call out told of its own connection, a
client's bytes kept. No request is run here. -/
partial def settle (s : State) (now : Nat) (events : List Tcp.Event) (out : Array ByteArray) : State × Array ByteArray :=
  match events with
  | [] => (s, out)
  | .emit peer segment :: rest =>
    settle s now rest (match Internet.tcpFrame s.wire.cfg peer segment with | some frame => out.push frame | none => out)
  | event :: rest =>
    let key := match event with
      | .opened key | .data key _ | .finished key | .closed key => key
      | .emit peer _ => ⟨peer.ip, 0, 0⟩
    match s.jobs.findIdx? (·.call.key? == some key) with
    | some i =>
      let (s, out) := s.stepJob now i (.tcp event) out
      settle s now rest out
    | none =>
      if let some i := s.lines.findIdx? (·.2.key == key) then
        let (s, out) := s.onLine now i event out
        settle s now rest out
      else if s.leaving.contains key then
        -- Whatever else comes on a connection being closed is dropped; closed on both sides, its place
        -- is given back at once, as a call's is (`Outbound.Call.step`).
        match event with
        | .closed _ =>
          let (tcp, _) := s.wire.tcp.abort key
          settle { s with leaving := s.leaving.filter (· != key), wire := { s.wire with tcp } } now rest out
        | _ => settle s now rest out
      else
      match event with
      | .opened key => settle { s with clients := s.clients.push { key } } now rest out
      | .closed key => settle (s.removeClient key) now rest out
      | .finished key =>
        settle { s with clients := s.clients.map fun (c : Client) => if c.key == key then { c with leaving := true } else c } now rest out
      | .data key bytes =>
        let (s, kept) := s.addData key bytes now
        if kept then settle s now rest out
        else
          let (tcp, more) := s.wire.tcp.close now key
          settle { (s.removeClient key) with wire := { s.wire with tcp } } now (rest ++ more.toList) out
      | .emit _ _ => settle s now rest out

/-- A frame off the wire, as far as putting its pieces together: what it turned out to be. -/
def reassemble (s : State) (now : Nat) (frame : ByteArray) : Option Internet.Event × State :=
  let (fragments, event) := s.fragments.receive now s.wire.cfg frame
  (event, { s with fragments })

/-- What arrived, acted on. `iss` is a fresh number for a connection that is asking to be opened. -/
def onEvent (s : State) (now : Nat) (iss : UInt32) (event : Internet.Event) : Array ByteArray × State :=
  match event with
  | .transmit answer => (#[answer], s)
  | .fragmentReply peer proto body =>
    (Fragment.ipFrames s.wire.cfg peer proto body s.nextIpId, { s with nextIpId := s.nextIpId + 1 })
  | .tcp peer segment =>
    let (tcp, events) := s.wire.tcp.receive now iss peer segment
    let (s, out) := settle { s with wire := { s.wire with tcp } } now events.toList #[]
    (out, s)
  | .neighbor peer =>
    let s := { s with wire := { s.wire with neighbors := s.wire.neighbors.learn now peer } }
    let (s, out) := s.stepJobs now (.internet (.neighbor peer)) #[]
    (out, s)
  | .udp peer src dst payload =>
    let (s, out) := s.stepJobs now (.internet (.udp peer src dst payload)) #[]
    (out, s)

/-- Time passed: TCP's timers, pieces of packets grown old, and every call out. -/
def tick (s : State) (now : Nat) : Array ByteArray × State :=
  let (tcp, events) := s.wire.tcp.tick now
  let (s, out) := settle { s with wire := { s.wire with tcp }, fragments := s.fragments.expire now, lastTick := now } now events.toList #[]
  let (s, out) := s.stepJobs now .tick out
  -- Kept connections nothing has been asked on for a while are closed.
  let (old, lines) := s.lines.partition fun (_, line) => now ≥ line.since + Outbound.idle
  let (s, out) := old.foldl (fun (s, out) (_, line) => s.leave now line out) ({ s with lines }, out)
  (out, s)

/-- What there is to do next for the clients. -/
inductive Next
  | nothing
  /-- This client's request is here whole and its turn has come; `since` is when its first bytes came. -/
  | run (key : Tcp.Key) (request : ByteArray) (since : Nat)
  /-- This client sent a length that is not accepted, or is done and has been answered. -/
  | drop (key : Tcp.Key)

def next (s : State) : Next × State :=
  go s 0 s.clients.size
where
  go (s : State) (i : Nat) : Nat → Next × State
    | 0 => (.nothing, s)
    | fuel + 1 =>
      match s.clients[i]? with
      | none => (.nothing, s)
      | some client =>
        if client.waiting then go s (i + 1) fuel
        else match client.pending.front with
          | .refuse => (.drop client.key, s)
          | .whole request since rest => (.run client.key request since, { s with clients := s.clients.set! i { client with pending := rest } })
          | .wait => if client.leaving then (.drop client.key, s) else go s (i + 1) fuel

/-- A client let go: its connection closed in the orderly way. -/
def drop (s : State) (now : Nat) (key : Tcp.Key) : Array ByteArray × State :=
  let (tcp, events) := s.wire.tcp.close now key
  let (s, out) := settle { (s.removeClient key) with wire := { s.wire with tcp } } now events.toList #[]
  (out, s)

/-- An answer sent to a client. `release` when it is the answer the client's later requests waited for. -/
def reply (s : State) (now : Nat) (key : Tcp.Key) (bytes : ByteArray) (release : Bool := false) : Array ByteArray × State :=
  let (tcp, events) := s.wire.tcp.send now key bytes
  let s := { s with wire := { s.wire with tcp } }
  let s := if release then { s with clients := s.clients.map fun (c : Client) => if c.key == key then { c with waiting := false } else c } else s
  let (s, out) := settle s now events.toList #[]
  (out, s)

/-- A call out begun for a client, which waits for it. -/
def begin (s : State) (now : Nat) (key : Tcp.Key) (asked : Option ByteArray) (call : Outbound.Call) : Array ByteArray × State :=
  let s := { s with
    clients := s.clients.map fun (c : Client) => if c.key == key then { c with waiting := true } else c
    jobs := s.jobs.push { call, client := key, asked, started := now } }
  let (s, out) := s.stepJob now (s.jobs.size - 1) .tick #[]
  (out, s)

/-- A block begun on its way to relays for a client, which waits for all of them. Each call is paired
with its relay's place in the list. -/
def beginSending (s : State) (now : Nat) (key : Tcp.Key) (asked : Option ByteArray) (bid : ByteArray)
    (wanted : Array Fast.Lack) (calls : Array (Nat × Outbound.Call)) (worth : Nat × ByteArray × Nat := (0, .empty, 0)) :
    Array ByteArray × State :=
  let id := s.nextSending
  let first := s.jobs.size
  let s := { s with
    nextSending := id + 1
    clients := s.clients.map fun (c : Client) => if c.key == key then { c with waiting := true } else c
    sendings := s.sendings.push { id, client := key, asked, started := now, bid, wanted, left := calls.size, worth }
    jobs := calls.foldl (fun jobs (place, call) => jobs.push { call, client := key, asked, started := now, place, sending := some id }) s.jobs }
  -- From the last to the first, as in `stepJobs`: one that fails at once is forgotten at once.
  let (s, out) := (List.range calls.size).reverse.foldl (fun (s, out) i => s.stepJob now (first + i) .tick out) (s, #[])
  (out, s)

end State

abbrev M := StateT State IO

def transmit (frames : Array ByteArray) : M Unit := do
  if frames.isEmpty then return
  match ← modifyGet fun s => (s.card, { s with card := none }) with
  | none => for frame in frames do Efi.send frame
  | some card =>
    let card ← Kernel.Net.Wire.sendAll card frames
    modify fun s => { s with card := some card }

/-- The next frame from the network, or nothing. -/
def receive : M ByteArray := do
  match ← modifyGet fun s => (s.card, { s with card := none }) with
  | none => Efi.receive
  | some card =>
    let (card, frame) ← Kernel.Net.Wire.receive card
    modify fun s => { s with card := some card }
    return frame

/-- The card asked whether it has started over or wants to be, and brought up again if so (`Wire.mend`).
After that it is not asked for ten seconds: a card that goes on wanting it is not obeyed every second. -/
def mend : M Unit := do
  match ← modifyGet fun s => (s.card, { s with card := none }) with
  | none => pure ()
  | some card =>
    let (card, said) ← Kernel.Net.Wire.mend card
    modify fun s => { s with card := some card }
    if said != "" then
      modify fun s => { s with lookedAt := s.lookedAt + 9000 }
      Platform.write s!"evm: {said}\n".toUTF8

def freshWord : IO UInt32 := do
  let b ← Platform.random 4
  return (length b).toUInt32

/-- The builder's key: drawn from the platform's randomness when the machine starts, held in this machine's
memory and nowhere else, and gone when it stops. About one draw in ten is not below the group's order and
is thrown away; sixty-four in a row would be a random source that is not one, and the machine stops. -/
def drawKey : IO Evm.Bid.Key := do
  for _ in [0 : 64] do
    if let some key := Evm.Bid.keyOf (← Platform.random 32) then return key
  throw (IO.userError "no key could be drawn")

/-- A response, and after it the TDREPORT that binds it to what was asked, when a report was asked for
and this machine can make one (`Evm.Attest`). -/
def attested (asked : Option ByteArray) (reply : ByteArray) : IO ByteArray := do
  match asked with
  | none => return reply
  | some asked =>
    let report ← Efi.report (Evm.Attest.reportData asked reply)
    return if report.size == 1024 then reply ++ report else reply

/-- The answers relays have given, sent on to the clients that asked. -/
def deliver : M Unit := do
  let finished ← modifyGet fun s => (s.finished, { s with finished := #[] })
  for done in finished do
    let now := (← Efi.millis).toNat
    Platform.write s!"evm: {done.said}, {now - done.started} ms\n".toUTF8
    let reply ← attested done.asked done.reply
    transmit (← modifyGet (·.reply now done.client (frame reply) true))

/-- One look at the network: a frame read if there is one and acted on, the timers every 20 ms, and
relays' answers passed on. No request is run. Whether a frame was there. -/
def pump : M Bool := do
  let now := (← Efi.millis).toNat
  let frame ← receive
  if !frame.isEmpty then
    if let some event ← modifyGet (·.reassemble now frame) then
      -- A connection asking to be opened gets a first sequence number nobody could guess.
      let opening : Bool := match event with
        | .tcp _ segment => segment.size ≥ 20 && segment[13]! &&& 0x12 == 2
        | _ => false
      let iss ← if opening then (try pure (some (← freshWord)) catch _ => pure none) else pure (some 0)
      if let some iss := iss then transmit (← modifyGet (·.onEvent now iss event))
  if now ≥ (← get).lastTick + 20 then transmit (← modifyGet (·.tick now))
  if now ≥ (← get).lookedAt + 1000 then
    modify fun s => { s with lookedAt := now }
    mend
  deliver
  return !frame.isEmpty

/-- Any request but one for a relay: one for a bid or for the builder's key, which need the key, or one
of the others. A request for a bid may name the milliseconds it allows for transactions, counted from
when its first bytes arrived (`since`); this machine's clock is what says they have run out. Between
transactions it also looks at the network. -/
def buildWith (request : ByteArray) (added : ByteArray → Evm.Bid.Extra := fun _ => {}) (since : Nat := 0) : M Evm.Bid.Outcome := do
  let serving := (← get).serving
  if !Evm.Bid.mine request then return { reply := ← IO.lazyPure fun _ => serving.rest request }
  let key := (← get).key
  let allowed := Evm.Bid.allowed request
  -- Counted from the request's first bytes when that is known: whoever set the allowance set it when
  -- they began to send, and a request that was slow to arrive must not make the block late.
  let now := (← Efi.millis).toNat
  let stopAt := (if since == 0 then now else since) + allowed
  let over : M Bool := do
    let _ ← pump
    if allowed == 0 then pure false else return (← Efi.millis).toNat ≥ stopAt
  let kept ← modifyGet fun s => (s.kept, { s with kept := {} })
  let outcome ← Evm.Bid.buildWith over key request added serving.other kept
  -- Put back before anything else is done with the outcome; it is not part of what is answered.
  modify fun s => { s with kept := outcome.kept }
  return { outcome with kept := {} }

/-- A block built, bid for, and sent to relays: a call out to each relay asked for, or the answer at once
when there is nothing to send. The transactions sealed to this machine that are good for the slot are
tried with those the request proposes; if any goes in, the request's sender is not shown the block. -/
def send (key : Tcp.Key) (asked : Option ByteArray) (request : ByteArray) (since : Nat := 0) : M Unit := do
  let started := (← Efi.millis).toNat
  let finish (bid : ByteArray) (wanted : Array Fast.Lack) (why : String) : M Unit := do
    Platform.write s!"evm: a block not sent: {why}\n".toUTF8
    let reply ← attested asked (Send.answer bid #[] wanted)
    transmit (← modifyGet (·.reply (← Efi.millis).toNat key (frame reply)))
  let refused := ({ status := 5 } : Evm.Build.Response).encode
  let some r := Send.request? request | finish refused #[] "a request that cannot be read"
  if r.seconds < Relays.earliest then return ← finish refused #[] "a time before this image's roots were written down"
  -- The sealed transactions still good for this slot; those whose time is up, or whose last slot is
  -- further on than a sender may name, are dropped here. Which of
  -- them are tried depends on the block built on: those that brought proofs only on the block the
  -- proofs have been kept good at (`Follow.extra`).
  let slot := Evm.Bid.slotOf r.bid
  let (pool, chain) ← modifyGet fun s =>
    let pool : Seal.Pool := { kept := s.pool.kept.filter (·.good slot) }
    ((pool, s.chain), { s with pool })
  let built ← buildWith r.bid (Follow.extra pool chain slot) since
  let now := (← Efi.millis).toNat
  -- The console is the host's to read: it is told that sealed transactions were tried, as it knows
  -- already, and not whether any went in.
  let sealed := if built.tried then ", with sealed transactions to try" else ""
  let more := match built.wentOn with
    | some had => s!", going on from {had}"
    | none => ""
  Platform.write s!"evm: status {built.reply[0]!}, {now - started} ms{sealed}{more}\n".toUTF8
  let bid := if built.tried then Send.hidden else built.reply
  let some submission := built.submission | finish bid built.wanted "no block was built"
  -- A block for the same slot on the same parent as one a relay has already taken, paying no more, stays
  -- here: a relay keeps a builder's newest, and a block cut short by the clock, or built from a pool
  -- that has lost something, would otherwise take the better one's place.
  let beaten := match (← get).best with
    | some (slot, parent, value) => slot == built.slot && parent == built.parent && built.value ≤ value
    | none => false
  if beaten then return ← finish bid built.wanted "it pays no more than one already sent for this slot"
  -- Nor one that pays the proposer nothing: a relay refuses it, and it would only be this machine's noise.
  if built.value == 0 then return ← finish bid built.wanted "it pays the proposer nothing"
  -- Nor one ended too long after its time was up: it would reach the relay late, if at all in time.
  let allowed := Evm.Bid.allowed r.bid
  let began := if since == 0 then started else since
  if allowed != 0 && now > began + allowed + Send.grace then
    return ← finish bid built.wanted "it was ended too long after the time allowed for it"
  let relays := (← get).relays
  let anchors := (← get).anchors
  let resolver := (← get).wire.resolver
  let mut calls : Array (Nat × Outbound.Call) := #[]
  let mut kept := 0
  for place in [0:relays.relays.size] do
    if (r.relays >>> place) % 2 == 1 then
      let some relay := relays.relays[place]? | continue
      let random ← try Platform.random Outbound.randomSize.toUSize catch _ => pure .empty
      let question := Send.question relay.name submission
      -- On the connection the last block to this relay left open, if there is one; else on a new one,
      -- which is left open in its turn.
      let line ← modifyGet fun (s : State) => match s.lines.findIdx? (·.1 == place) with
        | some i => (s.lines[i]?.map (·.2), { s with lines := s.lines.eraseIdxIfInBounds i })
        | none => (none, s)
      let call := match line with
        | some line => Outbound.Call.onLine now line relay.name relay.port relay.address anchors r.seconds question random r.allowed
        | none => { Outbound.Call.start now resolver relay.name relay.port relay.address anchors r.seconds question random r.allowed with
                    keep := true }
      if line.isSome then kept := kept + 1
      calls := calls.push (place, { call with limit := 65536, bucket := Send.bucket })
  if calls.isEmpty then return ← finish bid built.wanted "no relay of this image was named"
  -- How long it is, is said only when the request's sender has the block anyway.
  let size := if built.tried then "a block" else s!"{submission.size} bytes"
  Platform.write s!"evm: sending {size} to {calls.size} relays, {kept} on connections kept\n".toUTF8
  transmit (← modifyGet (·.beginSending now key asked bid built.wanted calls (built.slot, built.parent, built.value)))

/-- A question for a relay: a call out begun, or the reason there can be none. -/
def ask (key : Tcp.Key) (asked : Option ByteArray) (request : ByteArray) : M Unit := do
  let now := (← Efi.millis).toNat
  let refuse (why : String) : M Unit := do
    Platform.write s!"evm: a relay not asked: {why}\n".toUTF8
    let reply ← attested asked (Ask.refused why)
    transmit (← modifyGet (·.reply now key (frame reply)))
  let some r := Ask.request? request | refuse "a request that cannot be read"
  let relays := (← get).relays
  let anchors := (← get).anchors
  let some relay := relays.relays[r.relay]? | refuse "no relay of that number in this image"
  if r.seconds < Relays.earliest then return ← refuse "a time before this image's roots were written down"
  let random ← try Platform.random Outbound.randomSize.toUSize catch _ => pure .empty
  if random.size != Outbound.randomSize then return ← refuse "no random bytes to be had"
  Platform.write s!"evm: asking {relay.name} for {r.path}\n".toUTF8
  let call := { Outbound.Call.start now (← get).wire.resolver relay.name relay.port relay.address anchors r.seconds
                  (Ask.question relay.name r.path) random with limit := maxAsked }
  transmit (← modifyGet (·.begin now key asked call))

/-- A quote of a report, asked of the host: the answer `Evm/Attest.lean` describes. The machine waits
for the host and does nothing else meanwhile, up to five seconds; the host is whom that costs. -/
def quote (key : Tcp.Key) (report : ByteArray) : M Unit := do
  let s ← get
  -- What is answered: the quote, or the reason there is none, which is also what the console is told.
  let (code, body, why) : UInt8 × ByteArray × String ← do
    if s.quoteLost then pure (2, .empty, "an earlier request was never finished by the host")
    else
      let at_ ← if s.quoteAt != 0 then pure s.quoteAt else Kernel.Hw.alloc Kernel.Quote.room
      modify fun s => { s with quoteAt := at_ }
      let clock : BaseIO UInt64 := do
        match ← Efi.millis.toBaseIO with
        | .ok t => pure t
        | .error _ => pure 0
      match ← Kernel.Quote.ask at_ report clock with
      | .quote bytes => pure (0, bytes, "")
      | .refused why => pure (1, .empty, why)
      | .lost =>
        modify fun s => { s with quoteLost := true }
        pure (2, .empty, "the host took the request and did not finish it")
  let body := if code == 0 then body else why.toUTF8
  Platform.write (if code == 0 then s!"evm: a quote from the host, {body.size} bytes\n" else s!"evm: no quote: {why}\n").toUTF8
  transmit (← modifyGet (·.reply (← Efi.millis).toNat key (frame (ByteArray.mk #[code] ++ body))))

/-- Every request that is ready is run, one after another. -/
partial def work : M Unit := do
  match ← modifyGet State.next with
  | .nothing => return
  | .drop key =>
    transmit (← modifyGet (·.drop (← Efi.millis).toNat key))
    work
  | .run key request since =>
    let started ← Efi.millis
    -- How long it took to arrive is said too: it has been most of what a round costs outside this work.
    Platform.write s!"evm: request of {request.size} bytes, {if since == 0 then 0 else started.toNat - since} ms in coming\n".toUTF8
    let (asked, inner) := match Evm.Attest.asked? request with
      | some asked => (some asked, Evm.Attest.request asked)
      | none => (none, request)
    if let some report := Evm.Attest.quoted? request then quote key report
    else if Ask.mine inner then ask key asked inner
    else if Send.mine inner then send key asked inner since
    else if Follow.mine inner then
      -- A block of the chain shown to the machine: checked, and if it is valid, what it wrote is kept
      -- and the proofs that sealed transactions brought are made good at it.
      let answer ← modifyGet fun s =>
        let (answer, chain, pool) := Follow.serve s.chain s.pool inner
        (answer, { s with chain, pool })
      let reply ← attested asked answer
      let ended ← Efi.millis
      Platform.write s!"evm: status {answer[0]!}, {(ended - started).toNat} ms\n".toUTF8
      transmit (← modifyGet (·.reply ended.toNat key (frame reply)))
    else if Seal.withProofs inner then
      -- A transaction sealed with its own proofs, handed in.
      let status ← modifyGet fun s =>
        let (pool, status) := Follow.handIn s.sealing s.pool s.chain inner
        (status, { s with pool })
      let reply ← attested asked (ByteArray.mk #[status])
      let ended ← Efi.millis
      Platform.write s!"evm: status {status}, {(ended - started).toNat} ms\n".toUTF8
      transmit (← modifyGet (·.reply ended.toNat key (frame reply)))
    else if Seal.mine inner then
      -- The sealing key asked for, or a sealed transaction handed in: answered at once, and nothing
      -- said on the console of what was in it.
      let answer ← modifyGet fun s => let (pool, answer) := Seal.serve s.sealing s.pool inner; (answer, { s with pool })
      let reply ← attested asked answer
      Platform.write s!"evm: status {answer[0]!}, 0 ms\n".toUTF8
      transmit (← modifyGet (·.reply (← Efi.millis).toNat key (frame reply)))
    else
      let built ← buildWith inner (since := since)
      let reply ← attested asked built.reply
      let ended ← Efi.millis
      let report := if asked.isSome && reply.size > 1024 then ", with a report" else ""
      let more := match built.wentOn with
        | some had => s!", going on from {had}"
        | none => ""
      Platform.write s!"evm: status {reply[0]!}, {(ended - started).toNat} ms{report}{more}\n".toUTF8
      transmit (← modifyGet (·.reply ended.toNat key (frame reply)))
    work

partial def serve (s : State) (quiet : Nat := 0) : IO UInt32 := do
  let (got, s) ← pump.run s
  let ((), s) ← work.run s
  -- With nothing from the network the firmware is asked for a millisecond of sleep; but not, when this
  -- program drives the card itself, until nothing has come some twenty thousand times running. A
  -- request is megabytes in a thousand frames, and a millisecond slept wherever two of them were a
  -- moment apart was a third of the time a request took to arrive.
  if got then serve s 0
  else if s.card.isSome && quiet < 20000 then
    Kernel.Hw.pause
    serve s (quiet + 1)
  else
    Efi.idle
    serve s quiet

/-- The machine, talking to the relays of `relays` and to nobody else, with the fast engine alone unless
it is given more. -/
def run (relays : Relays.Table) (serving : Evm.Serving := .builder) : IO UInt32 := do
  -- The card is this program's own to drive if it is one it knows; the firmware's driver otherwise.
  let (card, said) ← Kernel.Net.Wire.start
  if card.isSome then Platform.write s!"evm: the network card is driven from here\nevm: it is {said}\n".toUTF8
  else if said != "" then Platform.write s!"evm: the network card could not be brought up: {said}\n".toUTF8
  let mac ← match card with
    | some own => pure (Kernel.Net.Wire.mac own)
    | none => Efi.mac
  if mac.size != 6 then
    Platform.write "evm: no network: no card this program drives, and none the firmware does\n".toUTF8
    return 2
  let cfg : Internet.Config := { mac }
  -- Where the machine is follows from its card: the way out, the name server, the size of a segment.
  let wire : Outbound.Wire := match card.map Kernel.Net.Wire.around with
    | some a => { cfg, tcp := { listenPort := servicePort, mss := a.mss }, resolver := a.resolver,
                  routes := { ipv4Prefix := a.onLink, ipv4Gateway := some a.gateway } }
    | none => { cfg, tcp := { listenPort := servicePort } }
  let anchors := relays.anchors
  if anchors.size != relays.roots.size then
    Platform.write "evm: a root in this image cannot be read\n".toUTF8
    return 2
  let card ← match card, Internet.solicit cfg cfg.ipv4 with
    | some own, some announcement => do pure (some (← Kernel.Net.Wire.sendAll own #[announcement]))
    | none, some announcement => do Efi.send announcement; pure none
    | card, none => pure card
  let key ← drawKey
  -- The key transactions are sealed to: 32 bytes from the same source, which X25519 takes as they are.
  let drawn ← Platform.random 32
  if drawn.size != 32 then
    Platform.write "evm: no key for sealing could be drawn\n".toUTF8
    return 2
  let sealing := Seal.Key.of drawn
  Platform.write s!"evm: connects out only to {relays.what}\n".toUTF8
  Platform.write s!"evm: {serving.what}\n".toUTF8
  Platform.write "evm: Ethernet ready, serving TCP 5005\n".toUTF8
  serve { key, sealing, relays, serving, anchors, card, wire }

end Evm.Machine
