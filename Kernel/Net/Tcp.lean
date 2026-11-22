import Kernel.Net.Address

/-! A bounded TCP stream endpoint. Checksums and Ethernet delivery belong to the IP layer.
The caller supplies a fresh initial sequence number for each connection and a monotonic time in
milliseconds. Only one segment per connection is outstanding; unacknowledged data stays available
for retransmission. The receive side acknowledges gaps and retains one out-of-order segment. -/

namespace Kernel.Net.Tcp

open Internet (Peer)

def fin : UInt8 := 1
def syn : UInt8 := 2
def rst : UInt8 := 4
def psh : UInt8 := 8
def ack : UInt8 := 16

def rxWindow : UInt16 := 8192
def maxQueued : Nat := 131072
def maxConnections : Nat := 32

private def read16 (b : ByteArray) (i : Nat) : UInt16 :=
  (b[i]!.toUInt16 <<< 8) ||| b[i+1]!.toUInt16

private def read32 (b : ByteArray) (i : Nat) : UInt32 :=
  ((read16 b i).toUInt32 <<< 16) ||| (read16 b (i+2)).toUInt32

private def put16 (b : ByteArray) (v : UInt16) : ByteArray :=
  b.push (v >>> 8).toUInt8 |>.push v.toUInt8

private def put32 (b : ByteArray) (v : UInt32) : ByteArray :=
  put16 (put16 b (v >>> 16).toUInt16) v.toUInt16

structure Segment where
  src : UInt16
  dst : UInt16
  seq : UInt32
  answer : UInt32 := 0
  flags : UInt8 := 0
  window : UInt16 := rxWindow
  mss : Option UInt16 := none
  data : ByteArray := .empty
  deriving Inhabited

def Segment.has (s : Segment) (flag : UInt8) : Bool := s.flags &&& flag != 0

def Segment.length (s : Segment) : Nat :=
  s.data.size + (if s.has syn then 1 else 0) + (if s.has fin then 1 else 0)

/-- The checksum field is filled by the IP layer after it selects the source address. -/
def Segment.encode (s : Segment) : ByteArray :=
  let b := put32 (put32 (put16 (put16 .empty s.src) s.dst) s.seq) s.answer
  let b := put32 (put16 (b.push (if s.mss.isSome then 0x60 else 0x50) |>.push s.flags) s.window) 0
  let b := match s.mss with
    | none => b
    | some n => put16 (b.push 2 |>.push 4) n
  b ++ s.data

/-- Length-delimited TCP options. A missing or zero length can never advance the cursor. -/
private def parseOptions (b : ByteArray) (stop : Nat) : Nat → Nat → Option UInt16 → Option (Option UInt16)
  | 0, _, _ => none
  | fuel + 1, i, mss =>
    if i ≥ stop || b[i]! == 0 then some mss
    else if b[i]! == 1 then parseOptions b stop fuel (i+1) mss
    else if i + 2 > stop then none else
    let n := b[i+1]!.toNat
    if n < 2 || i + n > stop then none else
    if b[i]! == 2 then
      if n != 4 || mss.isSome then none else
      let value := read16 b (i+2)
      if value == 0 then none else parseOptions b stop fuel (i+n) (some value)
    else parseOptions b stop fuel (i+n) mss

def Segment.decode? (b : ByteArray) : Option Segment := do
  if b.size < 20 || b.size > 65535 then none else
  let header := (b[12]!.toNat >>> 4) * 4
  if header < 20 || header > b.size then none else
  let mss ← parseOptions b header 41 20 none
  return { src := read16 b 0, dst := read16 b 2, seq := read32 b 4, answer := read32 b 8,
           flags := b[13]!, window := read16 b 14, mss, data := b.extract header b.size }

structure Key where
  ip : ByteArray
  port : UInt16
  localPort : UInt16
  deriving BEq, Inhabited

inductive Event where
  | emit (peer : Peer) (segment : ByteArray)
  | opened (key : Key)
  | data (key : Key) (bytes : ByteArray)
  | finished (key : Key)
  | closed (key : Key)
  deriving Inhabited

inductive Phase where
  | synSent | synReceived | established | timeWait
  deriving BEq, Inhabited

structure Flight where
  segment : Segment
  due : Nat
  retries : Nat := 0
  deriving Inhabited

structure Conn where
  key : Key
  peer : Peer
  phase : Phase
  /-- First sequence number we have not sent and first peer sequence number we still need. -/
  snd : UInt32
  rcv : UInt32
  peerWindow : UInt16 := 0
  windowSeq : UInt32 := 0
  windowAck : UInt32 := 0
  peerMss : Nat := 536
  flight : Option Flight := none
  queued : ByteArray := .empty
  queuedAt : Nat := 0
  early : Option Segment := none
  closing : Bool := false
  peerFin : Bool := false
  sentFin : Bool := false
  passiveClose : Bool := false
  probeDue : Nat := 0
  touched : Nat
  deriving Inhabited

structure Endpoint where
  listenPort : UInt16
  conns : Array Conn := #[]
  deriving Inhabited

private def before (a b : UInt32) : Bool := (a - b) ≥ 0x80000000

private def localMss (peer : Peer) : UInt16 := if peer.ip.size == 4 then 1460 else 1440

private def negotiatedMss (peer : Peer) (s : Segment) : Nat :=
  min (localMss peer).toNat (s.mss.getD (if peer.ip.size == 4 then 536 else 1220)).toNat

private def Conn.packet (c : Conn) (flags : UInt8) (bytes := ByteArray.empty) : Segment :=
  { src := c.key.localPort, dst := c.key.port, seq := c.snd,
    answer := if flags &&& ack != 0 then c.rcv else 0, flags, data := bytes,
    mss := if flags &&& syn != 0 then some (localMss c.peer) else none }

private def Conn.emit (c : Conn) (s : Segment) : Event := .emit c.peer s.encode
private def Conn.ack (c : Conn) : Event := c.emit (c.packet Tcp.ack)

private def Endpoint.store (e : Endpoint) (c : Conn) : Endpoint :=
  { e with conns := e.conns.map fun old => if old.key == c.key then c else old }

private def Endpoint.remove (e : Endpoint) (key : Key) : Endpoint :=
  { e with conns := e.conns.filter (·.key != key) }

private def Conn.transmit (c : Conn) (now : Nat) (s : Segment) : Conn × Event :=
  ({ c with flight := some { segment := s, due := now + 1000 }, snd := c.snd + s.length.toUInt32 }, c.emit s)

/-- Send a single piece in the peer's advertised window. Timers handle a lost window update. -/
private def pump (c : Conn) (now : Nat) (events : Array Event) : Conn × Array Event := Id.run do
  if c.phase != .established || c.flight.isSome || c.sentFin then return (c, events)
  if c.queued.isEmpty && !c.closing then return (c, events)
  -- WND is relative to the ACK that advertised it. A reordered window update can
  -- survive a later cumulative ACK; count only bytes inside that older right edge.
  let free := c.peerWindow.toNat - (c.snd - c.windowAck).toNat
  if free == 0 then
    if now < c.probeDue then return (c, events)
    let probe := { c.packet ack with seq := c.snd - 1 }
    return ({ c with probeDue := now + 1000 }, events.push (c.emit probe))
  if c.queued.isEmpty then
    let (c, event) := c.transmit now (c.packet (fin ||| ack))
    return ({ c with sentFin := true }, events.push event)
  let n := min (c.queued.size - c.queuedAt) (min c.peerMss free)
  let next := c.queuedAt + n
  let s := c.packet (psh ||| ack) (c.queued.extract c.queuedAt next)
  let (c, event) := c.transmit now s
  let c := if next == c.queued.size then { c with queued := .empty, queuedAt := 0 } else { c with queuedAt := next }
  return (c, events.push event)

/-- A reset is never answered with another reset. For an ACK, its ACK number becomes our sequence. -/
private def reset (p : Peer) (s : Segment) : Array Event :=
  if s.has rst then #[] else
  let response : Segment :=
    { src := s.dst, dst := s.src, seq := if s.has ack then s.answer else 0,
      answer := if s.has ack then 0 else s.seq + s.length.toUInt32,
      flags := if s.has ack then rst else rst ||| ack, window := 0 }
  #[.emit p response.encode]

/-- Drop segment-sized prefixes the peer retransmitted, retaining a FIN at the end.
Only sequence numbers near this connection's receive window can reach this function. -/
private def consume (c : Conn) (s : Segment) (events : Array Event) : Conn × Array Event := Id.run do
  if c.peerFin || before c.rcv s.seq then return (c, events)
  let skip := (c.rcv - s.seq).toNat
  if skip > s.data.size then return (c, events)
  let stop := skip + rxWindow.toNat
  let data := s.data.extract skip (min s.data.size stop)
  let mut c := { c with rcv := c.rcv + data.size.toUInt32 }
  let mut events := events
  if !data.isEmpty then events := events.push (.data c.key data)
  if s.has fin && s.data.size < stop then
    c := { c with rcv := c.rcv + 1, peerFin := true }
    events := events.push (.finished c.key)
  return (c, events)

private def receiveData (c : Conn) (s : Segment) (events : Array Event) : Conn × Array Event := Id.run do
  if s.data.isEmpty && !s.has fin then return (c, events)
  if before c.rcv s.seq then
    -- Prefer the segment closest to closing the gap. Never buffer past our advertised right edge.
    let dist := (s.seq - c.rcv).toNat
    let take := !c.peerFin && dist + s.length ≤ rxWindow.toNat &&
      (c.early.all fun saved => before s.seq saved.seq)
    let c := if take then { c with early := some s } else c
    return (c, events.push c.ack)
  let (c, events) := consume c s events
  let (c, events) := match c.early with
    | some saved =>
      if before c.rcv saved.seq && !c.peerFin then (c, events)
      else consume { c with early := none } saved events
    | none => (c, events)
  return (c, events.push c.ack)

/-- Accept partial acknowledgments as well. A later retry begins at the first unacknowledged byte. -/
private def acknowledge (c : Conn) (s : Segment) (now : Nat) : Conn := Id.run do
  let mut c := c
  let una := (c.flight.map (·.segment.seq)).getD c.snd
  let recent := before c.windowSeq s.seq || (c.windowSeq == s.seq && !before s.answer c.windowAck)
  if !before s.answer una && recent then
    c := { c with peerWindow := s.window, windowSeq := s.seq, windowAck := s.answer }
  let some f := c.flight | return c
  if !before f.segment.seq s.answer then return c
  if s.answer == c.snd then return { c with flight := none }
  let n := (s.answer - f.segment.seq).toNat
  let tail := f.segment.data.extract n f.segment.data.size
  let trimmed := { f.segment with seq := s.answer, data := tail }
  return { c with flight := some { segment := trimmed, due := now + 1000 } }

private def complete (e : Endpoint) (c : Conn) (now : Nat) (events : Array Event) : Endpoint × Array Event :=
  if c.peerFin && c.sentFin && c.flight.isNone then
    let events := events.push (.closed c.key)
    if c.passiveClose then (e.remove c.key, events)
    else (e.store { c with phase := .timeWait, early := none, touched := now }, events)
  else
    let (c, events) := pump c now events
    (e.store c, events)

private def synchronized (e : Endpoint) (c : Conn) (s : Segment) (now : Nat) (events : Array Event) :
    Endpoint × Array Event := Id.run do
  let first := (s.seq - c.rcv).toNat < rxWindow.toNat
  let coversNext := (c.rcv - s.seq).toNat < s.length
  if !first && !coversNext then
    if s.has rst then return (e, events)
    -- A segment wholly behind what has been received is answered with an ACK and otherwise dropped, but
    -- not its acknowledgement of what was sent: BSD's TCP, QEMU's among them, acknowledges bytes that
    -- reach it after its FIN by sending the FIN again, and with that dropped every such byte waited a
    -- second for its retransmission (seen on each connection out, whose last bytes follow the peer's FIN).
    let behind := (c.rcv - (s.seq + s.length.toUInt32)).toNat
    let sound := s.has ack && !s.has syn && behind ≤ 65535 &&
      !(before c.snd s.answer || (c.snd - s.answer).toNat > 65535)
    if sound then
      let c := acknowledge { c with touched := now } s now
      return complete e c now (events.push c.ack)
    return (e, events.push c.ack)
  if s.has rst then
    if s.seq != c.rcv then return (e, events.push c.ack)
    return (e.remove c.key, events.push (.closed c.key))
  if s.has syn then return (e, events.push c.ack)
  if !s.has ack then return (e, events)
  if before c.snd s.answer || (c.snd - s.answer).toNat > 65535 then return (e, events.push c.ack)
  let c := acknowledge { c with touched := now } s now
  let (c, events) := receiveData c s events
  return complete e c now events

private def handshake (e : Endpoint) (c : Conn) (s : Segment) (now : Nat) : Endpoint × Array Event := Id.run do
  if c.phase == .synSent then
    if s.has ack && s.answer != c.snd then return (e, reset c.peer s)
    if s.has rst then
      if s.has ack then return (e.remove c.key, #[.closed c.key])
      return (e, #[])
    if !s.has syn || s.has fin then return (e, #[])
    let c := { c with rcv := s.seq + 1, peerWindow := s.window, windowSeq := s.seq,
                      windowAck := s.answer, peerMss := negotiatedMss c.peer s, touched := now }
    if !s.has ack then
      -- Simultaneous open reuses the sequence already consumed by our SYN.
      let s' := { c.packet (syn ||| ack) with seq := c.snd - 1 }
      return (e.store { c with phase := .synReceived, flight := some { segment := s', due := now+1000 } },
              #[c.emit s'])
    let c := { c with phase := .established, flight := none }
    return (e.store c, #[.opened c.key, c.ack])
  if s.has rst then
    if s.seq == c.rcv then return (e.remove c.key, #[.closed c.key])
    return (e, #[])
  if s.has syn && s.seq + 1 == c.rcv && !s.has ack && !s.has fin then
    let some f := c.flight | return (e, #[])
    return (e, #[c.emit f.segment])
  if !s.has ack then return (e, #[])
  if s.seq != c.rcv then return (e, #[c.ack])
  if s.answer != c.snd then return (e, reset c.peer s)
  if s.has syn then return (e, #[c.ack])
  let c := { c with phase := .established, flight := none }
  return synchronized (e.store c) c s now #[.opened c.key]

private def listen (e : Endpoint) (p : Peer) (s : Segment) (iss : UInt32) (now : Nat) :
    Endpoint × Array Event := Id.run do
  if s.dst != e.listenPort || s.has ack then return (e, reset p s)
  if s.has rst || !s.has syn || s.has fin || s.src == 0 || e.conns.size ≥ maxConnections then return (e, #[])
  let c : Conn :=
    { key := ⟨p.ip, s.src, s.dst⟩, peer := p, phase := .synReceived, snd := iss, rcv := s.seq + 1,
      peerWindow := s.window, windowSeq := s.seq, peerMss := negotiatedMss p s, touched := now }
  let (c, event) := c.transmit now (c.packet (syn ||| ack))
  return ({ e with conns := e.conns.push c }, #[event])

/-- Receive a checksum-verified segment from the IP layer. -/
def Endpoint.receive (e : Endpoint) (now : Nat) (iss : UInt32) (p : Peer) (bytes : ByteArray) :
    Endpoint × Array Event := Id.run do
  let some s := Segment.decode? bytes | return (e, #[])
  let key : Key := ⟨p.ip, s.src, s.dst⟩
  let some c := e.conns.find? (·.key == key) | return listen e p s iss now
  if c.phase == .timeWait then
    if s.has fin && s.seq + s.length.toUInt32 == c.rcv then
      return (e.store { c with touched := now }, #[c.ack])
    return (e, if !s.has rst && s.length > 0 then #[c.ack] else #[])
  if c.phase != .established then return handshake e c s now
  return synchronized e c s now #[]

/-- Start a connection to an already resolved next hop. An existing tuple or a full table emits nothing. -/
def Endpoint.connect (e : Endpoint) (now : Nat) (iss : UInt32) (peer : Peer) (localPort remotePort : UInt16) :
    Endpoint × Array Event := Id.run do
  let key : Key := ⟨peer.ip, remotePort, localPort⟩
  if localPort == 0 || remotePort == 0 || e.conns.size ≥ maxConnections || e.conns.any (·.key == key) then
    return (e, #[])
  let c : Conn := { key, peer, phase := .synSent, snd := iss, rcv := 0, touched := now }
  let (c, event) := c.transmit now (c.packet syn)
  return ({ e with conns := e.conns.push c }, #[event])

def Endpoint.send (e : Endpoint) (now : Nat) (key : Key) (bytes : ByteArray) : Endpoint × Array Event := Id.run do
  let some c := e.conns.find? (·.key == key) | return (e, #[])
  if c.phase != .established || c.closing || bytes.isEmpty then return (e, #[])
  let inFlight := (c.flight.map (·.segment.data.size)).getD 0
  if c.queued.size - c.queuedAt + inFlight + bytes.size > maxQueued then
    return (e.remove key, #[c.emit (c.packet (rst ||| ack)), .closed key])
  let remaining := if c.queuedAt == 0 then c.queued else c.queued.extract c.queuedAt c.queued.size
  let (c, events) := pump { c with queued := remaining ++ bytes, queuedAt := 0 } now #[]
  return (e.store c, events)

def Endpoint.close (e : Endpoint) (now : Nat) (key : Key) : Endpoint × Array Event := Id.run do
  let some c := e.conns.find? (·.key == key) | return (e, #[])
  if c.phase != .established || c.closing then return (e, #[])
  let (c, events) := pump { c with closing := true, passiveClose := c.peerFin } now #[]
  return (e.store c, events)

/-- Give a connection up at once: a reset to the peer if it was open or opening, and its place freed with
no wait. For whoever opened it and no longer wants it; `close` is the orderly way. -/
def Endpoint.abort (e : Endpoint) (key : Key) : Endpoint × Array Event :=
  match e.conns.find? (·.key == key) with
  | none => (e, #[])
  | some c =>
    let said := if c.phase == .timeWait then #[]
      else if c.phase == .synSent then #[c.emit { c.packet rst with seq := c.snd }]
      else #[c.emit (c.packet (rst ||| ack))]
    (e.remove key, said.push (.closed key))

private def onTimer (c : Conn) (now : Nat) : Option Conn × Array Event := Id.run do
  if c.phase == .timeWait then
    return (if now ≥ c.touched + 120000 then none else some c, #[])
  if now ≥ c.touched + 300000 then return (none, #[c.emit (c.packet (rst ||| ack)), .closed c.key])
  if let some f := c.flight then
    if now < f.due then return (some c, #[])
    if f.retries ≥ 6 then return (none, #[c.emit (c.packet (rst ||| ack)), .closed c.key])
    let seg := { f.segment with answer := if f.segment.has ack then c.rcv else 0 }
    let retry := f.retries + 1
    let f := { f with segment := seg, retries := retry, due := now + min 60000 (1000 <<< retry) }
    return (some { c with flight := some f }, #[c.emit seg])
  let (c, events) := pump c now #[]
  return (some c, events)

/-- Retransmit lost packets, probe a zero window, and reclaim timed-out state. -/
def Endpoint.tick (e : Endpoint) (now : Nat) : Endpoint × Array Event := Id.run do
  let mut conns := #[]
  let mut events := #[]
  for c in e.conns do
    let (c, more) := onTimer c now
    if let some live := c then conns := conns.push live
    events := events ++ more
  return ({ e with conns }, events)

end Kernel.Net.Tcp
