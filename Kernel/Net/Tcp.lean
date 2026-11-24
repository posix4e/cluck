import Kernel.Net.Address

/-! A bounded TCP stream endpoint. Checksums and Ethernet delivery belong to the IP layer.
The caller supplies a fresh initial sequence number for each connection and a monotonic time in
milliseconds.

Taking in: a large window is offered, with the scaling option when the peer has it, so that megabytes
arrive in a few round trips; bytes go to the caller as they come in order and are never held here, so
the window is always wholly open. Segments that come ahead of a gap are kept, in order, up to
`maxEarly` of them a connection and `maxEarlyBytes` over all connections, and every one is answered
with an acknowledgement of where the gap is, which is what tells the sender to send again.

Sending: up to `maxQueued` bytes a connection wait here until they are acknowledged. As many segments
go as the peer's window and a window of our own allow; ours opens as acknowledgements come and closes
on loss (RFC 5681), a segment is sent again when three acknowledgements repeat (RFC 6582, without
selective acknowledgements) or when a timer measured from the path runs out (RFC 6298, with a floor
of 200 ms). SYN and FIN go one at a time, as before, each with its own timer from a second. -/

namespace Kernel.Net.Tcp

open Internet (Peer)

def fin : UInt8 := 1
def syn : UInt8 := 2
def rst : UInt8 := 4
def psh : UInt8 := 8
def ack : UInt8 := 16

def maxQueued : Nat := 131072
def maxConnections : Nat := 32
/-- Segments kept from ahead of a gap, a connection; and their bytes, over all connections. -/
def maxEarly : Nat := 2048
def maxEarlyBytes : Nat := 4 * 1024 * 1024
/-- The most our own sending window is ever worth: more than can wait here to be sent. -/
def maxFlight : Nat := 2 * maxQueued

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
  /-- As it is on the wire: shifted, on all but a SYN, by what the connection agreed. -/
  window : UInt16 := 8192
  mss : Option UInt16 := none
  /-- The window scaling option: how far the sender's later windows are shifted. -/
  scale : Option UInt8 := none
  data : ByteArray := .empty
  deriving Inhabited

def Segment.has (s : Segment) (flag : UInt8) : Bool := s.flags &&& flag != 0

def Segment.length (s : Segment) : Nat :=
  s.data.size + (if s.has syn then 1 else 0) + (if s.has fin then 1 else 0)

/-- The checksum field is filled by the IP layer after it selects the source address. -/
def Segment.encode (s : Segment) : ByteArray :=
  let options := match s.mss with
    | none => ByteArray.empty
    | some n => put16 (ByteArray.empty.push 2 |>.push 4) n
  let options := match s.scale with
    | none => options
    | some k => options.push 1 |>.push 3 |>.push 3 |>.push k
  let b := put32 (put32 (put16 (put16 .empty s.src) s.dst) s.seq) s.answer
  let b := put32 (put16 (b.push ((5 + options.size / 4).toUInt8 <<< (4 : UInt8)) |>.push s.flags) s.window) 0
  b ++ options ++ s.data

/-- Length-delimited TCP options. A missing or zero length can never advance the cursor. -/
private def parseOptions (b : ByteArray) (stop : Nat) :
    Nat → Nat → Option UInt16 → Option UInt8 → Option (Option UInt16 × Option UInt8)
  | 0, _, _, _ => none
  | fuel + 1, i, mss, scale =>
    if i ≥ stop || b[i]! == 0 then some (mss, scale)
    else if b[i]! == 1 then parseOptions b stop fuel (i+1) mss scale
    else if i + 2 > stop then none else
    let n := b[i+1]!.toNat
    if n < 2 || i + n > stop then none else
    if b[i]! == 2 then
      if n != 4 || mss.isSome then none else
      let value := read16 b (i+2)
      if value == 0 then none else parseOptions b stop fuel (i+n) (some value) scale
    else if b[i]! == 3 then
      if n != 3 || scale.isSome then none else
      -- A shift of more than 14 is to be read as 14 (RFC 7323, 2.3).
      parseOptions b stop fuel (i+n) mss (some (min b[i+2]! 14))
    else parseOptions b stop fuel (i+n) mss scale

def Segment.decode? (b : ByteArray) : Option Segment := do
  if b.size < 20 || b.size > 65535 then none else
  let header := (b[12]!.toNat >>> 4) * 4
  if header < 20 || header > b.size then none else
  let (mss, scale) ← parseOptions b header 41 20 none none
  return { src := read16 b 0, dst := read16 b 2, seq := read32 b 4, answer := read32 b 8,
           flags := b[13]!, window := read16 b 14, mss, scale, data := b.extract header b.size }

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

/-- A SYN or a FIN on its way: one at a time, with no data, sent again from a second. -/
structure Flight where
  segment : Segment
  due : Nat
  retries : Nat := 0
  deriving Inhabited

structure Conn where
  key : Key
  peer : Peer
  phase : Phase
  /-- Of what we send: the first number not acknowledged, the next to send, and one past the furthest
  ever sent. `una ≤ snd ≤ top`, and `snd` is short of `top` only while sending again after the timer. -/
  una : UInt32
  snd : UInt32
  top : UInt32
  /-- The first of the peer's numbers still needed. -/
  rcv : UInt32
  /-- The peer's window in bytes, and the segment that said so. -/
  peerWindow : Nat := 0
  windowSeq : UInt32 := 0
  windowAck : UInt32 := 0
  peerMss : Nat := 536
  /-- Whether window scaling was agreed, and how far the peer's windows are shifted. -/
  scaling : Bool := false
  peerShift : UInt8 := 0
  /-- From the endpoint when the connection began: our window in bytes, the shift we offer, the largest
  segment we ask for, and how many segments go before anything is acknowledged. -/
  window : Nat
  shift : UInt8
  mss : UInt16
  burst : Nat
  flight : Option Flight := none
  /-- Bytes not yet acknowledged, those sent first: the byte numbered `una` is at `outAt`. -/
  out : ByteArray := .empty
  outAt : Nat := 0
  /-- Segments from ahead of a gap, in order of their numbers, and the bytes in them. -/
  early : Array Segment := #[]
  earlyBytes : Nat := 0
  /-- Our own window in bytes, and where it stops doubling. -/
  cwnd : Nat := 0
  ssthresh : Nat := maxFlight
  /-- Acknowledgements that repeated the last one; whether a lost segment is being recovered; and the
  number that has to be acknowledged before repeats may start another recovery. -/
  dups : Nat := 0
  fast : Bool := false
  recover : UInt32 := 0
  /-- When what is on its way is sent again if nothing is acknowledged (0: nothing is on its way), and
  how often that has happened in a row. -/
  due : Nat := 0
  retries : Nat := 0
  /-- The path's round trip in milliseconds, smoothed, and how it varies (0: not yet measured); and
  the number whose acknowledgement is being timed, with when it was sent. -/
  srtt : Nat := 0
  rttvar : Nat := 0
  timed : Option (UInt32 × Nat) := none
  closing : Bool := false
  peerFin : Bool := false
  sentFin : Bool := false
  passiveClose : Bool := false
  probeDue : Nat := 0
  touched : Nat
  deriving Inhabited

/-- Bytes handed to `send` and not yet acknowledged. -/
def Conn.held (c : Conn) : Nat := c.out.size - c.outAt

structure Endpoint where
  listenPort : UInt16
  /-- How many bytes ahead of what has come a peer may send, and the shift offered for saying so.
  Without scaling a peer is told 65,535 at the most. -/
  window : Nat := 2097152
  shift : UInt8 := 5
  /-- The largest segment to ask for over IPv4, twenty less over IPv6: the link's packet size less 40. -/
  mss : UInt16 := 1460
  /-- How many segments a new connection sends before anything is acknowledged (RFC 6928 has ten). -/
  burst : Nat := 10
  conns : Array Conn := #[]
  deriving Inhabited

private def before (a b : UInt32) : Bool := (a - b) ≥ 0x80000000

private def Endpoint.mssFor (e : Endpoint) (peer : Peer) : UInt16 := if peer.ip.size == 4 then e.mss else e.mss - 20

private def negotiatedMss (own : UInt16) (peer : Peer) (s : Segment) : Nat :=
  min own.toNat (s.mss.getD (if peer.ip.size == 4 then 536 else 1220)).toNat

/-- How far ahead of `rcv` a segment may reach: what the peer has been told. -/
private def Conn.open (c : Conn) : Nat :=
  if c.scaling then min c.window (65535 <<< c.shift.toNat) else min c.window 65535

/-- A segment of ours with no data in flight behind it: numbered from the furthest sent, which is where
the peer expects the next to be. A SYN carries our options, and offers scaling unless it answers a SYN
that did not. -/
private def Conn.packet (c : Conn) (flags : UInt8) (bytes := ByteArray.empty) : Segment :=
  let opening := flags &&& syn != 0
  { src := c.key.localPort, dst := c.key.port, seq := c.top,
    answer := if flags &&& ack != 0 then c.rcv else 0, flags, data := bytes,
    window := if opening || !c.scaling then (min c.window 65535).toUInt16
              else (min 65535 (c.window >>> c.shift.toNat)).toUInt16,
    mss := if opening then some c.mss else none,
    scale := if opening && (c.scaling || flags &&& ack == 0) then some c.shift else none }

private def Conn.emit (c : Conn) (s : Segment) : Event := .emit c.peer s.encode
private def Conn.ack (c : Conn) : Event := c.emit (c.packet Tcp.ack)

private def Endpoint.store (e : Endpoint) (c : Conn) : Endpoint :=
  { e with conns := e.conns.map fun old => if old.key == c.key then c else old }

private def Endpoint.remove (e : Endpoint) (key : Key) : Endpoint :=
  { e with conns := e.conns.filter (·.key != key) }

/-- A SYN or a FIN sent, to be sent again from a second. Nothing else is on its way when one goes. -/
private def Conn.transmit (c : Conn) (now : Nat) (s : Segment) : Conn × Event :=
  let next := c.snd + s.length.toUInt32
  ({ c with flight := some { segment := s, due := now + 1000 }, snd := next, top := next }, c.emit s)

/-- How long to wait for an acknowledgement before sending again (RFC 6298; the floor is 200 ms, as
Linux has it, where the RFC has a second). -/
private def Conn.wait (c : Conn) : Nat :=
  if c.srtt == 0 then 1000 else min 60000 (max 200 (c.srtt + 4 * c.rttvar))

/-- One round trip measured. -/
private def Conn.measure (c : Conn) (sample : Nat) : Conn :=
  let sample := max sample 1
  if c.srtt == 0 then { c with srtt := sample, rttvar := sample / 2 } else
  let apart := if c.srtt > sample then c.srtt - sample else sample - c.srtt
  { c with rttvar := (3 * c.rttvar + apart) / 4, srtt := (7 * c.srtt + sample) / 8 }

/-- The handshake done: what the SYN took is acknowledged, and its round trip is the first measured,
unless the SYN had to be sent twice. -/
private def Conn.establish (c : Conn) (now : Nat) : Conn :=
  let c := match c.flight with
    | some f => if f.retries == 0 && now + 1000 ≥ f.due then c.measure (now + 1000 - f.due) else c
    | none => c
  { c with phase := .established, flight := none, una := c.snd, recover := c.snd,
           cwnd := max 1 c.burst * c.peerMss }

/-- The first segment not acknowledged, once more. -/
private def Conn.again (c : Conn) : Event :=
  let n := min c.peerMss (min (c.top - c.una).toNat (c.out.size - c.outAt))
  c.emit { c.packet (Tcp.psh ||| Tcp.ack) (c.out.extract c.outAt (c.outAt + n)) with seq := c.una }

/-- Send what the peer's window and our own allow; with nothing on its way, probe a shut window, or
send the FIN that was waiting behind the last byte. -/
private def pump (c : Conn) (now : Nat) (events : Array Event) : Conn × Array Event := Id.run do
  if c.phase != .established || c.flight.isSome || c.sentFin then return (c, events)
  let mut c := c
  let mut events := events
  for _ in [0:1024] do
    let sent := (c.snd - c.una).toNat
    let unsent := c.out.size - c.outAt - sent
    -- WND is relative to the ACK that advertised it. A reordered window update can
    -- survive a later cumulative ACK; count only bytes inside that older right edge.
    let free := c.peerWindow - (c.snd - c.windowAck).toNat
    if unsent == 0 || free == 0 || sent ≥ c.cwnd then break
    let n := min unsent (min c.peerMss free)
    let start := c.outAt + sent
    let s := { c.packet (if n == unsent then psh ||| ack else ack) (c.out.extract start (start + n)) with seq := c.snd }
    let next := c.snd + n.toUInt32
    -- One segment at a time has its acknowledgement timed, and never one that is being sent again.
    let timed := if c.timed.isNone && c.snd == c.top then some (next, now) else c.timed
    c := { c with snd := next, top := if before c.top next then next else c.top, timed,
                  due := if c.due == 0 then now + c.wait else c.due }
    events := events.push (c.emit s)
  if c.una != c.snd then return (c, events)
  let unsent := c.out.size - c.outAt
  if unsent == 0 && !c.closing then return (c, events)
  if c.peerWindow - (c.snd - c.windowAck).toNat == 0 then
    -- Timers handle a lost window update.
    if now < c.probeDue then return (c, events)
    let probe := { c.packet ack with seq := c.snd - 1 }
    return ({ c with probeDue := now + 1000 }, events.push (c.emit probe))
  if unsent == 0 then
    let (sent, event) := c.transmit now (c.packet (fin ||| ack))
    return ({ sent with sentFin := true }, events.push event)
  return (c, events)

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
  let stop := skip + c.open
  let data := s.data.extract skip (min s.data.size stop)
  let mut c := { c with rcv := c.rcv + data.size.toUInt32 }
  let mut events := events
  if !data.isEmpty then events := events.push (.data c.key data)
  if s.has fin && s.data.size < stop then
    c := { c with rcv := c.rcv + 1, peerFin := true }
    events := events.push (.finished c.key)
  return (c, events)

/-- A segment from ahead of a gap, put in its place among those kept. One that begins where another
kept one does replaces it only if it reaches further. -/
private def Conn.keep (c : Conn) (s : Segment) : Conn := Id.run do
  let n := c.early.size
  -- Most come in order behind the gap: the end is tried first.
  let mut i := n
  if n != 0 && !before c.early[n-1]!.seq s.seq then
    i := 0
    while i < n && before c.early[i]!.seq s.seq do i := i + 1
  if i < n && c.early[i]!.seq == s.seq then
    let old := c.early[i]!
    if s.length ≤ old.length then return c
    return { c with early := c.early.set! i s, earlyBytes := c.earlyBytes - old.data.size + s.data.size }
  return { c with early := (c.early.extract 0 i).push s ++ c.early.extract i n,
                  earlyBytes := c.earlyBytes + s.data.size }

/-- What was kept from ahead of a gap, taken in as far as the gap has closed. -/
private def drain (c : Conn) (events : Array Event) : Conn × Array Event := Id.run do
  if c.early.isEmpty then return (c, events)
  let kept := c.early
  let mut c := c
  let mut events := events
  let mut taken := 0
  let mut bytes := 0
  for s in kept do
    if before c.rcv s.seq && !c.peerFin then break
    (c, events) := consume c s events
    taken := taken + 1
    bytes := bytes + s.data.size
  return ({ c with early := kept.extract taken kept.size, earlyBytes := c.earlyBytes - bytes }, events)

/-- `room` is how many more bytes may be kept from ahead of gaps, over all connections. -/
private def receiveData (c : Conn) (s : Segment) (room : Nat) (events : Array Event) : Conn × Array Event := Id.run do
  if s.data.isEmpty && !s.has fin then return (c, events)
  if before c.rcv s.seq then
    -- Never keep past our advertised right edge, nor more than the bounds.
    let dist := (s.seq - c.rcv).toNat
    let take := !c.peerFin && dist + s.length ≤ c.open && c.early.size < maxEarly && s.data.size ≤ room
    let c := if take then c.keep s else c
    return (c, events.push c.ack)
  let (c, events) := consume c s events
  let (c, events) := drain c events
  return (c, events.push c.ack)

/-- What an acknowledgement does to what we have sent. The caller has made sure it acknowledges nothing
that was never sent. -/
private def acknowledge (c : Conn) (s : Segment) (now : Nat) (events : Array Event) : Conn × Array Event := Id.run do
  let mut c := c
  let mut events := events
  let was := c.peerWindow
  let recent := before c.windowSeq s.seq || (c.windowSeq == s.seq && !before s.answer c.windowAck)
  if !before s.answer c.una && recent then
    c := { c with peerWindow := s.window.toNat <<< c.peerShift.toNat, windowSeq := s.seq, windowAck := s.answer }
  if c.flight.isSome then
    -- Only a FIN can be on its way here, and it is acknowledged whole or not at all.
    if s.answer == c.snd then c := { c with flight := none, una := c.snd }
    return (c, events)
  if before c.una s.answer then
    let acked := (s.answer - c.una).toNat
    let at_ := c.outAt + acked
    let done := at_ ≥ c.out.size
    c := { c with una := s.answer, snd := if before c.snd s.answer then s.answer else c.snd,
                  out := if done then .empty else c.out, outAt := if done then 0 else at_, retries := 0 }
    if let some (mark, sent) := c.timed then
      if !before s.answer mark then c := { c.measure (now - sent) with timed := none }
    if c.fast then
      if !before s.answer c.recover then
        c := { c with fast := false, dups := 0, cwnd := max c.peerMss c.ssthresh }
      else
        -- Short of where the recovery began: the next gap, sent at once (RFC 6582).
        c := { c with cwnd := max c.peerMss (c.cwnd - min c.cwnd acked + c.peerMss) }
        events := events.push c.again
    else
      let more := if c.cwnd < c.ssthresh then acked else max 1 (c.peerMss * c.peerMss / max 1 c.cwnd)
      c := { c with dups := 0, cwnd := min maxFlight (c.cwnd + more) }
    return ({ c with due := if c.una == c.top then 0 else now + c.wait }, events)
  -- Nothing new is acknowledged. With something on its way, an acknowledgement that repeats the last
  -- one, carries nothing and moves no window says a later segment came and an earlier one did not.
  let repeats := s.answer == c.una && c.una != c.top && s.data.isEmpty && !s.has fin &&
    c.peerWindow == was && was != 0
  if repeats then
    c := { c with dups := c.dups + 1 }
    if c.fast then c := { c with cwnd := min maxFlight (c.cwnd + c.peerMss) }
    else if c.dups == 3 && !before c.una c.recover then
      let half := max ((c.top - c.una).toNat / 2) (2 * c.peerMss)
      c := { c with fast := true, recover := c.top, ssthresh := half, cwnd := half + 3 * c.peerMss, timed := none }
      events := events.push c.again
  return (c, events)

private def complete (e : Endpoint) (c : Conn) (now : Nat) (events : Array Event) : Endpoint × Array Event :=
  if c.peerFin && c.sentFin && c.flight.isNone then
    let events := events.push (.closed c.key)
    if c.passiveClose then (e.remove c.key, events)
    else (e.store { c with phase := .timeWait, early := #[], earlyBytes := 0, touched := now }, events)
  else
    let (c, events) := pump c now events
    (e.store c, events)

/-- Whether an acknowledgement is of something never sent, or of something long gone. -/
private def Conn.stale (c : Conn) (answer : UInt32) : Bool :=
  before c.top answer || (before answer c.una && (c.una - answer).toNat > 65535)

private def synchronized (e : Endpoint) (c : Conn) (s : Segment) (now : Nat) (events : Array Event) :
    Endpoint × Array Event := Id.run do
  let first := (s.seq - c.rcv).toNat < c.open
  let coversNext := (c.rcv - s.seq).toNat < s.length
  if !first && !coversNext then
    if s.has rst then return (e, events)
    -- A segment wholly behind what has been received is answered with an ACK and otherwise dropped, but
    -- not its acknowledgement of what was sent: BSD's TCP, QEMU's among them, acknowledges bytes that
    -- reach it after its FIN by sending the FIN again, and with that dropped every such byte waited a
    -- second for its retransmission (seen on each connection out, whose last bytes follow the peer's FIN).
    let behind := (c.rcv - (s.seq + s.length.toUInt32)).toNat
    let sound := s.has ack && !s.has syn && behind ≤ 65535 && !c.stale s.answer
    if sound then
      let ackNow := c.ack
      let (c, events) := acknowledge { c with touched := now } s now (events.push ackNow)
      return complete e c now events
    return (e, events.push c.ack)
  if s.has rst then
    if s.seq != c.rcv then return (e, events.push c.ack)
    return (e.remove c.key, events.push (.closed c.key))
  if s.has syn then return (e, events.push c.ack)
  if !s.has ack then return (e, events)
  if c.stale s.answer then return (e, events.push c.ack)
  let (c, events) := acknowledge { c with touched := now } s now events
  let room := maxEarlyBytes - e.conns.foldl (· + ·.earlyBytes) 0
  let (c, events) := receiveData c s room events
  return complete e c now events

private def handshake (e : Endpoint) (c : Conn) (s : Segment) (now : Nat) : Endpoint × Array Event := Id.run do
  if c.phase == .synSent then
    if s.has ack && s.answer != c.snd then return (e, reset c.peer s)
    if s.has rst then
      if s.has ack then return (e.remove c.key, #[.closed c.key])
      return (e, #[])
    if !s.has syn || s.has fin then return (e, #[])
    let c := { c with rcv := s.seq + 1, peerWindow := s.window.toNat, windowSeq := s.seq,
                      windowAck := s.answer, peerMss := negotiatedMss c.mss c.peer s,
                      scaling := s.scale.isSome, peerShift := s.scale.getD 0, touched := now }
    if !s.has ack then
      -- Simultaneous open reuses the sequence already consumed by our SYN.
      let s' := { c.packet (syn ||| ack) with seq := c.snd - 1 }
      return (e.store { c with phase := .synReceived, flight := some { segment := s', due := now+1000 } },
              #[c.emit s'])
    let c := c.establish now
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
  let c := c.establish now
  return synchronized (e.store c) c s now #[.opened c.key]

private def Endpoint.fresh (e : Endpoint) (key : Key) (peer : Peer) (phase : Phase) (iss rcv : UInt32) (now : Nat) : Conn :=
  { key, peer, phase, una := iss, snd := iss, top := iss, rcv, window := e.window, shift := min e.shift 14,
    mss := e.mssFor peer, burst := e.burst, touched := now }

private def listen (e : Endpoint) (p : Peer) (s : Segment) (iss : UInt32) (now : Nat) :
    Endpoint × Array Event := Id.run do
  if s.dst != e.listenPort || s.has ack then return (e, reset p s)
  if s.has rst || !s.has syn || s.has fin || s.src == 0 || e.conns.size ≥ maxConnections then return (e, #[])
  let c := e.fresh ⟨p.ip, s.src, s.dst⟩ p .synReceived iss (s.seq + 1) now
  let c := { c with peerWindow := s.window.toNat, windowSeq := s.seq, peerMss := negotiatedMss c.mss p s,
                    scaling := s.scale.isSome, peerShift := s.scale.getD 0 }
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
  let c := e.fresh key peer .synSent iss 0 now
  let (c, event) := c.transmit now (c.packet syn)
  return ({ e with conns := e.conns.push c }, #[event])

def Endpoint.send (e : Endpoint) (now : Nat) (key : Key) (bytes : ByteArray) : Endpoint × Array Event := Id.run do
  let some c := e.conns.find? (·.key == key) | return (e, #[])
  if c.phase != .established || c.closing || bytes.isEmpty then return (e, #[])
  if c.held + bytes.size > maxQueued then
    return (e.remove key, #[c.emit (c.packet (rst ||| ack)), .closed key])
  let waiting := if c.outAt == 0 then c.out else c.out.extract c.outAt c.out.size
  let (c, events) := pump { c with out := waiting ++ bytes, outAt := 0 } now #[]
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
  if c.una != c.top && c.due != 0 && now ≥ c.due then
    -- Nothing was acknowledged in time: everything from the first unacknowledged byte is to be sent
    -- again, a segment at first, with the wait doubled. A peer whose window is shut is not counted
    -- against: it is probed instead, for as long as it answers.
    let shut := c.peerWindow - (c.una - c.windowAck).toNat == 0
    if c.retries ≥ 8 && !shut then return (none, #[c.emit (c.packet (rst ||| ack)), .closed c.key])
    let retries := if shut then c.retries else c.retries + 1
    let c := { c with ssthresh := max ((c.top - c.una).toNat / 2) (2 * c.peerMss), cwnd := c.peerMss,
                      snd := c.una, recover := c.top, fast := false, dups := 0, timed := none, retries,
                      due := now + min 60000 (c.wait <<< retries) }
    let (c, events) := pump c now #[]
    return (some c, events)
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
