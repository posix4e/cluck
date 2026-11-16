/-! # The vsock stream protocol

The only wire between an enclave and the instance it runs on is a virtio socket device. This is the protocol
spoken over it, as a pure function: packets in, packets and events out. Nothing here touches a device; the
driver underneath moves whole packets and this decides what they mean.

Every byte that arrives was chosen by the parent instance, which the enclave does not trust. So the rules
are: a packet that is not well-formed is dropped; a packet for a connection that does not exist is answered
with a reset; a packet that breaks the protocol on a connection that does exist ends that connection. No
input can make the tables grow past a fixed bound, and nothing is indexed without its length being checked.

The layout and the numbers are virtio's (the socket device, as in Linux's `virtio_vsock.h`): a 44-byte
little-endian header, then the payload. Only stream sockets are spoken. -/

namespace Kernel.Vsock

/-! ## Bytes -/

/-- `value` appended as `width` little-endian bytes. -/
def putLE (out : ByteArray) (value width : Nat) : ByteArray :=
  (List.range width).foldl (fun out i => out.push (value >>> (8 * i)).toUInt8) out

/-- The `width` little-endian bytes at `offset`. Only called with `offset + width ≤ b.size`. -/
def getLE (b : ByteArray) (offset width : Nat) : Nat :=
  (List.range width).foldl (fun acc i => acc ||| (b[offset + i]!.toNat <<< (8 * i))) 0

/-! ## Packets -/

def headerSize : Nat := 44

def typeStream : UInt16 := 1

def opRequest : UInt16 := 1
def opResponse : UInt16 := 2
def opRst : UInt16 := 3
def opShutdown : UInt16 := 4
def opRw : UInt16 := 5
def opCreditUpdate : UInt16 := 6
def opCreditRequest : UInt16 := 7

/-- Shutdown flags: the sender will receive no more, will send no more. -/
def shutdownRcv : UInt32 := 1
def shutdownSend : UInt32 := 2

structure Header where
  srcCid : UInt64
  dstCid : UInt64
  srcPort : UInt32
  dstPort : UInt32
  /-- Length of the payload that follows. -/
  len : UInt32
  type : UInt16
  op : UInt16
  flags : UInt32
  /-- The sender's receive buffer, in bytes. -/
  bufAlloc : UInt32
  /-- How many bytes the sender has taken out of that buffer so far, modulo 2^32. -/
  fwdCnt : UInt32
  deriving BEq, Repr, Inhabited

def Header.encode (h : Header) : ByteArray :=
  ByteArray.empty
    |> (putLE · h.srcCid.toNat 8) |> (putLE · h.dstCid.toNat 8)
    |> (putLE · h.srcPort.toNat 4) |> (putLE · h.dstPort.toNat 4)
    |> (putLE · h.len.toNat 4) |> (putLE · h.type.toNat 2) |> (putLE · h.op.toNat 2)
    |> (putLE · h.flags.toNat 4) |> (putLE · h.bufAlloc.toNat 4) |> (putLE · h.fwdCnt.toNat 4)

/-- The header at the start of `b`. Only called with `headerSize ≤ b.size`. -/
def Header.decode (b : ByteArray) : Header where
  srcCid := (getLE b 0 8).toUInt64
  dstCid := (getLE b 8 8).toUInt64
  srcPort := (getLE b 16 4).toUInt32
  dstPort := (getLE b 20 4).toUInt32
  len := (getLE b 24 4).toUInt32
  type := (getLE b 28 2).toUInt16
  op := (getLE b 30 2).toUInt16
  flags := (getLE b 32 4).toUInt32
  bufAlloc := (getLE b 36 4).toUInt32
  fwdCnt := (getLE b 40 4).toUInt32

structure Packet where
  header : Header
  payload : ByteArray
  deriving Inhabited

def Packet.encode (p : Packet) : ByteArray := p.header.encode ++ p.payload

/-- What the device handed over, as a packet: a whole header, followed by exactly the payload it announces.
Anything else is not a packet. -/
def Packet.decode? (raw : ByteArray) : Option Packet :=
  if raw.size < headerSize then none else
  let header := Header.decode raw
  if raw.size - headerSize != header.len.toNat then none else
  some { header, payload := raw.extract headerSize raw.size }

/-! ## Connections -/

/-- Which connection a packet belongs to: who the peer is, and the port at each end. -/
structure Key where
  peerCid : UInt64
  peerPort : UInt32
  localPort : UInt32
  deriving BEq, Repr, Inhabited

inductive Phase where
  /-- We asked to connect and are waiting for the answer. -/
  | connecting
  | established
  /-- We said we are done and are waiting for the peer's reset. -/
  | closing
  deriving BEq, Repr, Inhabited

structure Conn where
  key : Key
  phase : Phase
  /-- Bytes received and handed on, modulo 2^32: our `fwd_cnt`. Data is handed on as it arrives, so our
  receive buffer is always empty. -/
  received : UInt32 := 0
  /-- `received` as of the last packet we sent: what the peer knows. -/
  advertised : UInt32 := 0
  /-- Bytes sent, modulo 2^32. -/
  sent : UInt32 := 0
  /-- The peer's receive buffer and how much of what we sent it has taken out, from its latest packet. -/
  peerBufAlloc : UInt32 := 0
  peerFwdCnt : UInt32 := 0
  /-- The peer has said it will send no more, will receive no more. -/
  peerDoneSending : Bool := false
  peerDoneReceiving : Bool := false
  deriving Repr, Inhabited

/-- How many more bytes the peer has said it can take. The counters wrap; a peer whose numbers make no sense
(more outstanding than its buffer holds) gets nothing more. -/
def Conn.peerFree (c : Conn) : Nat :=
  let outstanding := (c.sent - c.peerFwdCnt).toNat
  c.peerBufAlloc.toNat - outstanding

/-- One end of the vsock device: our address, the one port we accept connections on, and the connections
that exist. -/
structure Endpoint where
  cid : UInt64
  listenPort : UInt32
  /-- The receive buffer we tell peers we have. A single packet may not carry more. -/
  bufAlloc : UInt32 := 65536
  /-- The most connections that may exist at once. -/
  maxConns : Nat := 4
  conns : Array Conn := #[]
  deriving Repr, Inhabited

/-- What the caller has to act on. -/
inductive Event where
  /-- Hand this packet to the device. -/
  | send (packet : ByteArray)
  /-- A connection now exists: one we accepted, or one of ours that was answered. -/
  | opened (key : Key)
  /-- Bytes arrived on a connection. -/
  | data (key : Key) (bytes : ByteArray)
  /-- The peer will send no more on this connection; it may still be reading. -/
  | finished (key : Key)
  /-- The connection is gone. -/
  | closed (key : Key)

def Endpoint.find? (e : Endpoint) (key : Key) : Option (Nat × Conn) :=
  (List.range e.conns.size).findSome? fun i =>
    match e.conns[i]? with
    | some c => if c.key == key then some (i, c) else none
    | none => none

def Endpoint.put (e : Endpoint) (i : Nat) (c : Conn) : Endpoint :=
  { e with conns := e.conns.setIfInBounds i c }

def Endpoint.remove (e : Endpoint) (key : Key) : Endpoint :=
  { e with conns := e.conns.filter (·.key != key) }

/-- A packet of ours on connection `c`. Every packet carries our buffer size and how much we have taken, so
sending one brings the peer up to date. -/
def Endpoint.packet (e : Endpoint) (c : Conn) (op : UInt16) (flags : UInt32 := 0)
    (payload : ByteArray := ByteArray.empty) : ByteArray × Conn :=
  let header : Header := {
    srcCid := e.cid, dstCid := c.key.peerCid, srcPort := c.key.localPort, dstPort := c.key.peerPort,
    len := payload.size.toUInt32, type := typeStream, op, flags, bufAlloc := e.bufAlloc, fwdCnt := c.received }
  (Packet.encode { header, payload }, { c with advertised := c.received })

/-- The answer to a packet that belongs to no connection: a reset back where it came from. A reset is never
answered with a reset, or two confused ends would do it forever. -/
def Endpoint.refuse (e : Endpoint) (h : Header) : Array Event :=
  if h.op == opRst then #[] else
  let header : Header := {
    srcCid := e.cid, dstCid := h.srcCid, srcPort := h.dstPort, dstPort := h.srcPort,
    len := 0, type := h.type, op := opRst, flags := 0, bufAlloc := 0, fwdCnt := 0 }
  #[.send header.encode]

/-- Ends a connection that exists: tells the peer, forgets it, tells the caller. -/
def Endpoint.abort (e : Endpoint) (c : Conn) : Endpoint × Array Event :=
  let (packet, _) := e.packet c opRst
  (e.remove c.key, #[.send packet, .closed c.key])

/-- A packet on an established connection, or one we are closing. -/
def Endpoint.onConnected (e : Endpoint) (i : Nat) (c : Conn) (p : Packet) : Endpoint × Array Event :=
  let op := p.header.op
  if op == opRst then
    (e.remove c.key, #[.closed c.key])
  else if op == opRw then
    -- Our buffer is always empty, so the only way to overrun it is one packet larger than all of it.
    if p.payload.size > e.bufAlloc.toNat || c.peerDoneSending then e.abort c else
    let c := { c with received := c.received + p.payload.size.toUInt32 }
    let events : Array Event := if c.phase == .established && !p.payload.isEmpty then #[.data c.key p.payload] else #[]
    -- Tell the peer its bytes were taken before it could run out of room by its own count.
    if (c.received - c.advertised).toNat * 2 ≥ e.bufAlloc.toNat then
      let (packet, c) := e.packet c opCreditUpdate
      (e.put i c, events.push (.send packet))
    else
      (e.put i c, events)
  else if op == opCreditUpdate then
    (e.put i c, #[])
  else if op == opCreditRequest then
    let (packet, c) := e.packet c opCreditUpdate
    (e.put i c, #[.send packet])
  else if op == opShutdown then
    let c := { c with
      peerDoneSending := c.peerDoneSending || (p.header.flags &&& shutdownSend) != 0
      peerDoneReceiving := c.peerDoneReceiving || (p.header.flags &&& shutdownRcv) != 0 }
    if c.peerDoneSending && c.peerDoneReceiving then
      -- Nothing more can pass either way. The reset is the acknowledgement the peer waits for.
      e.abort c
    else if c.peerDoneSending && c.phase == .established then
      (e.put i c, #[.finished c.key])
    else
      (e.put i c, #[])
  else
    -- A second request, an answer nobody asked for, or an operation that does not exist.
    e.abort c

/-- A packet on a connection we asked for and have not heard back about. -/
def Endpoint.onConnecting (e : Endpoint) (i : Nat) (c : Conn) (p : Packet) : Endpoint × Array Event :=
  if p.header.op == opResponse then
    (e.put i { c with phase := .established }, #[.opened c.key])
  else if p.header.op == opRst then
    (e.remove c.key, #[.closed c.key])
  else
    e.abort c

/-- A packet for no connection we have. A request for the port we listen on makes one, if there is room. -/
def Endpoint.onUnknown (e : Endpoint) (key : Key) (p : Packet) : Endpoint × Array Event :=
  if p.header.op != opRequest || key.localPort != e.listenPort then (e, e.refuse p.header) else
  -- A connection we are closing only waits for a reset that may never come; it does not keep a newcomer out.
  let e := if e.conns.size < e.maxConns then e else { e with conns := e.conns.filter (·.phase != .closing) }
  if e.conns.size ≥ e.maxConns then (e, e.refuse p.header) else
  let c : Conn := { key, phase := .established, peerBufAlloc := p.header.bufAlloc, peerFwdCnt := p.header.fwdCnt }
  let (packet, c) := e.packet c opResponse
  ({ e with conns := e.conns.push c }, #[.send packet, .opened key])

/-- One packet from the device. -/
def Endpoint.receive (e : Endpoint) (raw : ByteArray) : Endpoint × Array Event :=
  match Packet.decode? raw with
  | none => (e, #[])
  | some p =>
    let h := p.header
    if h.dstCid != e.cid then (e, #[]) else
    let key : Key := { peerCid := h.srcCid, peerPort := h.srcPort, localPort := h.dstPort }
    match e.find? key with
    | none => if h.type != typeStream then (e, e.refuse h) else e.onUnknown key p
    | some (i, c) =>
      if h.type != typeStream then e.abort c else
      -- Every packet says how much room its sender has.
      let c := { c with peerBufAlloc := h.bufAlloc, peerFwdCnt := h.fwdCnt }
      match c.phase with
      | .connecting => e.onConnecting i c p
      | .established | .closing => e.onConnected i c p

/-- The most payload one of our packets carries. -/
def maxPayload : Nat := 4096

/-- Sends as much of `bytes` as the peer has room for, and returns how many bytes that was. Zero means wait
for the peer to say it has taken some; `askForRoom` prompts it. -/
def Endpoint.write (e : Endpoint) (key : Key) (bytes : ByteArray) : Endpoint × Array Event × Nat :=
  match e.find? key with
  | none => (e, #[], 0)
  | some (i, c) =>
    if c.phase != .established || c.peerDoneReceiving then (e, #[], 0) else
    let total := min bytes.size c.peerFree
    let rec go (fuel : Nat) (c : Conn) (offset : Nat) (events : Array Event) : Conn × Array Event :=
      match fuel with
      | 0 => (c, events)
      | fuel + 1 =>
        if offset ≥ total then (c, events) else
        let size := min maxPayload (total - offset)
        let (packet, c) := e.packet c opRw 0 (bytes.extract offset (offset + size))
        go fuel { c with sent := c.sent + size.toUInt32 } (offset + size) (events.push (.send packet))
    let (c, events) := go (total / maxPayload + 1) c 0 #[]
    (e.put i c, events, total)

/-- Asks the peer to say how much room it has. -/
def Endpoint.askForRoom (e : Endpoint) (key : Key) : Endpoint × Array Event :=
  match e.find? key with
  | none => (e, #[])
  | some (i, c) =>
    let (packet, c) := e.packet c opCreditRequest
    (e.put i c, #[.send packet])

/-- Asks to connect to `key.peerPort` at `key.peerCid` from `key.localPort`. `false` if that connection
already exists or there is no room for another; nothing was sent and nothing changed. Otherwise the answer
arrives later, as `opened` or `closed`. -/
def Endpoint.connect (e : Endpoint) (key : Key) : Endpoint × Array Event × Bool :=
  if (e.find? key).isSome || e.conns.size ≥ e.maxConns then (e, #[], false) else
  let c : Conn := { key, phase := .connecting }
  let (packet, c) := e.packet c opRequest
  ({ e with conns := e.conns.push c }, #[.send packet], true)

/-- Says we are done with a connection, both ways. It is gone once the peer's reset arrives. -/
def Endpoint.close (e : Endpoint) (key : Key) : Endpoint × Array Event :=
  match e.find? key with
  | none => (e, #[])
  | some (i, c) =>
    if c.phase == .closing then (e, #[]) else
    let (packet, c) := e.packet c opShutdown (shutdownRcv ||| shutdownSend)
    (e.put i { c with phase := .closing }, #[.send packet])

end Kernel.Vsock
