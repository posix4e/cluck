import Evm
import Evm.Bid
import Kernel.Efi
import Kernel.Net.Tcp
import Kernel.Net.Fragment

/-! The service as a whole machine: an EFI guest on the OS's Ethernet, IP and TCP, in Intel TDX or under an
emulator. This is `TdxMain.lean` with the demo taken out. Each TCP connection carries frames (a 4-byte
big-endian length, then that many bytes); each frame is a request and is answered with one frame holding the
69 bytes of the response, and after them a TDREPORT when the request asked for one (`Evm/Attest.lean`). A
request may be far longer than a demo payload, up to `maxRequest`, and what is held of requests still on their
way in is bounded over all clients (`maxHeld`).

The machine does nothing else while a request runs: no packet is read and no timer serviced until the import
returns, which for a hard block is many seconds. A second client waits, and its TCP waits with it. -/

open Kernel Kernel.Net

private def servicePort : UInt16 := 5005

/-- The longest request accepted. A block of mainnet with its witness has been 2 to 22 MB (`TODO.md`), and
this is room for half as much again. The heap (256 MiB) has held the largest seen; what a request of this
length needs of it has not been measured. -/
private def maxRequest : Nat := 32 * 1024 * 1024

/-- The most that is held of requests still arriving, over all clients together. Each client may be part
way through a request of `maxRequest`, and eight of those would be the whole heap: a client whose next
bytes would take the total past this is closed instead. -/
private def maxHeld : Nat := 40 * 1024 * 1024

/-- What a client has sent that is not yet a whole request: the pieces as they came, and how long they are
together. A request arrives as thousands of segments, and joining each to the last as it came would copy
the request thousands of times; they are joined once, when the last is here. The first piece is never
shorter than the four bytes of the length while there are four to be had. -/
private structure Pending where
  pieces : Array ByteArray := #[]
  size : Nat := 0
  deriving Inhabited

private def Pending.add (p : Pending) (bytes : ByteArray) : Pending :=
  if bytes.isEmpty then p
  else if p.pieces.size == 1 && p.size < 4 then { pieces := #[p.pieces[0]! ++ bytes], size := p.size + bytes.size }
  else { pieces := p.pieces.push bytes, size := p.size + bytes.size }

private structure Server where
  key : Evm.Bid.Key
  tcp : Tcp.Endpoint := { listenPort := servicePort }
  fragments : Fragment.Cache := {}
  nextIpId : UInt32 := 0
  clients : Array (Tcp.Key × Pending) := #[]

private def removeClient (s : Server) (key : Tcp.Key) : Server :=
  { s with clients := s.clients.filter (·.1 != key) }

private def length (b : ByteArray) : Nat :=
  (b[0]!.toNat <<< 24) ||| (b[1]!.toNat <<< 16) ||| (b[2]!.toNat <<< 8) ||| b[3]!.toNat

private inductive Front
  /-- The request at the front is not all here. -/
  | wait
  /-- Its length is not one that is accepted. -/
  | refuse
  /-- It is here, and this is what came after it. -/
  | whole (request : ByteArray) (rest : Pending)

/-- The request at the front of what a client has sent, joined into one array of exactly its length. -/
private def Pending.front (p : Pending) : Front :=
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
    return .whole request rest

/-- The whole requests at the front of what a client has sent, and what is left. `none` when a length is
not acceptable. -/
private partial def requests (p : Pending) (out : Array ByteArray) : Option (Pending × Array ByteArray) :=
  match p.front with
  | .wait => some (p, out)
  | .refuse => none
  | .whole request rest => requests rest (out.push request)

private def frame (payload : ByteArray) : ByteArray :=
  Evm.Service.be 4 payload.size ++ payload

/-- The builder's key: drawn from the platform's randomness when the machine starts, held in this machine's
memory and nowhere else, and gone when it stops. About one draw in ten is not below the group's order and
is thrown away; sixty-four in a row would be a random source that is not one, and the machine stops. -/
private def drawKey : IO Evm.Bid.Key := do
  for _ in [0 : 64] do
    if let some key := Evm.Bid.keyOf (← Platform.random 32) then return key
  throw (IO.userError "no key could be drawn")

/-- Any request: one for a bid or for the builder's key, which need the key, or one of the others. A
request for a bid may name the milliseconds it allows for transactions, counted from here, where the whole
request has arrived; this machine's clock is what says they have run out. -/
private def serveWith (key : Evm.Bid.Key) (request : ByteArray) : IO ByteArray := do
  if !Evm.Bid.mine request then return ← IO.lazyPure fun _ => Evm.serve request
  let allowed := Evm.Bid.allowed request
  let stopAt := (← Efi.millis).toNat + allowed
  let over : IO Bool := if allowed == 0 then pure false else do return (← Efi.millis).toNat ≥ stopAt
  Evm.Bid.serveWith over key request

/-- The response to one frame, and after it the TDREPORT that binds it to the frame when the frame asked for
one and this machine can make one (`Evm.Attest`). -/
private def answer (key : Evm.Bid.Key) (request : ByteArray) : IO ByteArray := do
  match Evm.Attest.asked? request with
  | none => serveWith key request
  | some asked =>
    let reply ← serveWith key (Evm.Attest.request asked)
    let report ← Efi.report (Evm.Attest.reportData asked reply)
    return if report.size == 1024 then reply ++ report else reply

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
    let some i := s.clients.findIdx? (·.1 == key) | settle cfg now s rest
    -- The client's pieces are taken out of the table while they are added to: held in two places, every
    -- segment would copy the list of them.
    let clients := s.clients
    let s := { s with clients := #[] }
    let pending := clients[i]!.2
    let clients := clients.set! i (key, {})
    let others := clients.foldl (fun held client => held + client.2.size) 0
    let gathered :=
      if others + pending.size + bytes.size > maxHeld then none else requests (pending.add bytes) #[]
    match gathered with
    | none =>
      let (tcp, more) := s.tcp.close now key
      settle cfg now { (removeClient { s with clients } key) with tcp } (rest ++ more.toList)
    | some (pending, whole) =>
      let mut replies := ByteArray.empty
      for request in whole do
        Platform.write s!"evm: request of {request.size} bytes\n".toUTF8
        let started ← Efi.millis
        let reply ← answer s.key request
        let ended ← Efi.millis
        let attested := if reply.size > 69 then ", with a report" else ""
        Platform.write s!"evm: status {reply[0]!}, {(ended - started).toNat} ms{attested}\n".toUTF8
        replies := replies ++ frame reply
      -- The clock moved while the service ran; the stack is told the time it is now.
      let after ← Efi.millis
      let now := if whole.isEmpty then now else after.toNat
      let (tcp, more) := s.tcp.send now key replies
      settle cfg now { s with tcp, clients := clients.set! i (key, pending) } (rest ++ more.toList)

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
  let key ← drawKey
  Platform.write "evm: Ethernet ready, serving TCP 5005\n".toUTF8
  serve cfg { key } 0
