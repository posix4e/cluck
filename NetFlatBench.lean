import Kernel.Net.Flat
import Kernel.Net.Tcp

/-! How many connections a second the trial TCP (`Kernel/Net/Flat.lean`) takes on one core, with no
network card: clients made up here open a connection, send a request, take the answer and close, over and
over, and only the time spent inside the stack is counted.

    .lake/build/bin/net-flat-bench [connections] [at once] [checksums: 1 or 0] [request bytes] [answer bytes] [FILE.pcap or -]
                                   [requests a connection]

With a file named, every frame of the run, both ways, is written to it as a capture, for another program
to read and judge (`scripts/flat-capture-check`); a run for that should be a small one.

Each connection is four frames in (SYN, ACK, the request, FIN) and three out (SYN-ACK, the answer with
FIN, ACK). `at once` is how many connections are open together, which is what decides how much of the
table is out of the processor's caches.

It ends with the system's own TCP (`Kernel/Net/Tcp.lean`) put through the same exchange one connection at
a time, at the level of TCP segments, for comparison. -/

open Kernel.Net
open Kernel.Net.Flat

def clientBase : UInt32 := 0x0b000000

/-- A frame from client `cip:cport` written at `at_` in `rx`; where the next one goes. -/
def clientFrame (cfg : Tuning) (rx : ByteArray) (at_ : USize) (cip : UInt32) (cport : UInt16) (flags : UInt8)
    (seq ack : UInt32) (payload : ByteArray) : ByteArray × USize :=
  let options : USize := if flags &&& 0x02 != 0 then 4 else 0
  let segment := 20 + options + payload.usize
  let total := 34 + segment
  let rx := wr16 rx at_ total.toUInt16
  let e := at_ + 2
  let rx := wr32 (wr16 rx e 0x0200) (e + 2) 0x00000002
  let rx := wr32 (wr16 rx (e + 6) 0x0200) (e + 8) 0x00000001
  let rx := wr16 rx (e + 12) 0x0800
  let ip := e + 14
  let rx := wr16 (wr16 rx ip 0x4500) (ip + 2) (20 + segment).toUInt16
  let rx := wr16 (wr32 rx (ip + 4) 0x00004000) (ip + 8) 0x4006
  let rx := wr16 rx (ip + 10) 0
  let rx := wr32 (wr32 rx (ip + 12) cip) (ip + 16) cfg.localIp
  let t := ip + 20
  let rx := wr16 (wr16 rx t cport) (t + 2) cfg.localPort
  let rx := wr32 (wr32 rx (t + 4) seq) (t + 8) ack
  let rx := wr8 (wr8 rx (t + 12) (if options != 0 then 0x60 else 0x50)) (t + 13) flags
  let rx := wr32 (wr16 rx (t + 14) 65535) (t + 16) 0
  let rx := if options != 0 then wr16 (wr16 rx (t + 20) 0x0204) (t + 22) 1460 else rx
  let rx := if payload.isEmpty then rx else payload.copySlice 0 rx (t + 20 + options).toNat payload.size
  let rx :=
    if cfg.checksums then
      let rx := wr16 rx (ip + 10) (fold (sum16 rx ip (ip + 20) 0))
      let pseudo := (sum16 rx (ip + 12) (ip + 20) 0) + 6 + segment.toUInt64
      wr16 rx (t + 16) (fold (sum16 rx t (t + segment) pseudo))
    else rx
  (rx, at_ + 2 + total)

/-- The frames in `frames` from `o` to `stop`, each with its length before it, added to a capture. -/
partial def captured (capture : ByteArray) (frames : ByteArray) (o stop : USize) (round : UInt32) : ByteArray :=
  if o + 2 > stop then capture else
  let n := (rd16 frames o).toUSize
  let at_ := capture.usize
  let capture := capture ++ ByteArray.mk (Array.replicate 16 0)
  let capture := st32 (st32 (st32 (st32 capture at_ (round / 1000)) (at_ + 4) (round % 1000 * 1000)) (at_ + 8) n.toUInt32) (at_ + 12) n.toUInt32
  captured (capture ++ frames.extract (o + 2).toNat (o + 2 + n).toNat) frames (o + 2 + n) stop round

def flat (connections atOnce : Nat) (checksums : Bool) (requestBytes answerBytes : Nat) (capturePath : Option String := none)
    (each : Nat := 1) : IO Unit := do
  let slotBits := (Nat.log2 (4 * atOnce) + 1).max 10
  let cfg : Tuning := { slotBits := slotBits.toUSize, checksums }
  -- The application: when so many bytes have come, the one answer.
  let wanted := requestBytes.toUInt32
  let respond (_ : ByteArray) (_ length : USize) (had : UInt32) : UInt64 :=
    let got := had + length.toUInt32
    if got ≥ wanted then (if each > 1 then Flat.sendOn 0 0 else Flat.send 0 got) else Flat.more got
  let request := ByteArray.mk (Array.replicate requestBytes 0x61)
  let answers := #[ByteArray.mk (Array.replicate answerBytes 0x62)]
  -- For each client: its state (1 has sent a SYN, 2 the request, 3 its FIN), its port, its first number.
  let mut clients := zeros (16 * atOnce)
  let mut rx := zeros (atOnce * 2 * (60 + requestBytes))
  let mut rxLength : USize := 0
  for i in [0:atOnce] do
    let c := (16 * i).toUSize
    let first : UInt32 := (i.toUInt32 * 2654435761) + 12345
    clients := st32 (st32 (st32 clients c 1) (c + 4) 1024) (c + 8) first
    (rx, rxLength) := clientFrame cfg rx rxLength (clientBase + i.toUInt32) 1024 0x02 first 0 .empty
  let mut t := Flat.table cfg
  -- Room for every client's answer at once, a frame's heading for each segment of it.
  let mut tx := Flat.outbox (atOnce * (answerBytes + 64 * (answerBytes / 1000 + 2)))
  let mut done := 0
  let mut spent := 0
  let mut framesIn := 0
  let mut framesOut := 0
  let mut now : UInt32 := (1 : UInt32) <<< 20
  let mut pendingIn := atOnce
  -- A capture's heading: microseconds, Ethernet.
  let mut capture := st32 (st32 (st32 (st32 (Flat.zeros 24) 0 0xa1b2c3d4) 4 0x00040002) 16 65535) 20 1
  while done < connections do
    if capturePath.isSome then capture := captured capture rx 0 rxLength now
    let began ← IO.monoNanosNow
    (t, tx) := Flat.process cfg answers respond now rx rxLength t tx
    (t, tx) := Flat.tick cfg answers now 1 t tx
    let ended ← IO.monoNanosNow
    if capturePath.isSome then capture := captured capture tx 8 (written tx) now
    spent := spent + (ended - began)
    framesIn := framesIn + pendingIn
    now := now + 1
    -- The clients read what was written to them and write what they send next.
    let stop := written tx
    let mut o : USize := 8
    rxLength := 0
    pendingIn := 0
    while o < stop do
      let n := (rd16 tx o).toUSize
      let f := o + 2
      framesOut := framesOut + 1
      let cip := rd32 tx (f + 30)
      let i := cip - clientBase
      let flags := rd8 tx (f + 47)
      let theirs := rd32 tx (f + 38)
      let acked := rd32 tx (f + 42)
      let payload : UInt32 := (rd16 tx (f + 16)).toUInt32 - (20 : UInt32) - (((rd8 tx (f + 46)) >>> 4).toUInt32 <<< (2 : UInt32))
      let c := (16 * i.toNat).toUSize
      let state := ld32 clients c
      let port := (ld32 clients (c + 4)).toUInt16
      let first := ld32 clients (c + 8)
      if flags == 0x12 && state == 1 then
        (rx, rxLength) := clientFrame cfg rx rxLength cip port 0x10 (first + 1) (theirs + 1) .empty
        (rx, rxLength) := clientFrame cfg rx rxLength cip port 0x18 (first + 1) (theirs + 1) request
        clients := st32 clients c 2
        pendingIn := pendingIn + 2
      else if each > 1 && state == 2 && payload != 0 && flags &&& 0x08 != 0 then
        -- The answer, on a connection that stays open: the next request with its acknowledgement, or after
        -- the last of them this end's closing.
        let had := ld32 clients (c + 12) + 1
        let at_ := first + 1 + had * request.size.toUInt32
        if had.toNat < each then
          (rx, rxLength) := clientFrame cfg rx rxLength cip port 0x18 at_ (theirs + payload) request
          clients := st32 clients (c + 12) had
        else
          (rx, rxLength) := clientFrame cfg rx rxLength cip port 0x11 at_ (theirs + payload) .empty
          clients := st32 (st32 clients c 3) (c + 12) 0
        pendingIn := pendingIn + 1
      else if each > 1 && state == 3 && flags == 0x11 then
        -- The server's closing in answer to this end's: acknowledged, and the next connection begun.
        (rx, rxLength) := clientFrame cfg rx rxLength cip port 0x10 acked (theirs + 1) .empty
        done := done + 1
        let port := if port ≥ 60000 then 1024 else port + 1
        let first := first * 1664525 + 1013904223
        clients := st32 (st32 (st32 clients c 1) (c + 4) port.toUInt32) (c + 8) first
        (rx, rxLength) := clientFrame cfg rx rxLength cip port 0x02 first 0 .empty
        pendingIn := pendingIn + 2
      else if flags &&& 0x01 != 0 && state == 2 && payload != 0 then
        -- The last of the answer, with the end of the stream on it: everything before it is acknowledged
        -- with it, and this end closes.
        (rx, rxLength) := clientFrame cfg rx rxLength cip port 0x11 (first + 1 + request.size.toUInt32) (theirs + payload + 1) .empty
        clients := st32 clients c 3
        pendingIn := pendingIn + 1
      else if flags == 0x10 && state == 3 && acked == first + 2 + request.size.toUInt32 then
        done := done + 1
        let port := if port ≥ 60000 then 1024 else port + 1
        let first := first * 1664525 + 1013904223
        clients := st32 (st32 (st32 clients c 1) (c + 4) port.toUInt32) (c + 8) first
        (rx, rxLength) := clientFrame cfg rx rxLength cip port 0x02 first 0 .empty
        pendingIn := pendingIn + 1
      o := f + n
    if pendingIn == 0 then
      IO.println "the clients have nothing more to send: the exchange has stalled"
      break
  let seconds := spent.toFloat / 1e9
  IO.println s!"flat: {done} connections, {atOnce} at once, checksums {if checksums then "on" else "off"}, request {requestBytes} bytes, answer {answerBytes} bytes, table of 2^{slotBits}"
  IO.println s!"  {seconds} s in the stack: {(done.toFloat / seconds).round} connections a second on one core, {(spent.toFloat / framesIn.toFloat).round} ns a frame in ({framesIn} in, {framesOut} out)"
  if each > 1 then IO.println s!"  {each} requests a connection: {((done * each).toFloat / seconds).round} requests a second"
  if let some path := capturePath then IO.FS.writeBinFile path capture
  IO.println s!"  counters: live {ld64 t 0}, accepted {ld64 t 8}, closed {ld64 t 16}, SYNs {ld64 t 24}, dropped {ld64 t 32}, out of order {ld64 t 40}, resets taken {ld64 t 48}, no room {ld64 t 56}, sent again {ld64 t 72}, timed out {ld64 t 80}, resets sent {ld64 t 88}, sent again on repeats {ld64 t 96}, held back {ld64 t 104}, round trips measured {ld64 t 120}"

/-- The system's TCP through the same exchange, one connection at a time, in TCP segments. -/
def system (connections requestBytes answerBytes : Nat) : IO Unit := do
  let remote : Internet.Peer := ⟨ByteArray.mk #[2, 0, 0, 0, 0, 1], ByteArray.mk #[11, 0, 0, 1]⟩
  let request := ByteArray.mk (Array.replicate requestBytes 0x61)
  let answer := ByteArray.mk (Array.replicate answerBytes 0x62)
  let mut e : Tcp.Endpoint := { listenPort := 80 }
  let mut spent := 0
  let mut done := 0
  let packets (events : Array Tcp.Event) : Array Tcp.Segment := events.filterMap fun
    | .emit _ raw => Tcp.Segment.decode? raw
    | _ => none
  for c in [0:connections] do
    let port : UInt16 := (1024 + c % 60000).toUInt16
    let key : Tcp.Key := ⟨remote.ip, port, 80⟩
    let first : UInt32 := 1000 + c.toUInt32
    let syn : Tcp.Segment := { src := port, dst := 80, seq := first, answer := 0, flags := Tcp.syn, window := 65535, mss := some 1460 }
    let synBytes := syn.encode
    let began ← IO.monoNanosNow
    let (e1, events) := e.receive c 77 remote synBytes
    let ended ← IO.monoNanosNow
    spent := spent + (ended - began)
    let some hello := (packets events)[0]? | do IO.println "the system's TCP did not answer a SYN"; return
    let theirs := hello.seq + 1
    let ackBytes := ({ syn with seq := first + 1, answer := theirs, flags := Tcp.ack, mss := none } : Tcp.Segment).encode
    let dataBytes := ({ syn with seq := first + 1, answer := theirs, flags := Tcp.psh ||| Tcp.ack ||| Tcp.fin, mss := none, data := request } : Tcp.Segment).encode
    let lastSeq := first + 2 + request.size.toUInt32
    let ackData := ({ syn with seq := lastSeq, answer := theirs + answer.size.toUInt32, flags := Tcp.ack, mss := none } : Tcp.Segment).encode
    let ackFin := ({ syn with seq := lastSeq, answer := theirs + answer.size.toUInt32 + 1, flags := Tcp.ack, mss := none } : Tcp.Segment).encode
    let began ← IO.monoNanosNow
    let (e2, _) := e1.receive c 77 remote ackBytes
    let (e3, _) := e2.receive c 77 remote dataBytes
    let (e4, _) := e3.send c key answer
    let (e5, _) := e4.close c key
    let (e6, _) := e5.receive c 77 remote ackData
    let (e7, _) := e6.receive c 77 remote ackFin
    let ended ← IO.monoNanosNow
    spent := spent + (ended - began)
    if e7.conns.isEmpty then done := done + 1
    e := e7
  let seconds := spent.toFloat / 1e9
  IO.println s!"the system's TCP: {done} of {connections} connections ended cleanly, one at a time; {seconds} s in the stack: {(done.toFloat / seconds).round} connections a second on one core"

def main (args : List String) : IO UInt32 := do
  let number (i : Nat) (otherwise : Nat) : Nat := (args[i]?.bind String.toNat?).getD otherwise
  let connections := number 0 1000000
  let atOnce := number 1 1000
  flat connections atOnce (number 2 1 == 1) (number 3 100) (number 4 128) (args[5]?.filter (· != "-")) (number 6 1)
  system (min connections 200000) (number 3 100) (number 4 128)
  return 0
