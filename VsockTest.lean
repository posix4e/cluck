import Kernel.Vsock

/-! # Tests of the vsock protocol

Scenarios first: each one plays the parent instance's side by hand and checks every packet and event that
comes back. Then a fuzzer: a long run of packets and calls chosen by a fixed-seed generator, some well-formed,
some nearly, some noise, with the endpoint's invariants checked after every step. Pure: no device. -/

open Kernel.Vsock

def parent : UInt64 := 3
def us : UInt64 := 16
def port : UInt32 := 5005

/-- A packet as the parent would send it. -/
def pkt (op : UInt16) (srcPort : UInt32) (dstPort : UInt32 := port) (payload : ByteArray := ByteArray.empty)
    (flags : UInt32 := 0) (bufAlloc : UInt32 := 1000) (fwdCnt : UInt32 := 0) (srcCid : UInt64 := parent)
    (dstCid : UInt64 := us) (type : UInt16 := typeStream) : ByteArray :=
  Packet.encode {
    header := { srcCid, dstCid, srcPort, dstPort, len := payload.size.toUInt32, type, op, flags, bufAlloc, fwdCnt }
    payload }

def filled (n : Nat) (b : UInt8) : ByteArray := ⟨Array.replicate n b⟩

def sent (events : Array Event) : Array Packet :=
  events.filterMap fun | .send raw => Packet.decode? raw | _ => none

def ops (events : Array Event) : List UInt16 := (sent events).toList.map (·.header.op)

def opened (events : Array Event) : List Key := events.toList.filterMap fun | .opened k => some k | _ => none
def closed (events : Array Event) : List Key := events.toList.filterMap fun | .closed k => some k | _ => none
def finished (events : Array Event) : List Key := events.toList.filterMap fun | .finished k => some k | _ => none
def received (events : Array Event) : List ByteArray := events.toList.filterMap fun | .data _ b => some b | _ => none

def key (peerPort : UInt32) (localPort : UInt32 := port) : Key := { peerCid := parent, peerPort, localPort }

def fresh (maxConns : Nat := 4) (bufAlloc : UInt32 := 65536) : Endpoint :=
  { cid := us, listenPort := port, maxConns, bufAlloc }

/-- An endpoint with one connection accepted from the parent's port 1234. -/
def connected (bufAlloc : UInt32 := 65536) (peerBuf : UInt32 := 1000) : Endpoint :=
  ((fresh (bufAlloc := bufAlloc)).receive (pkt opRequest 1234 (bufAlloc := peerBuf))).1

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

/-! ## The fuzzer -/

structure Rng where
  state : UInt64

def Rng.next (r : Rng) : Rng × UInt64 :=
  let s := r.state * 6364136223846793005 + 1442695040888963407
  ({ state := s }, s >>> 33)

def Rng.below (r : Rng) (n : Nat) : Rng × Nat :=
  let (r, v) := r.next
  (r, v.toNat % n)

def Rng.pick {α : Type} [Inhabited α] (r : Rng) (xs : Array α) : Rng × α :=
  let (r, i) := r.below xs.size
  (r, xs[i]!)

def Rng.bytes (r : Rng) (n : Nat) : Rng × ByteArray := Id.run do
  let mut r := r
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (r', v) := r.next
    r := r'
    out := out.push v.toUInt8
  return (r, out)

structure Tally where
  steps : Nat := 0
  opened : Nat := 0
  data : Nat := 0
  closed : Nat := 0
  resets : Nat := 0
  written : Nat := 0
  problems : Array String := #[]

/-- What must hold of an endpoint and of anything it asks to send, whatever it was fed. -/
def invariants (e : Endpoint) (events : Array Event) (step : Nat) (tally : Tally) : Tally := Id.run do
  let mut tally := tally
  let complain (t : Tally) (what : String) : Tally :=
    if t.problems.size < 10 then { t with problems := t.problems.push s!"step {step}: {what}" } else t
  if e.conns.size > e.maxConns then tally := complain tally "more connections than allowed"
  for i in [0:e.conns.size] do
    for j in [i + 1:e.conns.size] do
      if e.conns[i]!.key == e.conns[j]!.key then tally := complain tally "two connections with one key"
  for event in events do
    match event with
    | .send raw =>
      match Packet.decode? raw with
      | none => tally := complain tally "sent something that is not a packet"
      | some p =>
        if p.header.srcCid != e.cid then tally := complain tally "sent from someone else's address"
        if p.payload.size > maxPayload then tally := complain tally "sent a payload over the limit"
        if p.header.op == opRst then tally := { tally with resets := tally.resets + 1 }
    | .opened _ => tally := { tally with opened := tally.opened + 1 }
    | .data _ _ => tally := { tally with data := tally.data + 1 }
    | .closed k =>
      tally := { tally with closed := tally.closed + 1 }
      if (e.find? k).isSome then tally := complain tally "reported closed but still there"
    | .finished _ => pure ()
  return { tally with steps := tally.steps + 1 }

def fuzz (iterations : Nat) (seed : UInt64) : Tally := Id.run do
  let cids : Array UInt64 := #[parent, parent, parent, us, 99]
  let ports : Array UInt32 := #[port, port, 1234, 1235, 1236, 9000, 40000]
  let opsPool : Array UInt16 := #[0, 1, 1, 1, 2, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 7, 7, 8]
  let mut r : Rng := { state := seed }
  let mut e : Endpoint := { cid := us, listenPort := port, maxConns := 3, bufAlloc := 256 }
  let mut tally : Tally := {}
  for step in [0:iterations] do
    let (r1, choice) := r.below 100
    r := r1
    if choice < 8 then
      -- Noise: any bytes at all.
      let (r1, n) := r.below 90
      let (r2, raw) := r1.bytes n
      r := r2
      let (e', events) := e.receive raw
      e := e'
      tally := invariants e events step tally
    else if choice < 70 then
      -- A packet with fields drawn from a small pool, so that it often lands on a real connection.
      let (r1, srcCid) := r.pick cids
      let (r2, dstCid) := r1.pick #[us, us, us, us, parent]
      let (r3, srcPort) := r2.pick ports
      let (r4, dstPort) := r3.pick ports
      let (r5, op) := r4.pick opsPool
      let (r6, flags) := r5.below 4
      let (r7, n) := r6.below 300
      let (r8, payload) := r7.bytes n
      let (r9, bufAlloc) := r8.below 20000
      let (r10, fwdNoise) := r9.below 5000
      let (r11, odd) := r10.below 40
      let (r12, aim) := r11.below 100
      let (r13, which) := r12.below (max e.conns.size 1)
      r := r13
      -- More often than not, address a connection that exists, so that the run spends its time inside
      -- connections and not only knocking on closed doors.
      let (srcCid, srcPort, dstPort) :=
        match e.conns[which]? with
        | some c => if aim < 65 then (c.key.peerCid, c.key.peerPort, c.key.localPort) else (srcCid, srcPort, dstPort)
        | none => (srcCid, srcPort, dstPort)
      let dstCid := if aim < 65 then us else dstCid
      -- On a connection that exists, mostly the traffic a connection sees, so that some of them live long
      -- enough for their counters to matter.
      let (r14, gentle) := r.pick (#[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 4, 3, 1, 9] : Array UInt16)
      r := r14
      let op := if aim < 65 && e.conns.size > 0 then gentle else op
      -- With no connection at all, usually open one.
      let (op, dstPort, dstCid) := if e.conns.isEmpty && aim < 80 then (opRequest, port, us) else (op, dstPort, dstCid)
      let payload := if op == opRw then payload else ByteArray.empty
      -- A peer that keeps honest count reports having taken what we sent it; most of the time this one does,
      -- so that writing gets somewhere. The rest of the time its count is noise.
      let fwd : UInt32 :=
        match e.find? { peerCid := srcCid, peerPort := srcPort, localPort := dstPort } with
        | some (_, c) => if odd < 30 then c.sent else fwdNoise.toUInt32
        | none => fwdNoise.toUInt32
      let raw := pkt op srcPort dstPort payload flags.toUInt32 bufAlloc.toUInt32 fwd srcCid dstCid
        (if odd == 0 then 2 else typeStream)
      -- Now and then, a length that does not match what follows.
      let raw := if odd == 1 then raw.push 0 else raw
      let (e', events) := e.receive raw
      e := e'
      tally := invariants e events step tally
    else
      let (r1, peerPort) := r.pick ports
      let (r2, localPort) := r1.pick ports
      let (r3, action) := r2.below 10
      let (r4, n) := r3.below 9000
      r := r4
      let k : Key := { peerCid := parent, peerPort, localPort }
      if action < 6 then
        let room := match e.find? k with | some (_, c) => c.peerFree | none => 0
        let (e', events, accepted) := e.write k (filled n 0x77)
        e := e'
        tally := invariants e events step tally
        let carried := (sent events).foldl (fun total p => total + p.payload.size) 0
        if accepted > room || accepted > n || carried != accepted then
          tally := { tally with problems := tally.problems.push s!"step {step}: wrote {accepted} with room for {room}, carried {carried}" }
        tally := { tally with written := tally.written + accepted }
      else if action < 7 then
        let (e', events) := e.close k
        e := e'
        tally := invariants e events step tally
      else if action < 8 then
        let (e', events, _) := e.connect k
        e := e'
        tally := invariants e events step tally
      else
        let (e', events) := e.askForRoom k
        e := e'
        tally := invariants e events step tally
  return tally

def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  let check (name : String) (holds : Bool) : IO Unit := do
    unless holds do
      failures.modify (· + 1)
      IO.eprintln s!"FAIL {name}"
  -- The header, byte for byte.
  let header : Header := {
    srcCid := 3, dstCid := 16, srcPort := 0x01020304, dstPort := 5005, len := 2, type := 1, op := 5, flags := 0,
    bufAlloc := 0x10000, fwdCnt := 7 }
  check "header bytes"
    (hex header.encode == "0300000000000000100000000000000004030201" ++ "8d130000" ++ "02000000" ++ "0100" ++ "0500" ++
      "00000000" ++ "00000100" ++ "07000000")
  check "header size" (header.encode.size == headerSize)
  check "header round trip" (Header.decode header.encode == header)
  check "a short packet is not a packet" ((Packet.decode? (header.encode.extract 0 43)).isNone)
  check "a packet with the wrong length is not a packet" ((Packet.decode? header.encode).isNone)
  -- Accepting a connection.
  let (e, events) := (fresh).receive (pkt opRequest 1234)
  let answer := (sent events)[0]!.header
  check "a request is answered" (ops events == [opResponse] && opened events == [key 1234])
  check "the answer is addressed back" (answer.srcCid == us && answer.dstCid == parent && answer.srcPort == port &&
    answer.dstPort == 1234 && answer.bufAlloc == 65536 && answer.fwdCnt == 0 && answer.type == typeStream)
  check "one connection exists" (e.conns.size == 1)
  -- Data in.
  let (e, events) := e.receive (pkt opRw 1234 (payload := "hi".toUTF8))
  check "data is delivered" (received events == ["hi".toUTF8] && ops events == [])
  let (e, events) := e.receive (pkt opRw 1234 (payload := filled 32768 1))
  check "half a buffer taken is reported" (ops events == [opCreditUpdate] && (sent events)[0]!.header.fwdCnt == 32770)
  let (e, events) := e.receive (pkt opCreditRequest 1234)
  check "a request for credit is answered" (ops events == [opCreditUpdate] && (sent events)[0]!.header.fwdCnt == 32770)
  let (_, events) := e.receive (pkt opRw 1234 (payload := ByteArray.empty))
  check "an empty payload delivers nothing" (received events == [] && closed events == [])
  -- Data out, within the room the peer has.
  let e := connected (peerBuf := 1000)
  let (e, events, accepted) := e.write (key 1234) (filled 1500 9)
  check "writing stops at the peer's room" (accepted == 1000 && (sent events).toList.map (·.payload.size) == [1000])
  let (e, events, accepted) := e.write (key 1234) (filled 500 9)
  check "no room, nothing sent" (accepted == 0 && events.size == 0)
  let (e, events) := e.askForRoom (key 1234)
  check "asking for room" (ops events == [opCreditRequest])
  let (e, _) := e.receive (pkt opCreditUpdate 1234 (bufAlloc := 1000) (fwdCnt := 1000))
  let (_, events, accepted) := e.write (key 1234) (filled 500 9)
  check "room again after the peer reports" (accepted == 500 && ops events == [opRw])
  let e := connected (peerBuf := 10000)
  let (_, events, accepted) := e.write (key 1234) (filled 9000 9)
  check "a long write goes in pieces" (accepted == 9000 && (sent events).toList.map (·.payload.size) == [4096, 4096, 808])
  check "writing to no connection" (((fresh).write (key 1234) (filled 5 1)).2.2 == 0)
  -- Packets that belong to nothing.
  let (e, events) := (fresh).receive (pkt opRw 1234 (payload := "x".toUTF8))
  let reset := (sent events)[0]!.header
  check "data for no connection is reset" (ops events == [opRst] && reset.dstPort == 1234 && reset.srcPort == port &&
    reset.dstCid == parent && e.conns.size == 0)
  check "a reset for no connection is not answered" (((fresh).receive (pkt opRst 1234)).2.size == 0)
  check "a packet for someone else is dropped" (((fresh).receive (pkt opRequest 1234 (dstCid := 99))).2.size == 0)
  check "noise is dropped" (((fresh).receive (filled 20 0xFF)).2.size == 0)
  check "a request for another port is reset" (ops ((fresh).receive (pkt opRequest 1234 (dstPort := 7))).2 == [opRst])
  check "a request of another socket type is reset"
    (ops ((fresh).receive (pkt opRequest 1234 (type := 2))).2 == [opRst])
  -- The table is bounded.
  let e := fresh (maxConns := 2)
  let (e, _) := e.receive (pkt opRequest 1)
  let (e, _) := e.receive (pkt opRequest 2)
  let (e, events) := e.receive (pkt opRequest 3)
  check "a full table refuses" (ops events == [opRst] && e.conns.size == 2 && opened events == [])
  -- Ending a connection.
  let (e, events) := (connected).receive (pkt opShutdown 1234 (flags := 3))
  check "shutdown both ways is reset and closed" (ops events == [opRst] && closed events == [key 1234] && e.conns.size == 0)
  let (e, events) := (connected).receive (pkt opShutdown 1234 (flags := shutdownSend))
  check "shutdown of sending is reported, the connection stays" (finished events == [key 1234] && e.conns.size == 1 &&
    ops events == [])
  let (e, _, accepted) := e.write (key 1234) (filled 10 1)
  check "we can still write after the peer finishes sending" (accepted == 10)
  let (e, events) := e.receive (pkt opRw 1234 (payload := "late".toUTF8))
  check "data after the peer said it was done ends the connection" (ops events == [opRst] && closed events == [key 1234] &&
    e.conns.size == 0)
  let (e, events) := (connected).receive (pkt opShutdown 1234 (flags := shutdownRcv))
  check "a peer that stopped receiving gets nothing more" ((e.write (key 1234) (filled 10 1)).2.2 == 0 && events.size == 0)
  let (e, events) := (connected).receive (pkt opRst 1234)
  check "a reset closes without an answer" (events.size == 1 && closed events == [key 1234] && e.conns.size == 0)
  let (e, events) := (connected).receive (pkt opRequest 1234)
  check "a second request on a connection ends it" (ops events == [opRst] && closed events == [key 1234] && e.conns.size == 0)
  let (e, events) := (connected).receive (pkt opResponse 1234)
  check "an answer nobody asked for ends it" (ops events == [opRst] && e.conns.size == 0)
  let (e, events) := (connected (bufAlloc := 100)).receive (pkt opRw 1234 (payload := filled 101 1))
  check "a packet larger than the buffer ends it" (ops events == [opRst] && closed events == [key 1234] && e.conns.size == 0)
  let (_, events) := (connected (bufAlloc := 100)).receive (pkt opRw 1234 (payload := filled 100 1))
  check "a packet exactly the buffer is taken" (received events == [filled 100 1])
  -- Our own close.
  let (e, events) := (connected).close (key 1234)
  check "closing says so both ways" (ops events == [opShutdown] && (sent events)[0]!.header.flags == 3 && e.conns.size == 1)
  check "closing twice says it once" ((e.close (key 1234)).2.size == 0)
  let (e2, events) := e.receive (pkt opRw 1234 (payload := "x".toUTF8))
  check "data while closing is not delivered" (received events == [] && e2.conns.size == 1)
  let (e, events) := e.receive (pkt opRst 1234)
  check "the peer's reset finishes the close" (closed events == [key 1234] && e.conns.size == 0)
  let e := fresh (maxConns := 1)
  let (e, _) := e.receive (pkt opRequest 1)
  let (e, _) := e.close (key 1)
  let (e, events) := e.receive (pkt opRequest 2)
  check "a connection being closed does not keep a new one out" (opened events == [key 2] && e.conns.size == 1)
  -- Connecting out, as the boot heartbeat does.
  let beat : Key := { peerCid := parent, peerPort := 9000, localPort := 40000 }
  let (e, events, asked) := (fresh).connect beat
  let request := (sent events)[0]!.header
  check "connecting asks" (asked && ops events == [opRequest] && request.dstPort == 9000 && request.srcPort == 40000 &&
    request.dstCid == parent)
  check "nothing is written before the answer" ((e.write beat (filled 1 0xb7)).2.2 == 0)
  let (e, events) := e.receive (pkt opResponse 9000 (dstPort := 40000) (bufAlloc := 4096))
  check "the answer opens it" (opened events == [beat])
  let (e, events, accepted) := e.write beat (filled 1 0xb7)
  check "the heartbeat byte goes out" (accepted == 1 && (sent events).toList.map (·.payload) == [filled 1 0xb7])
  let (e, events) := e.receive (pkt opRw 9000 (dstPort := 40000) (payload := filled 1 0xb7) (bufAlloc := 4096) (fwdCnt := 1))
  check "and its echo comes back" (received events == [filled 1 0xb7])
  let (e, _) := e.close beat
  let (e, events) := e.receive (pkt opRst 9000 (dstPort := 40000))
  check "then it closes" (closed events == [beat] && e.conns.size == 0)
  let (e, _, _) := (fresh).connect beat
  let (e, events) := e.receive (pkt opRst 9000 (dstPort := 40000))
  check "a refused connection is reported" (closed events == [beat] && e.conns.size == 0)
  let (again, events, asked) := ((fresh).connect beat).1.connect beat
  check "connecting twice changes nothing" (!asked && events.size == 0 && again.conns.size == 1)
  let (full, events, asked) := (fresh (maxConns := 0)).connect beat
  check "connecting with no room changes nothing" (!asked && events.size == 0 && full.conns.size == 0)
  -- The fuzzer.
  let tally := fuzz 300000 0x53494c4f56534f43
  for problem in tally.problems do
    IO.eprintln s!"FAIL fuzz {problem}"
  check "the fuzzer found nothing" tally.problems.isEmpty
  check "the fuzzer got somewhere" (tally.opened > 5000 && tally.data > 20000 && tally.closed > 5000 && tally.written > 1000000)
  IO.println s!"fuzz: {tally.steps} steps, {tally.opened} opened, {tally.data} deliveries, {tally.closed} closed, {tally.resets} resets sent, {tally.written} bytes written"
  let failed ← failures.get
  if failed == 0 then
    IO.println "vsock-test: all checks passed"
    return 0
  else
    IO.eprintln s!"vsock-test: {failed} check(s) failed"
    return 1
