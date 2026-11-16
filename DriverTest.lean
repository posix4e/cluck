import Kernel.Socket
import Kernel.SecureModule

/-! # The socket driver against a device that lies

The protocol has its own tests and fuzzer (`vsock-test`), which feed it packets. This is about what is under
it: the driver takes buffers out of queues the device writes, and believes nothing the device says about
them. Here the test is the device. The machine is ordinary memory (`rt/hosted/machine.c`) with the real
device layer on top, so anything written into the registers and the queues is what the driver reads, and a
driver led to an address outside what it was given stops the process, which fails the test.

Each round is a new machine with a socket device whose queue sizes and address are whatever the round's
numbers say. The driver starts on it, and then, step after step, the device writes what it likes: entries in
the used rings that name buffers that do not exist and lengths no buffer has, indices that jump, packets that
are noise, and packets that are nearly right. After each step the driver is asked for what arrived.

What must hold: the process is never stopped, no data handed up is longer than a buffer, and the table of
connections never passes its bound.

The Secure Module's driver is put through the same: the device's answers are proper ones, proper ones cut
short, and noise, and what it says about which buffer it used and how much it wrote is whatever it likes. -/

open Kernel Kernel.Virtio

@[extern "silo_machine_reset"]
opaque machineReset : BaseIO Unit

/-- A source of numbers that is the same on every run. -/
structure Numbers where
  state : UInt64

def Numbers.next (n : Numbers) : Nat × Numbers :=
  let state := n.state * 6364136223846793005 + 1442695040888963407
  ((state >>> 33).toNat, { state })

/-- Numbers a device might report that a driver has to survive: small, large, and around every boundary. -/
def awkwardNumbers : Array Nat :=
  #[0, 1, 2, 3, 15, 16, 17, 43, 44, 45, 255, 256, 4095, 4096, 8191, 8192, 8193, 65535, 65536, 0x7FFFFFFF, 0xFFFFFFFF]

def Numbers.awkward (n : Numbers) : Nat × Numbers :=
  let (r, n) := n.next
  if r % 3 == 0 then (r % 0x100000000, n) else (awkwardNumbers[r % awkwardNumbers.size]!, n)

def Numbers.bytes (n : Numbers) (count : Nat) : ByteArray × Numbers := Id.run do
  let mut n := n
  let mut out := ByteArray.emptyWithCapacity count
  for _ in [0:count] do
    let (r, n') := n.next
    n := n'
    out := out.push r.toUInt8
  return (out, n)

/-- Writes one entry of a queue's used ring as the device would: which buffer, and how much it wrote there. -/
def writeUsed (q : Queue) (position buffer length : Nat) : BaseIO Unit :=
  Hw.store (q.tables + (q.layout.usedSlot position).toUInt64) (Virtq.le buffer 4 ++ Virtq.le length 4)

def writeUsedIndex (q : Queue) (index : Nat) : BaseIO Unit :=
  Hw.store (q.tables + q.layout.usedIndex.toUInt64) (Virtq.le index 2)

/-- A packet for this machine that is nearly right: a real header with some fields left to chance. -/
def nearlyRight (cid : UInt64) (n : Numbers) : ByteArray × Numbers :=
  let (a, n) := n.next
  let (b, n) := n.awkward
  let (c, n) := n.awkward
  let (size, n) := n.next
  let (payload, n) := n.bytes (size % 200)
  let header : Vsock.Header := {
    srcCid := 3, dstCid := if a % 8 == 0 then 99 else cid, srcPort := (1000 + a % 3).toUInt32,
    dstPort := if a % 5 == 0 then 7 else 5005, len := if a % 7 == 0 then b.toUInt32 else payload.size.toUInt32,
    type := if a % 11 == 0 then 2 else Vsock.typeStream, op := (a / 16 % 9).toUInt16, flags := (a / 256 % 4).toUInt32,
    bufAlloc := c.toUInt32, fwdCnt := (a / 1024 % 5).toUInt32 }
  (header.encode ++ payload, n)

def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  let check (name : String) (holds : Bool) : IO Unit := do
    unless holds do
      IO.eprintln s!"FAIL {name}"
      failures.modify (· + 1)
  let mut n : Numbers := { state := 0x51105110 }
  let mut started := 0
  let mut refused := 0
  let mut arrived := 0
  let mut opened := 0
  for round in [0:300] do
    machineReset
    let window := (← Hw.windows)[0]!
    let device : Device := { base := window.base, id := idSocket }
    -- The device as the driver first finds it. Most rounds it is a proper one; some it is not.
    let (shape, n1) := n.next
    n := n1
    Hw.write32 (window.base + regMagic) magic
    Hw.write32 (window.base + regVersion) 2
    Hw.write32 (window.base + regDeviceId) idSocket
    Hw.write32 (window.base + regDeviceFeatures) (if shape % 13 == 0 then 0 else 1)
    let (offered, n2) := n.awkward
    n := n2
    Hw.write32 (window.base + regQueueNumMax) (if shape % 4 == 0 then offered.toUInt32 else 16)
    Hw.write32 (window.base + regConfig) (if shape % 6 == 0 then (shape / 64).toUInt32 else 18)
    Hw.write32 (window.base + regConfig + 4) (if shape % 17 == 0 then 0xFFFFFFFF else 0)
    let some socket ← Socket.start device 5005
      | do refused := refused + 1; continue
    started := started + 1
    let mut socket := socket
    check s!"round {round}: a queue has at least one entry and at most {maxQueueSize}"
      (socket.receive.layout.size ≥ 1 && socket.receive.layout.size ≤ maxQueueSize)
    for step in [0:400] do
      let (kind, n1) := n.next
      n := n1
      let (buffer, n2) := n.awkward
      n := n2
      let (length, n3) := n.awkward
      n := n3
      -- What the device leaves in the receive queue this step.
      let size := socket.receive.layout.size
      let slot := kind / 8 % size
      if kind % 4 == 0 then
        -- noise over the whole used ring, and an index from anywhere
        let (noise, n4) := n.bytes (4 + 8 * size)
        n := n4
        Hw.store (socket.receive.tables + socket.receive.layout.used.toUInt64) noise
      else
        let (packet, n4) := if kind % 4 == 1 then n.bytes (length % 300) else nearlyRight socket.endpoint.cid n
        n := n4
        Hw.store (socket.receive.bufferAddress slot) packet
        -- the entry says which buffer and how much: the truth, or not
        writeUsed socket.receive socket.receive.taken (if kind % 16 < 12 then slot else buffer)
          (if kind % 32 < 24 then packet.size else length)
        writeUsedIndex socket.receive ((socket.receive.taken + (if kind % 64 < 56 then 1 else buffer)) % 65536)
      -- The device takes what the driver sends, most of the time, and says odd things about it.
      if kind % 128 != 5 then
        writeUsed socket.transmit socket.transmit.taken buffer length
        writeUsedIndex socket.transmit ((socket.transmit.taken + 8) % 65536)
      let (events, next) ← socket.poll
      socket := next
      for event in events do
        match event with
        | .data _ bytes =>
          arrived := arrived + 1
          check s!"round {round} step {step}: data handed up fits in a buffer" (bytes.size ≤ packetBuffer)
        | .opened _ => opened := opened + 1
        | _ => pure ()
      check s!"round {round} step {step}: the table of connections is within its bound"
        (socket.endpoint.conns.size ≤ socket.endpoint.maxConns)
      check s!"round {round} step {step}: the device took what was sent" (!socket.stuck)
  -- A device that takes nothing the driver sends: asked to connect, the driver answers, waits its bounded
  -- time for the answer to be taken, and then knows the socket is stuck.
  machineReset
  let window := (← Hw.windows)[0]!
  Hw.write32 (window.base + regMagic) magic
  Hw.write32 (window.base + regVersion) 2
  Hw.write32 (window.base + regDeviceId) idSocket
  Hw.write32 (window.base + regDeviceFeatures) 1
  Hw.write32 (window.base + regQueueNumMax) 16
  Hw.write32 (window.base + regConfig) 18
  match ← Socket.start { base := window.base, id := idSocket } 5005 with
  | none => check "a proper device is started" false
  | some socket =>
    let request : Vsock.Header := {
      srcCid := 3, dstCid := 18, srcPort := 1000, dstPort := 5005, len := 0, type := Vsock.typeStream,
      op := Vsock.opRequest, flags := 0, bufAlloc := 65536, fwdCnt := 0 }
    Hw.store (socket.receive.bufferAddress 0) request.encode
    writeUsed socket.receive 0 0 request.encode.size
    writeUsedIndex socket.receive 1
    let (_, socket) ← socket.poll
    check "a device that never takes the answer leaves the socket stuck" socket.stuck
    let (events, socket) ← socket.poll
    check "and a stuck socket sends nothing more and stays stuck" (socket.stuck && events.isEmpty)
  -- The Secure Module's driver, the same way. Each exchange puts a request and room for an answer in the
  -- queue; the device here has already written what it will say, true or not, about both.
  let mut modules := 0
  let mut answered := 0
  let mut unanswered := 0
  for round in [0:300] do
    machineReset
    let window := (← Hw.windows)[0]!
    let (shape, n1) := n.next
    n := n1
    let (offered, n2) := n.awkward
    n := n2
    Hw.write32 (window.base + regMagic) magic
    Hw.write32 (window.base + regVersion) 2
    Hw.write32 (window.base + regDeviceId) idNitroSecureModule
    Hw.write32 (window.base + regDeviceFeatures) (if shape % 13 == 0 then 0 else 1)
    Hw.write32 (window.base + regQueueNumMax) (if shape % 4 == 0 then offered.toUInt32 else 4)
    let some module ← SecureModule.start { base := window.base, id := idNitroSecureModule }
      | continue
    modules := modules + 1
    let mut module := module
    for step in [0:40] do
      let (kind, n1) := n.next
      n := n1
      let (length, n2) := n.awkward
      n := n2
      let (noise, n3) := n.bytes (kind / 4 % 600)
      n := n3
      -- What the device says it answered: a proper answer, a proper one cut or padded, or noise.
      let randomAnswer := Nsm.mapHead 1 ++ Nsm.text "GetRandom" ++ Nsm.mapHead 1 ++ Nsm.text "random" ++ Nsm.bytes noise
      let document := Nsm.mapHead 1 ++ Nsm.text "Attestation" ++ Nsm.mapHead 1 ++ Nsm.text "document" ++ Nsm.bytes noise
      let refusal := Nsm.mapHead 1 ++ Nsm.text "Error" ++ Nsm.text "InvalidArgument"
      let answer := match kind % 5 with
        | 0 => randomAnswer
        | 1 => document
        | 2 => refusal
        | 3 => randomAnswer.extract 0 (kind / 64 % (randomAnswer.size + 1))
        | _ => noise
      Hw.store (module.queue.bufferAddress SecureModule.answerSlot) answer
      -- Ten exchanges' worth of used entries, so that a driver that asks again finds an answer waiting.
      let size := module.queue.layout.size
      for position in [0:size] do
        let slot := if kind % 16 == 7 then length else position % 2
        let count := if kind % 8 == 6 then length else answer.size
        writeUsed module.queue (module.queue.taken + position) slot count
      writeUsedIndex module.queue ((module.queue.taken + 20) % 65536)
      match kind / 1024 % 3 with
      | 0 =>
        -- never asked for more than a proper answer would hold, so the driver has no cause to ask twice
        let wanted := 1 + kind / 4096 % 8
        let (bytes, next) ← module.random wanted
        module := next
        match bytes with
        | some bytes => answered := answered + 1; check s!"module round {round} step {step}: random bytes are as many as asked for" (bytes.size == wanted)
        | none => unanswered := unanswered + 1
      | 1 =>
        let (document, next) ← module.attest (noise.extract 0 32)
        module := next
        match document with
        | some document => answered := answered + 1; check s!"module round {round} step {step}: a document fits in an answer" (document.size ≤ Nsm.maxResponse)
        | none => unanswered := unanswered + 1
      | _ =>
        let (time, next) ← module.time
        module := next
        if time.isSome then answered := answered + 1 else unanswered := unanswered + 1
      if module.gone then break
  check "Secure Modules were started, and answered some requests and not others" (modules > 100 && answered > 100 && unanswered > 100)
  IO.println s!"driver-test: {modules} Secure Modules started, {answered} requests answered and {unanswered} not"
  IO.println s!"driver-test: {started} devices started and {refused} refused; {opened} connections opened, {arrived} packets of data handed up"
  check "some devices were started and some refused" (started > 100 && refused > 10)
  check "connections were opened and data arrived, so the lies were told to a working driver" (opened > 50 && arrived > 50)
  let failed ← failures.get
  if failed == 0 then
    IO.println "driver-test: all checks passed"
    return 0
  else
    IO.eprintln s!"driver-test: {failed} check(s) failed"
    return 1
