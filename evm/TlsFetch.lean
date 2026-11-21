import Tls

/-! Drives `Tls/Client.lean` over a real connection, for testing it against other people's servers.

    tls-fetch HOST PATH NOW OUT ROOT.der...        with the connection as standard input and output

It asks HOST for PATH over TLS on the connection it was started with (`scripts/tls-get` makes one), judges
certificates at the time NOW (seconds since 1970) against the roots given, writes the answer's body to OUT
(`-` for nowhere) and says on standard error what happened. Exit status 0 for an answer, 1 for a refusal
or a failure. This is a program for the host: the guest will move the bytes itself. -/
open Tls

/-- Exactly `n` bytes of `h`, or fewer if it ends. -/
partial def readExactly (h : IO.FS.Stream) (n : Nat) (soFar : ByteArray := .empty) : IO ByteArray := do
  if soFar.size ≥ n then return soFar
  let more ← h.read (n - soFar.size).toUSize
  if more.isEmpty then return soFar else readExactly h n (soFar ++ more)

def main (args : List String) : IO UInt32 := do
  let host :: path :: now :: out :: roots := args
    | do IO.eprintln "usage: tls-fetch HOST PATH NOW OUT ROOT.der..."; return 2
  let mut anchors := #[]
  for root in roots do
    match X509.Anchor.of (← IO.FS.readBinFile root) with
    | some anchor => anchors := anchors.push anchor
    | none => IO.eprintln s!"tls-fetch: {root} is not a certificate this reads"; return 2
  let wire ← IO.getStdin
  let back ← IO.getStdout
  let (begun, hello) := Client.start host.toUTF8 anchors now.toNat! (← IO.getRandomBytes 32) (← IO.getRandomBytes 32)
  back.write hello
  back.flush
  let mut c := begun
  let mut asked := false
  let mut got := ByteArray.empty
  let mut records := 0
  for _ in [0:100000] do
    -- One record at a time: its five bytes of heading say how long it is.
    let heading ← readExactly wire 5
    let length := if heading.size == 5 then heading[3]!.toNat * 256 + heading[4]!.toNat else 0
    let body ← readExactly wire length
    let ended := heading.size < 5 || body.size < length
    let step := c.receive (heading ++ body)
    c := step.client
    got := got ++ step.data
    records := records + 1
    let mut toSend := step.send
    if c.stage == .ready && !asked then
      let (next, sealed) := c.write (Http.request "GET" host.toUTF8 path #[("User-Agent", "research"), ("Accept", "*/*"), ("Connection", "close")])
      c := next
      toSend := toSend ++ sealed
      asked := true
    if !toSend.isEmpty then
      back.write toSend
      back.flush
    if let .failed why := c.stage then
      IO.eprintln s!"refused: {why}"
      return 1
    let over := ended || c.stage == .closed
    match Http.response got over with
    | .whole answer _ =>
      if out != "-" then IO.FS.writeBinFile out answer.body
      let (_, bye) := c.close
      back.write bye
      back.flush
      IO.eprintln s!"answered: HTTP {answer.status}, {answer.body.size} bytes, in {records} records"
      return 0
    | .broken why =>
      IO.eprintln s!"failed: an answer that cannot be read ({why})"
      return 1
    | .more =>
      if over then
        IO.eprintln (if asked then "failed: the connection ended before an answer" else "failed: the connection ended before the handshake did")
        return 1
  IO.eprintln "failed: too many records"
  return 1
