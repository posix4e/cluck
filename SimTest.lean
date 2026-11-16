import Demo
import SelfTest
import Relay

/-! # Driving a running demo service

`sim-test <path>` starts the service at `path`, talks to it over its pipes and checks the replies. It checks
only what every platform answers the same way, so the same test holds the service on Lean's runtime and on
the minimal runtime to one behaviour.

`sim-test --socket <command> [arguments...]` is the same conversation with a service that is somewhere else:
the command is a relay between its own pipes and that service (for a vsock, `socat - VSOCK-CONNECT:16:5005`),
started once per connection. -/

open Demo Demo.Wire Relay

def bytes (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩

/-- How the service under test is reached: the command to run, and whether that command is a relay to a
service that lives elsewhere and outlives it (a socket), not the service itself (a process on pipes). -/
structure Target where
  cmd : String
  args : Array String
  relay : Bool

def Target.spawn (t : Target) := Relay.spawn t.cmd t.args

def main (args : List String) : IO UInt32 := do
  let target? : Option Target :=
    match args with
    | "--socket" :: cmd :: rest => some { cmd, args := rest.toArray, relay := true }
    | cmd :: rest => if cmd.startsWith "--" then none else some { cmd, args := rest.toArray, relay := false }
    | [] => none
  let some target := target? | do
    IO.eprintln "usage: sim-test <service> [arguments...]"
    IO.eprintln "       sim-test --socket <relay command> [arguments...]"
    return 2
  let failures ← IO.mkRef 0
  let check (name : String) (holds : Bool) : IO Unit := do
    unless holds do
      failures.modify (· + 1)
      IO.eprintln s!"FAIL {name}"
  -- A conversation, ended by closing the service's input.
  let child ← target.spawn
  let ask := exchange child.stdin child.stdout
  check "ping" ((← ask (bytes [0x01, 0x68, 0x69])) == bytes [0x81, 0x68, 0x69])
  check "ping with no body" ((← ask (bytes [0x01])) == bytes [0x81])
  let big : ByteArray := ⟨Array.replicate (maxPayload - 1) 0x5A⟩
  check "ping with the largest body" ((← ask (bytes [0x01] ++ big)) == bytes [0x81] ++ big)
  check "unknown command" ((← ask (bytes [0x7F])) == bytes [0xFF, 0x01])
  check "malformed random" ((← ask (bytes [0x03, 0x00, 0x00])) == bytes [0xFF, 0x02])
  let first ← ask (bytes [0x03, 0x00, 0x20])
  let second ← ask (bytes [0x03, 0x00, 0x20])
  check "random returns the count asked for" (first.size == 33 && first[0]! == 0x83 && second.size == 33)
  check "random does not repeat" (first != second)
  -- The service runs the runtime self-test on whatever runtime it is linked against; this process runs it on
  -- Lean's own. The digests must agree.
  check "selftest digest matches the one computed here" ((← ask (bytes [0x04])) == bytes [0x84] ++ SelfTest.digest)
  check "still answering after all that" ((← ask (bytes [0x01, 0x21])) == bytes [0x81, 0x21])
  let (toService, child) ← child.takeStdin
  drop toService
  check "ends cleanly when its input ends" ((← child.wait) == 0)
  -- A stream that is not frames.
  let child ← target.spawn
  child.stdin.write (u32be (maxPayload + 1))
  child.stdin.flush
  if target.relay then
    -- A service behind a socket hangs up on the connection and goes on serving the next one.
    check "hangs up on an oversized header" ((← child.stdout.read 1).isEmpty)
    let _ ← child.wait
    let child ← target.spawn
    check "and still answers a new connection" ((← exchange child.stdin child.stdout (bytes [0x01, 0x07])) == bytes [0x81, 0x07])
    let (toService, child) ← child.takeStdin
    drop toService
    let _ ← child.wait
  else
    check "exits 1 on an oversized header, without waiting for its payload" ((← child.wait) == 1)
  let failed ← failures.get
  let what := " ".intercalate (target.cmd :: target.args.toList)
  if failed == 0 then
    IO.println s!"sim-test: all checks passed against {what}"
    return 0
  else
    IO.eprintln s!"sim-test: {failed} check(s) failed against {what}"
    return 1
where
  /-- Lets go of a handle, which closes it. -/
  drop (_ : IO.FS.Handle) : IO Unit := pure ()
