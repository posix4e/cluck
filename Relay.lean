import Demo

/-! # Talking to a demo service through a command's pipes

The service is reached by running a command and using its standard input and output: either the service
itself (the simulator), or a relay to wherever the service is (for an enclave's vsock,
`socat - VSOCK-CONNECT:<cid>:5005`). Used by the test of the service and by the parent's client. -/

namespace Relay

open Demo.Wire

partial def readExact (h : IO.FS.Handle) (n : Nat) (acc : ByteArray := ByteArray.empty) : IO ByteArray := do
  if acc.size ≥ n then return acc
  let chunk ← h.read (n - acc.size).toUSize
  if chunk.isEmpty then throw (IO.userError s!"the service closed its output after {acc.size} of {n} bytes")
  readExact h n (acc ++ chunk)

/-- Sends one payload and returns the payload that comes back. -/
def exchange (toService fromService : IO.FS.Handle) (payload : ByteArray) : IO ByteArray := do
  toService.write (frame payload)
  toService.flush
  let header ← readExact fromService 4
  let size := readU32be header 0
  if size > maxPayload then throw (IO.userError s!"the service announced a reply of {size} bytes")
  readExact fromService size

/-- Starts `cmd` with pipes to and from it. -/
def spawn (cmd : String) (args : Array String) :=
  IO.Process.spawn { cmd, args, stdin := .piped, stdout := .piped }

end Relay
