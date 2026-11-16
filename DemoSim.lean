import Demo
import Platform
import SelfTest

/-! # The demo service as an ordinary process

The service over a pipe: requests on standard input, replies on standard output. The same program is linked
twice, once with Lean's own runtime (`demo-sim`, the reference) and once with the minimal runtime
(`demo-sim-min`), and the two are held to the same behaviour. It has no attestation device, so `attest` is
refused as unavailable.

Bytes are read in whatever pieces they arrive and go through `Wire.Decoder`, as they will on bare metal. -/

open Demo

/-- Carries out one action the way this platform can. -/
def perform : Action → IO ByteArray
  | .reply payload => pure payload
  | .attest _ => pure (refusal .unavailable)
  | .random count => do return ok cmdRandom (← Platform.random count.toUSize)
  | .selfTest => pure (ok cmdSelfTest SelfTest.digest)

/-- Serves until the input ends (exit 0) or stops being frames (exit 1). -/
partial def serve (decoder : Wire.Decoder) : IO UInt32 := do
  let chunk ← Platform.read 4096
  if chunk.isEmpty then return 0
  match decoder.feed chunk with
  | .error _ => return 1
  | .ok (decoder, payloads) =>
    for payload in payloads do
      Platform.write (Wire.frame (← perform (decide payload)))
    serve decoder

def main : IO UInt32 := serve {}
