import Demo
import Platform
import SelfTest
import Kernel.Server

/-! # The demo service on bare metal

The whole machine: find the socket device and the Secure Module, listen, and answer the demo protocol on every
connection the parent opens. The same `Demo.decide` and the same framing as the simulator; what differs is that the bytes
come through the vsock driver in this repository and not through an operating system.

Progress is printed on the serial port. Nothing the parent sends is ever printed. -/

open Kernel Demo

/-- Where the parent connects. -/
def servicePort : UInt32 := 5005

/-- Carries out one action the way this machine can. An attestation document can only come from the Secure
Module. So do random bytes on a machine that has one: if it then fails, the request is refused, and nothing
quietly falls back to the processor's generator, which is what a machine without the module uses. -/
def perform (module : Option SecureModule) : Action → IO (ByteArray × Option SecureModule)
  | .reply payload => pure (payload, module)
  | .selfTest => pure (ok cmdSelfTest SelfTest.digest, module)
  | .attest nonce =>
    match module with
    | none => pure (refusal .unavailable, none)
    | some m => do
      let (document, m) ← m.attest nonce
      return (document.elim (refusal .unavailable) (ok cmdAttest), some m)
  | .random count => do
    let (bytes, module) ← randomBytes module count
    return (bytes.elim (refusal .unavailable) (ok cmdRandom), module)

/-- The demo service: what it keeps is the Secure Module, and each connection has the frames it has sent
part of. A connection that stops sending frames is hung up on. -/
def demo : Service (Option SecureModule) Wire.Decoder where
  fresh := {}
  receive module decoder bytes := do
    match decoder.feed bytes with
    | .error _ => return (module, none, ByteArray.empty)
    | .ok (decoder, payloads) =>
      let mut module := module
      let mut replies := ByteArray.empty
      for payload in payloads do
        let (reply, module') ← perform module (decide payload)
        module := module'
        replies := replies ++ Wire.frame reply
      return (module, some decoder, replies)

def main : IO UInt32 := run servicePort demo fun module => pure (.ok module)
