import Demo.Wire

/-! # The demo service

What the OS milestone serves, so that there is something to ask an enclave: a payload's first byte is the
command, the rest its body. A reply's first byte is the command with the top bit set, or `0xFF` followed by
a refusal code.

`decide` is pure. Commands that need the machine (an attestation document, random bytes, the self-test)
come back as an `Action` for the platform underneath to carry out, so the same decision runs in the
simulator and on bare metal. -/

namespace Demo

/-- Command bytes. -/
def cmdPing : UInt8 := 0x01
def cmdAttest : UInt8 := 0x02
def cmdRandom : UInt8 := 0x03
def cmdSelfTest : UInt8 := 0x04

/-- Refusal codes, the byte after `0xFF`. -/
inductive Refusal where
  /-- The command byte is not one of ours. -/
  | unknownCommand
  /-- The body does not have the shape the command needs. -/
  | malformed
  /-- This platform cannot do it (the simulator has no attestation device). -/
  | unavailable
  deriving Repr, BEq, DecidableEq

def Refusal.code : Refusal → UInt8
  | .unknownCommand => 0x01
  | .malformed => 0x02
  | .unavailable => 0x03

/-- The longest nonce `attest` accepts and the most bytes one `random` returns. -/
def maxNonce : Nat := 64
def maxRandom : Nat := 256

/-- What to do about one request. -/
inductive Action where
  /-- Send this payload back. -/
  | reply (payload : ByteArray)
  /-- Fetch an attestation document carrying `nonce` and send it back. -/
  | attest (nonce : ByteArray)
  /-- Send back `count` bytes from the platform's random source. -/
  | random (count : Nat)
  /-- Run the runtime self-test and send back its digest. -/
  | selfTest

def ok (command : UInt8) (body : ByteArray) : ByteArray := (ByteArray.empty.push (command ||| 0x80)) ++ body

def refusal (r : Refusal) : ByteArray := ByteArray.empty.push 0xFF |>.push r.code

/-- The body of a payload: everything after its command byte. -/
def body (payload : ByteArray) : ByteArray := payload.extract 1 payload.size

def decide (payload : ByteArray) : Action :=
  if payload.isEmpty then .reply (refusal .malformed) else
  let command := payload[0]!
  let b := body payload
  if command == cmdPing then .reply (ok cmdPing b)
  else if command == cmdAttest then
    if b.size ≤ maxNonce then .attest b else .reply (refusal .malformed)
  else if command == cmdRandom then
    if b.size == 2 then
      let count := (b[0]!.toNat <<< 8) ||| b[1]!.toNat
      if 0 < count && count ≤ maxRandom then .random count else .reply (refusal .malformed)
    else .reply (refusal .malformed)
  else if command == cmdSelfTest then
    if b.isEmpty then .selfTest else .reply (refusal .malformed)
  else .reply (refusal .unknownCommand)

end Demo
