import Evm.Service

/-! # An answer a relying party can tie to this machine

A plain request is answered with the 69 bytes of the response and nothing that says who computed them. An
attested request is a plain one with a tag and a challenge in front:

    "JATT1", challenge (32 bytes), then a request as `Evm.Service` reads it

and its answer is the same 69 bytes followed, in a trust domain, by the 1024-byte TDREPORT whose REPORTDATA
is

    SHA-256(challenge ++ request) ++ SHA-256(response)

Whoever has that report turned into a quote and checks the quote's signature learns that a machine with the
quoted measurements gave this response to this request after the challenge was chosen. The measurements say
which firmware and which image; they are for the relying party to compare with ones it has reason to trust.

Outside a trust domain there is no report and the answer is the 69 bytes alone, so an answer never carries
bytes that look like a report and are not one.

The hash is Jaune's SHA-256, the one behind the EVM's precompile at address 2. -/

open Jaune

namespace Evm.Attest

def tag : ByteArray := "JATT1".toUTF8

def challengeSize : Nat := 32

/-- The challenge and request of an attested frame, as one run of bytes, or `none` for any other frame. -/
def asked? (frame : ByteArray) : Option ByteArray :=
  if frame.size ≥ tag.size + challengeSize && frame.extract 0 tag.size == tag then
    some (frame.extract tag.size frame.size)
  else none

/-- The request inside what `asked?` returned. -/
def request (asked : ByteArray) : ByteArray := asked.extract challengeSize asked.size

def sha256 (bytes : ByteArray) : ByteArray := (Bytes.sha256 bytes.toList).toBytes.toByteArray

/-- The 64 bytes of REPORTDATA for a response to what was asked. -/
def reportData (asked response : ByteArray) : ByteArray := sha256 asked ++ sha256 response

end Evm.Attest
