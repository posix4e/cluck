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

Where whoever runs the host has a quoting service, the host makes the quote of a report it was sent.
Where there is none to go to (a cloud's machine), the machine is asked to have one made:

    "JQUO1", then a report (1,024 bytes)

and answers with a byte and what follows it: 0 and the quote; 1 and why the host made none; 2 when the
host took the request and never finished it, after which no more are asked. The machine asks the host
that carries it (`Kernel/Quote.lean`). It is handed a report and not 64 bytes to have reported: it
makes reports only of answers it gave (above), so a quote that says an answer was given is of an
answer that was. A report is not secret, and the quoting enclave signs only one made in a trust
domain on the same machine, so this lends out nothing but the host's own service.

The hash is Jaune's SHA-256, the one behind the EVM's precompile at address 2: its compression function and
its padding, with the walk over the bytes written here (`sha256`), because Jaune's own takes a list and a
request of a few million bytes as a list is more than this machine's heap. -/

open Jaune

namespace Evm.Attest

def tag : ByteArray := "JATT1".toUTF8

def quoteTag : ByteArray := "JQUO1".toUTF8

/-- The report of a request for a quote, or `none` for any other frame. -/
def quoted? (frame : ByteArray) : Option ByteArray :=
  if frame.size == quoteTag.size + 1024 && frame.extract 0 quoteTag.size == quoteTag then
    some (frame.extract quoteTag.size frame.size)
  else none

def challengeSize : Nat := 32

/-- The challenge and request of an attested frame, as one run of bytes, or `none` for any other frame. -/
def asked? (frame : ByteArray) : Option ByteArray :=
  if frame.size ≥ tag.size + challengeSize && frame.extract 0 tag.size == tag then
    some (frame.extract tag.size frame.size)
  else none

/-- The request inside what `asked?` returned. -/
def request (asked : ByteArray) : ByteArray := asked.extract challengeSize asked.size

/-- The 64 bytes from `start`, as Jaune's compression function takes a block. -/
private def block (bytes : ByteArray) (start : Nat) : Array UInt8 :=
  Array.ofFn (n := 64) fun i => bytes.get! (start + i)

/-- The state after the blocks numbered `i` and on, of the `whole` blocks the bytes hold. -/
private def blocks (bytes : ByteArray) (whole i : Nat) (state : Vector UInt32 8) : Vector UInt32 8 :=
  if i < whole then blocks bytes whole (i + 1) (SHA256.consumeChunk state (block bytes (64 * i))) else state
termination_by whole - i

/-- SHA-256 of a byte array, in memory that does not grow with it. Each whole block of 64 bytes goes to
Jaune's compression function from where it lies; what is left over, under 64 bytes, is padded by Jaune's own
padding, told the length of the whole. Nothing proves it equal to `Bytes.sha256` of the same bytes as a
list, which a request of a few million bytes cannot be made into here (a list of 4.5 million bytes ended the
guest); `evm-test` compares the two at every length to 300 and checks the standard's long example. -/
def sha256 (bytes : ByteArray) : ByteArray :=
  let whole := bytes.size / 64
  let state := blocks bytes whole 0 SHA256.initChunk
  let rest := (bytes.extract (64 * whole) bytes.size).toList
  let last := SHA256.Bytes.toChunks (UInt64.toBytes (bytes.size * 8).toUInt64) 1 rest rest.length
  let hash := last.foldl SHA256.consumeChunk state
  (UInt32s.toU256 hash[0] hash[1] hash[2] hash[3] hash[4] hash[5] hash[6] hash[7]).toBytes.toByteArray

/-- The 64 bytes of REPORTDATA for a response to what was asked. -/
def reportData (asked response : ByteArray) : ByteArray := sha256 asked ++ sha256 response

end Evm.Attest
