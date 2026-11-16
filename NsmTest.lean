import Kernel.Nsm

/-! # Tests of the Nitro Secure Module messages

The requests, byte for byte; the responses, read; and every way a response can be nearly right. Then noise.
Pure: no device, so nothing here shows that the real module agrees. The request bytes for `GetRandom` are
the ones Linux's `nsm` driver sends, and the response prefix is the one it expects. -/

open Kernel.Nsm

def unhex (s : String) : ByteArray := Id.run do
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  let cs := s.toList.filter (!·.isWhitespace)
  let mut out := ByteArray.empty
  let mut rest := cs
  for _ in [0:cs.length / 2] do
    match rest with
    | a :: b :: tail =>
      out := out.push (digit a * 16 + digit b).toUInt8
      rest := tail
    | _ => pure ()
  return out

def filled (n : Nat) (b : UInt8) : ByteArray := ⟨Array.replicate n b⟩

def isRandom (r : Option Response) (expected : ByteArray) : Bool :=
  match r with | some (.random b) => b == expected | _ => false

def isDocument (r : Option Response) (expected : ByteArray) : Bool :=
  match r with | some (.attestation b) => b == expected | _ => false

def isError (r : Option Response) (expected : String) : Bool :=
  match r with | some (.error code) => code == expected | _ => false

/-- `{"GetRandom": {"random": ` as Linux's driver spells it out. -/
def randomPrefix : ByteArray := unhex "A1 69 47657452616E646F6D A1 66 72616E646F6D"

/-- `{"Attestation": {"document": `. -/
def documentPrefix : ByteArray := unhex "A1 6B 4174746573746174696F6E A1 68 646F63756D656E74"

def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  let check (name : String) (holds : Bool) : IO Unit := do
    unless holds do
      failures.modify (· + 1)
      IO.eprintln s!"FAIL {name}"
  -- Heads, in each width.
  check "head, short" (head 2 23 == unhex "57")
  check "head, one byte" (head 2 24 == unhex "5818" && head 2 255 == unhex "58FF")
  check "head, two bytes" (head 2 256 == unhex "590100" && head 2 65535 == unhex "59FFFF")
  check "head, four bytes" (head 2 65536 == unhex "5A00010000")
  check "head, eight bytes" (head 2 0x100000000 == unhex "5B0000000100000000")
  -- Requests.
  check "GetRandom is what Linux sends" (getRandom == unhex "69 47657452616E646F6D")
  check "attestation with a nonce only"
    (attestation none (some (unhex "010203")) none == some (unhex ("A1 6B 4174746573746174696F6E A3" ++
      "69 757365725F64617461 F6" ++ "65 6E6F6E6365 43 010203" ++ "6A 7075626C69635F6B6579 F6")))
  check "attestation with everything"
    (attestation (some (unhex "AA")) (some (unhex "BB")) (some (unhex "CC")) == some (unhex
      ("A1 6B 4174746573746174696F6E A3" ++ "69 757365725F64617461 41 AA" ++ "65 6E6F6E6365 41 BB" ++
        "6A 7075626C69635F6B6579 41 CC")))
  check "attestation with a long field uses a longer head"
    ((attestation (some (filled 300 7)) none none).map (·.size) == some (1 + 12 + 1 + 10 + 3 + 300 + 6 + 1 + 11 + 1))
  check "an attestation request too large for the device is not made"
    ((attestation (some (filled 5000 7)) none none).isNone)
  -- Responses.
  let random32 := filled 32 0x5A
  check "random bytes" (isRandom (Response.parse? (randomPrefix ++ unhex "5820" ++ random32)) random32)
  let random256 := filled 256 0xA5
  check "256 random bytes, two-byte length" (isRandom (Response.parse? (randomPrefix ++ unhex "590100" ++ random256)) random256)
  check "no random bytes" (isRandom (Response.parse? (randomPrefix ++ unhex "40")) ByteArray.empty)
  let document := filled 4500 0x33
  check "a document" (isDocument (Response.parse? (documentPrefix ++ unhex "591194" ++ document)) document)
  check "an error" (isError (Response.parse? (unhex "A1 65 4572726F72 6F 496E76616C6964417267756D656E74")) "InvalidArgument")
  -- Nearly right.
  let good := randomPrefix ++ unhex "5820" ++ random32
  check "cut short" ((Response.parse? (good.extract 0 (good.size - 1))).isNone)
  check "a byte left over" ((Response.parse? (good.push 0)).isNone)
  check "length longer than what follows" ((Response.parse? (randomPrefix ++ unhex "5821" ++ random32)).isNone)
  check "text where bytes belong" ((Response.parse? (randomPrefix ++ unhex "7820" ++ random32)).isNone)
  check "an indefinite length" ((Response.parse? (randomPrefix ++ unhex "5F" ++ random32 ++ unhex "FF")).isNone)
  check "two entries where one belongs"
    ((Response.parse? (unhex "A2 69 47657452616E646F6D A1 66 72616E646F6D 40 61 78 F6")).isNone)
  check "the wrong field name" ((Response.parse? (unhex "A1 69 47657452616E646F6D A1 66 72616E646F6E 40")).isNone)
  check "a random answer under the attestation name"
    ((Response.parse? (unhex "A1 6B 4174746573746174696F6E A1 66 72616E646F6D 40")).isNone)
  check "an error code that is not a name" ((Response.parse? (unhex "A1 65 4572726F72 63 41 0A 42")).isNone)
  check "nothing" ((Response.parse? ByteArray.empty).isNone)
  check "larger than the device can answer" ((Response.parse? (documentPrefix ++ head 2 12300 ++ filled 12300 1)).isNone)
  check "the largest length that claims to fit, with nothing behind it"
    ((Response.parse? (randomPrefix ++ unhex "5BFFFFFFFFFFFFFFFF")).isNone)
  -- Noise, and good answers with one byte changed: none may be read as something it is not, and none may
  -- stop the program. A changed byte inside the payload still reads, as a different payload.
  let mut state : UInt64 := 0x4E534D54455354
  let mut read := 0
  let mut refused := 0
  for i in [0:200000] do
    state := state * 6364136223846793005 + 1442695040888963407
    let r := (state >>> 33).toNat
    let candidate :=
      if i % 2 == 0 then
        (List.range (r % 60)).foldl (fun b j => b.push ((state >>> (j % 56).toUInt64).toUInt8 + j.toUInt8)) ByteArray.empty
      else
        let base := if i % 4 == 1 then good else documentPrefix ++ unhex "43010203"
        base.set! (r % base.size) (r / 256).toUInt8
    match Response.parse? candidate with
    | some (.random b) => read := read + 1; check "a read random answer is no longer than its input" (b.size < candidate.size)
    | some (.attestation b) => read := read + 1; check "a read document is no longer than its input" (b.size < candidate.size)
    | some (.error _) => read := read + 1
    | none => refused := refused + 1
  check "the noise run read some and refused some" (read > 1000 && refused > 1000)
  IO.println s!"noise: {read} read, {refused} refused"
  -- The time in an attestation document: the two a real enclave returned (run from the repo root), and
  -- made-up ones.
  let real ← IO.FS.readBinFile "verify/vectors/enclave.bin"
  let debug ← IO.FS.readBinFile "verify/vectors/enclave-debug.bin"
  check "the time in a real document" (documentTime? real == some 1794767570427)
  check "the time in the other real document" (documentTime? debug == some 1794767625690)
  check "a real document cut short has no time" (documentTime? (real.extract 0 60) == none)
  -- [h'', {}, payload, h''] with the payload a map of known size: {"digest": "SHA384", "timestamp": 1000}
  let payload := unhex "A2 66 646967657374 66 534841333834 69 74696D657374616D70 19 03E8"
  let document (payload : ByteArray) : ByteArray := unhex "84 40 A0" ++ bytes payload ++ unhex "40"
  check "the time in a map of known size" (documentTime? (document payload) == some 1000)
  check "and with the COSE tag in front" (documentTime? (unhex "D2" ++ document payload) == some 1000)
  -- the time behind members of every other kind: an array, a nested map of indefinite length, a tag
  let busy := unhex "BF 61 61 83 01 02 03 61 62 BF 61 78 9F 01 FF FF 61 63 C1 00 69 74696D657374616D70 1A 000F4240 FF"
  check "the time behind members of other kinds" (documentTime? (document busy) == some 1000000)
  check "a document with no time" (documentTime? (document (unhex "A1 66 646967657374 66 534841333834")) == none)
  check "a time that is not a number" (documentTime? (document (unhex "A1 69 74696D657374616D70 61 31")) == none)
  check "a payload that is not a map" (documentTime? (document (unhex "83 01 02 03")) == none)
  check "something that is not a document" (documentTime? (unhex "A1 01 02") == none)
  check "nothing at all" (documentTime? ByteArray.empty == none)
  -- Noise: a real document with bytes changed is read or refused, and reading never looks outside it.
  let mut timed := 0
  let mut untimed := 0
  let mut seed : UInt64 := 0x1234567
  for _ in [0:3000] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let r := (seed >>> 33).toNat
    let changed := real.set! (r % 400) (r / 1024).toUInt8
    match documentTime? changed with
    | some _ => timed := timed + 1
    | none => untimed := untimed + 1
  check "changed documents: some still give a time and some do not" (timed > 100 && untimed > 100)
  IO.println s!"changed documents: {timed} with a time, {untimed} without"
  let failed ← failures.get
  if failed == 0 then
    IO.println "nsm-test: all checks passed"
    return 0
  else
    IO.eprintln s!"nsm-test: {failed} check(s) failed"
    return 1
