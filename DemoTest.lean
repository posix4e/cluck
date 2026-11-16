import Demo

/-! # Tests of the framing and the commands

Pure: nothing here starts a process or touches a device. Exits non-zero if any check fails. -/

open Demo Demo.Wire

def bytes (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩

def filled (n : Nat) (b : UInt8) : ByteArray := ⟨Array.replicate n b⟩

/-- Every payload `chunks` complete when fed in order, or the fault that stopped them. -/
def feedAll (chunks : List ByteArray) : Except Fault (Array ByteArray) := do
  let mut decoder : Decoder := {}
  let mut out := #[]
  for chunk in chunks do
    let (next, payloads) ← decoder.feed chunk
    decoder := next
    out := out ++ payloads
  return out

instance : BEq (Except Fault (Array ByteArray)) where
  beq
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false

/-- `b` one byte at a time. -/
def singly (b : ByteArray) : List ByteArray := b.toList.map fun x => bytes [x]

def isReply (a : Action) (expected : ByteArray) : Bool :=
  match a with
  | .reply payload => payload == expected
  | _ => false

def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  let check (name : String) (holds : Bool) : IO Unit := do
    unless holds do
      failures.modify (· + 1)
      IO.eprintln s!"FAIL {name}"
  -- Numbers
  for n in [0, 1, 255, 256, 65535, 65536, 0xFFFFFFFF] do
    check s!"u32be round trip {n}" (readU32be (u32be n) 0 == n && (u32be n).size == 4)
  check "u32be is big-endian" (u32be 0x01020304 == bytes [1, 2, 3, 4])
  -- Frames
  let hello := bytes [0x01, 0x68, 0x69]
  let other := bytes [0x7F]
  check "one frame" (feedAll [frame hello] == .ok #[hello])
  check "two frames in one piece" (feedAll [frame hello ++ frame other] == .ok #[hello, other])
  check "a frame a byte at a time" (feedAll (singly (frame hello ++ frame other)) == .ok #[hello, other])
  check "an incomplete frame yields nothing" (feedAll [(frame hello).extract 0 6] == .ok #[])
  check "an empty payload is a fault" (feedAll [u32be 0] == .error .empty)
  check "an oversized header is a fault before any payload"
    (feedAll [u32be (maxPayload + 1)] == .error (.tooLarge (maxPayload + 1)))
  check "the largest payload passes" (feedAll [frame (filled maxPayload 0xAB)] == .ok #[filled maxPayload 0xAB])
  check "a fault after a good frame still faults" (feedAll [frame hello ++ u32be 0] == .error .empty)
  -- Commands
  check "ping echoes its body" (isReply (decide hello) (bytes [0x81, 0x68, 0x69]))
  check "ping with no body" (isReply (decide (bytes [0x01])) (bytes [0x81]))
  check "an unknown command is refused" (isReply (decide other) (bytes [0xFF, 0x01]))
  check "an empty payload is malformed" (isReply (decide ByteArray.empty) (bytes [0xFF, 0x02]))
  check "attest takes a nonce of up to 64 bytes"
    (match decide (bytes [0x02] ++ filled 64 7) with | .attest nonce => nonce == filled 64 7 | _ => false)
  check "attest refuses a longer nonce" (isReply (decide (bytes [0x02] ++ filled 65 7)) (bytes [0xFF, 0x02]))
  check "random takes a count" (match decide (bytes [0x03, 0x01, 0x00]) with | .random 256 => true | _ => false)
  check "random refuses zero" (isReply (decide (bytes [0x03, 0x00, 0x00])) (bytes [0xFF, 0x02]))
  check "random refuses more than 256" (isReply (decide (bytes [0x03, 0x01, 0x01])) (bytes [0xFF, 0x02]))
  check "random refuses a short body" (isReply (decide (bytes [0x03, 0x20])) (bytes [0xFF, 0x02]))
  check "selftest takes no body" (match decide (bytes [0x04]) with | .selfTest => true | _ => false)
  check "selftest refuses a body" (isReply (decide (bytes [0x04, 0x00])) (bytes [0xFF, 0x02]))
  let failed ← failures.get
  if failed == 0 then
    IO.println "demo-test: all checks passed"
    return 0
  else
    IO.eprintln s!"demo-test: {failed} check(s) failed"
    return 1
