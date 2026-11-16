import Demo
import SelfTest
import Relay

/-! # ask: the parent's side of the demo service

    ask ping [text]                  -- <relay command> [arguments...]
    ask random <count>               -- ...
    ask selftest                     -- ...
    ask attest <nonce in hex> <file> -- ...

Makes one request of a running service and reports the answer. The service is reached through the relay
command's pipes; for an enclave that is `socat - VSOCK-CONNECT:<enclave's cid>:5005`, run on its parent.

`attest` writes the attestation document to the file, as the enclave returned it, for
`verify/verify-attestation` to judge somewhere else: this program does not decide whether a document is
any good. `selftest` compares the digest the service computed on its runtime with the one computed here on
Lean's own.

The exit status is 0 if the service did what was asked. -/

open Demo

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

def unhex (s : String) : Option ByteArray := do
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let rec go : List Char → ByteArray → Option ByteArray
    | [], out => some out
    | high :: low :: rest, out => do go rest (out.push ((← digit high) * 16 + (← digit low)).toUInt8)
    | [_], _ => none
  go s.toList ByteArray.empty

/-- What the service said, if it did the thing: the reply's body. -/
def answer (command : UInt8) (reply : ByteArray) : Except String ByteArray :=
  if reply.size ≥ 1 ∧ reply[0]! == (command ||| 0x80) then .ok (reply.extract 1 reply.size)
  else if reply.size == 2 ∧ reply[0]! == 0xFF then
    .error (match reply[1]! with
      | 0x01 => "the service does not know that command"
      | 0x02 => "the service found the request malformed"
      | 0x03 => "the service cannot do that on this machine"
      | code => s!"the service refused with code {code}")
  else .error "the service's reply is not one this program understands"

def usage : IO UInt32 := do
  IO.eprintln "usage: ask ping [text] | random <count> | selftest | attest <nonce in hex> <file>"
  IO.eprintln "           -- <relay command> [arguments...]"
  return 2

def main (args : List String) : IO UInt32 := do
  let request := args.takeWhile (· != "--")
  let relay := (args.dropWhile (· != "--")).drop 1
  let cmd :: relayArgs := relay | usage
  -- The request's command byte and payload, and what to do with the reply's body.
  let plan : Option (UInt8 × ByteArray × (ByteArray → IO UInt32)) ← match request with
    | "ping" :: text =>
      pure (some (cmdPing, (" ".intercalate text).toUTF8, fun reply => do
        IO.println s!"ping: {String.fromUTF8! reply}"
        return 0))
    | ["random", count] =>
      match count.toNat? with
      | some n => pure (some (cmdRandom, ByteArray.empty.push (n / 256).toUInt8 |>.push (n % 256).toUInt8,
          fun reply => do
            IO.println (hex reply)
            return if reply.size == n then 0 else 1))
      | none => pure none
    | ["selftest"] =>
      pure (some (cmdSelfTest, ByteArray.empty, fun reply => do
        let same := reply == SelfTest.digest
        IO.println s!"selftest: the service's digest is {hex reply}, {if same then "the same as" else "NOT"} \
          the one computed here"
        return if same then 0 else 1))
    | ["attest", nonce, file] =>
      match unhex nonce with
      | some nonce => pure (some (cmdAttest, nonce, fun reply => do
          IO.FS.writeBinFile file reply
          IO.println s!"attest: wrote a document of {reply.size} bytes to {file}"
          return 0))
      | none => pure none
    | _ => pure none
  let some (command, payload, report) := plan | usage
  let child ← Relay.spawn cmd relayArgs.toArray
  let reply ← Relay.exchange child.stdin child.stdout ((ByteArray.empty.push command) ++ payload)
  let (toService, child) ← child.takeStdin
  drop toService
  let _ ← child.wait
  match answer command reply with
  | .ok reply => report reply
  | .error why =>
    IO.eprintln s!"ask: {why}"
    return 1
where
  /-- Lets go of a handle, which closes it. -/
  drop (_ : IO.FS.Handle) : IO Unit := pure ()
