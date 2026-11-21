import Tls
import Platform
import Std.Data.HashMap

/-! `evm/Tls/` against the standards' examples and against OpenSSL.

    cat Tls/vectors.txt Tls/handshakes.txt | .lake/build/bin/tls-test        (from evm/)

and the same into `tls-test-min` after `scripts/build-min tls-test`. `Tls/handshakes.txt` is made by
`scripts/tls-handshakes`: whole conversations with a TLS 1.3 server written there, which the client in
`Tls/Client.lean` must come through, or refuse for the reason given.

The file of cases is made by `scripts/tls-vectors` from Python's hashlib and `cryptography` package. For
each case the same inputs are given to the Lean and the answers must be the same bytes; for a signature or
a chain of certificates the answer is whether it holds, and the cases have both kinds: signatures OpenSSL
made and the same with a bit changed, chains made for the purpose that are good, for another name, out of
date, under another root, out of order or badly signed, and the chains four relays served, each against
each root in this machine's store. Beside the file:
the examples printed in FIPS 180-4 and RFC 7748, a sealed message that must not open once any one bit of
it, of its tag, of the data beside it or of its key is changed, and X25519's own check that two sides
arrive at the same secret. -/
open Tls

/-- Bytes from their hexadecimal digits, themselves as bytes; `-` is no bytes. -/
def unhexBytes (s : ByteArray) : ByteArray :=
  let digit (c : UInt8) : UInt8 := if c ≤ 0x39 then c - 0x30 else c - 0x57
  (List.range (s.size / 2)).foldl (fun out i => out.push (digit s[2 * i]! * 16 + digit s[2 * i + 1]!)) ByteArray.empty

def unhex (s : String) : ByteArray := unhexBytes s.toUTF8

def hex (b : ByteArray) : String :=
  b.foldl (fun out x => out ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

def verdict (yes : Bool) : ByteArray := (if yes then "ok" else "no").toUTF8

partial def readAll (soFar : ByteArray) : IO ByteArray := do
  let chunk ← Platform.read 65536
  if chunk.isEmpty then pure soFar else readAll (soFar ++ chunk)

def say (s : String) : IO Unit := Platform.write (s ++ "\n").toUTF8

/-- Bytes that are plain letters, as a string. -/
def ascii (b : ByteArray) : String := String.ofList (b.toList.map fun c => Char.ofNat c.toNat)

/-- `b` cut at each byte `mark`. -/
def cut (b : ByteArray) (mark : UInt8) : Array ByteArray := Id.run do
  let mut parts := #[]
  let mut start := 0
  for i in [0:b.size] do
    if b[i]! == mark then
      parts := parts.push (b.extract start i)
      start := i + 1
  return if start < b.size then parts.push (b.extract start b.size) else parts

/-- Whether `needle` lies somewhere in `hay`. -/
def contains (hay needle : ByteArray) : Bool :=
  (List.range (hay.size + 1 - needle.size)).any fun i => hay.extract i (i + needle.size) == needle

/-- A whole conversation with a server whose every byte is given: the client's first message, then what
came of the server's bytes (how the connection stands, what the client sent back, the data that came out,
and the record it makes of "ping"), and its reason if it refused. The server's bytes arrive all at once,
or with `pieces` not zero a few at a time, in pieces of changing size. -/
def converse (host : ByteArray) (now : Nat) (anchor random key flight : ByteArray) (pieces : Nat) : ByteArray × ByteArray × String := Id.run do
  let anchors := match X509.Anchor.of anchor with | some a => #[a] | none => #[]
  let (begun, hello) := Client.start host anchors now random key
  let mut c := begun
  let mut sent := ByteArray.empty
  let mut data := ByteArray.empty
  let mut pos := 0
  for turn in [0:flight.size + 1] do
    if pos ≥ flight.size then break
    let size := if pieces == 0 then flight.size else 1 + (turn * 7 + pieces) % 23
    let step := c.receive (flight.extract pos (pos + size))
    c := step.client
    sent := sent ++ step.send
    data := data ++ step.data
    pos := pos + size
  let (verdict, why) := match c.stage with
    | .ready => ("ok", "") | .closed => ("closed", "") | .failed why => ("no", why) | _ => ("waiting", "")
  let bar := ByteArray.mk #[0x7c]
  return (hello, verdict.toUTF8 ++ bar ++ sent ++ bar ++ data ++ bar ++ (c.write "ping".toUTF8).2, why)

def main : IO UInt32 := do
  let mut failures := 0
  let mut counts : Std.HashMap String Nat := {}
  for line in cut (← readAll .empty) 0x0a do
    let fields := cut line 0x20
    let kind := ascii (fields.getD 0 .empty)
    let f (i : Nat) : ByteArray := unhexBytes (fields.getD i .empty)
    let n (i : Nat) : Nat := (fields.getD i .empty).foldl (fun n c => n * 10 + (c.toNat - 48)) 0
    if kind == "handshake" then
      counts := counts.insert kind (counts.getD kind 0 + 1)
      let (hello, whole, why) := converse (f 2) (n 3) (f 4) (f 5) (f 6) (f 8) 0
      let (_, inPieces, _) := converse (f 2) (n 3) (f 4) (f 5) (f 6) (f 8) 3
      let bar := ByteArray.mk #[0x7c]
      let want := f 9 ++ bar ++ f 11 ++ bar ++ f 12 ++ bar ++ f 13
      let wrong := (if hello != f 7 then "its first message; " else "")
        ++ (if whole != want then s!"what came of it ({ascii ((cut whole 0x7c).getD 0 .empty)} {why}); " else "")
        ++ (if inPieces != whole then "what came of it a few bytes at a time; " else "")
        ++ (if !contains why.toUTF8 (f 10) then s!"its reason ({why}); " else "")
      if wrong != "" then
        failures := failures + 1
        say s!"handshake {ascii (fields.getD 1 .empty)}: wrong in {wrong}"
      continue
    let (got, want) : ByteArray × ByteArray :=
      match kind with
      | "sha256" => (Sha256.hash (f 1), f 2)
      | "sha384" => (Sha512.hash384 (f 1), f 2)
      | "sha512" => (Sha512.hash512 (f 1), f 2)
      | "hmac" => (hmac (f 1) (f 2), f 3)
      | "hkdf" => (Hkdf.expand (Hkdf.extract (if (f 1).size == 0 then ByteArray.mk (Array.replicate 32 0) else f 1) (f 2)) (f 3) (n 4), f 5)
      | "label" => (Hkdf.expandLabel (f 1) (ascii (f 2)) (f 3) (n 4), f 5)
      | "aead" =>
        -- Sealing gives the library's bytes, and they open to what was sealed.
        let sealed := Aead.encrypt (f 1) (f 2) (f 3) (f 4)
        (sealed ++ ((Aead.decrypt? (f 1) (f 2) (f 3) (f 5)).getD (ByteArray.mk #[0xee])), f 5 ++ f 4)
      | "poly1305" => (Poly1305.tag (f 1) (f 2), f 3)
      | "x25519" => (X25519.x25519 (f 1) (f 2), f 3)
      | "public" => (X25519.publicKey (f 1), f 2)
      -- Signatures and chains: the answer is yes or no, and OpenSSL's is the last field.
      | "rsa1" => (verdict (Rsa.verifyPkcs1 ⟨natOf (f 1), natOf (f 2), (f 1).size⟩ (f 3) (f 4)), fields.getD 5 .empty)
      | "rsapss" => (verdict (Rsa.verifyPss ⟨natOf (f 1), natOf (f 2), (f 1).size⟩ (f 3) (f 4)), fields.getD 5 .empty)
      | "ecdsa" =>
        (verdict (Ecdsa.verify (if fields.getD 1 .empty == "p256".toUTF8 then Ecdsa.p256 else Ecdsa.p384) (natOf (f 2)) (natOf (f 3)) (f 4)
          (natOf (f 5)) (natOf (f 6))), fields.getD 7 .empty)
      | "chain" =>
        let anchors := match X509.Anchor.of (f 3) with | some a => #[a] | none => #[]
        let chain := (cut (fields.getD 4 .empty) 0x2c).map unhexBytes
        (verdict (X509.validate anchors chain (f 1) (n 2)).isOk, fields.getD 5 .empty)
      | _ => (ByteArray.empty, ByteArray.mk #[1])
    counts := counts.insert kind (counts.getD kind 0 + 1)
    if got != want then
      failures := failures + 1
      if failures < 12 then say s!"{kind}: {ascii (line.extract 0 150)}…\n  got {hex (got.extract 0 75)}"
  for (kind, count) in counts.toList do
    if kind == "handshake" then say s!"handshake: {count} conversations with a server that behaves or misbehaves as told, each twice"
    else say s!"{kind}: {count} cases against OpenSSL"
  -- The standards' own examples.
  let abc := "abc".toUTF8
  let printed : List (String × ByteArray × String) := [
    ("SHA-256 of abc", Sha256.hash abc, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("SHA-256 of nothing", Sha256.hash ByteArray.empty, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("SHA-384 of abc", Sha512.hash384 abc,
      "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"),
    ("SHA-512 of abc", Sha512.hash512 abc,
      "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"),
    ("X25519, RFC 7748 5.2", X25519.x25519 (unhex "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
        (unhex "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"),
      "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")]
  for (what, got, want) in printed do
    if hex got != want then
      failures := failures + 1
      say s!"{what}: {hex got}"
  -- RFC 7748's iteration: the answer becomes the key and the key the point, a thousand times.
  let mut k := (ByteArray.mk (Array.replicate 32 0)).set! 0 9
  let mut u := k
  for i in [0:1000] do
    let next := X25519.x25519 k u
    u := k
    k := next
    if i == 0 && hex k != "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079" then
      failures := failures + 1
      say s!"X25519 iterated once: {hex k}"
  if hex k != "684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51" then
    failures := failures + 1
    say s!"X25519 iterated a thousand times: {hex k}"
  -- Two sides, each with the other's public key, arrive at the same secret.
  let a := Sha256.hash "one side".toUTF8
  let b := Sha256.hash "the other".toUTF8
  if X25519.x25519 a (X25519.publicKey b) != X25519.x25519 b (X25519.publicKey a) then
    failures := failures + 1
    say "X25519: the two sides do not agree"
  -- A sealed message opens only as it was sealed: one bit changed anywhere and it does not.
  let key := Sha256.hash "a key".toUTF8
  let nonce := (Sha256.hash "a nonce".toUTF8).extract 0 12
  let aad := "beside".toUTF8
  let plain := "the message that was sealed, longer than one block of the cipher's stream by a good way".toUTF8
  let sealed := Aead.encrypt key nonce aad plain
  let mut refused := 0
  let mut tried := 0
  if Aead.decrypt? key nonce aad sealed != some plain then
    failures := failures + 1
    say "a sealed message did not open"
  for i in [0:sealed.size * 8] do
    tried := tried + 1
    let changed := sealed.set! (i / 8) (sealed.get! (i / 8) ^^^ (1 <<< (i % 8).toUInt8))
    if (Aead.decrypt? key nonce aad changed).isNone then refused := refused + 1
  for (k', n', a') in [(key.set! 3 (key.get! 3 ^^^ 1), nonce, aad), (key, nonce.set! 0 (nonce.get! 0 ^^^ 0x80), aad),
      (key, nonce, aad.push 0), (key, nonce, ByteArray.empty)] do
    tried := tried + 1
    if (Aead.decrypt? k' n' a' sealed).isNone then refused := refused + 1
  if (Aead.decrypt? key nonce aad (sealed.extract 0 15)).isSome then failures := failures + 1
  if refused != tried then
    failures := failures + 1
    say s!"a sealed message with something changed opened {tried - refused} times of {tried}"
  say s!"the standards' examples: {printed.length + 2}; a sealed message changed in {tried} ways, refused {refused} times"
  if failures == 0 then say "tls-test: all checks passed" else say s!"tls-test: {failures} FAILED"
  return if failures == 0 then 0 else 1
