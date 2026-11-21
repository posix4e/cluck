import Tls
import Std.Data.HashMap

/-! `evm/Tls/` against the standards' examples and against OpenSSL.

    .lake/build/bin/tls-test Tls/vectors.txt        (from evm/)

The file of cases is made by `scripts/tls-vectors` from Python's hashlib and `cryptography` package. For
each case the same inputs are given to the Lean and the answers must be the same bytes. Beside the file:
the examples printed in FIPS 180-4 and RFC 7748, a sealed message that must not open once any one bit of
it, of its tag, of the data beside it or of its key is changed, and X25519's own check that two sides
arrive at the same secret. -/
open Tls

def unhex (s : String) : ByteArray :=
  if s == "-" then ByteArray.empty else
  let digit (c : Char) : UInt8 := (if c.isDigit then c.toNat - 48 else c.toNat - 87).toUInt8
  let rec go (cs : List Char) (out : ByteArray) : ByteArray :=
    match cs with
    | a :: b :: rest => go rest (out.push (digit a * 16 + digit b))
    | _ => out
  go s.toList ByteArray.empty

def hex (b : ByteArray) : String :=
  b.foldl (fun out x => out ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: tls-test VECTORS"; return 2
  let mut failures := 0
  let mut counts : Std.HashMap String Nat := {}
  for line in (← IO.FS.lines path) do
    let fields := line.splitOn " "
    let kind := fields.headD ""
    let f (i : Nat) : ByteArray := unhex (fields.getD i "-")
    let n (i : Nat) : Nat := (fields.getD i "0").toNat!
    let (got, want) : ByteArray × ByteArray :=
      match kind with
      | "sha256" => (Sha256.hash (f 1), f 2)
      | "sha384" => (Sha512.hash384 (f 1), f 2)
      | "sha512" => (Sha512.hash512 (f 1), f 2)
      | "hmac" => (hmac (f 1) (f 2), f 3)
      | "hkdf" => (Hkdf.expand (Hkdf.extract (if (f 1).size == 0 then ByteArray.mk (Array.replicate 32 0) else f 1) (f 2)) (f 3) (n 4), f 5)
      | "label" => (Hkdf.expandLabel (f 1) (String.fromUTF8! (f 2)) (f 3) (n 4), f 5)
      | "aead" =>
        -- Sealing gives the library's bytes, and they open to what was sealed.
        let sealed := Aead.encrypt (f 1) (f 2) (f 3) (f 4)
        (sealed ++ ((Aead.decrypt? (f 1) (f 2) (f 3) (f 5)).getD (ByteArray.mk #[0xee])), f 5 ++ f 4)
      | "poly1305" => (Poly1305.tag (f 1) (f 2), f 3)
      | "x25519" => (X25519.x25519 (f 1) (f 2), f 3)
      | "public" => (X25519.publicKey (f 1), f 2)
      | _ => (ByteArray.empty, ByteArray.mk #[1])
    counts := counts.insert kind (counts.getD kind 0 + 1)
    if got != want then
      failures := failures + 1
      if failures < 12 then IO.println s!"{kind}: {(line.take 150)}…\n  got {(hex got).take 150}"
  for (kind, count) in counts.toList do IO.println s!"{kind}: {count} cases against OpenSSL"
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
      IO.println s!"{what}: {hex got}"
  -- RFC 7748's iteration: the answer becomes the key and the key the point, a thousand times.
  let mut k := (ByteArray.mk (Array.replicate 32 0)).set! 0 9
  let mut u := k
  for i in [0:1000] do
    let next := X25519.x25519 k u
    u := k
    k := next
    if i == 0 && hex k != "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079" then
      failures := failures + 1
      IO.println s!"X25519 iterated once: {hex k}"
  if hex k != "684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51" then
    failures := failures + 1
    IO.println s!"X25519 iterated a thousand times: {hex k}"
  -- Two sides, each with the other's public key, arrive at the same secret.
  let a := Sha256.hash "one side".toUTF8
  let b := Sha256.hash "the other".toUTF8
  if X25519.x25519 a (X25519.publicKey b) != X25519.x25519 b (X25519.publicKey a) then
    failures := failures + 1
    IO.println "X25519: the two sides do not agree"
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
    IO.println "a sealed message did not open"
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
    IO.println s!"a sealed message with something changed opened {tried - refused} times of {tried}"
  IO.println s!"the standards' examples: {printed.length + 2}; a sealed message changed in {tried} ways, refused {refused} times"
  if failures == 0 then IO.println "tls-test: all checks passed" else IO.println s!"tls-test: {failures} FAILED"
  return if failures == 0 then 0 else 1
