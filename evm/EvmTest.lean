import Evm

/-! Pure tests: `Evm.powMod` against Lean's own `Nat.powMod`, and the request format against itself and
against input that is not a request, and the attested answer's hash and framing. Run on Lean's own runtime, where `Nat.powMod` is the reference. -/
open Jaune Evm.Service

/-- A pseudo-random number of about `bits` bits; the same sequence every run. -/
def scramble (seed bits : Nat) : Nat := Id.run do
  let mut x := seed * 6364136223846793005 + 1442695040888963407
  let mut n := 0
  for _ in [0 : bits / 64 + 1] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    n := (n <<< 64) ||| x
  return n % 2 ^ bits

def powModCases : List (Nat × Nat × Nat) :=
  [(0, 0, 0), (0, 0, 1), (0, 0, 7), (5, 0, 0), (0, 5, 0), (3, 4, 0), (3, 4, 1), (3, 4, 5), (2, 10, 1000),
   (7, 1, 13), (2 ^ 200, 3, 0), (2 ^ 64, 2 ^ 64, 2 ^ 64 + 13)] ++
  (List.range 200).map fun i =>
    (scramble (3 * i) (8 * (i % 40) + 1), scramble (3 * i + 1) (4 * (i % 50) + 1),
     scramble (3 * i + 2) (8 * (i % 40) + 1))

def sample : Request :=
  { fork := .prague, chainId := 1,
    accounts := [(⟨7, 9⟩, ⟨3, 1000, Storage.ofList [(1, 2), (5, 6)], ⟨#[0x60, 0x00]⟩⟩),
                 (⟨8, 1⟩, ⟨0, 0, Storage.ofList [], .empty⟩)],
    genesis := [0xc0], blocks := [[1, 2, 3], []] }

def hex (bytes : ByteArray) : String :=
  bytes.foldl (fun out b => out ++ String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)]) ""

def sha256Cases : List (String × String) :=
  [("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
   ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
   ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")]

def main : IO UInt32 := do
  let mut failures := 0
  for (b, e, m) in powModCases do
    if Evm.powMod b e m != Nat.powMod b e m then
      failures := failures + 1
      IO.println s!"powMod {b} {e} {m}: {Evm.powMod b e m}, Nat.powMod gives {Nat.powMod b e m}"
  IO.println s!"powMod: {powModCases.length} cases against Nat.powMod"
  let some bytes := sample.encode | throw (IO.userError "the sample request has no encoding")
  match (request bytes).run 0 with
  | some (decoded, pos) =>
    if pos != bytes.size || decoded.encode != some bytes then
      failures := failures + 1
      IO.println "a request read back does not write back to the same bytes"
  | none =>
    failures := failures + 1
    IO.println "an encoded request does not read back"
  -- Every way of cutting the sample short, and one byte too many, is malformed and says so.
  let malformed := (⟨5, 0, 0, 0⟩ : Response).encode
  for n in [0 : bytes.size] do
    if serve (bytes.extract 0 n) != malformed then
      failures := failures + 1
      IO.println s!"the first {n} bytes of a request were not refused as malformed"
  if serve (bytes.push 0) != malformed then
    failures := failures + 1
    IO.println "a request with a byte after its end was not refused"
  -- The sample's genesis is an empty list, which is no block: status 1, and nothing else claimed.
  if serve bytes != (⟨1, 0, 0, 0⟩ : Response).encode then
    failures := failures + 1
    IO.println "a request whose genesis is not a block was not answered with status 1"
  IO.println s!"request format: {bytes.size + 3} cases"
  -- SHA-256 as the attested answer uses it, against the standard's own examples (FIPS 180-4, one block,
  -- none, and two), and the shape of an attested frame.
  for (text, digest) in sha256Cases do
    if hex (Evm.Attest.sha256 text.toUTF8) != digest then
      failures := failures + 1
      IO.println s!"SHA-256 of {text.quote} is {hex (Evm.Attest.sha256 text.toUTF8)}"
  let challenge : ByteArray := ⟨(List.range 32).map (·.toUInt8) |>.toArray⟩
  let attested := Evm.Attest.tag ++ challenge ++ bytes
  if (Evm.Attest.asked? attested).map Evm.Attest.request != some bytes then
    failures := failures + 1
    IO.println "an attested frame does not give back the request inside it"
  if (Evm.Attest.asked? bytes).isSome || (Evm.Attest.asked? (Evm.Attest.tag ++ challenge.extract 0 31)).isSome then
    failures := failures + 1
    IO.println "a frame that is not an attested one was taken for one"
  let data := Evm.Attest.reportData (challenge ++ bytes) malformed
  if data != Evm.Attest.sha256 (challenge ++ bytes) ++ Evm.Attest.sha256 malformed || data.size != 64 then
    failures := failures + 1
    IO.println "REPORTDATA is not the two hashes, 64 bytes"
  IO.println s!"attested answer: {sha256Cases.length + 3} cases"
  -- This package's Jaune compiles `jumpable` as a forward pass that nothing proves equal to it. `jumpdestOk`
  -- is proved equal to it, so the two must agree at every position of code made of the bytes that matter:
  -- jump destinations, pushes of every width, and whatever else.
  let mut jumps := 0
  for seed in [0 : 300] do
    let length := seed % 97 + 1
    let code : ByteArray := ⟨(List.range length).map (fun i =>
      let x := scramble (seed * 131 + i) 16
      if x % 5 == 0 then (0x5b : UInt8) else if x % 5 < 3 then (0x5f + (x / 5) % 34).toUInt8 else x.toUInt8) |>.toArray⟩
    for k in [0 : length + 2] do
      jumps := jumps + 1
      if jumpable code k != jumpdestOk code k then
        failures := failures + 1
        IO.println s!"jumpable and jumpdestOk differ at {k} of {hex code}"
  IO.println s!"jump destinations: {jumps} positions in 300 codes"
  if failures == 0 then IO.println "evm-test: all checks passed" else IO.println s!"evm-test: {failures} FAILED"
  return if failures == 0 then 0 else 1
