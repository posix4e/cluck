import Evm

/-! Pure tests: `Evm.powMod` against Lean's own `Nat.powMod`, and the request format against itself and
against input that is not a request. Run on Lean's own runtime, where `Nat.powMod` is the reference. -/
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
  if failures == 0 then IO.println "evm-test: all checks passed" else IO.println s!"evm-test: {failures} FAILED"
  return if failures == 0 then 0 else 1
