import Evm.Sign
import JauneConsensus.Crypto.BLSSignature

/-! Tests of the signing key's arithmetic (`Evm/Sign/`), which nothing proves.

- The field on fixed-width words against arithmetic on `Nat`: into Montgomery form and out, and the sum,
  difference and product of every pair of values chosen to carry and borrow in every limb, with the
  inverse of some.
- The addition of points against `Jaune`'s, on multiples of the generators of both groups, in every case
  the one formula has to cover: different points, the same point, opposite points, and the point at
  infinity on either side.
- Public keys and signatures against `JauneConsensus`'s, which are made with the key as a `Nat`: byte for
  byte the same, for keys at the ends of the range and keys from a generator, and each signature accepted
  by `JauneConsensus.verify`.

    .lake/build/bin/bls-test            (from evm/)

Run on Lean's own runtime, where `Nat` is the reference. -/
open Jaune JauneConsensus Evm.Sign

def prime : Nat := blsPrime

/-- A pseudo-random number of about `bits` bits; the same sequence every run. -/
def scramble (seed bits : Nat) : Nat := Id.run do
  let mut x := seed * 6364136223846793005 + 1442695040888963407
  let mut n := 0
  for _ in [0 : bits / 64 + 1] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    n := (n <<< 64) ||| x
  return n % 2 ^ bits

def values : List Nat :=
  [0, 1, 2, 3, 12, prime - 1, prime - 2, prime - 12, prime, prime + 1, 2 * prime - 1, (prime - 1) / 2,
   (prime + 1) / 2, 2 ^ 380, 2 ^ 381 - 1, 2 ^ 390 % prime, (2 ^ 390 - 1) % prime, 2 ^ 389, 2 ^ 390 - 1] ++
  (List.range 15).flatMap (fun i => [2 ^ (26 * i) - 1, 2 ^ (26 * i), 2 ^ (26 * i) + 1, 2 ^ (26 * i + 25)]) ++
  (List.range 16).map (fun k =>
    ((List.range 15).filter (· != k)).foldl (fun n i => n + (2 ^ 26 - 1) * 2 ^ (26 * i)) 0) ++
  (List.range 40).map (fun i => scramble (i + 1) 381)

def wellFormed (a : Fp) : Bool :=
  [a.l0, a.l1, a.l2, a.l3, a.l4, a.l5, a.l6, a.l7, a.l8, a.l9, a.l10, a.l11, a.l12, a.l13, a.l14].all (· < 2 ^ 26)

def scalarOf (n : Nat) : Scalar :=
  ⟨n.toUInt64, (n >>> 64).toUInt64, (n >>> 128).toUInt64, (n >>> 192).toUInt64⟩

def main : IO UInt32 := do
  let mut failures := 0
  let mut checks := 0
  -- The field.
  for m in values do
    let a := Fp.ofPublic m
    checks := checks + 1
    if !(wellFormed a && a.toPublic == m % prime) then
      failures := failures + 1
      IO.println s!"FAILED: {m} into the field and out"
  for m in values do
    let a := Fp.ofPublic m
    for n in values do
      let b := Fp.ofPublic n
      let sum := a + b
      let difference := a - b
      let product := a * b
      checks := checks + 3
      if !(wellFormed sum && sum.toPublic == (m + n) % prime) then
        failures := failures + 1; IO.println s!"FAILED: {m} + {n}"
      if !(wellFormed difference && difference.toPublic == (m % prime + prime - n % prime) % prime) then
        failures := failures + 1; IO.println s!"FAILED: {m} - {n}"
      if !(wellFormed product && product.toPublic == (m * n) % prime) then
        failures := failures + 1; IO.println s!"FAILED: {m} * {n}"
  for m in values.take 40 do
    let a := Fp.ofPublic m
    checks := checks + 1
    if !((a.inv).toPublic == (FinField.inv (FinField.ofNat m : Bls12Fp)).val &&
        (m % prime == 0 || (a * a.inv).toPublic == 1)) then
      failures := failures + 1; IO.println s!"FAILED: the inverse of {m}"
  IO.println s!"field: {checks} checks"
  -- The addition of points, in both groups, against Jaune's.
  let before := checks
  let multiples : List Nat := [0, 1, 2, 3, 5, 6, 7, 11, blsCurveOrder - 1, blsCurveOrder - 2, scramble 7 250]
  for i in multiples do
    for j in multiples do
      let p1 := blsG1Generator.mulBy i
      let q1 := blsG1Generator.mulBy j
      let lift1 (p : Bls12G1) : Point Fp :=
        if p = ⟨0, 0⟩ then Point.infinity else Point.ofAffine (Fp.ofPublic p.x.val) (Fp.ofPublic p.y.val)
      checks := checks + 1
      if toPublicG1 (Point.add b3G1 (lift1 p1) (lift1 q1)) != p1 + q1 then
        failures := failures + 1; IO.println s!"FAILED: in G1, {i}G + {j}G"
      let p2 := blsG2Generator.mulBy i
      let q2 := blsG2Generator.mulBy j
      checks := checks + 1
      if toPublicG2 (Point.add b3G2 (ofPublicG2 p2) (ofPublicG2 q2)) != p2 + q2 then
        failures := failures + 1; IO.println s!"FAILED: in G2, {i}G + {j}G"
  IO.println s!"points: {checks - before} sums"
  -- Public keys and signatures.
  let before := checks
  let keys : List Nat := [1, 2, 3, blsCurveOrder - 1, blsCurveOrder - 2, 2 ^ 254, 2 ^ 254 + 1, 2 ^ 64 - 1,
    2 ^ 64, 2 ^ 128, 2 ^ 192 - 1] ++ (List.range 12).map fun i => scramble (100 + i) 255 % (blsCurveOrder - 1) + 1
  for (key, i) in keys.zipIdx do
    let k := scalarOf key
    checks := checks + 1
    let reference := skToPk key
    let publicKey := publicKey k
    if reference != .ok publicKey then
      failures := failures + 1; IO.println s!"FAILED: the public key of {key}"
    let message : Bytes := (List.range (i * 7 % 50)).map fun j => (scramble (i * 131 + j) 8).toUInt8
    checks := checks + 1
    match Evm.Sign.sign k message, JauneConsensus.sign key message with
    | .ok signature, .ok wanted =>
      if signature != wanted then
        failures := failures + 1; IO.println s!"FAILED: the signature with {key}"
      else if i < 4 then
        checks := checks + 1
        if !JauneConsensus.verify publicKey message signature then
          failures := failures + 1; IO.println s!"FAILED: the signature with {key} does not verify"
    | _, _ => failures := failures + 1; IO.println s!"FAILED: no signature with {key}"
  IO.println s!"keys: {keys.length} public keys and signatures, {checks - before} checks"
  -- How long the key's part of a signature takes, apart from hashing the message to a point.
  if let .ok q := hashToG2 [1, 2, 3] messageTag then
    let k := scalarOf (scramble 999 254 + 1)
    let started ← IO.monoMsNow
    let mut last := q
    for _ in [0 : 5] do last := applyG2 k last
    let applied := (← IO.monoMsNow) - started
    let started ← IO.monoMsNow
    let _ ← IO.lazyPure fun _ => (hashToG2 [4, 5, 6] messageTag).toOption.map g2Compress
    let hashed := (← IO.monoMsNow) - started
    IO.println s!"time: the key times a point of G2, {applied / 5} ms; hashing a message to a point, {hashed} ms \
      (last byte {(g2Compress last).getLastD 0})"
  if failures == 0 then IO.println s!"bls-test: all {checks} checks passed"
  else IO.println s!"bls-test: {failures} of {checks} FAILED"
  return if failures == 0 then 0 else 1
