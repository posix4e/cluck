import Evm.Bid
import JauneConsensus.Crypto.BLSSignature
import JauneConsensus.Signing

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

- The hashing of a bid (`Evm/Bid.lean`) against `JauneConsensus`'s own merkleization, domain and signing
  root; against a registration that a validator signed for a relay on mainnet, under the same builder
  domain, which has to verify; and a bid made and signed for a block built from a fixture, which has to
  verify under the builder's key.

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

def bytesOfHex (hex : String) : ByteArray :=
  let digits := hex.toList.filterMap fun c =>
    if c.isDigit then some (c.toNat - '0'.toNat) else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none
  let rec pairs : List Nat → List UInt8
    | a :: b :: rest => (a * 16 + b).toUInt8 :: pairs rest
    | _ => []
  (pairs digits).toByteArray

def wordOf (bytes : ByteArray) : Jaune.U256 := Bytes.toU256 bytes.toList

/-- A registration a validator signed for a relay (boost-relay.flashbots.net's public list, 2026-11-21,
for slot 15700576): fee recipient, gas limit, time, public key, and the signature over them under the
builder's domain for mainnet. -/
def registration : ByteArray × Nat × Nat × ByteArray × ByteArray :=
  (bytesOfHex "cAe2b829451ba6692418ec79faa762a6B5d93388", 45000000, 1756754519,
   bytesOfHex "897a4c268a7480d6b7ea38888390d5bd6f0644ea76a974c8206e565460cd920872d791874b532051d0474dcc933f802a",
   bytesOfHex "932b0e816a6ff5f0647dcc6cf9b8ea3927865a5bbd1f11908dbc633434576e67ecd9d99c57437fd6d471ba8f9b32a68514a902c4bf9f56d7fbd8405c127025262c34ff9f8e5d24d5bd72efd4d82631feeb93d5caa77e22e6ec89f1752c1d556a")

def bidChecks : IO (Nat × Nat) := do
  let mut failures := 0
  let mut checks := 0
  let expect (what : String) (ok : Bool) (f c : Nat) : IO (Nat × Nat) := do
    if !ok then IO.println s!"FAILED: {what}"
    pure (f + (if ok then 0 else 1), c + 1)
  -- The domain and the signing root against JauneConsensus's.
  let mainnet := Evm.Bid.domain (Evm.Bid.zeros 4)
  match versionOf [0, 0, 0, 0] with
  | .ok version =>
    let theirs := computeDomain #v[0, 0, 0, 1] version 0
    (failures, checks) ← expect "the builder's domain for mainnet is not JauneConsensus's" (wordOf mainnet == theirs) failures checks
    let object := Evm.Bid.sha "an object".toUTF8
    (failures, checks) ← expect "the signing root is not JauneConsensus's"
      (wordOf (Evm.Bid.signingRoot object mainnet) == computeSigningRootOfRoot (wordOf object) theirs) failures checks
  | .error _ => (failures, checks) ← expect "no version" false failures checks
  -- A bid's root against JauneConsensus's merkleization of the same nine leaves.
  let key := bytesOfHex "897a4c268a7480d6b7ea38888390d5bd6f0644ea76a974c8206e565460cd920872d791874b532051d0474dcc933f802a"
  let bid : Evm.Bid.Bid :=
    { slot := 15700576, parentHash := Evm.Bid.sha "parent".toUTF8, blockHash := Evm.Bid.sha "block".toUTF8,
      builderKey := key, proposerKey := key.extract 1 48 ++ key.extract 0 1,
      feeRecipient := bytesOfHex "cAe2b829451ba6692418ec79faa762a6B5d93388", gasLimit := 60000000,
      gasUsed := 12345678, value := 2 ^ 70 + 5 }
  let leaves : List Jaune.U256 := [
    wordOf (Evm.Bid.leaf (Evm.Bid.little 8 bid.slot)), wordOf bid.parentHash, wordOf bid.blockHash,
    wordOf (Evm.Bid.keyRoot bid.builderKey), wordOf (Evm.Bid.keyRoot bid.proposerKey),
    wordOf (Evm.Bid.leaf bid.feeRecipient), wordOf (Evm.Bid.leaf (Evm.Bid.little 8 bid.gasLimit)),
    wordOf (Evm.Bid.leaf (Evm.Bid.little 8 bid.gasUsed)), wordOf (Evm.Bid.little 32 bid.value)]
  (failures, checks) ← expect "a bid's root is not JauneConsensus's merkleization of its leaves"
    ((JauneConsensus.merkleize leaves).toOption == some (wordOf bid.root)) failures checks
  (failures, checks) ← expect "a key's root is not JauneConsensus's merkleization of its two leaves"
    ((JauneConsensus.merkleize [wordOf (key.extract 0 32), wordOf (Evm.Bid.leaf (key.extract 32 48))]).toOption ==
      some (wordOf (Evm.Bid.keyRoot key))) failures checks
  -- A registration signed on mainnet under the same domain verifies.
  let (feeRecipient, gasLimit, time, validator, signature) := registration
  let root := Evm.Bid.merkle #[Evm.Bid.leaf feeRecipient, Evm.Bid.leaf (Evm.Bid.little 8 gasLimit),
    Evm.Bid.leaf (Evm.Bid.little 8 time), Evm.Bid.keyRoot validator]
  let message := (Evm.Bid.signingRoot root mainnet).toList
  (failures, checks) ← expect "a validator's registration from mainnet does not verify under the builder's domain"
    (JauneConsensus.verify validator.toList message signature.toList) failures checks
  (failures, checks) ← expect "the registration verifies under another domain too"
    (!JauneConsensus.verify validator.toList
      (Evm.Bid.signingRoot root (Evm.Bid.domain (bytesOfHex "00000001"))).toList signature.toList) failures checks
  -- A bid for a block built from a fixture, made and signed, verifies under the builder's key.
  let some builder := Evm.Bid.testKey
    | expect "no key from the test's bytes" false failures checks
  (failures, checks) ← expect "the request for the key is not answered with it"
    (Evm.Bid.serve builder Evm.Bid.keyMagic == builder.publicKey && builder.publicKey.size == 48) failures checks
  let request ← IO.FS.readBinFile "fixtures/build/DelegateCallSpam-1.req"
  let proposer := key
  let asked := Evm.Bid.magic ++ Evm.Service.be 8 15700576 ++ proposer ++ Evm.Bid.zeros 4 ++ Evm.Service.be 4 0 ++ request
  let reply := Evm.Bid.serve builder asked
  let plain := Evm.Build.serve request
  (failures, checks) ← expect "the bid's reply does not begin with the reply to the request to build"
    (reply.size == plain.size + 48 + 96 && reply.extract 0 plain.size == plain) failures checks
  match (Evm.Build.request request).run 0 with
  | some (parsed, _) =>
    match (Evm.Build.run parsed).built with
    | some built =>
      let made : Evm.Bid.Bid :=
        { slot := 15700576, parentHash := Evm.Trie.wordBytes built.header.parentHash,
          blockHash := Evm.Trie.wordBytes built.hash, builderKey := builder.publicKey, proposerKey := proposer,
          feeRecipient := built.header.coinbase.toBytes.toByteArray, gasLimit := built.header.gasLimit,
          gasUsed := built.header.gasUsed, value := built.value }
      let signed := (Evm.Bid.signingRoot made.root mainnet).toList
      let signature := reply.extract (plain.size + 48) reply.size
      (failures, checks) ← expect "the bid's signature does not verify under the builder's key"
        (reply.extract plain.size (plain.size + 48) == builder.publicKey &&
          JauneConsensus.verify builder.publicKey.toList signed signature.toList) failures checks
      let other := (Evm.Bid.signingRoot { made with value := made.value + 1 }.root mainnet).toList
      (failures, checks) ← expect "the signature verifies for a bid of another value"
        (!JauneConsensus.verify builder.publicKey.toList other signature.toList) failures checks
    | none => (failures, checks) ← expect "nothing built from the fixture" false failures checks
  | none => (failures, checks) ← expect "the fixture is not a request to build" false failures checks
  -- A bid asked for with time allowed, when the time runs out before the first transaction: still a whole
  -- block and a signed bid, with nothing in it; and the time allowed is read from where it is written.
  let hurried := Evm.Bid.magic ++ Evm.Service.be 8 15700576 ++ proposer ++ Evm.Bid.zeros 4 ++ Evm.Service.be 4 1500 ++ request
  let empty := Id.run (Evm.Bid.serveWith (pure true) builder hurried)
  (failures, checks) ← expect "a bid cut short before its first transaction is not a signed, empty block"
    (Evm.Bid.allowed hurried == 1500 && Evm.Bid.allowed asked == 0 && empty.size > 109 + 144 && empty[0]! == 0 &&
      empty.extract 97 109 == Evm.Service.be 12 0 && Evm.Bid.serve builder hurried == reply) failures checks
  -- A bid for a request whose block may go on from the one before: the first is built from nothing
  -- and kept; the second goes on from it and, with nothing new proposed, is the same block and the same
  -- bid; and one the machine adds a transaction of its own to is built from nothing, and what is kept
  -- to go on from is as it was.
  match ((Evm.Build.request request).run 0).bind fun (parsed, _) =>
      Evm.Build.Request.encode { parsed with engine := true, seen := some false, goesOn := true } with
  | some goingOn =>
    let bidFor := Evm.Bid.magic ++ Evm.Service.be 8 15700576 ++ proposer ++ Evm.Bid.zeros 4 ++ Evm.Service.be 4 0 ++ goingOn
    let first := Id.run (Evm.Bid.buildWith (pure false) builder bidFor (other := Evm.Build.noOther))
    let second := Id.run (Evm.Bid.buildWith (pure false) builder bidFor (other := Evm.Build.noOther) (kept := first.kept))
    let added := Id.run (Evm.Bid.buildWith (pure false) builder bidFor (fun _ => { wires := #[ByteArray.mk #[2, 0]] })
      Evm.Build.noOther second.kept)
    let taken (outcome : Evm.Bid.Outcome) : Option (Array Fast.Word) := outcome.kept.before.map (·.taken)
    (failures, checks) ← expect "a bid that may go on from the block before did not, or is another bid, or one with a \
      transaction added went on or changed what is kept"
      (first.reply.size > 109 + 144 && first.reply[0]! == 0 && first.wentOn.isNone && (taken first).isSome
        && second.wentOn == (taken first).map (·.size) && second.reply == first.reply && taken second == taken first
        && added.tried && added.wentOn.isNone && added.reply[0]! == 0 && taken added == taken first) failures checks
  | none => (failures, checks) ← expect "the fixture is not a request to build, or has no encoding" false failures checks
  -- A key is usable exactly when it is in range.
  let unusable := [Evm.Bid.zeros 32, Evm.Bid.little 32 blsCurveOrder, Evm.Bid.little 32 (blsCurveOrder + 1)]
  (failures, checks) ← expect "a key that is zero or not below the order was taken"
    (unusable.all fun bytes => (Evm.Bid.keyOf bytes).isNone) failures checks
  (failures, checks) ← expect "the largest key, or the smallest, was not taken"
    ((Evm.Bid.keyOf (Evm.Bid.little 32 (blsCurveOrder - 1))).isSome && (Evm.Bid.keyOf (Evm.Bid.little 32 1)).isSome)
    failures checks
  IO.println s!"bids: {checks} checks"
  pure (failures, checks)

def main : IO UInt32 := do
  let mut failures := 0
  let mut checks := 0
  let (bidFailures, bidCount) ← bidChecks
  failures := failures + bidFailures
  checks := checks + bidCount
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
  -- The doubling by its own formula, against the addition of a point to itself and against Jaune's.
  for i in multiples do
    let p1 := blsG1Generator.mulBy i
    let lift1 (p : Bls12G1) : Point Fp :=
      if p = ⟨0, 0⟩ then Point.infinity else Point.ofAffine (Fp.ofPublic p.x.val) (Fp.ofPublic p.y.val)
    let p2 := blsG2Generator.mulBy i
    checks := checks + 1
    if toPublicG1 (Point.double b3G1 (lift1 p1)) != p1 + p1
        || toPublicG1 (Point.double b3G1 (Point.double b3G1 (lift1 p1))) != (p1 + p1) + (p1 + p1)
        || toPublicG2 (Point.double b3G2 (ofPublicG2 p2)) != p2 + p2
        || toPublicG2 (Point.double b3G2 (Point.double b3G2 (ofPublicG2 p2))) != (p2 + p2) + (p2 + p2) then
      failures := failures + 1; IO.println s!"FAILED: twice {i}G, or twice that"
  -- Four bits of a key, and whether they are a given number, for every number they can be.
  for word in [0, 1, 0xfedcba9876543210, 0x0123456789abcdef, 0xffffffffffffffff] do
    for w in [0, 1, 7, 15, 16, 31, 32, 47, 48, 62, 63] do
      let k : Scalar := ⟨word.toUInt64, (word + 1).toUInt64, (word * 3).toUInt64, (word * 5).toUInt64⟩
      let whole := k.w0.toNat + k.w1.toNat * 2 ^ 64 + k.w2.toNat * 2 ^ 128 + k.w3.toNat * 2 ^ 192
      let four := (whole >>> (4 * w)) % 16
      checks := checks + 1
      if (k.four w).toNat != four || !(List.range 16).all (fun j => Scalar.is (k.four w) j.toUInt64 == (j == four)) then
        failures := failures + 1; IO.println s!"FAILED: four bits {w} of a key"
  IO.println s!"points: {checks - before} sums, doublings and fours of a key"
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
  -- A message made a point by this project's arithmetic (`Evm/Sign/Hash.lean`) is the point
  -- `JauneConsensus` makes of it: messages of every length to 70 bytes, and some long ones.
  let before := checks
  for i in [0 : 90] do
    let length := if i < 71 then i else i * 37
    let message : Bytes := (List.range length).map fun j => (scramble (i * 977 + j) 8).toUInt8
    checks := checks + 1
    match Evm.Sign.Hash.toPoint message messageTag, hashToG2 message messageTag with
    | .ok point, .ok wanted =>
      if toPublicG2 point != wanted then
        failures := failures + 1; IO.println s!"FAILED: the point of a message of {length} bytes"
    | _, _ => failures := failures + 1; IO.println s!"FAILED: no point for a message of {length} bytes"
  IO.println s!"points: {checks - before} messages hashed to the point Jaune's hashing gives"
  -- How long the key's part of a signature takes, apart from hashing the message to a point.
  if let .ok q := hashToG2 [1, 2, 3] messageTag then
    let k := scalarOf (scramble 999 254 + 1)
    let started ← IO.monoMsNow
    let mut last := q
    for _ in [0 : 5] do last := applyG2 k last
    let applied := (← IO.monoMsNow) - started
    let started ← IO.monoMsNow
    let theirs ← IO.lazyPure fun _ => (hashToG2 [4, 5, 6] messageTag).toOption.map g2Compress
    let hashed := (← IO.monoMsNow) - started
    let started ← IO.monoMsNow
    let mut ours : Option Bytes := none
    for i in [0 : 10] do
      ours ← IO.lazyPure fun _ => (Evm.Sign.Hash.toPoint [4, 5, 6 + (i / 10).toUInt8] messageTag).toOption.map fun p => g2Compress (toPublicG2 p)
    let here := (← IO.monoMsNow) - started
    IO.println s!"time: the key times a point of G2, {applied / 5} ms; hashing a message to a point, {here / 10}.{here % 10} ms here \
      and {hashed} ms by Jaune's{if ours == theirs then "" else ", AND NOT THE SAME POINT"} (last byte {(g2Compress last).getLastD 0})"
  if failures == 0 then IO.println s!"bls-test: all {checks} checks passed"
  else IO.println s!"bls-test: {failures} of {checks} FAILED"
  return if failures == 0 then 0 else 1
