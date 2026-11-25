import Evm.Bridge

/-! The engine's bn254 against `Nat` and against Jaune's.

The field's arithmetic is compared with the same arithmetic on `Nat` modulo the prime. The three
precompiled contracts are compared with Jaune's through the two hosts of `Evm/Bridge.lean`: for the same
input and gas they must succeed or fail alike, leave the same gas and return the same bytes. The inputs:
points made by multiplying the generators, the point at infinity, points that are not on the curve, numbers
that are not under the prime, inputs too short and too long, and for the pairing sets of pairs that are
bilinear by construction, sets that are not, and pairs with a point at infinity. A point on the twist that
is not in the pairing's subgroup is not among them: making one needs a square root this test does not
have. Runs on Lean's runtime, Jaune being the reference. -/
open Fast Fast.Bn254

def p : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
def r : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

def next (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

def bytes32 (n : Nat) : ByteArray := (Word.ofNat n).bytes

def natOf (a : Fp) : Nat :=
  let plain := Fp.fromMontgomery a
  plain.a0.toNat + plain.a1.toNat <<< 64 + plain.a2.toNat <<< 128 + plain.a3.toNat <<< 192

def fpOf (n : Nat) : Fp := (Fp.read (bytes32 (n % p)) 0).getD Fp.zero

/-- A number of 256 bits from the generator, and the generator moved on. -/
def draw (s : UInt64) : Nat × UInt64 :=
  let a := next s
  let b := next a
  let c := next b
  let d := next c
  (a.toNat + b.toNat <<< 64 + c.toNat <<< 128 + d.toNat <<< 192, d)

def g1 : G1 := ⟨Fp.one, fpOf 2, Fp.one⟩
def g2 : G2 :=
  ⟨Fp2.of (fpOf 11559732032986387107991004021392285783925812861821192530917403151452391805634)
          (fpOf 10857046999023057135944570762232829481370756359578518086990519993285655852781),
   Fp2.of (fpOf 4082367875863433681332203403145435568316851327593401208105741076214120093531)
          (fpOf 8495653923123431417604973247489272438418190587263600148770280649306958101930),
   Fp2.one, Fp2.one⟩

def scalar (n : Nat) : Fp := let w := Word.ofNat n; ⟨w.w0, w.w1, w.w2, w.w3⟩

def encode1 (pt : G1) : ByteArray := G1.write ByteArray.empty pt
def encode2 (pt : G2) : ByteArray :=
  if pt.z.isZero then ByteArray.mk (Array.replicate 128 0) else
  let zi := pt.z.inverse
  let zi2 := zi.square
  let x := pt.x.mul zi2
  let y := pt.y.mul (zi2.mul zi)
  Fp.write (Fp.write (Fp.write (Fp.write ByteArray.empty x.im) x.re) y.im) y.re

def hexOf (b : ByteArray) : String :=
  b.foldl (fun out x => out ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

def main : IO UInt32 := do
  let mut failures := 0
  let mut seed : UInt64 := 0x13198a2e03707344
  -- The field against Nat.
  let mut fieldCases := 0
  for i in [0:3000] do
    let (x, s1) := draw seed
    let (y, s2) := draw s1
    seed := s2
    let (x, y) := if i < 6 then ([0, 1, p - 1, p - 2, 2, p / 2][i]!, [p - 1, 1, p - 1, 0, p - 2, 3][i]!) else (x % p, y % p)
    let (a, b) := (fpOf x, fpOf y)
    fieldCases := fieldCases + 1
    if natOf (a.mul b) != x * y % p || natOf (a.add b) != (x + y) % p || natOf (a.sub b) != (x + p - y) % p ||
        natOf a.neg != (p - x) % p || natOf a != x then
      failures := failures + 1
      if failures < 10 then IO.println s!"field: {x} and {y}"
    if i < 60 && x != 0 && natOf (a.mul a.inverse) != 1 then
      failures := failures + 1
      IO.println s!"field: the inverse of {x}"
  IO.println s!"the field against Nat: {fieldCases} pairs"
  -- Points to make inputs of.
  let mut numbers : Array Nat := #[0, 1, 2, 3, r - 1, r, r + 1, 2 ^ 256 - 1, 2 ^ 255, p]
  for _ in [0:14] do
    let (n, s) := draw seed
    numbers := numbers.push n
    seed := s
  let points1 : Array ByteArray := numbers.map fun n => encode1 (g1.mul (scalar n))
  let bad1 : Array ByteArray := #[bytes32 1 ++ bytes32 3, bytes32 p ++ bytes32 2, bytes32 1 ++ bytes32 (p + 2),
    bytes32 0 ++ bytes32 1, bytes32 (2 ^ 256 - 1) ++ bytes32 (2 ^ 256 - 1)]
  let prague := Evm.Bridge.host .prague
  let jaune := Evm.Bridge.jauneHost .prague
  let compare (what : String) (address : UInt64) (input : ByteArray) (gas : UInt64) : IO Bool := do
    let mine := prague.precompile (Word.ofUInt64 address) input gas
    let theirs := jaune.precompile (Word.ofUInt64 address) input gas
    if mine.success != theirs.success || mine.gasLeft != theirs.gasLeft || mine.output != theirs.output then
      IO.println s!"{what}: input {hexOf input}\n  the engine: {mine.success} {mine.gasLeft.toNat} {hexOf mine.output}\n  Jaune:      {theirs.success} {theirs.gasLeft.toNat} {hexOf theirs.output}"
      return false
    return true
  -- Addition.
  let mut additions := 0
  for a in points1 ++ bad1 do
    for b in points1 ++ bad1.extract 0 2 do
      additions := additions + 1
      if !(← compare "addition" 6 (a ++ b) 1000) then failures := failures + 1
  for (input, gas) in [(points1[3]!, 1000), (points1[3]! ++ points1[4]!.extract 0 40, 1000), (ByteArray.empty, 1000),
      (points1[3]! ++ points1[4]! ++ bytes32 7, 1000), (points1[3]! ++ points1[4]!, 149), (points1[3]! ++ points1[4]!, 150)] do
    additions := additions + 1
    if !(← compare "addition" 6 input gas.toUInt64) then failures := failures + 1
  IO.println s!"addition against Jaune's: {additions} inputs"
  -- The contract that hands its input back, which the engine has of its own too.
  let mut copies := 0
  for size in [0, 1, 31, 32, 33, 64, 1000, 4097] do
    let input : ByteArray := ⟨(List.range size).map (fun i => (i * 7 + size).toUInt8) |>.toArray⟩
    let cost := 15 + 3 * ((size + 31) / 32)
    for gas in [0, cost - 1, cost, cost + 1, 100000] do
      copies := copies + 1
      if !(← compare "the input handed back" 4 input gas.toUInt64) then failures := failures + 1
  IO.println s!"the input handed back, against Jaune's: {copies} inputs"
  -- Multiplication.
  let mut multiplications := 0
  for a in points1.extract 0 12 ++ bad1 do
    for n in numbers do
      multiplications := multiplications + 1
      if !(← compare "multiplication" 7 (a ++ bytes32 n) 10000) then failures := failures + 1
  for (input, gas) in [(points1[3]!, 10000), (points1[3]! ++ (bytes32 5).extract 0 20, 10000), (ByteArray.empty, 10000),
      (points1[3]! ++ bytes32 5 ++ bytes32 9, 10000), (points1[3]! ++ bytes32 5, 5999)] do
    multiplications := multiplications + 1
    if !(← compare "multiplication" 7 input gas.toUInt64) then failures := failures + 1
  IO.println s!"multiplication against Jaune's: {multiplications} inputs"
  -- The pairing check.
  let pair (a b : Nat) : ByteArray := encode1 (g1.mul (scalar a)) ++ encode2 (g2.mul (scalar b))
  let mut checks := 0
  let mut held := 0
  let mut inputs : Array ByteArray := #[ByteArray.empty, pair 1 1, pair 0 5, pair 5 0, pair 0 0,
    pair 1 1 ++ pair (r - 1) 1, pair 2 3 ++ pair (r - 6) 1, pair 2 3 ++ pair (r - 5) 1, pair 2 3 ++ pair 6 (r - 1),
    pair 7 1 ++ pair 11 1 ++ pair (r - 18) 1, pair 7 1 ++ pair 11 1 ++ pair (r - 17) 1,
    pair 3 4 ++ pair 0 9 ++ pair (r - 12) 1 ++ pair 5 0, pair 1 1 ++ pair 1 1,
    (pair 1 1).extract 0 191, pair 1 1 ++ bytes32 0, bad1[0]! ++ encode2 g2, bad1[1]! ++ encode2 g2,
    encode1 g1 ++ ((encode2 g2).set! 127 7), encode1 g1 ++ bytes32 p ++ (encode2 g2).extract 32 128,
    encode1 g1 ++ (encode2 g2).extract 0 96 ++ bytes32 (2 ^ 256 - 1)]
  for _ in [0:6] do
    let (a, s1) := draw seed
    let (b, s2) := draw s1
    seed := s2
    let (a, b) := (a % r, b % r)
    inputs := inputs.push (pair a b ++ pair (r - a * b % r) 1)
    inputs := inputs.push (pair a b ++ pair (r - a) b)
    inputs := inputs.push (pair a b ++ pair b a)
  for input in inputs do
    checks := checks + 1
    let mine := prague.precompile (Word.ofUInt64 8) input 10000000
    if mine.success && mine.output.size == 32 && mine.output.get! 31 == 1 then held := held + 1
    if !(← compare "pairing" 8 input 10000000) then failures := failures + 1
  for (input, gas) in [(pair 1 1, 78999), (pair 1 1, 79000), (ByteArray.empty, 44999), (ByteArray.empty, 45000)] do
    checks := checks + 1
    if !(← compare "pairing" 8 input gas.toUInt64) then failures := failures + 1
  IO.println s!"the pairing check against Jaune's: {checks} inputs, {held} of them holding"
  if failures == 0 then IO.println "bn254-test: all checks passed" else IO.println s!"bn254-test: {failures} FAILED"
  return if failures == 0 then 0 else 1
