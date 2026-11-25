import Evm
import Platform

/-! Times the precompiled contracts as a transaction reaches them (`Evm.Bridge.host`), on whichever runtime
this is linked against, with inputs chosen to cost the most work for the gas: what one call takes, what it
is charged, and so what a transaction of the most gas one may have (2^24, EIP-7825) could keep the builder
busy for with nothing but such calls. Runs as a process only. -/
open Jaune

@[extern "evm_clock_millis"] opaque clockMillis : IO UInt64
@[extern "evm_clock_seed"] opaque clockSeed : IO UInt64

def say (s : String) : IO Unit := Platform.write s.toUTF8

def be (n : Nat) (size : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity size
  for i in [0:size] do
    out := out.push ((n >>> (8 * (size - 1 - i))) % 256).toUInt8
  return out

def filled (size : Nat) (seed : UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity size
  let mut x := seed * 6364136223846793005 + 1442695040888963407
  for _ in [0:size] do
    x := x * 6364136223846793005 + 1442695040888963407
    out := out.push (x >>> 33).toUInt8
  return out

/-- `count` calls of one contract with one input: milliseconds for each, the gas each took, and from the
two the seconds a transaction of 2^24 gas spent on nothing else would take. -/
def one (label : String) (address : UInt64) (input : ByteArray) (count : Nat) : IO Unit := do
  let seed ← clockSeed
  let host := Evm.Bridge.host .osaka
  let given : UInt64 := 0xffffffffff
  let t0 ← clockMillis
  let mut used : UInt64 := 0
  let mut good := 0
  let mut size := 0
  for i in [0:count] do
    -- The seed (always 1) keeps the compiler from working the call out; the input is the same each time.
    let answer := host.precompile (Fast.Word.ofUInt64 (address * seed)) (if i == count then ByteArray.empty else input) given
    if answer.success then
      good := good + 1
      used := given - answer.gasLeft
      size := answer.output.size
  let t1 ← clockMillis
  -- In whole numbers: the runtime the guest has prints no others.
  let each := (t1 - t0).toNat * 1000 / count
  let most := if used == 0 then 0 else each * 16777216 / used.toNat / 1000
  let reckoned := Evm.Bridge.work (Fast.Word.ofUInt64 address) input
  say s!"{label}: {each} us a call (reckoned at {reckoned}), {used.toNat} gas, {good} of {count} succeeded with {size} bytes; a full transaction of them {most} ms\n"

def secpGx : Nat := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
def blsG1x : Nat := 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
def blsG1y : Nat := 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1
def bnG2 : ByteArray :=
  be 11559732032986387107991004021392285783925812861821192530917403151452391805634 32 ++
  be 10857046999023057135944570762232829481370756359578518086990519993285655852781 32 ++
  be 4082367875863433681332203403145435568316851327593401208105741076214120093531 32 ++
  be 8495653923123431417604973247489272438418190587263600148770280649306958101930 32
def bnP : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
def p256Gx : Nat := 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
def p256Gy : Nat := 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

def main (args : List String) : IO Unit := do
  let scale := (args.head? >>= String.toNat?).getD 1
  one "0x01 ecrecover" 1 (be 1 32 ++ be 27 32 ++ be secpGx 32 ++ be 0x1234567 32) (200 * scale)
  one "0x02 sha256, 96 KB" 2 (filled 96000 1) (20 * scale)
  one "0x03 ripemd160, 96 KB" 3 (filled 96000 2) (10 * scale)
  one "0x04 identity, 960 KB" 4 (filled 960000 3) (50 * scale)
  for size in [32, 64, 128, 256, 512, 1024] do
    let head := be size 32 ++ be size 32 ++ be size 32
    one s!"0x05 modexp, base, exponent and modulus of {size} bytes, all bits set but the modulus's last" 5
      (head ++ filled size 4 ++ ByteArray.mk (Array.replicate size 0xff) ++ (filled size 5).set! (size - 1) 0xfd |>.set! (96 + 2 * size) 0xff)
      (max 1 (scale * 2000000 / (size * size * size)))
    one s!"0x05 modexp, base and modulus of {size} bytes, exponent of one byte" 5
      (be size 32 ++ be 1 32 ++ be size 32 ++ filled size 4 ++ be 255 1 ++ ((filled size 5).set! 0 0xff)) (max 10 (scale * 200000 / (size * size)))
  one "0x06 bn254 addition" 6 (be 1 32 ++ be 2 32 ++ be 1 32 ++ be 2 32) (2000 * scale)
  one "0x07 bn254 multiplication" 7 (be 1 32 ++ be 2 32 ++ be (2 ^ 256 - 1) 32) (50 * scale)
  one "0x08 bn254 pairing, two pairs" 8 (be 1 32 ++ be 2 32 ++ bnG2 ++ be 1 32 ++ be (bnP - 2) 32 ++ bnG2) (10 * scale)
  one "0x09 blake2f, 100,000 rounds" 9 (be 100000 4 ++ filled 208 6 ++ be 1 1) (10 * scale)
  one "0x0b BLS12-381 G1 addition" 0x0b (be blsG1x 64 ++ be blsG1y 64 ++ be blsG1x 64 ++ be blsG1y 64) (50 * scale)
  one "0x0c BLS12-381 G1 multiplication, one point" 0x0c (be blsG1x 64 ++ be blsG1y 64 ++ be (2 ^ 255 - 19) 32) (3 * scale)
  one "0x10 BLS12-381 field element to G1" 0x10 (be (blsG1x - 5) 64) (10 * scale)
  one "0x100 P-256 verification" 0x100 (be 1 32 ++ be 1 32 ++ be 1 32 ++ be p256Gx 32 ++ be p256Gy 32) (20 * scale)
