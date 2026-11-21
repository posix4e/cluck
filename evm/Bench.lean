import Jaune.Precompiles
import Jaune.MessageCall.Exec
import Evm
import Fast.Spike
import Fast.Keccak
import Platform

/-! Times Jaune's hashing, curve arithmetic and interpreter, on whichever runtime this is linked against.
Each line ends with the result, so that two runtimes can be compared on what they computed as well as on how
long they took. Runs as a process only. -/
open Jaune

@[extern "evm_clock_millis"] opaque clockMillis : IO UInt64
/-- A number the compiler cannot see, so that no workload is worked out while compiling. Always 1. -/
@[extern "evm_clock_seed"] opaque clockSeed : IO UInt64

def say (s : String) : IO Unit := Platform.write s.toUTF8

def timed (label : String) (f : Unit → String) : IO Unit := do
  let t0 ← clockMillis
  let r ← IO.lazyPure f
  let t1 ← clockMillis
  say s!"{label}: {(t1 - t0).toNat} ms -> {r}\n"

def iter {α} (n : Nat) (f : α → α) (x : α) : α := Nat.rec x (fun _ acc => f acc) n

def keccakChain (n : Nat) (x : U256) : U256 := Id.run do
  let mut x := x
  for _ in [0:n] do x := U256.keccak x
  return x

def mulmodChain (n : Nat) (x : U256) : U256 := Id.run do
  let p : U256 := (2 ^ 256 - 189 : Nat).toU256
  let mut x := x
  for _ in [0:n] do x := U256.mulmod x (x + 3) p
  return x

def recoverMany (n : Nat) (x : U256) : Nat := Id.run do
  let mut h := x
  let mut hits := 0
  for _ in [0:n] do
    h := U256.keccak h
    let r := U256.keccak h
    let s := U256.keccak r
    if (secp256k1.recover h false r s).isSome then hits := hits + 1
  return hits

def g2Generator : Bytes :=
  (11559732032986387107991004021392285783925812861821192530917403151452391805634 : Nat).toU256.toBytes ++
  (10857046999023057135944570762232829481370756359578518086990519993285655852781 : Nat).toU256.toBytes ++
  (4082367875863433681332203403145435568316851327593401208105741076214120093531 : Nat).toU256.toBytes ++
  (8495653923123431417604973247489272438418190587263600148770280649306958101930 : Nat).toU256.toBytes

def pairingOnce (seed : Nat) : String :=
  let data : Bytes := seed.toU256.toBytes ++ (2 : Nat).toU256.toBytes ++ g2Generator
  match executePairingCheckInner data 0 with
  | .ok (_, out) => s!"ok {out.toHex}"
  | .error _ => "error"

def bigOf (limbs : Nat) (x : U256) : Nat := Id.run do
  let mut h := x
  let mut n := 0
  for _ in [0:limbs] do
    h := U256.keccak h
    n := (n <<< 256) ||| h.toNat
  return n

def powModOnce (x : U256) : U256 :=
  let b := bigOf 8 x
  let e := bigOf 8 (x + 1)
  let m := bigOf 8 (x + 2) ||| 1
  (Nat.powMod b e m % 2 ^ 256).toU256

/-- PUSH1 0; JUMPDEST; PUSH1 1; ADD; DUP1; PUSH3 n; GT; PUSH1 2; JUMPI; STOP: eight opcodes a round. -/
def loopCode (n : Nat) : ByteArray :=
  ⟨#[0x60, 0x00, 0x5b, 0x60, 0x01, 0x01, 0x80, 0x62,
     (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8, 0x11, 0x60, 0x02, 0x57, 0x00]⟩

def loopRun (n : Nat) : String :=
  let sevm : Sevm := { (default : Sevm) with code := loopCode n }
  let devm : Devm := (default : Devm).withGasLeft 1000000000
  match exec ⟨0, sevm, devm⟩ with
  | .ok d => s!"ok gasLeft {d.gasLeft} stack {d.stack.length}"
  | .error (_, d) => s!"error gasLeft {d.gasLeft}"

def fastKeccakChain (n : Nat) (x : U256) : String := Id.run do
  let mut b := Evm.Trie.wordBytes x
  for _ in [0:n] do b := (Fast.Keccak.hash b 0 32).bytes
  return (Evm.Trie.word b 0).toHex

def jauneKeccakBytes (n : Nat) (size : Nat) : String := Id.run do
  let mut b : ByteArray := ⟨Array.replicate size 0x5a⟩
  let mut x : U256 := 0
  for _ in [0:n] do
    x := ByteArray.keccak 0 size b
    b := b.set! 0 x.2.2.toUInt8
  return x.toHex

def fastKeccakBytes (n : Nat) (size : Nat) : String := Id.run do
  let mut b : ByteArray := ⟨Array.replicate size 0x5a⟩
  let mut d : Fast.Keccak.Digest := ⟨0, 0, 0, 0⟩
  for _ in [0:n] do
    d := Fast.Keccak.hash b 0 size
    b := b.set! 0 (d.w3 >>> 56).toUInt8
  return (Evm.Trie.word d.bytes 0).toHex

def fastLoop (n : Nat) : String :=
  let out := Fast.Spike.bytesRun (loopCode n) 1000000000
  s!"halt {out.halt} gasLeft {out.gas} stack {out.depth}"

def fastLimbs (n : Nat) : String :=
  let out := Fast.Spike.limbsRun (loopCode n) 1000000000
  s!"halt {out.halt} gasLeft {out.gas} stack {out.depth}"

def main : IO UInt32 := do
  let seed := (← clockSeed).toNat
  let x := seed.toU256
  timed "keccak256 of 32 bytes x 5000" fun _ => (keccakChain 5000 x).toHex
  timed "mulmod 256-bit x 200000" fun _ => (mulmodChain 200000 x).toHex
  timed "secp256k1 recover x 20" fun _ => toString (recoverMany 20 x)
  timed "bn254 pairing, one pair" fun _ => pairingOnce seed
  timed "modexp 2048-bit" fun _ => (powModOnce x).toHex
  timed "EVM loop, 200000 rounds of 8 opcodes" fun _ => loopRun (200000 * seed)
  timed "fast keccak256 of 32 bytes x 5000" fun _ => fastKeccakChain 5000 x
  timed "keccak256 of 32 bytes x 200000" fun _ => (keccakChain 200000 x).toHex
  timed "fast keccak256 of 32 bytes x 200000" fun _ => fastKeccakChain 200000 x
  timed "keccak256 of 532 bytes x 50000" fun _ => jauneKeccakBytes 50000 (532 * seed)
  timed "fast keccak256 of 532 bytes x 50000" fun _ => fastKeccakBytes 50000 (532 * seed)
  timed "fast loop, stack as bytes, 200000 rounds of 8 opcodes" fun _ => fastLoop (200000 * seed)
  timed "fast loop, stack as bytes, 10000000 rounds of 8 opcodes" fun _ => fastLoop (10000000 * seed)
  timed "fast loop, stack as limbs, 10000000 rounds of 8 opcodes" fun _ => fastLimbs (10000000 * seed)
  return 0
