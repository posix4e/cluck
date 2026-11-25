import Jaune.MessageCall.Exec
import Fast.Interp

/-! The fast engine's interpreter against Jaune's, a program at a time. Each program is run by both from
the same code, input and gas, and the two must end the same way with the same gas left and the same bytes
returned. The programs: every arithmetic, comparison and bitwise instruction on awkward and random
operands; and programs of instructions drawn at random from those that need no world (stack, arithmetic,
memory, input, code, flow of control by fixed jumps), kept valid as they are drawn by counting what is on
the stack. Runs on Lean's runtime: Jaune is the reference, and it is not asked to be anything else here. -/
open Fast

def next (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

def draw (s : UInt64) : Word × UInt64 :=
  let a := next s
  let b := next a
  let c := next b
  let d := next c
  let e := next d
  let w : Word :=
    match e % 10 with
    | 0 | 1 | 2 => ⟨a, b, c, d⟩
    | 3 => ⟨a, 0, 0, 0⟩
    | 4 => ⟨a % 300, 0, 0, 0⟩
    | 5 => ⟨a % 40, 0, 0, 0⟩
    | 6 => Word.ofNat (2 ^ (a % 256).toNat + (b % 3).toNat - 1)
    | 7 => (Word.ofNat (2 ^ (a % 256).toNat)).not
    | 8 => Word.zero
    | _ => ⟨a &&& b, 0, d &&& a, if (b >>> 9) % 2 == 0 then 0 else c ||| d⟩
  (w, e)

def hexOf (b : ByteArray) : String :=
  b.foldl (fun out x => out ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

def gasGiven : Nat := 2000000

/-- How Jaune ends a program: how, the gas left, the bytes returned. -/
def byJaune (osaka : Bool) (code input : ByteArray) : String :=
  let stat : Jaune.BenvStat := { (default : Jaune.BenvStat) with fork := if osaka then .osaka else .prague }
  let sevm : Jaune.Sevm := { (default : Jaune.Sevm) with code := code, data := input.toList, benvStat := stat }
  let devm : Jaune.Devm := (default : Jaune.Devm).withGasLeft gasGiven
  match Jaune.exec ⟨0, sevm, devm⟩ with
  | .ok d => s!"ok {d.gasLeft} {hexOf ⟨d.output.toArray⟩}"
  | .error (e, d) =>
    match e with
    | .revert => s!"revert {d.gasLeft} {hexOf ⟨d.output.toArray⟩}"
    | _ => "lost"

def byFast (osaka : Bool) (code input : ByteArray) : String :=
  let blk : BlockEnv :=
    { coinbase := Word.zero, number := 0, timestamp := 0, gasLimit := 0, prevRandao := Word.zero,
      baseFee := Word.zero, blobBaseFee := Word.zero, chainId := 0, blockHash := fun _ => Word.zero, osaka }
  let tx : TxEnv := { origin := Word.zero, gasPrice := Word.zero, blobHashes := #[] }
  let host : Host := { isPrecompile := fun _ => false, precompile := fun _ _ _ => ⟨false, 0, ByteArray.empty⟩ }
  let frame : Frame :=
    { address := Word.zero, caller := Word.zero, value := Word.zero, input, code,
      jumps := World.jumpBits code, static := false, depth := 0, base := 0 }
  let out := execute blk tx host frame ByteArray.empty gasGiven.toUInt64 (World.new default)
  if out.halt == 0 then s!"ok {out.gas.toNat} {hexOf out.output}"
  else if out.halt == 1 then s!"revert {out.gas.toNat} {hexOf out.output}"
  else "lost"

def push32 (w : Word) : ByteArray := (ByteArray.mk #[0x7f]) ++ w.bytes

/-- The top of the stack returned as 32 bytes. -/
def returnTop : ByteArray := ⟨#[0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- Instructions for random programs: the byte, how many words it takes off, how many it puts on. -/
def plain : Array (UInt8 × Nat × Nat) := #[
  (0x01, 2, 1), (0x02, 2, 1), (0x03, 2, 1), (0x04, 2, 1), (0x05, 2, 1), (0x06, 2, 1), (0x07, 2, 1),
  (0x08, 3, 1), (0x09, 3, 1), (0x0b, 2, 1), (0x10, 2, 1), (0x11, 2, 1), (0x12, 2, 1), (0x13, 2, 1),
  (0x14, 2, 1), (0x15, 1, 1), (0x16, 2, 1), (0x17, 2, 1), (0x18, 2, 1), (0x19, 1, 1), (0x1a, 2, 1),
  (0x1b, 2, 1), (0x1c, 2, 1), (0x1d, 2, 1), (0x30, 0, 1), (0x33, 0, 1), (0x34, 0, 1), (0x35, 1, 1),
  (0x36, 0, 1), (0x38, 0, 1), (0x3d, 0, 1), (0x50, 1, 0), (0x58, 0, 1), (0x59, 0, 1), (0x5a, 0, 1),
  (0x5b, 0, 0), (0x5f, 0, 1)]

/-- A program of `length` random instructions and what is left on its stack. Memory instructions get small
offsets pushed for them, so that they are affordable; everything else takes what is there. -/
def randomProgram (seed : UInt64) (length : Nat) : ByteArray × Nat × UInt64 := Id.run do
  let mut code := ByteArray.empty
  let mut depth := 0
  let mut s := seed
  for _ in [0:length] do
    s := next s
    let choice := s % 100
    if depth < 3 || choice < 22 then
      -- A push of a random width and value.
      let (w, s') := draw s
      s := s'
      let n := (s % 32).toNat + 1
      code := (code.push (0x5f + n).toUInt8) ++ w.bytes.extract (32 - n) 32
      depth := depth + 1
    else if choice < 32 && depth < 1000 then
      let n := (s >>> 8) % (min depth 16).toUInt64
      code := code.push (0x80 + n).toUInt8
      depth := depth + 1
    else if choice < 40 && depth ≥ 2 then
      let n := (s >>> 8) % (min (depth - 1) 16).toUInt64
      code := code.push (0x90 + n).toUInt8
    else if choice < 46 then
      -- MSTORE or MSTORE8 of the top at a small offset.
      code := (code ++ ⟨#[0x61, ((s >>> 9) % 3).toUInt8, (s >>> 17).toUInt8]⟩).push (if s >>> 30 % 2 == 0 then 0x52 else 0x53)
      depth := depth - 1
    else if choice < 51 then
      -- MLOAD at a small offset.
      code := code ++ ⟨#[0x61, ((s >>> 9) % 3).toUInt8, (s >>> 17).toUInt8, 0x51]⟩
      depth := depth + 1
    else if choice < 54 then
      -- KECCAK256 of a small range.
      code := code ++ ⟨#[0x61, ((s >>> 9) % 2).toUInt8, (s >>> 17).toUInt8, 0x60, (s >>> 25).toUInt8, 0x20]⟩
      depth := depth + 1
    else if choice < 59 then
      -- CALLDATACOPY, CODECOPY or MCOPY: length, source, destination, all small.
      let op : UInt8 := if (s >>> 40) % 3 == 0 then 0x37 else if (s >>> 40) % 3 == 1 then 0x39 else 0x5e
      code := code ++ ⟨#[0x61, ((s >>> 9) % 2).toUInt8, (s >>> 17).toUInt8, 0x61, ((s >>> 44) % 2).toUInt8, (s >>> 25).toUInt8,
                         0x61, ((s >>> 33) % 2).toUInt8, (s >>> 48).toUInt8, op]⟩
    else if choice < 61 then
      -- EXP with a small exponent pushed, so that its price is not the whole budget.
      code := code ++ ⟨#[0x61, (s >>> 9).toUInt8, (s >>> 17).toUInt8, 0x90, 0x0a]⟩
    else
      let (op, takes, gives) := plain[((s >>> 8) % plain.size.toUInt64).toNat]!
      if depth ≥ takes && depth - takes + gives ≤ 1000 then
        code := code.push op
        depth := depth - takes + gives
  return (code, depth, s)

/-- The end of a random program: up to four words of what is on the stack, and all of memory up to a
kilobyte, returned. -/
def returnSome (depth : Nat) : ByteArray := Id.run do
  let mut code := ByteArray.empty
  for i in [0:min depth 4] do
    code := code ++ ⟨#[0x61, 0x04, (i * 32).toUInt8, 0x52]⟩
  return code ++ ⟨#[0x61, 0x04, 0x80, 0x60, 0x00, 0xf3]⟩

def main : IO UInt32 := do
  let mut failures := 0
  let mut seed : UInt64 := 0x243f6a8885a308d3
  let mut words : Array Word := #[Word.zero, Word.one, Word.ones, Word.ofNat (2 ^ 255), Word.ofNat (2 ^ 255 - 1),
    Word.ofNat 31, Word.ofNat 32, Word.ofNat 255, Word.ofNat 256, Word.ofNat (2 ^ 64), Word.ofNat (2 ^ 128 - 1)]
  for _ in [0:60] do
    let (w, s) := draw seed
    words := words.push w
    seed := s
  -- One instruction at a time.
  let mut ran := 0
  for (op, takes) in ([(0x01, 2), (0x02, 2), (0x03, 2), (0x04, 2), (0x05, 2), (0x06, 2), (0x07, 2), (0x08, 3), (0x09, 3),
      (0x0a, 2), (0x0b, 2), (0x10, 2), (0x11, 2), (0x12, 2), (0x13, 2), (0x14, 2), (0x15, 1), (0x16, 2), (0x17, 2),
      (0x18, 2), (0x19, 1), (0x1a, 2), (0x1b, 2), (0x1c, 2), (0x1d, 2), (0x1e, 1)] : List (UInt8 × Nat)) do
    for i in [0:words.size] do
      for j in [0:if takes ≥ 2 then words.size else 1] do
        for k in [0:if takes == 3 then 6 else 1] do
          let c := words[(i * 5 + j * 11 + k * 17) % words.size]!
          let code := (if takes == 3 then push32 c else ByteArray.empty) ++ (if takes ≥ 2 then push32 words[j]! else ByteArray.empty) ++
            push32 words[i]! ++ (ByteArray.mk #[op]) ++ returnTop
          let osaka := op == 0x1e
          let (a, b) := (byJaune osaka code ByteArray.empty, byFast osaka code ByteArray.empty)
          ran := ran + 1
          if a != b then
            failures := failures + 1
            if failures < 15 then IO.println s!"instruction {op}: code {hexOf code}\n  Jaune: {a}\n  fast:  {b}"
  IO.println s!"single instructions: {ran} programs"
  -- Programs drawn at random.
  let mut programs := 0
  let mut ended := 0
  let mut returned := 0
  for round in [0:3000] do
    let (body, depth, s) := randomProgram seed (20 + round % 180)
    seed := s
    let code := body ++ returnSome depth
    let input : ByteArray := ⟨(List.range ((s >>> 20) % 200).toNat).map (fun i => (i * 37 + round).toUInt8) |>.toArray⟩
    let (a, b) := (byJaune false code input, byFast false code input)
    programs := programs + 1
    if a.startsWith "ok" then
      ended := ended + 1
      returned := returned + (a.length - 10) / 2
    if a != b then
      failures := failures + 1
      if failures < 15 then IO.println s!"program {round}: code {hexOf code}\n  input {hexOf input}\n  Jaune: {a}\n  fast:  {b}"
  IO.println s!"random programs: {programs}, of which {ended} ran to their end, returning {returned} bytes in all"
  -- Work for precompiled contracts. A host with one contract, at address 9, that costs 1,000 a call and
  -- answers with one byte; a program that calls it three times and returns what the three calls said.
  let host : Host :=
    { isPrecompile := fun a => a == Word.ofUInt64 9, work := fun _ _ => 1000
      precompile := fun _ _ gas => ⟨true, gas, ⟨#[7]⟩⟩ }
  -- STATICCALL(gas 50000, 9, 0, 0, 0, 0), its answer stored at 0, 32 and 64; then 96 bytes returned.
  let call (at_ : UInt8) : ByteArray := ⟨#[0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0x09, 0x61, 0xc3, 0x50, 0xfa, 0x60, at_, 0x52]⟩
  let code := call 0 ++ call 32 ++ call 64 ++ ⟨#[0x60, 0x60, 0x5f, 0xf3]⟩
  let blk : BlockEnv :=
    { coinbase := Word.zero, number := 0, timestamp := 0, gasLimit := 0, prevRandao := Word.zero,
      baseFee := Word.zero, blobBaseFee := Word.zero, chainId := 0, blockHash := fun _ => Word.zero, osaka := true }
  let frame : Frame :=
    { address := Word.zero, caller := Word.zero, value := Word.zero, input := ByteArray.empty, code,
      jumps := World.jumpBits code, static := false, depth := 0, base := 0 }
  let env : TxEnv := { origin := Word.zero, gasPrice := Word.zero, blobHashes := #[] }
  let said (out : Outcome) : List UInt8 := [31, 63, 95].map fun i => out.output.data.getD i 9
  let expect (what : String) (work : UInt64) (answers : List UInt8) (left : UInt64) (over : Bool) : IO Bool := do
    let out := execute blk env host frame ByteArray.empty 1000000 { World.new default with work }
    let good := out.halt == 0 && said out == answers && out.world.work == left && out.world.overworked == over
    if !good then
      IO.println s!"work for precompiled contracts, {what}: halt {out.halt}, the calls said {said out}, work left {out.world.work.toNat}, marked {out.world.overworked}"
    return good
  let mut works := 0
  for (what, work, answers, left, over) in [
      ("no limit", (0xffffffffffffffff : UInt64), [1, 1, 1], (0xffffffffffffffff : UInt64) - 3000, false),
      ("enough for exactly three calls", 3000, [1, 1, 1], 0, false),
      ("enough for two: the third fails and the world is marked", 2999, [1, 1, 0], 999, true),
      ("enough for none: all three fail", 999, [0, 0, 0], 999, true)] do
    works := works + 1
    if !(← expect what work answers left over) then failures := failures + 1
  IO.println s!"work for precompiled contracts: {works} limits"
  if failures == 0 then IO.println "fast-op-test: all checks passed" else IO.println s!"fast-op-test: {failures} FAILED"
  return if failures == 0 then 0 else 1
