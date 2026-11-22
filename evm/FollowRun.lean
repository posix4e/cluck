import Evm.Follow
import Platform

/-! Blocks put to `Evm/Follow.lean` one after another in one process, as the machine is put them, for
finding out how much memory following the chain takes.

    scripts/follow-memory BLOCK.req...       (frames them, runs this on the minimal runtime, reports)

Standard input is frames: four bytes of length, then a request to follow a block ("JFOL1" and what
follows). Each is read as the machine reads one, in pieces that are joined once, answered, and a line
printed. Linked against the minimal runtime (`scripts/build-min follow-run`) the process's memory is the
runtime's one region, handed out from the front and never given back, so the most memory the process ever
held is how far into the region the allocator got: what a machine with that much heap needs. -/
open Evm

/-- Exactly `n` bytes of standard input, read in pieces and joined once; fewer at its end. -/
partial def frame (n : Nat) : IO ByteArray := do
  let mut pieces : Array ByteArray := #[]
  let mut have_ := 0
  while have_ < n do
    let piece ← Platform.read (min 65536 (n - have_)).toUSize
    if piece.isEmpty then break
    pieces := pieces.push piece
    have_ := have_ + piece.size
  let mut whole := ByteArray.emptyWithCapacity have_
  for piece in pieces do whole := piece.copySlice 0 whole whole.size piece.size
  return whole

partial def loop (chain : Follow.Chain) (pool : Seal.Pool) (count : Nat) : IO UInt32 := do
  let head ← frame 4
  if head.size < 4 then
    Platform.write s!"{count} blocks put\n".toUTF8
    return 0
  let size := head.foldl (fun n b => n * 256 + b.toNat) 0
  let request ← frame size
  let (answer, chain, pool) := Follow.serve chain pool request
  let number := (chain.head?.map (·.number)).getD 0
  Platform.write s!"{size} bytes: status {answer[0]!.toNat}, the newest block known is {number}, {chain.recent.size} kept\n".toUTF8
  loop chain pool (count + 1)

def main : IO UInt32 := loop {} {} 0
