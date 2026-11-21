import Evm
import Evm.Bid
import Platform

/-! The service as a process: reads one request to the end of standard input, writes one response. The same
compiled Lean is linked against Lean's own runtime and against the minimal one, and the two must agree.

A process holds no key of its own. A request for a bid, or for the builder's key, is answered with a key
that everyone knows (`Evm.Bid.testKey`), so that the answers are the same every time and can be kept as
fixtures; a signature from it binds nobody. -/

partial def readAll (soFar : ByteArray) : IO ByteArray := do
  let chunk ← Platform.read 65536
  if chunk.isEmpty then pure soFar else readAll (soFar ++ chunk)

def main : IO UInt32 := do
  let request ← readAll .empty
  match Evm.Bid.testKey with
  | some key => Platform.write (if Evm.Bid.mine request then Evm.Bid.serve key request else Evm.serve request)
  | none => Platform.write (Evm.serve request)
  return 0
