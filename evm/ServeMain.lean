import Evm
import Platform

/-! The service as a process: reads one request to the end of standard input, writes one response. The same
compiled Lean is linked against Lean's own runtime and against the minimal one, and the two must agree. -/

partial def readAll (soFar : ByteArray) : IO ByteArray := do
  let chunk ← Platform.read 65536
  if chunk.isEmpty then pure soFar else readAll (soFar ++ chunk)

def main : IO UInt32 := do
  Platform.write (Evm.Service.serve (← readAll .empty))
  return 0
