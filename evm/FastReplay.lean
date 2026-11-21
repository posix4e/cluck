import Evm.Bridge

/-! Saved blocks of the real chain put through the fast engine, with each block's own header as the judge.

    .lake/build/bin/fast-replay REQUEST...       stateless requests, as `witness/fetch` writes them

A header commits to the gas its block used, to the root of its receipts (each transaction's success, the
gas used up to it and its logs), to the bloom of those logs and to the hash of its requests. The engine
runs the block on the state the request's witness gives and all four must come out as the header has them.
What this does not judge is the state after the block: the state root is not worked out here yet. Runs on
Lean's runtime; the roots are made by Jaune's functions. -/
open Jaune Evm

def judge (path : String) : IO Bool := do
  let input ← IO.FS.readBinFile path
  let name := (System.FilePath.mk path).fileName.getD path
  let some (r, _) := (Stateless.request input).run 0 | do IO.println s!"{name}: not a request"; return false
  let .ok (block, _) := rlpToBlockE r.block.toList | do IO.println s!"{name}: the block does not decode"; return false
  let fork? := match r.fork with
    | some fork => some fork
    | none => (mainnetChainConfig.forkAt block.header.number block.header.timestamp).toOption
  let some fork := fork? | do IO.println s!"{name}: no fork"; return false
  let some ancestors := r.headers.mapM Stateless.header | do IO.println s!"{name}: a header does not decode"; return false
  let some parent := ancestors.getLast? | do IO.println s!"{name}: no headers"; return false
  let t0 ← IO.monoMsNow
  let .ok known := Stateless.materialise r parent.stateRoot | do IO.println s!"{name}: the witness does not read"; return false
  let t1 ← IO.monoMsNow
  let some body := Bridge.body fork r.chainId block | do IO.println s!"{name}: a transaction does not decode"; return false
  let t2 ← IO.monoMsNow
  let blk := Bridge.environment fork r.chainId block.header ancestors
  let result ← IO.lazyPure fun _ =>
    Fast.runBlock blk (Bridge.host fork) body ByteArray.empty (Fast.World.new (Bridge.backing known))
  let t3 ← IO.monoMsNow
  match result with
  | .error why => IO.println s!"{name}: REFUSED: {why}"; return false
  | .ok out =>
    let (root, bloom) := Bridge.receiptsRootAndBloom out.receipts
    let requests := computeRequestsHash (out.requests.toList.map (·.toList))
    let header := block.header
    let mut wrong : List String := []
    if out.gasUsed.toNat != header.gasUsed then wrong := s!"gas used {out.gasUsed.toNat}, the header has {header.gasUsed}" :: wrong
    if root != header.receiptsRoot then wrong := "receipts root" :: wrong
    if bloom != header.logsBloom then wrong := "logs bloom" :: wrong
    if header.requestsHash.isSome && header.requestsHash != some requests then wrong := "requests hash" :: wrong
    if out.world.missing then wrong := "something was asked for that the witness did not have" :: wrong
    let times := s!"witness {t1 - t0} ms, senders {t2 - t1} ms, block {t3 - t2} ms"
    if wrong.isEmpty then
      IO.println s!"{name}: block {header.number}, {out.receipts.size} transactions, {header.gasUsed} gas: as the header has it ({times})"
      return true
    else
      IO.println s!"{name}: block {header.number}, {out.receipts.size} transactions: WRONG: {", ".intercalate wrong.reverse} ({times})"
      return false

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: fast-replay REQUEST..."
    return 2
  let mut good := 0
  for path in args do
    if ← judge path then good := good + 1
  IO.println s!"fast-replay: {good} of {args.length} blocks as their headers have them"
  return if good == args.length then 0 else 1
