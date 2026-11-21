import Evm.Bridge

/-! Saved blocks of the real chain put through the fast engine, with each block's own header as the judge.

    .lake/build/bin/fast-replay REQUEST...       stateless requests, as `witness/fetch` writes them
    .lake/build/bin/fast-replay --where ADDRESS REQUEST     which transaction first makes the engine fetch an account

A header commits to the gas its block used, to the root of its receipts (each transaction's success, the
gas used up to it and its logs), to the bloom of those logs, to the hash of its requests, and to the root
of the state after it. The engine runs the block on the request's witness, asking it for each account and
slot as it comes to them, nothing may be asked that the witness cannot prove an answer to, and all five
must come out as the header has them. Runs
on Lean's runtime; the receipts root and the bloom are made by Jaune's functions, the state root by this
package's trie. -/
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
  let witness ← IO.lazyPure fun _ => Bridge.Witness.of r parent.stateRoot
  let indexed := witness.codes.size
  let t1 ← IO.monoMsNow
  let .ok decoded := block.transactions.mapM (decodeTransaction fork.ruleSet)
    | do IO.println s!"{name}: a transaction does not decode"; return false
  let some body := Bridge.body fork r.chainId block decoded | do IO.println s!"{name}: a transaction has no sender"; return false
  let t2 ← IO.monoMsNow
  let blk := Bridge.environment fork r.chainId block.header ancestors
  let result ← IO.lazyPure fun _ =>
    Fast.runBlock blk (Bridge.host fork) body ByteArray.empty (Fast.World.new witness.backing)
  let t3 ← IO.monoMsNow
  match result with
  | .error (why, _) => IO.println s!"{name}: REFUSED: {why}"; return false
  | .ok out =>
    let (root, bloom) ← IO.lazyPure fun _ => Bridge.receiptsRootAndBloom out.receipts
    let requests := computeRequestsHash (out.requests.toList.map (·.toList))
    let header := block.header
    let mut wrong : List String := []
    if out.gasUsed.toNat != header.gasUsed then wrong := s!"gas used {out.gasUsed.toNat}, the header has {header.gasUsed}" :: wrong
    if root != header.receiptsRoot then wrong := "receipts root" :: wrong
    if bloom != header.logsBloom then wrong := "logs bloom" :: wrong
    if header.requestsHash.isSome && header.requestsHash != some requests then wrong := "requests hash" :: wrong
    if out.world.missing then wrong := s!"the witness lacks what was asked of {(Bridge.u256 out.world.lacking).toHex}" :: wrong
    let stateRoot ← IO.lazyPure fun _ => Bridge.rootAfter witness out.world
    let t4 ← IO.monoMsNow
    match stateRoot with
    | .ok stateRoot => if stateRoot != header.stateRoot then wrong := "state root" :: wrong
    | .error (.lacking _ what) => wrong := s!"the witness lacks {what}" :: wrong
    | .error _ => wrong := "the state root could not be worked out" :: wrong
    let times := s!"witness {t1 - t0} ms ({indexed} codes), senders {t2 - t1} ms, block {t3 - t2} ms, state root {t4 - t3} ms"
    if wrong.isEmpty then
      IO.println s!"{name}: block {header.number}, {out.receipts.size} transactions, {header.gasUsed} gas: as the header has it ({times})"
      return true
    else
      IO.println s!"{name}: block {header.number}, {out.receipts.size} transactions: WRONG: {", ".intercalate wrong.reverse} ({times})"
      return false

/-- Which transaction of a block first makes the engine fetch an account: for finding out why a witness
that was enough for Jaune is not enough for the engine. Runs the block again with one more transaction
each time, so it is slow. -/
def whereFetched (path : String) (hexAddress : String) : IO Unit := do
  let input ← IO.FS.readBinFile path
  let some (r, _) := (Stateless.request input).run 0 | IO.println "not a request"
  let .ok (block, _) := rlpToBlockE r.block.toList | IO.println "the block does not decode"
  let some fork := (match r.fork with
    | some fork => some fork
    | none => (mainnetChainConfig.forkAt block.header.number block.header.timestamp).toOption) | IO.println "no fork"
  let some ancestors := r.headers.mapM Stateless.header | IO.println "a header does not decode"
  let some parent := ancestors.getLast? | IO.println "no headers"
  let witness := Bridge.Witness.of r parent.stateRoot
  let .ok decoded := block.transactions.mapM (decodeTransaction fork.ruleSet) | IO.println "a transaction does not decode"
  let some body := Bridge.body fork r.chainId block decoded | IO.println "a transaction has no sender"
  let blk := Bridge.environment fork r.chainId block.header ancestors
  let wanted := Fast.Word.ofHex hexAddress
  -- What the witness has for the account.
  match Trie.get witness.store (.sealed witness.root) (Bridge.pathOf wanted.addressBytes) with
  | .ok (some bytes) =>
    match Stateless.Leaf.read bytes with
    | some leaf =>
      IO.println s!"in the witness's trie: nonce {leaf.nonce.toNat}, balance {leaf.balance.toNat}, code hash {leaf.codeHash.toHex}, \
        storage root {leaf.storageRoot.toHex}; a code with that hash is in the request: \
        {witness.codes.contains (Bridge.word leaf.codeHash)}"
    | none => IO.println "in the witness's trie, and its entry does not read"
  | .ok none => IO.println "proven by the witness not to be in the state"
  | .error _ => IO.println "the witness does not reach it"
  for count in [0:body.transactions.size + 1] do
    let part := { body with transactions := body.transactions.extract 0 count }
    match Fast.runBlock blk (Bridge.host fork) part ByteArray.empty (Fast.World.new witness.backing) with
    | .error (why, _) => IO.println s!"with {count} transactions: {why}"; return
    | .ok out =>
      if out.world.accounts.contains wanted then
        if count == 0 then IO.println "fetched by the block's own calls, before any transaction"
        else if let some tx := body.transactions[count - 1]? then
          IO.println s!"first fetched in transaction {count - 1}: from {(Bridge.u256 tx.sender).toHex} to \
            {(tx.callee.map fun a => (Bridge.u256 a).toHex).getD "(creation)"}, nonce {tx.nonce.toNat}, gas {tx.gasLimit.toNat}; \
            it {if (out.receipts.back?.map (·.success)).getD false then "succeeded" else "failed"}"
        return
  IO.println "never fetched"

def main (args : List String) : IO UInt32 := do
  if let ["--where", address, path] := args then
    whereFetched path address
    return 0
  if args.isEmpty then
    IO.eprintln "usage: fast-replay REQUEST..."
    return 2
  let mut good := 0
  for path in args do
    if ← judge path then good := good + 1
  IO.println s!"fast-replay: {good} of {args.length} blocks as their headers have them"
  return if good == args.length then 0 else 1
