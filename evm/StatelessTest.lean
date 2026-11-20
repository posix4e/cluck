import Evm

/-! Tests of `Evm.Stateless` against the import that has the whole state.

Each fixture in `fixtures/` is a chain with its whole starting state. Every block of it is imported the
ordinary way, and before each one a witness is cut from the whole state as it then stands: every node of
the state trie and of every storage trie, every contract's code, every address and slot. The block and
that witness, with no state, must get the same answer.

Then the witness is made to fall short, one piece at a time: each node, each key and each code is left out
in turn. With a piece missing the answer must be the same again (the block did not need it) or say that
there is no verdict (6 or 8). It must never be a different verdict. That is the property the whole design
is for: nothing left out of a witness can turn into a wrong answer.

    .lake/build/bin/stateless-test          (from evm/; add `all` for the fixture that takes a minute,
                                             `write` to make fixtures/stateless/ again)

Run on Lean's own runtime. -/
open Jaune Evm

def headerBytes (h : Header) : ByteArray := (Header.toRlpItem h).toBytes.toByteArray

structure Witness where
  nodes : Array ByteArray
  codes : List ByteArray
  keys : List ByteArray
  root : U256

/-- A witness for all of a state. -/
def witnessOf (state : State) : Except Trie.Fault Witness := do
  let mut trie : Trie.Node := .empty
  let mut nodes : Array ByteArray := #[]
  let mut codes : List ByteArray := []
  let mut keys : List ByteArray := []
  for (address, account) in state.toList do
    let mut storage : Trie.Node := .empty
    for (slot, value) in Std.TreeMap.toList account.storage do
      storage ← Trie.put .empty storage (Stateless.keyOf slot.toBytes) (Stateless.slotValue value)
      keys := slot.toBytes.toByteArray :: keys
    nodes := Trie.encodings storage nodes
    let leaf : Stateless.Leaf :=
      ⟨account.nonce, account.balance, Trie.rootHash storage, Trie.hashOf account.code⟩
    trie ← Trie.put .empty trie (Stateless.keyOf address.toBytes) leaf.write
    if account.code.size > 0 then codes := account.code :: codes
    keys := address.toBytes.toByteArray :: keys
  pure ⟨Trie.encodings trie nodes, codes, keys, Trie.rootHash trie⟩

def same (a b : Service.Response) : Bool := a.encode == b.encode

def noVerdict (r : Service.Response) : Bool := r.status == 6 || r.status == 8

structure Tally where
  failures : Nat := 0
  blocks : Nat := 0
  shortened : Nat := 0
  noticed : Nat := 0

def fixture (name : String) (shorten : Bool) (tally : Tally) (write : Bool := false) : IO Tally := do
  let mut tally := tally
  let fail (what : String) (t : Tally) : IO Tally := do
    IO.println s!"{name}: {what}"
    pure { t with failures := t.failures + 1 }
  let bytes ← IO.FS.readBinFile s!"fixtures/{name}.req"
  let some (whole, _) := (Service.request bytes).run 0 | fail "the fixture is not a request" tally
  let .ok rules := whole.fork.rules | fail "the fixture's fork has no rules" tally
  let .ok (genesis, _) := rlpToBlockEAt rules whole.genesis | fail "the genesis block does not decode" tally
  let mut chain : BlockChain :=
    { blocks := [genesis], state := State.ofPresentList whole.accounts, chainId := whole.chainId }
  let mut number := 0
  for block in whole.blocks do
    number := number + 1
    let .ok witness := witnessOf chain.state | return ← fail s!"block {number}: no witness could be cut" tally
    if witness.root != chain.state.root then
      tally ← fail s!"block {number}: the witness's root is not the state's" tally
    -- Jaune keeps the 255 blocks before the next one, which is what a request has to carry.
    let headers := chain.blocks.map fun b => headerBytes b.header
    let request : Stateless.Request :=
      { fork := some whole.fork, chainId := whole.chainId, block := block.toByteArray, headers,
        nodes := witness.nodes, codes := witness.codes, keys := witness.keys }
    let answer := Stateless.run request
    let .ok (.inl next) := addBlockToChainAt whole.fork chain block
      | return ← fail s!"block {number}: the ordinary import does not accept it" tally
    let some tip := next.blocks.getLast? | return ← fail "an empty chain" tally
    let wanted : Service.Response := ⟨0, 1, tip.header.hash, next.state.root⟩
    if !same answer wanted then
      tally ← fail s!"block {number}: status {answer.status}, tip {answer.tip}, root {answer.root}" tally
    tally := { tally with blocks := tally.blocks + 1 }
    -- The request survives being written and read.
    match request.encode with
    | none => tally ← fail "a request has no encoding" tally
    | some encoded =>
      if number == 1 && Stateless.serve encoded != wanted.encode then
        tally ← fail s!"block {number}: the request as bytes is answered differently" tally
    -- With `write`, the last block of the chain is kept as a request for the service as a process.
    if write && number == whole.blocks.length then
      if let some encoded := request.encode then
        IO.FS.createDirAll "fixtures/stateless"
        IO.FS.writeBinFile s!"fixtures/stateless/{name}-{number}.req" encoded
        IO.FS.writeBinFile s!"fixtures/stateless/{name}-{number}.expected" wanted.encode
    if shorten then
      let mut variants : List (String × Stateless.Request) := []
      for i in [0 : witness.nodes.size] do
        variants := (s!"node {i} of {witness.nodes[i]!.size} bytes",
          { request with nodes := witness.nodes.eraseIdx! i }) :: variants
      for i in [0 : witness.keys.length] do
        variants := (s!"a key of {(witness.keys[i]!).size} bytes",
          { request with keys := witness.keys.eraseIdx i }) :: variants
      for i in [0 : witness.codes.length] do
        variants := ("a code", { request with codes := witness.codes.eraseIdx i }) :: variants
      variants := ("a header", { request with headers := headers.drop 1 }) :: variants
      for (left, variant) in variants do
        let got := Stateless.run variant
        tally := { tally with shortened := tally.shortened + 1 }
        if noVerdict got then
          tally := { tally with noticed := tally.noticed + 1 }
        else if !same got wanted then
          tally ← fail s!"block {number}: without {left}, status {got.status}" tally
      -- A block that claims a state root its execution does not give is invalid, and provably so.
      let lying : Block := { tip with header := { tip.header with stateRoot := tip.header.stateRoot + 1 } }
      let got := Stateless.run { request with block := lying.toRlpItem.toBytes.toByteArray }
      if got.status != 3 then
        tally ← fail s!"block {number}: a wrong state root got status {got.status}" tally
      let got := Stateless.run { request with nodes := #[] }
      if !noVerdict got then
        tally ← fail s!"block {number}: no nodes at all got status {got.status}" tally
    chain := next
  pure tally

def main (args : List String) : IO UInt32 := do
  let mut tally : Tally := {}
  for name in ["highGasUsage", "wallet2outOf3txsRevokeAndConfirmAgain", "DelegateCallSpam"] do
    tally ← fixture name true tally (args.contains "write")
  IO.println s!"three fixtures, witness whole and then one piece short: {tally.blocks} blocks, \
    {tally.shortened} shortened witnesses, {tally.noticed} of them answered with no verdict"
  let before := tally.blocks
  for name in ["walletReorganizeOwners"] ++ (if args.contains "all" then ["ShanghaiLove"] else []) do
    tally ← fixture name false tally
  IO.println s!"longer fixtures, witness whole: {tally.blocks - before} blocks"
  if tally.failures == 0 then IO.println "stateless-test: all checks passed"
  else IO.println s!"stateless-test: {tally.failures} FAILED"
  return if tally.failures == 0 then 0 else 1
