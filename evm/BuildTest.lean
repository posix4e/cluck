import Evm

/-! Tests of `Evm.Build` against `Evm.Stateless`, which checks blocks, and against blocks that exist.

A stateless request is a block and a witness for it. Its block is used as the makings of a block: the
header as the template and the transactions as what is proposed.

- **Built again as given.** With the transactions kept in their order, the block built has to be the block
  the request holds: the same hash, which is every field of the header. That is the test that the header
  is put together as the chain puts it together.
- **A transaction that cannot go in.** The first transaction proposed a second time has a nonce already
  used. It has to be left out and the block come out as before.
- **Built by the rule.** With the transactions ordered by what they pay, whatever is built has to be a
  block `Evm.Stateless` accepts with the same witness.
- **A witness that falls short.** Each node, key and code of the witness is left out in turn. The answer
  has to be that nothing was built (4 when what is missing is needed before or after the transactions, by
  a system call; 6 or 7 otherwise), or a block that `Evm.Stateless` accepts with the whole witness: with
  less to go on it may build a smaller block, never a wrong one.

    .lake/build/bin/build-test             (from evm/: the three fixtures in fixtures/stateless/)
    .lake/build/bin/build-test write       (the same, and fixtures/build/ made again from them: a request
                                            to build by the rule and the response it must get)
    .lake/build/bin/build-test DIR         (every NAME.req in DIR as well, built again as given and by
                                            the rule; for blocks of mainnet made by witness/fetch)
    .lake/build/bin/build-test real DIR [STEP]
                                           (every NAME.req in DIR built by the rule with every STEPth
                                            address, by default every tenth, left out of its witness)

Run on Lean's own runtime. -/
open Jaune Evm

structure Tally where
  failures : Nat := 0
  checks : Nat := 0

def Tally.expect (t : Tally) (what : String) (ok : Bool) : IO Tally := do
  if !ok then IO.println s!"FAILED: {what}"
  pure { failures := t.failures + (if ok then 0 else 1), checks := t.checks + 1 }

/-- The block a response describes, as bytes: its header, the proposed transactions it names, and the
withdrawals proposed. -/
def blockOf (template : Block) (built : Build.Built) : ByteArray :=
  let proposed := template.transactions.toArray
  let block : Block :=
    { header := built.header, transactions := built.included.filterMap (proposed[·]?), ommers := [],
      withdrawals := template.withdrawals }
  block.toRlpItem.toBytes.toByteArray

/-- Whether `Evm.Stateless` accepts the block a response describes, with this witness, as the block the
response says it is. -/
def accepted (witness : Stateless.Request) (template : Block) (built : Build.Built) : Bool :=
  let answer := Stateless.run { witness with block := blockOf template built }
  answer.status == 0 && answer.tip == built.hash && answer.root == built.header.stateRoot

def one (engine : Bool) (name : String) (bytes : ByteArray) (shorten : Bool) (tally : Tally) (write : Bool := false) :
    IO Tally := do
  let mut tally := tally
  let name := (if engine then "the engine: " else "") ++ name
  let some (witness, _) := (Stateless.request bytes).run 0
    | tally.expect s!"{name}: not a stateless request" false
  let .ok (template, hash) := rlpToBlockE witness.block.toList
    | tally.expect s!"{name}: the block does not decode" false
  let count := template.transactions.length
  let limit := template.header.gasLimit
  -- Built again as given.
  let started ← IO.monoMsNow
  let again := Build.run { witness, rule := 0, gasCap := limit, engine }
  let took := (← IO.monoMsNow) - started
  match again.built with
  | some b =>
    tally ← tally.expect s!"{name}: built again as given, {b.included.length} of {count} went in and the \
      hash is {b.hash}, not {hash}" (b.hash == hash && b.included.length == count)
    -- The request survives being written and read, and the response says the same as bytes.
    match (Build.Request.encode { witness, rule := 0, gasCap := limit, engine }) with
    | some encoded =>
      let reply := Build.serve encoded
      tally ← tally.expect s!"{name}: the request as bytes is answered differently"
        (reply == again.encode && reply.size > 100 && reply.extract 1 33 == Trie.wordBytes hash)
    | none => tally ← tally.expect s!"{name}: the request has no encoding" false
  | none => tally ← tally.expect s!"{name}: nothing built from the block's own transactions, status {again.status}" false
  -- What the parent fixes is worked out here, whatever the sender put.
  let h := template.header
  let wrongHeader : Header :=
    { h with
      baseFeePerGas := h.baseFeePerGas.map fun fee => fee + 7
      excessBlobGas := h.excessBlobGas.map fun excess => excess + 131072
      stateRoot := 5
      gasUsed := 9 }
  let wrong : Block := { template with header := wrongHeader }
  let righted := Build.run
    { witness := { witness with block := wrong.toRlpItem.toBytes.toByteArray }, rule := 0, gasCap := limit, engine }
  tally ← tally.expect s!"{name}: a wrong base fee and excess blob gas in the template were not put right"
    ((righted.built.map fun b => b.hash == hash) == some true)
  -- A transaction that cannot go in.
  if let first :: _ := template.transactions then
    let doubled := { template with transactions := template.transactions ++ [first] }
    let twice := Build.run
      { witness := { witness with block := doubled.toRlpItem.toBytes.toByteArray }, rule := 0, gasCap := limit, engine }
    tally ← tally.expect s!"{name}: a transaction proposed twice was not left out the second time"
      ((twice.built.map fun b => b.hash == hash && b.included.length == count) == some true)
  -- Built by the rule.
  let started ← IO.monoMsNow
  let ruled := Build.run { witness, rule := 1, gasCap := limit, engine }
  let ruledTook := (← IO.monoMsNow) - started
  let mut went := 0
  match ruled.built with
  | some b =>
    went := b.included.length
    tally ← tally.expect s!"{name}: the block built by the rule is not one the checker accepts"
      (accepted witness template b)
  | none =>
    -- With the order changed the witness may not reach: that is an answer, and it is said.
    tally ← tally.expect s!"{name}: by the rule, status {ruled.status}" (ruled.status == 6)
  -- Out of time before the first transaction, and half way through: what was in by then is a whole block,
  -- one the checker accepts, and nothing after it went in. (`over` is asked before each transaction; here
  -- it counts how often.) Ending early can need a node of the witness that the whole block did not, and
  -- then the answer is that, said.
  for k in [0, count / 2] do
    let over : StateM Nat Bool := modifyGet fun asked => (asked ≥ k, asked + 1)
    let ((cut, _, _), _) := (Build.runWith over { witness, rule := 0, gasCap := limit, engine }).run 0
    match cut.built with
    | some b =>
      tally ← tally.expect s!"{name}: out of time after {k} transactions, {b.included.length} went in, or the \
        checker does not accept the block" (b.included == List.range k && accepted witness template b)
    | none => tally ← tally.expect s!"{name}: out of time after {k} transactions, status {cut.status}" (cut.status == 6)
  if write && !engine then
    if let some encoded := Build.Request.encode { witness, rule := 1, gasCap := limit, engine } then
      IO.FS.createDirAll "fixtures/build"
      IO.FS.writeBinFile s!"fixtures/build/{name}.req" encoded
      IO.FS.writeBinFile s!"fixtures/build/{name}.expected" ruled.encode
  IO.println s!"{name}: {count} transactions; as given {took} ms; by the rule {went} went in \
    (status {ruled.status}), {ruledTook} ms"
  -- A witness that falls short.
  if shorten then
    let mut variants : List (String × Stateless.Request) := []
    for i in [0 : witness.nodes.size] do
      variants := (s!"node {i}", { witness with nodes := witness.nodes.eraseIdx! i }) :: variants
    for i in [0 : witness.keys.length] do
      variants := (s!"key {i}", { witness with keys := witness.keys.eraseIdx i }) :: variants
    for i in [0 : witness.codes.length] do
      variants := (s!"code {i}", { witness with codes := witness.codes.eraseIdx i }) :: variants
    let mut smaller := 0
    let mut nothing := 0
    for (left, short) in variants do
      for rule in [0, 1] do
        let answer := Build.run { witness := short, rule, gasCap := limit, engine }
        match answer.built with
        | some b =>
          if b.included.length < count then smaller := smaller + 1
          tally ← tally.expect s!"{name}: without {left}, rule {rule}, a block was built that the checker \
            does not accept" (accepted witness template b)
        | none =>
          nothing := nothing + 1
          tally ← tally.expect s!"{name}: without {left}, rule {rule}, status {answer.status}"
            (answer.status == 4 || answer.status == 6 || answer.status == 7)
    IO.println s!"{name}: {2 * variants.length} shortened witnesses; {nothing} built nothing, {smaller} built a \
      smaller block"
  pure tally

/-- A block of the real chain built by the rule with every `step`th address left out of the witness in
turn: nothing built, or a block the checker accepts with the whole witness. -/
def real (engine : Bool) (name : String) (bytes : ByteArray) (step : Nat) (tally : Tally) : IO Tally := do
  let mut tally := tally
  let name := (if engine then "the engine: " else "") ++ name
  let some (witness, _) := (Stateless.request bytes).run 0
    | tally.expect s!"{name}: not a stateless request" false
  let .ok (template, _) := rlpToBlockE witness.block.toList
    | tally.expect s!"{name}: the block does not decode" false
  let addresses := (witness.keys.filter (·.size == 20)).toArray
  let whole := (Build.run { witness, rule := 1, gasCap := template.header.gasLimit, engine }).built.map (·.included.length)
  let mut smaller := 0
  let mut nothing := 0
  let mut tried := 0
  for turn in [0 : (addresses.size + step) / (step + 1)] do
    let left := addresses[turn * (step + 1)]!
    let short := { witness with keys := witness.keys.filter (· != left) }
    let answer := Build.run { witness := short, rule := 1, gasCap := template.header.gasLimit, engine }
    tried := tried + 1
    match answer.built with
    | some b =>
      if some b.included.length != whole then smaller := smaller + 1
      tally ← tally.expect s!"{name}: without the address {Stateless.hexOf left.toList} a block was built \
        that the checker does not accept" (accepted witness template b)
    | none =>
      nothing := nothing + 1
      tally ← tally.expect s!"{name}: without the address {Stateless.hexOf left.toList}, status {answer.status}"
        (answer.status == 4 || answer.status == 6 || answer.status == 7)
  IO.println s!"{name}: {tried} of {addresses.size} addresses left out in turn; {nothing} built nothing, \
    {smaller} built a different block, each one the checker accepts"
  pure tally

def main (args : List String) : IO UInt32 := do
  let mut tally : Tally := {}
  -- Every case is put to Jaune's builder and then to the fast engine's.
  for engine in [false, true] do
    for name in ["highGasUsage-11", "wallet2outOf3txsRevokeAndConfirmAgain-8", "DelegateCallSpam-1"] do
      tally ← one engine name (← IO.FS.readBinFile s!"fixtures/stateless/{name}.req") true tally (args == ["write"])
  -- `build-test real DIR [STEP]`: only the blocks of the real chain in DIR, with addresses left out.
  if let "real" :: dir :: rest := args then
    let step := (rest.head?.bind String.toNat?).getD 10 - 1
    let entries := (← System.FilePath.readDir dir).filter (·.fileName.endsWith ".req")
    for engine in [false, true] do
      for entry in entries.qsort (·.fileName < ·.fileName) do
        tally ← real engine ((entry.fileName.splitOn ".req").headD entry.fileName) (← IO.FS.readBinFile entry.path) step tally
    if tally.failures == 0 then IO.println s!"build-test: all {tally.checks} checks passed"
    else IO.println s!"build-test: {tally.failures} of {tally.checks} FAILED"
    return if tally.failures == 0 then 0 else 1
  if let [dir] := args.filter (· != "write") then
    let entries := (← System.FilePath.readDir dir).filter (·.fileName.endsWith ".req")
    for engine in [false, true] do
      for entry in entries.qsort (·.fileName < ·.fileName) do
        tally ← one engine ((entry.fileName.splitOn ".req").headD entry.fileName) (← IO.FS.readBinFile entry.path) false tally
  if tally.failures == 0 then IO.println s!"build-test: all {tally.checks} checks passed"
  else IO.println s!"build-test: {tally.failures} of {tally.checks} FAILED"
  return if tally.failures == 0 then 0 else 1
